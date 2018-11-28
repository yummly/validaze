(ns validaze.core
  (:require
   [clojure.spec.alpha :as s]
   [clojure.spec.test.alpha :as stest]
   [clojure.test.check.generators :as gen]
   [clojure.test.check.properties :as prop]
   [clojure.test.check :as tc]
   [com.rpl.specter :as specter]
   [com.gfredericks.test.chuck.generators :as gen']
   [clojure.core.match :refer [match]]
   [arrangement.core :as order]
   [validaze.refinements :as refinements]))

(s/def ::nonempty-string
  (s/and string? seq))

(def ^:private base-refinements
  {:string string?
   :object map?
   :number number?
   :integer integer?
   :boolean boolean?})

(def ^:dynamic primitive-type-to-gen nil)
(s/def ::nonnilable-json-primitive
  (s/with-gen
    (s/or :b boolean? :n number? :s string?)
    #(let [selected (select-keys base-refinements [:boolean :number :string])]
      ((merge {nil (gen/one-of (map (fn [p] (s/gen p)) (vals selected)))}
              (specter/transform [specter/MAP-VALS] s/gen selected))
       primitive-type-to-gen))))

(def value-level-value-spec (s/or :primitive ::json-primitive :seq sequential? :map map?))
(s/def ::value-level-value
  (s/with-gen
    value-level-value-spec
    #(if (not (nil? primitive-type-to-gen))
       (s/gen ::nonnilable-json-primitive)
       (s/gen value-level-value-spec))))

(s/def ::json-primitive
  (s/nilable ::nonnilable-json-primitive))

(s/def ::json-map
  (s/with-gen
    (let [checker (fn inner [primitives? v]
                    (cond
                      (map? v) (and (every? string? (keys v)) (every? (partial inner true) (vals v)))
                      (coll? v) (every? (partial inner true) v)
                      primitives? (s/valid? ::json-primitive v)
                      :else false))]
      (partial checker false))
    #(gen/recursive-gen (fn [inner] (gen/map gen/string inner))
                        (s/gen ::json-primitive))))

(defn- printable-fn [f to-string]
  (reify clojure.lang.IFn
    (toString [this] (to-string))
    (invoke [this a] (f a))
    (applyTo [this a] (apply f a))))

(defn- printable-const-fn [constant]
  (printable-fn
   (fn [_] constant)
   #(format "(fn [_] %s)" (if (string? constant) (format "\"%s\"" constant) constant))))

(def validation-fn-gen
  #(gen/frequency [[8 (gen/return (with-meta (printable-const-fn true)  {:validates? true}))]
                   [1 (gen/return (with-meta (printable-const-fn false) {:validates? false}))]]))

(s/def ::value-level-validation-fn
  (s/with-gen
    (s/fspec :args (s/cat :v ::value-level-value)
             :ret boolean?)
    validation-fn-gen))

(s/def ::validation-fn
  (s/with-gen
    (s/or :func (s/fspec :args (s/cat :x ::json-map)
                         :ret boolean?)
          :set set?
          :spec s/spec?)
    validation-fn-gen))

(def message-fn-gen
  #(gen/let [msg gen/string] (with-meta (printable-const-fn msg) {:msg msg})))

(s/def ::primitive-message-fn
  (s/with-gen
    (s/fspec :args (s/cat :x ::json-primitive) :ret string?)
    message-fn-gen))

(s/def ::message-fn
  (s/with-gen
    (s/fspec :args (s/cat :x ::json-primitive)
             :ret string?)
    message-fn-gen))

(s/def ::validation-result
   (s/nilable string?))

(s/fdef validate-to-msg
        :args (s/cat :validation-fn ::value-level-validation-fn :message-fn ::primitive-message-fn
                     :value ::json-primitive)
        :ret ::validation-result)
(defn- validate-to-msg [validation-fn message-fn value]
  (if-not (s/valid? validation-fn value)
    (message-fn value)))

(defn validator-generator [v-fn-gen m-fn-gen]
  #(gen/let [v-fn (s/gen v-fn-gen)
            validates? (gen/return (:validates? (meta v-fn)))
            msg-fn (s/gen m-fn-gen)]
    (printable-fn
     (partial validate-to-msg v-fn msg-fn)
     (fn [] (if validates? "(fn [_] nil)" (str msg-fn))))))

(s/def ::validator
  (s/with-gen
    (s/fspec :args (s/cat :v ::json-map)
             :ret ::validation-result)
    (validator-generator ::validation-fn ::message-fn)))

(s/def ::primitive-validator
  (s/with-gen
    (s/fspec :args (s/cat :v ::json-primitive)
             :ret ::validation-result)
    (validator-generator ::value-level-validation-fn ::primitive-message-fn)))

(defn- into-recursively-sorted-map [m]
  (specter/transform
   [(specter/recursive-path
     [] p (specter/cond-path
           map? (specter/continue-then-stay specter/MAP-VALS p)
           coll? (specter/continue-then-stay specter/ALL p)))]
   #(cond
      (map? %1) (into (sorted-map-by order/rank) %1)
      (coll? %1) %1) m))

(def ^:private vowels #{\a \e \i \o \u})
(def ^:private normalized-base-refinements
  (let [article #(if (vowels (first %1)) "an" "a")]
    (specter/transform
     [specter/ALL]
     (fn [[k v]]
       (let [typ (name k)]
         [k [nil [v (fn [_] (format "must be %s %s" (article typ) typ))]]]))
     base-refinements)))

(defn- seq->gen
  "Takes a sequence of generators and produces a generator of sequences."
  [seq]
  (apply gen/tuple seq))

(defn- map-seq->gen
  "Takes a sequence of values and a function to apply over them
  and produces a generator of the sequence of mapped values."
  [f val-seq]
  (seq->gen (map f val-seq)))

(s/def ::refinement-tup
  (s/tuple (s/nilable keyword?) (s/tuple ::value-level-validation-fn ::primitive-message-fn)))

(s/def ::refinements
  (s/with-gen
    (s/map-of keyword? ::refinement-tup)
    #(gen/let [kwds (gen/fmap (fn [c] (if (even? (count c)) (vec (butlast c)) c))
                              (gen/vector-distinct gen/keyword {:min-elements 5 :max-elements 25}))
               cyclic-kwds (gen/return (cycle kwds))
               pairs (gen/return (distinct (take (count kwds) (partition 2 cyclic-kwds))))
               broken-cycle (gen/return (specter/transform [specter/LAST] (fn [p] [(first p) nil]) pairs))
               refinements
               (map-seq->gen
                (fn [[kwd prev]]
                  (gen/let [prev-k (gen/frequency [[4 (gen/return prev)] [1 (gen/return nil)]])
                            validation-fn (s/gen ::value-level-validation-fn)
                            validates? (gen/return (:validates? (meta validation-fn)))
                            message-fn (s/gen ::primitive-message-fn)
                            msg (gen/return (:msg (meta message-fn)))]
                    [kwd [prev-k (with-meta [validation-fn message-fn] {:validates? validates? :msg msg})]]))
                broken-cycle)]
       (into {} refinements))))

(s/def ::user-defined-refinements
  (s/map-of keyword? (s/or :set set? :refinement-tup ::refinement-tup)))

(s/def ::refinements-with-string
  (s/with-gen
    ::refinements
    #(gen/fmap (partial merge (select-keys normalized-base-refinements [:string])) (s/gen ::refinements))))

(s/def ::refinements-with-string-and-object
  (s/with-gen
    ::refinements
    #(gen/fmap (partial merge (select-keys normalized-base-refinements [:object])) (s/gen ::refinements-with-string))))

(defn- gen-derived-from-refinements [f]
  (gen/bind
   (s/gen ::refinements-with-string)
   (fn [refinements] (gen/let [kwd (gen/elements (keys refinements))] (f refinements kwd)))))

(s/def ::refinements-refinement-kwd-tup
  (s/with-gen
    (s/tuple ::refinements-with-string keyword?)
    #(gen-derived-from-refinements vector)))

(s/fdef -refinement-kwd->validator
        :args (s/cat :tup ::refinements-refinement-kwd-tup)
        :fn #(let [[refinements kwd] (-> %1 :args :tup)
                   funcs (reverse
                          (loop [[prev tup] (refinements kwd)
                                 funcs []]
                            (if (nil? prev)
                              (conj funcs tup)
                              (recur (refinements prev) (conj funcs tup)))))
                   failing-msg (if-let [f (some (fn [t] (if (-> t meta :validates? not) (second t))) funcs)] (f nil))
                   returned-msg ((:ret %1) nil)]
               (= returned-msg failing-msg))
        :ret ::primitive-validator)
(defn- -refinement-kwd->validator [[refinements refinement-kwd]] ; tuple allows both inputs to be generated simult.
  (let [_ (if-not (contains? refinements refinement-kwd)
            (throw (IllegalStateException. (format "Unknown refinement: %s" refinement-kwd))))
        [prev [validator-fn msg-fn]] (refinement-kwd refinements)
        validate-this #(validate-to-msg validator-fn msg-fn %1)]
    (cond
      (nil? prev) validate-this
      :else #(if-let [msg ((-refinement-kwd->validator [refinements prev]) %1)]
               msg
               (validate-this %1)))))

(defn- refinement-kwd->validator [refinements refinement-kwd]
  (-refinement-kwd->validator [refinements refinement-kwd]))

(defn- assign-ordering
  "Takes a collection and produces a sorted map with the key
  for each element being its index starting counting from the number one."
  [col]
  (into (sorted-map) (map-indexed (comp #(specter/transform [specter/FIRST] inc %) vector) col)))

(defn- deep-merge
  "Recursively merges maps. If keys are not maps, the last value wins."
  [& vals]
  (if (every? map? vals)
    (apply merge-with deep-merge vals)
    (last vals)))

(s/def ::snake-cased-alpha-numeric
  (let [regex #"[a-z0-9\_]+"]
    (s/with-gen
      (s/and string? #(re-matches regex %))
      #(gen'/string-from-regex regex))))
(s/def ::required?
  (s/or :bool boolean?
        :when (s/tuple #{:when}
                       ::snake-cased-alpha-numeric
                       (s/or :set (s/coll-of ::nonnilable-json-primitive :kind set?)
                             :exists #{:exists}))))
(s/def ::property-attrs
  (s/keys :req-un [::required?]))
(def property-spec
  (gen/fmap #(into {} [%]) (gen/tuple (s/gen ::snake-cased-alpha-numeric) (s/gen ::property-attrs))))

(defn- valid-includes? [property-set]
  (if (contains? property-set :includes)
    (s/valid? (s/coll-of keyword? :kind vector?)
              (property-set :includes))
    true))

(s/def ::property-set
  (s/map-of ::snake-cased-alpha-numeric (s/nilable ::property-attrs)))

(s/def ::event-property-set
  #(and (valid-includes? %1)
        (s/valid? ::property-set (dissoc %1 :includes))))

(defn- one-based-contig-range? [c]
  (= c (range 1 (+ 1 (count c)))))

(s/def ::events-schema
  (s/with-gen
    (s/and
     (s/map-of ::snake-cased-alpha-numeric
               (s/map-of integer? ::event-property-set)
               :min-count 1)
     #(every? one-based-contig-range?
              (specter/select [specter/MAP-VALS (specter/view (comp sort keys))] %)))
    #(gen/let [min-events (gen/return 2)
               max-events (gen/return 5)
               max-versions (gen/return 7)
               min-props (gen/return 1)
               max-props (gen/return 7)
               events (gen/vector (s/gen ::snake-cased-alpha-numeric) min-events max-events)
               version-counts (gen/vector (gen/choose 1 max-versions) (count events) (count events))
               shared-property-count (gen/frequency [[2 (gen/return (count events))]
                                                     [8 (gen/fmap (fn [d] (int (* (count events) d)))
                                                                  (gen/double* {:min 1.0 :max 2.0}))]])
               shared-properties (gen/vector (s/gen ::snake-cased-alpha-numeric)
                                             shared-property-count shared-property-count)
               event-cyc (gen/return (cycle events))
               shared-prop-mappings (gen/return (mapv vector shared-properties event-cyc))
               shared-groups (gen/return (specter/transform [specter/MAP-VALS] (partial map first)
                                                            (group-by second shared-prop-mappings)))
               zipped (gen/return (map vector events version-counts))
               with-shared-props (gen/return (map (fn [t] (conj t (shared-groups (first t)))) zipped))
               alternates (gen/return (cycle '(:create :delete)))
               weave-deletions (gen/return
                                (fn [altern-prop alternations prop-attrs versions]
                                  (let [zipped (map vector alternations alternates prop-attrs)
                                        mapped (mapv (fn [t] {(t 0) {altern-prop (if (= :create (t 1))
                                                                                   (t 2))}}) zipped)]
                                    (apply deep-merge (conj mapped versions)))))
               with-all-props
               (map-seq->gen (fn [t] (gen/fmap (fn [[shared ps [altern-prop alternations prop-attrs]]]
                                                 [(t 0)
                                                  (weave-deletions
                                                   altern-prop
                                                   alternations
                                                   prop-attrs
                                                   (assign-ordering
                                                    (conj (rest ps)
                                                          (apply merge (conj shared (first ps))))))])
                                               (gen/tuple
                                                (map-seq->gen (fn [p]
                                                                (gen/let [attr (s/gen ::property-attrs)] {p attr}))
                                                              (t 2))
                                                (map-seq->gen (fn [_]
                                                                (gen/let [props (gen/choose min-props max-props)
                                                                          prop-specs
                                                                          (gen/vector property-spec props props)]
                                                                  (apply merge prop-specs)))
                                                              (range (t 1)))
                                                (gen/let [altern-prop (s/gen ::snake-cased-alpha-numeric)
                                                          num-alternations (gen/choose 0 (- (t 1) 1))
                                                          alternations (gen/return
                                                                        (sort (take num-alternations
                                                                                    (shuffle (range 1 (+ 1 (t 1)))))))
                                                          prop-attrs (gen/vector (s/gen ::property-attrs)
                                                                                 num-alternations num-alternations)]
                                                  [altern-prop alternations prop-attrs])))) with-shared-props)]
       (into (sorted-map) with-all-props))))

(defn- materialize-versions [[event versions]]
  (into (sorted-map)
        {event
         (reduce
          (fn [acc [version prop-specs]]
            (let [this-version (into (sorted-map) (merge (acc (- version 1)) prop-specs))
                  deletes (filter #(nil? (second %1)) this-version)]
              (doseq [del deletes]
                (if (not (contains? (acc (- version 1)) (first del)))
                  (throw (IllegalStateException.
                          (format "ERROR: Attempt to delete non-existent property '%s' on event '%s' in version %s"
                                  (first del) event version)))))
              (assoc acc version (apply (partial dissoc this-version) (map first deletes)))))
          (sorted-map)
          versions)}))

(defn- materialize-event-schema [events-schema]
  (apply merge (map materialize-versions events-schema)))

(defn- all-referenced-properties [events-schema]
  (keys (apply merge (mapcat vals (vals events-schema)))))

(defn- check-property-references [events-schema properties-schema]
  (let [referenced (set (all-referenced-properties events-schema))
        defined (set (mapcat keys properties-schema))
        undefined (into (sorted-set) (clojure.set/difference referenced defined))
        unreferenced (into (sorted-set) (clojure.set/difference defined referenced))]
    (if (or (not-empty unreferenced) (not-empty undefined))
      (let [undefined-errs (if (not-empty undefined)
                             (format "ERROR: undefined referenced properties:\n%s"
                                     (with-out-str (clojure.pprint/pprint undefined))))
            unreferenced-errs (if (not-empty unreferenced)
                                (format "ERROR: unreferenced defined properties:\n%s"
                                        (with-out-str (clojure.pprint/pprint unreferenced))))
            msg (clojure.string/join "\n\n" (filter identity [undefined-errs unreferenced-errs]))]
        (throw (IllegalStateException. (str "\n" msg))))
      true))) ; true if validation succeeded

(s/fdef keys-validator
        :args (s/cat :required-keys (s/coll-of string?)
                     :optional-keys (s/coll-of string?))
        :ret (s/tuple (s/fspec :args (s/cat :v ::json-map) :ret set?)
                      (s/fspec :args (s/cat :v ::json-map) :ret set?)))
(defn- keys-validator [required-keys optional-keys]
  (let [missing #(clojure.set/difference (set required-keys) (set (keys %)))
        unexpected #(clojure.set/difference (set (keys %)) (set (concat required-keys optional-keys)))]
    (with-meta
      [missing unexpected]
      {:required required-keys
       :optional optional-keys})))

(defn- prop-set->keys-validator [field-descs]
  (let [{required true optional false} (group-by #(-> % second :required?) field-descs)
        [required optional] [(map first required) (map first optional)]]
    (keys-validator required optional)))

(defn- events-schema->keys-validators [events-schema]
  (let [materialized (materialize-event-schema events-schema)]
    (specter/transform
     [specter/MAP-VALS specter/MAP-VALS]
     prop-set->keys-validator
     materialized)))

(defn- super-props-schema->keys-validators [super-properties-schema]
  (let [append-version (fn [acc [version props]]
                         (assoc acc version (merge props (get acc (- version 1)))))
        reduced (reduce append-version {} super-properties-schema)
        denormalized (if (empty? reduced) {0 {}} reduced)]
    (specter/transform [specter/MAP-VALS] prop-set->keys-validator denormalized)))

(defn- reify-keys-validator [refinements
                             [event-keys-missing event-keys-unexpected]
                             [super-props-missing super-props-unexpected]]
  (let [unexpected (fn [v] (clojure.set/intersection (event-keys-unexpected v) (super-props-unexpected v)))
        missing (fn [v] (clojure.set/union (event-keys-missing v) (super-props-missing v)))
        validation-fn (fn [v] (and (map? v) (empty? (missing v)) (empty? (unexpected v))))
        msg-fn (fn [v]
                 (if (not (map? v))
                   "internal error" ; can't happen
                   (-> " "
                       (clojure.string/join
                        [(if (not-empty (missing v))
                           (format "Missing required keys: %s." (into [] (missing v))))
                         (if (not-empty (unexpected v))
                           (format "Unexpected keys: %s." (into [] (unexpected v))))])
                       (clojure.string/trim))))]
    (refinement-kwd->validator (assoc refinements :keys [:object [validation-fn msg-fn]]) :keys)))

(s/fdef enum-validator
        :args (s/cat :refinements ::refinements-with-string :values (s/coll-of string? :min-count 1))
        :fn #(let [val-set (set (-> %1 :args :values))
                   ret (:ret %1)]
               (-> (prop/for-all [v (s/gen any?)] (boolean (val-set v)))
                   (partial tc/quick-check 100)))
        :ret ::primitive-validator)
(defn- enum-validator [refinements values]
  (let [value-set (set values)
        validation-fn #(-> %1 value-set boolean)
        msg-fn (fn [_] (format "must be one of: %s" value-set))]
    (refinement-kwd->validator (assoc refinements :enum [:string [validation-fn msg-fn]]) :enum)))

(s/fdef -list-validator
        :args (s/cat :udr ::refinements :tup ::refinements-refinement-kwd-tup)
        :ret ::primitive-validator)
(defn- -list-validator [user-defined-refinements [refinements inner-type]]
  (let [validator (refinement-kwd->validator refinements inner-type)
        is-user-defined? (contains? user-defined-refinements inner-type)
        validation-fn (fn [v] (and (sequential? v) (every? #(nil? (validator %1)) v)))
        msg-fn (fn [v] (format "must be a vector of type '%s'%s"
                               (name inner-type)
                               (if is-user-defined?
                                 (format " and '%s' %s" (name inner-type) (some identity (map validator v)))
                                 "")))]
    (refinement-kwd->validator (assoc refinements
                                      :list [nil [vector? (fn [_] "must be a vector")]]
                                      :elements [:list [validation-fn msg-fn]]) :elements)))

(defn- list-validator [user-defined-refinements refinements inner-type]
  (-list-validator user-defined-refinements [refinements inner-type]))

(defn- name-type [typ]
  (cond
    (keyword? typ) (name typ)
    (and (vector? typ) (= :list (first typ))) (format "[ %s ]" (name (second typ)))
    :else "[internal error]"))

(declare vectorized-refinement->validator)
(defn- object-validator [user-defined-refinements refinements key-type value-type]
  (let [kwd->validator (partial refinement-kwd->validator refinements)
        key-validator (kwd->validator key-type)
        value-type->validator (cond (keyword? value-type) kwd->validator
                                    (and (vector? value-type) (= :list (first value-type)))
                                    #(apply (partial vectorized-refinement->validator
                                                     user-defined-refinements refinements) %1)
                                    :else (throw
                                           (IllegalStateException. (format "Invalid nested type: %s" value-type))))
        value-validator (value-type->validator value-type)
        validation-fn (fn [v] (and (every? #(nil? (key-validator %1)) (keys v))
                                   (every? #(nil? (value-validator %1)) (vals v))))
        msg-fn (fn [_] (format "must be an object from type '%s' to type '%s'"
                               (name key-type) (name-type value-type)))]
    (refinement-kwd->validator (assoc refinements
                                      :specialized-obj [:object [validation-fn msg-fn]]) :specialized-obj)))

(defn- vectorized-refinement->validator [user-defined-refinements refinements head & rest]
  (condp = head
    :enum (enum-validator refinements rest)
    :object (if (= 2 (count rest))
              (object-validator user-defined-refinements refinements (first rest) (second rest))
              (throw (IllegalStateException.
                      (format "Object vectorized refinement type expects exactly two arguments. Received: %s"
                              rest))))
    :list (if (= 1 (count rest))
            (list-validator user-defined-refinements refinements (first rest))
            (throw (IllegalStateException.
                    (format "List vectorized refinement type expects a single argument. Received: %s" rest))))
    (throw (IllegalStateException. (format "Invalid vectorized refinement type: %s" head)))))

(s/fdef transform-msg
        :args (s/cat :prop ::snake-cased-alpha-numeric
                     :validator ::primitive-validator
                     :xfm (s/fspec :args (s/cat :msg string?)
                                   :ret string?))
        :ret ::validator)
(defn- transform-msg [property validator transform-fn]
  (fn [e]
    (if (contains? e property)
      (if-let [msg (validator (get e property))]
        (transform-fn msg)))))

(s/fdef prepend-prop
        :args (s/cat :prop ::snake-cased-alpha-numeric
                     :validator ::primitive-validator)
        :ret ::validator)
(defn- prepend-prop [prop validator]
  (transform-msg prop validator #(format "'%s' %s" prop %1)))

(defn- list-refinement-gen [refinements]
  (gen/let [inner-refinement (gen/elements (keys refinements))]
    [:list inner-refinement]))

(s/def ::enum-refinement
  (s/cat :head (s/with-gen #{:enum} #(gen/return :enum))
         :tail (s/+ string?)))

(s/def ::list-refinement
  (s/cat :head (s/with-gen #{:list} #(gen/return :list))
         :tail keyword?))

(s/def ::object-refinement
  (s/cat :head (s/with-gen #{:object} #(gen/return :object))
         :from keyword?
         :to (s/or :kwd keyword? :lst ::list-refinement)))

(s/def ::type
  (s/or :kwd keyword?
        :vectorized (s/alt :enum ::enum-refinement :list ::list-refinement :obj ::object-refinement)))

(s/def ::refinements-property-refinement-tup
  (s/with-gen
    (s/and
     (s/tuple ::refinements-with-string
              (s/tuple ::snake-cased-alpha-numeric ::type))
     #(let [[refinements [_ [refinement-type refinement]]] %1]
        (condp = refinement-type
          :kwd (contains? refinements refinement)
          :vectorized (cond (= :list (first refinement))
                            (contains? refinements (:tail (second refinement)))
                            (= :enum (first refinement)) true))))
    #(gen/let [refinements (gen-derived-from-refinements (comp first vector))
               property (s/gen ::snake-cased-alpha-numeric)
               refinement (gen/one-of [(gen/elements (keys refinements))
                                       (s/gen ::enum-refinement)
                                       (list-refinement-gen refinements)])]
       [refinements [property refinement]])))

(s/fdef -prop-spec->prop-validator
        :args (s/cat :udr ::refinements :tup ::refinements-property-refinement-tup)
        :ret (s/tuple ::snake-cased-alpha-numeric ::validator))
(defn- -prop-spec->prop-validator [user-defined-refinements [refinements [property refinement]]]
  [property
   (prepend-prop property
                 (cond
                   (keyword? refinement)
                   (refinement-kwd->validator refinements refinement)
                   (coll? refinement)
                   (apply (partial vectorized-refinement->validator
                                   user-defined-refinements refinements) refinement)))])

(defn- prop-spec->prop-validator [user-defined-refinements refinements [property refinement]]
  (-prop-spec->prop-validator user-defined-refinements [refinements [property refinement]]))

(defn- all-properties [properties-schema]
  (apply merge properties-schema))

(def ^:private trivial-validator (fn [_] nil))

(defn- properties-schemas->validators [user-defined-refinements refinements properties-schema
                                       super-properties-schema-reified]
  (let [validator-gen (partial prop-spec->prop-validator user-defined-refinements refinements)
        transform-all #(specter/transform [specter/ALL] %1 %2) ; can't use partial because macro
        transform-last #(specter/transform [specter/LAST] %1 %2)]
    (merge
     (transform-all validator-gen (all-properties properties-schema))
     (transform-all
      (fn [tup]
        (transform-last
         (fn [validator]
           (fn [o]
             (let [[always-required? required-validator] (:required? (second tup))]
               (when (or always-required? (not= required-validator trivial-validator) (contains? o (first tup)))
                 (some force [(delay (required-validator o)) (delay (validator o))])))))
         (validator-gen (transform-last :type tup))))
      super-properties-schema-reified))))

(defn- validate-property-values [properties-validators props]
  (let [validators (map #(properties-validators (first %1)) props)]
    (map #(%1 props) validators)))

(defn- validate-conditional-requires [events-schema-reified event-type event-version properties]
  (let [prop-specs ((events-schema-reified event-type) event-version)
        validators (specter/select
                    [specter/ALL specter/LAST :required? specter/LAST #(not= % trivial-validator)]
                    prop-specs)]
    (map #(%1 properties) validators)))

(defn- event-key->optional-spec [events-schema-reified event-type event-version key]
  (if (< event-version 1) false
      (let [event-schema ((events-schema-reified event-type) event-version)]
        (if (contains? event-schema key)
          (or (-> key event-schema :required? meta :syntax) false)
          (recur events-schema-reified event-type (- event-version 1) key)))))

(defn- event->schema [events-schema-reified super-keys-validators keys-validators
                      properties-schema super-properties-schema-raw
                      super-properties-version event-type event-version]
  (if-let [super-keys-validator (get super-keys-validators super-properties-version)]
    (if-let [event-keys-validators (keys-validators event-type)]
      (if-let [event-keys-validator (get event-keys-validators event-version)]
        (let [{keys-req :required keys-optional :optional} (meta event-keys-validator)
              {sup-keys-req :required sup-keys-optional :optional} (meta super-keys-validator)
              keys-spec (fn [keys req?] (apply merge (map #(do {% {:required? req?}}) keys)))
              req-keys (keys-spec keys-req true)
              opt-spec (partial event-key->optional-spec events-schema-reified event-type event-version)
              opt-keys (apply merge (map #(do {%1 {:required? (opt-spec %1)}}) keys-optional))
              event-keys (merge req-keys opt-keys)
              super-keys (merge (keys-spec sup-keys-req true) (keys-spec sup-keys-optional false))
              merged-prop-schema (apply merge properties-schema)
              referred-key-props (keys event-keys)
              event-key-types (apply merge (map #(do {%1 (merged-prop-schema %1)}) referred-key-props))
              merged-super-prop-schema (apply merge (vals super-properties-schema-raw))
              referred-super-props (keys super-keys)
              super-key-types (apply merge (map #(do {%1 (merged-super-prop-schema %1)}) referred-super-props))
              types (merge event-key-types super-key-types)
              reduced (into {} (for [[k v] types] [k (or (:type v) v)]))]
          {:keys event-keys
           :super-keys super-keys
           :types reduced})))))

(defn- validate-single-extended [refinements keys-validators super-keys-validators
                                 properties-validators events-schema-reified
                                 {:strs [event_type event_version properties super_properties_version]
                                  :or {super_properties_version (apply min (keys super-keys-validators))}}]
  (if-let [super-keys-validator (get super-keys-validators super_properties_version)]
    (let [event-keys-validators (keys-validators event_type)
          event-keys-validator (get event-keys-validators event_version)]
      (if (and event-keys-validators event-keys-validator)
        (let [keys-validator (reify-keys-validator refinements event-keys-validator super-keys-validator)]
          (if-let [msg (keys-validator properties)]
            [msg]
            (not-empty
             (remove nil? (concat (validate-conditional-requires
                                   events-schema-reified event_type event_version properties)
                                  (validate-property-values properties-validators properties))))))
        [(format "There is no version %s for event '%s'" event_version event_type)]))
    [(format "There is no super-properties version %s" super_properties_version)]))

(defn- validate-vector-or-single [vec-or-single validator-fn success-fn]
  (let [errors
        (if (sequential? vec-or-single)
          (into {} (map-indexed #(let [e (validator-fn %2)] (when (not-empty e) [%1 e])) vec-or-single))
          (validator-fn vec-or-single))]
    (if (empty? errors)
      (success-fn vec-or-single)
      (if (sequential? errors)
        (into [] errors)
        errors))))

(defn- validate-extended [refinements keys-validators super-keys-validators
                          properties-validators events-schema-reified event]
  (validate-vector-or-single
   event
   (partial validate-single-extended refinements keys-validators
            super-keys-validators properties-validators events-schema-reified)
   (constantly nil)))

(defn- property->validator [refinements prop refinement-kwd]
  (prepend-prop prop (refinement-kwd->validator refinements refinement-kwd)))

(def ^:private missing-nothing (constantly #{}))
(def ^:private unexpected-everything (comp set keys))
(defn- base-event-validators [refinements]
  [(reify-keys-validator
    refinements
    (keys-validator ["event_version" "event_type" "properties"] ["super_properties_version"])
    [missing-nothing unexpected-everything])
   (property->validator refinements "super_properties_version" :integer)
   (property->validator refinements "event_version" :integer)
   (property->validator refinements "event_type" :string)
   (property->validator refinements "properties" :object)])

(defn- validate-base [base-event-validators event]
  (let [validator (fn [event] (filter identity (map #(% event) base-event-validators)))]
    (validate-vector-or-single event validator (constantly nil))))

(defn- check-super-property-separateness [properties-schema super-properties-schema]
  (let [prop-keys (-> properties-schema all-properties keys set)
        super-prop-keys (-> super-properties-schema keys set)
        intersection (clojure.set/intersection prop-keys super-prop-keys)]
    (if (not-empty intersection)
      (throw (IllegalStateException.
              (format "Super-properties cannot be explicitly referenced. Illegal: %s"
                      (into [] intersection))))
      true)))

(defn- check-spec [spec data]
  (if-not (s/valid? spec data)
    (throw (IllegalStateException. ^String (s/explain-str spec data)))
    true))

(s/def ::properties-schema
  (s/coll-of (s/map-of ::snake-cased-alpha-numeric ::type) :min-count 1))

(s/def ::super-property-field
  (s/keys :req-un [::type ::required?]))
(s/def ::super-properties-schema
  (s/and
   (s/map-of integer? (s/map-of ::snake-cased-alpha-numeric ::super-property-field))
   #(one-based-contig-range? (sort (keys %1)))))

(s/def ::property-lists
  (s/map-of keyword? ::property-set))

(defn- check-property-list-references [events-schema property-lists]
  (let [keys (set (keys property-lists))
        includes
        (set (apply concat (remove nil? (specter/select [specter/MAP-VALS specter/MAP-VALS :includes] events-schema))))
        undefined (clojure.set/difference includes keys)]
    (if (not-empty undefined)
      (throw (IllegalStateException.
              (format "Undefined property list references: %s" (into [] undefined))))
      true)))

(defn- check-super-prop-version-additiveness [super-properties-schema]
  (let [keys-sets (specter/transform
                   [specter/MAP-VALS]
                   (comp set keys)
                   super-properties-schema)
        verify-version (fn [acc [version props]]
                         (let [intersection (clojure.set/intersection acc props)]
                           (if (not-empty intersection)
                             (throw (IllegalStateException.
                                     (format
                                      "Version %s of super-properties schema duplicates existing properties: %s"
                                      version (into [] intersection))))
                             (clojure.set/union acc props))))]
    (reduce verify-version #{} (into (sorted-map) keys-sets))
    true))

(defn- schemas-valid? [events-schema events-schema-raw properties-schema
                       super-properties-schema super-properties-schema-raw
                       property-lists]
  (and
   (check-property-references events-schema properties-schema)
   (check-super-property-separateness properties-schema super-properties-schema)
   (check-super-prop-version-additiveness super-properties-schema)
   (check-spec ::events-schema events-schema-raw)
   (check-property-list-references events-schema-raw property-lists)
   (check-spec ::properties-schema properties-schema)
   (check-spec ::super-properties-schema super-properties-schema-raw)))

(defn- reify-required-specs [prop-schema]
  (specter/transform
   [specter/ALL (specter/collect-one specter/FIRST) specter/LAST :required?]
   (fn [prop req-spec]
     (match req-spec
            [:when other-prop values]
            (let [[pred msg] (if (= values :exists)
                               [#(contains? % other-prop) "exists"]
                               [#(contains? values (% other-prop))
                                (format "is any of: %s" values)])]
              (with-meta
                [false
                 (fn [o]
                   (if (pred o)
                     (if-not (contains? o prop)
                       (format "'%s' is required when '%s' %s"
                               prop other-prop msg))))]
                {:syntax [:when other-prop values]}))
            :else [req-spec trivial-validator]))
   prop-schema))

(defn- explode-includes [property-lists m]
  (specter/transform [specter/MAP-VALS specter/MAP-VALS (specter/submap [:includes])]
                     #(apply merge (map property-lists (%1 :includes))) m))

(defn- prepare-refinements [user-defined-refinements normalized-base-refinements]
  (let [user-defined-refinements (specter/transform
                                  [specter/MAP-VALS set?]
                                  #(do [:string [%1 (fn [_] (str "must be one of: " %1))]])
                                  user-defined-refinements)
        refinements (s/assert ::refinements
                              (merge user-defined-refinements
                                     refinements/user-defined-refinements
                                     normalized-base-refinements))]
    [user-defined-refinements refinements]))

(s/fdef validator
        :args (s/alt
               :binary
               (s/cat :events-schema ::events-schema
                      :properties-schema ::properties-schema)
               :tertiary
               (s/cat :events-schema ::events-schema
                      :properties-schema ::properties-schema
                      :super-properties-schema ::super-properties-schema)
               :quaternary
               (s/cat :events-schema ::events-schema
                      :properties-schema ::properties-schema
                      :super-properties-schema ::super-properties-schema
                      :refinements ::user-defined-refinements)
               :pentary
               (s/cat :events-schema ::events-schema
                      :properties-schema ::properties-schema
                      :super-properties-schema ::super-properties-schema
                      :property-lists ::property-lists
                      :refinements ::user-defined-refinements))
        :ret ::validator)
(defn validator
  ([events-schema properties-schema]
   (validator events-schema properties-schema {}))
  ([events-schema properties-schema super-properties-schema]
   (validator events-schema properties-schema super-properties-schema {}))
  ([events-schema properties-schema super-properties-schema refinements]
   (validator events-schema properties-schema super-properties-schema {} refinements))
  ([events-schema properties-schema super-properties-schema property-lists refinements]
   (let [property-lists (into-recursively-sorted-map property-lists)
         events-schema-raw (into-recursively-sorted-map events-schema)
         events-schema-reified (specter/transform
                                [specter/MAP-VALS specter/MAP-VALS]
                                reify-required-specs
                                (explode-includes property-lists events-schema-raw))
         events-schema (specter/transform
                        [specter/MAP-VALS specter/MAP-VALS specter/MAP-VALS :required?]
                        first
                        events-schema-reified)
         properties-schema (into-recursively-sorted-map properties-schema)
         super-properties-schema-raw (into-recursively-sorted-map super-properties-schema)
         super-properties-schema-reified (specter/transform
                                          [specter/MAP-VALS]
                                          reify-required-specs
                                          super-properties-schema-raw)
         super-properties-schema (specter/transform
                                  [specter/MAP-VALS specter/MAP-VALS :required?]
                                  first
                                  super-properties-schema-reified)
         refinements-raw (into-recursively-sorted-map refinements)
         [user-defined-refinements refinements]
         (prepare-refinements refinements-raw normalized-base-refinements)
         keys-validators (events-schema->keys-validators events-schema)
         super-keys-validators (super-props-schema->keys-validators super-properties-schema)
         super-properties-schemas-flattened (apply merge (reverse (vals super-properties-schema-reified)))
         properties-validators (properties-schemas->validators
                                user-defined-refinements refinements properties-schema
                                super-properties-schemas-flattened)]
     (if (schemas-valid? events-schema events-schema-raw properties-schema super-properties-schema
                         super-properties-schema-raw property-lists)
       (with-meta
         (fn [event-or-events]
           (if-let [msg (validate-base (base-event-validators refinements) event-or-events)]
             msg
             (validate-extended refinements keys-validators super-keys-validators
                                properties-validators events-schema-reified event-or-events)))
         {:events-schema events-schema
          :events-schema-reified events-schema-reified
          :super-properties-schema super-properties-schema
          :super-properties-schema-reified super-properties-schema-reified
          :super-properties-schemas-flattened super-properties-schemas-flattened
          :user-defined-refinements user-defined-refinements
          :refinements refinements
          :event->schema (partial event->schema events-schema-reified super-keys-validators keys-validators
                                  properties-schema super-properties-schema-raw)})))))

(defn- refinement->base-refinement [refinements refinement]
  (loop [cur refinement]
    (let [[nxt _] (refinements cur)]
      (if (nil? nxt) cur (recur nxt)))))

(s/fdef refinements->validators
        :args (s/cat :refinements
                     (fn [v]
                       (every?
                        identity
                        (map
                         (fn [[refinement [kwd refinement-spec :as refinement-tup]]]
                           (or (set? refinement-spec)
                               (binding [primitive-type-to-gen
                                         (refinement->base-refinement
                                          (merge v normalized-base-refinements) kwd)]
                                 (s/valid? ::refinement-tup refinement-tup))))
                         v))))
        :ret (s/map-of keyword? ::validator))
(defn refinements->validators [refinements]
  (let [[_ refinements] (prepare-refinements refinements normalized-base-refinements)]
    (specter/transform
     [specter/ALL]
     (fn [[kwd _]]
          [kwd (-refinement-kwd->validator [refinements kwd])])
     refinements)))

(stest/instrument `validator)
(stest/instrument `refinements->validators)
