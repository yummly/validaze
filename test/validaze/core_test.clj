(ns validaze.core-test
  (:require [validaze.core :as core]
            [clojure.test :refer :all]
            [clojure.set :as set]
            [clojure.spec.alpha :as s]
            [clojure.spec.test.alpha :as stest]
            [clojure.test.check.generators :as gen]))

(defn instrument-all-syms []
  (stest/instrument (stest/instrumentable-syms)))

(defn spec-check-is-success [check-res]
  (stest/summarize-results check-res)
  (if (nil? check-res)
    (is false "stest/check result was nil. did you pass it any valid symbols?")
    (let [check #(let [res %1]
                   (is (= true (-> res :clojure.spec.test.check/ret :result))
                       (format "spec check failure:\r\n%s" (with-out-str (clojure.pprint/pprint res)))))]
      (doall (map check check-res)))))

(defn explain-valid? [spec data]
  (is (s/valid? spec data)
      (format "`valid?` failure explanation:\r\n%s" (s/explain-str spec data))))

(deftest ^:eftest/slow specd-functions-pass-check
  (instrument-all-syms)
  (let [fns [`core/enum-validator
          ;   `core/-list-validator
          ;   `core/-refinement-kwd->validator
          ;   `core/transform-msg
          ;   `core/prepend-prop
          ;   `core/-prop-spec->prop-validator
          ;   `core/validate-to-msg
          ;   `core/keys-validator
             ]]
    (spec-check-is-success (stest/check fns))))

(deftest generator-spec-congruence
  (instrument-all-syms)
  ;; These are the specs in our project defined with `with-gen`.
  ;; Verifies that generator and spec are congruent with one another.
  (doseq [spec '(::core/json-map
                 ::core/refinements
                 ::core/refinements-with-string
                 ::core/refinements-refinement-kwd-tup
                 ::core/snake-cased-alpha-numeric
                 ::core/events-schema
                 ::core/refinements-property-refinement-tup
                 ::core/primitive-validation-fn
                 ::core/primitive-message-fn
                 ::core/validation-fn
                 ::core/message-fn
                 ::core/enum-refinement
                 ::core/list-refinement
                 ::core/object-refinement
                 ::core/primitive-validator
                 ::core/validator)]
    (is (gen/sample (s/gen spec) 1000)
        (format "incongruence between spec and its generator: %s" spec))))
