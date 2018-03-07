(defproject yummly/validaze "1.0.0"
  :description
  "Hiccup-inspired DSL implementation of refinement types for validating JSON data."
  :license {:name "Eclipse Public License"
            :url "http://www.eclipse.org/legal/epl-v10.html"}
  :dependencies [[org.clojure/clojure "1.9.0"]
                 [com.gfredericks/test.chuck "0.2.8"]
                 [clj-time "0.14.2"]
                 [com.rpl/specter "1.0.4"]
                 [org.clojure/data.codec "0.1.0"]
                 [org.clojure/core.match "0.3.0-alpha5"]
                 [mvxcvi/arrangement "1.1.1"]
                 ;; require 0.10.0 to fix a bug around monkey patching with clojure.test
                 [org.clojure/test.check "0.10.0-alpha2"]]
  :exact-lein-version "2.8.1"
  :main ^:skip-aot validaze.core
  :target-path "target/%s"
  :eftest {:test-warn-time 5000}
  :profiles {:dev {:plugins [[lein-eftest "0.4.1"]]}})
