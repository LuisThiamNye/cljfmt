(ns cljfmt.core
  #?(:clj (:refer-clojure :exclude [reader-conditional?]))
  (:require #?(:clj [clojure.java.io :as io])
            [clojure.string :as str]
            [rewrite-clj.node :as n]
            [rewrite-clj.parser :as p]
            [rewrite-clj.zip :as z])
  #?(:clj (:import java.util.regex.Pattern)
     :cljs (:require-macros [cljfmt.core :refer [read-resource]])))

(defmacro dbl
  [ms p body]
  (if true
    body
    `(let [before# (System/currentTimeMillis)
           r# ~body
           t# (- (System/currentTimeMillis) before#)]
       (when (< 0 ~ms t#)
         (prn "Time Tripped: " t#)
         (prn ~p))
       r#)))

#?(:clj (def read-resource* (comp read-string slurp io/resource)))
#?(:clj (defmacro read-resource [path] `'~(read-resource* path)))

(def includes?
  #?(:clj  (fn [^String a ^String b] (.contains a b))
     :cljs str/includes?))

(defn- find-all [zloc p?]
  (loop [matches []
         zloc zloc]
    (if-let [zloc (z/find-next zloc z/next* p?)]
      (recur (conj matches zloc)
             (z/next* zloc))
      matches)))

(defonce edit-all-counter (atom 0))
(defonce edit-call (atom 0))
(defonce indenting? (atom false))

(defn- edit-all [zloc p? f]
  (when (zero? @edit-all-counter) (reset! edit-call 0))
  (swap! edit-call inc)
  (loop [zloc (if (p? zloc) (f zloc) zloc)
         i 1]
    (swap! edit-all-counter inc)
    ;; (prn "edit-all: z/find-next")
    ;; (prn "editing:" i)
    ;; (when (= 2 @edit-call)
    ;;   (println "editing this node:\n" (z/node zloc)))
    (if-let [zloc2 (z/find-next zloc z/next* p?)]
      (do
        ;; (println "found next zloc\n" (z/node zloc2) "\nafter\n" (z/node zloc) "\n\non cycle" @edit-all-counter)
        ;; (throw (Exception. ""))
        (recur (f zloc2) (inc i)))
      (do
        ;; (when indenting? (prn "the edit-all happened" i "loops"))
        zloc))))

(defn- transform [form zf & args]
  (let [
        ;; _ (prn "Transform: z/edn")
        e (vary-meta (z/edn form) merge (meta form))

        ;; Longest consuming part:
        o (apply zf e args)
        ;; _ (prn "that was transform: apply zf e args")

        ;; _ (prn "Transform: z/root")
        t (z/root o)]
    t))

(defn- surrounding? [zloc p?]
  (and (p? zloc) (or (nil? (z/left* zloc))
                     (nil? (z/skip z/right* p? zloc)))))

(defn root? [zloc]
  (nil? (z/up* zloc)))

(defn- top? [zloc]
  (and zloc (not= (z/node zloc) (z/root zloc))))

(defn- top [zloc]
  (if (root? zloc) zloc (recur (z/up zloc))))

(defn- clojure-whitespace? [zloc]
  (z/whitespace? zloc))

(defn- surrounding-whitespace? [zloc]
  (and (top? (z/up zloc))
       (surrounding? zloc clojure-whitespace?)))

(defn remove-surrounding-whitespace [form]
  (transform form edit-all surrounding-whitespace? z/remove*))

(defn- element? [zloc]
  (and zloc (not (z/whitespace-or-comment? zloc))))

(defn- reader-macro? [zloc]
  (and zloc (= (n/tag (z/node zloc)) :reader-macro)))

(defn- namespaced-map? [zloc]
  (and zloc (= (n/tag (z/node zloc)) :namespaced-map)))

(defn- missing-whitespace? [zloc]
  (and (element? zloc)
       (not (reader-macro? (z/up* zloc)))
       (not (namespaced-map? (z/up* zloc)))
       (element? (z/right* zloc))))

(defn insert-missing-whitespace [form]
  (transform form edit-all missing-whitespace? z/append-space))

(defn- space? [zloc]
  (= (z/tag zloc) :whitespace))

(defn- comment? [zloc]
  (some-> zloc z/node n/comment?))

(defn- comma? [zloc]
  (some-> zloc z/node n/comma?))

(defn- line-break? [zloc]
  (or (z/linebreak? zloc) (comment? zloc)))

(defn- skip-whitespace [zloc]
  (z/skip z/next* space? zloc))

(defn- skip-whitespace-and-commas [zloc]
  (z/skip z/next* #(or (space? %) (comma? %)) zloc))

(defn- skip-clojure-whitespace
  ([zloc] (skip-clojure-whitespace zloc z/next*))
  ([zloc f] (z/skip f clojure-whitespace? zloc)))

(defn- count-newlines [zloc]
  (loop [zloc' zloc, newlines 0]
    (if (z/linebreak? zloc')
      (recur (-> zloc' z/right* skip-whitespace-and-commas)
             (-> zloc' z/string count (+ newlines)))
      (if (comment? (skip-clojure-whitespace zloc z/left*))
        (inc newlines)
        newlines))))

(defn- final-transform-element? [zloc]
  (nil? (skip-clojure-whitespace (z/next* zloc))))

(defn- consecutive-blank-line? [zloc]
  (and (> (count-newlines zloc) 2)
       (not (final-transform-element? zloc))))

(defn- remove-clojure-whitespace [zloc]
  (if (clojure-whitespace? zloc)
    (recur (z/remove* zloc))
    zloc))

(defn- replace-consecutive-blank-lines [zloc]
  (let [zloc-elem-before (-> zloc
                             skip-clojure-whitespace
                             z/prev*
                             remove-clojure-whitespace)]
    (-> zloc-elem-before
        z/next*
        (z/insert-left* (n/newlines (if (comment? zloc-elem-before) 1 2))))))

(defn remove-consecutive-blank-lines [form]
  (transform form edit-all consecutive-blank-line? replace-consecutive-blank-lines))

(defn- indentation? [zloc]
  (and (line-break? (z/prev* zloc)) (space? zloc)))

(defn- comment-next? [zloc]
  (-> zloc z/next* skip-whitespace comment?))

(defn should-indent? [zloc]
  (and (line-break? zloc) (not (comment-next? zloc))))

(defn- should-unindent? [zloc]
  (and (indentation? zloc) (not (comment-next? zloc))))

(defn unindent [form]
  (transform form edit-all should-unindent? z/remove*))

(def ^:private start-element
  {:meta "^", :meta* "#^", :vector "[",       :map "{"
   :list "(", :eval "#=",  :uneval "#_",      :fn "#("
   :set "#{", :deref "@",  :reader-macro "#", :unquote "~"
   :var "#'", :quote "'",  :syntax-quote "`", :unquote-splicing "~@"
   :namespaced-map "#"})

(defn- prior-line-string [zloc]
  (loop [zloc     zloc
         worklist '()]
    (if-let [p (z/left* zloc)]
      (let [s            (str (n/string (z/node p)))
            new-worklist (cons s worklist)]
        (if-not (includes? s "\n")
          (recur p new-worklist)
          (apply str new-worklist)))
      (if-let [p (z/up* zloc)]
        ;; newline cannot be introduced by start-element
        (recur p (cons (start-element (n/tag (z/node p))) worklist))
        (apply str worklist)))))

(defn- last-line-in-string [^String s]
  (subs s (inc (.lastIndexOf s "\n"))))

(defn- margin [zloc]
  (-> zloc prior-line-string last-line-in-string count))

(defn whitespace [width]
  (n/whitespace-node (apply str (repeat width " "))))

(defn- coll-indent [zloc]
  ;; (prn "coll-indent")
  (dbl 5 "coll indent" (-> zloc z/leftmost* margin)))

(defn- uneval? [zloc]
  (= (z/tag zloc) :uneval))

(defn- index-of [zloc]
  (->> (iterate z/left zloc)
       (remove uneval?)
       (take-while identity)
       (count)
       (dec)))

(defn- list-indent [zloc]
  (dbl 5 "list indent"
       (if (> (index-of zloc) 1)
     (-> zloc z/leftmost* z/right margin)
     (coll-indent zloc))))

(def indent-size 2)

(defn- indent-width [zloc]
  (case (z/tag zloc)
    :list indent-size
    :fn   (inc indent-size)))

(defn- remove-namespace [x]
  (if (symbol? x) (symbol (name x)) x))

(defn pattern? [v]
  (instance? #?(:clj Pattern :cljs js/RegExp) v))

(defn- top-level-form [zloc]
  (->> zloc
       (iterate z/up)
       (take-while (complement root?))
       last))

(defn- token? [zloc]
  (= (z/tag zloc) :token))

(defn- ns-token? [zloc]
  (and (token? zloc)
       (= 'ns (z/sexpr zloc))))

(defn- ns-form? [zloc]
  (dbl 1 "ns form?" (some-> zloc z/down ns-token?)))

(defn- find-namespace [zloc]
  (dbl -1 "find namespace"
       ;; (some-> zloc top (z/find z/next ns-form?) z/down z/next z/sexpr)
       (let [at-top (dbl 1 "1" (top zloc))
             a2 (dbl 1 "2" (when at-top (z/find at-top z/next ns-form?)))
             a3 (dbl 1 "3" (some-> a2 z/down z/next))
             a4 (dbl 1 "4" (when a3 (z/sexpr a3)))]
         a4)))

(def find-namespace-memo
  (memoize
   (fn [zloc]
     (some-> zloc top (z/find z/next ns-form?) z/down z/next z/sexpr))))

(defn- indent-matches? [key sym]
  (if (symbol? sym)
    (cond
      (symbol? key)  (= key sym)
      (pattern? key) (re-find key (str sym)))))

(defn- token-value [zloc]
  (if (token? zloc) (z/sexpr zloc)))

(defn- reader-conditional? [zloc]
  (and (reader-macro? zloc) (#{"?" "?@"} (-> zloc z/down token-value str))))

(defn- form-symbol [zloc]
  (-> zloc z/leftmost token-value))

(defn- index-matches-top-argument? [zloc depth idx]
  (and (> depth 0)
       (= (inc idx) (index-of (nth (iterate z/up zloc) depth)))))

(defn- qualify-symbol-by-alias-map [possible-sym alias-map]
  (when-let [ns-str (namespace possible-sym)]
    (symbol (get alias-map ns-str ns-str) (name possible-sym))))

(defn- qualify-symbol-by-ns-form [possible-sym zloc]
  (when-let [ns-name #_(find-namespace-memo zloc) (doto (-> zloc meta :ns-name) #_(some->> (prn "the ns-name")))]
    (symbol (name ns-name) (name possible-sym))))

(defn- fully-qualified-symbol [zloc alias-map]
  (let [possible-sym (dbl 1 "fqs form symbol"
                          (form-symbol zloc))]
    (if (symbol? possible-sym)
      (or (dbl 1 "fqs q alias"
               (qualify-symbol-by-alias-map possible-sym alias-map))
          (dbl -1 "fqs 1 ns"
               (qualify-symbol-by-ns-form possible-sym zloc)))
      possible-sym)))

(defn- inner-indent [zloc key depth idx alias-map]
  (dbl -1 "inner indent"
       (let [top (nth (iterate z/up zloc) depth)]
     (if (and (or (indent-matches? key (fully-qualified-symbol zloc alias-map))
                  (indent-matches? key (remove-namespace (form-symbol top))))
              (or (nil? idx) (index-matches-top-argument? zloc depth idx)))
       (let [zup (z/up zloc)]
         (+ (margin zup) (indent-width zup)))))))

(defn- nth-form [zloc n]
  (reduce (fn [z f] (if z (f z)))
          (z/leftmost zloc)
          (repeat n z/right)))

(defn- first-form-in-line? [zloc]
  (and (some? zloc)
       (if-let [zloc (z/left* zloc)]
         (if (space? zloc)
           (recur zloc)
           (or (z/linebreak? zloc) (comment? zloc)))
         true)))

(defn- block-indent [zloc key idx alias-map]
  (dbl -1 "block indent"
       (if (dbl -1 "block check 1"
                (or (dbl -1 "block check 1 1"
                         (indent-matches? key (dbl -1 "block check 1 1 fully qual"
                                                   (fully-qualified-symbol zloc alias-map))))
                    (dbl 1 "block check 1 2"
                         (indent-matches? key (remove-namespace (form-symbol zloc))))))
         (let [zloc-after-idx (some-> zloc (nth-form (inc idx)))]
           (if (dbl 1 "block check 2"
                    (and (or (nil? zloc-after-idx) (first-form-in-line? zloc-after-idx))
                         (> (index-of zloc) idx)))
             (dbl -1 "block inner indent"
                  (inner-indent zloc key 0 nil alias-map))
             (dbl 1 "block list indent"
                  (list-indent zloc)))))))

(def default-indents
  (merge (read-resource "cljfmt/indents/clojure.clj")
         (read-resource "cljfmt/indents/compojure.clj")
         (read-resource "cljfmt/indents/fuzzy.clj")))

#_#_#_
(defmulti ^:private indenter-fn
  (fn [sym alias-map [type & args]] type))

(defmethod indenter-fn :inner [sym alias-map [_ depth idx]]
  (fn [zloc] (inner-indent zloc sym depth idx alias-map)))

(defmethod indenter-fn :block [sym alias-map [_ idx]]
  (fn [zloc] (block-indent zloc sym idx alias-map)))

#_(defn safe-nth [coll n]
  (when (< n (count coll))
    (nth coll n)))

(defn- indenter-fn
  [sym alias-map args]
  (let [a1 (get args 1)
        a2 (get args 2)
        type (nth args 0)]
    (case type
      :inner (fn [zloc] (inner-indent zloc sym a1 a2 alias-map))
      :block (fn [zloc] (block-indent zloc sym a1 alias-map)))))

(defn- make-indenter [[key opts] alias-map]
  #_(apply some-fn (map (partial indenter-fn key alias-map) opts))
  (let [coll (mapv #(indenter-fn key alias-map %) opts)]
    (fn [x]
      ;; Note: this always returns the first result
      (dbl 10 "the indenter that has been made"
           (some #(% x) coll)))))

(defn- indent-order [[key _]]
  (cond
    (and (symbol? key) (namespace key)) (str 0 key)
    (symbol? key) (str 1 key)
    (pattern? key) (str 2 key)))

(defn- custom-indent [zloc indents alias-map]
  (if (empty? indents)
    (list-indent zloc)
    (let [
          sorted-indenters (sort-by indent-order indents)
          all-indenters (mapv #(make-indenter % alias-map) sorted-indenters)
          in-num (count all-indenters)
          indenter #_(->> (sort-by indent-order indents)
                          (map #(make-indenter % alias-map))
                          (apply some-fn))
          (fn [x] (loop [i 0]
                    (when (< i in-num)
                      (if-some [r ((nth all-indenters i) x)]
                        (do
                          ;; (prn "found an indenter at" i)
                          r)
                        (do
                          ;; (prn "did not find any indenter")
                          (recur (inc i)))))) )]
      (or (dbl -9 "indenter" (indenter zloc))
          (list-indent zloc)))))

(defn- indent-amount [zloc indents alias-map]
  (let [tag (-> zloc z/up z/tag)
        gp  (-> zloc z/up z/up)]
    (cond
      (reader-conditional? gp) (coll-indent zloc)
      (#{:list :fn} tag)       (custom-indent zloc indents alias-map)
      (= :meta tag)            (indent-amount (z/up zloc) indents alias-map)
      :else                    (coll-indent zloc))))

(defn- indent-line [zloc indents alias-map]
  (let [width (dbl -10 "amount" (indent-amount zloc indents alias-map))]
    ;; (prn "that was indent-amount")
    (if (> width 0)
      (do
        ;; (prn "indent-line: z/insert-right")
        (z/insert-right* zloc (whitespace width)))
      zloc)))

(defn with-ns-meta [form]
  (let [n (find-namespace (z/edn form))]
;; (prn "setting ns-name to" n)
    (with-meta form {:ns-name n})))

(defn indent
  ([form]
   (indent form default-indents))
  ([form indents]
   (transform (with-ns-meta form) edit-all should-indent? #(indent-line % indents {})))
  ([form indents alias-map]
   (transform (with-ns-meta form) edit-all should-indent? #(indent-line % indents alias-map))))

(defn- map-key? [zloc]
  (and (z/map? (z/up zloc))
       (even? (index-of zloc))
       (not (uneval? zloc))
       (not (z/whitespace-or-comment? zloc))))

(defn- preceded-by-line-break? [zloc]
  (loop [previous (z/left* zloc)]
    (cond
      (line-break? previous)
      true
      (z/whitespace-or-comment? previous)
      (recur (z/left* previous)))))

(defn- map-key-without-line-break? [zloc]
  (and (map-key? zloc) (not (preceded-by-line-break? zloc))))

(defn- insert-newline-left [zloc]
  (z/insert-left* zloc (n/newlines 1)))

(defn split-keypairs-over-multiple-lines [form]
  (transform form edit-all map-key-without-line-break? insert-newline-left))

(defn reindent
  ([form]
   (indent (unindent form)))
  ([form indents]
   (indent (unindent form) indents))
  ([form indents alias-map]
   ;; (prn "==== unindenting")
   (reset! indenting? false)
   (let [u (unindent form)]
     ;; (prn "^ unindented ======= indenting v")
     (reset! indenting? true)
     (indent u indents alias-map))))

(defn final? [zloc]
  (and (nil? (z/right* zloc)) (root? (z/up* zloc))))

(defn- trailing-whitespace? [zloc]
  (and (space? zloc)
       (or (z/linebreak? (z/right* zloc)) (final? zloc))))

(defn remove-trailing-whitespace [form]
  (transform form edit-all trailing-whitespace? z/remove*))

(defn- replace-with-one-space [zloc]
  (z/replace* zloc (whitespace 1)))

(defn- non-indenting-whitespace? [zloc]
  (and (space? zloc) (not (indentation? zloc))))

(defn remove-multiple-non-indenting-spaces [form]
  (transform form edit-all non-indenting-whitespace? replace-with-one-space))

(defn reformat-form
  ([form]
   (reformat-form form {}))
  ([form opts]
   (-> form
       (cond-> (:split-keypairs-over-multiple-lines? opts false)
         (split-keypairs-over-multiple-lines))
       (cond-> (:remove-consecutive-blank-lines? opts true)
         remove-consecutive-blank-lines)
       (cond-> (:remove-surrounding-whitespace? opts true)
         remove-surrounding-whitespace)
       (cond-> (:insert-missing-whitespace? opts true)
         insert-missing-whitespace)
       (cond-> (:remove-multiple-non-indenting-spaces? opts false)
         remove-multiple-non-indenting-spaces)
       (cond-> (:indentation? opts true)
         (reindent (:indents opts default-indents)
                   (:alias-map opts {})))
       (cond-> (:remove-trailing-whitespace? opts true)
         remove-trailing-whitespace))))

#?(:clj
   (defn- ns-require-form? [zloc]
     (and (some-> zloc top-level-form ns-form?)
          (some-> zloc z/child-sexprs first (= :require)))))

#?(:clj
   (defn- as-keyword? [zloc]
     (and (= :token (z/tag zloc))
          (= :as (z/sexpr zloc)))))

#?(:clj
   (defn- as-zloc->alias-mapping [as-zloc]
     (let [alias             (some-> as-zloc z/right z/sexpr)
           current-namespace (some-> as-zloc z/leftmost z/sexpr)
           grandparent-node  (some-> as-zloc z/up z/up)
           parent-namespace  (when-not (ns-require-form? grandparent-node)
                               (first (z/child-sexprs grandparent-node)))]
       (when (and (symbol? alias) (symbol? current-namespace))
         {(str alias) (if parent-namespace
                        (format "%s.%s" parent-namespace current-namespace)
                        (str current-namespace))}))))

#?(:clj
   (defn- alias-map-for-form [form]
     (when-let [require-zloc (dbl 1 "alias map find"
                                  (-> form z/edn (z/find z/next ns-require-form?)))]
       (->> (find-all require-zloc as-keyword?)
            (map as-zloc->alias-mapping)
            (apply merge)))))

(defn reformat-string
  ([form-string]
   (reformat-string form-string {}))
  ([form-string options]
   (let [parsed-form (p/parse-string-all form-string)
         alias-map   #?(:clj (or (:alias-map options)
                                 (alias-map-for-form parsed-form))
                        :cljs (:alias-map options))]
     (-> parsed-form
         (reformat-form (cond-> options
                          alias-map (assoc :alias-map alias-map)))
         (n/string)))))

(def default-line-separator
  #?(:clj (System/lineSeparator) :cljs \newline))

(defn normalize-newlines [s]
  (str/replace s #"\r\n" "\n"))

(defn replace-newlines [s sep]
  (str/replace s #"\n" sep))

(defn find-line-separator [s]
  (or (re-find #"\r?\n" s) default-line-separator))

(defn wrap-normalize-newlines [f]
  (fn [s]
    (let [sep (find-line-separator s)]
      (-> s normalize-newlines f (replace-newlines sep)))))

(defn test-edit-all [zloc]
  (edit-all zloc should-indent? identity))
