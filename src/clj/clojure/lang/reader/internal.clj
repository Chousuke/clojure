(ns clojure.lang.reader.internal)
 
(defn namespace-for [sym]
  (let [ns-sym (symbol sym)]
    (or (.lookupAlias *ns* ns-sym) 
        (clojure.lang.Namespace/find ns-sym))))

(defn var->symbol [#^clojure.lang.Var v]
  (symbol (str (.ns v)) (str (.sym v))))

(defn resolve-symbol [sym]
  (let [ns   (when (.getNamespace sym)
               (namespace-for (.getNamespace sym)))
        name (str (name sym))
        res  (resolve sym)]
  (cond
    (and res (class? res)) (symbol (.getCanonicalName res))
    (and res (var? res)) (var->symbol res)  
    (not ns) (symbol (str *ns*) name)
    :else (symbol (str ns) name))))

(def *autofn-syms* nil)

(defn- get-or-set! [index themeta]
  (if-let [sym (*autofn-syms* index)]
    sym
    (let [sym (with-meta (gensym (str "p" index "__")) themeta)]
      (when (and (number? index) 
                 (> index (:max *autofn-syms* -1)))
        (set! *autofn-syms* (assoc *autofn-syms* :max index)))
      (set! *autofn-syms* (assoc *autofn-syms* index sym))
      sym)))

(defn- parse-autoarg [form]
  (cond
    (vector? form) (vec (map parse-autoarg form))
    (map? form) (into {} (map parse-autoarg form))
    (set? form) (into #{} (map parse-autoarg form))
    (seq? form) (doall (map parse-autoarg form))
    (= form '%) (get-or-set! 1 ^form)
    (= form '%&) (get-or-set! 'rest ^form)
    (= (first (str form)) \%) 
    (try (get-or-set! (Integer/parseInt (apply str (rest (str form)))) ^form) 
         (catch NumberFormatException e 
           form))
    :else form))


(defn autofn* [form]
  (let [gen-positional-params 
        (fn [max-idx] 
          (map #(*autofn-syms* % (gensym (str "p" % "__")))
               (range 1 (inc max-idx))))
 
        nform (doall (map parse-autoarg form))
        args
        (concat 
         (gen-positional-params (:max *autofn-syms* 0)) 
         (when-let [r (*autofn-syms* 'rest)]
           (list '& r)))]
    `(fn* ~(vec args) ~nform)))

;; syntax-quote*

(def #^{:private true} *within-seq* false)
(def #^{:private true} *sq-gensyms* nil)

(defn is-call? {:private true} [operator form]
  (when (seq? form)
    (.equals operator (first form))))

(defn real-namespace {:private true} [ns-name]
  (if ns-name
    (str ((.getAliases *ns*) (symbol ns-name) ns-name))
    ns-name))

(defn remove-dot {:private true} [the-name]
  (if (.endsWith the-name ".")
    (.substring the-name 0 (dec (.length the-name)))
    the-name))

(defn var->sym {:private true} [v]
  (symbol (str (.ns v)) (str (.sym v))))

(defn qualify-symbol
  "Works all kinds of magic to resolve a symbol to its fully qualified form"
  {:private true}
  [sym]
  (let [the-ns (real-namespace (namespace sym))
        the-name (remove-dot (name sym))
        ns-res (when the-ns (.getMapping *ns* (symbol the-ns)))
        res (.getMapping *ns* (symbol the-name))]

    (cond
      ;; there is no need to care about the namespace in this case;
      ;; the original syntax-quote did not resolve names containing dots
      ;; No "and" available yet...
      (.startsWith (name sym) ".")
      , sym
      (when (not res)
        (.contains (name sym) "."))
      , sym
      (var? res)         (var->sym res)
      (class? ns-res)    (symbol (.getName ns-res) the-name)
      (when (not the-ns)
        (class? res))    (symbol (str (.getName res)
                                      (when (.endsWith (name sym) ".") ".")))
      the-ns             (symbol the-ns the-name)
      :else              (symbol (str *ns*) the-name))))

(defn sq-w
  "syntax-quote helper; everything is wrapped in a list
  so that splicing things is easier"
  {:private true}
  ([form]
     (if *within-seq*
       (list 'clojure.core/list form)
       form))
  ([quote? form]
     (if *within-seq*
       (list 'clojure.core/list (list 'quote form))
       (list 'quote form))))

(def syntax-quote*)

(defn sq-seq 
  {:private true}
  ([form]
     (try
      (clojure.lang.Var/pushThreadBindings {#'*within-seq* true})
      ;; loop enforces strictness
      (if (seq form)
        (list 'clojure.core/seq (cons 'clojure.core/concat (loop [f form a []]
                                                             (if (seq f)
                                                               (recur (next f) (conj a (syntax-quote* (first f))))
                                                               a))))
        (list 'list))
      (finally
       (clojure.lang.Var/popThreadBindings)))))

(defn sq-sym
  {:private true} 
  [sym]
  (if (not (.endsWith (name sym) "#"))
    (with-meta (qualify-symbol sym) ^sym)
    (let [auto (*sq-gensyms* (name sym))]
      (if auto
        auto
        (let [new-sym 
              (with-meta
                (gensym (apply str (concat (butlast (name sym)) "__auto__")))
                ^sym)]
          (set! *sq-gensyms* (assoc *sq-gensyms* (name sym) new-sym))
          new-sym)))))  
  
(defn syntax-quote*
  ;{:private true} 
  [form]
  (cond
    (special-symbol? form) (sq-w :q form)
    (is-call? 'clojure.core/unquote form) 
    , (sq-w (second form))
    (is-call? 'clojure.core/unquote-splicing form) 
    , (if *within-seq* 
        (second form)
        (throw (IllegalStateException. "Splice not in sequential collection"))) 
     
    (is-call? 'clojure.core/syntax-quote form) (sq-w :q form)
    (symbol? form) (sq-w :q (sq-sym form))
    (vector? form) (sq-w (list 'clojure.core/apply 'clojure.core/vector (sq-seq form)))
    (map? form) (sq-w (list 'clojure.core/apply 'clojure.core/hash-map 
                         (sq-seq (apply concat (seq form)))))
    (set? form) (sq-w (list 'clojure.core/apply 'clojure.core/hash-set (sq-seq form)))
    (seq? form) (sq-w (sq-seq form))
    (keyword? form) (sq-w form)
    (string? form) (sq-w form)
    (instance? java.lang.Number form) (sq-w form)
    (instance? Character form) (sq-w form)
    :else (sq-w (list 'quote form))))

