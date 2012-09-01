(defn random-entity
  "Creates a random entity (i.e. parent)"
  [genes length]
  (vec (take length (repeatedly #(nth genes (rand-int (count genes)))))))

(defn random-population
  "Creates a random population."
  [genes length pop_size]
  (vec (take pop_size (repeatedly #(random-entity genes length)))))

(defn fitness
  "Calculates the fitness of an entity."
  ([entity target] (fitness entity target 0))
  ([entity target fitness]
    (if (empty? target) fitness
      (recur (rest entity) (rest target) (if (= (first entity) (first target)) (inc fitness) fitness)))))

(defn mutate
  "Mutates a vector."
  [entity genes]
  (assoc entity (rand-int (count entity)) (nth genes (rand-int (count genes)))))

(defn crossover-single
  "Creates a single child by crossing-over two parents."
  [x y pos]
  (vec (concat (subvec x 0 pos) (subvec y pos))))

(defn crossover
  "Creates two children by crossing-over two parents."
  ([x y] (crossover x y (let [rng (dec (count x))] (inc (rand-int rng)))))
  ([x y pos] [(crossover-single x y pos) (crossover-single y x pos)]))

(defn choose-parent
  ([population fitness-map fitness-sum]
    (choose-parent population fitness-map (rand-int fitness-sum) 0 0))
  ([population fitness-map r index current-sum]
    (let [new-sum (+ current-sum (nth fitness-map index))]
      (if (<= r new-sum) (nth population index)
        (recur population fitness-map r (inc index) new-sum)))))

(defn breed-pair
  "Returns a vector of two children."
  [population genes fitness-map fitness-sum p_mutate p_crossover_preservation]
  (let [p1 (choose-parent population fitness-map fitness-sum)
        p2 (choose-parent population fitness-map fitness-sum)
        [c1,c2] (if (> p_crossover_preservation (rand)) [p1 p2] (crossover p1 p2))
        c1m (if (< (rand) p_mutate) (mutate c1 genes) c1)
        c2m (if (< (rand) p_mutate) (mutate c2 genes) c2)
        ] [c1m,c2m]))

(defn breed-population
  "Returns a vector of children the same size as the provided population."
  ([population genes fitness-map p_mutate p_crossover_preservation]
    (let [min-fitness (apply min fitness-map)
          new-fit-map (vec (map #(inc(- % min-fitness)) fitness-map)) ]
          (breed-population population genes new-fit-map (reduce + new-fit-map) p_mutate p_crossover_preservation (/ (count population) 2) [] )))
  ([population genes fitness-map fitness-sum p_mutate p_crossover_preservation it cur]
    (if (= it 0) cur
      (recur population genes fitness-map fitness-sum p_mutate p_crossover_preservation (dec it)
             (apply conj cur (breed-pair population genes fitness-map fitness-sum p_mutate p_crossover_preservation))))))

(defn get-best
  ([population fitness-map] (get-best population fitness-map -1 nil))
  ([population fitness-map best-score best-value]
    (if (empty? population) [best-score best-value]
      (let [cur-score (first fitness-map)
            [new-best-score,new-best-value] (if (< best-score cur-score) [cur-score (first population)] [best-score best-value]) ]
        (recur (rest population) (rest fitness-map) new-best-score new-best-value)))))

(defn ga
  ([genes population fitness-fn acceptable-fn]
    (let [fmap (map fitness-fn population)]
      (ga 1 genes population fmap fitness-fn acceptable-fn 0.2 0.98 (get-best population fmap))))
  ([it genes population fitness-map fitness-fn acceptable-fn p_mutate p_crossover_preservation [best-score best-value]]
    (println "#" it " - (" best-score ") " (apply str best-value))
    (let [new-pop (breed-population population genes fitness-map p_mutate p_crossover_preservation)
          new-fitness-map (map fitness-fn new-pop)
          [new-best-score,new-best-value] (get-best new-pop new-fitness-map) ]
      (if (acceptable-fn new-best-score)
        (apply str new-best-value)
        (recur (inc it) genes new-pop new-fitness-map fitness-fn acceptable-fn p_mutate p_crossover_preservation [new-best-score new-best-value])))))


(def genes "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz .,!")
(def target "What an awesome algorithm this is.")
;(def weights (vec (map #(* % % %) (range 35))))
;(def fitness-fn #(get weights (fitness target %)))
;(def acceptable-fn #(= (get weights (count target)) %))
(def fitness-fn #(fitness target %))
(def acceptable-fn #(= (count target) %))

(println (ga genes (random-population genes (count target) 400) fitness-fn acceptable-fn))
