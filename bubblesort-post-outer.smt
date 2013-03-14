(declare-fun array () (Array Int Int))
(declare-fun index () Int)
(declare-fun index2 () Int)
(declare-fun length () Int)

(declare-fun b1 () Bool)
(declare-fun res1 () (Array Int Int))
(declare-fun res () (Array Int Int))
(declare-fun new-array () (Array Int Int))

(define-fun is-sorted ((a (Array Int Int)) (length Int) (from Int)) Bool
  (forall ((i Int))
    (=> (and (> i 0) (> i from) (< i length))
        (<= (select a (- i 1)) (select a i)))))

(define-fun is-partitioned ((a (Array Int Int)) (length Int) (index Int)) Bool
    (and (is-sorted a length index)
         (forall ((i Int))
            (=> (and (>= i 0) (< i length) (< i index))
                (<= (select a i) (select a index)))))
)
(define-fun is-top ((a (Array Int Int)) (length Int) (index Int)) Bool
   (forall ((i Int))
      (=> (and (>= i 0) (< i length) (< i index))
          (<= (select a i) (select a index)))))

(declare-fun sort ((Array Int Int Int) Int) (Array Int Int))

(assert (>= length 0))
(assert (>= index 0))
(assert (>= index2 0))
(assert (< index length))
(assert (< index2 index))

(assert (is-top array length index2))
(assert (is-partitioned array length index))

(assert (= b1 (select array index2) (select array (+ index2 1))))
(assert (=> b1 (= res1
  (store
    (store array index2 (select array (+ index2 1)))
    (+ index2 1)
    (select array index2)))))
(assert (=> (not b1) (= res1 array)))

;(assert (= b1 (<= index 0)))
;(assert (=> b1 (= res1 array)))
;
;(assert (=> (not b1)
;            (is-partitioned new-array length (- index 1))))
;
;(assert (=> (not b1) (= res1 new-array)))

(assert (not (is-top res1 length (+ index2 1))))

(check-sat)
(get-model)
