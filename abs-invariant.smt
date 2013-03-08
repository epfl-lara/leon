(declare-fun array () (Array Int Int))
(declare-fun index () Int)
(declare-fun to () Int)
(declare-fun length () Int)

(declare-fun b1 () Bool)
(declare-fun res1 () Bool)
(declare-fun res () Bool)

(declare-fun isPos ((Array Int Int) Int Int Int) Bool)
(define-fun is-pos ((a (Array Int Int)) (length Int) (from Int) (to Int)) Bool
  (forall ((i Int))
    (=> (and (>= i from) (< i length) (< i to))
        (>= (select a i) 0))))

(assert (>= index 0))
(assert (>= length 0))

;(assert b1)
(assert (= b1 (or (>= index to) (>= index length))))
(assert (=> b1 res1))
(assert (=> (not b1) 
  (= res1 
    (and 
      (>= (select array index) 0)
      (isPos array length (+ index 1) to)))))

(assert (= (is-pos array length (+ index 1) to) (isPos array length (+ index 1) to)))

(assert (not (= res1 (is-pos array length index to))))

(check-sat)
(get-model)
