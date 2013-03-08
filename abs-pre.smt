(declare-fun array () (Array Int Int))
(declare-fun index () Int)
(declare-fun length () Int)

(declare-fun b1 () Bool)
(declare-fun res1 () (Array Int Int))
(declare-fun res () (Array Int Int))
(declare-fun new-array () (Array Int Int))

;(declare-fun is-pos ((Array Int Int) Int Int Int) Bool)
(define-fun is-pos ((a (Array Int Int)) (length Int) (from Int) (to Int)) Bool
  (forall ((i Int))
    (=> (and (>= i from) (< i length) (< i to))
        (>= (select a i) 0))))

(declare-fun abs ((Array Int Int) Int Int) (Array Int Int))

(assert (>= index 0))
(assert (>= length 0))
(assert (is-pos array length 0 index))

(assert (< index length))
(assert (= new-array 
                  (store array index
                    (ite (< (select array index) 0) (- (select array index)) (select array index))
                  )))
(assert (not (is-pos new-array length 0 (+ index 1))))

(check-sat)
(get-model)
