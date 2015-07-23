(declare-fun array () (Array Int Int))
(declare-fun index () Int)
(declare-fun length () Int)

(declare-fun b1 () Bool)
(declare-fun b2 () Bool)
(declare-fun b3 () Bool)
(declare-fun b4 () Bool)
(declare-fun res1 () (Array Int Int))
(declare-fun res2 () (Array Int Int))
(declare-fun res3 () (Array Int Int))
(declare-fun res4 () (Array Int Int))
(declare-fun resPos1 () Bool)
(declare-fun resPos2 () Bool)
(declare-fun resPos3 () Bool)
(declare-fun resPos4 () Bool)
(declare-fun res () (Array Int Int))
(declare-fun new-array () (Array Int Int))

;(declare-fun is-pos ((Array Int Int) Int Int Int) Bool)
(declare-fun abs ((Array Int Int) Int Int) (Array Int Int))

(define-fun is-pos ((a (Array Int Int)) (length Int) (from Int) (to Int)) Bool
  (forall ((i Int))
    (=> (and (>= i from) (< i length) (< i to))
        (>= (select a i) 0))))

(assert (>= index 0))
(assert (>= length 0))
(assert (is-pos array length 0 index))

(assert (= new-array 
                  (store array index
                    (ite (< (select array index) 0) (- (select array index)) (select array index))
                  )))
(assert (= res (abs new-array length (+ index 1))))

(assert (= b1 (>= index length)))
(assert (=> b1 (= res1 array)))
(assert (=> (not b1) (= res1 res)))

(assert (is-pos res length 0 (+ index 1)))
(assert (not (is-pos res1 length 0 (+ index 1))))

(check-sat)
(get-model)
