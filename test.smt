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

(declare-fun is-pos ((Array Int Int) Int Int Int) Bool)
(declare-fun abs ((Array Int Int) Int Int) (Array Int Int))

;precondition
(assert (>= index 0))
(assert (>= length 0))
(assert (is-pos array length 0 index))
;(assert b3)
(assert (= b3 (or (>= 0 index)) (>= 0 length)))
(assert (=> b3 (= resPos1 true)))
(assert (=> (not b3) (= resPos1 
  (and (>= (select array 0) 0) (is-pos array length 1 index)))))
(assert resPos1)

;body as res1
;(assert b1)
(assert (= b1 (>= index length)))
(assert (=> b1 (= res1 array)))
(assert (=> (not b1) (= res1 (abs (store array index 0) length (+ index 1)))))

;postcondition
;(assert b2)
(assert (= b2 (or (>= 0 (+ index 1)) (>= 0 length))))
(assert (=> b2 (= resPos2 true)))
(assert (=> (not b2) (= resPos2 
  (and (>= (select array 0) 0) (is-pos array length 1 (+ index 1))))))
(assert (not resPos2))

(check-sat)
