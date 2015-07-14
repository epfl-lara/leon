(declare-fun start!1 () Bool)

(assert start!1)

(declare-datatypes () ( (CoinDist!2 (CoinDist!3 (pHead!1 Real))) ))

(declare-fun c1!0 () CoinDist!2)

(declare-fun c2!0 () CoinDist!2)

(declare-datatypes () ( (CoinsJoinDist!1 (CoinsJoinDist!2 (hh!1 Real) (ht!1 Real) (th!1 Real) (tt!1 Real))) ))

(declare-fun lt!2 () CoinsJoinDist!1)

(declare-fun isDist!1 (CoinsJoinDist!1) Bool)

(assert (and (>= (pHead!1 c1!0) 0) (<= (pHead!1 c1!0) 1) (>= (pHead!1 c2!0) 0) (<= (pHead!1 c2!0) 1)))

(assert (= lt!2 (CoinsJoinDist!2 (* (pHead!1 c1!0) (pHead!1 c2!0)) (* (pHead!1 c1!0) (- 1 (pHead!1 c2!0))) (* (- 1 (pHead!1 c1!0)) (pHead!1 c2!0)) (* (- 1 (pHead!1 c1!0)) (- 1 (pHead!1 c2!0))))))


(assert (not 
          (and (>= (hh!1 lt!2) 0) (<= (hh!1 lt!2) 1)
               (>= (ht!1 lt!2) 0) (<= (ht!1 lt!2) 1) 
               (>= (th!1 lt!2) 0) (<= (th!1 lt!2) 1) 
               (>= (tt!1 lt!2) 0) (<= (tt!1 lt!2) 1)
               (= (+ (hh!1 lt!2) (ht!1 lt!2) (th!1 lt!2) (tt!1 lt!2)) 1))))


(check-sat)

