(declare-fun c1 () Real)
(declare-fun c2 () Real)
(declare-fun hh () Real)
(declare-fun ht () Real)
(declare-fun th () Real)
(declare-fun tt () Real)

(assert (and (>= c1 0) (<= c1 1) (>= c2 0) (<= c2 1)))

(assert (= hh (* c1       c2)))
(assert (= ht (* c1       (- 1 c2))))
(assert (= th (* (- 1 c1) c2)))
(assert (= tt (* (- 1 c1) (- 1 c2))))

(assert (not 
          (and (>= hh 0) (<= hh 1)
               (>= ht 0) (<= ht 1)
               (>= th 0) (<= th 1)
               (>= tt 0) (<= tt 1)
               (= (+ hh ht th tt) 1))))


(check-sat)
