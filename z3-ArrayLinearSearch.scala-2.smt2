(declare-fun b!988 () Bool)
(declare-fun e!990 () Bool)
(declare-fun index!234 () (_ BitVec 32))
(declare-fun x!233 () Int)
(declare-fun e!987 () Bool)
(declare-datatypes () ( (array!993 (array!993!994 (size!995 (_ BitVec 32)) (content!996 (Array (_ BitVec 32) Int)))) ))
(declare-fun a!232 () array!993)
(declare-fun i!997 () (_ BitVec 32))
(declare-fun i!998 () (_ BitVec 32))
(declare-fun b!989 () Bool)
(declare-fun b!991 () Bool)
(declare-fun b!992 () Bool)
(declare-fun existsRec!235 (array!993 Int (_ BitVec 32)) Bool)


(assert 
  (not (=> 
    (and 
      (bvsgt (size!995 a!232) #x00000000) 
      (bvsgt (size!995 a!232) #x00000000) 
      (bvsge index!234 #x00000000) 
      (bvslt index!234 (size!995 a!232)) 
      (forall ((i!997 (_ BitVec 32))) (=> (and (bvsge i!997 #x00000000) (bvslt i!997 index!234)) (not (= (select (content!996 a!232) i!997) x!233)))) 
      (bvsge (size!995 a!232) #x00000000))
    (or 
      e!987 
      (and 
        ;(= index!234 (bvsub (size!995 a!232) #x00000001)) 
        ;(= index!234 (bvsub (size!995 a!232) #x00000001)) 
        (not (= (select (content!996 a!232) index!234) x!233)) 
        (forall ((i!998 (_ BitVec 32))) 
          (=> 
            (and 
              (bvsge i!998 #x00000000) 
              (bvslt i!998 index!234))
            (not (= (select (content!996 a!232) i!998) x!233))))))
  ))
)

(assert (=> b!988 (= e!990 false)))

(assert (= b!989 (= (select (content!996 a!232) index!234) x!233)))

(assert (or (or (not b!989) (not b!989)) (not b!991)))

(assert (or (or b!989 b!989) b!991))

(assert (and (and (bvsge index!234 #x00000000) (bvsge index!234 #x00000000)) (bvslt index!234 (size!995 a!232))))

(assert (=> b!989 (= e!987 true)))

(assert (=> b!991 (= e!987 e!990)))

(assert (=> b!991 (= b!988 (= index!234 (bvsub (size!995 a!232) #x00000001)))))

(assert (=> b!991 (or (or (not b!988) (not b!988)) (not b!992))))

(assert (=> b!991 (or (or b!988 b!988) b!992)))

;(assert (=> b!992 (= e!990 (existsRec!235 a!232 x!233 (bvadd index!234 #x00000001)))))

(push 1)

(assert (not b!992))

(check-sat)

(pop 1)
