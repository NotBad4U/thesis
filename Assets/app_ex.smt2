(set-logic UF)

(declare-sort S1 0)
(declare-sort S3 0)
(declare-sort S4 0)
(declare-sort S5 0)
(declare-sort S6 0)
(declare-sort S39 0)
(declare-sort S46 0)

(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f5 (S3 S4) S1)
(declare-fun f6 (S5 S3) S3)
(declare-fun f7 () S5)
(declare-fun f8 (S6 S4) S5)
(declare-fun f63 (S39 S3) S4)
(declare-fun f72 () S39)
(declare-fun f80 (S46 S4) S39)
(declare-fun f81 () S46)

(assert (not (= f1 f2)))
(assert (forall ((?v0 S4) (?v1 S3)) 
    (= 
        (f63 (f80 f81 ?v0) ?v1) 
        (ite 
            (exists ((?v0 S4)) 
                (and 
                    (= (f5 ?v1 ?v0) f1) 
                    (forall ((?v3 S4)) (=> (= (f5 ?v1 ?v3) f1) (= ?v3 ?v0))))) 
            (f63 f72 ?v1)
            ?v0
        )
    )
))
(assert (forall ((x S1) (y S1)) (= x y)))
(check-sat)
(get-proof)