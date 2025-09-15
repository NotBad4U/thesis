(set-logic UFLIA)
(declare-sort Idv 0)
(declare-fun Mem (Idv Idv) Bool)
(declare-fun FunApp (Idv Idv) Idv)
(declare-fun TrigEq_Idv (Idv Idv) Bool)

(declare-fun S () Idv)
(declare-fun f () Idv)

;; f ∈ [S → subset S]
(assert (Mem f (FunSet S (Subset S))))

(declare-fun X () Idv)

;; take x ∈ S
(assert (Mem X S)) 

(declare-fun SetSt (Idv) Idv)

(assert
  (!
    (forall ((x Idv) (y Idv))
      (! (= (TrigEq_Idv x y) (= x y))
        :pattern ((TrigEq_Idv x y))))
    :named |ExtTrigEqDef Idv|))

(assert
  (! (forall ((a Idv) (x Idv))
    (!
        (=
            (Mem x (SetSt a))
            (and (Mem x a) (not (Mem x (FunApp f x)))))
    :pattern ((Mem x (SetSt a)))
    :pattern ((Mem x a)
                (SetSt a))))
    :named |SetStDef SetSt|))

;; x ∈ T ∨ x ∉ T
(assert (or (Mem X (SetSt S)) (not (Mem X (SetSt S)))))

(assert (! 
    (not (not (TrigEq_Idv (FunApp f X) (SetSt S))))
    :named |Goal|))
(check-sat)