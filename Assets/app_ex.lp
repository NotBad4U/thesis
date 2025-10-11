require open lambdapi.Alethe;
require open lambdapi.Simplify;
require open lambdapi.Rare;
require open lambdapi.Lia;
require open lambdapi.Clause;

symbol S1 : Set;
symbol S3 : Set;
symbol S4 : Set;
symbol S5 : Set;
symbol S6 : Set;
symbol S39 : Set;
symbol S46 : Set;

symbol f1 : τ S1;
symbol f2 : τ S1;
symbol f5 : τ (S3 ⤳ S4 ⤳ S1);
symbol f6 : τ (S5 ⤳ S3 ⤳ S3);
symbol f7 : τ S5;
symbol f8 : τ (S6 ⤳ S4 ⤳ S5);
symbol f63 : τ (S39 ⤳ S3 ⤳ S4);
symbol f72 : τ S39;
symbol f80 : τ (S46 ⤳ S4 ⤳ S39);
symbol f81 : τ S46;

symbol p_2 ≔ ((∀ x : τ S1, ∀ y : τ S1, x = y) ⇒ f2 = f1) = (∀ x : τ S1, ∀ y : τ S1, x = y) ⇒ f1 = f2;
symbol p_3 ≔ ((∀ x : τ S1, ∀ y : τ S1, x = y) ⇒ f2 = f1);
symbol p_4 ≔ (∀ x : τ S1, ∀ y : τ S1, x = y);
symbol p_5 ≔ (f2 = f1);
symbol p_6 ≔ (∀ x : τ S1, ∀ y : τ S1, x = y) ⇒ f1 = f2;
symbol p_7 ≔ f1 = f2;
symbol p_11 ≔ ¬ (∀ x : τ S1, ∀ y : τ S1, x = y);

opaque symbol t0 : $\prfcl$ (¬ (p_3 = p_6)  ⟇ ¬ p_3  ⟇ p_6 ⟇ ▩) ≔ 
begin apply equiv_pos2; end;

opaque symbol t1 : $\prfcl$ (p_4 = p_4 ⟇ ▩) ≔ 
begin apply $\lor_{i1}$; reflexivity; end;

opaque symbol t2 : $\prfcl$ (p_5 = p_7 ⟇ ▩) ≔ 
begin apply $\lor_{i1}$; apply eq-symm f2 f1; end;

opaque symbol t3 : $\prfcl$ (p_2 ⟇ ▩) ≔ 
begin apply $\lor_{i1}$; apply (cong2 (⇒) (headcl t1) (headcl t2)); end;

opaque symbol t4 : $\prfcl$ (p_3 ⟇ p_4 ⟇ ▩) ≔ 
begin apply implies_neg1; end;

symbol t5_a0 : $\prfcl$ (p_4 ⟇ ▩);

opaque symbol t5_t0 : $\prfcl$ ((p_11 ∨ p_5) ⟇ ▩) ≔ 
begin
apply $\lor_{i1}$;
apply imply_to_or;
assume H;
refine (H f2 f1);
end;

opaque symbol t5_t1 : $\prfcl$ (p_11 ⟇ p_5 ⟇ ▩) ≔ 
begin
refine (¬ (∀ x : τ S1, ∀ y : τ S1, x = y) ⸬ f2 = f1 ⸬ □) _;
simplify;
eval #repeat_or_id_r ;
refine (headcl t5_t0);
end;

opaque symbol t5_t2 : $\prfcl$ (p_5 ⟇ ▩) ≔ 
begin
have t5_t1_t5_a0 : $\prfcl$ (p_5 ⟇ ▩) {
    apply resolutionL 0 0 t5_t1 t5_a0 $\top_i$ $\top_i$ (eq_refl _);
};
refine t5_t1_t5_a0;
end;

opaque symbol t5 : $\prfcl$ (¬ p_4 ⟇ p_5 ⟇ ▩) ≔ 
begin
apply $\lor_{i2}$;
apply $\lor_{i1}$;
apply (headcl t5_t2);
end;

opaque symbol t6 : $\prfcl$ (p_3 ⟇ p_5 ⟇ ▩) ≔ 
begin
have t4_t5 : $\prfcl$ (p_3  ⟇ p_5 ⟇ ▩) {
    apply resolutionR 1 0 t4 t5 $\top_i$ $\top_i$ (eq_refl _);
};
refine t4_t5;
end;

opaque symbol t7 : $\prfcl$ (p_3 ⟇ (¬ p_5 ⟇ ▩) ≔ 
begin apply implies_neg2; end;

opaque symbol t8 : $\prfcl$ (p_3 ⟇ p_3 ⟇ ▩) ≔ 
begin
have t6_t7 : $\prfcl$ (p_3  ⟇ p_3 ⟇ ▩) {
    apply resolutionR 1 1 t6 t7 $\top_i$ $\top_i$ (eq_refl _);
};
refine t6_t7;
end;

opaque symbol t9 : $\prfcl$ (p_3 ⟇ ▩) ≔ 
begin
set ir ≔ reify_cl ((∀ (x : τ S1), ∀ (y : τ S1), x = y) ⇒ f2 = f1
    ⟇ ((∀ (x : τ S1), ∀ (y : τ S1), x = y)) ⇒ f2 = f1
    ⟇ ▩
);
have H : $\prf$ (
  cl2disj (((∀ x : τ S1, ∀ y : τ S1, x = y) ⇒ f2 = f1) ⟇ (∀ x : τ S1, ∀ y : τ S1, x = y) ⇒ f2 = f1 ⟇ ▩)
  = 
  cl2disj (((∀ x : τ S1, ∀ y : τ S1, x = y) ⇒ f2 = f1) ⟇ ▩)
) {
    change $\prf$ (($\Uparrow$ (ir ₂) (ir ₁)) = (cl2disj ((∀ x : τ S1, ∀ y : τ S1, x = y) ⇒ f2 = f1 ⟇ ▩)));
    rewrite left  contraction_correct;
    reflexivity;
};
refine subst_equiv_clause H t8;
end;

opaque symbol t10 : $\prfcl$ (p_6 ⟇ ▩) ≔ 
begin
have t0_t3 : $\prfcl$ (¬ p_3 ⟇ p_6 ⟇ ▩) {
    apply resolutionL 0 0 t0 t3 $\top_i$ $\top_i$ (eq_refl _);
};
have t0_t3_t9 : $\prfcl$ (p_6 ⟇ ▩) {
    apply resolutionL 0 0  t0_t3 t9 $\top_i$ $\top_i$ (eq_refl _);
};
refine t0_t3_t9;
end;

opaque symbol t11 : $\prfcl$ (p_11 ⟇ p_7 ⟇ ▩) ≔ 
begin
apply implies (headcl t10);
end;

symbol a2 : $\prfcl$ (p_4 ⟇ ▩);

symbol a0 : $\prfcl$ (¬ p_7 ⟇ ▩);

opaque symbol t13 : $\prfcl$ ▩ ≔ 
begin
have t11_a2 : $\prfcl$ (p_7 ⟇ ▩) {
    apply resolutionL 0 0 t11 a2 $\top_i$ $\top_i$ (eq_refl _);
};
have t11_a2_a0 : $\prfcl$ ▩ {
    apply resolutionR 0 0 t11_a2 a0 $\top_i$ $\top_i$ (eq_refl _);
};
refine t11_a2_a0;
end;