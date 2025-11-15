symbol U : Set;
symbol a : τ U;
symbol b : τ U;
symbol p : τ (U ⤳ o);

symbol p_2 ≔ (p b);
symbol p_4 ≔ (p a);
symbol p_6 ≔ (p a = p b);

symbol a2 : $\prfcl$ (¬ (p b) ⟇ ▩);
symbol a1 : $\prfcl$ (a = b ⟇ ▩);
symbol a0 : $\prfcl$ (p a ⟇ ▩);ls

opaque symbol t1 : $\prfcl$ (¬ p_6 ⟇ ¬ p_4 ⟇ p_2 ⟇ ▩) ≔ 
begin
apply equiv_pos2;
end;

opaque symbol t2 : $\prfcl$ (p_6 ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
apply feq p (headcl a1);
end;

opaque symbol t3 : $\prfcl$ (p_2 ⟇ ▩) ≔ 
begin
have t1_t2 : $\prfcl$ (¬ p_4  ⟇ p_2 ⟇ ▩) {
    apply disj_resolutionN1 0 0 t1 t2 $\top_i$ $\top_i$ (eq_refl _);
};
have t1_t2_a0 : $\prfcl$ (p_2 ⟇ ▩) {
    apply disj_resolutionN1 0 0 t1_t2 a0 $\top_i$ $\top_i$ (eq_refl _);
};
refine t1_t2_a0;
end;

opaque symbol t4 : $\prfcl$ ▩ ≔ 
begin
have a2_t3 : $\prfcl$ ▩ {
    apply disj_resolutionN1 0 0 a2 t3 $\top_i$ $\top_i$ (eq_refl _);
};
refine a2_t3;
end;
