opaque symbol t2: $\pid$ ((¬ (3 < x) ∨ ¬ (x = 2)) ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    rewrite Zinv_lt_eq;
    rewrite Z_diff_gt_Z0_eq (— 3) (— x);
    rewrite Z_diff_eq_Z0_eq (x) 2;
    rewrite Zgt_le_succ_r_eq ((— 3) - (— x)) 0;
    rewrite Zmult_ge_compat_eq 1 ((— 3) - (— x)) ((0 + 1));
    rewrite Zmult_eq_compat_eq (— 1) (x - 2) 0;
    rewrite imp_eq_or; assume H0 H1;
    
    set H0l' ≔ (1 * ((— 3) - (— x))); set H0r' ≔ (1 * (0 + 1));
    set H1l' ≔ ((— 1) * (x - 2)); set H1r' ≔ ((— 1) * 0);
    have H1': $\pic$ (H1l' ≥ H1r') { refine Z_eq_implies_ge H1 }; remove H1;
    have contra : $\pic$ ((⇓ (⇑ (H0l' + H1l'))) ≥ (⇓ (⇑ (H0r' + H1r')))){
        rewrite ⇓_⇑;
        rewrite ⇓_⇑; 
        apply (Zsum_geq_s H0l' H0r' H1l' H1r' H0 H1');
    };
    apply contra; apply ⊤ᶜᵢ;
};