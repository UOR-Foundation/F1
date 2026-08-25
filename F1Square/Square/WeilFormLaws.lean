/-
F1 square — **component laws of the closed Weil form, I: the pole term** (`WeilFormLaws.lean`):
the improper-integral bricks that turn POINTWISE symmetry/additivity of an integrand into
symmetry/additivity of its improper integral even though the sealed decay constants and Lipschitz
moduli differ syntactically between the two sides —
  • `improper_congr_sched` — block-wise congruent integrands, different constants: reconcile to `K+K'`;
  • `improper_add_sched`   — block-wise additive integrands: `∫(f₁+f₂) = ∫f₁ + ∫f₂`, each at its own
    constant (`decay_add`, certificate weakening, certificate irrelevance, schedule independence);
and their application to `PoleForm` (`PoleForm_symm`, `PoleForm_add_left`, `PoleForm_add_right`),
with the support certificates reconciled (`coreTest_add`).
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.WeilArchSemantic

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- (1) Generic bricks.
-- ===========================================================================

/-- **Block-wise congruent integrands at different constants have the same improper integral.** -/
theorem improper_congr_sched (φ ψ : L2Test) {K K' : Q} (hKd : 0 < K.den) (hK0 : 0 ≤ K.num)
    (hK'd : 0 < K'.den) (hK'0 : 0 ≤ K'.num) (hφ : DecayAt φ K hKd) (hψ : DecayAt ψ K' hK'd)
    (hterm : ∀ m, Req (integralTerm φ.hLd φ.hLn φ.hlip φ.hfc m) (integralTerm ψ.hLd ψ.hLn ψ.hlip ψ.hfc m)) :
    Req (improperIntegral1 φ.hLd φ.hLn φ.hlip φ.hfc hKd hK0 hφ)
        (improperIntegral1 ψ.hLd ψ.hLn ψ.hlip ψ.hfc hK'd hK'0 hψ) := by
  have hKKd : 0 < (add K K').den := add_den_pos hKd hK'd
  have hKK0 : 0 ≤ (add K K').num := Qadd_num_nonneg_loc hK0 hK'0
  have hφ' : DecayAt φ (add K K') hKKd := decay_mono φ hKd hKKd (Qle_self_add hK'0) hφ
  have hψ' : DecayAt ψ (add K K') hKKd := decay_mono ψ hK'd hKKd (Qle_self_add_l hK0) hψ
  refine Req_trans (improperIntegral1_sched _ _ _ _ hKd hK0 hKKd hKK0 hφ hφ') ?_
  refine Req_trans (improperIntegral1_congr_terms _ _ _ _ _ _ _ _ hKKd hKK0 hφ' hψ' hterm) ?_
  exact improperIntegral1_sched _ _ _ _ hKKd hKK0 hK'd hK'0 hψ' hψ

/-- **Block-wise additive integrands: the improper integral is additive**, each side at its own
    constant. -/
theorem improper_add_sched (φ₁ φ₂ φ : L2Test) {K₁ K₂ K : Q}
    (hK₁d : 0 < K₁.den) (hK₁0 : 0 ≤ K₁.num) (hK₂d : 0 < K₂.den) (hK₂0 : 0 ≤ K₂.num)
    (hKd : 0 < K.den) (hK0 : 0 ≤ K.num)
    (h₁ : DecayAt φ₁ K₁ hK₁d) (h₂ : DecayAt φ₂ K₂ hK₂d) (h : DecayAt φ K hKd)
    (hterm : ∀ m, Req (integralTerm φ.hLd φ.hLn φ.hlip φ.hfc m)
      (Radd (integralTerm φ₁.hLd φ₁.hLn φ₁.hlip φ₁.hfc m) (integralTerm φ₂.hLd φ₂.hLn φ₂.hlip φ₂.hfc m))) :
    Req (improperIntegral1 φ.hLd φ.hLn φ.hlip φ.hfc hKd hK0 h)
        (Radd (improperIntegral1 φ₁.hLd φ₁.hLn φ₁.hlip φ₁.hfc hK₁d hK₁0 h₁)
              (improperIntegral1 φ₂.hLd φ₂.hLn φ₂.hlip φ₂.hfc hK₂d hK₂0 h₂)) := by
  -- the common constant Kc = K + (K₁ + K₂), and its double K2 = Kc + Kc
  have hKcd : 0 < (add K (add K₁ K₂)).den := add_den_pos hKd (add_den_pos hK₁d hK₂d)
  have hKc0 : 0 ≤ (add K (add K₁ K₂)).num := Qadd_num_nonneg_loc hK0 (Qadd_num_nonneg_loc hK₁0 hK₂0)
  have hK2d : 0 < (add (add K (add K₁ K₂)) (add K (add K₁ K₂))).den := add_den_pos hKcd hKcd
  have hK20 : 0 ≤ (add (add K (add K₁ K₂)) (add K (add K₁ K₂))).num := Qadd_num_nonneg_loc hKc0 hKc0
  have hK_le : Qle K (add K (add K₁ K₂)) := Qle_self_add (Qadd_num_nonneg_loc hK₁0 hK₂0)
  have hK₁_le : Qle K₁ (add K (add K₁ K₂)) :=
    Qle_trans (add_den_pos hK₁d hK₂d) (Qle_self_add hK₂0) (Qle_self_add_l hK0)
  have hK₂_le : Qle K₂ (add K (add K₁ K₂)) :=
    Qle_trans (add_den_pos hK₁d hK₂d) (Qle_self_add_l hK₁0) (Qle_self_add_l hK0)
  have hKc_le : Qle (add K (add K₁ K₂)) (add (add K (add K₁ K₂)) (add K (add K₁ K₂))) := Qle_self_add hKc0
  have h₁c : DecayAt φ₁ _ hKcd := decay_mono φ₁ hK₁d hKcd hK₁_le h₁
  have h₂c : DecayAt φ₂ _ hKcd := decay_mono φ₂ hK₂d hKcd hK₂_le h₂
  have h₁2 : DecayAt φ₁ _ hK2d := decay_mono φ₁ hKcd hK2d hKc_le h₁c
  have h₂2 : DecayAt φ₂ _ hK2d := decay_mono φ₂ hKcd hK2d hKc_le h₂c
  have h2 : DecayAt φ _ hK2d := decay_mono φ hKd hK2d (Qle_trans hKcd hK_le hKc_le) h
  have hadd : DecayAt (L2Test.add φ₁ φ₂) _ hK2d := decay_add φ₁ φ₂ hKcd h₁c h₂c
  -- φ at K → at K2 → the sum test at K2 → sum of improper integrals at K2 → back to K₁, K₂
  refine Req_trans (improperIntegral1_sched _ _ _ _ hKd hK0 hK2d hK20 h h2) ?_
  refine Req_trans (improperIntegral1_congr_terms _ _ _ _ _ _ _ _ hK2d hK20 h2 hadd
    (fun m => Req_trans (hterm m) (Req_symm (integralTerm_addTest φ₁ φ₂ m)))) ?_
  refine Req_trans (improperIntegral1_add (L2Test.add φ₁ φ₂).hLd (L2Test.add φ₁ φ₂).hLn
    (lip_weaken φ₁.hLd (L2Test.add φ₁ φ₂).hLd (Qle_self_add φ₂.hLn) φ₁.hlip) φ₁.hfc
    (lip_weaken φ₂.hLd (L2Test.add φ₁ φ₂).hLd (Qle_self_add_l φ₁.hLn) φ₂.hlip) φ₂.hfc
    (L2Test.add φ₁ φ₂).hlip (L2Test.add φ₁ φ₂).hfc hK2d hK20
    (decay_weaken_L φ₁ _ _ _ hK2d h₁2) (decay_weaken_L φ₂ _ _ _ hK2d h₂2) hadd) ?_
  refine Radd_congr ?_ ?_
  · exact Req_trans (improperIntegral1_certif_irrel _ _ _ _ _ _ _ _ _ _ _ _)
      (improperIntegral1_sched _ _ _ _ hK2d hK20 hK₁d hK₁0 h₁2 h₁)
  · exact Req_trans (improperIntegral1_certif_irrel _ _ _ _ _ _ _ _ _ _ _ _)
      (improperIntegral1_sched _ _ _ _ hK2d hK20 hK₂d hK₂0 h₂2 h₂)

-- ===========================================================================
-- (2) The pole integrand: pointwise symmetry and additivity.
-- ===========================================================================

theorem poleIntegrand_symm_pt (G : ClosedGeom) (f g : L2Test) (x : Real) :
    Req ((poleIntegrand G f g).f x) ((poleIntegrand G g f).f x) := by
  rw [poleIntegrand_f, poleIntegrand_f]
  exact Rmul_congr (Radd_comm _ _) (Req_refl _)

theorem poleIntegrand_add_left_pt (G : ClosedGeom) (f₁ f₂ g : L2Test) (x : Real) :
    Req ((poleIntegrand G (L2Test.add f₁ f₂) g).f x)
        (Radd ((poleIntegrand G f₁ g).f x) ((poleIntegrand G f₂ g).f x)) := by
  rw [poleIntegrand_f, poleIntegrand_f, poleIntegrand_f]
  refine Req_trans (Rmul_congr (Radd_congr (FTestG_add_left G f₁ f₂ g x) (FTestG_add_right G g f₁ f₂ x))
    (Req_refl _)) ?_
  refine Req_trans (Rmul_congr (Radd_add_add_comm _ _ _ _) (Req_refl _)) ?_
  exact Rmul_distrib_right _ _ _

theorem poleIntegrand_add_right_pt (G : ClosedGeom) (f g₁ g₂ : L2Test) (x : Real) :
    Req ((poleIntegrand G f (L2Test.add g₁ g₂)).f x)
        (Radd ((poleIntegrand G f g₁).f x) ((poleIntegrand G f g₂).f x)) := by
  rw [poleIntegrand_f, poleIntegrand_f, poleIntegrand_f]
  refine Req_trans (Rmul_congr (Radd_congr (FTestG_add_right G f g₁ g₂ x) (FTestG_add_left G g₁ g₂ f x))
    (Req_refl _)) ?_
  refine Req_trans (Rmul_congr (Radd_add_add_comm _ _ _ _) (Req_refl _)) ?_
  exact Rmul_distrib_right _ _ _

/-- The pole integrand's decay as a `DecayAt` (its own sealed constant `poleK`). -/
theorem poleDecayAt (G : ClosedGeom) (f g : L2Test) (hf : CoreTest G f) (hg : CoreTest G g) :
    DecayAt (poleIntegrand G f g) (poleK G f g) (poleK_den G f g) := poleDecay G f g hf hg

/-- Block-wise term congruence from a global pointwise congruence. -/
theorem integralTerm_congr_all (φ ψ : L2Test) (h : ∀ x, Req (φ.f x) (ψ.f x)) (m : Nat) :
    Req (integralTerm φ.hLd φ.hLn φ.hlip φ.hfc m) (integralTerm ψ.hLd ψ.hLn ψ.hlip ψ.hfc m) :=
  integralTerm_congr_ge _ _ _ _ _ _ _ _ m (fun x _ => h x)

-- ===========================================================================
-- (3) THE POLE-TERM LAWS.
-- ===========================================================================

/-- **`PoleForm_symm`**: `PoleForm(f,g) = PoleForm(g,f)`. -/
theorem PoleForm_symm (G : ClosedGeom) (f g : L2Test) (hf : CoreTest G f) (hg : CoreTest G g) :
    Req (PoleForm G f g hf hg) (PoleForm G g f hg hf) := by
  unfold PoleForm
  exact improper_congr_sched _ _ (poleK_den G f g) (poleK_num G f g) (poleK_den G g f) (poleK_num G g f)
    (poleDecayAt G f g hf hg) (poleDecayAt G g f hg hf)
    (integralTerm_congr_all _ _ (poleIntegrand_symm_pt G f g))

/-- **`PoleForm_add_left`**. -/
theorem PoleForm_add_left (G : ClosedGeom) (f₁ f₂ g : L2Test) (h₁ : CoreTest G f₁) (h₂ : CoreTest G f₂)
    (hg : CoreTest G g) :
    Req (PoleForm G (L2Test.add f₁ f₂) g (coreTest_add h₁ h₂) hg)
        (Radd (PoleForm G f₁ g h₁ hg) (PoleForm G f₂ g h₂ hg)) := by
  unfold PoleForm
  exact improper_add_sched _ _ _ (poleK_den G f₁ g) (poleK_num G f₁ g) (poleK_den G f₂ g) (poleK_num G f₂ g)
    (poleK_den G _ g) (poleK_num G _ g) (poleDecayAt G f₁ g h₁ hg) (poleDecayAt G f₂ g h₂ hg)
    (poleDecayAt G _ g (coreTest_add h₁ h₂) hg)
    (fun m => Req_trans (integralTerm_congr_all _ (L2Test.add (poleIntegrand G f₁ g) (poleIntegrand G f₂ g))
      (poleIntegrand_add_left_pt G f₁ f₂ g) m) (integralTerm_addTest _ _ m))

/-- **`PoleForm_add_right`**. -/
theorem PoleForm_add_right (G : ClosedGeom) (f g₁ g₂ : L2Test) (hf : CoreTest G f) (h₁ : CoreTest G g₁)
    (h₂ : CoreTest G g₂) :
    Req (PoleForm G f (L2Test.add g₁ g₂) hf (coreTest_add h₁ h₂))
        (Radd (PoleForm G f g₁ hf h₁) (PoleForm G f g₂ hf h₂)) := by
  unfold PoleForm
  exact improper_add_sched _ _ _ (poleK_den G f g₁) (poleK_num G f g₁) (poleK_den G f g₂) (poleK_num G f g₂)
    (poleK_den G f _) (poleK_num G f _) (poleDecayAt G f g₁ hf h₁) (poleDecayAt G f g₂ hf h₂)
    (poleDecayAt G f _ hf (coreTest_add h₁ h₂))
    (fun m => Req_trans (integralTerm_congr_all _ (L2Test.add (poleIntegrand G f g₁) (poleIntegrand G f g₂))
      (poleIntegrand_add_right_pt G f g₁ g₂) m) (integralTerm_addTest _ _ m))

end UOR.Bridge.F1Square.Square
