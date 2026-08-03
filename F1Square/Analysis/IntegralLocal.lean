/-
F1 square — Track 1, item 3 substrate: **interval-local monotonicity of the certified integral**.
`riemannIntegral_le` requires `f ≤ g` *globally*, but the dyadic Riemann sums only sample `[0, 1]`, so
monotonicity holds from `f ≤ g` *on `[0, 1]`* alone (`riemannSum_le` is already local). This local form
is what every decay bound needs: to bound `∫_{m+1}^{m+2} h` by a per-interval constant `c_m`, one
compares `h` to the constant `c_m` only on `[m+1, m+2]` (where `h ≤ c_m`), not globally (where it fails).

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by `scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.IntervalIntegral

namespace UOR.Bridge.F1Square.Analysis

/-- The dyadic sample point `i/(N+1)` lies in `[0, 1]` for `i < N+1`. -/
private theorem dyadic_sample_mem (N i : Nat) (hi : i < N + 1) :
    Rle zero (ofQ (⟨(i : Int), N + 1⟩ : Q) (Nat.succ_pos N))
    ∧ Rle (ofQ (⟨(i : Int), N + 1⟩ : Q) (Nat.succ_pos N)) one :=
  ⟨Rle_zero_of_Rnonneg (Rnonneg_ofQ (Nat.succ_pos N) (Int.ofNat_nonneg i)),
   Rle_ofQ_ofQ (Nat.succ_pos N) (by decide) (by simp only [Qle]; push_cast; omega)⟩

/-- **`∫₀¹ f ≤ ∫₀¹ g` from `f ≤ g` on `[0, 1]` only** (shared modulus `L`). -/
theorem riemannIntegral_le_unit {f g : Real → Real} {L : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlipf : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfcf : ∀ x y, Req x y → Req (f x) (f y))
    (hlipg : ∀ x y, Rle (Rabs (Rsub (g x) (g y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfcg : ∀ x y, Req x y → Req (g x) (g y))
    (hfg : ∀ x, Rle zero x → Rle x one → Rle (f x) (g x)) :
    Rle (riemannIntegral hLd hLn hlipf hfcf) (riemannIntegral hLd hLn hlipg hfcg) := by
  have hZfReg : RReg (fun j => Radd (dyadicR f 0) (genSum (dyadicTerm f) (digammaMidx L j))) :=
    RReg_add_const (dyadicR f 0) _ (dyadicSum_RReg hLd hLn hlipf hfcf)
  have hZgReg : RReg (fun j => Radd (dyadicR g 0) (genSum (dyadicTerm g) (digammaMidx L j))) :=
    RReg_add_const (dyadicR g 0) _ (dyadicSum_RReg hLd hLn hlipg hfcg)
  have hZle : ∀ j, Rle (Radd (dyadicR f 0) (genSum (dyadicTerm f) (digammaMidx L j)))
      (Radd (dyadicR g 0) (genSum (dyadicTerm g) (digammaMidx L j))) := fun j =>
    Rle_trans (Rle_of_Req (Req_symm (dyadicR_eq f (digammaMidx L j))))
      (Rle_trans (riemannSum_le (2 ^ digammaMidx L j - 1)
          (fun i hi => hfg _ (dyadic_sample_mem _ i hi).1 (dyadic_sample_mem _ i hi).2))
        (Rle_of_Req (dyadicR_eq g (digammaMidx L j))))
  refine Rle_trans (Rle_of_Req (Req_symm
      (Rlim_add_const (dyadicR f 0) _ (dyadicSum_RReg hLd hLn hlipf hfcf) hZfReg))) ?_
  exact Rle_trans (Rlim_le_seq hZfReg hZgReg hZle)
    (Rle_of_Req (Rlim_add_const (dyadicR g 0) _ (dyadicSum_RReg hLd hLn hlipg hfcg) hZgReg))

/-- **`∫₀¹ f ≈ ∫₀¹ g` from `f ≈ g` on `[0, 1]` only** (shared modulus `L`) — the unit-local
    congruence, by antisymmetry of the unit-local monotonicity. The lemma every evaluation of a
    clamped integrand runs through: the integrand need only agree with its closed form on the
    integration domain. -/
theorem riemannIntegral_congr_unit {f g : Real → Real} {L : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlipf : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfcf : ∀ x y, Req x y → Req (f x) (f y))
    (hlipg : ∀ x y, Rle (Rabs (Rsub (g x) (g y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfcg : ∀ x y, Req x y → Req (g x) (g y))
    (hfg : ∀ x, Rle zero x → Rle x one → Req (f x) (g x)) :
    Req (riemannIntegral hLd hLn hlipf hfcf) (riemannIntegral hLd hLn hlipg hfcg) :=
  Rle_antisymm
    (riemannIntegral_le_unit hLd hLn hlipf hfcf hlipg hfcg
      (fun x h0 h1 => Rle_of_Req (hfg x h0 h1)))
    (riemannIntegral_le_unit hLd hLn hlipg hfcg hlipf hfcf
      (fun x h0 h1 => Rle_of_Req (Req_symm (hfg x h0 h1))))

/-- **`∫_a^{a+w} f ≤ ∫_a^{a+w} g` from `f ≤ g` on the affine image of `[0,1]`** (i.e. on `[a, a+w]`),
    `w ≥ 0`, shared modulus `L`. -/
theorem riemannIntegralI_le_unit {f g : Real → Real} {L : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlipf : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfcf : ∀ x y, Req x y → Req (f x) (f y))
    (hlipg : ∀ x y, Rle (Rabs (Rsub (g x) (g y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfcg : ∀ x y, Req x y → Req (g x) (g y))
    (a w : Q) (ha : 0 < a.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (hfg : ∀ x, Rle zero x → Rle x one → Rle (f (affineMap a w ha hw x)) (g (affineMap a w ha hw x))) :
    Rle (riemannIntegralI hLd hLn hlipf hfcf a w ha hw hwn)
        (riemannIntegralI hLd hLn hlipg hfcg a w ha hw hwn) :=
  Rmul_le_Rmul_left (Rnonneg_ofQ hw hwn)
    (riemannIntegral_le_unit _ _ _ _ _ _ (fun x hx0 hx1 => hfg x hx0 hx1))

end UOR.Bridge.F1Square.Analysis
