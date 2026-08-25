/-
F1 square — **translation of tests and windows** (`WeilShiftTest.lean`): the shifted test
`(shiftTest δ φ)(u) = φ(u + δ)` (an `L2Test` with φ's own certificates — translation is an isometry)
and THE WINDOW TRANSLATION `∫_{[a, a+w]} φ(·+δ) = ∫_{[a+δ, a+δ+w]} φ` (the affine pullbacks agree
pointwise).  Substrate for the far translation `x = u + 1` and for the lower-end truncations.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.WeilArchKern

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

/-- `(x + d) − (y + d) = x − y`. -/
theorem add_shift_iso_gen (x y d : Real) : Req (Rsub (Radd x d) (Radd y d)) (Rsub x y) :=
  Req_trans (Rsub_Radd_Radd x d y d)
    (Req_trans (Radd_congr (Req_refl (Rsub x y)) (Radd_neg d)) (Radd_zero (Rsub x y)))

/-- **The shifted test** `u ↦ φ(u + δ)`. -/
def shiftTest (δ : Q) (hδd : 0 < δ.den) (φ : L2Test) : L2Test where
  f := fun u => φ.f (Radd u (ofQ δ hδd))
  L := φ.L
  M := φ.M
  hLd := φ.hLd
  hLn := φ.hLn
  hMd := φ.hMd
  hMn := φ.hMn
  hlip := fun x y =>
    Rle_trans (φ.hlip (Radd x (ofQ δ hδd)) (Radd y (ofQ δ hδd)))
      (Rle_of_Req (Rmul_congr (Req_refl _) (Rabs_congr (add_shift_iso_gen x y _))))
  hfc := fun x y h => φ.hfc _ _ (Radd_congr h (Req_refl _))
  hbd := fun u => φ.hbd (Radd u (ofQ δ hδd))

theorem shiftTest_f (δ : Q) (hδd : 0 < δ.den) (φ : L2Test) (u : Real) :
    (shiftTest δ hδd φ).f u = φ.f (Radd u (ofQ δ hδd)) := rfl

/-- `affineMap a w t + δ = affineMap (a+δ) w t`. -/
theorem affineMap_add_shift (a w δ : Q) (ha : 0 < a.den) (hw : 0 < w.den) (hδd : 0 < δ.den) (t : Real) :
    Req (Radd (affineMap a w ha hw t) (ofQ δ hδd)) (affineMap (add a δ) w (add_den_pos ha hδd) hw t) := by
  show Req (Radd (Radd (ofQ a ha) (Rmul (ofQ w hw) t)) (ofQ δ hδd))
    (Radd (ofQ (add a δ) (add_den_pos ha hδd)) (Rmul (ofQ w hw) t))
  refine Req_trans (Radd_assoc _ _ _) ?_
  refine Req_trans (Radd_congr (Req_refl _) (Radd_comm _ _)) ?_
  refine Req_trans (Req_symm (Radd_assoc _ _ _)) ?_
  exact Radd_congr (Radd_ofQ_ofQ ha hδd) (Req_refl _)

/-- **THE WINDOW TRANSLATION** `∫_{[a, a+w]} φ(·+δ) = ∫_{[a+δ, a+δ+w]} φ`. -/
theorem shift_window (δ : Q) (hδd : 0 < δ.den) (φ : L2Test) (a w : Q) (ha : 0 < a.den)
    (hw : 0 < w.den) (hwn : 0 ≤ w.num) :
    Req (riemannIntegralI (shiftTest δ hδd φ).hLd (shiftTest δ hδd φ).hLn (shiftTest δ hδd φ).hlip
          (shiftTest δ hδd φ).hfc a w ha hw hwn)
        (riemannIntegralI φ.hLd φ.hLn φ.hlip φ.hfc (add a δ) w (add_den_pos ha hδd) hw hwn) := by
  refine Rmul_congr (Req_refl _) ?_
  refine riemannIntegral_congr_mod _ _ _ _ _ _ _ _ (Qeq_le (Qeq_refl _)) (fun t => ?_)
  exact φ.hfc _ _ (affineMap_add_shift a w δ ha hw hδd t)

/-- Shifts compose: `shiftTest Δ (shiftTest δ φ) = shiftTest (δ+Δ) φ` pointwise. -/
theorem shiftTest_comp (δ Δ : Q) (hδd : 0 < δ.den) (hΔd : 0 < Δ.den) (φ : L2Test) (u : Real) :
    Req ((shiftTest Δ hΔd (shiftTest δ hδd φ)).f u)
        ((shiftTest (add δ Δ) (add_den_pos hδd hΔd) φ).f u) := by
  rw [shiftTest_f, shiftTest_f, shiftTest_f]
  refine φ.hfc _ _ ?_
  refine Req_trans (Radd_assoc _ _ _) ?_
  exact Radd_congr (Req_refl _) (Req_trans (Radd_comm _ _) (Radd_ofQ_ofQ hδd hΔd))

/-- The shifted test respects `Qeq` of the shift. -/
theorem shiftTest_congr_shift (δ δ' : Q) (hδd : 0 < δ.den) (hδ'd : 0 < δ'.den) (h : Qeq δ δ')
    (φ : L2Test) (u : Real) :
    Req ((shiftTest δ hδd φ).f u) ((shiftTest δ' hδ'd φ).f u) :=
  φ.hfc _ _ (Radd_congr (Req_refl _) (ofQ_congr hδd hδ'd h))

/-- The unit term of a shifted-by-one test is the next unit term. -/
theorem integralTerm_shift_one (φ : L2Test) (m : Nat) :
    Req (integralTerm (shiftTest (⟨1, 1⟩ : Q) Nat.one_pos φ).hLd (shiftTest (⟨1, 1⟩ : Q) Nat.one_pos φ).hLn
          (shiftTest (⟨1, 1⟩ : Q) Nat.one_pos φ).hlip (shiftTest (⟨1, 1⟩ : Q) Nat.one_pos φ).hfc m)
        (integralTerm φ.hLd φ.hLn φ.hlip φ.hfc (m + 1)) := by
  refine Req_trans (shift_window (⟨1, 1⟩ : Q) Nat.one_pos φ _ _ Nat.one_pos (by decide) (by decide)) ?_
  refine riemannIntegralI_congr_Q _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ (Qeq_refl _)
  simp only [Qeq, add]; push_cast; ring_uor

end UOR.Bridge.F1Square.Square
