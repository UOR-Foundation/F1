/-
F1 square — **the parametric certified integral** (`AtlasParamIntegral.lean`): the two lemmas that let an
inner Haar integral `x ↦ ∫₀¹ F(x,·)` be used as the integrand of an outer certified integral in the
scale variable `x`:

  * `riemannIntegral_abs_le_unit_real` — `|h| ≤ b` on `[0,1]` (REAL `b`) ⟹ `|∫₀¹ h| ≤ b`;
  * `param_integral_lip` — if `F(x,·)` is certified for every `x` (modulus `L x`, any `x`-dependence) and
    `x ↦ F(x,y)` is `Lx`-Lipschitz uniformly for `y ∈ [0,1]`, then `x ↦ ∫₀¹ F(x,·)` is `Lx`-Lipschitz;
  * `param_integral_congr` — pointwise `F(x,·) ≈ F(x',·)` ⟹ equal inner integrals.

No form, no fiber, no positivity: finite-linearity bookkeeping of the certified integral only.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.IntegralFiniteLin
import F1Square.Analysis.IntegralLocal
import F1Square.Analysis.IntervalCert

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

/-- Negation transports a Lipschitz certificate (local copy). -/
theorem lip_neg_pi {F : Real → Real} {L : Q} (hLd : 0 < L.den)
    (hF : ∀ x y, Rle (Rabs (Rsub (F x) (F y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y)))) :
    ∀ x y, Rle (Rabs (Rsub (Rneg (F x)) (Rneg (F y)))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))) := by
  intro x y
  have h : Req (Rabs (Rsub (Rneg (F x)) (Rneg (F y)))) (Rabs (Rsub (F x) (F y))) := by
    refine Req_trans (Rabs_congr (Req_trans (Radd_congr (Req_refl _) (Rneg_neg (F y))) (Radd_comm _ _))) ?_
    exact Req_trans (Rabs_congr (Req_symm (Rneg_Rsub_flip (F x) (F y)))) (Rabs_Rneg _)
  exact Rle_trans (Rle_of_Req h) (hF x y)

/-- **`|h| ≤ b` on `[0,1]` (real `b`) ⟹ `|∫₀¹ h| ≤ b`** — comparison against the constant integrands
    `±b` (`riemannIntegral_const_gen`, unit-local monotonicity). -/
theorem riemannIntegral_abs_le_unit_real {h : Real → Real} {L : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlip : ∀ x y, Rle (Rabs (Rsub (h x) (h y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfc : ∀ x y, Req x y → Req (h x) (h y))
    (b : Real) (hb : ∀ x, Rle zero x → Rle x one → Rle (Rabs (h x)) b) :
    Rle (Rabs (riemannIntegral hLd hLn hlip hfc)) b := by
  have hzeroL : Qle (⟨0, 1⟩ : Q) L := by
    show (0 : Int) * (L.den : Int) ≤ L.num * 1
    rw [Int.zero_mul, Int.mul_one]; exact hLn
  have hlipB : ∀ x y, Rle (Rabs (Rsub b b)) (Rmul (ofQ L hLd) (Rabs (Rsub x y))) :=
    lip_weaken_fl (by decide) hLd hzeroL (const_lip0 b)
  have hlipnB : ∀ x y, Rle (Rabs (Rsub (Rneg b) (Rneg b))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))) :=
    lip_weaken_fl (by decide) hLd hzeroL (const_lip0 (Rneg b))
  have hcB := riemannIntegral_const_gen b hLd hLn hlipB (fun _ _ _ => Req_refl _)
  have hcnB := riemannIntegral_const_gen (Rneg b) hLd hLn hlipnB (fun _ _ _ => Req_refl _)
  refine Rabs_le_of_both ?_ ?_
  · exact Rle_trans (riemannIntegral_le_unit hLd hLn hlip hfc hlipB (fun _ _ _ => Req_refl _)
      (fun x h0 h1 => Rle_of_Rabs_le (hb x h0 h1))) (Rle_of_Req hcB)
  · have hlo : Rle (Rneg b) (riemannIntegral hLd hLn hlip hfc) :=
      Rle_trans (Rle_of_Req (Req_symm hcnB))
        (riemannIntegral_le_unit hLd hLn hlipnB (fun _ _ _ => Req_refl _) hlip hfc
          (fun x h0 h1 => Rneg_le_of_Rabs_le (hb x h0 h1)))
    exact Rle_trans (Rle_Rneg hlo) (Rle_of_Req (Rneg_neg b))

/-- **★ THE PARAMETRIC LIPSCHITZ LEMMA**: with `F(x,·)` certified at the (possibly `x`-dependent) modulus
    `L x` and `x ↦ F(x,y)` `Lx`-Lipschitz for every `y ∈ [0,1]`, the inner integrals satisfy
    `|∫₀¹ F(x,·) − ∫₀¹ F(x',·)| ≤ Lx·|x − x'|`. -/
theorem param_integral_lip {F : Real → Real → Real} {L : Real → Q}
    (hLd : ∀ x, 0 < (L x).den) (hLn : ∀ x, 0 ≤ (L x).num)
    (hlip : ∀ x y z, Rle (Rabs (Rsub (F x y) (F x z))) (Rmul (ofQ (L x) (hLd x)) (Rabs (Rsub y z))))
    (hfc : ∀ x y z, Req y z → Req (F x y) (F x z))
    {Lx : Q} (hLxd : 0 < Lx.den)
    (hxlip : ∀ y, Rle zero y → Rle y one → ∀ x x',
      Rle (Rabs (Rsub (F x y) (F x' y))) (Rmul (ofQ Lx hLxd) (Rabs (Rsub x x'))))
    (x x' : Real) :
    Rle (Rabs (Rsub (riemannIntegral (hLd x) (hLn x) (hlip x) (hfc x))
                    (riemannIntegral (hLd x') (hLn x') (hlip x') (hfc x'))))
        (Rmul (ofQ Lx hLxd) (Rabs (Rsub x x'))) := by
  have hSd : 0 < (add (L x) (L x')).den := add_den_pos (hLd x) (hLd x')
  have hSn : 0 ≤ (add (L x) (L x')).num := Qadd_num_nonneg_loc (hLn x) (hLn x')
  have h1 := lip_weaken_fl (hLd x) hSd (Qle_add_right_nonneg (hLn x')) (hlip x)
  have h2 := lip_weaken_fl (hLd x') hSd (Qle_add_left_nonneg (hLn x)) (hlip x')
  have hn2 := lip_neg_pi hSd h2
  have hfcn : ∀ y z, Req y z → Req (Rneg (F x' y)) (Rneg (F x' z)) := fun y z h => Rneg_congr (hfc x' y z h)
  have hsum := lip_add_fl (hLd x) (hLd x') (hlip x) (lip_neg_pi (hLd x') (hlip x'))
  have hfcs : ∀ y z, Req y z → Req (Radd (F x y) (Rneg (F x' y))) (Radd (F x z) (Rneg (F x' z))) :=
    fun y z h => Radd_congr (hfc x y z h) (Rneg_congr (hfc x' y z h))
  -- ∫_{L x} F x − ∫_{L x'} F x' ≈ ∫_{S} (F x − F x')
  have hdiff : Req (Rsub (riemannIntegral (hLd x) (hLn x) (hlip x) (hfc x))
                          (riemannIntegral (hLd x') (hLn x') (hlip x') (hfc x')))
                   (riemannIntegral hSd hSn hsum hfcs) := by
    refine Req_trans (Radd_congr (riemannIntegral_certif_irrel _ _ (hlip x) (hfc x) hSd hSn h1 (hfc x))
      (Rneg_congr (riemannIntegral_certif_irrel _ _ (hlip x') (hfc x') hSd hSn h2 (hfc x')))) ?_
    refine Req_trans (Radd_congr (Req_refl _) (Req_symm (riemannIntegral_neg hSd hSn h2 (hfc x') hn2 hfcn))) ?_
    exact Req_symm (riemannIntegral_add hSd hSn h1 (hfc x) hn2 hfcn hsum hfcs)
  refine Rle_trans (Rle_of_Req (Rabs_congr hdiff)) ?_
  exact riemannIntegral_abs_le_unit_real hSd hSn hsum hfcs _ (fun y h0 h1 => hxlip y h0 h1 x x')

/-- Pointwise `F(x,·) ≈ F(x',·)` ⟹ equal inner integrals (certificates reconciled). -/
theorem param_integral_congr {F : Real → Real → Real} {L : Real → Q}
    (hLd : ∀ x, 0 < (L x).den) (hLn : ∀ x, 0 ≤ (L x).num)
    (hlip : ∀ x y z, Rle (Rabs (Rsub (F x y) (F x z))) (Rmul (ofQ (L x) (hLd x)) (Rabs (Rsub y z))))
    (hfc : ∀ x y z, Req y z → Req (F x y) (F x z))
    (x x' : Real) (hxc : ∀ y, Req (F x y) (F x' y)) :
    Req (riemannIntegral (hLd x) (hLn x) (hlip x) (hfc x))
        (riemannIntegral (hLd x') (hLn x') (hlip x') (hfc x')) := by
  have hlip' : ∀ y z, Rle (Rabs (Rsub (F x' y) (F x' z))) (Rmul (ofQ (L x) (hLd x)) (Rabs (Rsub y z))) :=
    fun y z => Rle_trans (Rle_of_Req (Rabs_congr (Rsub_congr (Req_symm (hxc y)) (Req_symm (hxc z))))) (hlip x y z)
  refine Req_trans (riemannIntegral_congr (hLd x) (hLn x) (hlip x) (hfc x) hlip' (hfc x') hxc) ?_
  exact riemannIntegral_certif_irrel _ _ hlip' (hfc x') (hLd x') (hLn x') (hlip x') (hfc x')

end UOR.Bridge.F1Square.Square
