/-
F1 square — Track 1, item 3: the **theta Mellin integral** `∫₁^∞ ψ(t) dt` as a genuine constructive
real (the `σ = 1` Mellin transform of the Jacobi theta function). This is the first fully assembled
Mellin object — it consumes the entire analytic profile of `ψ` built in the theta stack:

- the **totalized integrand** `thetaClamp t = ψ(max(t,1))` (total `Real → Real`, `= ψ(t)` on `[1,∞)`),
  Lipschitz with constant `32/3` (`clampOne` is `1`-Lipschitz ∘ `ψ` is `32/3`-Lipschitz: `thetaFn_lip`),
  non-negative and `≈`-respecting — exactly the certified-integration interface;
- the **decay** `|∫_{m+1}^{m+2} ψ| ≤ 2/((m+1)m)` (`m ≥ 1`): on `[m+1, m+2]` the clamp is inert and `ψ`
  is antitone, so the integrand is `≤ ψ(m+1) ≤ 2/((m+1)m)` (`thetaFn_value_decay`); bounding the integral
  by that per-interval constant uses the interval-local `riemannIntegralI_le_unit`;
- the convergent sum `Σ_{n≥1} ∫_n^{n+1} ψ` via `improperIntegral1` (`K = 2`).

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by `scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.ThetaLipschitzFn
import F1Square.Analysis.IntegralLocal

namespace UOR.Bridge.F1Square.Analysis

/-- **The totalized theta integrand** `thetaClamp t = ψ(max(t,1))` — total `Real → Real`, `= ψ(t)` on
    `[1, ∞)`, `32/3`-Lipschitz, non-negative. -/
def thetaClamp (t : Real) : Real := thetaFn (clampOne t) (clampOne_ge_one t)

/-- `thetaClamp` respects `≈`. -/
theorem thetaClamp_congr {x y : Real} (h : Req x y) : Req (thetaClamp x) (thetaClamp y) :=
  thetaFn_congr (clampOne_ge_one x) (clampOne_ge_one y) (clampOne_congr h)

/-- `thetaClamp` is `32/3`-Lipschitz (clamp `1`-Lipschitz, `ψ` `32/3`-Lipschitz). -/
theorem thetaClamp_lip (x y : Real) :
    Rle (Rabs (Rsub (thetaClamp x) (thetaClamp y)))
      (Rmul (ofQ (⟨32, 3⟩ : Q) (by decide)) (Rabs (Rsub x y))) :=
  Rle_trans (thetaFn_lip (clampOne_ge_one x) (clampOne_ge_one y))
    (Rmul_le_Rmul_left (Rnonneg_ofQ (by decide) (by decide)) (clampOne_lipschitz x y))

/-- `thetaClamp t ≥ 0`. -/
theorem thetaClamp_nonneg (t : Real) : Rnonneg (thetaClamp t) :=
  thetaFn_nonneg (clampOne t) (clampOne_ge_one t)

/-- The constant integrand is `32/3`-Lipschitz (trivially, `|c − c| = 0`). -/
private theorem const_lip32 (c : Real) (x y : Real) :
    Rle (Rabs (Rsub c c)) (Rmul (ofQ (⟨32, 3⟩ : Q) (by decide)) (Rabs (Rsub x y))) :=
  Rle_trans (Rle_of_Req (Req_trans (Rabs_congr (Radd_neg c)) Rabs_zero))
    (Rle_zero_of_Rnonneg (Rnonneg_Rmul (Rnonneg_ofQ (by decide) (by decide)) (Rnonneg_Rabs _)))

/-- The interval integral of a constant, general modulus: `∫_a^{a+w} c = w·c`. -/
private theorem riemannIntegralI_const32 (c : Real) (a w : Q) (ha : 0 < a.den) (hw : 0 < w.den)
    (hwn : 0 ≤ w.num) :
    Req (riemannIntegralI (f := fun _ => c) (L := (⟨32, 3⟩ : Q)) (by decide) (by decide)
          (const_lip32 c) (fun _ _ _ => Req_refl c) a w ha hw hwn) (Rmul (ofQ w hw) c) :=
  Rmul_congr (Req_refl _) (riemannIntegral_const_gen c _ _ _ _)

/-- **Per-interval decay** `∫_{m+1}^{m+2} ψ ≤ 2/((m+1)m)` (`m ≥ 1`). On the interval the clamp is inert
    and `ψ` is antitone, so the integrand is `≤ ψ(m+1)`; integrate the constant and apply the value decay. -/
theorem integralTerm_thetaClamp_le (m : Nat) (hm : 1 ≤ m) :
    Rle (integralTerm (by decide : 0 < (⟨32, 3⟩ : Q).den) (by decide) thetaClamp_lip
        (fun _ _ h => thetaClamp_congr h) m)
      (ofQ (mul (⟨2, 1⟩ : Q) (⟨1, (m + 1) * m⟩ : Q))
        (Qmul_den_pos (by decide) (digamma_succ_mul_pos hm))) := by
  -- compare to the constant `ψ(m+1)` on the interval
  have hub : Rle (integralTerm (by decide : 0 < (⟨32, 3⟩ : Q).den) (by decide) thetaClamp_lip
        (fun _ _ h => thetaClamp_congr h) m)
      (riemannIntegralI (f := fun _ => thetaFn (RnatSucc m) (one_le_RnatSucc m))
        (L := (⟨32, 3⟩ : Q)) (by decide) (by decide) (const_lip32 _) (fun _ _ _ => Req_refl _)
        (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) Nat.one_pos (by decide) (by decide)) := by
    refine riemannIntegralI_le_unit (by decide) (by decide) thetaClamp_lip
      (fun _ _ h => thetaClamp_congr h) (const_lip32 _) (fun _ _ _ => Req_refl _)
      (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) Nat.one_pos (by decide) (by decide) (fun x hx0 hx1 => ?_)
    -- `ψ(clampOne(affineMap x)) ≤ ψ(m+1)`
    have hxnn : Rnonneg x := Rnonneg_of_Rle_zero hx0
    have hpge : Rle (RnatSucc m) (affineMap (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) Nat.one_pos
        (by decide) x) :=
      Rle_self_Radd_right (Rnonneg_Rmul (Rnonneg_ofQ (by decide) (by decide)) hxnn)
    have hp1 : Rle one (affineMap (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) Nat.one_pos (by decide) x) :=
      Rle_trans (one_le_RnatSucc m) hpge
    refine Rle_trans (Rle_of_Req (thetaFn_congr (clampOne_ge_one _) hp1
        (clampOne_eq_of_ge hp1))) ?_
    exact thetaFn_antitone (one_le_RnatSucc m) hp1 hpge
  refine Rle_trans hub ?_
  refine Rle_trans (Rle_of_Req (riemannIntegralI_const32 _ _ _ _ _ _)) ?_
  refine Rle_trans (Rle_of_Req (Rmul_comm _ _)) ?_
  refine Rle_trans (Rle_of_Req (Rmul_one _)) ?_
  -- `ψ(m+1) ≤ 2/((m+1)m) = mul ⟨2,1⟩ ⟨1,(m+1)m⟩`
  refine Rle_trans (thetaFn_value_decay m hm (one_le_RnatSucc m)) ?_
  exact Rle_of_Req (ofQ_congr (Nat.mul_pos (Nat.succ_pos m) hm)
    (Qmul_den_pos (by decide) (digamma_succ_mul_pos hm)) (by simp only [Qeq, mul]; push_cast; ring_uor))

/-- **The theta Mellin integral** `∫₁^∞ ψ(t) dt`, a genuine constructive real (`σ = 1` Mellin transform
    of `ψ`). Convergent by the per-interval decay `integralTerm_thetaClamp_le` (`K = 2`). -/
def thetaMellin1 : Real :=
  improperIntegral1 (by decide : 0 < (⟨32, 3⟩ : Q).den) (by decide) thetaClamp_lip
    (fun _ _ h => thetaClamp_congr h) (by decide : 0 < (⟨2, 1⟩ : Q).den) (by decide)
    (fun m hm => ⟨Rle_trans
        (Rle_trans (Rle_Rneg (Rle_zero_of_Rnonneg (Rnonneg_ofQ
          (Qmul_den_pos (by decide) (digamma_succ_mul_pos hm)) (by show (0 : Int) ≤ 2 * 1; decide))))
          (Rle_of_Req Rneg_zero))
        (Rle_zero_of_Rnonneg (riemannIntegralI_nonneg _ _ _ _ thetaClamp_nonneg _ _ _ _ _)),
      integralTerm_thetaClamp_le m hm⟩)

/-- **`∫₁^∞ ψ ≥ 0`** — the integrand is non-negative. -/
theorem thetaMellin1_nonneg : Rnonneg thetaMellin1 :=
  improperIntegral1_nonneg _ _ _ _ _ _ _ thetaClamp_nonneg

end UOR.Bridge.F1Square.Analysis
