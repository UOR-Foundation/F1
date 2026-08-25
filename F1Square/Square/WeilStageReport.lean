/-
F1 square — **a certified sign of the prime component on an explicit context** (`WeilStageReport.lean`).
On the explicit context `C₀` (`a = 1/2, b = 2/3, X = 2`) and its explicit core test (the tent), the
prime component of the coupled form is CERTIFIED strictly positive:

    `PrimeForm C₀.X tent tent > 0`   (`prime_component_positive`; indeed `≥ 2·log 2·2^{-1/2}·(1/176)`),

so its contribution `−PrimeForm` to `CoupledForm = ArchForm − PrimeForm` is strictly negative there.
The finite consequence `no_cut_stage_reads_prime` says exactly this: no single cut-slice value
`Q_M(a⊕b)` with `Σa = 0` (a sum of squares, `Qform_cut_nonneg`) equals `−PrimeForm C₀.X tent tent`.
It is a statement about ONE cut-slice value.  It says nothing about coefficient maps, stages, path
independence, or a `CoupledForm` readback, and it does not exclude a mixed cut/cycle-valued family —
indeed `AtlasPrimeDyadicReadback` builds one whose Bishop limit IS `−PrimeForm` (the negative sign
enters through the `−I` cycle term of the same mixed expression).
HONEST SCOPE: a certified number and a finite consequence; no factorization, no positivity claim.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.WeilStageFalsify
import F1Square.Square.AtlasIncidence

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

theorem Pos_logN_two : Pos (logN 2 (by omega)) :=
  Pos_of_Rle_ofQ (c := (⟨1, 2⟩ : Q)) (by decide) (Nat.succ_pos 1) logN_2_ge_half

/-- `2^{-1/2} = normWeight 2 ≥ 1/2 > 0`. -/
theorem Pos_normWeight_two : Pos (normWeight (⟨2, 1⟩ : Q)) := by
  have hqn : (0 : Int) < (⟨2, 1⟩ : Q).num := by decide
  refine Pos_congr (Req_symm (normWeight_pos_eq hqn)) ?_
  refine Pos_of_Rle_ofQ (c := (⟨1, 2⟩ : Q)) (by decide) (Nat.succ_pos 1) ?_
  refine Rle_of_Rsq_le (Rnonneg_ofQ (Nat.succ_pos 1) (by decide)) (Rsqrt_nonneg _ _ _) ?_
  refine Rle_trans (Rle_of_Req (Rmul_ofQ_ofQ (Nat.succ_pos 1) (Nat.succ_pos 1))) ?_
  refine Rle_trans (Rle_ofQ_ofQ _ (Qinv_den_pos hqn)
    (by decide : Qle (mul (⟨1, 2⟩ : Q) (⟨1, 2⟩ : Q)) (Qinv (⟨2, 1⟩ : Q)))) ?_
  exact Rle_of_Req (Req_symm (Rsqrt_sq _ _ _))

theorem Pos_H2_tent :
    Pos (HForm tentTest43 tentTest43 (⟨2, 1⟩ : Q) (by decide) Nat.one_pos (⟨1, 2⟩ : Q) (by decide) (Nat.succ_pos 1)
      (⟨1, 1⟩ : Q) Nat.one_pos (by decide)) :=
  Pos_of_Rle_ofQ (c := (⟨1, 176⟩ : Q)) (by decide) (by decide) HForm_tent_ge

theorem Pos_B2_tent :
    Pos (BForm tentTest43 tentTest43 (⟨2, 1⟩ : Q) (by decide) Nat.one_pos (⟨1, 2⟩ : Q) (by decide) (Nat.succ_pos 1)
      (⟨1, 1⟩ : Q) Nat.one_pos (by decide)) := by
  show Pos (Rmul (normWeight (⟨2, 1⟩ : Q)) _)
  exact Pos_Rmul Pos_normWeight_two Pos_H2_tent

theorem reflect_tent_nonneg (y : Real) :
    Rnonneg ((reflectTest (⟨1, 2⟩ : Q) (by decide) (Nat.succ_pos 1) tentTest43).f y) := tent_nonneg _

theorem Bhalf_tent_nonneg :
    Rnonneg (BForm tentTest43 tentTest43 (⟨1, 2⟩ : Q) (by decide) (Nat.succ_pos 1) (⟨1, 2⟩ : Q) (by decide)
      (Nat.succ_pos 1) (⟨1, 1⟩ : Q) Nat.one_pos (by decide)) := by
  show Rnonneg (Rmul (normWeight (⟨1, 2⟩ : Q)) (HForm tentTest43 tentTest43 (⟨1, 2⟩ : Q) _ _ _ _ _ _ _ _))
  refine Rnonneg_Rmul (Rnonneg_congr (Req_symm (normWeight_pos_eq (by decide))) (Rsqrt_nonneg _ _ _)) ?_
  unfold HForm
  exact mulConv_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ tent_nonneg reflect_tent_nonneg

/-- `PForm 1 (tent,tent) = Λ(2)·(B₂ + ½·B_{1/2}) > 0`. -/
theorem PForm_one_tent_pos :
    Pos (PForm 1 tentTest43 tentTest43 (⟨1, 2⟩ : Q) (by decide) (Nat.succ_pos 1) (⟨1, 1⟩ : Q) Nat.one_pos (by decide)) := by
  show Pos (Rmul (vonMangoldt 2)
    (Radd (BForm tentTest43 tentTest43 (⟨2, 1⟩ : Q) _ _ (⟨1, 2⟩ : Q) _ _ (⟨1, 1⟩ : Q) _ _)
      (Rmul (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1))
        (BForm tentTest43 tentTest43 (⟨1, 2⟩ : Q) _ _ (⟨1, 2⟩ : Q) _ _ (⟨1, 1⟩ : Q) _ _))))
  refine Pos_mono (Rmul_le_Rmul_left (vonMangoldt_nonneg 2)
    (Rle_self_Radd_right (Rnonneg_Rmul (Rnonneg_ofQ (Nat.succ_pos 1) (by decide)) Bhalf_tent_nonneg))) ?_
  exact Pos_Rmul (Pos_congr (Req_symm vonMangoldt_two) Pos_logN_two) Pos_B2_tent

/-- **THE CERTIFIED TERM**: `PrimeForm C₀.X tent tent > 0`. -/
theorem prime_component_positive :
    Pos (PrimeForm ctx0.X tentTest43 tentTest43 ctx0.a ctx0.han ctx0.had ctx0.w ctx0.hw ctx0.hwn) := by
  show Pos (Radd (Radd zero (PForm 0 tentTest43 tentTest43 (⟨1, 2⟩ : Q) _ _ (⟨1, 1⟩ : Q) _ _))
    (PForm 1 tentTest43 tentTest43 (⟨1, 2⟩ : Q) _ _ (⟨1, 1⟩ : Q) _ _))
  have h0 : Req (PForm 0 tentTest43 tentTest43 (⟨1, 2⟩ : Q) (by decide) (Nat.succ_pos 1) (⟨1, 1⟩ : Q) Nat.one_pos (by decide)) zero := by
    show Req (Rmul (vonMangoldt 1) _) zero
    exact Req_trans (Rmul_congr vonMangoldt_one (Req_refl _)) (Req_trans (Rmul_comm _ _) (Rmul_zero _))
  refine Pos_congr (Req_symm (Req_trans (Radd_congr (Req_trans (Radd_congr (Req_refl _) h0) (Radd_zero _)) (Req_refl _))
    (Req_trans (Radd_comm _ _) (Radd_zero _)))) ?_
  exact PForm_one_tent_pos

/-- **What is proved** (exactly): there are no `a, b` with `Σa = 0` whose cut-slice quadratic value
    `Q_M(a⊕b)` equals `−PrimeForm C₀.X tent tent` — because that value is `≥ 0` while the term is `< 0`.
    This is a statement about ONE cut-slice value; it does not quantify over coefficient maps, stages,
    path independence, or a `CoupledForm` readback, and it does not exclude a mixed cut/cycle-valued
    stage in which the prime contribution enters through the `−I` (cycle) term. -/
theorem no_cut_stage_reads_prime :
    ¬ ∃ (a b : Nat → Real), Req (RsumN a 3) zero ∧
      Req (Qform (cutVec a b))
        (Rneg (PrimeForm ctx0.X tentTest43 tentTest43 ctx0.a ctx0.han ctx0.had ctx0.w ctx0.hw ctx0.hwn)) := by
  rintro ⟨a, b, hS, hq⟩
  exact not_Pos_of_Rnonneg_neg (Rnonneg_congr hq (Qform_cut_nonneg a b hS)) prime_component_positive

end UOR.Bridge.F1Square.Square
