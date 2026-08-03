/-
F1 square — **the pre-Hilbert layer, brick 25** (`CoSupportMember.lean`): **THE FIRST NONZERO
TRANSFORM VALUE** — a genuine `[0,1]`-supported test with `f̂(0) ≈ 1/6 > 0`, and the co-support
subspace is PROPER.

The member is the unit bump `bumpU = clamp·(1 − clamp)` (`x(1−x)` on `[0,1]`, vanishing
beyond), realized entirely by the test-algebra combinators (`mul`/`sub` of bricks 10/14):

- `qCapQ_eq_of_ge` + `clamp01_sat` — the missing saturation side of the band clamp: for
  `x ≥ 1`, `clamp01 x ≈ 1`; with the affine window's lower bound this gives `bumpU`'s
  unit support (`bumpU_supp`) — the first NONZERO member of the compact class.
- `mellinMoment_bumpU` — `∫₀¹ x(1−x) = 1/6`: the integrand collapses pointwise to
  `clamp − clamp²`, certificate-transported to the shared modulus, split by the integral's
  additivity, and evaluated by bricks 23–24 (`1/2 − 1/3`).
- **`mellinHat_bumpU_value`/`mellinHat_bumpU_pos`** — through `mellinHat_compact`, the
  TRANSFORM takes the value `1/6` at a genuine nonzero test: `Pos (f̂(0))`, the first strict
  positivity of the constructed transform.
- **`bumpU_not_hatVanishes`** — `bumpU` is NOT in the co-support class at `K = 1`: with brick
  22's zero member, the subspace `HatVanishes · 1` is both inhabited and PROPER — the
  co-support condition genuinely cuts.

HONEST SCOPE. One nonzero transform value and properness of the vanishing subspace. The
nonzero member OF the subspace (vanishing low moments with a nonzero function — the cubic
bump `x(1−x)(1−2x)`, needing the `∫x³ = 1/4` evaluation) is the banked next construction;
no continuous parameter, no coupling; step 4 is RH. The crux fields stay `none`.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Square.HatVanishes
import F1Square.Square.MomentSquare
import F1Square.Square.MomentValue
import F1Square.Square.PairingLimitI
import F1Square.Analysis.AffineIntegral

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- The saturation side of the band clamp.
-- ===========================================================================

/-- `|y| ≤ c` from `0 ≤ y.num` and `y ≤ c` (local mirror of the `BandClamp` private). -/
private theorem qabs_le_of_nonneg {y c : Q} (hy : 0 ≤ y.num) (h : Qle y c) :
    Qle (Qabs y) c := by
  show (↑y.num.natAbs : Int) * (c.den : Int) ≤ c.num * (y.den : Int)
  rw [Int.natAbs_of_nonneg hy]; exact h

/-- `|a − b| ≈ |b − a|` at the `ℚ` level (local mirror). -/
private theorem qabs_sub_comm (a b : Q) : Qeq (Qabs (Qsub a b)) (Qabs (Qsub b a)) := by
  show ((Qsub a b).num.natAbs : Int) * (((Qsub b a).den : Nat) : Int)
      = ((Qsub b a).num.natAbs : Int) * (((Qsub a b).den : Nat) : Int)
  have hn : (Qsub a b).num.natAbs = (Qsub b a).num.natAbs := by
    have he : (Qsub b a).num = -((Qsub a b).num) := by
      simp only [Qsub, add, neg]; ring_uor
    rw [he, Int.natAbs_neg]
  have hd : (Qsub a b).den = (Qsub b a).den := by
    show a.den * b.den = b.den * a.den
    exact Nat.mul_comm a.den b.den
  rw [hn, hd]

/-- **The ceiling saturates on `[b, ∞)`**: where `b ≤ x` (Real-level), `qCapQ b x ≈ b` — the
    missing saturation mirror of `qCapQ_eq_of_le`. -/
theorem qCapQ_eq_of_ge {b : Q} {hbd : 0 < b.den} {x : Real}
    (hx : Rle (ofQ b hbd) x) : Req (qCapQ b hbd x) (ofQ b hbd) := by
  refine Req_of_lin_bound (C := 2) ?_
  intro n
  show Qle (Qabs (Qsub (Qmin (x.seq n) b) b)) (⟨(2 : Int), n + 1⟩ : Q)
  have hbn : Qle b (add (x.seq n) (⟨2, n + 1⟩ : Q)) := hx n
  by_cases h : Qle (x.seq n) b
  · rw [Qmin_eq_left h]
    refine Qle_congr_left (a := Qabs (Qsub b (x.seq n)))
      (Qabs_den_pos (Qsub_den_pos hbd (x.den_pos n))) (qabs_sub_comm b (x.seq n)) ?_
    refine qabs_le_of_nonneg ?_ (Qsub_le_of_le_add (x.den_pos n) (Nat.succ_pos n) hbn)
    have hh := h; simp only [Qle] at hh
    simp only [Qsub, add, neg]
    have hneg : -(x.seq n).num * (b.den : Int) = -((x.seq n).num * (b.den : Int)) :=
      Int.neg_mul _ _
    push_cast at hh ⊢
    omega
  · rw [Qmin_eq_right h]
    have h0 : (Qsub b b).num = 0 := by simp only [Qsub, add, neg]; ring_uor
    refine qabs_le_of_nonneg (by rw [h0]; exact Int.le_refl 0) ?_
    show (Qsub b b).num * ((n + 1 : Nat) : Int) ≤ (2 : Int) * ((Qsub b b).den : Int)
    rw [h0]; simp only [Int.zero_mul]
    exact Int.mul_nonneg (by omega) (Int.ofNat_nonneg _)

/-- **The clamp saturates at `1` on `[1, ∞)`**: `clamp01 x ≈ 1` for `x ≥ 1`. -/
theorem clamp01_sat {x : Real} (h1 : Rle one x) : Req (clamp01 x) one := by
  have h0 : Rle (ofQ (⟨0, 1⟩ : Q) (by decide)) x :=
    Rle_trans (Rle_ofQ_ofQ (by decide) (by decide) (by decide)) h1
  have hcl : Req (qClampQ (⟨0, 1⟩ : Q) (by decide) x) x := qClampQ_eq_of_ge h0
  exact Req_trans (qCapQ_congr (⟨1, 1⟩ : Q) (by decide) hcl) (qCapQ_eq_of_ge h1)

/-- The half-line window points sit at or beyond `1`: `affineMap (m+1) 1 x ≥ 1` on `[0,1]`. -/
theorem affine_window_ge_one (m : Nat) {x : Real} (h0 : Rle zero x) :
    Rle one (affineMap (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) Nat.one_pos (by decide) x) := by
  have hnn : Rnonneg (Rmul (ofQ (⟨1, 1⟩ : Q) (by decide)) x) :=
    Rnonneg_Rmul (Rnonneg_ofQ (by decide) (by decide)) (Rnonneg_of_Rle_zero h0)
  refine Rle_trans (Rle_ofQ_ofQ (by decide) Nat.one_pos ?_) (Rle_self_Radd_right hnn)
  show (1 : Int) * ((1 : Nat) : Int) ≤ ((m : Int) + 1) * ((1 : Nat) : Int)
  push_cast; omega

-- ===========================================================================
-- The unit bump and its support.
-- ===========================================================================

/-- **The unit bump**: `x(1−x)` on `[0,1]`, vanishing beyond — realized by the test-algebra
    combinators alone. -/
def bumpU : L2Test := L2Test.mul clampTest (L2Test.sub oneTest clampTest)

/-- **The unit bump is `[0,1]`-supported**: at every half-line window point the clamp
    saturates, so the `(1 − clamp)` factor kills the product. -/
theorem bumpU_supp : UnitSupported bumpU := by
  intro m x h0 h1
  have hsat : Req (clamp01 (affineMap (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q)
      Nat.one_pos (by decide) x)) one :=
    clamp01_sat (affine_window_ge_one m h0)
  have hz : Req (Radd one (Rneg (clamp01 (affineMap (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q)
      Nat.one_pos (by decide) x)))) zero :=
    Req_trans (Radd_congr (Req_refl one) (Rneg_congr hsat)) (Radd_neg one)
  exact Req_trans (Rmul_congr (Req_refl _) hz) (Rmul_zero _)

-- ===========================================================================
-- The shared evaluation modulus and its certificates.
-- ===========================================================================

/-- The shared evaluation modulus `1 + L(clamp²)`. -/
private def Lc : Q := add (⟨1, 1⟩ : Q) (l2L clampTest clampTest)

private theorem Lc_den : 0 < Lc.den := add_den_pos (by decide) (l2L_den clampTest clampTest)

private theorem Lc_num : 0 ≤ Lc.num :=
  Qadd_num_nonneg_loc (by decide) (l2L_num clampTest clampTest)

private theorem hle_one_Lc : Qle (⟨1, 1⟩ : Q) Lc :=
  Qle_self_add (l2L_num clampTest clampTest)

private theorem lip_clamp_Lc : ∀ x y, Rle (Rabs (Rsub (clamp01 x) (clamp01 y)))
    (Rmul (ofQ Lc Lc_den) (Rabs (Rsub x y))) :=
  lip_weaken (by decide) Lc_den hle_one_Lc clampTest.hlip

private theorem fc_clamp : ∀ x y, Req x y → Req (clamp01 x) (clamp01 y) :=
  fun _ _ h => clamp01_congr h

private theorem lip_sq_Lc : ∀ x y, Rle (Rabs (Rsub (clampSq x) (clampSq y)))
    (Rmul (ofQ Lc Lc_den) (Rabs (Rsub x y))) :=
  lip_weaken (l2L_den clampTest clampTest) Lc_den (Qle_self_add_l (by decide))
    (l2lip clampTest clampTest)

private theorem fc_sq : ∀ x y : Real, Req x y → Req (clampSq x) (clampSq y) :=
  fun _ _ h => Rmul_congr (clamp01_congr h) (clamp01_congr h)

private theorem lip_nsq_Lc : ∀ x y, Rle (Rabs (Rsub (Rneg (clampSq x)) (Rneg (clampSq y))))
    (Rmul (ofQ Lc Lc_den) (Rabs (Rsub x y))) :=
  lip_neg lip_sq_Lc

private theorem fc_nsq : ∀ x y : Real, Req x y → Req (Rneg (clampSq x)) (Rneg (clampSq y)) :=
  congr_neg fc_sq

private theorem lip_gB_Lc : ∀ x y, Rle (Rabs (Rsub
      (Radd (clamp01 x) (Rneg (clampSq x))) (Radd (clamp01 y) (Rneg (clampSq y)))))
    (Rmul (ofQ Lc Lc_den) (Rabs (Rsub x y))) := fun x y =>
  Rle_trans (Radd_lipschitz_real clampTest.hlip (lip_neg (l2lip clampTest clampTest)) x y)
    (Rmul_le_Rmul_right (Rnonneg_Rabs _)
      (Rle_of_Req (Radd_ofQ_ofQ (by decide) (l2L_den clampTest clampTest))))

private theorem fc_gB : ∀ x y : Real, Req x y →
    Req (Radd (clamp01 x) (Rneg (clampSq x))) (Radd (clamp01 y) (Rneg (clampSq y))) :=
  fun x y h => Radd_congr (clamp01_congr h) (Rneg_congr (fc_sq x y h))

private theorem int_clamp_Lc :
    Req (riemannIntegral Lc_den Lc_num lip_clamp_Lc fc_clamp) half :=
  Req_trans (riemannIntegral_congr_unit (g := fun x => x) Lc_den Lc_num
      lip_clamp_Lc fc_clamp (lip_id_ge Lc_den hle_one_Lc) congr_id
      (fun _ h0 h1 => clamp01_inert h0 h1))
    (riemannIntegral_id_gen Lc_den Lc_num (lip_id_ge Lc_den hle_one_Lc) congr_id)

private theorem int_nsq_Lc :
    Req (riemannIntegral Lc_den Lc_num lip_nsq_Lc fc_nsq)
      (Rneg (ofQ (⟨1, 3⟩ : Q) (by decide))) :=
  Req_trans (riemannIntegral_neg Lc_den Lc_num lip_sq_Lc fc_sq lip_nsq_Lc fc_nsq)
    (Rneg_congr (riemannIntegral_clampSq_gen Lc_den Lc_num lip_sq_Lc fc_sq))

-- ===========================================================================
-- The moment and the transform value.
-- ===========================================================================

/-- **`mellinMoment bumpU 0 ≈ 1/6`** — `∫₀¹ x(1−x) dx`: pointwise collapse to
    `clamp − clamp²`, certificate transport, additivity, and the brick-23/24 values
    `1/2 − 1/3`. -/
theorem mellinMoment_bumpU : Req (mellinMoment bumpU 0) (ofQ (⟨1, 6⟩ : Q) (by decide)) := by
  have hdist : ∀ x, Req (Rmul (bumpU.f x) ((powTest 0).f x))
      (Radd (clamp01 x) (Rneg (clampSq x))) := fun x =>
    Req_trans (Rmul_one _)
      (Req_trans (Rmul_sub_distrib (clamp01 x) one (clamp01 x))
        (Radd_congr (Rmul_one (clamp01 x)) (Req_refl _)))
  have hlipT : ∀ x y, Rle (Rabs (Rsub
        (Radd (clamp01 x) (Rneg (clampSq x))) (Radd (clamp01 y) (Rneg (clampSq y)))))
      (Rmul (ofQ (l2L bumpU (powTest 0)) (l2L_den bumpU (powTest 0)))
        (Rabs (Rsub x y))) := fun x y =>
    Rle_trans (Rle_of_Req (Rabs_congr (Rsub_congr (Req_symm (hdist x)) (Req_symm (hdist y)))))
      (l2lip bumpU (powTest 0) x y)
  refine Req_trans (riemannIntegral_congr
    (g := fun x => Radd (clamp01 x) (Rneg (clampSq x)))
    (l2L_den bumpU (powTest 0)) (l2L_num bumpU (powTest 0))
    (l2lip bumpU (powTest 0)) (l2fc bumpU (powTest 0)) hlipT fc_gB hdist) ?_
  refine Req_trans (riemannIntegral_certif_irrel (l2L_den bumpU (powTest 0))
    (l2L_num bumpU (powTest 0)) hlipT fc_gB Lc_den Lc_num lip_gB_Lc fc_gB) ?_
  refine Req_trans (riemannIntegral_add Lc_den Lc_num lip_clamp_Lc fc_clamp
    lip_nsq_Lc fc_nsq lip_gB_Lc fc_gB) ?_
  refine Req_trans (Radd_congr int_clamp_Lc int_nsq_Lc) ?_
  refine Req_trans (Radd_congr (Req_refl half) (Rneg_ofQ (⟨1, 3⟩ : Q) (by decide))) ?_
  refine Req_trans (Radd_ofQ_ofQ (by decide) (by decide)) ?_
  exact Req_of_seq_Qeq (fun _ => by
    show Qeq (add (⟨1, 2⟩ : Q) (neg (⟨1, 3⟩ : Q))) (⟨1, 6⟩ : Q)
    decide)

/-- **THE FIRST NONZERO TRANSFORM VALUE**: `f̂(0) ≈ 1/6` at the genuine `[0,1]`-supported unit
    bump — the constructed Mellin transform takes a certified nonzero value. -/
theorem mellinHat_bumpU_value :
    Req (mellinHat bumpU 0 (C := (⟨0, 1⟩ : Q)) (by decide) (by show (0 : Int) ≤ 0; decide)
        (allDecay_of_supp bumpU bumpU_supp 0))
      (ofQ (⟨1, 6⟩ : Q) (by decide)) :=
  Req_trans (mellinHat_compact bumpU 0 bumpU_supp) mellinMoment_bumpU

/-- **The transform value is strictly positive**: `Pos (f̂(0))` at the unit bump. -/
theorem mellinHat_bumpU_pos :
    Pos (mellinHat bumpU 0 (C := (⟨0, 1⟩ : Q)) (by decide) (by show (0 : Int) ≤ 0; decide)
      (allDecay_of_supp bumpU bumpU_supp 0)) :=
  Pos_congr (Req_symm mellinHat_bumpU_value) ⟨6, by decide⟩

/-- **The co-support subspace is PROPER**: the unit bump is NOT in `HatVanishes · 1` — with
    the zero member (brick 22) the vanishing condition is both inhabited and strict: it
    genuinely cuts the test class. -/
theorem bumpU_not_hatVanishes :
    ¬ HatVanishes bumpU 1 (C := (⟨0, 1⟩ : Q)) (by decide) (by show (0 : Int) ≤ 0; decide)
      (allDecay_of_supp bumpU bumpU_supp) := by
  intro h
  have hz : Req (mellinHat bumpU 0 (by decide) (by show (0 : Int) ≤ 0; decide)
      (allDecay_of_supp bumpU bumpU_supp 0)) zero := h 0 (by decide)
  have hp : Pos zero := Pos_congr hz mellinHat_bumpU_pos
  obtain ⟨n, hn⟩ := hp
  have hlt : (1 : Int) * ((1 : Nat) : Int) < 0 * ((n + 1 : Nat) : Int) := hn
  omega

end UOR.Bridge.F1Square.Square
