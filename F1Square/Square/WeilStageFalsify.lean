/-
F1 square — **an explicit core test on an explicit context** (`WeilStageFalsify.lean`, part 1):
the tent `t(y) = max(0, 1 − (3/2)·|y − 4/3|)` (support `[2/3, 2]`, peak at `4/3`) as an `L2Test`, and
the concrete `NormCtx` `C₀` with `a = 1/2`, `b = 2/3`, `X = 2`, `S = 3`, `w = 1` whose own test is the
tent — so `ClosedCore C₀` is INHABITED by an explicit function.  This is the substrate on which the
sign of the prime component of the coupled form is certified numerically (part 2).
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.WeilDominance
import F1Square.Analysis.ClampedInvLower
import F1Square.Analysis.ClampOne

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- (1) The clamp collapses below its floor.
-- ===========================================================================

/-- `max(x, a) = a` when `x ≤ a`. -/
theorem qClampQ_eq_of_le {a : Q} {had : 0 < a.den} {x : Real} (hx : Rle x (ofQ a had)) :
    Req (qClampQ a had x) (ofQ a had) := by
  refine Req_of_lin_bound (C := 2) ?_
  intro n
  show Qle (Qabs (Qsub (Qmax (x.seq n) a) a)) (⟨(2 : Int), n + 1⟩ : Q)
  have h1 : Qle a (Qmax (x.seq n) a) := Qmax_ge_right (x.seq n) a
  have hxn : Qle (x.seq n) (add a (⟨2, n + 1⟩ : Q)) := hx n
  have h2 : Qle (Qmax (x.seq n) a) (add a (⟨2, n + 1⟩ : Q)) :=
    Qmax_le hxn (Qle_self_add (by show (0 : Int) ≤ 2; decide))
  refine Qabs_le_of_both (Qsub_le_of_le_add had (Nat.succ_pos n) h2) ?_
  -- −(Qmax − a) ≤ 2/(n+1) since 0 ≤ Qmax − a
  have h3 := Qsub_num_nonneg h1
  show (neg (Qsub (Qmax (x.seq n) a) a)).num * ((n + 1 : Nat) : Int) ≤ 2 * ((Qsub (Qmax (x.seq n) a) a).den : Int)
  simp only [neg]
  have hd : (0 : Int) ≤ ((Qsub (Qmax (x.seq n) a) a).den : Int) := Int.ofNat_nonneg _
  have hp : 0 ≤ (Qsub (Qmax (x.seq n) a) a).num * ((n + 1 : Nat) : Int) := Int.mul_nonneg h3 (Int.ofNat_nonneg _)
  rw [Int.neg_mul]
  omega

-- ===========================================================================
-- (2) The tent test `t(y) = max(0, 1 − (3/2)·|y − 4/3|)`.
-- ===========================================================================

/-- The raw tent profile before clamping. -/
def tentRaw (y : Real) : Real :=
  Rsub one (Rmul (ofQ (⟨3, 2⟩ : Q) (Nat.succ_pos 1)) (Rabs (Rsub y (ofQ (⟨4, 3⟩ : Q) (by decide)))))

theorem tentRaw_le_one (y : Real) : Rle (tentRaw y) one := by
  refine Rle_trans (Rsub_le_mono (Rle_refl one) (Rle_zero_of_Rnonneg
    (Rnonneg_Rmul (Rnonneg_ofQ (Nat.succ_pos 1) (by decide)) (Rnonneg_Rabs _)))) (Rle_of_Req (Rsub_zero one))

/-- `|tentRaw x − tentRaw y| ≤ (3/2)·|x − y|`. -/
theorem tentRaw_lip (x y : Real) :
    Rle (Rabs (Rsub (tentRaw x) (tentRaw y))) (Rmul (ofQ (⟨3, 2⟩ : Q) (Nat.succ_pos 1)) (Rabs (Rsub x y))) := by
  unfold tentRaw
  -- (1 − cA) − (1 − cB) = (1 − 1) − (cA − cB) = −(c(A − B))
  refine Rle_trans (Rle_of_Req (Rabs_congr (Rsub_sub_sub _ _ _ _))) ?_
  refine Rle_trans (Rle_of_Req (Rabs_congr (Rsub_congr (Radd_neg one) (Req_symm (Rmul_sub_distrib _ _ _))))) ?_
  refine Rle_trans (Rle_of_Req (Rabs_congr (Req_trans (Radd_comm _ _) (Radd_zero _)))) ?_
  refine Rle_trans (Rle_of_Req (Rabs_Rneg _)) ?_
  refine Rle_trans (Rle_of_Req (Rabs_Rmul_ofQ_nonneg (Nat.succ_pos 1) (by decide) _)) ?_
  refine Rmul_le_Rmul_left (Rnonneg_ofQ (Nat.succ_pos 1) (by decide)) ?_
  refine Rle_trans (Rabs_Rabs_sub_le _ _) ?_
  exact Rle_of_Req (Rabs_congr (add_shift_iso_gen x y _))

theorem tentRaw_congr {x y : Real} (h : Req x y) : Req (tentRaw x) (tentRaw y) :=
  Rsub_congr (Req_refl _) (Rmul_congr (Req_refl _) (Rabs_congr (Rsub_congr h (Req_refl _))))

/-- **The tent test.** -/
def tentTest43 : L2Test where
  f := fun y => qClampQ (⟨0, 1⟩ : Q) Nat.one_pos (tentRaw y)
  L := ⟨3, 2⟩
  M := ⟨1, 1⟩
  hLd := Nat.succ_pos 1
  hLn := by decide
  hMd := Nat.one_pos
  hMn := by decide
  hlip := fun x y => Rle_trans (qClampQ_lipschitz _ _ _ _) (tentRaw_lip x y)
  hfc := fun x y h => qClampQ_congr _ _ (tentRaw_congr h)
  hbd := fun y => by
    refine Rle_trans (Rle_of_Req (Rabs_of_nonneg (Rnonneg_of_Rle_zero (Rle_ofQ_qClampQ _ _ _)))) ?_
    exact Rle_qClampQ_ofQ Nat.one_pos Nat.one_pos (tentRaw_le_one y) (by decide)

theorem tentTest43_f (y : Real) : tentTest43.f y = qClampQ (⟨0, 1⟩ : Q) Nat.one_pos (tentRaw y) := rfl

/-- The tent vanishes once `|y − 4/3| ≥ 2/3`. -/
theorem tent_vanish_of_far (y : Real)
    (h : Rle (ofQ (⟨2, 3⟩ : Q) (by decide)) (Rabs (Rsub y (ofQ (⟨4, 3⟩ : Q) (by decide))))) :
    Req (tentTest43.f y) zero := by
  rw [tentTest43_f]
  refine Req_trans (qClampQ_eq_of_le ?_) (Req_of_seq_Qeq (fun _ => Qeq_refl _))
  unfold tentRaw
  -- 1 − (3/2)·|…| ≤ 1 − (3/2)(2/3) = 0
  refine Rle_trans (Rsub_le_mono (Rle_refl one)
    (Rmul_le_Rmul_left (Rnonneg_ofQ (Nat.succ_pos 1) (by decide)) h)) ?_
  refine Rle_of_Req ?_
  refine Req_trans (Rsub_congr (Req_refl _) (Req_trans (Rmul_ofQ_ofQ _ _) (ofQ_congr _ Nat.one_pos
    (by decide : Qeq (mul (⟨3, 2⟩ : Q) (⟨2, 3⟩ : Q)) (⟨1, 1⟩ : Q))))) ?_
  exact Radd_neg one

theorem tent_vanish_high (y : Real) (hy : Rle (ofQ (⟨2, 1⟩ : Q) Nat.one_pos) y) : Req (tentTest43.f y) zero := by
  refine tent_vanish_of_far y (Rle_trans ?_ (Rle_Rabs_self _))
  -- 2/3 ≤ y − 4/3  ⟸  2 ≤ y
  have h : Rle (Rsub (ofQ (⟨2, 1⟩ : Q) Nat.one_pos) (ofQ (⟨4, 3⟩ : Q) (by decide)))
      (Rsub y (ofQ (⟨4, 3⟩ : Q) (by decide))) := Rsub_le_mono hy (Rle_refl _)
  refine Rle_trans (Rle_of_Req ?_) h
  exact Req_symm (Req_trans (Rsub_ofQ_ofQ _ _) (ofQ_congr _ (by decide) (by decide)))

theorem tent_vanish_low (y : Real) (hy : Rle y (ofQ (⟨2, 3⟩ : Q) (by decide))) : Req (tentTest43.f y) zero := by
  refine tent_vanish_of_far y ?_
  refine Rle_trans ?_ (Rle_trans (Rle_Rabs_self _) (Rle_of_Req (Rabs_Rsub_symm _ _)))
  -- 2/3 ≤ 4/3 − y  ⟸  y ≤ 2/3
  have h : Rle (Rsub (ofQ (⟨4, 3⟩ : Q) (by decide)) (ofQ (⟨2, 3⟩ : Q) (by decide)))
      (Rsub (ofQ (⟨4, 3⟩ : Q) (by decide)) y) := Rsub_le_mono (Rle_refl _) hy
  refine Rle_trans (Rle_of_Req ?_) h
  exact Req_symm (Req_trans (Rsub_ofQ_ofQ _ _) (ofQ_congr _ (by decide) (by decide)))

-- ===========================================================================
-- (3) The concrete context `C₀`.
-- ===========================================================================

/-- **`C₀`**: `a = 1/2`, `b = 2/3`, `X = 2`, `S = 3`, `w = 1`, test = the tent. -/
def ctx0 : NormCtx where
  g := tentTest43
  S := ⟨3, 1⟩
  hSd := Nat.one_pos
  hSn := by decide
  a := ⟨1, 2⟩
  han := by decide
  had := Nat.succ_pos 1
  w := ⟨1, 1⟩
  hw := Nat.one_pos
  hwn := by decide
  X := 2
  hX := by decide
  b := ⟨2, 3⟩
  hbd := by decide
  hbn := by decide
  hTS := by decide
  hS1 := by decide
  hband_hi := by decide
  hband_lo := by decide
  hbnpos := by decide
  hfit := by decide
  hgh := fun y hy => tent_vanish_high y (Rle_trans (Rle_of_Req (ofQ_congr _ Nat.one_pos
    (by decide : Qeq (Qinv (⟨1, 2⟩ : Q)) (⟨2, 1⟩ : Q)))) hy)
  hgl := fun y hy => tent_vanish_low y hy

/-- The tent is a core test of `C₀`. -/
theorem tent_core : CoreTest ctx0.geom tentTest43 := normCtx_core ctx0

-- ===========================================================================
-- (5) Pointwise lower bounds of the tent.
-- ===========================================================================

/-- `tent(u) ≥ 1 − (3/2)·r` whenever `|u − 4/3| ≤ r`. -/
theorem tent_ge_of_close (u : Real) (r : Q) (hrd : 0 < r.den)
    (hr : Rle (Rabs (Rsub u (ofQ (⟨4, 3⟩ : Q) (by decide)))) (ofQ r hrd)) :
    Rle (Rsub one (Rmul (ofQ (⟨3, 2⟩ : Q) (Nat.succ_pos 1)) (ofQ r hrd))) (tentTest43.f u) := by
  rw [tentTest43_f]
  refine Rle_trans ?_ (Rle_self_qClampQ _ _ _)
  unfold tentRaw
  exact Rsub_le_mono (Rle_refl one) (Rmul_le_Rmul_left (Rnonneg_ofQ (Nat.succ_pos 1) (by decide)) hr)

/-- `tent(u) ≥ 1/8` for `3/4 ≤ u ≤ 11/12` (`|u − 4/3| ≤ 7/12`). -/
theorem tent_ge_eighth (u : Real) (hlo : Rle (ofQ (⟨3, 4⟩ : Q) (by decide)) u)
    (hhi : Rle u (ofQ (⟨11, 12⟩ : Q) (by decide))) :
    Rle (ofQ (⟨1, 8⟩ : Q) (by decide)) (tentTest43.f u) := by
  have habs : Rle (Rabs (Rsub u (ofQ (⟨4, 3⟩ : Q) (by decide)))) (ofQ (⟨7, 12⟩ : Q) (by decide)) := by
    refine Rabs_le_of_both ?_ ?_
    · -- u − 4/3 ≤ 11/12 − 4/3 = −5/12 ≤ 7/12
      refine Rle_trans (Rsub_le_mono hhi (Rle_refl _)) ?_
      refine Rle_trans (Rle_of_Req (Rsub_ofQ_ofQ _ _)) (Rle_ofQ_ofQ _ _ (by decide))
    · -- −(u − 4/3) = 4/3 − u ≤ 4/3 − 3/4 = 7/12
      refine Rle_trans (Rle_of_Req (Rneg_Rsub _ _)) ?_
      refine Rle_trans (Rsub_le_mono (Rle_refl _) hlo) ?_
      refine Rle_trans (Rle_of_Req (Rsub_ofQ_ofQ _ _)) (Rle_ofQ_ofQ _ _ (by decide))
  refine Rle_trans ?_ (tent_ge_of_close u (⟨7, 12⟩ : Q) (by decide) habs)
  refine Rle_of_Req ?_
  refine Req_symm (Req_trans (Rsub_congr (Req_refl _) (Rmul_ofQ_ofQ _ _)) ?_)
  exact Req_trans (Rsub_ofQ_ofQ _ _) (ofQ_congr _ (by decide) (by decide))

/-- `tent(v) ≥ 1/4` for `3/2 ≤ v ≤ 11/6` (`|v − 4/3| ≤ 1/2`). -/
theorem tent_ge_quarter (v : Real) (hlo : Rle (ofQ (⟨3, 2⟩ : Q) (Nat.succ_pos 1)) v)
    (hhi : Rle v (ofQ (⟨11, 6⟩ : Q) (by decide))) :
    Rle (ofQ (⟨1, 4⟩ : Q) (by decide)) (tentTest43.f v) := by
  have habs : Rle (Rabs (Rsub v (ofQ (⟨4, 3⟩ : Q) (by decide)))) (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1)) := by
    refine Rabs_le_of_both ?_ ?_
    · refine Rle_trans (Rsub_le_mono hhi (Rle_refl _)) ?_
      refine Rle_trans (Rle_of_Req (Rsub_ofQ_ofQ _ _)) (Rle_ofQ_ofQ _ _ (by decide))
    · refine Rle_trans (Rle_of_Req (Rneg_Rsub _ _)) ?_
      refine Rle_trans (Rsub_le_mono (Rle_refl _) hlo) ?_
      refine Rle_trans (Rle_of_Req (Rsub_ofQ_ofQ _ _)) (Rle_ofQ_ofQ _ _ (by decide))
  refine Rle_trans ?_ (tent_ge_of_close v (⟨1, 2⟩ : Q) (Nat.succ_pos 1) habs)
  refine Rle_of_Req ?_
  refine Req_symm (Req_trans (Rsub_congr (Req_refl _) (Rmul_ofQ_ofQ _ _)) ?_)
  exact Req_trans (Rsub_ofQ_ofQ _ _) (ofQ_congr _ (by decide) (by decide))

theorem tent_nonneg (y : Real) : Rnonneg (tentTest43.f y) :=
  Rnonneg_of_Rle_zero (Rle_ofQ_qClampQ _ _ _)


-- ===========================================================================
-- (6) `H₂(tent, tent)` on `C₀` is strictly positive: a certified lower bound `1/176`.
-- ===========================================================================

/-- The Haar autocorrelation integrand of the tent at lag `2`:
    `G(x) = (tent(2·(1/max(x,1/2)))·tent(1/max(x,1/2)))·(1/max(x,1/2))`. -/
def tentG (x : Real) : Real :=
  Rmul (Rmul (tentTest43.f (Rmul (ofQ (⟨2, 1⟩ : Q) Nat.one_pos) (clampedInv (⟨1, 2⟩ : Q) (by decide) (Nat.succ_pos 1) x)))
             (tentTest43.f (clampedInv (⟨1, 2⟩ : Q) (by decide) (Nat.succ_pos 1) x)))
       (clampedInv (⟨1, 2⟩ : Q) (by decide) (Nat.succ_pos 1) x)

/-- `H₂(tent,tent)` over `C₀` IS the certified integral of `tentG` over `[1/2, 3/2]`. -/
theorem HForm_tent_unfold :
    HForm tentTest43 tentTest43 (⟨2, 1⟩ : Q) (by decide) Nat.one_pos (⟨1, 2⟩ : Q) (by decide) (Nat.succ_pos 1)
        (⟨1, 1⟩ : Q) Nat.one_pos (by decide)
      = riemannIntegralI
          (l2L_den (productTest (reflectTest (⟨1, 2⟩ : Q) (by decide) (Nat.succ_pos 1)
              (dilateTest (⟨2, 1⟩ : Q) (by decide) Nat.one_pos tentTest43))
            (reflectTest (⟨1, 2⟩ : Q) (by decide) (Nat.succ_pos 1) tentTest43))
            (recipTest (⟨1, 2⟩ : Q) (by decide) (Nat.succ_pos 1)))
          (l2L_num _ _) (l2lip _ _) (l2fc _ _) (⟨1, 2⟩ : Q) (⟨1, 1⟩ : Q) (Nat.succ_pos 1) Nat.one_pos (by decide) :=
  rfl

/-- The integrand's value is `tentG`. -/
theorem tent_integrand_f (x : Real) :
    Rmul ((productTest (reflectTest (⟨1, 2⟩ : Q) (by decide) (Nat.succ_pos 1)
            (dilateTest (⟨2, 1⟩ : Q) (by decide) Nat.one_pos tentTest43))
          (reflectTest (⟨1, 2⟩ : Q) (by decide) (Nat.succ_pos 1) tentTest43)).f x)
         ((recipTest (⟨1, 2⟩ : Q) (by decide) (Nat.succ_pos 1)).f x) = tentG x := rfl

theorem tentG_nonneg (x : Real) : Rnonneg (tentG x) :=
  Rnonneg_Rmul (Rnonneg_Rmul (tent_nonneg _) (tent_nonneg _)) (Rnonneg_clampedInv _ _ _ _)

/-- On `12/11 ≤ x ≤ 4/3`: `tentG x ≥ 3/128`. -/
theorem tentG_ge (x : Real) (hlo : Rle (ofQ (⟨12, 11⟩ : Q) (by decide)) x)
    (hhi : Rle x (ofQ (⟨4, 3⟩ : Q) (by decide))) :
    Rle (ofQ (⟨3, 128⟩ : Q) (by decide)) (tentG x) := by
  have hxa : Rle (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1)) x :=
    Rle_trans (Rle_ofQ_ofQ _ _ (by decide)) hlo
  obtain ⟨kx, hkx⟩ := Pos_of_Rle_ofQ (by decide) (Nat.succ_pos 1) hxa
  have hu : Req (clampedInv (⟨1, 2⟩ : Q) (by decide) (Nat.succ_pos 1) x) (Rinv x kx hkx) :=
    clampedInv_eq_of_ge (a := (⟨1, 2⟩ : Q)) (han := by decide) (had := Nat.succ_pos 1) hkx hxa
  -- 3/4 ≤ 1/x ≤ 11/12
  have hu_hi : Rle (Rinv x kx hkx) (ofQ (⟨11, 12⟩ : Q) (by decide)) :=
    Rle_trans (Rinv_le_ofQ_inv (a := (⟨12, 11⟩ : Q)) (by decide) (by decide) hkx hlo)
      (Rle_of_Req (ofQ_congr _ (by decide) (by decide : Qeq (Qinv (⟨12, 11⟩ : Q)) (⟨11, 12⟩ : Q))))
  have hu_lo : Rle (ofQ (⟨3, 4⟩ : Q) (by decide)) (Rinv x kx hkx) :=
    Rle_trans (Rle_of_Req (ofQ_congr _ _ (by decide : Qeq (⟨3, 4⟩ : Q) (Qinv (⟨4, 3⟩ : Q)))))
      (Rinv_ge_ofQ_inv (B := (⟨4, 3⟩ : Q)) (by decide) (by decide) hkx hhi)
  have hu_hi' : Rle (clampedInv (⟨1, 2⟩ : Q) (by decide) (Nat.succ_pos 1) x) (ofQ (⟨11, 12⟩ : Q) (by decide)) :=
    Rle_trans (Rle_of_Req hu) hu_hi
  have hu_lo' : Rle (ofQ (⟨3, 4⟩ : Q) (by decide)) (clampedInv (⟨1, 2⟩ : Q) (by decide) (Nat.succ_pos 1) x) :=
    Rle_trans hu_lo (Rle_of_Req (Req_symm hu))
  -- 3/2 ≤ 2u ≤ 11/6
  have h2 : Rnonneg (ofQ (⟨2, 1⟩ : Q) Nat.one_pos) := Rnonneg_ofQ Nat.one_pos (by decide)
  have hv_lo : Rle (ofQ (⟨3, 2⟩ : Q) (Nat.succ_pos 1))
      (Rmul (ofQ (⟨2, 1⟩ : Q) Nat.one_pos) (clampedInv (⟨1, 2⟩ : Q) (by decide) (Nat.succ_pos 1) x)) :=
    Rle_trans (Rle_of_Req (Req_symm (Req_trans (Rmul_ofQ_ofQ _ _) (ofQ_congr _ _ (by decide)))))
      (Rmul_le_Rmul_left h2 hu_lo')
  have hv_hi : Rle (Rmul (ofQ (⟨2, 1⟩ : Q) Nat.one_pos) (clampedInv (⟨1, 2⟩ : Q) (by decide) (Nat.succ_pos 1) x))
      (ofQ (⟨11, 6⟩ : Q) (by decide)) :=
    Rle_trans (Rmul_le_Rmul_left h2 hu_hi')
      (Rle_of_Req (Req_trans (Rmul_ofQ_ofQ _ _) (ofQ_congr _ _ (by decide))))
  have hf1 := tent_ge_quarter _ hv_lo hv_hi
  have hf2 := tent_ge_eighth _ hu_lo' hu_hi'
  unfold tentG
  have hprod : Req (Rmul (Rmul (ofQ (⟨1, 4⟩ : Q) (by decide)) (ofQ (⟨1, 8⟩ : Q) (by decide)))
      (ofQ (⟨3, 4⟩ : Q) (by decide))) (ofQ (⟨3, 128⟩ : Q) (by decide)) :=
    Req_trans (Rmul_congr (Rmul_ofQ_ofQ (by decide) (by decide)) (Req_refl _))
      (Req_trans (Rmul_ofQ_ofQ (Qmul_den_pos (by decide) (by decide)) (by decide))
        (ofQ_congr (Qmul_den_pos (Qmul_den_pos (by decide) (by decide)) (by decide)) (by decide)
          (by decide : Qeq (mul (mul (⟨1, 4⟩ : Q) (⟨1, 8⟩ : Q)) (⟨3, 4⟩ : Q)) (⟨3, 128⟩ : Q))))
  refine Rle_trans (Rle_of_Req (Req_symm hprod)) ?_
  refine Rmul_le_Rmul_both (Rnonneg_Rmul (Rnonneg_ofQ (by decide) (by decide)) (Rnonneg_ofQ (by decide) (by decide)))
    (Rnonneg_clampedInv _ _ _ _) ?_ hu_lo'
  exact Rmul_le_Rmul_both (Rnonneg_ofQ (by decide) (by decide)) (tent_nonneg _) hf1 hf2

/-- The Lipschitz data of the integrand (abbreviations). -/
def tentInt : L2Test :=
  productTest (productTest (reflectTest (⟨1, 2⟩ : Q) (by decide) (Nat.succ_pos 1)
      (dilateTest (⟨2, 1⟩ : Q) (by decide) Nat.one_pos tentTest43))
    (reflectTest (⟨1, 2⟩ : Q) (by decide) (Nat.succ_pos 1) tentTest43))
    (recipTest (⟨1, 2⟩ : Q) (by decide) (Nat.succ_pos 1))

theorem tentInt_f (x : Real) : tentInt.f x = tentG x := rfl

/-- **`H₂(tent,tent) ≥ 1/176`** on `C₀`. -/
theorem HForm_tent_ge :
    Rle (ofQ (⟨1, 176⟩ : Q) (by decide))
      (HForm tentTest43 tentTest43 (⟨2, 1⟩ : Q) (by decide) Nat.one_pos (⟨1, 2⟩ : Q) (by decide) (Nat.succ_pos 1)
        (⟨1, 1⟩ : Q) Nat.one_pos (by decide)) := by
  rw [HForm_tent_unfold]
  -- the integral is that of tentInt over [1/2, 3/2]
  have hI : Req (riemannIntegralI (l2L_den _ _) (l2L_num _ _) (l2lip _ _) (l2fc _ _)
      (⟨1, 2⟩ : Q) (⟨1, 1⟩ : Q) (Nat.succ_pos 1) Nat.one_pos (by decide))
      (riemannIntegralI tentInt.hLd tentInt.hLn tentInt.hlip tentInt.hfc
      (⟨1, 2⟩ : Q) (⟨1, 1⟩ : Q) (Nat.succ_pos 1) Nat.one_pos (by decide)) := Req_refl _
  refine Rle_trans ?_ (Rle_of_Req (Req_symm hI))
  -- split at 13/22 then at 8/33
  have hs1 := riemannIntegralI_split_at tentInt.hLd tentInt.hLn tentInt.hlip tentInt.hfc
    (⟨1, 2⟩ : Q) (⟨1, 1⟩ : Q) (⟨13, 22⟩ : Q) (Nat.succ_pos 1) Nat.one_pos (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have hs2 := riemannIntegralI_split_at tentInt.hLd tentInt.hLn tentInt.hlip tentInt.hfc
    (add (⟨1, 2⟩ : Q) (⟨13, 22⟩ : Q)) (Qsub (⟨1, 1⟩ : Q) (⟨13, 22⟩ : Q)) (⟨8, 33⟩ : Q)
    (add_den_pos (Nat.succ_pos 1) (by decide)) (Qsub_den_pos Nat.one_pos (by decide)) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  refine Rle_trans ?_ (Rle_of_Req (Req_symm hs1))
  refine Rle_trans ?_ (Radd_le_add (Rle_refl _) (Rle_of_Req (Req_symm hs2)))
  -- lower: 0 + (middle + 0)
  have hnn1 : Rnonneg (riemannIntegralI tentInt.hLd tentInt.hLn tentInt.hlip tentInt.hfc
      (⟨1, 2⟩ : Q) (⟨13, 22⟩ : Q) (Nat.succ_pos 1) (by decide) (by decide)) :=
    riemannIntegralI_nonneg _ _ _ _ (fun x => by rw [tentInt_f]; exact tentG_nonneg x) _ _ _ _ _
  have hnn3 : Rnonneg (riemannIntegralI tentInt.hLd tentInt.hLn tentInt.hlip tentInt.hfc
      (add (add (⟨1, 2⟩ : Q) (⟨13, 22⟩ : Q)) (⟨8, 33⟩ : Q)) (Qsub (Qsub (⟨1, 1⟩ : Q) (⟨13, 22⟩ : Q)) (⟨8, 33⟩ : Q))
      (add_den_pos (add_den_pos (Nat.succ_pos 1) (by decide)) (by decide))
      (Qsub_den_pos (Qsub_den_pos Nat.one_pos (by decide)) (by decide)) (by decide)) :=
    riemannIntegralI_nonneg _ _ _ _ (fun x => by rw [tentInt_f]; exact tentG_nonneg x) _ _ _ _ _
  have hmid : Rle (ofQ (⟨1, 176⟩ : Q) (by decide))
      (riemannIntegralI tentInt.hLd tentInt.hLn tentInt.hlip tentInt.hfc
        (add (⟨1, 2⟩ : Q) (⟨13, 22⟩ : Q)) (⟨8, 33⟩ : Q) (add_den_pos (Nat.succ_pos 1) (by decide)) (by decide)
        (by decide)) := by
    have hw : Req (Rmul (ofQ (⟨8, 33⟩ : Q) (by decide)) (ofQ (⟨3, 128⟩ : Q) (by decide)))
        (ofQ (⟨1, 176⟩ : Q) (by decide)) :=
      Req_trans (Rmul_ofQ_ofQ (by decide) (by decide))
        (ofQ_congr (Qmul_den_pos (by decide) (by decide)) (by decide)
          (by decide : Qeq (mul (⟨8, 33⟩ : Q) (⟨3, 128⟩ : Q)) (⟨1, 176⟩ : Q)))
    refine Rle_trans (Rle_of_Req (Req_symm hw)) ?_
    refine riemannIntegralI_ge_const tentInt.hLd tentInt.hLn tentInt.hlip tentInt.hfc
      (ofQ (⟨3, 128⟩ : Q) (by decide)) _ _ _ _ _ (fun t h0 h1 => ?_)
    rw [tentInt_f]
    -- window points lie in [12/11, 4/3]
    have hx := affine_ge_lo (add (⟨1, 2⟩ : Q) (⟨13, 22⟩ : Q)) (⟨8, 33⟩ : Q)
      (add_den_pos (Nat.succ_pos 1) (by decide)) (by decide) (by decide) t h0
    have hxlo : Rle (ofQ (⟨12, 11⟩ : Q) (by decide))
        (affineMap (add (⟨1, 2⟩ : Q) (⟨13, 22⟩ : Q)) (⟨8, 33⟩ : Q) (add_den_pos (Nat.succ_pos 1) (by decide)) (by decide) t) :=
      Rle_trans (Rle_of_Req (ofQ_congr (by decide) (add_den_pos (Nat.succ_pos 1) (by decide))
        (by decide : Qeq (⟨12, 11⟩ : Q) (add (⟨1, 2⟩ : Q) (⟨13, 22⟩ : Q))))) hx
    have hxhi : Rle (affineMap (add (⟨1, 2⟩ : Q) (⟨13, 22⟩ : Q)) (⟨8, 33⟩ : Q) (add_den_pos (Nat.succ_pos 1) (by decide)) (by decide) t)
        (ofQ (⟨4, 3⟩ : Q) (by decide)) := by
      refine Rle_trans (Radd_le_add (Rle_refl _) (Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ (by decide) (by decide)) h1)
        (Rle_of_Req (Rmul_one _)))) ?_
      refine Rle_of_Req (Req_trans (Radd_ofQ_ofQ (add_den_pos (Nat.succ_pos 1) (by decide)) (by decide))
        (ofQ_congr (add_den_pos (add_den_pos (Nat.succ_pos 1) (by decide)) (by decide)) (by decide)
          (by decide : Qeq (add (add (⟨1, 2⟩ : Q) (⟨13, 22⟩ : Q)) (⟨8, 33⟩ : Q)) (⟨4, 3⟩ : Q))))
    exact tentG_ge _ hxlo hxhi
  refine Rle_trans ?_ (Radd_le_add (Rle_zero_of_Rnonneg hnn1) (Radd_le_add hmid (Rle_zero_of_Rnonneg hnn3)))
  have hid : Req (Radd zero (Radd (ofQ (⟨1, 176⟩ : Q) (by decide)) zero)) (ofQ (⟨1, 176⟩ : Q) (by decide)) :=
    Req_trans (Radd_congr (Req_refl zero) (Radd_zero (ofQ (⟨1, 176⟩ : Q) (by decide))))
      (Req_trans (Radd_comm zero (ofQ (⟨1, 176⟩ : Q) (by decide))) (Radd_zero (ofQ (⟨1, 176⟩ : Q) (by decide))))
  exact Rle_of_Req (Req_symm hid)

end UOR.Bridge.F1Square.Square
