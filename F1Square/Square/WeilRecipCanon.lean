/-
F1 square — **the CANONICAL-BAND real reciprocal transpose** (`WeilRecipCanon.lean`):

    `x⁻¹·F⁺_{f,g}(x⁻¹) ≈ F⁺_{g,f}(x)`   for every REAL `1 ≤ x ≤ C.X+1`,

with the weight band instantiated from the `NormCtx` ALONE: `B = C.X+1`, `c = B⁻¹` (so `c·B = 1`
EXACTLY, `canonC_mul_B`), `N = C.X+1`, and `c ≤ C.b·C.a` PROVED from `C.hband_lo` (`canonC_le_ba`).

The rational layer underneath (every rational `q ≥ 1`, `q = 1` included):
  • `normWeight_recip_Q` — the INDEPENDENTLY proved weight identity `normWeight(q⁻¹) = q·normWeight(q)`
    (unique non-negative root: `(q·√(1/q))² = q²/q = q = 1/(1/q)`);
  • `BForm_adjoint_swap_all_Q` — `B_{1/q}(f,g) = q·B_q(g,f)` from `HForm_recip_all_Q` (the rational
    Haar-dilation reciprocity `H_q(f,g) = H_{1/q}(g,f)`, no overlap hypothesis);
  • `FTwo_recip_Q` — rational `F⁺` reciprocity `q⁻¹·F⁺_{f,g}(q⁻¹) = F⁺_{g,f}(q)` by the exact readbacks.
The real extension is `FTwo_recip_real` (`WeilRecipReal.lean`): band-preserving rational
approximation (`Req_of_lipschitz_dense`) with the explicit reciprocal/composite continuity bounds.

Nothing here is a hypothesis: no reciprocity is assumed, no side is defined by reflection.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.WeilRecipReal
import F1Square.Square.ClosedWeilBilin

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- (1) Rational helpers.
-- ===========================================================================

/-- `Qinv` is an involution on the positive cone. -/
theorem qinv_qinv {a : Q} (han : 0 < a.num) : Qeq (Qinv (Qinv a)) a := by
  have hn : (Qinv (Qinv a)).num = a.num := by
    simp only [Qinv]; exact Int.toNat_of_nonneg (Int.le_of_lt han)
  have hd : ((Qinv (Qinv a)).den : Int) = (a.den : Int) := by
    simp only [Qinv]; omega
  show (Qinv (Qinv a)).num * (a.den : Int) = a.num * ((Qinv (Qinv a)).den : Int)
  rw [hn, hd]

/-- `1 ≤ q ⟹ 1/q ≤ 1`. -/
theorem qinv_le_one {q : Q} (hqd : 0 < q.den) (hq1 : Qle (⟨1, 1⟩ : Q) q) :
    Qle (Qinv q) (⟨1, 1⟩ : Q) := by
  have hqn : 0 < q.num := qnum_pos_of_one_le hqd hq1
  have hqq := hq1
  simp only [Qle] at hqq
  show (q.den : Int) * ((1 : Nat) : Int) ≤ 1 * ((q.num.toNat : Nat) : Int)
  push_cast [Int.toNat_of_nonneg (Int.le_of_lt hqn)] at hqq ⊢
  omega

/-- `(q·q)·(1/q) = 1/(1/q)` on the positive cone (rational identity behind the weight law). -/
theorem qsq_mul_qinv {q : Q} (hqn : 0 < q.num) (hqd : 0 < q.den) :
    Qeq (mul (mul q q) (Qinv q)) (Qinv (Qinv q)) := by
  have hn : (Qinv (Qinv q)).num = q.num := by
    simp only [Qinv]; exact Int.toNat_of_nonneg (Int.le_of_lt hqn)
  have hd : ((Qinv (Qinv q)).den : Int) = (q.den : Int) := by
    simp only [Qinv]; omega
  have hin : (Qinv q).num = (q.den : Int) := rfl
  have hid : ((Qinv q).den : Int) = q.num := by
    simp only [Qinv]; exact Int.toNat_of_nonneg (Int.le_of_lt hqn)
  show (mul (mul q q) (Qinv q)).num * ((Qinv (Qinv q)).den : Int)
      = (Qinv (Qinv q)).num * ((mul (mul q q) (Qinv q)).den : Int)
  simp only [mul]
  rw [hn, hd, hin]
  push_cast
  rw [hid]
  ring_uor

-- ===========================================================================
-- (2) The independently proved weight identity `normWeight(q⁻¹) = q·normWeight(q)`.
-- ===========================================================================

/-- **THE WEIGHT IDENTITY at every positive rational**: `normWeight(1/q) ≈ q·normWeight(q)` — the
    unique non-negative root of `1/(1/q)`: `(q·√(1/q))² = (q·q)·(1/q) = 1/(1/q)`. -/
theorem normWeight_recip_Q (q : Q) (hqn : 0 < q.num) (hqd : 0 < q.den) :
    Req (normWeight (Qinv q)) (Rmul (ofQ q hqd) (normWeight q)) := by
  have hqin : 0 < (Qinv q).num := Qinv_num_pos hqd
  have hqid : 0 < (Qinv q).den := Qinv_den_pos hqn
  refine Req_trans (normWeight_pos_eq hqin) ?_
  refine Req_trans ?_ (Rmul_congr (Req_refl _) (Req_symm (normWeight_pos_eq hqn)))
  refine Req_symm (Rsqrt_unique (Qinv_den_pos hqin) (qinv_num_nonneg _) ?_ ?_)
  · exact Rnonneg_Rmul (Rnonneg_ofQ hqd (Int.le_of_lt hqn)) (Rsqrt_nonneg _ _ _)
  · refine Req_trans (Rmul_mul_mul_comm _ _ _ _) ?_
    refine Req_trans (Rmul_congr (Rmul_ofQ_ofQ hqd hqd) (Rsqrt_sq _ _ _)) ?_
    refine Req_trans (Rmul_ofQ_ofQ (Qmul_den_pos hqd hqd) hqid) ?_
    exact ofQ_congr _ _ (qsq_mul_qinv hqn hqd)

-- ===========================================================================
-- (3) The adjoint swap law at every rational scale `q ≥ 1`.
-- ===========================================================================

/-- **THE ADJOINT SWAP LAW at every rational `q ≥ 1`**: `B_{1/q}(f,g) ≈ q·B_q(g,f)` — from the rational
    Haar-dilation reciprocity `H_q(g,f) = H_{1/q}(f,g)` (`HForm_recip_all_Q`, `q = 1` included) and the
    weight identity `normWeight_recip_Q`. -/
theorem BForm_adjoint_swap_all_Q (f g : L2Test) (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (b : Q) (hbd : 0 < b.den) (hbn : 0 < b.num)
    (q : Q) (hqn : 0 < q.num) (hqd : 0 < q.den) (hq1 : Qle (⟨1, 1⟩ : Q) q)
    (hgh_g : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (g.f y) zero)
    (hgl_f : ∀ y, Rle y (ofQ b hbd) → Req (f.f y) zero)
    (hfit : Qle (Qinv b) (add a w)) :
    Req (BForm f g (Qinv q) (Qinv_num_pos hqd) (Qinv_den_pos hqn) a han had w hw hwn)
        (Rmul (ofQ q hqd) (BForm g f q hqn hqd a han had w hw hwn)) := by
  show Req (Rmul (normWeight (Qinv q))
              (HForm f g (Qinv q) (Qinv_num_pos hqd) (Qinv_den_pos hqn) a han had w hw hwn))
           (Rmul (ofQ q hqd) (Rmul (normWeight q) (HForm g f q hqn hqd a han had w hw hwn)))
  refine Req_trans (Rmul_congr (Req_refl _)
      (Req_symm (HForm_recip_all_Q g f a han had w hw hwn b hbd hbn q hqn hqd hq1
        hgh_g hgl_f hfit))) ?_
  refine Req_trans (Rmul_congr (normWeight_recip_Q q hqn hqd) (Req_refl _)) ?_
  exact Rmul_assoc _ _ _

-- ===========================================================================
-- (4) Rational `F⁺` reciprocity `q⁻¹·F⁺_{f,g}(q⁻¹) = F⁺_{g,f}(q)`.
-- ===========================================================================

/-- **RATIONAL `F⁺` RECIPROCITY** at every rational `1 ≤ q ≤ B`, `q ≤ S` (with `c ≤ 1/q`, automatic
    for `c = 1/B`): `q⁻¹·F⁺_{f,g}(q⁻¹) ≈ F⁺_{g,f}(q)` — by the exact readbacks `FTwo_ofQ` on both
    sides of `1` and the adjoint swap law. -/
theorem FTwo_recip_Q (c B : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (hBd : 0 < B.den)
    (hB1 : Qle (⟨1, 1⟩ : Q) B) (hcB : Qle c B) (hc1 : Qle c (⟨1, 1⟩ : Q))
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q))
    (f g : L2Test) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (b : Q) (hbd : 0 < b.den) (hbn : 0 < b.num)
    (hgh_g : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (g.f y) zero)
    (hgl_f : ∀ y, Rle y (ofQ b hbd) → Req (f.f y) zero)
    (hfit : Qle (Qinv b) (add a w))
    (q : Q) (hqd : 0 < q.den) (hq1 : Qle (⟨1, 1⟩ : Q) q) (hqB : Qle q B) (hqS : Qle q S)
    (hcq : Qle c (Qinv q)) :
    Req (Rmul (ofQ (Qinv q) (Qinv_den_pos (qnum_pos_of_one_le hqd hq1)))
          ((FTwo c B hcn hcd hBd hB1 hcB hc1 N hN hBN f g S hSd hSn a han had w hw hwn).f
            (ofQ (Qinv q) (Qinv_den_pos (qnum_pos_of_one_le hqd hq1)))))
        ((FTwo c B hcn hcd hBd hB1 hcB hc1 N hN hBN g f S hSd hSn a han had w hw hwn).f
          (ofQ q hqd)) := by
  have hqn : 0 < q.num := qnum_pos_of_one_le hqd hq1
  have hS1 : Qle (⟨1, 1⟩ : Q) S := Qle_trans hqd hq1 hqS
  have hqi1 : Qle (Qinv q) (⟨1, 1⟩ : Q) := qinv_le_one hqd hq1
  have hqiB : Qle (Qinv q) B := Qle_trans (by decide) hqi1 hB1
  have hqiS : Qle (Qinv q) S := Qle_trans (by decide) hqi1 hS1
  have hcq' : Qle c q := Qle_trans (by decide) hc1 hq1
  have hlo := FTwo_ofQ c B hcn hcd hBd hB1 hcB hc1 N hN hBN f g S hSd hSn a han had w hw hwn
    (Qinv q) (Qinv_den_pos hqn) hcq hqiB hqiS
  have hhi := FTwo_ofQ c B hcn hcd hBd hB1 hcB hc1 N hN hBN g f S hSd hSn a han had w hw hwn
    q hqd hcq' hqB hqS
  refine Req_trans (Rmul_congr (Req_refl _) hlo) ?_
  refine Req_trans (Rmul_congr (Req_refl _)
    (BForm_adjoint_swap_all_Q f g a han had w hw hwn b hbd hbn q hqn hqd hq1 hgh_g hgl_f hfit)) ?_
  refine Req_trans (Req_symm (Rmul_assoc (ofQ (Qinv q) (Qinv_den_pos hqn)) (ofQ q hqd) _)) ?_
  have hone : Req (Rmul (ofQ (Qinv q) (Qinv_den_pos hqn)) (ofQ q hqd)) one :=
    Req_trans (Rmul_ofQ_ofQ (Qinv_den_pos hqn) hqd)
      (ofQ_congr _ (by decide) (Qinv_mul hqd hqn))
  refine Req_trans (Rmul_congr hone (Req_refl _)) ?_
  exact Req_trans (Rone_mul _) (Req_symm hhi)

-- ===========================================================================
-- (5) The canonical band from `NormCtx`: `B = X+1`, `c = 1/B`, `c·B = 1`, `c ≤ b·a`.
-- ===========================================================================

/-- The canonical band cap `B = C.X+1`. -/
def canonB (C : NormCtx) : Q := ⟨((C.X + 1 : Nat) : Int), 1⟩

/-- The canonical lower band edge `c = B⁻¹ = 1/(C.X+1)`. -/
def canonC (C : NormCtx) : Q := Qinv (canonB C)

theorem canonB_den (C : NormCtx) : 0 < (canonB C).den := Nat.one_pos

theorem canonB_num (C : NormCtx) : 0 < (canonB C).num := by
  show (0 : Int) < ((C.X + 1 : Nat) : Int); omega

theorem canonB_one (C : NormCtx) : Qle (⟨1, 1⟩ : Q) (canonB C) := by
  show (1 : Int) * ((1 : Nat) : Int) ≤ ((C.X + 1 : Nat) : Int) * ((1 : Nat) : Int)
  push_cast; omega

theorem canonC_num (C : NormCtx) : 0 < (canonC C).num := Qinv_num_pos (canonB_den C)

theorem canonC_den (C : NormCtx) : 0 < (canonC C).den := Qinv_den_pos (canonB_num C)

/-- **`c·B = 1` EXACTLY** for the canonical band. -/
theorem canonC_mul_B (C : NormCtx) : Qeq (mul (canonC C) (canonB C)) (⟨1, 1⟩ : Q) :=
  Qinv_mul (canonB_den C) (canonB_num C)

theorem canonC_mul_B_le (C : NormCtx) : Qle (mul (canonC C) (canonB C)) (⟨1, 1⟩ : Q) := by
  have h := canonC_mul_B C
  simp only [Qeq] at h; simp only [Qle]; omega

theorem canonC_le_one (C : NormCtx) : Qle (canonC C) (⟨1, 1⟩ : Q) :=
  qinv_le_one (canonB_den C) (canonB_one C)

theorem canonC_le_B (C : NormCtx) : Qle (canonC C) (canonB C) :=
  Qle_trans (by decide) (canonC_le_one C) (canonB_one C)

theorem canonB_le_N (C : NormCtx) : Qle (canonB C) (⟨((C.X + 1 : Nat) : Int), 1⟩ : Q) := Qle_refl _

theorem canonB_le_S (C : NormCtx) : Qle (canonB C) C.S := C.hTS

/-- **`c ≤ C.b·C.a` from `C.hband_lo`** (`1 ≤ ((X+1)·b)·a ⟺ 1/(X+1) ≤ b·a`): the canonical lower band
    edge sits below the lower support edge of the reflected window — the two-sided weight's genuine
    `x^{-1/2}` region covers the whole low side of the correlation. -/
theorem canonC_le_ba (C : NormCtx) : Qle (canonC C) (mul C.b C.a) := by
  have h := C.hband_lo
  simp only [Qle, mul] at h
  show (1 : Int) * ((mul C.b C.a).den : Int) ≤ (mul C.b C.a).num * (((C.X + 1 : Nat) : Int).toNat : Int)
  simp only [mul]
  push_cast at h ⊢
  have ht : ((((C.X : Int) + 1).toNat : Nat) : Int) = (C.X : Int) + 1 :=
    Int.toNat_of_nonneg (by omega)
  rw [ht]
  have e1 : C.b.num * C.a.num * ((C.X : Int) + 1)
      = ((C.X : Int) + 1) * C.b.num * C.a.num := by ring_uor
  have e2 : (1 : Int) * ((C.b.den : Int) * (C.a.den : Int)) = 1 * (C.b.den : Int) * (C.a.den : Int) := by
    ring_uor
  omega

-- ===========================================================================
-- (6) THE CANONICAL-BAND RECIPROCAL TRANSPOSE.
-- ===========================================================================

/-- The canonical two-sided normalized correlation of a `NormCtx` (band `[1/(X+1), X+1]`, `N = X+1`). -/
def FCanon (C : NormCtx) (f g : L2Test) : L2Test :=
  FTwo (canonC C) (canonB C) (canonC_num C) (canonC_den C) (canonB_den C) (canonB_one C)
    (canonC_le_B C) (canonC_le_one C) (C.X + 1) (Nat.succ_pos C.X) (canonB_le_N C)
    f g C.S C.hSd C.hSn C.a C.han C.had C.w C.hw C.hwn

/-- Rational canonical reciprocity `q⁻¹·F⁺_{f,g}(q⁻¹) ≈ F⁺_{g,f}(q)` for every rational `1 ≤ q ≤ X+1`
    (core tests of the canonical geometry). -/
theorem FCanon_recip_Q (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g)
    (q : Q) (hqd : 0 < q.den) (hq1 : Qle (⟨1, 1⟩ : Q) q) (hqB : Qle q (canonB C)) :
    Req (Rmul (ofQ (Qinv q) (Qinv_den_pos (qnum_pos_of_one_le hqd hq1)))
          ((FCanon C f g).f (ofQ (Qinv q) (Qinv_den_pos (qnum_pos_of_one_le hqd hq1)))))
        ((FCanon C g f).f (ofQ q hqd)) := by
  have hcq : Qle (canonC C) (Qinv q) :=
    Qinv_antitone (canonB_num C) (qnum_pos_of_one_le hqd hq1) hqB
  exact FTwo_recip_Q (canonC C) (canonB C) (canonC_num C) (canonC_den C) (canonB_den C) (canonB_one C)
    (canonC_le_B C) (canonC_le_one C) (C.X + 1) (Nat.succ_pos C.X) (canonB_le_N C)
    f g C.S C.hSd C.hSn C.a C.han C.had C.w C.hw C.hwn C.b C.hbd C.hbnpos hg.hgh hf.hgl C.hfit
    q hqd hq1 hqB (Qle_trans (canonB_den C) hqB (canonB_le_S C)) hcq

/-- **★★ THE CANONICAL-BAND REAL RECIPROCAL TRANSPOSE**
    `x⁻¹·F⁺_{f,g}(x⁻¹) ≈ F⁺_{g,f}(x)` for EVERY REAL `1 ≤ x ≤ C.X+1`, band and scale instantiated from
    the `NormCtx` alone (`c·B = 1` exactly), for core tests of the canonical geometry.  The reciprocal
    `x⁻¹` and the argument `x⁻¹` are both `clampedInv 1 x` (inert on `x ≥ 1`; no positivity witness).
    Proved by band-preserving rational approximation from the rational law — never assumed. -/
theorem FCanon_recip_real (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g)
    (x : Real) (hx1 : Rle one x) (hxB : Rle x (ofQ (canonB C) (canonB_den C))) :
    Req (Rmul (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x)
          ((FCanon C f g).f (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x)))
        ((FCanon C g f).f x) :=
  FTwo_recip_real (canonC C) (canonB C) (canonC_num C) (canonC_den C) (canonB_den C) (canonB_one C)
    (canonC_le_B C) (canonC_le_one C) (canonC_mul_B_le C) (C.X + 1) (Nat.succ_pos C.X) (canonB_le_N C)
    f g C.S C.hSd C.hSn C.a C.han C.had C.w C.hw C.hwn C.b C.hbd C.hbnpos hg.hgh hf.hgl C.hfit
    (canonB C) (canonB_den C) (canonB_one C) (canonB_le_S C) (Qle_refl _) x hx1 hxB

end UOR.Bridge.F1Square.Square
