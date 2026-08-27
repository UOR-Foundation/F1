/-
F1 square — **THE MEASURED ORBIT FIBER `J_{k,n,t}`** (`AtlasOrbitFiber.lean`, target-free).

For an active row `(n,t)`, `n = m+1 ≤ X`, `t ∈ [a, a+w]`, the measured orbit fiber is

    `J_{k,n,t} = [1 + 2^{-k}, B] ∩ [a·n/t, (a+w)·n/t]`,

the set of scales `x` whose mate `s = x·t/n` lies in the Haar window.  It is realized as the certified integral
over the fixed rational window `[1+2^{-k}, B]` against a Lipschitz window MASK `χ_t(x) = ramp((x̄ − λ(t))/η)·
ramp((μ(t) − x̄)/η)` with the certified endpoint fields `λ(t) = band_{[1+2^{-k},B]}(a·n/t)`,
`μ(t) = band_{[1+2^{-k},B]}((a+w)·n/t)` (`η = w/(8(a+w))`): the mask is supported in the fiber, equals `1` on the
fiber shrunk by `η`, and is certified in both variables.

Proved here: `maskF` in `[0,1]`; MATE-IN-WINDOW (`x̄ ≥ λ(t) ⟹ x̄·t/n ≥ a`); and the EXPLICIT UNIFORM POSITIVE
HAAR MASS `∫_{[1+2^{-k},B]} χ_t(x)/max(x,1) dx ≥ 2η/B` for every active row with `w > 0` (`massF_ge`): the
fiber always contains `[n, n+4η]` (for `t ≤ a + 5w/8`) or `[n−4η, n]` (for `t ≥ a + 3w/8`), decided by the
Bishop comparison `Rle_or_Rle`.  The cases `w = 0` (the fiber is the single point `{n}`) and `n = 1` (`Λ(1) = 0`)
are excluded by the hypotheses `0 < w.num`, `m < X` and carried separately by the callers.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasColligation5
import F1Square.Square.IntervalSplitAtCap

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis
open CField

-- ===========================================================================
-- (0) Rational and real order toolkit.
-- ===========================================================================

theorem two_num_nonneg_of (n : Nat) : 0 ≤ ((⟨2, n + 1⟩ : Q)).num := by show (0 : Int) ≤ 2; decide

theorem Qle_zero_of_num_of {L : Q} (h : 0 ≤ L.num) : Qle (⟨0, 1⟩ : Q) L := by unfold Qle; push_cast; omega

/-- `Qle` from the real order of the embedded rationals (Archimedean collapse of the `2/(n+1)` slack). -/
theorem Qle_of_Rle_ofQ_of {p q : Q} (hp : 0 < p.den) (hq : 0 < q.den) (h : Rle (ofQ p hp) (ofQ q hq)) : Qle p q :=
  Qarch_gen (C := 2) hp hq (fun m => h m)

theorem Qle_Qmax_left_of (a b : Q) : Qle a (Qmax a b) := by
  unfold Qmax; split
  · assumption
  · exact Qle_refl a

theorem not_Qle_of_Qlt {a b : Q} (h : Qlt b a) : ¬ Qle a b := by unfold Qle Qlt at *; omega

-- ===========================================================================
-- (1) The unit ramp `ramp u = min(1, max(u, 0))` and its field.
-- ===========================================================================

/-- The unit ramp `ramp u = min(1, max(u, 0))`. -/
def ramp (u : Real) : Real := qBandQ (⟨0, 1⟩ : Q) (⟨1, 1⟩ : Q) (by decide) (by decide) u

theorem ramp_nonneg (u : Real) : Rle zero (ramp u) := fun n =>
  Qle_trans ((ramp u).den_pos n) (qBandQ_ge (⟨0, 1⟩ : Q) (⟨1, 1⟩ : Q) (by decide) (by decide) (by decide) u n) (Qle_self_add (two_num_nonneg_of n))
theorem ramp_le_one (u : Real) : Rle (ramp u) one := fun n =>
  Qle_trans (by decide) (qBandQ_le _ _ _ _ u n) (Qle_self_add (two_num_nonneg_of n))
/-- `u ≤ q` (`q ≥ 0`) ⟹ `ramp u ≤ q`. -/
theorem ramp_le_of_le {u : Real} {q : Q} (hqd : 0 < q.den) (hqn : 0 ≤ q.num) (h : Rle u (ofQ q hqd)) :
    Rle (ramp u) (ofQ q hqd) := fun n =>
  Qle_trans (Qmax_den_pos (u.den_pos n) (by decide)) (Qmin_le_left _ _)
    (Qmax_le (h n) (Qle_zero_of_num_of (Qadd_num_nonneg_loc hqn (two_num_nonneg_of n))))
theorem ramp_eq_zero_of_le {u : Real} (h : Rle u zero) : Req (ramp u) zero :=
  Rle_antisymm (ramp_le_of_le (q := (⟨0, 1⟩ : Q)) (by decide) (by decide) h) (ramp_nonneg u)
theorem ramp_eq_one_of_ge {u : Real} (h : Rle one u) : Req (ramp u) one := by
  refine Rle_antisymm (ramp_le_one u) ?_
  intro n
  have hu : Qle (⟨1, 1⟩ : Q) (add (u.seq n) ⟨2, n + 1⟩) := h n
  show Qle (⟨1, 1⟩ : Q) (add (Qmin (Qmax (u.seq n) ⟨0, 1⟩) ⟨1, 1⟩) ⟨2, n + 1⟩)
  rcases Qle_or_Qlt (Qmax (u.seq n) (⟨0, 1⟩ : Q)) (⟨1, 1⟩ : Q) with hle | hlt
  · rw [Qmin_eq_left hle]
    exact Qle_trans (add_den_pos (u.den_pos n) (Nat.succ_pos n)) hu (Qadd_le_add (Qle_Qmax_left_of _ _) (Qle_refl _))
  · rw [Qmin_eq_right (not_Qle_of_Qlt hlt)]
    exact Qle_self_add (two_num_nonneg_of n)
theorem ramp_lip : ∀ u v, Rle (Rabs (Rsub (ramp u) (ramp v))) (Rmul (ofQ (⟨1, 1⟩ : Q) Nat.one_pos) (Rabs (Rsub u v))) :=
  fun u v => Rle_trans (qBandQ_lipschitz _ _ _ _ u v) (Rle_of_Req (Req_symm (Rone_mul _)))
theorem ramp_congr {u v : Real} (h : Req u v) : Req (ramp u) (ramp v) := qBandQ_congr _ _ _ _ h
theorem ramp_abs_le_one (u : Real) : Rle (Rabs (ramp u)) (ofQ (⟨1, 1⟩ : Q) Nat.one_pos) :=
  Rabs_le_of_nonneg_le Nat.one_pos (by decide) (Rnonneg_of_Rle_zero (ramp_nonneg u)) (ramp_le_one u)

namespace CField

/-- The ramp of a field. -/
def rampF (u : CField) : CField where
  F := fun x t => ramp (u.F x t)
  Lx := u.Lx
  Lt := u.Lt
  M := (⟨1, 1⟩ : Q)
  hLxd := u.hLxd
  hLxn := u.hLxn
  hLtd := u.hLtd
  hLtn := u.hLtn
  hMd := Nat.one_pos
  hMn := by decide
  hlipx := fun t x x' => Rle_trans (ramp_lip _ _) (Rle_trans (Rle_of_Req (Rone_mul _)) (u.hlipx t x x'))
  hlipt := fun x t t' => Rle_trans (ramp_lip _ _) (Rle_trans (Rle_of_Req (Rone_mul _)) (u.hlipt x t t'))
  hbd := fun x t => ramp_abs_le_one _
  hfcx := @fun _ _ t h => ramp_congr (u.hfcx t h)
  hfct := @fun x _ _ h => ramp_congr (u.hfct x h)

/-- The clamped reciprocal `1/max(u, a)` of a field (`a > 0`): globally certified (Lipschitz `1/a²`, bound `1/a`). -/
def clampInv (a : Q) (han : 0 < a.num) (had : 0 < a.den) (u : CField) : CField where
  F := fun x t => clampedInv a han had (u.F x t)
  Lx := mul (mul (Qinv a) (Qinv a)) u.Lx
  Lt := mul (mul (Qinv a) (Qinv a)) u.Lt
  M := Qinv a
  hLxd := Qmul_den_pos (Qmul_den_pos (Qinv_den_pos han) (Qinv_den_pos han)) u.hLxd
  hLxn := Qmul_num_nonneg (Qmul_num_nonneg (Int.le_of_lt (Qinv_num_pos had)) (Int.le_of_lt (Qinv_num_pos had))) u.hLxn
  hLtd := Qmul_den_pos (Qmul_den_pos (Qinv_den_pos han) (Qinv_den_pos han)) u.hLtd
  hLtn := Qmul_num_nonneg (Qmul_num_nonneg (Int.le_of_lt (Qinv_num_pos had)) (Int.le_of_lt (Qinv_num_pos had))) u.hLtn
  hMd := Qinv_den_pos han
  hMn := Int.le_of_lt (Qinv_num_pos had)
  hlipx := fun t x x' => Rle_trans (clampedInv_lipschitz a han had _ _)
    (Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ _ (Qmul_num_nonneg (Int.le_of_lt (Qinv_num_pos had)) (Int.le_of_lt (Qinv_num_pos had)))) (u.hlipx t x x'))
      (Rle_of_Req (Req_trans (Req_symm (Rmul_assoc _ _ _)) (Rmul_congr (Rmul_ofQ_ofQ _ u.hLxd) (Req_refl _)))))
  hlipt := fun x t t' => Rle_trans (clampedInv_lipschitz a han had _ _)
    (Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ _ (Qmul_num_nonneg (Int.le_of_lt (Qinv_num_pos had)) (Int.le_of_lt (Qinv_num_pos had)))) (u.hlipt x t t'))
      (Rle_of_Req (Req_trans (Req_symm (Rmul_assoc _ _ _)) (Rmul_congr (Rmul_ofQ_ofQ _ u.hLtd) (Req_refl _)))))
  hbd := fun x t => (recipTest a han had).hbd (u.F x t)
  hfcx := @fun _ _ t h => clampedInv_congr a han had (u.hfcx t h)
  hfct := @fun x _ _ h => clampedInv_congr a han had (u.hfct x h)

theorem rampF_F (u : CField) (x t : Real) : (rampF u).F x t = ramp (u.F x t) := rfl

end CField

-- ===========================================================================
-- (2) Real-level facts about the band clamp `qBandQ lo hi`, and the band field.
-- ===========================================================================

theorem band_ge_R (lo hi : Q) (hlo : 0 < lo.den) (hhi : 0 < hi.den) (hlohi : Qle lo hi) (v : Real) :
    Rle (ofQ lo hlo) (qBandQ lo hi hlo hhi v) := fun n =>
  Qle_trans ((qBandQ lo hi hlo hhi v).den_pos n) (qBandQ_ge lo hi hlo hhi hlohi v n) (Qle_self_add (two_num_nonneg_of n))
theorem band_le_R (lo hi : Q) (hlo : 0 < lo.den) (hhi : 0 < hi.den) (v : Real) :
    Rle (qBandQ lo hi hlo hhi v) (ofQ hi hhi) := fun n =>
  Qle_trans hhi (qBandQ_le lo hi hlo hhi v n) (Qle_self_add (two_num_nonneg_of n))
/-- `v ≤ q`, `lo ≤ q` ⟹ `band(v) ≤ q`. -/
theorem band_le_of_le (lo hi : Q) (hlo : 0 < lo.den) (hhi : 0 < hi.den) {v : Real} {q : Q} (hqd : 0 < q.den)
    (hv : Rle v (ofQ q hqd)) (hloq : Qle lo q) : Rle (qBandQ lo hi hlo hhi v) (ofQ q hqd) := fun n =>
  Qle_trans (Qmax_den_pos (v.den_pos n) hlo) (Qmin_le_left _ _)
    (Qmax_le (hv n) (Qle_trans hqd hloq (Qle_self_add (two_num_nonneg_of n))))
/-- `q ≤ v`, `q ≤ hi` ⟹ `q ≤ band(v)`. -/
theorem band_ge_of_ge (lo hi : Q) (hlo : 0 < lo.den) (hhi : 0 < hi.den) {v : Real} {q : Q} (hqd : 0 < q.den)
    (hv : Rle (ofQ q hqd) v) (hqhi : Qle q hi) : Rle (ofQ q hqd) (qBandQ lo hi hlo hhi v) := by
  intro n
  have h1 : Qle q (add (v.seq n) ⟨2, n + 1⟩) := hv n
  show Qle q (add (Qmin (Qmax (v.seq n) lo) hi) ⟨2, n + 1⟩)
  rcases Qle_or_Qlt (Qmax (v.seq n) lo) hi with hle | hlt
  · rw [Qmin_eq_left hle]
    exact Qle_trans (add_den_pos (v.den_pos n) (Nat.succ_pos n)) h1 (Qadd_le_add (Qle_Qmax_left_of _ _) (Qle_refl _))
  · rw [Qmin_eq_right (not_Qle_of_Qlt hlt)]
    exact Qle_trans hhi hqhi (Qle_self_add (two_num_nonneg_of n))

namespace CField

/-- The band clamp `band_{[lo,hi]}` of a field (`0 ≤ lo ≤ hi`). -/
def bandF (lo hi : Q) (hlo : 0 < lo.den) (hhi : 0 < hi.den) (hlohi : Qle lo hi) (hlo0 : 0 ≤ lo.num) (hhi0 : 0 ≤ hi.num)
    (u : CField) : CField where
  F := fun x t => qBandQ lo hi hlo hhi (u.F x t)
  Lx := u.Lx
  Lt := u.Lt
  M := hi
  hLxd := u.hLxd
  hLxn := u.hLxn
  hLtd := u.hLtd
  hLtn := u.hLtn
  hMd := hhi
  hMn := hhi0
  hlipx := fun t x x' => Rle_trans (qBandQ_lipschitz _ _ _ _ _ _) (u.hlipx t x x')
  hlipt := fun x t t' => Rle_trans (qBandQ_lipschitz _ _ _ _ _ _) (u.hlipt x t t')
  hbd := fun x t => Rabs_le_of_nonneg_le hhi hhi0
    (Rnonneg_of_Rle_zero (Rle_trans (Rle_ofQ_ofQ (by decide) hlo (Qle_zero_of_num_of hlo0)) (band_ge_R lo hi hlo hhi hlohi _)))
    (band_le_R lo hi hlo hhi _)
  hfcx := @fun _ _ t h => qBandQ_congr _ _ _ _ (u.hfcx t h)
  hfct := @fun x _ _ h => qBandQ_congr _ _ _ _ (u.hfct x h)

theorem bandF_F (lo hi : Q) (hlo : 0 < lo.den) (hhi : 0 < hi.den) (hlohi : Qle lo hi) (hlo0 : 0 ≤ lo.num) (hhi0 : 0 ≤ hi.num)
    (u : CField) (x t : Real) : (bandF lo hi hlo hhi hlohi hlo0 hhi0 u).F x t = qBandQ lo hi hlo hhi (u.F x t) := rfl

end CField

-- ===========================================================================
-- (3) The rational window constants: `u = w/(a+w)`, `η = u/8`, the thresholds `a + 3w/8 < a + 5w/8`.
-- ===========================================================================

theorem awQ_num_pos (C : NormCtx) : 0 < (add C.a C.w).num := by
  show (0 : Int) < C.a.num * (C.w.den : Int) + C.w.num * (C.a.den : Int)
  have h1 : 0 < C.a.num * (C.w.den : Int) := Int.mul_pos C.han (Int.ofNat_pos.mpr C.hw)
  have h2 : 0 ≤ C.w.num * (C.a.den : Int) := Int.mul_nonneg C.hwn (Int.ofNat_nonneg _)
  omega

/-- `u = w/(a+w) ∈ [0,1]`. -/
def uQ (C : NormCtx) : Q := mul C.w (Qinv (add C.a C.w))
theorem uQ_den (C : NormCtx) : 0 < (uQ C).den := Qmul_den_pos C.hw (Qinv_den_pos (awQ_num_pos C))
theorem uQ_num (C : NormCtx) : 0 ≤ (uQ C).num := Qmul_num_nonneg C.hwn (Int.le_of_lt (Qinv_num_pos (add_den_pos C.had C.hw)))
theorem uQ_num_pos (C : NormCtx) (hw0 : 0 < C.w.num) : 0 < (uQ C).num := Int.mul_pos hw0 (Qinv_num_pos (add_den_pos C.had C.hw))

/-- `η = u/8`. -/
def etaQ (C : NormCtx) : Q := mul (uQ C) (⟨1, 8⟩ : Q)
theorem etaQ_den (C : NormCtx) : 0 < (etaQ C).den := Qmul_den_pos (uQ_den C) (by decide)
theorem etaQ_num (C : NormCtx) : 0 ≤ (etaQ C).num := Qmul_num_nonneg (uQ_num C) (by decide)
theorem etaQ_num_pos (C : NormCtx) (hw0 : 0 < C.w.num) : 0 < (etaQ C).num := Int.mul_pos (uQ_num_pos C hw0) (by decide)

/-- The thresholds `t_L = a + 3w/8 < t_R = a + 5w/8` (`w > 0`). -/
def tLQ (C : NormCtx) : Q := add C.a (mul C.w (⟨3, 8⟩ : Q))
def tRQ (C : NormCtx) : Q := add C.a (mul C.w (⟨5, 8⟩ : Q))
theorem tLQ_den (C : NormCtx) : 0 < (tLQ C).den := add_den_pos C.had (Qmul_den_pos C.hw (by decide))
theorem tRQ_den (C : NormCtx) : 0 < (tRQ C).den := add_den_pos C.had (Qmul_den_pos C.hw (by decide))

theorem tLQ_lt_tRQ (C : NormCtx) (hw0 : 0 < C.w.num) : Qlt (tLQ C) (tRQ C) := by
  show (C.a.num * ((C.w.den * 8 : Nat) : Int) + C.w.num * 3 * (C.a.den : Int)) * ((C.a.den * (C.w.den * 8) : Nat) : Int)
    < (C.a.num * ((C.w.den * 8 : Nat) : Int) + C.w.num * 5 * (C.a.den : Int)) * ((C.a.den * (C.w.den * 8) : Nat) : Int)
  have hD : (0 : Int) < ((C.a.den * (C.w.den * 8) : Nat) : Int) := by
    have := Nat.mul_pos C.had (Nat.mul_pos C.hw (by decide : 0 < 8)); exact_mod_cast this
  have hY : (0 : Int) < C.w.num * (C.a.den : Int) := Int.mul_pos hw0 (Int.ofNat_pos.mpr C.had)
  refine Int.mul_lt_mul_of_pos_right ?_ hD
  have e1 : C.w.num * 3 * (C.a.den : Int) = 3 * (C.w.num * (C.a.den : Int)) := by ring_uor
  have e2 : C.w.num * 5 * (C.a.den : Int) = 5 * (C.w.num * (C.a.den : Int)) := by ring_uor
  rw [e1, e2]; omega

theorem a_le_tLQ (C : NormCtx) : Qle C.a (tLQ C) := Qle_self_add (Qmul_num_nonneg C.hwn (by decide))
theorem a_le_tRQ (C : NormCtx) : Qle C.a (tRQ C) := Qle_self_add (Qmul_num_nonneg C.hwn (by decide))

-- ===========================================================================
-- (4) Rational facts about the window constants.
-- ===========================================================================

theorem Qmul_Qinv_self_of (q : Q) (hqn : 0 < q.num) : Qeq (mul q (Qinv q)) (⟨1, 1⟩ : Q) := by
  simp only [Qeq, mul, Qinv]
  push_cast [Int.toNat_of_nonneg (Int.le_of_lt hqn)]
  ring_uor
theorem Qinv_mul_self_of (q : Q) (hqn : 0 < q.num) : Qeq (mul (Qinv q) q) (⟨1, 1⟩ : Q) := by
  simp only [Qeq, mul, Qinv]
  push_cast [Int.toNat_of_nonneg (Int.le_of_lt hqn)]
  ring_uor
theorem ofQ_mul_inv_self_of (q : Q) (hqd : 0 < q.den) (hqn : 0 < q.num) :
    Req (Rmul (ofQ q hqd) (ofQ (Qinv q) (Qinv_den_pos hqn))) one :=
  Req_trans (Rmul_ofQ_ofQ hqd (Qinv_den_pos hqn)) (ofQ_congr _ _ (Qmul_Qinv_self_of q hqn))
theorem ofQ_inv_mul_self_of (q : Q) (hqd : 0 < q.den) (hqn : 0 < q.num) :
    Req (Rmul (ofQ (Qinv q) (Qinv_den_pos hqn)) (ofQ q hqd)) one :=
  Req_trans (Rmul_ofQ_ofQ (Qinv_den_pos hqn) hqd) (ofQ_congr _ _ (Qinv_mul_self_of q hqn))

theorem Qadd_num_pos_of {p q : Q} (hp : 0 < p.num) (hpd : 0 < p.den) (hq : 0 ≤ q.num) (hqd : 0 < q.den) : 0 < (add p q).num := by
  show 0 < p.num * (q.den : Int) + q.num * (p.den : Int)
  have h1 : 0 < p.num * (q.den : Int) := Int.mul_pos hp (Int.ofNat_pos.mpr hqd)
  have h2 : 0 ≤ q.num * (p.den : Int) := Int.mul_nonneg hq (Int.ofNat_nonneg _)
  omega

/-- `u = w/(a+w) ≤ 1`. -/
theorem uQ_le_one (C : NormCtx) : Qle (uQ C) (⟨1, 1⟩ : Q) := by
  refine Qle_of_Rle_ofQ_of (uQ_den C) (by decide) ?_
  refine Rle_trans (Rle_of_Req (Req_symm (Rmul_ofQ_ofQ C.hw (Qinv_den_pos (awQ_num_pos C))))) ?_
  refine Rle_trans (Rmul_le_Rmul_right (Rnonneg_ofQ _ (Int.le_of_lt (Qinv_num_pos (add_den_pos C.had C.hw))))
    (Rle_ofQ_ofQ C.hw (add_den_pos C.had C.hw) (Qle_add_self (Int.le_of_lt C.han)))) ?_
  exact Rle_of_Req (ofQ_mul_inv_self_of _ (add_den_pos C.had C.hw) (awQ_num_pos C))

/-- `η ≤ 1/8`. -/
theorem etaQ_le_eighth (C : NormCtx) : Qle (etaQ C) (⟨1, 8⟩ : Q) :=
  Qle_trans (Qmul_den_pos Nat.one_pos (by decide)) (Qmul_le_mul_right (by decide) (uQ_le_one C)) (by decide)
/-- `3η ≤ 1`. -/
theorem three_eta_le_one (C : NormCtx) : Qle (mul (⟨3, 1⟩ : Q) (etaQ C)) (⟨1, 1⟩ : Q) :=
  Qle_trans (Qmul_den_pos Nat.one_pos (by decide)) (Qmul_le_mul_left (by decide) (etaQ_le_eighth C)) (by decide)
/-- `4η ≤ 1`. -/
theorem four_eta_le_one (C : NormCtx) : Qle (mul (⟨4, 1⟩ : Q) (etaQ C)) (⟨1, 1⟩ : Q) :=
  Qle_trans (Qmul_den_pos Nat.one_pos (by decide)) (Qmul_le_mul_left (by decide) (etaQ_le_eighth C)) (by decide)

theorem tailLo_num (k : Nat) : 0 ≤ (tailLo k).num := by
  show (0 : Int) ≤ 1 * ((2 ^ k : Nat) : Int) + 1 * ((1 : Nat) : Int)
  push_cast
  have : (0 : Int) ≤ (2 : Int) ^ k := by exact_mod_cast Nat.zero_le (2 ^ k)
  omega

/-- `1 + 2^{-k} ≤ B`. -/
theorem tailLo_le_B (C : NormCtx) (k : Nat) : Qle (tailLo k) (canonB C) := by
  have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hX : 1 ≤ C.X := C.hX
  show (1 * ((2 ^ k : Nat) : Int) + 1 * ((1 : Nat) : Int)) * ((1 : Nat) : Int) ≤ ((C.X + 1 : Nat) : Int) * ((1 * 2 ^ k : Nat) : Int)
  have hp' : (1 : Int) ≤ (2 : Int) ^ k := by exact_mod_cast hp
  have hX' : (1 : Int) ≤ (C.X : Int) := by exact_mod_cast hX
  push_cast
  generalize hP : (2 : Int) ^ k = P at hp' ⊢
  have h1 : 1 * P ≤ (C.X : Int) * P := Int.mul_le_mul_of_nonneg_right hX' (by omega)
  have e : ((C.X : Int) + 1) * (1 * P) = (C.X : Int) * P + P := by ring_uor
  rw [e]; omega

/-- `2 ≤ n` for `1 ≤ m`, as `Qle (tailLo k) (upQ m)` and `Qle 1 (upQ m)`. -/
theorem tailLo_le_upQ (k m : Nat) (hm1 : 1 ≤ m) : Qle (tailLo k) (upQ m) := by
  have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  show (1 * ((2 ^ k : Nat) : Int) + 1 * ((1 : Nat) : Int)) * ((1 : Nat) : Int) ≤ ((m + 1 : Nat) : Int) * ((1 * 2 ^ k : Nat) : Int)
  have hp' : (1 : Int) ≤ (2 : Int) ^ k := by exact_mod_cast hp
  have hm' : (1 : Int) ≤ (m : Int) := by exact_mod_cast hm1
  push_cast
  generalize hP : (2 : Int) ^ k = P at hp' ⊢
  have h1 : 1 * P ≤ (m : Int) * P := Int.mul_le_mul_of_nonneg_right hm' (by omega)
  have e : ((m : Int) + 1) * (1 * P) = (m : Int) * P + P := by ring_uor
  rw [e]; omega
theorem one_le_upQ (m : Nat) : Qle (⟨1, 1⟩ : Q) (upQ m) := by
  show (1 : Int) * ((1 : Nat) : Int) ≤ ((m + 1 : Nat) : Int) * ((1 : Nat) : Int); push_cast; omega
theorem upQ_add_one_le_B (C : NormCtx) (m : Nat) (hm : m < C.X) : Qle (add (upQ m) (⟨1, 1⟩ : Q)) (canonB C) := by
  show (((m + 1 : Nat) : Int) * ((1 : Nat) : Int) + 1 * ((1 : Nat) : Int)) * ((1 : Nat) : Int) ≤ ((C.X + 1 : Nat) : Int) * (((1 * 1 : Nat)) : Int)
  push_cast; omega
/-- `(n − (1 + 2^{-k})).num > 0` for `k ≥ 1`, `m ≥ 1`. -/
theorem upQ_sub_tailLo_num_pos (k m : Nat) (hk : 1 ≤ k) (hm1 : 1 ≤ m) : 0 < (Qsub (upQ m) (tailLo k)).num := by
  have hp : 2 ≤ 2 ^ k := two_le_two_pow k hk
  show (0 : Int) < ((m + 1 : Nat) : Int) * ((1 * 2 ^ k : Nat) : Int) + (-(1 * ((2 ^ k : Nat) : Int) + 1 * ((1 : Nat) : Int))) * ((1 : Nat) : Int)
  have hp' : (2 : Int) ≤ (2 : Int) ^ k := by exact_mod_cast hp
  have hm' : (1 : Int) ≤ (m : Int) := by exact_mod_cast hm1
  push_cast
  generalize hP : (2 : Int) ^ k = P at hp' ⊢
  have h1 : 1 * P ≤ (m : Int) * P := Int.mul_le_mul_of_nonneg_right hm' (by omega)
  have e : ((m : Int) + 1) * (1 * P) + -(1 * P + 1) * 1 = (m : Int) * P - 1 := by ring_uor
  rw [e]; omega
/-- `(n − 3/8 − (1 + 2^{-k})).num > 0` for `k ≥ 1`, `m ≥ 1`. -/
theorem upQ_sub_tailLo_38_num_pos (k m : Nat) (hk : 1 ≤ k) (hm1 : 1 ≤ m) :
    0 < (Qsub (Qsub (upQ m) (⟨3, 8⟩ : Q)) (tailLo k)).num := by
  have hp : 2 ≤ 2 ^ k := two_le_two_pow k hk
  show (0 : Int) < (((m + 1 : Nat) : Int) * ((8 : Nat) : Int) + (-(3 : Int)) * ((1 : Nat) : Int)) * ((1 * 2 ^ k : Nat) : Int)
      + (-(1 * ((2 ^ k : Nat) : Int) + 1 * ((1 : Nat) : Int))) * ((1 * 8 : Nat) : Int)
  have hp' : (2 : Int) ≤ (2 : Int) ^ k := by exact_mod_cast hp
  have hm' : (1 : Int) ≤ (m : Int) := by exact_mod_cast hm1
  push_cast
  generalize hP : (2 : Int) ^ k = P at hp' ⊢
  have h1 : 1 * P ≤ (m : Int) * P := Int.mul_le_mul_of_nonneg_right hm' (by omega)
  have e : (((m : Int) + 1) * 8 + -3) * (1 * P) + -(1 * P + 1) * 8 = 8 * ((m : Int) * P) - 3 * P - 8 := by ring_uor
  rw [e]; omega

-- ===========================================================================
-- (5) The fiber endpoints `λ(t) = band(a·n/t)`, `μ(t) = band((a+w)·n/t)`, the mask, and the mass field.
-- ===========================================================================

/-- `a·n` and `(a+w)·n` as rationals. -/
def anQ (C : NormCtx) (m : Nat) : Q := mul C.a (upQ m)
def awnQ (C : NormCtx) (m : Nat) : Q := mul (add C.a C.w) (upQ m)
theorem anQ_den (C : NormCtx) (m : Nat) : 0 < (anQ C m).den := Qmul_den_pos C.had Nat.one_pos
theorem anQ_num (C : NormCtx) (m : Nat) : 0 ≤ (anQ C m).num := Qmul_num_nonneg (Int.le_of_lt C.han) (Int.ofNat_nonneg _)
theorem awnQ_den (C : NormCtx) (m : Nat) : 0 < (awnQ C m).den := Qmul_den_pos (add_den_pos C.had C.hw) Nat.one_pos
theorem awnQ_num (C : NormCtx) (m : Nat) : 0 ≤ (awnQ C m).num := Qmul_num_nonneg (Int.le_of_lt (awQ_num_pos C)) (Int.ofNat_nonneg _)

/-- `λ(t) = band_{[1+2^{-k},B]}(a·n·r(t))` — the lower endpoint of the fiber, as a certified field. -/
def lamF (C : NormCtx) (k m : Nat) : CField :=
  bandF (tailLo k) (canonB C) (tailLo_den k) (canonB_den C) (tailLo_le_B C k) (tailLo_num k) (Int.le_of_lt (canonB_num C))
    (smulQF (anQ C m) (anQ_den C m) (anQ_num C m) (rF C))
/-- `μ(t) = band_{[1+2^{-k},B]}((a+w)·n·r(t))` — the upper endpoint of the fiber. -/
def muF (C : NormCtx) (k m : Nat) : CField :=
  bandF (tailLo k) (canonB C) (tailLo_den k) (canonB_den C) (tailLo_le_B C k) (tailLo_num k) (Int.le_of_lt (canonB_num C))
    (smulQF (awnQ C m) (awnQ_den C m) (awnQ_num C m) (rF C))
theorem lamF_F (C : NormCtx) (k m : Nat) (x t : Real) :
    (lamF C k m).F x t = qBandQ (tailLo k) (canonB C) (tailLo_den k) (canonB_den C) (Rmul (ofQ (anQ C m) (anQ_den C m)) (rEv C t)) := rfl
theorem muF_F (C : NormCtx) (k m : Nat) (x t : Real) :
    (muF C k m).F x t = qBandQ (tailLo k) (canonB C) (tailLo_den k) (canonB_den C) (Rmul (ofQ (awnQ C m) (awnQ_den C m)) (rEv C t)) := rfl

/-- `1/η`. -/
def invEtaQ (C : NormCtx) : Q := Qinv (etaQ C)
theorem invEtaQ_den (C : NormCtx) (hw0 : 0 < C.w.num) : 0 < (invEtaQ C).den := Qinv_den_pos (etaQ_num_pos C hw0)
theorem invEtaQ_num (C : NormCtx) : 0 ≤ (invEtaQ C).num := Int.le_of_lt (Qinv_num_pos (etaQ_den C))

/-- The two ramp arguments `(x̄ − λ)/η` and `(μ − x̄)/η`. -/
def arg1F (C : NormCtx) (k m : Nat) (hw0 : 0 < C.w.num) : CField :=
  smulQF (invEtaQ C) (invEtaQ_den C hw0) (invEtaQ_num C) (subF (xclF C) (lamF C k m))
def arg2F (C : NormCtx) (k m : Nat) (hw0 : 0 < C.w.num) : CField :=
  smulQF (invEtaQ C) (invEtaQ_den C hw0) (invEtaQ_num C) (subF (muF C k m) (xclF C))

/-- **★ THE FIBER MASK** `χ_t(x) = ramp((x̄ − λ(t))/η)·ramp((μ(t) − x̄)/η)`. -/
def maskF (C : NormCtx) (k m : Nat) (hw0 : 0 < C.w.num) : CField := mulF (rampF (arg1F C k m hw0)) (rampF (arg2F C k m hw0))
theorem maskF_F (C : NormCtx) (k m : Nat) (hw0 : 0 < C.w.num) (x t : Real) :
    (maskF C k m hw0).F x t
      = Rmul (ramp (Rmul (ofQ (invEtaQ C) (invEtaQ_den C hw0)) (Rsub (xcl C x) ((lamF C k m).F x t))))
             (ramp (Rmul (ofQ (invEtaQ C) (invEtaQ_den C hw0)) (Rsub ((muF C k m).F x t) (xcl C x)))) := rfl

theorem maskF_nonneg (C : NormCtx) (k m : Nat) (hw0 : 0 < C.w.num) (x t : Real) : Rnonneg ((maskF C k m hw0).F x t) :=
  Rnonneg_Rmul (Rnonneg_of_Rle_zero (ramp_nonneg _)) (Rnonneg_of_Rle_zero (ramp_nonneg _))
theorem maskF_le_one (C : NormCtx) (k m : Nat) (hw0 : 0 < C.w.num) (x t : Real) : Rle ((maskF C k m hw0).F x t) one := by
  rw [maskF_F]
  exact Rle_trans (Rmul_le_Rmul_left (Rnonneg_of_Rle_zero (ramp_nonneg _)) (ramp_le_one _)) (Rle_trans (Rle_of_Req (Rmul_one _)) (ramp_le_one _))
/-- The mask is at most its first ramp factor. -/
theorem maskF_le_ramp1 (C : NormCtx) (k m : Nat) (hw0 : 0 < C.w.num) (x t : Real) :
    Rle ((maskF C k m hw0).F x t) (ramp (Rmul (ofQ (invEtaQ C) (invEtaQ_den C hw0)) (Rsub (xcl C x) ((lamF C k m).F x t)))) := by
  rw [maskF_F]
  exact Rle_trans (Rmul_le_Rmul_left (Rnonneg_of_Rle_zero (ramp_nonneg _)) (ramp_le_one _)) (Rle_of_Req (Rmul_one _))

/-- The Haar-weighted mask `χ_t(x)·(1/max(x̄,1))`. -/
def maskrF (C : NormCtx) (k m : Nat) (hw0 : 0 < C.w.num) : CField := mulF (maskF C k m hw0) (rOneClF C)
theorem maskrF_F (C : NormCtx) (k m : Nat) (hw0 : 0 < C.w.num) (x t : Real) :
    (maskrF C k m hw0).F x t = Rmul ((maskF C k m hw0).F x t) (rOne (xcl C x)) := rfl

/-- **The Haar mass field** `t ↦ ∫_{[1+2^{-k},B]} χ_t(x)·(1/max(x̄,1)) dx`. -/
def massF (C : NormCtx) (k m : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) : CField :=
  xIntF (maskrF C k m hw0) (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk)
theorem massF_F (C : NormCtx) (k m : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (x t : Real) :
    (massF C k m hw0 hk).F x t
      = xInt (maskrF C k m hw0) (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk) t := rfl

-- ===========================================================================
-- (6) Generic window lemmas: window congruence, the middle piece, the plateau bound.
-- ===========================================================================

section WindowLemmas
variable {f : Real → Real} {L : Q}

theorem intI_window_congr (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfc : ∀ x y, Req x y → Req (f x) (f y))
    (lo w w' : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) (hw' : 0 < w'.den) (hw'n : 0 ≤ w'.num) (h : Qeq w w') :
    Req (riemannIntegralI hLd hLn hlip hfc lo w hlo hw hwn) (riemannIntegralI hLd hLn hlip hfc lo w' hlo hw' hw'n) := by
  unfold riemannIntegralI
  refine Rmul_congr (ofQ_congr hw hw' h) ?_
  exact intU_congr_free _ _ _ _ _ _ _ _ (fun y => hfc _ _ (Radd_congr (Req_refl _) (Rmul_congr (ofQ_congr hw hw' h) (Req_refl y))))

/-- **The middle piece of a nonnegative integrand is at most the whole**: `∫_{[lo+w1, v]} f ≤ ∫_{[lo, w1+(v+w3)]} f`. -/
theorem intI_ge_middle (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfc : ∀ x y, Req x y → Req (f x) (f y)) (hnn : ∀ x, Rnonneg (f x))
    (lo w1 v w3 : Q) (hlo : 0 < lo.den) (hw1 : 0 < w1.den) (hv : 0 < v.den) (hw3 : 0 < w3.den)
    (hw1n : 0 < w1.num) (hvn : 0 < v.num) (hw3n : 0 ≤ w3.num) :
    Rle (riemannIntegralI hLd hLn hlip hfc (add lo w1) v (add_den_pos hlo hw1) hv (Int.le_of_lt hvn))
        (riemannIntegralI hLd hLn hlip hfc lo (add w1 (add v w3)) hlo (add_den_pos hw1 (add_den_pos hv hw3))
          (Qadd_num_nonneg_loc (Int.le_of_lt hw1n) (Qadd_num_nonneg_loc (Int.le_of_lt hvn) hw3n))) := by
  have hW : 0 ≤ (add w1 (add v w3)).num := Qadd_num_nonneg_loc (Int.le_of_lt hw1n) (Qadd_num_nonneg_loc (Int.le_of_lt hvn) hw3n)
  have hle1 : Qle w1 (add w1 (add v w3)) := Qle_self_add (Qadd_num_nonneg_loc (Int.le_of_lt hvn) hw3n)
  have hs1 := riemannIntegralI_split_at hLd hLn hlip hfc lo (add w1 (add v w3)) w1 hlo (add_den_pos hw1 (add_den_pos hv hw3)) hW
    hw1 hw1n hle1 (Qsub_num_nonneg hle1)
  have hq : Qeq (Qsub (add w1 (add v w3)) w1) (add v w3) := Qsub_add_cancel w1 (add v w3)
  have hs1' := intI_window_congr hLd hLn hlip hfc (add lo w1) (Qsub (add w1 (add v w3)) w1) (add v w3) (add_den_pos hlo hw1)
    (Qsub_den_pos (add_den_pos hw1 (add_den_pos hv hw3)) hw1) (Qsub_num_nonneg hle1) (add_den_pos hv hw3)
    (Qadd_num_nonneg_loc (Int.le_of_lt hvn) hw3n) hq
  have hle2 : Qle v (add v w3) := Qle_self_add hw3n
  have hs2 := riemannIntegralI_split_at hLd hLn hlip hfc (add lo w1) (add v w3) v (add_den_pos hlo hw1) (add_den_pos hv hw3)
    (Qadd_num_nonneg_loc (Int.le_of_lt hvn) hw3n) hv hvn hle2 (Qsub_num_nonneg hle2)
  refine Rle_trans ?_ (Rle_of_Req (Req_symm hs1))
  refine Rle_trans ?_ (Rle_self_Radd_left (riemannIntegralI_nonneg hLd hLn hlip hfc hnn lo w1 hlo hw1 (Int.le_of_lt hw1n)))
  refine Rle_trans ?_ (Rle_of_Req (Req_symm hs1'))
  refine Rle_trans ?_ (Rle_of_Req (Req_symm hs2))
  exact Rle_trans (Rle_of_Req (Req_symm (Radd_zero _)))
    (Radd_le_add (Rle_refl _) (Rle_zero_of_Rnonneg (riemannIntegralI_nonneg hLd hLn hlip hfc hnn _ _ _ _ _)))

end WindowLemmas

/-- **The plateau bound**: if `z(·,t) ≥ 0` everywhere and `z(x,t) ≥ c` on the sub-window `[lo+w1, lo+w1+v]`, then
    `∫_{[lo, w1+(v+w3)]} z(x,t) dx ≥ v·c`. -/
theorem xInt_ge_plateau (z : CField) (lo w1 v w3 : Q) (hlo : 0 < lo.den) (hw1 : 0 < w1.den) (hv : 0 < v.den) (hw3 : 0 < w3.den)
    (hw1n : 0 < w1.num) (hvn : 0 < v.num) (hw3n : 0 ≤ w3.num) (t : Real) {c : Q} (hcd : 0 < c.den) (hcn : 0 ≤ c.num)
    (hnn : ∀ x, Rnonneg (z.F x t))
    (hplat : ∀ s, Rle zero s → Rle s one → Rle (ofQ c hcd) (z.F (affineMap (add lo w1) v (add_den_pos hlo hw1) hv s) t)) :
    Rle (ofQ (mul v c) (Qmul_den_pos hv hcd))
        (xInt z lo (add w1 (add v w3)) hlo (add_den_pos hw1 (add_den_pos hv hw3))
          (Qadd_num_nonneg_loc (Int.le_of_lt hw1n) (Qadd_num_nonneg_loc (Int.le_of_lt hvn) hw3n)) t) := by
  unfold xInt
  refine Rle_trans ?_ (intI_ge_middle z.hLxd z.hLxn (z.hlipx t) (fun _ _ h => z.hfcx t h) hnn lo w1 v w3 hlo hw1 hv hw3 hw1n hvn hw3n)
  have hc' : ∀ x y, Rle (Rabs (Rsub (ofQ c hcd) (ofQ c hcd))) (Rmul (ofQ z.Lx z.hLxd) (Rabs (Rsub x y))) :=
    fun x y => Rle_trans (const_lip0 _ x y) (Rmul_le_Rmul_right (Rnonneg_Rabs _) (Rle_ofQ_ofQ _ _ (Qle_zero_of_num_of z.hLxn)))
  refine Rle_trans ?_ (riemannIntegralI_le_unit (f := fun _ => ofQ c hcd) z.hLxd z.hLxn hc' (fun _ _ _ => Req_refl _)
    (z.hlipx t) (fun _ _ h => z.hfcx t h) (add lo w1) v (add_den_pos hlo hw1) hv (Int.le_of_lt hvn) hplat)
  refine Rle_of_Req (Req_symm ?_)
  refine Req_trans (riemannIntegralI_certif_irrel _ _ hc' _ (by decide) (by decide) (const_lip0 _) (fun _ _ _ => Req_refl _)
    (add lo w1) v (add_den_pos hlo hw1) hv (Int.le_of_lt hvn)) ?_
  refine Req_trans (riemannIntegralI_const _ (add lo w1) v (add_den_pos hlo hw1) hv (Int.le_of_lt hvn)) ?_
  exact Rmul_ofQ_ofQ hv hcd

-- ===========================================================================
-- (7) Real inequalities of the fiber endpoints on the Haar window.
-- ===========================================================================

theorem rEv_le_inv_a (C : NormCtx) (t : Real) : Rle (rEv C t) (ofQ (Qinv C.a) (Qinv_den_pos C.han)) :=
  Rle_of_Rabs_le ((recipTest C.a C.han C.had).hbd t)
theorem rEv_nonneg (C : NormCtx) (t : Real) : Rnonneg (rEv C t) := Rnonneg_clampedInv C.a C.han C.had t
theorem rEv_ge_inv_of_le (C : NormCtx) {t : Real} {q : Q} (hqd : 0 < q.den) (hqn : 0 < q.num) (htq : Rle t (ofQ q hqd))
    (haq : Qle C.a q) : Rle (ofQ (Qinv q) (Qinv_den_pos hqn)) (rEv C t) :=
  ofQ_inv_le_clampedInv C.han C.had hqd hqn htq haq
theorem rEv_mul_t (C : NormCtx) {t : Real} (hta : Rle (ofQ C.a C.had) t) : Req (Rmul (rEv C t) t) one := by
  obtain ⟨kt, hkt⟩ := Pos_of_Rle_ofQ C.han C.had hta
  exact Req_trans (Rmul_congr (clampedInv_eq_of_ge (han := C.han) hkt hta) (Req_refl t)) (Req_trans (Rmul_comm _ _) (Rmul_Rinv_self hkt))

theorem awQ_den (C : NormCtx) : 0 < (add C.a C.w).den := add_den_pos C.had C.hw

/-- `(a·n)·(1/a) = n`. -/
theorem anQ_mul_inv_a (C : NormCtx) (m : Nat) : Qeq (mul (anQ C m) (Qinv C.a)) (upQ m) := by
  simp only [Qeq, mul, Qinv, anQ, upQ]
  push_cast [Int.toNat_of_nonneg (Int.le_of_lt C.han)]
  ring_uor
/-- `(a+w)·n = n·(a+w)`. -/
theorem awnQ_eq (C : NormCtx) (m : Nat) : Qeq (awnQ C m) (mul (upQ m) (add C.a C.w)) := Qmul_comm _ _
theorem anQ_eq (C : NormCtx) (m : Nat) : Qeq (anQ C m) (mul (upQ m) C.a) := Qmul_comm _ _
/-- `(a+w) − t_R = 3w/8` and `t_L − a = 3w/8`. -/
theorem aw_sub_tR (C : NormCtx) : Qeq (Qsub (add C.a C.w) (tRQ C)) (mul C.w (⟨3, 8⟩ : Q)) := by
  simp only [Qeq, Qsub, add, neg, mul, tRQ]; push_cast; ring_uor
theorem tL_sub_a (C : NormCtx) : Qeq (Qsub (tLQ C) C.a) (mul C.w (⟨3, 8⟩ : Q)) := by
  simp only [Qeq, Qsub, add, neg, mul, tLQ]; push_cast; ring_uor
/-- `(3w/8)·(1/(a+w)) = u·(3/8)`. -/
theorem w38_inv_aw (C : NormCtx) : Qeq (mul (mul C.w (⟨3, 8⟩ : Q)) (Qinv (add C.a C.w))) (mul (uQ C) (⟨3, 8⟩ : Q)) := by
  simp only [Qeq, mul, Qinv, uQ, add]; push_cast; ring_uor
/-- `2·(u·3/8) = u·(3/4)` and `4·η = u·(1/2)`. -/
theorem two_u38 (C : NormCtx) : Qeq (mul (⟨2, 1⟩ : Q) (mul (uQ C) (⟨3, 8⟩ : Q))) (mul (uQ C) (⟨3, 4⟩ : Q)) := by
  simp only [Qeq, mul]; push_cast; ring_uor
theorem four_eta (C : NormCtx) : Qeq (mul (⟨4, 1⟩ : Q) (etaQ C)) (mul (uQ C) (⟨1, 2⟩ : Q)) := by
  simp only [Qeq, mul, etaQ]; push_cast; ring_uor
/-- `4η ≤ 2·(u·3/8)`. -/
theorem four_eta_le (C : NormCtx) : Qle (mul (⟨4, 1⟩ : Q) (etaQ C)) (mul (⟨2, 1⟩ : Q) (mul (uQ C) (⟨3, 8⟩ : Q))) := by
  refine Qle_congr_left (Qmul_den_pos (uQ_den C) (by decide)) (Qeq_symm (four_eta C)) ?_
  refine Qle_congr_right (Qmul_den_pos (uQ_den C) (by decide)) (Qeq_symm (two_u38 C)) ?_
  exact Qmul_le_mul_left (uQ_num C) (by decide)

/-- `a·n·r(t) ≤ n`. -/
theorem an_r_le_n (C : NormCtx) (m : Nat) (t : Real) :
    Rle (Rmul (ofQ (anQ C m) (anQ_den C m)) (rEv C t)) (ofQ (upQ m) Nat.one_pos) := by
  refine Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ (anQ_den C m) (anQ_num C m)) (rEv_le_inv_a C t)) ?_
  exact Rle_of_Req (Req_trans (Rmul_ofQ_ofQ (anQ_den C m) (Qinv_den_pos C.han)) (ofQ_congr _ _ (anQ_mul_inv_a C m)))

/-- `λ(t) ≤ n` (`m ≥ 1`). -/
theorem lam_le_n (C : NormCtx) (k m : Nat) (hm1 : 1 ≤ m) (x t : Real) :
    Rle ((lamF C k m).F x t) (ofQ (upQ m) Nat.one_pos) := by
  rw [lamF_F]
  exact band_le_of_le _ _ _ _ Nat.one_pos (an_r_le_n C m t) (tailLo_le_upQ k m hm1)

/-- `(a+w)·r(t) ≥ 1` for `t ≤ a+w`. -/
theorem aw_r_ge_one (C : NormCtx) {t : Real} (htw : Rle t (ofQ (add C.a C.w) (awQ_den C))) :
    Rle one (Rmul (ofQ (add C.a C.w) (awQ_den C)) (rEv C t)) := by
  refine Rle_trans (Rle_of_Req (Req_symm (ofQ_mul_inv_self_of _ (awQ_den C) (awQ_num_pos C)))) ?_
  exact Rmul_le_Rmul_left (Rnonneg_ofQ (awQ_den C) (Int.le_of_lt (awQ_num_pos C)))
    (rEv_ge_inv_of_le C (awQ_den C) (awQ_num_pos C) htw (Qle_self_add C.hwn))

/-- `(a+w)·n·r(t) ≥ n` for `t ≤ a+w`. -/
theorem awn_r_ge_n (C : NormCtx) (m : Nat) {t : Real} (htw : Rle t (ofQ (add C.a C.w) (awQ_den C))) :
    Rle (ofQ (upQ m) Nat.one_pos) (Rmul (ofQ (awnQ C m) (awnQ_den C m)) (rEv C t)) := by
  have h1 : Req (Rmul (ofQ (awnQ C m) (awnQ_den C m)) (rEv C t))
      (Rmul (ofQ (upQ m) Nat.one_pos) (Rmul (ofQ (add C.a C.w) (awQ_den C)) (rEv C t))) :=
    Req_trans (Rmul_congr (Req_trans (ofQ_congr _ (Qmul_den_pos Nat.one_pos (awQ_den C)) (awnQ_eq C m))
      (Req_symm (Rmul_ofQ_ofQ Nat.one_pos (awQ_den C)))) (Req_refl _)) (Rmul_assoc _ _ _)
  refine Rle_trans ?_ (Rle_of_Req (Req_symm h1))
  refine Rle_trans (Rle_of_Req (Req_symm (Rmul_one _))) ?_
  exact Rmul_le_Rmul_left (Rnonneg_ofQ Nat.one_pos (Int.ofNat_nonneg _)) (aw_r_ge_one C htw)

/-- `μ(t) ≥ n` for `t ≤ a+w`, `m < X`. -/
theorem mu_ge_n (C : NormCtx) (k m : Nat) (hm : m < C.X) {t : Real} (htw : Rle t (ofQ (add C.a C.w) (awQ_den C))) (x : Real) :
    Rle (ofQ (upQ m) Nat.one_pos) ((muF C k m).F x t) := by
  rw [muF_F]
  exact band_ge_of_ge _ _ _ _ Nat.one_pos (awn_r_ge_n C m htw) (upQ_le_B C m hm)

/-- `x − (y + z) ≈ (x − y) − z`. -/
theorem sub_add_eq_sub_sub_of (x y z : Real) : Req (Rsub x (Radd y z)) (Rsub (Rsub x y) z) :=
  Req_trans (Radd_congr (Req_refl x) (Rneg_Radd y z)) (Req_symm (Radd_assoc _ _ _))

/-- **Case R**: `t ≤ t_R = a + 5w/8` ⟹ `(a+w)·n·r(t) ≥ n + 4η` (`m ≥ 1`). -/
theorem awn_r_ge_R (C : NormCtx) (m : Nat) (hm1 : 1 ≤ m) {t : Real} (hta : Rle (ofQ C.a C.had) t)
    (htR : Rle t (ofQ (tRQ C) (tRQ_den C))) (htw : Rle t (ofQ (add C.a C.w) (awQ_den C))) :
    Rle (ofQ (add (upQ m) (mul (⟨4, 1⟩ : Q) (etaQ C))) (add_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos (etaQ_den C))))
        (Rmul (ofQ (awnQ C m) (awnQ_den C m)) (rEv C t)) := by
  -- ρ := (a+w)·r(t);  ρ − 1 = ((a+w) − t)·r(t) ≥ (3w/8)·(1/(a+w)) = u·3/8
  have hρ1 : Req (Rsub (Rmul (ofQ (add C.a C.w) (awQ_den C)) (rEv C t)) one)
      (Rmul (Rsub (ofQ (add C.a C.w) (awQ_den C)) t) (rEv C t)) := by
    refine Req_trans (Rsub_congr (Req_refl _) (Req_symm (Req_trans (Rmul_comm _ _) (rEv_mul_t C hta)))) ?_
    exact Req_symm (Rmul_sub_distrib_right _ _ _)
  have hgap : Rle (ofQ (mul C.w (⟨3, 8⟩ : Q)) (Qmul_den_pos C.hw (by decide))) (Rsub (ofQ (add C.a C.w) (awQ_den C)) t) := by
    refine Rle_trans (Rle_of_Req (Req_symm (Req_trans (Rsub_ofQ_ofQ (awQ_den C) (tRQ_den C)) (ofQ_congr _ _ (aw_sub_tR C))))) ?_
    exact Radd_le_add (Rle_refl _) (Rle_Rneg htR)
  have hprod : Rle (ofQ (mul (uQ C) (⟨3, 8⟩ : Q)) (Qmul_den_pos (uQ_den C) (by decide)))
      (Rmul (Rsub (ofQ (add C.a C.w) (awQ_den C)) t) (rEv C t)) := by
    refine Rle_trans (Rle_of_Req (Req_symm (Req_trans (Rmul_ofQ_ofQ (Qmul_den_pos C.hw (by decide)) (Qinv_den_pos (awQ_num_pos C)))
      (ofQ_congr _ _ (w38_inv_aw C))))) ?_
    exact Rmul_le_Rmul_both (Rnonneg_ofQ _ (Qmul_num_nonneg C.hwn (by decide))) (rEv_nonneg C t) hgap
      (rEv_ge_inv_of_le C (awQ_den C) (awQ_num_pos C) htw (Qle_self_add C.hwn))
  -- ρ ≥ 1 + u·3/8
  have hρ : Rle (Radd one (ofQ (mul (uQ C) (⟨3, 8⟩ : Q)) (Qmul_den_pos (uQ_den C) (by decide))))
      (Rmul (ofQ (add C.a C.w) (awQ_den C)) (rEv C t)) := by
    refine Rle_of_Rnonneg_Rsub ?_
    refine Rnonneg_congr (Req_symm (sub_add_eq_sub_sub_of _ _ _)) ?_
    exact Rnonneg_Rsub_of_Rle (Rle_trans hprod (Rle_of_Req (Req_symm hρ1)))
  -- (a+w)·n·r = n·ρ ≥ n·(1 + u·3/8) = n + n·(u·3/8) ≥ n + 2·(u·3/8) ≥ n + 4η
  have hsplit : Req (Rmul (ofQ (awnQ C m) (awnQ_den C m)) (rEv C t))
      (Rmul (ofQ (upQ m) Nat.one_pos) (Rmul (ofQ (add C.a C.w) (awQ_den C)) (rEv C t))) :=
    Req_trans (Rmul_congr (Req_trans (ofQ_congr _ (Qmul_den_pos Nat.one_pos (awQ_den C)) (awnQ_eq C m))
      (Req_symm (Rmul_ofQ_ofQ Nat.one_pos (awQ_den C)))) (Req_refl _)) (Rmul_assoc _ _ _)
  refine Rle_trans ?_ (Rle_of_Req (Req_symm hsplit))
  refine Rle_trans ?_ (Rmul_le_Rmul_left (Rnonneg_ofQ Nat.one_pos (Int.ofNat_nonneg _)) hρ)
  refine Rle_trans ?_ (Rle_of_Req (Req_symm (Rmul_distrib _ _ _)))
  refine Rle_trans (Rle_of_Req (Req_symm (Radd_ofQ_ofQ Nat.one_pos (Qmul_den_pos Nat.one_pos (etaQ_den C))))) ?_
  refine Radd_le_add (Rle_of_Req (Req_symm (Rmul_one _))) ?_
  -- 4η ≤ 2·(u·3/8) ≤ n·(u·3/8)
  have h2n : Rle (ofQ (⟨2, 1⟩ : Q) Nat.one_pos) (ofQ (upQ m) Nat.one_pos) := by
    refine Rle_ofQ_ofQ Nat.one_pos Nat.one_pos ?_
    show (2 : Int) * ((1 : Nat) : Int) ≤ ((m + 1 : Nat) : Int) * ((1 : Nat) : Int); push_cast; omega
  refine Rle_trans (Rle_ofQ_ofQ _ (Qmul_den_pos Nat.one_pos (Qmul_den_pos (uQ_den C) (by decide))) (four_eta_le C)) ?_
  refine Rle_trans (Rle_of_Req (Req_symm (Rmul_ofQ_ofQ Nat.one_pos (Qmul_den_pos (uQ_den C) (by decide))))) ?_
  exact Rmul_le_Rmul_right (Rnonneg_ofQ _ (Qmul_num_nonneg (uQ_num C) (by decide))) h2n

/-- **Case L**: `t ≥ t_L = a + 3w/8` (and `t ≤ a+w`) ⟹ `a·n·r(t) ≤ n − 4η` (`m ≥ 1`). -/
theorem an_r_le_L (C : NormCtx) (m : Nat) (hm1 : 1 ≤ m) {t : Real} (hta : Rle (ofQ C.a C.had) t)
    (htL : Rle (ofQ (tLQ C) (tLQ_den C)) t) (htw : Rle t (ofQ (add C.a C.w) (awQ_den C))) :
    Rle (Rmul (ofQ (anQ C m) (anQ_den C m)) (rEv C t))
        (ofQ (Qsub (upQ m) (mul (⟨4, 1⟩ : Q) (etaQ C))) (Qsub_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos (etaQ_den C)))) := by
  -- 1 − a·r(t) = (t − a)·r(t) ≥ (3w/8)·(1/(a+w)) = u·3/8
  have hσ : Req (Rsub one (Rmul (ofQ C.a C.had) (rEv C t))) (Rmul (Rsub t (ofQ C.a C.had)) (rEv C t)) := by
    refine Req_trans (Rsub_congr (Req_symm (Req_trans (Rmul_comm _ _) (rEv_mul_t C hta))) (Req_refl _)) ?_
    exact Req_symm (Rmul_sub_distrib_right _ _ _)
  have hgap : Rle (ofQ (mul C.w (⟨3, 8⟩ : Q)) (Qmul_den_pos C.hw (by decide))) (Rsub t (ofQ C.a C.had)) := by
    refine Rle_trans (Rle_of_Req (Req_symm (Req_trans (Rsub_ofQ_ofQ (tLQ_den C) C.had) (ofQ_congr _ _ (tL_sub_a C))))) ?_
    exact Radd_le_add htL (Rle_refl _)
  have hprod : Rle (ofQ (mul (uQ C) (⟨3, 8⟩ : Q)) (Qmul_den_pos (uQ_den C) (by decide)))
      (Rmul (Rsub t (ofQ C.a C.had)) (rEv C t)) := by
    refine Rle_trans (Rle_of_Req (Req_symm (Req_trans (Rmul_ofQ_ofQ (Qmul_den_pos C.hw (by decide)) (Qinv_den_pos (awQ_num_pos C)))
      (ofQ_congr _ _ (w38_inv_aw C))))) ?_
    exact Rmul_le_Rmul_both (Rnonneg_ofQ _ (Qmul_num_nonneg C.hwn (by decide))) (rEv_nonneg C t) hgap
      (rEv_ge_inv_of_le C (awQ_den C) (awQ_num_pos C) htw (Qle_self_add C.hwn))
  -- a·r ≤ 1 − u·3/8
  have hσle : Rle (Rmul (ofQ C.a C.had) (rEv C t))
      (Rsub one (ofQ (mul (uQ C) (⟨3, 8⟩ : Q)) (Qmul_den_pos (uQ_den C) (by decide)))) := by
    refine Rle_of_Rnonneg_Rsub ?_
    -- (1 − c) − σ = (1 − σ) − c ≥ 0
    have e : Req (Rsub (Rsub one (ofQ (mul (uQ C) (⟨3, 8⟩ : Q)) (Qmul_den_pos (uQ_den C) (by decide))))
                       (Rmul (ofQ C.a C.had) (rEv C t)))
                 (Rsub (Rsub one (Rmul (ofQ C.a C.had) (rEv C t)))
                       (ofQ (mul (uQ C) (⟨3, 8⟩ : Q)) (Qmul_den_pos (uQ_den C) (by decide)))) :=
      Req_trans (Radd_assoc _ _ _) (Req_trans (Radd_congr (Req_refl _) (Radd_comm _ _)) (Req_symm (Radd_assoc _ _ _)))
    refine Rnonneg_congr (Req_symm e) ?_
    exact Rnonneg_Rsub_of_Rle (Rle_trans hprod (Rle_of_Req (Req_symm hσ)))
  -- a·n·r = n·(a·r) ≤ n·(1 − u·3/8) = n − n·(u·3/8) ≤ n − 2·(u·3/8) ≤ n − 4η
  have hsplit : Req (Rmul (ofQ (anQ C m) (anQ_den C m)) (rEv C t))
      (Rmul (ofQ (upQ m) Nat.one_pos) (Rmul (ofQ C.a C.had) (rEv C t))) :=
    Req_trans (Rmul_congr (Req_trans (ofQ_congr _ (Qmul_den_pos Nat.one_pos C.had) (anQ_eq C m))
      (Req_symm (Rmul_ofQ_ofQ Nat.one_pos C.had))) (Req_refl _)) (Rmul_assoc _ _ _)
  have hR : Req (Rsub (ofQ (upQ m) Nat.one_pos) (ofQ (mul (⟨4, 1⟩ : Q) (etaQ C)) (Qmul_den_pos Nat.one_pos (etaQ_den C))))
      (ofQ (Qsub (upQ m) (mul (⟨4, 1⟩ : Q) (etaQ C))) (Qsub_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos (etaQ_den C)))) :=
    Req_trans (Rsub_ofQ_ofQ Nat.one_pos (Qmul_den_pos Nat.one_pos (etaQ_den C))) (ofQ_congr _ _ (Qeq_refl _))
  have hdist : Req (Rmul (ofQ (upQ m) Nat.one_pos) (Rsub one (ofQ (mul (uQ C) (⟨3, 8⟩ : Q)) (Qmul_den_pos (uQ_den C) (by decide)))))
      (Rsub (Rmul (ofQ (upQ m) Nat.one_pos) one)
            (Rmul (ofQ (upQ m) Nat.one_pos) (ofQ (mul (uQ C) (⟨3, 8⟩ : Q)) (Qmul_den_pos (uQ_den C) (by decide))))) :=
    Rmul_sub_distrib _ _ _
  refine Rle_trans (Rle_of_Req hsplit) ?_
  refine Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ Nat.one_pos (Int.ofNat_nonneg _)) hσle) ?_
  refine Rle_trans (Rle_of_Req hdist) ?_
  refine Rle_trans ?_ (Rle_of_Req hR)
  refine Radd_le_add (Rle_of_Req (Rmul_one _)) (Rle_Rneg ?_)
  have h2n : Rle (ofQ (⟨2, 1⟩ : Q) Nat.one_pos) (ofQ (upQ m) Nat.one_pos) := by
    refine Rle_ofQ_ofQ Nat.one_pos Nat.one_pos ?_
    show (2 : Int) * ((1 : Nat) : Int) ≤ ((m + 1 : Nat) : Int) * ((1 : Nat) : Int); push_cast; omega
  refine Rle_trans (Rle_ofQ_ofQ _ (Qmul_den_pos Nat.one_pos (Qmul_den_pos (uQ_den C) (by decide))) (four_eta_le C)) ?_
  refine Rle_trans (Rle_of_Req (Req_symm (Rmul_ofQ_ofQ Nat.one_pos (Qmul_den_pos (uQ_den C) (by decide))))) ?_
  exact Rmul_le_Rmul_right (Rnonneg_ofQ _ (Qmul_num_nonneg (uQ_num C) (by decide))) h2n

-- ===========================================================================
-- (8) ★ THE UNIFORM POSITIVE HAAR MASS OF THE FIBER.
-- ===========================================================================

theorem Rsub_le_Rsub_of {a a' b b' : Real} (h1 : Rle a a') (h2 : Rle b' b) : Rle (Rsub a b) (Rsub a' b') :=
  Radd_le_add h1 (Rle_Rneg h2)

/-- The mask is `1` where both ramp arguments are at least `1`, i.e. `x̄ − λ ≥ η` and `μ − x̄ ≥ η`. -/
theorem maskF_eq_one (C : NormCtx) (k m : Nat) (hw0 : 0 < C.w.num) (x t : Real)
    (h1 : Rle (ofQ (etaQ C) (etaQ_den C)) (Rsub (xcl C x) ((lamF C k m).F x t)))
    (h2 : Rle (ofQ (etaQ C) (etaQ_den C)) (Rsub ((muF C k m).F x t) (xcl C x))) :
    Req ((maskF C k m hw0).F x t) one := by
  rw [maskF_F]
  have hη : Req (Rmul (ofQ (invEtaQ C) (invEtaQ_den C hw0)) (ofQ (etaQ C) (etaQ_den C))) one :=
    ofQ_inv_mul_self_of (etaQ C) (etaQ_den C) (etaQ_num_pos C hw0)
  have hr1 : Rle one (Rmul (ofQ (invEtaQ C) (invEtaQ_den C hw0)) (Rsub (xcl C x) ((lamF C k m).F x t))) :=
    Rle_trans (Rle_of_Req (Req_symm hη)) (Rmul_le_Rmul_left (Rnonneg_ofQ _ (invEtaQ_num C)) h1)
  have hr2 : Rle one (Rmul (ofQ (invEtaQ C) (invEtaQ_den C hw0)) (Rsub ((muF C k m).F x t) (xcl C x))) :=
    Rle_trans (Rle_of_Req (Req_symm hη)) (Rmul_le_Rmul_left (Rnonneg_ofQ _ (invEtaQ_num C)) h2)
  exact Req_trans (Rmul_congr (ramp_eq_one_of_ge hr1) (ramp_eq_one_of_ge hr2)) (Rmul_one _)

/-- `(mask·r)(x,t) ≥ 1/B` where the mask is `1`. -/
theorem mask_r_ge_invB (C : NormCtx) (k m : Nat) (hw0 : 0 < C.w.num) (x t : Real) (hmask : Req ((maskF C k m hw0).F x t) one) :
    Rle (ofQ (invBQ C) (invBQ_den C)) ((maskrF C k m hw0).F x t) := by
  rw [maskrF_F]
  refine Rle_trans (rOneCl_ge_invB C x) (Rle_of_Req (Req_symm ?_))
  exact Req_trans (Rmul_congr hmask (Req_refl _)) (Rone_mul _)

theorem maskr_nonneg (C : NormCtx) (k m : Nat) (hw0 : 0 < C.w.num) (t : Real) : ∀ x, Rnonneg ((maskrF C k m hw0).F x t) :=
  fun x => Rnonneg_Rmul (maskF_nonneg C k m hw0 x t) (Rnonneg_clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) _)

/-- The mass constant `c_mass = 2η/B`. -/
def cMass (C : NormCtx) : Q := mul (mul (⟨2, 1⟩ : Q) (etaQ C)) (invBQ C)
theorem cMass_den (C : NormCtx) : 0 < (cMass C).den := Qmul_den_pos (Qmul_den_pos Nat.one_pos (etaQ_den C)) (invBQ_den C)
theorem cMass_num_pos (C : NormCtx) (hw0 : 0 < C.w.num) : 0 < (cMass C).num :=
  Int.mul_pos (Int.mul_pos (by decide) (etaQ_num_pos C hw0)) (invBQ_num C)

theorem one_le_B_sub_n (C : NormCtx) (m : Nat) (hm : m < C.X) : Qle (⟨1, 1⟩ : Q) (Qsub (canonB C) (upQ m)) := by
  show (1 : Int) * ((1 * 1 : Nat) : Int) ≤ (((C.X + 1 : Nat) : Int) * ((1 : Nat) : Int) + (-((m + 1 : Nat) : Int)) * ((1 : Nat) : Int)) * ((1 : Nat) : Int)
  push_cast; omega
theorem one_le_upQ_sub_one (m : Nat) (hm1 : 1 ≤ m) : Qle (⟨1, 1⟩ : Q) (add (upQ m) (neg (⟨1, 1⟩ : Q))) := by
  show (1 : Int) * ((1 * 1 : Nat) : Int) ≤ (((m + 1 : Nat) : Int) * ((1 : Nat) : Int) + (-(1 : Int)) * ((1 : Nat) : Int)) * ((1 : Nat) : Int)
  push_cast; omega
theorem three_eta_le_38 (C : NormCtx) : Qle (mul (⟨3, 1⟩ : Q) (etaQ C)) (⟨3, 8⟩ : Q) :=
  Qle_trans (Qmul_den_pos Nat.one_pos (by decide)) (Qmul_le_mul_left (by decide) (etaQ_le_eighth C)) (by decide)
theorem four_eta_le_half (C : NormCtx) : Qle (mul (⟨4, 1⟩ : Q) (etaQ C)) (⟨1, 2⟩ : Q) :=
  Qle_trans (Qmul_den_pos Nat.one_pos (by decide)) (Qmul_le_mul_left (by decide) (etaQ_le_eighth C)) (by decide)
theorem tailLo_add_half_le_upQ (k m : Nat) (hk : 1 ≤ k) (hm1 : 1 ≤ m) : Qle (add (tailLo k) (⟨1, 2⟩ : Q)) (upQ m) := by
  have hp : 2 ≤ 2 ^ k := two_le_two_pow k hk
  show ((1 * ((2 ^ k : Nat) : Int) + 1 * ((1 : Nat) : Int)) * ((2 : Nat) : Int) + 1 * ((1 * 2 ^ k : Nat) : Int)) * ((1 : Nat) : Int)
      ≤ ((m + 1 : Nat) : Int) * ((1 * 2 ^ k * 2 : Nat) : Int)
  have hp' : (2 : Int) ≤ (2 : Int) ^ k := by exact_mod_cast hp
  have hm' : (1 : Int) ≤ (m : Int) := by exact_mod_cast hm1
  push_cast
  generalize hP : (2 : Int) ^ k = P at hp' ⊢
  have h1 : 1 * P ≤ (m : Int) * P := Int.mul_le_mul_of_nonneg_right hm' (by omega)
  have e1 : ((1 * P + 1) * 2 + 1 * (1 * P)) * 1 = 3 * P + 2 := by ring_uor
  have e2 : ((m : Int) + 1) * (1 * P * 2) = 2 * ((m : Int) * P) + 2 * P := by ring_uor
  rw [e1, e2]; omega

/-- **★ THE MASS IS AT LEAST `2η/B`** on every active row (`m ≥ 1`, `m < X`, `w > 0`, `k ≥ 1`, `t ∈ [a, a+w]`). -/
theorem massF_ge (C : NormCtx) (k m : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (hm : m < C.X) (hm1 : 1 ≤ m)
    (x t : Real) (ht : InWin C t) :
    Rle (ofQ (cMass C) (cMass_den C)) ((massF C k m hw0 hk).F x t) := by
  rw [massF_F]
  have hta : Rle (ofQ C.a C.had) t := ht.1
  have htw : Rle t (ofQ (add C.a C.w) (awQ_den C)) := ht.2
  have hnn : ∀ x, Rnonneg ((maskrF C k m hw0).F x t) := maskr_nonneg C k m hw0 t
  rcases Rle_or_Rle (x := t) (tLQ_den C) (tRQ_den C) (tLQ_lt_tRQ C hw0) with hR | hL
  · -- CASE R: `t ≤ a + 5w/8`; the fiber contains `[n, n + 4η]`; plateau `[n + η, n + 3η]`.
    have hw1n : 0 < (add (Qsub (upQ m) (tailLo k)) (etaQ C)).num :=
      Qadd_num_pos_of (upQ_sub_tailLo_num_pos k m hk hm1) (Qsub_den_pos Nat.one_pos (tailLo_den k)) (etaQ_num C) (etaQ_den C)
    have hvn : 0 < (mul (⟨2, 1⟩ : Q) (etaQ C)).num := Int.mul_pos (by decide) (etaQ_num_pos C hw0)
    have hw3n : 0 ≤ (add (Qsub (Qsub (canonB C) (upQ m)) (⟨1, 1⟩ : Q)) (Qsub (⟨1, 1⟩ : Q) (mul (⟨3, 1⟩ : Q) (etaQ C)))).num :=
      Qadd_num_nonneg_loc (Qsub_num_nonneg (one_le_B_sub_n C m hm)) (Qsub_num_nonneg (three_eta_le_one C))
    have hq : Qeq (tailGap C k) (add (add (Qsub (upQ m) (tailLo k)) (etaQ C))
        (add (mul (⟨2, 1⟩ : Q) (etaQ C)) (add (Qsub (Qsub (canonB C) (upQ m)) (⟨1, 1⟩ : Q)) (Qsub (⟨1, 1⟩ : Q) (mul (⟨3, 1⟩ : Q) (etaQ C)))))) := by
      simp only [Qeq, tailGap, tailLo, add, Qsub, neg, mul, canonB, upQ, dyQ]; push_cast; ring_uor
    have hplo : Qeq (add (tailLo k) (add (Qsub (upQ m) (tailLo k)) (etaQ C))) (add (upQ m) (etaQ C)) := by
      simp only [Qeq, tailLo, add, Qsub, neg, mul, upQ, dyQ]; push_cast; ring_uor
    have hphi : Qeq (add (add (tailLo k) (add (Qsub (upQ m) (tailLo k)) (etaQ C))) (mul (⟨2, 1⟩ : Q) (etaQ C)))
        (add (upQ m) (mul (⟨3, 1⟩ : Q) (etaQ C))) := by
      simp only [Qeq, tailLo, add, Qsub, neg, mul, upQ, dyQ]; push_cast; ring_uor
    -- the plateau
    have hplat : ∀ s, Rle zero s → Rle s one → Rle (ofQ (invBQ C) (invBQ_den C))
        ((maskrF C k m hw0).F (affineMap (add (tailLo k) (add (Qsub (upQ m) (tailLo k)) (etaQ C))) (mul (⟨2, 1⟩ : Q) (etaQ C))
          (add_den_pos (tailLo_den k) (add_den_pos (Qsub_den_pos Nat.one_pos (tailLo_den k)) (etaQ_den C)))
          (Qmul_den_pos Nat.one_pos (etaQ_den C)) s) t) := by
      intro s hs0 hs1
      have hxlo := affineMap_ge_lo_c5 (add (tailLo k) (add (Qsub (upQ m) (tailLo k)) (etaQ C))) (mul (⟨2, 1⟩ : Q) (etaQ C)) (add_den_pos (tailLo_den k) (add_den_pos (Qsub_den_pos Nat.one_pos (tailLo_den k)) (etaQ_den C)))
        (Qmul_den_pos Nat.one_pos (etaQ_den C)) (Int.le_of_lt hvn) s hs0
      have hxhi := affineMap_le_hi_c5 (add (tailLo k) (add (Qsub (upQ m) (tailLo k)) (etaQ C))) (mul (⟨2, 1⟩ : Q) (etaQ C)) (add_den_pos (tailLo_den k) (add_den_pos (Qsub_den_pos Nat.one_pos (tailLo_den k)) (etaQ_den C)))
        (Qmul_den_pos Nat.one_pos (etaQ_den C)) (Int.le_of_lt hvn) s hs1
      have hxlo' : Rle (ofQ (add (upQ m) (etaQ C)) (add_den_pos Nat.one_pos (etaQ_den C))) _ :=
        Rle_trans (Rle_of_Req (ofQ_congr _ _ (Qeq_symm hplo))) hxlo
      have hxhi' : Rle _ (ofQ (add (upQ m) (mul (⟨3, 1⟩ : Q) (etaQ C))) (add_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos (etaQ_den C)))) :=
        Rle_trans hxhi (Rle_of_Req (ofQ_congr _ _ hphi))
      have hx1 : Rle one _ := Rle_trans (Rle_ofQ_ofQ (by decide) _ (Qle_trans Nat.one_pos (one_le_upQ m) (Qle_self_add (etaQ_num C)))) hxlo'
      have hxB : Rle _ (ofQ (canonB C) (canonB_den C)) :=
        Rle_trans hxhi' (Rle_ofQ_ofQ _ _ (Qle_trans (add_den_pos Nat.one_pos Nat.one_pos)
          (Qadd_le_add (Qle_refl _) (three_eta_le_one C)) (upQ_add_one_le_B C m hm)))
      have hxcl := xcl_eq_of_band C hx1 hxB
      refine mask_r_ge_invB C k m hw0 _ t (maskF_eq_one C k m hw0 _ t ?_ ?_)
      · -- x̄ − λ ≥ (n + η) − n = η
        refine Rle_trans (Rle_of_Req (Req_symm (Req_trans (Rsub_ofQ_ofQ (a := add (upQ m) (etaQ C)) (b := upQ m) (add_den_pos Nat.one_pos (etaQ_den C)) Nat.one_pos)
          (ofQ_congr _ _ (by simp only [Qeq, add, neg, mul, upQ]; push_cast; ring_uor))))) ?_
        exact Rsub_le_Rsub_of (Rle_trans hxlo' (Rle_of_Req (Req_symm hxcl))) (lam_le_n C k m hm1 _ t)
      · -- μ − x̄ ≥ (n + 4η) − (n + 3η) = η
        have hmu : Rle (ofQ (add (upQ m) (mul (⟨4, 1⟩ : Q) (etaQ C))) (add_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos (etaQ_den C))))
            ((muF C k m).F (affineMap (add (tailLo k) (add (Qsub (upQ m) (tailLo k)) (etaQ C))) (mul (⟨2, 1⟩ : Q) (etaQ C)) (add_den_pos (tailLo_den k) (add_den_pos (Qsub_den_pos Nat.one_pos (tailLo_den k)) (etaQ_den C))) (Qmul_den_pos Nat.one_pos (etaQ_den C)) s) t) := by
          rw [muF_F]
          exact band_ge_of_ge _ _ _ _ (add_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos (etaQ_den C))) (awn_r_ge_R C m hm1 hta hR htw)
            (Qle_trans (add_den_pos Nat.one_pos Nat.one_pos) (Qadd_le_add (Qle_refl _) (four_eta_le_one C)) (upQ_add_one_le_B C m hm))
        refine Rle_trans (Rle_of_Req (Req_symm (Req_trans (Rsub_ofQ_ofQ (a := add (upQ m) (mul (⟨4, 1⟩ : Q) (etaQ C))) (b := add (upQ m) (mul (⟨3, 1⟩ : Q) (etaQ C)))
          (add_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos (etaQ_den C)))
          (add_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos (etaQ_den C))))
          (ofQ_congr _ _ (by simp only [Qeq, add, neg, mul, upQ]; push_cast; ring_uor))))) ?_
        exact Rsub_le_Rsub_of hmu (Rle_trans (Rle_of_Req hxcl) hxhi')
    have hpl := xInt_ge_plateau (maskrF C k m hw0) (tailLo k) (add (Qsub (upQ m) (tailLo k)) (etaQ C)) (mul (⟨2, 1⟩ : Q) (etaQ C))
      (add (Qsub (Qsub (canonB C) (upQ m)) (⟨1, 1⟩ : Q)) (Qsub (⟨1, 1⟩ : Q) (mul (⟨3, 1⟩ : Q) (etaQ C))))
      (tailLo_den k) (add_den_pos (Qsub_den_pos Nat.one_pos (tailLo_den k)) (etaQ_den C)) (Qmul_den_pos Nat.one_pos (etaQ_den C))
      (add_den_pos (Qsub_den_pos (Qsub_den_pos (canonB_den C) Nat.one_pos) Nat.one_pos) (Qsub_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos (etaQ_den C))))
      hw1n hvn hw3n t (invBQ_den C) (Int.le_of_lt (invBQ_num C)) hnn hplat
    refine Rle_trans hpl ?_
    unfold xInt
    exact Rle_of_Req (intI_window_congr _ _ _ _ (tailLo k) _ _ (tailLo_den k) _ _ (tailGap_den C k) (tailGap_num_nonneg C k hk) (Qeq_symm hq))
  · -- CASE L: `t ≥ a + 3w/8`; the fiber contains `[n − 4η, n]`; plateau `[n − 3η, n − η]`.
    have h38 : Qle (mul (⟨3, 1⟩ : Q) (etaQ C)) (⟨3, 8⟩ : Q) := three_eta_le_38 C
    have hw1n : 0 < (add (Qsub (Qsub (upQ m) (⟨3, 8⟩ : Q)) (tailLo k)) (Qsub (⟨3, 8⟩ : Q) (mul (⟨3, 1⟩ : Q) (etaQ C)))).num :=
      Qadd_num_pos_of (upQ_sub_tailLo_38_num_pos k m hk hm1) (Qsub_den_pos (Qsub_den_pos Nat.one_pos (by decide)) (tailLo_den k))
        (Qsub_num_nonneg h38) (Qsub_den_pos (by decide) (Qmul_den_pos Nat.one_pos (etaQ_den C)))
    have hvn : 0 < (mul (⟨2, 1⟩ : Q) (etaQ C)).num := Int.mul_pos (by decide) (etaQ_num_pos C hw0)
    have hw3n : 0 ≤ (add (Qsub (canonB C) (upQ m)) (etaQ C)).num :=
      Qadd_num_nonneg_loc (Qsub_num_nonneg (upQ_le_B C m hm)) (etaQ_num C)
    have hq : Qeq (tailGap C k) (add (add (Qsub (Qsub (upQ m) (⟨3, 8⟩ : Q)) (tailLo k)) (Qsub (⟨3, 8⟩ : Q) (mul (⟨3, 1⟩ : Q) (etaQ C))))
        (add (mul (⟨2, 1⟩ : Q) (etaQ C)) (add (Qsub (canonB C) (upQ m)) (etaQ C)))) := by
      simp only [Qeq, tailGap, tailLo, add, Qsub, neg, mul, canonB, upQ, dyQ]; push_cast; ring_uor
    have hplo : Qeq (add (tailLo k) (add (Qsub (Qsub (upQ m) (⟨3, 8⟩ : Q)) (tailLo k)) (Qsub (⟨3, 8⟩ : Q) (mul (⟨3, 1⟩ : Q) (etaQ C)))))
        (Qsub (upQ m) (mul (⟨3, 1⟩ : Q) (etaQ C))) := by
      simp only [Qeq, tailLo, add, Qsub, neg, mul, upQ, dyQ]; push_cast; ring_uor
    have hphi : Qeq (add (add (tailLo k) (add (Qsub (Qsub (upQ m) (⟨3, 8⟩ : Q)) (tailLo k)) (Qsub (⟨3, 8⟩ : Q) (mul (⟨3, 1⟩ : Q) (etaQ C)))))
        (mul (⟨2, 1⟩ : Q) (etaQ C))) (Qsub (upQ m) (etaQ C)) := by
      simp only [Qeq, tailLo, add, Qsub, neg, mul, upQ, dyQ]; push_cast; ring_uor
    have hplat : ∀ s, Rle zero s → Rle s one → Rle (ofQ (invBQ C) (invBQ_den C))
        ((maskrF C k m hw0).F (affineMap (add (tailLo k) (add (Qsub (Qsub (upQ m) (⟨3, 8⟩ : Q)) (tailLo k)) (Qsub (⟨3, 8⟩ : Q) (mul (⟨3, 1⟩ : Q) (etaQ C)))))
          (mul (⟨2, 1⟩ : Q) (etaQ C))
          (add_den_pos (tailLo_den k) (add_den_pos (Qsub_den_pos (Qsub_den_pos Nat.one_pos (by decide)) (tailLo_den k))
            (Qsub_den_pos (by decide) (Qmul_den_pos Nat.one_pos (etaQ_den C)))))
          (Qmul_den_pos Nat.one_pos (etaQ_den C)) s) t) := by
      intro s hs0 hs1
      have hxlo := affineMap_ge_lo_c5 (add (tailLo k) (add (Qsub (Qsub (upQ m) (⟨3, 8⟩ : Q)) (tailLo k)) (Qsub (⟨3, 8⟩ : Q) (mul (⟨3, 1⟩ : Q) (etaQ C))))) (mul (⟨2, 1⟩ : Q) (etaQ C)) (add_den_pos (tailLo_den k) (add_den_pos (Qsub_den_pos (Qsub_den_pos Nat.one_pos (by decide)) (tailLo_den k))
            (Qsub_den_pos (by decide) (Qmul_den_pos Nat.one_pos (etaQ_den C)))))
        (Qmul_den_pos Nat.one_pos (etaQ_den C)) (Int.le_of_lt hvn) s hs0
      have hxhi := affineMap_le_hi_c5 (add (tailLo k) (add (Qsub (Qsub (upQ m) (⟨3, 8⟩ : Q)) (tailLo k)) (Qsub (⟨3, 8⟩ : Q) (mul (⟨3, 1⟩ : Q) (etaQ C))))) (mul (⟨2, 1⟩ : Q) (etaQ C)) (add_den_pos (tailLo_den k) (add_den_pos (Qsub_den_pos (Qsub_den_pos Nat.one_pos (by decide)) (tailLo_den k))
            (Qsub_den_pos (by decide) (Qmul_den_pos Nat.one_pos (etaQ_den C)))))
        (Qmul_den_pos Nat.one_pos (etaQ_den C)) (Int.le_of_lt hvn) s hs1
      have hxlo' : Rle (ofQ (Qsub (upQ m) (mul (⟨3, 1⟩ : Q) (etaQ C))) (Qsub_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos (etaQ_den C)))) _ :=
        Rle_trans (Rle_of_Req (ofQ_congr _ _ (Qeq_symm hplo))) hxlo
      have hxhi' : Rle _ (ofQ (Qsub (upQ m) (etaQ C)) (Qsub_den_pos Nat.one_pos (etaQ_den C))) :=
        Rle_trans hxhi (Rle_of_Req (ofQ_congr _ _ hphi))
      -- 1 ≤ n − 3η  (n − 3η ≥ n − 1 ≥ 1), and n − η ≤ n ≤ B
      have h1n3 : Qle (⟨1, 1⟩ : Q) (Qsub (upQ m) (mul (⟨3, 1⟩ : Q) (etaQ C))) := by
        refine Qle_of_Rle_ofQ_of (by decide) (Qsub_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos (etaQ_den C))) ?_
        refine Rle_trans ?_ (Rle_of_Req (Rsub_ofQ_ofQ Nat.one_pos (Qmul_den_pos Nat.one_pos (etaQ_den C))))
        refine Rle_trans ?_ (Rsub_le_Rsub_of (Rle_refl _) (Rle_ofQ_ofQ _ (by decide) (three_eta_le_one C)))
        refine Rle_trans ?_ (Rle_of_Req (Req_symm (Rsub_ofQ_ofQ Nat.one_pos Nat.one_pos)))
        exact Rle_ofQ_ofQ (by decide) _ (one_le_upQ_sub_one m hm1)
      have hx1 : Rle one (affineMap (add (tailLo k) (add (Qsub (Qsub (upQ m) (⟨3, 8⟩ : Q)) (tailLo k)) (Qsub (⟨3, 8⟩ : Q) (mul (⟨3, 1⟩ : Q) (etaQ C))))) (mul (⟨2, 1⟩ : Q) (etaQ C)) (add_den_pos (tailLo_den k) (add_den_pos (Qsub_den_pos (Qsub_den_pos Nat.one_pos (by decide)) (tailLo_den k)) (Qsub_den_pos (by decide) (Qmul_den_pos Nat.one_pos (etaQ_den C))))) (Qmul_den_pos Nat.one_pos (etaQ_den C)) s) := Rle_trans (Rle_ofQ_ofQ (by decide) _ h1n3) hxlo'
      have hxB : Rle (affineMap (add (tailLo k) (add (Qsub (Qsub (upQ m) (⟨3, 8⟩ : Q)) (tailLo k)) (Qsub (⟨3, 8⟩ : Q) (mul (⟨3, 1⟩ : Q) (etaQ C))))) (mul (⟨2, 1⟩ : Q) (etaQ C)) (add_den_pos (tailLo_den k) (add_den_pos (Qsub_den_pos (Qsub_den_pos Nat.one_pos (by decide)) (tailLo_den k)) (Qsub_den_pos (by decide) (Qmul_den_pos Nat.one_pos (etaQ_den C))))) (Qmul_den_pos Nat.one_pos (etaQ_den C)) s) (ofQ (canonB C) (canonB_den C)) := by
        refine Rle_trans hxhi' ?_
        refine Rle_trans (Rle_of_Req (Req_symm (Rsub_ofQ_ofQ Nat.one_pos (etaQ_den C)))) ?_
        refine Rle_trans (Radd_le_add (Rle_refl _) (Rle_Rneg (Rle_ofQ_ofQ (by decide) _ (Qle_zero_of_num_of (etaQ_num C))))) ?_
        refine Rle_trans (Rle_of_Req (Req_trans (Radd_congr (Req_refl _) (Rneg_ofQ _ _)) (Radd_ofQ_ofQ Nat.one_pos Nat.one_pos))) ?_
        exact Rle_ofQ_ofQ _ _ (Qle_trans Nat.one_pos (Qeq_le (by simp only [Qeq, add, neg, upQ]; push_cast; ring_uor)) (upQ_le_B C m hm))
      have hxcl := xcl_eq_of_band C hx1 hxB
      refine mask_r_ge_invB C k m hw0 _ t (maskF_eq_one C k m hw0 _ t ?_ ?_)
      · -- x̄ − λ ≥ (n − 3η) − (n − 4η) = η
        have hlam : Rle ((lamF C k m).F (affineMap (add (tailLo k) (add (Qsub (Qsub (upQ m) (⟨3, 8⟩ : Q)) (tailLo k)) (Qsub (⟨3, 8⟩ : Q) (mul (⟨3, 1⟩ : Q) (etaQ C))))) (mul (⟨2, 1⟩ : Q) (etaQ C)) (add_den_pos (tailLo_den k) (add_den_pos (Qsub_den_pos (Qsub_den_pos Nat.one_pos (by decide)) (tailLo_den k)) (Qsub_den_pos (by decide) (Qmul_den_pos Nat.one_pos (etaQ_den C))))) (Qmul_den_pos Nat.one_pos (etaQ_den C)) s) t)
            (ofQ (Qsub (upQ m) (mul (⟨4, 1⟩ : Q) (etaQ C))) (Qsub_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos (etaQ_den C)))) := by
          rw [lamF_F]
          refine band_le_of_le _ _ _ _ (Qsub_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos (etaQ_den C))) (an_r_le_L C m hm1 hta hL htw) ?_
          refine Qle_of_Rle_ofQ_of (tailLo_den k) (Qsub_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos (etaQ_den C))) ?_
          refine Rle_trans ?_ (Rle_of_Req (Rsub_ofQ_ofQ Nat.one_pos (Qmul_den_pos Nat.one_pos (etaQ_den C))))
          refine Rle_trans ?_ (Rsub_le_Rsub_of (Rle_refl _) (Rle_ofQ_ofQ _ (by decide) (four_eta_le_half C)))
          refine Rle_trans ?_ (Rle_of_Req (Req_symm (Rsub_ofQ_ofQ Nat.one_pos (by decide))))
          refine Rle_trans ?_ (Rle_ofQ_ofQ (add_den_pos (add_den_pos (tailLo_den k) (by decide)) (by decide)) _ (Qadd_le_add (tailLo_add_half_le_upQ k m hk hm1) (Qle_refl (neg (⟨1, 2⟩ : Q)))))
          exact Rle_of_Req (ofQ_congr _ _ (by simp only [Qeq, add, neg]; push_cast; ring_uor))
        refine Rle_trans (Rle_of_Req (Req_symm (Req_trans (Rsub_ofQ_ofQ (a := Qsub (upQ m) (mul (⟨3, 1⟩ : Q) (etaQ C))) (b := Qsub (upQ m) (mul (⟨4, 1⟩ : Q) (etaQ C)))
          (Qsub_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos (etaQ_den C)))
          (Qsub_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos (etaQ_den C))))
          (ofQ_congr _ _ (by simp only [Qeq, add, neg, mul, Qsub, upQ]; push_cast; ring_uor))))) ?_
        exact Rsub_le_Rsub_of (Rle_trans hxlo' (Rle_of_Req (Req_symm hxcl))) hlam
      · -- μ − x̄ ≥ n − (n − η) = η
        refine Rle_trans (Rle_of_Req (Req_symm (Req_trans (Rsub_ofQ_ofQ (a := upQ m) (b := Qsub (upQ m) (etaQ C)) Nat.one_pos (Qsub_den_pos Nat.one_pos (etaQ_den C)))
          (ofQ_congr _ _ (by simp only [Qeq, add, neg, mul, Qsub, upQ]; push_cast; ring_uor))))) ?_
        exact Rsub_le_Rsub_of (mu_ge_n C k m hm htw _) (Rle_trans (Rle_of_Req hxcl) hxhi')
    have hpl := xInt_ge_plateau (maskrF C k m hw0) (tailLo k) (add (Qsub (Qsub (upQ m) (⟨3, 8⟩ : Q)) (tailLo k)) (Qsub (⟨3, 8⟩ : Q) (mul (⟨3, 1⟩ : Q) (etaQ C))))
      (mul (⟨2, 1⟩ : Q) (etaQ C)) (add (Qsub (canonB C) (upQ m)) (etaQ C))
      (tailLo_den k) (add_den_pos (Qsub_den_pos (Qsub_den_pos Nat.one_pos (by decide)) (tailLo_den k))
        (Qsub_den_pos (by decide) (Qmul_den_pos Nat.one_pos (etaQ_den C)))) (Qmul_den_pos Nat.one_pos (etaQ_den C))
      (add_den_pos (Qsub_den_pos (canonB_den C) Nat.one_pos) (etaQ_den C))
      hw1n hvn hw3n t (invBQ_den C) (Int.le_of_lt (invBQ_num C)) hnn hplat
    refine Rle_trans hpl ?_
    unfold xInt
    exact Rle_of_Req (intI_window_congr _ _ _ _ (tailLo k) _ _ (tailLo_den k) _ _ (tailGap_den C k) (tailGap_num_nonneg C k hk) (Qeq_symm hq))

-- ===========================================================================
-- (9) Mate-in-window, and the reading identity on the fiber.
-- ===========================================================================

/-- `v ≤ hi ⟹ v ≤ band(v)`. -/
theorem band_ge_self_of_le (lo hi : Q) (hlo : 0 < lo.den) (hhi : 0 < hi.den) {v : Real} (hv : Rle v (ofQ hi hhi)) :
    Rle v (qBandQ lo hi hlo hhi v) := by
  intro n
  have h1 : Qle (v.seq n) (add hi ⟨2, n + 1⟩) := hv n
  show Qle (v.seq n) (add (Qmin (Qmax (v.seq n) lo) hi) ⟨2, n + 1⟩)
  rcases Qle_or_Qlt (Qmax (v.seq n) lo) hi with hle | hlt
  · rw [Qmin_eq_left hle]
    exact Qle_trans (Qmax_den_pos (v.den_pos n) hlo) (Qle_Qmax_left_of _ _) (Qle_self_add (two_num_nonneg_of n))
  · rw [Qmin_eq_right (not_Qle_of_Qlt hlt)]; exact h1

/-- `λ(t) ≥ a·n·r(t)` (the clamp is inert from above since `a·n·r(t) ≤ n ≤ B`). -/
theorem lam_ge_anr (C : NormCtx) (k m : Nat) (hm : m < C.X) (x t : Real) :
    Rle (Rmul (ofQ (anQ C m) (anQ_den C m)) (rEv C t)) ((lamF C k m).F x t) := by
  rw [lamF_F]
  exact band_ge_self_of_le _ _ _ _ (Rle_trans (an_r_le_n C m t) (Rle_ofQ_ofQ Nat.one_pos (canonB_den C) (upQ_le_B C m hm)))

/-- **★ MATE-IN-WINDOW**: `x̄ ≥ λ(t)` and `t ≥ a` ⟹ the mate `x̄·t/n ≥ a`. -/
theorem mate_ge_a_of_lam (C : NormCtx) (k m : Nat) (hm : m < C.X) {x t : Real} (hta : Rle (ofQ C.a C.had) t)
    (hxl : Rle ((lamF C k m).F x t) (xcl C x)) :
    Rle (ofQ C.a C.had) (Rmul (xcl C x) (Rmul t (ofQ (invNQ m) (Nat.succ_pos m)))) := by
  have hnn : Rnonneg (Rmul t (ofQ (invNQ m) (Nat.succ_pos m))) :=
    Rnonneg_Rmul (Rnonneg_of_ge_a C hta) (Rnonneg_ofQ (Nat.succ_pos m) (invNQ_num m))
  have hx : Rle (Rmul (ofQ (anQ C m) (anQ_den C m)) (rEv C t)) (xcl C x) := Rle_trans (lam_ge_anr C k m hm x t) hxl
  have hprod : Rle (Rmul (Rmul (ofQ (anQ C m) (anQ_den C m)) (rEv C t)) (Rmul t (ofQ (invNQ m) (Nat.succ_pos m))))
      (Rmul (xcl C x) (Rmul t (ofQ (invNQ m) (Nat.succ_pos m)))) := Rmul_le_Rmul_right hnn hx
  have halg : Req (Rmul (Rmul (ofQ (anQ C m) (anQ_den C m)) (rEv C t)) (Rmul t (ofQ (invNQ m) (Nat.succ_pos m)))) (ofQ C.a C.had) := by
    have e1 : Req (ofQ (anQ C m) (anQ_den C m)) (Rmul (ofQ C.a C.had) (upR m)) := Req_symm (Rmul_ofQ_ofQ C.had Nat.one_pos)
    have e2 : Req (Rmul (Rmul (Rmul (ofQ C.a C.had) (upR m)) (rEv C t)) (Rmul (ofQ (invNQ m) (Nat.succ_pos m)) t))
        (Rmul (ofQ C.a C.had) (Rmul (Rmul (upR m) (ofQ (invNQ m) (Nat.succ_pos m))) (Rmul (rEv C t) t))) :=
      Req_trans (Rmul_congr (Rmul_assoc _ _ _) (Req_refl _))
        (Req_trans (Rmul_assoc _ _ _) (Rmul_congr (Req_refl _) (mul4_swap_ch _ _ _ _)))
    refine Req_trans (Rmul_congr (Rmul_congr e1 (Req_refl _)) (Rmul_comm _ _)) (Req_trans e2 ?_)
    refine Req_trans (Rmul_congr (Req_refl _) (Rmul_congr (Req_trans (Rmul_comm _ _) (ofQ_recip_one m)) (rEv_mul_t C hta))) ?_
    exact Req_trans (Rmul_congr (Req_refl _) (Rmul_one _)) (Rmul_one _)
  exact Rle_trans (Rle_of_Req (Req_symm halg)) hprod

/-- **★ THE READING IDENTITY ON THE FIBER**: for `x̄ ≥ λ(t)` and `t ∈ [a, a+w]`, the reading integrand of the cut
    analysis at `(x,t)` is `r(x̄)·U_n(f,t)` (the orbit law only needs the mate `≥ a`). -/
theorem readF_source_fiber (C : NormCtx) (k m : Nat) (hm : m < C.X) (f : L2Test) (x t : Real)
    (hxl : Rle ((lamF C k m).F x t) (xcl C x)) (ht : InWin C t) :
    Req ((readF C k m (cutAnalysis5 C k f)).F x t) (Rmul (rOne (xcl C x)) (Uc C (upR m) f t)) := by
  rw [readF_F]
  have htb : Req (tBand C t) t := tBand_eq_of_win C ht.1 ht.2
  have hs : Req (Rmul (xcl C x) (Rmul (tBand C t) (ofQ (invNQ m) (Nat.succ_pos m))))
      (Rmul (xcl C x) (Rmul t (ofQ (invNQ m) (Nat.succ_pos m)))) :=
    Rmul_congr (Req_refl _) (Rmul_congr htb (Req_refl _))
  have hrec : Req ((recUF C k (cutAnalysis5 C k f)).F (xcl C x) (Rmul (xcl C x) (Rmul (tBand C t) (ofQ (invNQ m) (Nat.succ_pos m)))))
      (Uc C (xcl C x) f (Rmul (xcl C x) (Rmul t (ofQ (invNQ m) (Nat.succ_pos m))))) := by
    refine Req_trans ((recUF C k (cutAnalysis5 C k f)).hfct _ hs) ?_
    exact Req_trans (recUF_source C k f (xcl C x) _) (Uc_congr_x C (xcl_idem C x) f _)
  refine Req_trans (Rmul_congr (Req_refl _) hrec) ?_
  have hOrb : Req (Rmul (invSq C (upR m)) (Uc C (xcl C x) f (Rmul (xcl C x) (Rmul t (ofQ (invNQ m) (Nat.succ_pos m))))))
      (Rmul (invSq C (xcl C x)) (Uc C (upR m) f t)) :=
    Uc_orbit C f (xcl_zero_le C x) (xcl_le_S C x) (upR_nonneg m) (upR_le_S C m hm) (mate_ge_a_of_lam C k m hm ht.1 hxl) ht.1
      (orbit_mate_alg m (xcl C x) t)
  obtain ⟨kx, hkx⟩ := Pos_of_Rle_ofQ (canonC_num C) (canonC_den C) (c_le_xcl C x)
  have hW := invSq_sq_mul_self C (c_le_xcl C x) (xcl_le_B C x) hkx
  exact read_alg _ _ _ _ _ _ hOrb hW

-- --- the ε-argument: the masked reading equals `U_n(t)` times the masked weight, everywhere ---

theorem Qlt_zero_inv_succ (j : Nat) : Qlt (⟨0, 1⟩ : Q) (⟨1, j + 1⟩ : Q) := by unfold Qlt; push_cast; omega

/-- The uniform bound of `|readF − U_n(t)·r|` on the analysis: `M_read + (M_f/c)·1`. -/
def diffBound (C : NormCtx) (k m : Nat) (f : L2Test) : Q :=
  add (readF C k m (cutAnalysis5 C k f)).M (mul (mul (Qinv (canonC C)) f.M) (Qinv (⟨1, 1⟩ : Q)))
theorem diffBound_den (C : NormCtx) (k m : Nat) (f : L2Test) : 0 < (diffBound C k m f).den :=
  add_den_pos (readF C k m (cutAnalysis5 C k f)).hMd (Qmul_den_pos (Qmul_den_pos (Qinv_den_pos (canonC_num C)) f.hMd) (Qinv_den_pos (by decide)))
theorem diffBound_num (C : NormCtx) (k m : Nat) (f : L2Test) : 0 ≤ (diffBound C k m f).num :=
  Qadd_num_nonneg_loc (readF C k m (cutAnalysis5 C k f)).hMn
    (Qmul_num_nonneg (Qmul_num_nonneg (Int.le_of_lt (Qinv_num_pos (canonC_den C))) f.hMn) (Int.le_of_lt (Qinv_num_pos (by decide))))

theorem diff_abs_bd (C : NormCtx) (k m : Nat) (f : L2Test) (x t : Real) :
    Rle (Rabs (Rsub ((readF C k m (cutAnalysis5 C k f)).F x t) (Rmul (Uc C (upR m) f t) (rOne (xcl C x)))))
        (ofQ (diffBound C k m f) (diffBound_den C k m f)) := by
  have h2 : Rle (Rabs (Rneg (Rmul (Uc C (upR m) f t) (rOne (xcl C x)))))
      (ofQ (mul (mul (Qinv (canonC C)) f.M) (Qinv (⟨1, 1⟩ : Q)))
        (Qmul_den_pos (Qmul_den_pos (Qinv_den_pos (canonC_num C)) f.hMd) (Qinv_den_pos (by decide)))) :=
    Rle_trans (Rle_of_Req (Rabs_Rneg _)) (abs_mul_bd _ (Qinv_den_pos (by decide)) (Int.le_of_lt (Qinv_num_pos (by decide)))
      (Uc_bd C f (upR m) t) (rOne_bd (xcl C x)))
  exact Rle_trans (Rabs_Radd _ _)
    (Rle_trans (Radd_le_add ((readF C k m (cutAnalysis5 C k f)).hbd x t) h2) (Rle_of_Req (Radd_ofQ_ofQ _ _)))

/-- `μ·R − U·(μ·r) ≈ μ·(R − U·r)`. -/
theorem mask_diff_alg (μ R U r : Real) : Req (Rsub (Rmul μ R) (Rmul U (Rmul μ r))) (Rmul μ (Rsub R (Rmul U r))) := by
  refine Req_trans (Rsub_congr (Req_refl _) (Req_trans (Req_symm (Rmul_assoc _ _ _))
    (Req_trans (Rmul_congr (Rmul_comm _ _) (Req_refl _)) (Rmul_assoc _ _ _)))) ?_
  exact Req_symm (Rmul_sub_distrib _ _ _)

/-- The constant `K = (1/η)·(M_read + M_f/c)` and its integer ceiling. -/
def epsK (C : NormCtx) (k m : Nat) (f : L2Test) : Q := mul (invEtaQ C) (diffBound C k m f)
theorem epsK_den (C : NormCtx) (k m : Nat) (hw0 : 0 < C.w.num) (f : L2Test) : 0 < (epsK C k m f).den :=
  Qmul_den_pos (invEtaQ_den C hw0) (diffBound_den C k m f)
def epsN (C : NormCtx) (k m : Nat) (hw0 : 0 < C.w.num) (f : L2Test) : Nat := xBound (ofQ (epsK C k m f) (epsK_den C k m hw0 f))

/-- **The ε-estimate**: for every `j`, `|χ·readF − U_n(t)·(χ·r)| ≤ N/(j+1)` at every scale — where `x̄ ≥ λ(t)` the
    reading is exact, and where `x̄ ≤ λ(t) + 1/(j+1)` the mask is at most `(1/η)/(j+1)`. -/
theorem mask_read_le_eps (C : NormCtx) (k m : Nat) (hw0 : 0 < C.w.num) (hm : m < C.X) (f : L2Test) (x t : Real)
    (ht : InWin C t) (j : Nat) :
    Rle (Rabs (Rsub (Rmul ((maskF C k m hw0).F x t) ((readF C k m (cutAnalysis5 C k f)).F x t))
                    (Rmul (Uc C (upR m) f t) (Rmul ((maskF C k m hw0).F x t) (rOne (xcl C x))))))
        (ofQ (⟨((epsN C k m hw0 f : Nat) : Int), j + 1⟩ : Q) (Nat.succ_pos j)) := by
  refine Rle_trans (Rle_of_Req (Rabs_congr (mask_diff_alg _ _ _ _))) ?_
  rcases Rle_or_Rle (x := Rsub (xcl C x) ((lamF C k m).F x t)) (q1 := (⟨0, 1⟩ : Q)) (q2 := (⟨1, j + 1⟩ : Q))
      (by decide) (Nat.succ_pos j) (Qlt_zero_inv_succ j) with hB | hA
  · -- the mask is small
    have hmask : Rle ((maskF C k m hw0).F x t)
        (ofQ (mul (invEtaQ C) (⟨1, j + 1⟩ : Q)) (Qmul_den_pos (invEtaQ_den C hw0) (Nat.succ_pos j))) := by
      refine Rle_trans (maskF_le_ramp1 C k m hw0 x t) ?_
      refine ramp_le_of_le _ (Qmul_num_nonneg (invEtaQ_num C) (show (0 : Int) ≤ 1 by decide)) ?_
      refine Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ _ (invEtaQ_num C)) hB) ?_
      exact Rle_of_Req (Rmul_ofQ_ofQ _ _)
    refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
    refine Rle_trans (Rmul_le_Rmul_both (Rnonneg_Rabs _) (Rnonneg_ofQ _ (diffBound_num C k m f))
      (Rabs_le_of_nonneg_le _ (Qmul_num_nonneg (invEtaQ_num C) (show (0 : Int) ≤ 1 by decide)) (maskF_nonneg C k m hw0 x t) hmask)
      (diff_abs_bd C k m f x t)) ?_
    -- ((1/η)·(1/(j+1)))·K_d = K·(1/(j+1)) ≤ N·(1/(j+1)) = N/(j+1)
    refine Rle_trans (Rle_of_Req (Req_trans (Rmul_ofQ_ofQ (Qmul_den_pos (invEtaQ_den C hw0) (Nat.succ_pos j)) (diffBound_den C k m f))
      (ofQ_congr (b := mul (epsK C k m f) (⟨1, j + 1⟩ : Q)) (Qmul_den_pos (Qmul_den_pos (invEtaQ_den C hw0) (Nat.succ_pos j)) (diffBound_den C k m f))
        (Qmul_den_pos (epsK_den C k m hw0 f) (Nat.succ_pos j))
      (by simp only [Qeq, mul, epsK]; push_cast; ring_uor)))) ?_
    refine Rle_trans (Rle_of_Req (Req_symm (Rmul_ofQ_ofQ (epsK_den C k m hw0 f) (Nat.succ_pos j)))) ?_
    refine Rle_trans (Rmul_le_Rmul_right (Rnonneg_ofQ (Nat.succ_pos j) (show (0 : Int) ≤ 1 by decide))
      (Rle_of_Rabs_le (Rabs_le_ofQ_xBound (ofQ (epsK C k m f) (epsK_den C k m hw0 f))))) ?_
    refine Rle_of_Req (Req_trans (Rmul_ofQ_ofQ Nat.one_pos (Nat.succ_pos j)) (ofQ_congr _ _ ?_))
    show Qeq (mul (⟨((epsN C k m hw0 f : Nat) : Int), 1⟩ : Q) (⟨1, j + 1⟩ : Q)) (⟨((epsN C k m hw0 f : Nat) : Int), j + 1⟩ : Q)
    simp only [Qeq, mul]; push_cast; ring_uor
  · -- the reading is exact
    have hxl : Rle ((lamF C k m).F x t) (xcl C x) := Rle_of_Rnonneg_Rsub (Rnonneg_of_Rle_zero hA)
    have hR := readF_source_fiber C k m hm f x t hxl ht
    have h0 : Req (Rmul ((maskF C k m hw0).F x t)
        (Rsub ((readF C k m (cutAnalysis5 C k f)).F x t) (Rmul (Uc C (upR m) f t) (rOne (xcl C x))))) zero :=
      Req_trans (Rmul_congr (Req_refl _) (Req_trans (Rsub_congr hR (Rmul_comm _ _)) (Radd_neg _))) (Rmul_zero _)
    refine Rle_trans (Rle_of_Req (Req_trans (Rabs_congr h0) Rabs_zero)) ?_
    exact Rle_zero_of_Rnonneg (Rnonneg_ofQ (Nat.succ_pos j) (Int.ofNat_nonneg _))

/-- **★ THE MASKED READING IS `U_n(t)` TIMES THE MASKED WEIGHT, AT EVERY SCALE** (on the cut analysis, `t` in the
    Haar window): the two one-sided ε-collapses of `mask_read_le_eps`. -/
theorem mask_read_eq (C : NormCtx) (k m : Nat) (hw0 : 0 < C.w.num) (hm : m < C.X) (f : L2Test) (x t : Real) (ht : InWin C t) :
    Req (Rmul ((maskF C k m hw0).F x t) ((readF C k m (cutAnalysis5 C k f)).F x t))
        (Rmul (Uc C (upR m) f t) (Rmul ((maskF C k m hw0).F x t) (rOne (xcl C x)))) := by
  refine Rle_antisymm ?_ ?_
  · exact Rle_of_Rsub_le_eps (C := epsN C k m hw0 f) (fun j => Rle_trans (Rle_Rabs_self _) (mask_read_le_eps C k m hw0 hm f x t ht j))
  · exact Rle_of_Rsub_le_eps (C := epsN C k m hw0 f) (fun j => Rle_trans (Rle_Rabs_self _)
      (Rle_trans (Rle_of_Req (Rabs_Rsub_symm _ _)) (mask_read_le_eps C k m hw0 hm f x t ht j)))

-- ===========================================================================
-- (10) ★ THE NORMALIZED FIBER READING and its exactness.
-- ===========================================================================

/-- The numerator field `t ↦ ∫_{[1+2^{-k},B]} χ_t(x)·readF(x,t) dx`. -/
def numF (C : NormCtx) (k m : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (z : Carrier5) : CField :=
  xIntF (mulF (maskF C k m hw0) (readF C k m z)) (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk)

/-- **The Lipschitz reciprocal of the mass** `1/max(mass(t), 2η/B)` — equal to `1/mass(t)` on active rows. -/
def massInvF (C : NormCtx) (k m : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) : CField :=
  clampInv (cMass C) (cMass_num_pos C hw0) (cMass_den C) (massF C k m hw0 hk)

/-- **★ THE FIBER READING** `readFiber_m(z)(t) = (∫_J χ·readF) / (∫_J χ/max(x̄,1))`. -/
def readFiber (C : NormCtx) (k m : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (z : Carrier5) : CField :=
  mulF (massInvF C k m hw0 hk) (numF C k m hw0 hk z)

theorem readFiber_F (C : NormCtx) (k m : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (z : Carrier5) (x t : Real) :
    (readFiber C k m hw0 hk z).F x t = Rmul ((massInvF C k m hw0 hk).F x t) ((numF C k m hw0 hk z).F x t) := rfl

/-- The numerator on the analysis is `U_n(t)·mass(t)`. -/
theorem numF_F (C : NormCtx) (k m : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (z : Carrier5) (x t : Real) :
    (numF C k m hw0 hk z).F x t
      = xInt (mulF (maskF C k m hw0) (readF C k m z)) (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk) t := rfl

theorem numF_source (C : NormCtx) (k m : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (hm : m < C.X) (f : L2Test) (x t : Real)
    (ht : InWin C t) :
    Req ((numF C k m hw0 hk (cutAnalysis5 C k f)).F x t) (Rmul (Uc C (upR m) f t) ((massF C k m hw0 hk).F x t)) := by
  rw [numF_F, massF_F]
  exact xInt_congr_smul _ _ (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk) _ t t
    (fun s _ _ => mask_read_eq C k m hw0 hm f _ t ht)

/-- The reciprocal of the mass is exact on active rows. -/
theorem massInvF_mul (C : NormCtx) (k m : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (hm : m < C.X) (hm1 : 1 ≤ m) (x t : Real)
    (ht : InWin C t) :
    Req (Rmul ((massF C k m hw0 hk).F x t) ((massInvF C k m hw0 hk).F x t)) one := by
  have hge := massF_ge C k m hw0 hk hm hm1 x t ht
  have hwit := Rlt_Qbound_of_Rle_ofQ (cMass_num_pos C hw0) (cMass_den C) hge
  show Req (Rmul _ (clampedInv (cMass C) (cMass_num_pos C hw0) (cMass_den C) _)) one
  exact Req_trans (Rmul_congr (Req_refl _) (clampedInv_eq_of_ge (han := cMass_num_pos C hw0) hwit hge)) (Rmul_Rinv_self hwit)

/-- **★ THE FIBER READING IS `U_n(f,t)` EXACTLY** on every cut analysis, at every active row (`1 ≤ m < X`, `w > 0`,
    `k ≥ 1`, `t ∈ [a, a+w]`): a genuine normalized `dx/x` integral over the measured fiber `J_{k,n,t}`. -/
theorem readFiber_source (C : NormCtx) (k m : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (hm : m < C.X) (hm1 : 1 ≤ m) (f : L2Test)
    (x t : Real) (ht : InWin C t) :
    Req ((readFiber C k m hw0 hk (cutAnalysis5 C k f)).F x t) (Uc C (upR m) f t) := by
  rw [readFiber_F]
  refine Req_trans (Rmul_congr (Req_refl _) (numF_source C k m hw0 hk hm f x t ht)) ?_
  refine Req_trans (Rmul_congr (Req_refl _) (Rmul_comm _ _)) (Req_trans (Req_symm (Rmul_assoc _ _ _)) ?_)
  exact Req_trans (Rmul_congr (Req_trans (Rmul_comm _ _) (massInvF_mul C k m hw0 hk hm hm1 x t ht)) (Req_refl _)) (Rone_mul _)

end UOR.Bridge.F1Square.Square
