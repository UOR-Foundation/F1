/-
F1 square — **positive scalings, the window change of variables, and the dilation representation**
(`AtlasOrbitHaar.lean`).  Independent of F1: no test context, no form.

  * `OrbitArrow` — raw scaling arrows `t ⟶ λ·t` with composition; associativity, units and inverses hold
    up to `Qeq` (`arrow_*`).  This is NOT yet a typed Lean groupoid (no quotient of arrows, no categorical
    interface); it is the raw data such a groupoid would be built on.
  * `HaarWindow` — a window `[lo, lo+w]` with a floor `a ≤ lo`, on which the repository's certified Haar
    integral `∫ φ(t) dt/max(t,a)` is exactly `∫ φ(t) dt/t`; `scaleWindow s W = [s·lo, s·(lo+w)]`.
  * `haar_invariance` — the certified WINDOW change-of-variables theorem `∫_{s·W} φ dt/t = ∫_W φ(s·) dt/t`
    (the repository's `haarIntegral_dilate` restated).  It is not a groupoid Haar-system object and no
    uniqueness of the Haar system is proved.
  * `regRep s φ = φ(s·)` (`dilateTest`), with `regRep_comp`, `regRep_one` pointwise; `regRep_unitary` and
    `regRep_adjoint` compare the carrier on `W` with the carrier on `s·W` — they are change-of-variables
    identities between two windows, NOT a unitary endomorphism of one completed Hilbert carrier.

Nothing here is a kernel, a coefficient, or a sign.  Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasOrbitAddress
import F1Square.Square.HaarInvariant
import F1Square.Square.WeilPrimeShiftRecipAutocorr

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- (1) The action groupoid of positive scalings.
-- ===========================================================================

/-- An arrow of the action groupoid: `src ⟶ scale·src`. -/
structure OrbitArrow where
  src : PosRat
  scale : PosRat

def PosRat.pmul (a b : PosRat) : PosRat := ⟨UOR.Bridge.F1Square.Analysis.mul a.q b.q, Qmul_num_pos a.hn b.hn, Qmul_den_pos a.hd b.hd⟩
def PosRat.pone : PosRat := ⟨⟨1, 1⟩, by decide, by decide⟩
def PosRat.pinv (a : PosRat) : PosRat := ⟨Qinv a.q, Qinv_num_pos a.hd, Qinv_den_pos a.hn⟩

/-- The target of an arrow. -/
def OrbitArrow.tgt (f : OrbitArrow) : PosRat := f.scale.pmul f.src

/-- Composition `g ∘ f` of composable arrows (`g.src ≈ f.tgt`): scalings multiply. -/
def OrbitArrow.comp (f g : OrbitArrow) : OrbitArrow := ⟨f.src, g.scale.pmul f.scale⟩

theorem arrow_comp_tgt (f g : OrbitArrow) (h : Qeq g.src.q f.tgt.q) : Qeq (f.comp g).tgt.q g.tgt.q := by
  show Qeq (mul (mul g.scale.q f.scale.q) f.src.q) (mul g.scale.q g.src.q)
  exact Qeq_trans (Qmul_den_pos g.scale.hd (Qmul_den_pos f.scale.hd f.src.hd)) (Qmul_assoc _ _ _)
    (Qmul_congr (Qeq_refl _) (Qeq_symm h))

theorem arrow_comp_assoc (f g h : OrbitArrow) : Qeq ((f.comp g).comp h).scale.q (f.comp (g.comp h)).scale.q := by
  show Qeq (mul h.scale.q (mul g.scale.q f.scale.q)) (mul (mul h.scale.q g.scale.q) f.scale.q)
  exact Qeq_symm (Qmul_assoc _ _ _)

theorem arrow_id_left (f : OrbitArrow) : Qeq (f.comp ⟨f.tgt, PosRat.pone⟩).scale.q f.scale.q := Qone_mul _
theorem arrow_id_right (f : OrbitArrow) : Qeq ((⟨f.src, PosRat.pone⟩ : OrbitArrow).comp f).scale.q f.scale.q := by
  show Qeq (mul f.scale.q ⟨1, 1⟩) f.scale.q
  exact Qeq_trans (Qmul_den_pos (by decide) f.scale.hd) (Qmul_comm _ _) (Qone_mul _)
theorem arrow_inv (f : OrbitArrow) : Qeq (f.comp ⟨f.tgt, f.scale.pinv⟩).scale.q PosRat.pone.q :=
  Qinv_mul f.scale.hd f.scale.hn

-- ===========================================================================
-- (2) Haar windows and the invariant Haar system.
-- ===========================================================================

/-- A Haar window `[lo, lo+w]` with floor `a ≤ lo` (so `1/max(t,a) = 1/t` on the window). -/
structure HaarWindow where
  a : Q
  han : 0 < a.num
  had : 0 < a.den
  lo : Q
  hlo : 0 < lo.den
  w : Q
  hw : 0 < w.den
  hwn : 0 ≤ w.num
  hfloor : Rle (ofQ a had) (ofQ lo hlo)

/-- The Haar integral of a test over a window. -/
def HaarWindow.integral (W : HaarWindow) (φ : L2Test) : Real :=
  haarIntegral φ W.a W.han W.had W.lo W.w W.hlo W.hw W.hwn

/-- The scaled window `s·W = [s·lo, s·(lo+w)]` with floor `s·a`. -/
def scaleWindow (s : PosRat) (W : HaarWindow) : HaarWindow where
  a := mul s.q W.a
  han := Qmul_num_pos s.hn W.han
  had := Qmul_den_pos s.hd W.had
  lo := mul s.q W.lo
  hlo := Qmul_den_pos s.hd W.hlo
  w := mul s.q W.w
  hw := Qmul_den_pos s.hd W.hw
  hwn := Int.mul_nonneg (Int.le_of_lt s.hn) W.hwn
  hfloor := by
    refine Rle_trans (Rle_of_Req (Req_symm (Rmul_ofQ_ofQ s.hd W.had))) ?_
    refine Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ s.hd (Int.le_of_lt s.hn)) W.hfloor) ?_
    exact Rle_of_Req (Rmul_ofQ_ofQ s.hd W.hlo)

/-- **The window change of variables**: `∫_{s·W} φ dt/t = ∫_W φ(s·t) dt/t` (`haarIntegral_dilate` on windows). -/
theorem haar_invariance (s : PosRat) (W : HaarWindow) (φ : L2Test) :
    Req ((scaleWindow s W).integral φ) (W.integral (dilateTest s.q s.hn s.hd φ)) :=
  haarIntegral_dilate φ s.q s.hn s.hd W.a (mul s.q W.a) W.han W.had (Qmul_num_pos s.hn W.han) (Qmul_den_pos s.hd W.had)
    W.lo W.w W.hlo W.hw W.hwn W.hfloor (scaleWindow s W).hfloor

-- ===========================================================================
-- (3) The regular representation: composition, unitarity, adjoint — by change of variables.
-- ===========================================================================

/-- **The regular representation** `(R_s φ)(t) = φ(s·t)`. -/
def regRep (s : PosRat) (φ : L2Test) : L2Test := dilateTest s.q s.hn s.hd φ

theorem regRep_comp (s s' : PosRat) (φ : L2Test) (t : Real) :
    Req ((regRep s (regRep s' φ)).f t) ((regRep (s.pmul s') φ).f t) :=
  dilateTest_comp s.q s'.q s.hn s.hd s'.hn s'.hd φ t
theorem regRep_one (φ : L2Test) (t : Real) : Req ((regRep PosRat.pone φ).f t) (φ.f t) := dilateTest_one φ t

/-- The Haar inner product on a window: `⟨φ, ψ⟩_W = ∫_W φ·ψ dt/t`. -/
def HaarWindow.inner (W : HaarWindow) (φ ψ : L2Test) : Real := W.integral (productTest φ ψ)

/-- **Isometry between the two windows** (change of variables, not a field): `⟨R_s φ, R_s ψ⟩_W = ⟨φ, ψ⟩_{s·W}`. -/
theorem regRep_unitary (s : PosRat) (W : HaarWindow) (φ ψ : L2Test) :
    Req (W.inner (regRep s φ) (regRep s ψ)) ((scaleWindow s W).inner φ ψ) := by
  refine Req_symm (Req_trans (haar_invariance s W (productTest φ ψ)) ?_)
  -- (dilateTest s (φ·ψ))(t)·r = ((dilateTest s φ)·(dilateTest s ψ))(t)·r pointwise
  exact haarIntegral_congr_window _ _ W.a W.a W.han W.had W.han W.had W.lo W.w W.hlo W.hw W.hwn
    (fun _ _ _ => Req_refl _)

/-- `(1/s)·(s·t) ≈ t`. -/
theorem inv_scale_cancel (s : PosRat) (t : Real) :
    Req (Rmul (ofQ (Qinv s.q) (Qinv_den_pos s.hn)) (Rmul (ofQ s.q s.hd) t)) t := by
  refine Req_trans (Req_symm (Rmul_assoc _ _ _)) ?_
  refine Req_trans (Rmul_congr (Req_trans (Rmul_ofQ_ofQ (Qinv_den_pos s.hn) s.hd)
    (ofQ_congr (Qmul_den_pos (Qinv_den_pos s.hn) s.hd) Nat.one_pos (Qinv_mul s.hd s.hn))) (Req_refl t)) ?_
  exact Rone_mul t

/-- **The adjoint identity between the two windows** (change of variables, not a field): `⟨R_s φ, ψ⟩_W = ⟨φ, R_{1/s} ψ⟩_{s·W}`. -/
theorem regRep_adjoint (s : PosRat) (W : HaarWindow) (φ ψ : L2Test) :
    Req (W.inner (regRep s φ) ψ) ((scaleWindow s W).inner φ (regRep s.pinv ψ)) := by
  refine Req_symm (Req_trans (haar_invariance s W (productTest φ (regRep s.pinv ψ))) ?_)
  refine haarIntegral_congr_window _ _ W.a W.a W.han W.had W.han W.had W.lo W.w W.hlo W.hw W.hwn (fun x _ _ => ?_)
  -- φ(s·t)·ψ((1/s)·(s·t))·r ≈ φ(s·t)·ψ(t)·r
  refine Rmul_congr (Rmul_congr (Req_refl _) (ψ.hfc _ _ (inv_scale_cancel s _))) (Req_refl _)

end UOR.Bridge.F1Square.Square
