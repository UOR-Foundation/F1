/-
F1 square — **the neutral lower core of a context** (`WeilGeom.lean`):

  * the canonical band `canonB = X+1`, `canonC = 1/(X+1)` and their rational laws (`c·B = 1`,
    `c ≤ 1 ≤ B`, `B ≤ S`, `c ≤ b·a`) — previously in `WeilRecipCanon`;
  * the canonical closed geometry `NormCtx.geom` (`Bd := B := N := X+1`, `hband := hband_hi`,
    `hBdS := hTS`) and `normCtx_core` — previously in `ClosedWeilBilin`;
  * the fixed core `ClosedCore C = {f // CoreTest C.geom f}`.

This module imports only the source layer below the closed Weil form (`WeilArchNear` and its cone):
`closedWeilBilin`, `CoupledForm`, `ArchTailForm`, `PoleForm`'s identification and the dominance
predicate are NOT reachable from here.  Every construction that must be transitively independent of
the target forms (the Atlas scale field, fibers, carriers and the source Gram) imports this file.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.WeilArchNear

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- (1) The canonical band from `NormCtx`: `B = X+1`, `c = 1/B`, `c·B = 1`, `c ≤ b·a`.
-- ===========================================================================

/-- `1 ≤ q ⟹ 1/q ≤ 1`. -/
theorem qinv_le_one {q : Q} (hqd : 0 < q.den) (hq1 : Qle (⟨1, 1⟩ : Q) q) :
    Qle (Qinv q) (⟨1, 1⟩ : Q) := by
  have hqn : 0 < q.num := qnum_pos_of_one_le hqd hq1
  have hqq := hq1
  simp only [Qle] at hqq
  show (q.den : Int) * ((1 : Nat) : Int) ≤ 1 * ((q.num.toNat : Nat) : Int)
  push_cast [Int.toNat_of_nonneg (Int.le_of_lt hqn)] at hqq ⊢
  omega


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
-- (2) The closed geometry, derived CANONICALLY from a `NormCtx` (no extra data).
-- ===========================================================================


/-- **The canonical closed geometry of a `NormCtx`** — every field derives from the context:
    `Bd := X+1` (the support bound), `B := X+1` (the weight band cap), `N := X+1` (the scale witness),
    `hband := hband_hi`, `hBdS := hTS`.  NO arbitrary geometry. -/
def NormCtx.geom (C : NormCtx) : ClosedGeom where
  S := C.S
  hSd := C.hSd
  hSn := C.hSn
  hS1 := C.hS1
  a := C.a
  han := C.han
  had := C.had
  w := C.w
  hw := C.hw
  hwn := C.hwn
  b := C.b
  hbd := C.hbd
  hbn := C.hbnpos
  hfit := C.hfit
  B := ⟨((C.X + 1 : Nat) : Int), 1⟩
  hBd := Nat.one_pos
  hB1 := by
    show (1 : Int) * ((1 : Nat) : Int) ≤ ((C.X + 1 : Nat) : Int) * ((1 : Nat) : Int)
    push_cast
    omega
  N := C.X + 1
  hN := Nat.succ_pos C.X
  hBN := Qle_refl _
  Bd := ⟨((C.X + 1 : Nat) : Int), 1⟩
  hBdd := Nat.one_pos
  hBd1 := by
    show (1 : Int) * ((1 : Nat) : Int) ≤ ((C.X + 1 : Nat) : Int) * ((1 : Nat) : Int)
    push_cast
    omega
  hband := C.hband_hi
  hBdS := C.hTS
  hBdB := Qle_refl _

/-- The context's own test is a core test for its canonical geometry (from `NormCtx.hgh/hgl` —
    the test domain is exactly the context's support data, never vacuous by fiat). -/
theorem normCtx_core (C : NormCtx) : CoreTest C.geom C.g where
  hgh := C.hgh
  hgl := C.hgl

-- ===========================================================================
-- (3) The fixed core.
-- ===========================================================================

/-- **The fixed core**: tests with the context's support certificates. -/
def ClosedCore (C : NormCtx) := { f : L2Test // CoreTest C.geom f }

end UOR.Bridge.F1Square.Square
