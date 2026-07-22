/-
F1 square — **the pre-Hilbert layer, brick 19** (`WindowPower.lean`): **the window power
substrate of the Mellin twist** — the band-clamped identity on each half-line window and its
iterated powers, as members of the test algebra.

The Mellin transform's `t^n` twist grows on the half-line, so it cannot be a single global
bounded-Lipschitz test; but on each window `[m+1, m+2]` it is one. This brick builds exactly
that:

- `bandTest m` — the identity clamped to `[m+1, m+2]` (the `qBandQ` band): a genuine `L2Test`
  (1-Lipschitz, bounded by `m+2`), INERT on its window (`bandTest_inert`: `≈ t` there).
- `powWinTest m n` — its `n`-th power by iterated `L2Test.mul`: certificates compose
  automatically through the algebra, and `powWinTest_succ_inert` shows it is `tⁿ` on the
  window (recursively `≈ (previous)·t`, base `≡ 1`). (The exact `(m+2)ⁿ` value of the
  accumulated bound field is banked for the tail brick that consumes it.)

WHY (the Sonine route, step 3). The twisted integrand of the transform at the integer point
`n` is, on window `m`, the product `φ · powWinTest m n` — a member of the test algebra with
automatic certificates, agreeing with `φ(t)·tⁿ` on the window. The twisted tail (summing these
window integrals under exponent-strengthened decay) is the banked next brick; this one is its
substrate.

HONEST SCOPE. Per-window clamped powers and their inertness; no transform, no tail, no pair.
The crux fields stay `none`.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Square.TestAlgebra

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

/-- `m+1 ≤ m+2` as rationals. -/
private theorem qle_window (m : Nat) : Qle (⟨(m : Int) + 1, 1⟩ : Q) (⟨(m : Int) + 2, 1⟩ : Q) := by
  show ((m : Int) + 1) * 1 ≤ ((m : Int) + 2) * 1
  omega

/-- **The band-clamped identity on `[m+1, m+2]`** — the window copy of the identity as a
    genuine test: 1-Lipschitz, bounded by `m+2`, inert on the window. -/
def bandTest (m : Nat) : L2Test where
  f := qBandQ (⟨(m : Int) + 1, 1⟩ : Q) (⟨(m : Int) + 2, 1⟩ : Q) Nat.one_pos Nat.one_pos
  L := ⟨1, 1⟩
  M := ⟨(m : Int) + 2, 1⟩
  hLd := by decide
  hLn := by decide
  hMd := Nat.one_pos
  hMn := by show (0 : Int) ≤ (m : Int) + 2; omega
  hlip := fun x y =>
    Rle_trans (qBandQ_lipschitz (⟨(m : Int) + 1, 1⟩ : Q) (⟨(m : Int) + 2, 1⟩ : Q)
      Nat.one_pos Nat.one_pos x y)
      (Rle_of_Req (Req_symm (Req_trans (Rmul_comm _ _) (Rmul_one (Rabs (Rsub x y))))))
  hfc := fun _ _ h => qBandQ_congr _ _ Nat.one_pos Nat.one_pos h
  hbd := fun x => by
    have hnn : Rnonneg (qBandQ (⟨(m : Int) + 1, 1⟩ : Q) (⟨(m : Int) + 2, 1⟩ : Q)
        Nat.one_pos Nat.one_pos x) := by
      intro n
      refine Qle_trans Nat.one_pos ?_ (qBandQ_ge (⟨(m : Int) + 1, 1⟩ : Q)
        (⟨(m : Int) + 2, 1⟩ : Q) Nat.one_pos Nat.one_pos (qle_window m) x n)
      show Qle (neg (Qbound n)) (⟨(m : Int) + 1, 1⟩ : Q)
      simp only [Qle, neg, Qbound]; push_cast
      have hp : (0 : Int) ≤ ((m : Int) + 1) * ((n : Int) + 1) :=
        Int.mul_nonneg (by omega) (by omega)
      omega
    have hle : Rle (qBandQ (⟨(m : Int) + 1, 1⟩ : Q) (⟨(m : Int) + 2, 1⟩ : Q)
        Nat.one_pos Nat.one_pos x) (ofQ (⟨(m : Int) + 2, 1⟩ : Q) Nat.one_pos) := by
      intro n
      refine Qle_trans Nat.one_pos (qBandQ_le (⟨(m : Int) + 1, 1⟩ : Q)
        (⟨(m : Int) + 2, 1⟩ : Q) Nat.one_pos Nat.one_pos x n) ?_
      show Qle (⟨(m : Int) + 2, 1⟩ : Q) (add (⟨(m : Int) + 2, 1⟩ : Q) (⟨2, n + 1⟩ : Q))
      simp only [Qle, add]; push_cast
      rw [Int.one_mul]
      omega
    exact Rle_trans (Rle_of_Req (Rabs_of_nonneg hnn)) hle

/-- **The band is inert on its window**: `bandTest m ≈ t` for `m+1 ≤ t ≤ m+2`. -/
theorem bandTest_inert (m : Nat) {x : Real}
    (hlo : Rle (ofQ (⟨(m : Int) + 1, 1⟩ : Q) Nat.one_pos) x)
    (hhi : Rle x (ofQ (⟨(m : Int) + 2, 1⟩ : Q) Nat.one_pos)) :
    Req ((bandTest m).f x) x :=
  qBandQ_eq_of_band hlo hhi

/-- **The window power** `tⁿ` on `[m+1, m+2]` — iterated product in the test algebra:
    certificates compose automatically. -/
def powWinTest (m : Nat) : Nat → L2Test
  | 0 => oneTest
  | n + 1 => L2Test.mul (powWinTest m n) (bandTest m)

/-- The zeroth window power is the constant `1` (definitional). -/
theorem powWinTest_zero (m : Nat) (x : Real) : (powWinTest m 0).f x = one := rfl

/-- **The window power is inert on its window, recursively**: for `m+1 ≤ t ≤ m+2`,
    `(powWinTest m (n+1)) t ≈ (powWinTest m n) t · t` — with the base `≡ 1`, the window power
    IS `tⁿ` on the window. -/
theorem powWinTest_succ_inert (m n : Nat) {x : Real}
    (hlo : Rle (ofQ (⟨(m : Int) + 1, 1⟩ : Q) Nat.one_pos) x)
    (hhi : Rle x (ofQ (⟨(m : Int) + 2, 1⟩ : Q) Nat.one_pos)) :
    Req ((powWinTest m (n + 1)).f x) (Rmul ((powWinTest m n).f x) x) :=
  Rmul_congr (Req_refl _) (bandTest_inert m hlo hhi)

end UOR.Bridge.F1Square.Square
