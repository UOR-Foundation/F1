/-
F1 square — **binomial coefficients and the factorial identity from scratch** (Lean core here has no
`Nat.choose` / `Nat.factorial` / `Nat.add_pow`). This is the foundational first piece of the v0.15.0
keystone: the exponential/trigonometric functional equation via the Cauchy product needs the binomial
identity `Σ_{i+j=k} (xⁱ/i!)(yʲ/j!) = (x+y)ᵏ/k!`, whose heart is `C(k,i)·i!·(k−i)! = k!`.

This module builds `choose` (Pascal's recurrence) and that factorial identity (the ℤ ring algebra is
discharged by `ring_uor`, the project's from-scratch `ring`). Pure Lean 4, no Mathlib, no `sorry`.
-/

import F1Square.Analysis.Exp

namespace UOR.Bridge.F1Square.Analysis

/-- Binomial coefficients via Pascal's recurrence. -/
def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, (_ + 1) => 0
  | (n + 1), (k + 1) => choose n k + choose n (k + 1)

@[simp] theorem choose_zero_right (n : Nat) : choose n 0 = 1 := by cases n <;> rfl
@[simp] theorem choose_zero_succ (k : Nat) : choose 0 (k + 1) = 0 := rfl
theorem choose_succ_succ (n k : Nat) : choose (n + 1) (k + 1) = choose n k + choose n (k + 1) := rfl

/-- `C(n,k) = 0` when `k > n`. -/
theorem choose_eq_zero_of_lt : ∀ {n k : Nat}, n < k → choose n k = 0
  | 0, 0, h => absurd h (by omega)
  | 0, (_ + 1), _ => rfl
  | (_ + 1), 0, h => absurd h (by omega)
  | (n + 1), (k + 1), h => by
      rw [choose_succ_succ, choose_eq_zero_of_lt (by omega : n < k),
        choose_eq_zero_of_lt (by omega : n < k + 1)]

/-- `C(n,n) = 1`. -/
theorem choose_self : ∀ n, choose n n = 1
  | 0 => rfl
  | (n + 1) => by
      rw [choose_succ_succ, choose_self n, choose_eq_zero_of_lt (Nat.lt_succ_self n)]

/-- **The factorial identity** `C(n,k)·k!·(n−k)! = n!` for `k ≤ n` — the divisibility heart of the
    binomial theorem. -/
theorem choose_mul_fct_mul_fct : ∀ {n k : Nat}, k ≤ n →
    choose n k * fct k * fct (n - k) = fct n
  | _, 0, _ => by simp [fct]
  | 0, (_ + 1), h => absurd h (by omega)
  | (n + 1), (k + 1), h => by
      rcases Nat.eq_or_lt_of_le (Nat.le_of_succ_le_succ h) with hkn | hkn
      · -- k = n : the corner term
        subst hkn
        rw [Nat.sub_self, choose_self]; simp [fct]
      · -- k < n : Pascal step (ℤ ring algebra via ring_uor)
        have ih1 := choose_mul_fct_mul_fct (Nat.le_of_lt hkn)
        have ih2 := choose_mul_fct_mul_fct hkn
        have hsub : n + 1 - (k + 1) = n - k := by omega
        -- cast the facts to ℤ, keeping each Nat subterm as an opaque atom
        have ih1Z : (↑(choose n k) : Int) * ↑(fct k) * ↑(fct (n - k)) = ↑(fct n) := by
          exact_mod_cast ih1
        have ih2Z : (↑(choose n (k + 1)) : Int) * ↑(fct (k + 1)) * ↑(fct (n - (k + 1))) = ↑(fct n) := by
          exact_mod_cast ih2
        have hFk1 : (↑(fct (k + 1)) : Int) = ↑(k + 1) * ↑(fct k) := by exact_mod_cast fct_succ k
        have hFnk_nat : fct (n - k) = (n - k) * fct (n - (k + 1)) := by
          rw [show n - k = (n - (k + 1)) + 1 from by omega, fct_succ]
        have hFnk : (↑(fct (n - k)) : Int) = ↑(n - k) * ↑(fct (n - (k + 1))) := by
          exact_mod_cast hFnk_nat
        have hFn1 : (↑(fct (n + 1)) : Int) = ↑(n + 1) * ↑(fct n) := by exact_mod_cast fct_succ n
        have hk1 : (↑(k + 1) : Int) + ↑(n - k) = ↑(n + 1) := by
          exact_mod_cast (show (k + 1) + (n - k) = n + 1 from by omega)
        have hterm1 : (↑(choose n k) : Int) * ↑(fct (k + 1)) * ↑(fct (n - k)) = ↑(k + 1) * ↑(fct n) := by
          rw [hFk1, ← ih1Z]; ring_uor
        have hterm2 : (↑(choose n (k + 1)) : Int) * ↑(fct (k + 1)) * ↑(fct (n - k))
            = ↑(n - k) * ↑(fct n) := by
          rw [hFnk, ← ih2Z]; ring_uor
        have keyZ : ((↑(choose n k) : Int) + ↑(choose n (k + 1))) * ↑(fct (k + 1)) * ↑(fct (n - k))
            = ↑(fct (n + 1)) :=
          calc ((↑(choose n k) : Int) + ↑(choose n (k + 1))) * ↑(fct (k + 1)) * ↑(fct (n - k))
              = (↑(choose n k) : Int) * ↑(fct (k + 1)) * ↑(fct (n - k))
                + ↑(choose n (k + 1)) * ↑(fct (k + 1)) * ↑(fct (n - k)) := by ring_uor
            _ = ↑(k + 1) * ↑(fct n) + ↑(n - k) * ↑(fct n) := by rw [hterm1, hterm2]
            _ = (↑(k + 1) + ↑(n - k)) * ↑(fct n) := by ring_uor
            _ = ↑(n + 1) * ↑(fct n) := by rw [hk1]
            _ = ↑(fct (n + 1)) := by rw [← hFn1]
        rw [hsub, choose_succ_succ]
        exact_mod_cast keyZ

end UOR.Bridge.F1Square.Analysis
