/-
F1 square — **the canonical prime-power decomposition and the bounded prime fold** (`AtlasPrimePowerFold.lean`).

  * `ppExp n` — the exponent `e` with `n = (spf n)^e` for a prime power `n` (`ppExp_spec`), computed by
    stripping the smallest prime factor; the decomposition `n ↦ (spf n, ppExp n)` is canonical.
  * `vonMangoldt_prime_pow_addr` — `Λ(n) = log (spf n)` on every prime-power address (definitional).
  * `primeFoldDirect_vanish` — the folded prime channel vanishes at every scale `n = m+1` that is NOT a
    prime power (`Λ(n) = 0`): the bounded prime fold `Σ_{m<X}` is supported on the prime-power addresses
    `n ≤ X` alone (`primeFoldGram_eq_pp`: the sum is unchanged when non-prime-power terms are dropped).

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasOrbitDecode

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

/-- Strip factors of `p` from `n`, counting them (fuel-bounded). -/
def ppExpFrom (n p fuel : Nat) : Nat :=
  match fuel with
  | 0 => 0
  | fuel + 1 => if n = 1 then 0 else if n % p = 0 then ppExpFrom (n / p) p fuel + 1 else 0

/-- **The canonical exponent** of a prime power `n = (spf n)^e`. -/
def ppExp (n : Nat) : Nat := ppExpFrom n (spf n) n

/-- `isPow n p fuel = true` ⟹ `n = p ^ ppExpFrom n p fuel` (for `2 ≤ p`). -/
theorem isPow_spec (p : Nat) (hp : 2 ≤ p) : ∀ fuel n, isPow n p fuel = true → n = p ^ ppExpFrom n p fuel
  | 0, n, h => by
      unfold isPow at h; unfold ppExpFrom
      have : n = 1 := of_decide_eq_true h
      simp [this]
  | fuel + 1, n, h => by
      unfold isPow at h; unfold ppExpFrom
      by_cases h1 : n = 1
      · simp [h1]
      · rw [if_neg h1] at h ⊢
        by_cases hm : n % p = 0
        · rw [if_pos hm] at h ⊢
          have ih := isPow_spec p hp fuel (n / p) h
          have hdiv : p * (n / p) = n := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hm)
          rw [Nat.pow_succ, Nat.mul_comm, ← ih, hdiv]
        · rw [if_neg hm] at h; simp at h

/-- **`n = (spf n)^(ppExp n)`** for every prime power. -/
theorem ppExp_spec (n : PrimePowerAddr) : n.1 = (spf n.1) ^ ppExp n.1 := by
  have h := n.2
  unfold isPrimePow at h
  rw [Bool.and_eq_true] at h
  exact isPow_spec (spf n.1) (spf_two_le (primePowerAddr_two_le n)) n.1 n.1 h.2

/-- `Λ(n) = log (spf n)` on a prime-power address (definitional). -/
theorem vonMangoldt_prime_pow_addr (n : PrimePowerAddr) :
    vonMangoldt n.1 = logN (spf n.1) (one_le_spf n.1 (by have := primePowerAddr_two_le n; omega)) := by
  unfold vonMangoldt
  rw [dif_pos n.2]

/-- `Λ(n) = 0` when `n` is not a prime power (definitional). -/
theorem vonMangoldt_not_pp {n : Nat} (h : ¬ isPrimePow n = true) : vonMangoldt n = zero := by
  unfold vonMangoldt
  rw [dif_neg h]

/-- **The folded prime channel vanishes off the prime powers**: `primeFoldDirect_m = 0` when `m+1` is not a
    prime power. -/
theorem primeFoldDirect_vanish (C : NormCtx) (m : Nat) (h : ¬ isPrimePow (m + 1) = true) (f g : L2Test) :
    Req (primeFoldDirect C m f g) zero := by
  refine Req_trans (primeFoldDirect_eq C m f g) ?_
  rw [vonMangoldt_not_pp h]
  refine Req_trans (Rneg_congr (Req_trans (Rmul_congr (Req_trans (Rmul_comm _ _) (Rmul_zero _)) (Req_refl _))
    (Req_trans (Rmul_comm _ _) (Rmul_zero _)))) ?_
  exact Rneg_zero

/-- The prime-power–supported fold: the same sum with non-prime-power terms replaced by `0`. -/
def primeFoldGramPP (C : NormCtx) (f g : L2Test) : Real :=
  RsumN (fun m => if isPrimePow (m + 1) = true then primeFoldDirect C m f g else zero) C.X

/-- **★ THE BOUNDED PRIME FOLD IS SUPPORTED ON THE PRIME-POWER ADDRESSES**: `primeFoldGram = primeFoldGramPP`. -/
theorem primeFoldGram_eq_pp (C : NormCtx) (f g : L2Test) : Req (primeFoldGram C f g) (primeFoldGramPP C f g) := by
  unfold primeFoldGram primeFoldGramPP
  refine RsumN_congr C.X (fun m _ => ?_)
  by_cases h : isPrimePow (m + 1) = true
  · rw [if_pos h]; exact Req_refl _
  · rw [if_neg h]; exact primeFoldDirect_vanish C m h f g

end UOR.Bridge.F1Square.Square
