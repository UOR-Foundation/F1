/-
F1 square — the **Euler–Mascheroni constant** `γ₀` as a genuine constructive real, via the
alternating series

  γ = Σ_{k≥2} (−1)ᵏ ζ(k)/k     (reindex i = k−2:  γ = Σ_{i≥0} (−1)ⁱ · ζ(i+2)/(i+2)).

The terms `b(i) = ζ(i+2)/(i+2)` are positive and **antitone** (both `ζ(s)` decreasing in `s` and the
`1/(i+2)` factor decreasing), so this is a textbook alternating series. We mechanize the alternating
bracket from scratch over `Q`:

  `AltSum b (L+1) = b 0 − AltSum (shift b) L`

— the "Leibniz" recursion that makes both the enclosure `0 ≤ AltSum b L ≤ b 0` and the gap bound
`|AltSum b (L+m) − AltSum b L| ≤ b L` provable by a single induction (no parity case-split). γ₀ is then
a custom single rational diagonal `gammaSeq j`, exactly as `Rpi`: a finite double sum of the rational
ζ-approximants whose truncation (in the number of terms) and approximation (in the ζ-depth) errors are
each driven below the Bishop modulus `1/(j+1)`.

Pure Lean 4, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Analysis.Zeta
import F1Square.Analysis.Complete
import F1Square.Analysis.Pi

namespace UOR.Bridge.F1Square.Analysis

/-! ### The alternating (Leibniz) partial sum over `Q` -/

/-- The alternating partial sum `Σ_{i=0}^{L-1} (−1)ⁱ b i`, via the Leibniz recursion
    `AltSum b (L+1) = b 0 − AltSum (b∘succ) L`. -/
def AltSum (b : Nat → Q) : Nat → Q
  | 0 => ⟨0, 1⟩
  | (L + 1) => Qsub (b 0) (AltSum (fun i => b (i + 1)) L)

theorem AltSum_succ (b : Nat → Q) (L : Nat) :
    AltSum b (L + 1) = Qsub (b 0) (AltSum (fun i => b (i + 1)) L) := rfl

/-- `0 ≤ a − c` when `c ≤ a`. -/
theorem Qsub_nonneg_of_le {a c : Q} (h : Qle c a) : Qle (⟨0, 1⟩ : Q) (Qsub a c) := by
  show (0 : Int) * ((add a (neg c)).den : Int) ≤ (add a (neg c)).num * 1
  simp only [add, neg]
  have h' : c.num * (a.den : Int) ≤ a.num * (c.den : Int) := h
  push_cast
  rw [Int.neg_mul]
  generalize a.num * (c.den : Int) = X at h' ⊢
  generalize c.num * (a.den : Int) = Y at h' ⊢
  omega

/-- `0 ≤ q` (as `Qle ⟨0,1⟩ q`) from `0 ≤ q.num`. -/
theorem Qzero_le {q : Q} (h : 0 ≤ q.num) : Qle (⟨0, 1⟩ : Q) q := by
  show (0 : Int) * (q.den : Int) ≤ q.num * 1; omega

/-- `0 ≤ q.num` from `0 ≤ q` (as `Qle ⟨0,1⟩ q`). -/
theorem num_nonneg_of_Qzero_le {q : Q} (h : Qle (⟨0, 1⟩ : Q) q) : 0 ≤ q.num := by
  have h' : (0 : Int) * (q.den : Int) ≤ q.num * 1 := h; omega

/-- `a − 0 ≈ a`. -/
theorem Qsub_zero_eq (a : Q) : Qeq (Qsub a (⟨0, 1⟩ : Q)) a := by
  simp only [Qeq, Qsub, add, neg]; push_cast; ring_uor

/-- The Leibniz partial sum has positive denominator (its terms do). -/
theorem AltSum_den_pos (b : Nat → Q) (hden : ∀ i, 0 < (b i).den) :
    ∀ L, 0 < (AltSum b L).den
  | 0 => Nat.one_pos
  | (L + 1) => by
      rw [AltSum_succ]
      exact Qsub_den_pos (hden 0)
        (AltSum_den_pos (fun i => b (i + 1)) (fun i => hden (i + 1)) L)

/-! ### The alternating bracket and gap bound -/

/-- **The Leibniz enclosure**: for a non-negative, antitone sequence `b`, every alternating partial
    sum lies in `[0, b 0]`. -/
theorem altSum_bracket (b : Nat → Q) (hnn : ∀ i, 0 ≤ (b i).num) (hden : ∀ i, 0 < (b i).den)
    (hanti : ∀ i, Qle (b (i + 1)) (b i)) (L : Nat) :
    Qle (⟨0, 1⟩ : Q) (AltSum b L) ∧ Qle (AltSum b L) (b 0) := by
  induction L generalizing b with
  | zero =>
    exact ⟨Qle_refl _, Qzero_le (hnn 0)⟩
  | succ L ih =>
    have ihb := ih (fun i => b (i + 1)) (fun i => hnn (i + 1)) (fun i => hden (i + 1))
      (fun i => hanti (i + 1))
    rw [AltSum_succ]
    refine ⟨Qsub_nonneg_of_le (Qle_trans (hden 1) ihb.2 (hanti 0)),
      Qsub_le_self (num_nonneg_of_Qzero_le ihb.1)⟩

/-- **The alternating gap bound**: consecutive tails are controlled by the first omitted term —
    `|AltSum b (L+m) − AltSum b L| ≤ b L`. The Bishop modulus for γ₀'s truncation error. -/
theorem altSum_gap (b : Nat → Q) (hnn : ∀ i, 0 ≤ (b i).num) (hden : ∀ i, 0 < (b i).den)
    (hanti : ∀ i, Qle (b (i + 1)) (b i)) (L m : Nat) :
    Qle (Qabs (Qsub (AltSum b (L + m)) (AltSum b L))) (b L) := by
  induction L generalizing b with
  | zero =>
    rw [Nat.zero_add, show AltSum b 0 = (⟨0, 1⟩ : Q) from rfl]
    have hbr := altSum_bracket b hnn hden hanti m
    have hnn' : 0 ≤ (Qsub (AltSum b m) (⟨0, 1⟩ : Q)).num :=
      num_nonneg_of_Qzero_le (Qle_congr_right (AltSum_den_pos b hden m)
        (Qeq_symm (Qsub_zero_eq _)) hbr.1)
    refine Qabs_le_of_nonneg hnn' ?_
    exact Qle_congr_left (AltSum_den_pos b hden m) (Qeq_symm (Qsub_zero_eq _)) hbr.2
  | succ L ih =>
    have ihb := ih (fun i => b (i + 1)) (fun i => hnn (i + 1)) (fun i => hden (i + 1))
      (fun i => hanti (i + 1))
    rw [show L + 1 + m = (L + m) + 1 from by omega, AltSum_succ, AltSum_succ]
    -- `Qsub (Qsub b0 X) (Qsub b0 Y)` cancels `b0` to `Qsub Y X`; abs equals `|Qsub X Y|` (ihb's).
    have hcancel : Qeq (Qsub (Qsub (b 0) (AltSum (fun i => b (i + 1)) (L + m)))
        (Qsub (b 0) (AltSum (fun i => b (i + 1)) L)))
        (Qsub (AltSum (fun i => b (i + 1)) L) (AltSum (fun i => b (i + 1)) (L + m))) := by
      simp only [Qeq, Qsub, add, neg]; push_cast; ring_uor
    have e1 := Qabs_Qeq hcancel
    rw [Qabs_Qsub_comm (AltSum (fun i => b (i + 1)) L) (AltSum (fun i => b (i + 1)) (L + m))] at e1
    exact Qle_congr_left
      (Qabs_den_pos (Qsub_den_pos (AltSum_den_pos (fun i => b (i + 1)) (fun i => hden (i + 1)) (L + m))
        (AltSum_den_pos (fun i => b (i + 1)) (fun i => hden (i + 1)) L)))
      (Qeq_symm e1) ihb

end UOR.Bridge.F1Square.Analysis
