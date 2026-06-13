/-
F1 square — the **second Stieltjes constant `γ₂`** (the v0.20.0 frontier ingredient that, with
`γ`, `γ₁`, `log 4π`, `ζ(2)`, `ζ(3)`, gives the third Li coefficient `λ₃`).

`γ₂` is the limit of the **defining sequence**

    g₂(N) = S₂(N) − ⅓·(ln N)³,        S₂(N) = Σ_{k=1}^N (ln k)²/k,

i.e. `γ₂ = lim_{N→∞} [ Σ_{k=1}^N (ln k)²/k − ⅓(ln N)³ ] ≈ −0.00969`. Telescoping the `⅓(ln N)³` term,
`g₂(N) = Σ_{k=2}^N e_k` with `e_k = (ln k)²/k − ⅓[(ln k)³ − (ln(k−1))³]`; the leading `(ln k)²/k`
terms cancel against the cubic-log difference, leaving `e_k = O((ln k)²/k²)`, a convergent tail —
so `γ₂ := Rlim g₂Seq` is a genuine constructive real (the regularity is the analytic content
scoped on top of this substrate, mirroring `GammaOne` for `γ₁`).

THIS FILE (brick 1 of γ₂): the real substrate — the term `(ln k)²/k`, the partial sum `S₂(N)`, the
cube `(ln N)³`, and the sequence `g₂(N)`. The monotonicity/regularity layers and the certified
bracket follow (the γ₂ analogue of `GammaOne`'s dyadic-tail stack).

Pure Lean 4, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Analysis.GammaOne
import F1Square.Analysis.RAddNF

namespace UOR.Bridge.F1Square.Analysis

/-- The squared-log harmonic term `(ln k)²/k` (for `k ≥ 1`), as a constructive real. -/
def lnSqOver (k : Nat) (hk : 1 ≤ k) : Real :=
  Rmul (Rmul (logN k hk) (logN k hk)) (ofQ ⟨1, k⟩ (by show 0 < k; omega))

/-- Each term `(ln k)²/k ≥ 0` (`(ln k)² ≥ 0` and `1/k > 0`). -/
theorem lnSqOver_nonneg (k : Nat) (hk : 1 ≤ k) : Rnonneg (lnSqOver k hk) :=
  Rnonneg_Rmul (Rnonneg_Rmul_self (logN k hk))
    (Rnonneg_ofQ (by show 0 < k; omega) (by show (0 : Int) ≤ 1; decide))

/-- The partial sum `S₂(N) = Σ_{k=1}^N (ln k)²/k`. -/
def lnSqSum : Nat → Real
  | 0 => zero
  | (n + 1) => Radd (lnSqSum n) (lnSqOver (n + 1) (by omega))

/-- `S₂(n) ≤ S₂(n+1)` (the new term is `≥ 0`). -/
theorem lnSqSum_step (n : Nat) : Rle (lnSqSum n) (lnSqSum (n + 1)) :=
  Rle_self_Radd_right (lnSqOver_nonneg (n + 1) (by omega))

/-- `S₂` is monotone (non-decreasing). -/
theorem lnSqSum_mono {a b : Nat} (hab : a ≤ b) : Rle (lnSqSum a) (lnSqSum b) := by
  induction hab with
  | refl => exact Rle_refl _
  | step _ ih => exact Rle_trans ih (lnSqSum_step _)

/-- The cube `(ln N)³` as a constructive real. -/
def logCube (N : Nat) (hN : 1 ≤ N) : Real :=
  Rmul (Rmul (logN N hN) (logN N hN)) (logN N hN)

/-- `(ln N)³ ≥ 0` for `N ≥ 1`. -/
theorem logCube_nonneg (N : Nat) (hN : 1 ≤ N) : Rnonneg (logCube N hN) :=
  Rnonneg_Rmul (Rnonneg_Rmul_self (logN N hN)) (Rnonneg_logN N hN)

/-- The **defining sequence** `g₂(j+1) = S₂(j+1) − ⅓·(ln (j+1))³` (indexed from `j = 0`).
    `γ₂ = Rlim g₂Seq`. -/
def g2Seq (j : Nat) : Real :=
  Rsub (lnSqSum (j + 1)) (Rmul (ofQ ⟨1, 3⟩ (by decide)) (logCube (j + 1) (by omega)))

-- ===========================================================================
-- The per-step difference `e_{p+1} = g₂(p+1) − g₂(p)` and its telescoping identity.
-- ===========================================================================

/-- `(a₁ − b₁) − (a₀ − b₀) ≈ (a₁ − a₀) − (b₁ − b₀)` — pointwise (all of `Rsub`/`Radd`/`Rneg`
    are pointwise on the regular sequences). -/
theorem Rsub_sub_sub (a₁ b₁ a₀ b₀ : Real) :
    Req (Rsub (Rsub a₁ b₁) (Rsub a₀ b₀)) (Rsub (Rsub a₁ a₀) (Rsub b₁ b₀)) := by
  apply Req_of_seq_Qeq; intro n
  simp only [Rsub, Radd, Rneg, neg, add, Qeq]; push_cast; ring_uor

/-- The per-step difference `e_{p+1} = g₂(p+1) − g₂(p) = (ln(p+1))²/(p+1) − ⅓((ln(p+1))³ − (ln p)³)`
    (`p ≥ 1`). -/
def e2Step (p : Nat) (hp : 1 ≤ p) : Real :=
  Rsub (lnSqOver (p + 1) (Nat.succ_pos p))
    (Rmul (ofQ ⟨1, 3⟩ (by decide))
      (Rsub (logCube (p + 1) (Nat.succ_pos p)) (logCube p hp)))

/-- **`g₂(j+1) − g₂(j) ≈ e_{j+1}`** — the consecutive difference is the per-step `e`. -/
theorem g2Seq_step_eq (j : Nat) :
    Req (Rsub (g2Seq (j + 1)) (g2Seq j)) (e2Step (j + 1) (Nat.succ_pos j)) := by
  -- the sum telescopes: S₂(j+2) − S₂(j+1) = (ln(j+2))²/(j+2)
  have hA : Req (Rsub (lnSqSum (j + 2)) (lnSqSum (j + 1)))
      (lnSqOver (j + 2) (Nat.succ_pos (j + 1))) := by
    show Req (Rsub (Radd (lnSqSum (j + 1)) (lnSqOver (j + 2) (by omega))) (lnSqSum (j + 1)))
             (lnSqOver (j + 2) (Nat.succ_pos (j + 1)))
    refine Req_trans (Rsub_congr (Radd_comm (lnSqSum (j + 1)) (lnSqOver (j + 2) (by omega)))
      (Req_refl _)) ?_
    refine Req_trans (Radd_assoc (lnSqOver (j + 2) (by omega)) (lnSqSum (j + 1))
      (Rneg (lnSqSum (j + 1)))) ?_
    exact Req_trans (Radd_congr (Req_refl _) (Radd_neg (lnSqSum (j + 1)))) (Radd_zero _)
  -- the cube term: ⅓C(j+2) − ⅓C(j+1) = ⅓(C(j+2) − C(j+1))
  have hB : Req (Rsub (Rmul (ofQ ⟨1, 3⟩ (by decide)) (logCube (j + 2) (by omega)))
        (Rmul (ofQ ⟨1, 3⟩ (by decide)) (logCube (j + 1) (by omega))))
      (Rmul (ofQ ⟨1, 3⟩ (by decide))
        (Rsub (logCube (j + 2) (by omega)) (logCube (j + 1) (by omega)))) :=
    Req_symm (Rmul_sub_distrib (ofQ ⟨1, 3⟩ (by decide)) (logCube (j + 2) (by omega))
      (logCube (j + 1) (by omega)))
  -- rearrange and combine
  refine Req_trans (Rsub_sub_sub (lnSqSum (j + 2))
    (Rmul (ofQ ⟨1, 3⟩ (by decide)) (logCube (j + 2) (by omega)))
    (lnSqSum (j + 1)) (Rmul (ofQ ⟨1, 3⟩ (by decide)) (logCube (j + 1) (by omega)))) ?_
  exact Rsub_congr hA hB

-- ===========================================================================
-- The cubic algebra: `a³ − b³ = (a−b)(a²+ab+b²)` and the cancellation identity.
-- ===========================================================================

/-- **`(a−b)(a² + ab + b²) ≈ a³ − b³`** — the difference-of-cubes factoring (the cubic analogue
    of `sq_diff_identity`), by distributing and telescoping the cross terms. -/
theorem cube_diff_identity (a b : Real) :
    Req (Rmul (Rsub a b) (Radd (Radd (Rmul a a) (Rmul a b)) (Rmul b b)))
        (Rsub (Rmul (Rmul a a) a) (Rmul (Rmul b b) b)) := by
  -- (a−b)·S = a·S − b·S
  refine Req_trans (Rmul_sub_distrib_right a b
    (Radd (Radd (Rmul a a) (Rmul a b)) (Rmul b b))) ?_
  -- expand a·S = a·a² + a·ab + a·b² and b·S = b·a² + b·ab + b·b²
  have haS : Req (Rmul a (Radd (Radd (Rmul a a) (Rmul a b)) (Rmul b b)))
      (Radd (Radd (Rmul a (Rmul a a)) (Rmul a (Rmul a b))) (Rmul a (Rmul b b))) :=
    Req_trans (Rmul_distrib a (Radd (Rmul a a) (Rmul a b)) (Rmul b b))
      (Radd_congr (Rmul_distrib a (Rmul a a) (Rmul a b)) (Req_refl _))
  have hbS : Req (Rmul b (Radd (Radd (Rmul a a) (Rmul a b)) (Rmul b b)))
      (Radd (Radd (Rmul b (Rmul a a)) (Rmul b (Rmul a b))) (Rmul b (Rmul b b))) :=
    Req_trans (Rmul_distrib b (Radd (Rmul a a) (Rmul a b)) (Rmul b b))
      (Radd_congr (Rmul_distrib b (Rmul a a) (Rmul a b)) (Req_refl _))
  refine Req_trans (Rsub_congr haS hbS) ?_
  -- now a pure Radd/Rneg/Rsub rearrangement on the six atoms (pointwise), modulo identifying
  -- the equal cross terms a·(a·b) = b·(a·a) and a·(b·b) = b·(a·b)
  have hx1 : Req (Rmul a (Rmul a b)) (Rmul b (Rmul a a)) := by
    refine Req_trans (Req_symm (Rmul_assoc a a b)) ?_
    refine Req_trans (Rmul_comm (Rmul a a) b) ?_
    exact Req_refl _
  have hx2 : Req (Rmul a (Rmul b b)) (Rmul b (Rmul a b)) := by
    refine Req_trans (Req_symm (Rmul_assoc a b b)) ?_
    refine Req_trans (Rmul_congr (Rmul_comm a b) (Req_refl b)) ?_
    refine Req_trans (Rmul_assoc b a b) ?_
    exact Req_refl _
  -- substitute the cross-term identifications, making the two middle pairs syntactically equal
  refine Req_trans (Rsub_congr (Radd_congr (Radd_congr (Req_refl _) hx1) hx2) (Req_refl _)) ?_
  -- telescope the matched atoms: (P + M₁ + M₂) − (M₁ + M₂ + Q) ≈ P − Q.  Done by Real algebra
  -- (assoc + `Radd_neg`), NOT pointwise: M₁,M₂ recur in both halves, so the cleared denominators
  -- would be squared and overrun `ring_uor`.
  have hcancel : ∀ P S Q : Real, Req (Rsub (Radd P S) (Radd S Q)) (Rsub P Q) := by
    intro P S Q
    refine Req_trans (Radd_congr (Req_refl (Radd P S)) (Rneg_Radd S Q)) ?_
    refine Req_trans (Radd_assoc P S (Radd (Rneg S) (Rneg Q))) ?_
    refine Req_trans (Radd_congr (Req_refl P) (Req_symm (Radd_assoc S (Rneg S) (Rneg Q)))) ?_
    refine Req_trans (Radd_congr (Req_refl P) (Radd_congr (Radd_neg S) (Req_refl (Rneg Q)))) ?_
    exact Radd_congr (Req_refl P)
      (Req_trans (Radd_comm zero (Rneg Q)) (Radd_zero (Rneg Q)))
  have htel : ∀ P M₁ M₂ Q : Real,
      Req (Rsub (Radd (Radd P M₁) M₂) (Radd (Radd M₁ M₂) Q)) (Rsub P Q) := fun P M₁ M₂ Q =>
    Req_trans (Rsub_congr (Radd_assoc P M₁ M₂) (Req_refl _)) (hcancel P (Radd M₁ M₂) Q)
  refine Req_trans (htel (Rmul a (Rmul a a)) (Rmul b (Rmul a a)) (Rmul b (Rmul a b))
    (Rmul b (Rmul b b))) ?_
  -- finally reorient P = a·a² → a²·a and Q = b·b² → b²·b
  exact Rsub_congr (Rmul_comm a (Rmul a a)) (Rmul_comm b (Rmul b b))

/-- **`(a²+ab+b²) + (a−b)(2a+b) ≈ 3a²`** — the quadratic identity behind the `e_k` decomposition,
    discharged by the RAddNF additive normalizer: expand `(a−b)(2a+b)`, flatten to a signed-atom
    list, then permute (decidably, via ℕ-indices) and cancel the `ab`/`b²` pairs. -/
theorem tri_sum_3a2 (a b : Real) :
    Req (Radd (Radd (Radd (Rmul a a) (Rmul a b)) (Rmul b b))
          (Rmul (Rsub a b) (Radd (Radd a a) b)))
        (Radd (Radd (Rmul a a) (Rmul a a)) (Rmul a a)) := by
  -- expand X = (a−b)(2a+b) ≈ (a²+a²+ab) − (ab+ab+b²)
  have hX : Req (Rmul (Rsub a b) (Radd (Radd a a) b))
      (Rsub (Radd (Radd (Rmul a a) (Rmul a a)) (Rmul a b))
            (Radd (Radd (Rmul a b) (Rmul a b)) (Rmul b b))) := by
    refine Req_trans (Rmul_sub_distrib_right a b (Radd (Radd a a) b)) ?_
    refine Rsub_congr ?_ ?_
    · exact Req_trans (Rmul_distrib a (Radd a a) b) (Radd_congr (Rmul_distrib a a a) (Req_refl _))
    · refine Req_trans (Rmul_distrib b (Radd a a) b) (Radd_congr ?_ (Req_refl _))
      exact Req_trans (Rmul_distrib b a a) (Radd_congr (Rmul_comm b a) (Rmul_comm b a))
  -- flatten LHS to the canonical signed-atom list [0,1,2,0,0,1,3,3,4].map f
  refine Req_trans (Radd_congr (Radd_eq_RsumL3 (Rmul a a) (Rmul a b) (Rmul b b)) hX) ?_
  refine Req_trans (Radd_congr (Req_refl _)
    (Req_trans (Radd_congr (Radd_eq_RsumL3 (Rmul a a) (Rmul a a) (Rmul a b))
        (Req_trans (Rneg_congr (Radd_eq_RsumL3 (Rmul a b) (Rmul a b) (Rmul b b)))
          (RsumL_map_Rneg [Rmul a b, Rmul a b, Rmul b b])))
      (Req_symm (RsumL_append [Rmul a a, Rmul a a, Rmul a b]
        [Rneg (Rmul a b), Rneg (Rmul a b), Rneg (Rmul b b)])))) ?_
  refine Req_trans (Req_symm (RsumL_append [Rmul a a, Rmul a b, Rmul b b]
    [Rmul a a, Rmul a a, Rmul a b, Rneg (Rmul a b), Rneg (Rmul a b), Rneg (Rmul b b)])) ?_
  -- convert the RHS 3a² to canonical-list form
  refine Req_trans ?_ (Req_symm (Radd_eq_RsumL3 (Rmul a a) (Rmul a a) (Rmul a a)))
  -- now: RsumL [a²,ab,b²,a²,a²,ab,−ab,−ab,−b²]  ≈  RsumL [a²,a²,a²]
  -- cancel the three ± pairs at known positions (choice-free, no `decide` on `Perm`):
  --   ab (pos 1) ↔ −ab (pos 6); then ab (pos 4) ↔ −ab; then b² ↔ −b²
  refine Req_trans (RsumL_cancel_anywhere (Rmul a b) [Rmul a a]
    [Rmul b b, Rmul a a, Rmul a a, Rmul a b] [Rneg (Rmul a b), Rneg (Rmul b b)]) ?_
  refine Req_trans (RsumL_cancel_anywhere (Rmul a b) [Rmul a a, Rmul b b, Rmul a a, Rmul a a]
    [] [Rneg (Rmul b b)]) ?_
  exact RsumL_cancel_anywhere (Rmul b b) [Rmul a a] [Rmul a a, Rmul a a] []

/-- **`⅓·(Y+Y+Y) ≈ Y`** — the rational coefficient that closes the `e_k` decomposition
    (`⅓ · 3a² = a²`): distribute `⅓` over the threefold sum, factor back to `(⅓+⅓+⅓)·Y`, and
    `⅓+⅓+⅓ = 1`. -/
theorem Rmul_third_three (Y : Real) :
    Req (Rmul (ofQ (⟨1, 3⟩ : Q) (by decide)) (Radd (Radd Y Y) Y)) Y := by
  have hdist : Req (Rmul (ofQ (⟨1, 3⟩ : Q) (by decide)) (Radd (Radd Y Y) Y))
      (Rmul (Radd (Radd (ofQ (⟨1, 3⟩ : Q) (by decide)) (ofQ (⟨1, 3⟩ : Q) (by decide)))
        (ofQ (⟨1, 3⟩ : Q) (by decide))) Y) := by
    refine Req_trans (Rmul_distrib (ofQ (⟨1, 3⟩ : Q) (by decide)) (Radd Y Y) Y) ?_
    refine Req_trans (Radd_congr (Rmul_distrib (ofQ (⟨1, 3⟩ : Q) (by decide)) Y Y) (Req_refl _)) ?_
    refine Req_trans (Radd_congr
      (Req_symm (Rmul_distrib_right (ofQ (⟨1, 3⟩ : Q) (by decide)) (ofQ (⟨1, 3⟩ : Q) (by decide)) Y))
      (Req_refl _)) ?_
    exact Req_symm (Rmul_distrib_right (Radd (ofQ (⟨1, 3⟩ : Q) (by decide))
      (ofQ (⟨1, 3⟩ : Q) (by decide))) (ofQ (⟨1, 3⟩ : Q) (by decide)) Y)
  refine Req_trans hdist ?_
  have hcoef : Req (Radd (Radd (ofQ (⟨1, 3⟩ : Q) (by decide)) (ofQ (⟨1, 3⟩ : Q) (by decide)))
      (ofQ (⟨1, 3⟩ : Q) (by decide))) one := by
    refine Req_trans (Radd_congr (Radd_ofQ_ofQ (by decide) (by decide)) (Req_refl _)) ?_
    refine Req_trans (Radd_ofQ_ofQ (by decide) (by decide)) ?_
    exact Req_of_seq_Qeq (fun _ => by
      show Qeq (add (add (⟨1, 3⟩ : Q) ⟨1, 3⟩) ⟨1, 3⟩) ⟨1, 1⟩; decide)
  exact Req_trans (Rmul_congr hcoef (Req_refl Y)) (Rone_mul Y)

/-- **The e_k multiplicative core**: `a²(a−b) ≈ ⅓·(δ·W + δ²·(2a+b))`, `δ = a−b`,
    `W = a²+ab+b²` — combining `tri_sum_3a2` (`W + δ(2a+b) = 3a²`) and `Rmul_third_three`
    (`⅓·3a² = a²`). The identity that turns `e_k` into its bound-ready decomposition. -/
theorem e2_core (a b : Real) :
    Req (Rmul (Rmul a a) (Rsub a b))
        (Rmul (ofQ (⟨1, 3⟩ : Q) (by decide))
          (Radd (Rmul (Rsub a b) (Radd (Radd (Rmul a a) (Rmul a b)) (Rmul b b)))
                (Rmul (Rmul (Rsub a b) (Rsub a b)) (Radd (Radd a a) b)))) := by
  refine Req_symm ?_
  -- ⅓·(δW + δ²T) ≈ ⅓·(δW + δ(δT))
  refine Req_trans (Rmul_congr (Req_refl _) (Radd_congr (Req_refl _)
    (Rmul_assoc (Rsub a b) (Rsub a b) (Radd (Radd a a) b)))) ?_
  -- ≈ ⅓·(δ·(W + δT))
  refine Req_trans (Rmul_congr (Req_refl _)
    (Req_symm (Rmul_distrib (Rsub a b) (Radd (Radd (Rmul a a) (Rmul a b)) (Rmul b b))
      (Rmul (Rsub a b) (Radd (Radd a a) b))))) ?_
  -- ≈ ⅓·(δ·3a²)   [tri_sum_3a2 on W + δT]
  refine Req_trans (Rmul_congr (Req_refl _)
    (Rmul_congr (Req_refl _) (tri_sum_3a2 a b))) ?_
  -- rearrange ⅓·(δ·3a²) ≈ δ·(⅓·3a²) ≈ δ·a² ≈ a²·δ
  refine Req_trans (Req_symm (Rmul_assoc (ofQ (⟨1, 3⟩ : Q) (by decide)) (Rsub a b)
    (Radd (Radd (Rmul a a) (Rmul a a)) (Rmul a a)))) ?_
  refine Req_trans (Rmul_congr (Rmul_comm (ofQ (⟨1, 3⟩ : Q) (by decide)) (Rsub a b))
    (Req_refl _)) ?_
  refine Req_trans (Rmul_assoc (Rsub a b) (ofQ (⟨1, 3⟩ : Q) (by decide))
    (Radd (Radd (Rmul a a) (Rmul a a)) (Rmul a a))) ?_
  refine Req_trans (Rmul_congr (Req_refl _) (Rmul_third_three (Rmul a a))) ?_
  exact Rmul_comm (Rsub a b) (Rmul a a)

private theorem Rneg_Rneg_g2 (x : Real) : Req (Rneg (Rneg x)) x :=
  Req_of_seq_Qeq (fun _ => by simp only [Rneg, Qeq, neg]; push_cast; ring_uor)

/-- **The e_k upper-bound identity**: `⅓δ²(2a+b) − e_k ≈ a²(δ−u)` (`δ = a−b`), the difference
    whose non-negativity (since `δ ≥ u = 1/(p+1)` and `a² ≥ 0`) gives `e_k ≤ ⅓δ²(2a+b)`. -/
theorem e2_ub_identity (a b u : Real) :
    Req (Rsub (Rmul (ofQ (⟨1, 3⟩ : Q) (by decide))
              (Rmul (Rmul (Rsub a b) (Rsub a b)) (Radd (Radd a a) b)))
          (Rsub (Rmul (Rmul a a) u)
            (Rmul (ofQ (⟨1, 3⟩ : Q) (by decide))
              (Rmul (Rsub a b) (Radd (Radd (Rmul a a) (Rmul a b)) (Rmul b b))))))
        (Rmul (Rmul a a) (Rsub (Rsub a b) u)) := by
  -- quadUB − (Au − ⅓δW) ≈ (⅓δW + quadUB) − Au ≈ a²δ − Au ≈ a²(δ−u)
  refine Req_trans (Radd_congr (Req_refl _)
    (Req_trans (Rneg_Radd (Rmul (Rmul a a) u)
        (Rneg (Rmul (ofQ (⟨1, 3⟩ : Q) (by decide))
          (Rmul (Rsub a b) (Radd (Radd (Rmul a a) (Rmul a b)) (Rmul b b))))))
      (Radd_congr (Req_refl _) (Rneg_Rneg_g2 _)))) ?_
  refine Req_trans (Radd_congr (Req_refl _) (Radd_comm _ _)) ?_
  refine Req_trans (Req_symm (Radd_assoc _ _ _)) ?_
  refine Req_trans (Radd_congr (Radd_comm _ _) (Req_refl _)) ?_
  refine Req_trans (Radd_congr
    (Req_trans (Req_symm (Rmul_distrib (ofQ (⟨1, 3⟩ : Q) (by decide))
        (Rmul (Rsub a b) (Radd (Radd (Rmul a a) (Rmul a b)) (Rmul b b)))
        (Rmul (Rmul (Rsub a b) (Rsub a b)) (Radd (Radd a a) b))))
      (Req_symm (e2_core a b))) (Req_refl _)) ?_
  exact Req_symm (Rmul_sub_distrib (Rmul a a) (Rsub a b) u)

/-- **The e_k UPPER bound** `e_k ≤ ⅓·(a−b)²·(2a+b)` (`a = ln(p+1)`, `b = ln p`): from
    `e2_ub_identity` and `δ ≥ 1/(p+1)` (`deltaLog_lower`), `a² ≥ 0`. -/
theorem e2Step_le_quad (p : Nat) (hp : 1 ≤ p) :
    Rle (e2Step p hp)
        (Rmul (ofQ (⟨1, 3⟩ : Q) (by decide))
          (Rmul (Rmul (Rsub (logN (p + 1) (Nat.succ_pos p)) (logN p hp))
                      (Rsub (logN (p + 1) (Nat.succ_pos p)) (logN p hp)))
                (Radd (Radd (logN (p + 1) (Nat.succ_pos p)) (logN (p + 1) (Nat.succ_pos p)))
                  (logN p hp)))) := by
  have he2 : Req (e2Step p hp)
      (Rsub (Rmul (Rmul (logN (p + 1) (Nat.succ_pos p)) (logN (p + 1) (Nat.succ_pos p)))
              (ofQ (⟨1, p + 1⟩ : Q) (Nat.succ_pos p)))
        (Rmul (ofQ (⟨1, 3⟩ : Q) (by decide))
          (Rmul (Rsub (logN (p + 1) (Nat.succ_pos p)) (logN p hp))
            (Radd (Radd (Rmul (logN (p + 1) (Nat.succ_pos p)) (logN (p + 1) (Nat.succ_pos p)))
                    (Rmul (logN (p + 1) (Nat.succ_pos p)) (logN p hp)))
              (Rmul (logN p hp) (logN p hp)))))) := by
    show Req (Rsub (Rmul (Rmul (logN (p + 1) (Nat.succ_pos p)) (logN (p + 1) (Nat.succ_pos p)))
              (ofQ (⟨1, p + 1⟩ : Q) (Nat.succ_pos p)))
        (Rmul (ofQ (⟨1, 3⟩ : Q) (by decide))
          (Rsub (Rmul (Rmul (logN (p + 1) (Nat.succ_pos p)) (logN (p + 1) (Nat.succ_pos p)))
                  (logN (p + 1) (Nat.succ_pos p)))
                (Rmul (Rmul (logN p hp) (logN p hp)) (logN p hp))))) _
    exact Rsub_congr (Req_refl _) (Rmul_congr (Req_refl _)
      (Req_symm (cube_diff_identity (logN (p + 1) (Nat.succ_pos p)) (logN p hp))))
  have hub := e2_ub_identity (logN (p + 1) (Nat.succ_pos p)) (logN p hp)
    (ofQ (⟨1, p + 1⟩ : Q) (Nat.succ_pos p))
  have hnn : Rnonneg (Rmul (Rmul (logN (p + 1) (Nat.succ_pos p)) (logN (p + 1) (Nat.succ_pos p)))
      (Rsub (Rsub (logN (p + 1) (Nat.succ_pos p)) (logN p hp))
        (ofQ (⟨1, p + 1⟩ : Q) (Nat.succ_pos p)))) :=
    Rnonneg_Rmul (Rnonneg_Rmul_self _) (Rnonneg_Rsub_of_Rle (deltaLog_lower p hp))
  exact Rle_of_Rnonneg_Rsub (Rnonneg_congr (Req_symm (Req_trans (Rsub_congr (Req_refl _) he2) hub)) hnn)

end UOR.Bridge.F1Square.Analysis
