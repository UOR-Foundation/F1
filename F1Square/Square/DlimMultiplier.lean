/-
# The real-weight diagonal MULTIPLIER as a constructive GRAPH / DOMAIN on the completion

Reviewer multiplier-gate items 2-3, in the ZETA-FREE completion cone.

We do NOT build a choice-based output map.  A multiplier `M_w` with a real weight sequence
`w : ℕ → ℝ` is presented as a RELATION (its GRAPH) between completion members: `(X, Y) ∈ Γ(M_w)`
iff the coordinates of `Y` are the weighted coordinates of `X`, `coord i Y ≈ w_i · coord i X`.
Its maximal DOMAIN `D(M_w)` is the (choice-free) predicate "some `Y` realises the weighted
coordinates".  This keeps every output constructive: the graph is a `Prop`, the domain an `∃`, and
uniqueness of the output is a THEOREM (coordinate separation), not a definitional choice.

Item 2 (constructive graph/domain): the definitions `MulGraph`, `MulDom` above.
Item 3 (structure): setoid congruence (`MulGraph_congr_mp`), output uniqueness
(`MulGraph_unique_mp`), additive & scalar graph-linearity (`MulGraph_add_mp`, `MulGraph_smul_mp`),
the finite-support vectors lie in the domain (`MulDom_of_mp`), density of that finite-support domain
(`MulDom_dense_mp`), and subspace closure of the domain (`MulDom_add_mp`, `MulDom_smul_mp`).

ZETA-FREE: imports only the completion cone (`DlimProjHardening` + `DlimCompletionCS`); no
transcendental / reciprocal / radical primitives and no operator-core import (the cone stays clean).
WHNF-safe: `completedInner`
/`completedNormSq`/`completedDist2`/`coord` are never unfolded by defeq — only the `coord_*`,
`completedInner_*`, `dlimBasis_coord_bo`, `coord_separation_hd` black-box laws are used.
-/
import F1Square.Square.DlimProjHardening
import F1Square.Square.DlimCompletionCS

open UOR.Bridge.F1Square Square
open UOR.Bridge.F1Square.Analysis

namespace UOR.Bridge.F1Square.Square

-- ===========================================================================
-- Local ℂ zero micro-helpers (leaf names end `_mp`).
-- ===========================================================================

/-- `z · 0 ≈ 0` on ℂ. -/
private theorem cmul_czero_mp (z : Complex) : Ceq (Cmul z Czero) Czero :=
  ⟨Req_trans (Radd_congr (Rmul_zero z.re) (Rneg_congr (Rmul_zero z.im))) (Radd_neg zero),
   Req_trans (Radd_congr (Rmul_zero z.re) (Rmul_zero z.im)) (Radd_zero zero)⟩

/-- `0 · z ≈ 0` on ℂ. -/
private theorem czero_cmul_mp (z : Complex) : Ceq (Cmul Czero z) Czero :=
  Ceq_trans (Cmul_comm Czero z) (cmul_czero_mp z)

/-- `z ⊕ 0 ≈ z` on ℂ. -/
private theorem cadd_czero_mp (z : Complex) : Ceq (Cadd z Czero) z :=
  ⟨Radd_zero z.re, Radd_zero z.im⟩

/-- A finite sum whose every entry is `≈ 0` is `≈ 0`. -/
private theorem cvecSum_eq_zero_mp : ∀ (N : Nat) (g : CVec N), (∀ k, Ceq (g k) Czero) →
    Ceq (cvecSum N g) Czero
  | 0, _, _ => Ceq_refl _
  | (N + 1), g, h => by
      refine Ceq_trans (Cadd_congr
        (cvecSum_eq_zero_mp N _ (fun k => h ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩))
        (h ⟨N, Nat.lt_succ_self N⟩)) ?_
      exact cadd_czero_mp Czero

/-- Pointwise value of the included `i`-th coordinate basis vector at `k`: `1` if `k = i`, else `0`. -/
private theorem cvInc_stdBasis_apply_mp {i K : Nat} (hiK : i + 1 ≤ K) (k : Fin K) :
    Ceq ((cvInc hiK (stdBasisVec (i + 1) ⟨i, Nat.lt_succ_self i⟩)) k)
        (if k.val = i then Cone else Czero) := by
  by_cases hk : k.val < i + 1
  · simp only [cvInc, stdBasisVec, dif_pos hk]; exact Ceq_refl _
  · have hne : ¬ (k.val = i) := by intro hc; apply hk; rw [hc]; exact Nat.lt_succ_self i
    simp only [cvInc, stdBasisVec, dif_neg hk, if_neg hne]; exact Ceq_refl _

-- ===========================================================================
-- Coordinate vanishing BEYOND the support (companion of `dlimBasis_coord_bo`).
--   `⟨e_i, dlimMk x⟩ ≈ 0`  whenever  `i ≥ stage(x)`.
-- Mirrors `dlimBasis_ortho_bo`, but the second slot is a GENERAL finite vector: at `k = i` the
-- included `x` is padded to `0` (since `i ≥ N`), at `k ≠ i` the basis spike is `0`.
-- ===========================================================================

/-- **Beyond-support vanishing**: pairing the `i`-th basis vector against a stage-`N` finite vector
    `x` with `i ≥ N` gives `≈ 0` (the spike sits past the support of `x`). -/
private theorem dlimInner_basis_ge (i N : Nat) (x : CVec N) (h : N ≤ i) :
    Ceq (dlimInner (dlimBasis i) (dlimMk x)) Czero := by
  have hiK : i + 1 ≤ max (i + 1) N := Nat.le_max_left _ _
  have hjK : N ≤ max (i + 1) N := Nat.le_max_right _ _
  refine Ceq_trans (Ceq_symm (dlimInner_eval (dlimBasis i) (dlimMk x) hiK hjK)) ?_
  show Ceq (cvecSum (max (i + 1) N)
    (fun k => Cmul (Cconj ((cvInc hiK (stdBasisVec (i + 1) ⟨i, Nat.lt_succ_self i⟩)) k))
                   ((cvInc hjK x) k))) Czero
  refine cvecSum_eq_zero_mp _ _ (fun k => ?_)
  by_cases hki : k.val = i
  · -- `k = i ≥ N`: the included `x` is padded to `0` at this coordinate.
    have hknl : ¬ (k.val < N) := by omega
    refine Ceq_trans (Cmul_congr (Ceq_refl _) ?_) (cmul_czero_mp _)
    show Ceq (cvInc hjK x k) Czero
    simp only [cvInc, dif_neg hknl]; exact Ceq_refl _
  · -- `k ≠ i`: the basis spike vanishes here.
    refine Ceq_trans (Cmul_congr (Cconj_congr (cvInc_stdBasis_apply_mp hiK k)) (Ceq_refl _)) ?_
    rw [if_neg hki]
    exact Ceq_trans (Cmul_congr Cconj_Czero (Ceq_refl _)) (czero_cmul_mp _)

-- ===========================================================================
-- ITEM 2 — the constructive GRAPH and DOMAIN of the real-weight multiplier.
-- ===========================================================================

/-- Real → complex embedding (the ζ-tainted `Cofreal` is out of cone, so we build it locally). -/
private def cReal (r : Real) : Complex := ⟨r, zero⟩

/-- **The multiplier GRAPH**: `(X, Y)` is in the graph of the `w`-weighted diagonal multiplier iff
    `Y` has coordinates `w_i · X_i`.  A RELATION — no function, no choice-based output selection. -/
def MulGraph (w : Nat → Real) (X Y : DLimCompletionRaw) : Prop :=
  ∀ i : Nat, Ceq (coord i Y) (Cmul (cReal (w i)) (coord i X))

/-- **The maximal DOMAIN**: `X ∈ D(M_w)` iff some completion member `Y` realises the weighted
    coordinates. -/
def MulDom (w : Nat → Real) (X : DLimCompletionRaw) : Prop :=
  ∃ Y : DLimCompletionRaw, MulGraph w X Y

-- ===========================================================================
-- ITEM 3 — structural properties.
-- ===========================================================================

/-- **Setoid congruence of the graph**: the relation descends to `DLimCompletionEq` in both slots. -/
theorem MulGraph_congr_mp (w : Nat → Real) {X Xb Y Yb : DLimCompletionRaw}
    (hX : DLimCompletionEq X Xb) (hY : DLimCompletionEq Y Yb) (h : MulGraph w X Y) :
    MulGraph w Xb Yb := fun i =>
  Ceq_trans (Ceq_symm (coord_congr i hY))
    (Ceq_trans (h i) (Cmul_congr (Ceq_refl (cReal (w i))) (coord_congr i hX)))

/-- **Output uniqueness**: two members realising the same weighted coordinates are `≈`-equal
    (coordinate separation on `coord i Y ≈ w_i · X_i ≈ coord i Yb`). -/
theorem MulGraph_unique_mp (w : Nat → Real) {X Y Yb : DLimCompletionRaw}
    (h : MulGraph w X Y) (h2 : MulGraph w X Yb) : DLimCompletionEq Y Yb :=
  coord_separation_hd (fun i => Ceq_trans (h i) (Ceq_symm (h2 i)))

/-- **Additive graph-linearity**: `(X,Y), (X',Y') ∈ Γ ⟹ (X⊕X', Y⊕Y') ∈ Γ`.  Uses coordinate
    additivity and the distribution of `w_i·(·)` over `⊕`. -/
theorem MulGraph_add_mp (w : Nat → Real) {X Y X2 Y2 : DLimCompletionRaw}
    (h : MulGraph w X Y) (h2 : MulGraph w X2 Y2) :
    MulGraph w (dlimCompletionAdd X X2) (dlimCompletionAdd Y Y2) := fun i =>
  Ceq_trans (coord_add i Y Y2)
    (Ceq_trans (Cadd_congr (h i) (h2 i))
      (Ceq_trans (Ceq_symm (Cmul_distrib (cReal (w i)) (coord i X) (coord i X2)))
        (Cmul_congr (Ceq_refl (cReal (w i))) (Ceq_symm (coord_add i X X2)))))

/-- **Scalar graph-linearity**: `(X,Y) ∈ Γ ⟹ (c•X, c•Y) ∈ Γ`.  Uses coordinate homogeneity and the
    commutation `c·(w_i·X_i) ≈ w_i·(c·X_i)`. -/
theorem MulGraph_smul_mp (w : Nat → Real) (c : Complex) {X Y : DLimCompletionRaw}
    (h : MulGraph w X Y) :
    MulGraph w (dlimCompletionSmul c X) (dlimCompletionSmul c Y) := fun i =>
  Ceq_trans (coord_smul i c Y)
    (Ceq_trans (Cmul_congr (Ceq_refl c) (h i))
      (Ceq_trans (Ceq_symm (Cmul_assoc c (cReal (w i)) (coord i X)))
        (Ceq_trans (Cmul_congr (Cmul_comm c (cReal (w i))) (Ceq_refl (coord i X)))
          (Ceq_trans (Cmul_assoc (cReal (w i)) c (coord i X))
            (Cmul_congr (Ceq_refl (cReal (w i))) (Ceq_symm (coord_smul i c X)))))))

-- ===========================================================================
-- ITEM 3 (crux) — the embedded FINITE-SUPPORT vectors are in the domain.
-- ===========================================================================

/-- **Finite-support vectors are in the domain**: `of a ∈ D(M_w)`, with the explicit witness the
    coordinatewise-weighted finite vector `⟨e_i,a⟩ ↦ w_i·⟨e_i,a⟩`.  Coordinate `i` of both `of a` and
    the witness is computed from `coord_of`: for `i < a.stage` it is the vector entry
    (`dlimBasis_coord_bo`), for `i ≥ a.stage` it is `0` (`dlimInner_basis_ge`); the weighting matches
    in both cases. -/
theorem MulDom_of_mp (w : Nat → Real) (a : DLimRaw) : MulDom w (DLimCompletionRaw.of a) := by
  refine ⟨DLimCompletionRaw.of
      (dlimMk (fun j : Fin a.stage => Cmul (cReal (w j.val)) (a.vec j))), ?_⟩
  intro i
  by_cases h : i < a.stage
  · -- `i < a.stage`: both coordinates read off the finite vector entries.
    have hL : Ceq (coord i (DLimCompletionRaw.of
          (dlimMk (fun j : Fin a.stage => Cmul (cReal (w j.val)) (a.vec j)))))
        (Cmul (cReal (w i)) (a.vec ⟨i, h⟩)) :=
      Ceq_trans (coord_of i (dlimMk (fun j : Fin a.stage => Cmul (cReal (w j.val)) (a.vec j))))
        (dlimBasis_coord_bo i a.stage h (fun j : Fin a.stage => Cmul (cReal (w j.val)) (a.vec j)))
    have hR : Ceq (coord i (DLimCompletionRaw.of a)) (a.vec ⟨i, h⟩) :=
      Ceq_trans (coord_of i a) (dlimBasis_coord_bo i a.stage h a.vec)
    exact Ceq_trans hL (Cmul_congr (Ceq_refl (cReal (w i))) (Ceq_symm hR))
  · -- `i ≥ a.stage`: both coordinates vanish, and `w_i·0 ≈ 0`.
    have hge : a.stage ≤ i := Nat.le_of_not_lt h
    have hL : Ceq (coord i (DLimCompletionRaw.of
          (dlimMk (fun j : Fin a.stage => Cmul (cReal (w j.val)) (a.vec j))))) Czero :=
      Ceq_trans (coord_of i (dlimMk (fun j : Fin a.stage => Cmul (cReal (w j.val)) (a.vec j))))
        (dlimInner_basis_ge i a.stage
          (fun j : Fin a.stage => Cmul (cReal (w j.val)) (a.vec j)) hge)
    have hR : Ceq (coord i (DLimCompletionRaw.of a)) Czero :=
      Ceq_trans (coord_of i a) (dlimInner_basis_ge i a.stage a.vec hge)
    exact Ceq_trans hL
      (Ceq_symm (Ceq_trans (Cmul_congr (Ceq_refl (cReal (w i))) hR) (cmul_czero_mp (cReal (w i)))))

-- ===========================================================================
-- ITEM 3 — DENSITY of the finite-support domain, and subspace closure.
-- ===========================================================================

/-- **Density of the finite-support domain**: every completion member `X` is within squared distance
    `1/(k+1)` of some `of a` that lies in `D(M_w)`.  Combine `completion_dense` (the finite
    representative `of (X.seq N)` is close) with `MulDom_of_mp` (it is in the domain). -/
theorem MulDom_dense_mp (w : Nat → Real) (X : DLimCompletionRaw) (k : Nat) :
    ∃ a : DLimRaw, MulDom w (DLimCompletionRaw.of a) ∧
      Rle (completedDist2 X (DLimCompletionRaw.of a)) (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k)) := by
  obtain ⟨N, hN⟩ := completion_dense X k
  exact ⟨X.seq N, MulDom_of_mp w (X.seq N), hN⟩

/-- **Additive closure of the domain**: `X, X' ∈ D(M_w) ⟹ X⊕X' ∈ D(M_w)` (combine the witnesses). -/
theorem MulDom_add_mp (w : Nat → Real) {X X2 : DLimCompletionRaw}
    (h : MulDom w X) (h2 : MulDom w X2) : MulDom w (dlimCompletionAdd X X2) := by
  obtain ⟨Y, hY⟩ := h
  obtain ⟨Y2, hY2⟩ := h2
  exact ⟨dlimCompletionAdd Y Y2, MulGraph_add_mp w hY hY2⟩

/-- **Scalar closure of the domain**: `X ∈ D(M_w) ⟹ c•X ∈ D(M_w)` (scale the witness). -/
theorem MulDom_smul_mp (w : Nat → Real) (c : Complex) {X : DLimCompletionRaw}
    (h : MulDom w X) : MulDom w (dlimCompletionSmul c X) := by
  obtain ⟨Y, hY⟩ := h
  exact ⟨dlimCompletionSmul c Y, MulGraph_smul_mp w c hY⟩

end UOR.Bridge.F1Square.Square
