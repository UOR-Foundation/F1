/-
# The GENUINE inner-product ADJOINT of the real-weight diagonal multiplier — SELF-ADJOINTNESS

The culmination of the ζ-free real-weight multiplier programme (reviewer gate items 6-7): the genuine
inner-product ADJOINT of `M_w`, presented — like the operator itself — as a choice-free RELATION (its
graph), together with:

* `adj_of_dom_adj` — the EASY inclusion `D(M_w) ⊆ D(M_w*)`: a domain pair is an adjoint pair
  (directly from the symmetry `mult_symm_sy`).
* `dom_of_adj_adj` — the HARD inclusion `D(M_w*) ⊆ D(M_w)` (MAXIMALITY, the crux distinguishing a
  SELF-adjoint from a merely symmetric operator): an adjoint pair is a domain pair, proved by testing
  the adjoint relation against the DENSE coordinate basis `of e_i ∈ D(M_w)` and separating coordinates.
* `dom_eq_adj` — `Dom(M_w*) = Dom(M_w)`.
* `selfadjoint_adj` — ACTUAL graph-level SELF-ADJOINTNESS `Γ(M_w*) = Γ(M_w)` (not symmetry, not a
  coordinatewise statement): the adjoint relation EQUALS the operator relation.

The maximality (`dom_of_adj_adj`) is the genuine content: for each coordinate `i`, the basis vector
`of e_i` sits in `D(M_w)` (`MulDom_of_mp`) with image `Xp_i`; the adjoint hypothesis at `X := of e_i`
reads `⟨Xp_i, Y⟩ = ⟨of e_i, Z⟩ = coord i Z`, while `Xp_i ≈ w_i•(of e_i)` (coordinate agreement, both
`= w_i·δ_{ij}`) turns the left side into `⟨w_i•(of e_i), Y⟩ = conj(w_i)·coord i Y = w_i·coord i Y`
(the weight is real, hence self-conjugate).  Chaining gives `coord i Z ≈ w_i·coord i Y` for every `i`,
i.e. `Γ(M_w) (Y,Z)`.

ZETA-FREE, sqrt-free, division-free, choice-free.  WHNF-safe: `completedInner`/`coord` are never
unfolded by defeq beyond the trivial `coord i · := ⟨of e_i, ·⟩` name-substitution; only the completion
black-box laws (`completedInner_congr`, `completedInner_conj`, `completedInner_smul_right`, `coord_*`,
`coord_separation_hd`, `dlimBasis_ortho_bo`, `MulDom_of_mp`, `mult_symm_sy`) are used.
Axioms `[propext, Quot.sound]`.
-/
import F1Square.Square.DlimMultiplierSymm

open UOR.Bridge.F1Square.Square
open UOR.Bridge.F1Square.Analysis

namespace UOR.Bridge.F1Square.Square

-- ===========================================================================
-- Local ℝ / ℂ micro-helpers (leaf names end `_adj`).
-- ===========================================================================

/-- `−0 ≈ 0`. -/
private theorem Rneg_zero_adj : Req (Rneg zero) zero :=
  Req_of_seq_Qeq (fun n => by show Qeq (neg (zero.seq n)) (zero.seq n); rw [zero_seq]; decide)

/-- `z · 0 ≈ 0` on ℂ. -/
private theorem cmul_czero_adj (z : Complex) : Ceq (Cmul z Czero) Czero :=
  ⟨Req_trans (Radd_congr (Rmul_zero z.re) (Rneg_congr (Rmul_zero z.im))) (Radd_neg zero),
   Req_trans (Radd_congr (Rmul_zero z.re) (Rmul_zero z.im)) (Radd_zero zero)⟩

/-- `conj(r) ≈ r` for a real-embedded scalar `r + 0i` (the weight is real, hence self-conjugate). -/
private theorem Cconj_cReal_adj (r : Real) : Ceq (Cconj (⟨r, zero⟩ : Complex)) (⟨r, zero⟩ : Complex) :=
  ⟨Req_refl r, Rneg_zero_adj⟩

/-- **Completion inner-product LEFT scalar law**: `⟨c•U, V⟩ ≈ (conj c)·⟨U, V⟩`.  Built from Hermitian
    symmetry (`completedInner_conj`) and the right scalar law (`completedInner_smul_right`) — the
    completion inner laws used as black boxes; no `completedInner` whnf unfold. -/
private theorem completedInner_smul_left_adj (c : Complex) (U V : DLimCompletionRaw) :
    Ceq (completedInner (dlimCompletionSmul c U) V) (Cmul (Cconj c) (completedInner U V)) :=
  Ceq_trans (completedInner_conj (dlimCompletionSmul c U) V)
    (Ceq_trans (Cconj_congr (completedInner_smul_right c V U))
      (Ceq_trans (Cconj_Cmul c (completedInner V U))
        (Cmul_congr (Ceq_refl (Cconj c)) (Ceq_symm (completedInner_conj U V)))))

-- ===========================================================================
-- The GENUINE inner-product ADJOINT — a choice-free RELATION (its graph & domain).
-- ===========================================================================

/-- **The adjoint GRAPH** (universal property): `(Y, Z)` is in the graph of the adjoint `M_w*` iff, for
    every domain pair `(X, Xp) ∈ Γ(M_w)` (so `Xp = M_w X`), `⟨M_w X, Y⟩ ≈ ⟨X, Z⟩`.  A `Prop` — no
    choice-based output selection. -/
def AdjGraph (w : Nat → Real) (Y Z : DLimCompletionRaw) : Prop :=
  ∀ X Xp : DLimCompletionRaw, MulGraph w X Xp → Ceq (completedInner Xp Y) (completedInner X Z)

/-- **The adjoint DOMAIN**: `Y ∈ D(M_w*)` iff some `Z` realises the adjoint output of `Y`. -/
def AdjDom (w : Nat → Real) (Y : DLimCompletionRaw) : Prop := ∃ Z, AdjGraph w Y Z

-- ===========================================================================
-- TARGET 1 — the EASY inclusion `D(M_w) ⊆ D(M_w*)`.
-- ===========================================================================

/-- **Domain ⊆ adjoint-domain, at the graph level**: if `(Y, Yp) ∈ Γ(M_w)`, then `(Y, Yp)` is an
    adjoint pair.  Immediate from the symmetry `⟨M_w X, Y⟩ ≈ ⟨X, M_w Y⟩` (`mult_symm_sy`). -/
theorem adj_of_dom_adj (w : Nat → Real) {Y Yp : DLimCompletionRaw} (hY : MulGraph w Y Yp) :
    AdjGraph w Y Yp :=
  fun _X _Xp hX => mult_symm_sy w hX hY

/-- **`D(M_w) ⊆ D(M_w*)`**: a member of the multiplier domain lies in the adjoint domain (same
    witness). -/
theorem AdjDom_of_dom_adj (w : Nat → Real) {Y : DLimCompletionRaw} (h : MulDom w Y) : AdjDom w Y :=
  match h with
  | ⟨Yp, hY⟩ => ⟨Yp, adj_of_dom_adj w hY⟩

-- ===========================================================================
-- TARGET 2 — the HARD inclusion `D(M_w*) ⊆ D(M_w)`  (MAXIMALITY / self-adjointness crux).
-- ===========================================================================

/-- **Adjoint-domain ⊆ domain, at the graph level** (MAXIMALITY — the crux that makes `M_w`
    SELF-adjoint, not merely symmetric): an adjoint pair `(Y, Z)` is a multiplier pair `Γ(M_w) (Y,Z)`.

    Route (per coordinate `i`): the basis vector `of e_i` lies in `D(M_w)` (`MulDom_of_mp`) with some
    image `Xp_i`.  Testing the adjoint hypothesis at `X := of e_i` gives `⟨Xp_i, Y⟩ ≈ ⟨of e_i, Z⟩`, and
    `⟨of e_i, Z⟩` IS `coord i Z`.  Separately, `Xp_i ≈ w_i•(of e_i)` because both have coordinates
    `w_j·δ_{ij}` (at `j = i` the weights literally agree; at `j ≠ i` the basis coordinate vanishes by
    `dlimBasis_ortho_bo`), so by the LEFT scalar law and `conj(w_i) = w_i`,
    `⟨Xp_i, Y⟩ ≈ ⟨w_i•(of e_i), Y⟩ ≈ w_i·⟨of e_i, Y⟩ = w_i·coord i Y`.  Chaining:
    `coord i Z ≈ w_i·coord i Y`. -/
theorem dom_of_adj_adj (w : Nat → Real) {Y Z : DLimCompletionRaw} (hYZ : AdjGraph w Y Z) :
    MulGraph w Y Z := by
  intro i
  -- The `i`-th basis vector lies in the domain, with image `Xp_i`.
  obtain ⟨Xp_i, hXp_i⟩ := MulDom_of_mp w (dlimBasis i)
  -- The real-embedded weight scalar.
  let c_i : Complex := ⟨w i, zero⟩
  -- Coordinate agreement `w_j·δ_{ij}` for the two vectors `Xp_i` and `w_i•(of e_i)`.
  have claim : ∀ j : Nat,
      Ceq (Cmul (⟨w j, zero⟩ : Complex) (coord j (DLimCompletionRaw.of (dlimBasis i))))
          (Cmul c_i (coord j (DLimCompletionRaw.of (dlimBasis i)))) := by
    intro j
    by_cases hj : j = i
    · subst hj; exact Ceq_refl _
    · -- `j ≠ i`: the basis coordinate `⟨e_j, e_i⟩` vanishes; both products collapse to `0`.
      have hcoord0 : Ceq (coord j (DLimCompletionRaw.of (dlimBasis i))) Czero :=
        Ceq_trans (coord_of j (dlimBasis i)) (dlimBasis_ortho_bo j i hj)
      exact Ceq_trans
        (Ceq_trans (Cmul_congr (Ceq_refl (⟨w j, zero⟩ : Complex)) hcoord0)
          (cmul_czero_adj (⟨w j, zero⟩ : Complex)))
        (Ceq_symm (Ceq_trans (Cmul_congr (Ceq_refl c_i) hcoord0) (cmul_czero_adj c_i)))
  -- `Xp_i ≈ w_i•(of e_i)`, via coordinate separation.
  have hsep : DLimCompletionEq Xp_i (dlimCompletionSmul c_i (DLimCompletionRaw.of (dlimBasis i))) :=
    coord_separation_hd (fun j =>
      Ceq_trans (hXp_i j)
        (Ceq_trans (claim j)
          (Ceq_symm (coord_smul j c_i (DLimCompletionRaw.of (dlimBasis i))))))
  -- `⟨Xp_i, Y⟩ ≈ w_i·⟨of e_i, Y⟩` (left scalar law + `conj(w_i) = w_i`).
  have hchain : Ceq (completedInner Xp_i Y)
      (Cmul c_i (completedInner (DLimCompletionRaw.of (dlimBasis i)) Y)) :=
    Ceq_trans (completedInner_congr hsep (DLimCompletionEq_refl Y))
      (Ceq_trans
        (completedInner_smul_left_adj c_i (DLimCompletionRaw.of (dlimBasis i)) Y)
        (Cmul_congr (Cconj_cReal_adj (w i))
          (Ceq_refl (completedInner (DLimCompletionRaw.of (dlimBasis i)) Y))))
  -- Testing the adjoint hypothesis at `of e_i`: `⟨Xp_i, Y⟩ ≈ ⟨of e_i, Z⟩ = coord i Z`.
  have hkey : Ceq (completedInner Xp_i Y)
      (completedInner (DLimCompletionRaw.of (dlimBasis i)) Z) :=
    hYZ (DLimCompletionRaw.of (dlimBasis i)) Xp_i hXp_i
  -- Chain: `coord i Z ≈ ⟨Xp_i, Y⟩ ≈ w_i·coord i Y` (both boundary reads are `coord` defeq).
  exact Ceq_trans (Ceq_symm hkey) hchain

/-- **`D(M_w*) ⊆ D(M_w)`**: a member of the adjoint domain lies in the multiplier domain (same
    witness) — MAXIMALITY of the operator. -/
theorem dom_of_adj_dom_adj (w : Nat → Real) {Y : DLimCompletionRaw} (h : AdjDom w Y) : MulDom w Y :=
  match h with
  | ⟨Z, hYZ⟩ => ⟨Z, dom_of_adj_adj w hYZ⟩

-- ===========================================================================
-- TARGET 3 — `Dom(M_w*) = Dom(M_w)`.
-- ===========================================================================

/-- **Domain equality `Dom(M_w*) = Dom(M_w)`**: the two domains coincide (both inclusions). -/
theorem dom_eq_adj (w : Nat → Real) (Y : DLimCompletionRaw) : MulDom w Y ↔ AdjDom w Y :=
  ⟨AdjDom_of_dom_adj w, dom_of_adj_dom_adj w⟩

-- ===========================================================================
-- TARGET 4 — ACTUAL graph-level SELF-ADJOINTNESS  `Γ(M_w*) = Γ(M_w)`.
-- ===========================================================================

/-- **SELF-ADJOINTNESS** `M_w* = M_w` at the graph level (reviewer gate items 6-7): the adjoint
    relation EQUALS the operator relation.  This is genuine self-adjointness — NOT symmetry, NOT a
    coordinatewise statement.  Forward is MAXIMALITY (`dom_of_adj_adj`); backward is the symmetry
    inclusion (`adj_of_dom_adj`). -/
theorem selfadjoint_adj (w : Nat → Real) (Y Z : DLimCompletionRaw) :
    AdjGraph w Y Z ↔ MulGraph w Y Z :=
  ⟨fun hYZ => dom_of_adj_adj w hYZ, fun hYZ => adj_of_dom_adj w hYZ⟩


-- ===========================================================================
-- Adjoint congruence, adjoint-witness UNIQUENESS, and the PACKAGED self-adjointness
-- (explicitly incorporating the density and closed-graph theorems).
-- ===========================================================================

/-- The adjoint graph descends to the completion setoid. -/
theorem AdjGraph_congr_adj (w : Nat → Real) {Y Y' Z Z' : DLimCompletionRaw}
    (hY : DLimCompletionEq Y Y') (hZ : DLimCompletionEq Z Z') (h : AdjGraph w Y Z) :
    AdjGraph w Y' Z' := by
  intro X Xp hX
  exact Ceq_trans (Ceq_symm (completedInner_congr (DLimCompletionEq_refl Xp) hY))
    (Ceq_trans (h X Xp hX) (completedInner_congr (DLimCompletionEq_refl X) hZ))

/-- **Adjoint-output UNIQUENESS**: an adjoint witness is unique up to the setoid. Test the two adjoint
    relations against the dense basis `of (e_i)` (in the domain via `MulDom_of_mp`): both force
    `coord i Z ≈ ⟨Xp_i, Y⟩ ≈ coord i Z'`, then coordinate separation. -/
theorem adj_unique_adj (w : Nat → Real) {Y Z Z' : DLimCompletionRaw}
    (h : AdjGraph w Y Z) (h' : AdjGraph w Y Z') : DLimCompletionEq Z Z' := by
  refine coord_separation_hd (fun i => ?_)
  obtain ⟨Xp, hXp⟩ := MulDom_of_mp w (dlimBasis i)
  exact Ceq_trans (Ceq_symm (h (DLimCompletionRaw.of (dlimBasis i)) Xp hXp))
    (h' (DLimCompletionRaw.of (dlimBasis i)) Xp hXp)

/-- **The real-weight diagonal multiplier is a genuine self-adjoint operator.** A single packaged
    predicate bundling: the domain is DENSE, the graph is CLOSED under completion convergence, the adjoint
    graph EQUALS the operator graph (self-adjointness `M_w* = M_w`), and `Dom(M_w*) = Dom(M_w)`. Every field
    is an already-proven theorem — density (`MulDom_dense_mp`), closedness (`MulGraph_closed_cl`),
    graph self-adjointness (`selfadjoint_adj`), domain equality (`dom_eq_adj`). -/
structure MultiplierSelfAdjoint (w : Nat → Real) : Prop where
  dense : ∀ (X : DLimCompletionRaw) (k : Nat), ∃ a : DLimRaw,
    MulDom w (DLimCompletionRaw.of a) ∧
      Rle (completedDist2 X (DLimCompletionRaw.of a)) (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k))
  closed : ∀ (Xs Ys : Nat → DLimCompletionRaw) (X Y : DLimCompletionRaw),
    CompletionTendsTo Xs X → CompletionTendsTo Ys Y → (∀ n : Nat, MulGraph w (Xs n) (Ys n)) →
      MulGraph w X Y
  selfAdjointGraph : ∀ Y Z : DLimCompletionRaw, AdjGraph w Y Z ↔ MulGraph w Y Z
  domEq : ∀ Y : DLimCompletionRaw, MulDom w Y ↔ AdjDom w Y

/-- **The packaged self-adjointness theorem** for every real weight `w`: `M_w` is a densely-defined,
    closed, self-adjoint diagonal multiplier — assembled from the density, closed-graph, adjoint-domain,
    and graph-equality theorems. -/
theorem multiplier_selfAdjoint (w : Nat → Real) : MultiplierSelfAdjoint w where
  dense := MulDom_dense_mp w
  closed := MulGraph_closed_cl w
  selfAdjointGraph := selfadjoint_adj w
  domEq := dom_eq_adj w

end UOR.Bridge.F1Square.Square
