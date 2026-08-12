/-
F1 square — **generic diagonal-operator theory on the finite-support pre-Hilbert tower**. This module
factors out the reusable, weight-agnostic operator machinery so it does NOT depend on any particular
diagonal (Atlas seed, block-ladder, or otherwise). Nothing here mentions `atlasEig`, a scale ladder,
or any spectrum; the weight is an abstract `w : ℕ → ℝ`.

WHAT IS PROVIDED:
- `Cofreal r = ⟨r, 0⟩`: the real→ℂ embedding.
- `diagOp w N`: the diagonal operator on `CVec N` multiplying coordinate `i` by the real scalar
  `w i.val` (keyed by the GLOBAL index so one `w` acts coherently across every stage of the `cvInc`
  tower). It is setoid-respecting and ℂ-linear (`diagOp_congr`/`diagOp_add`/`diagOp_smul`), SYMMETRIC
  w.r.t. the positive metric `cInner` for a REAL weight (`diagOp_herm`: `⟨Ax,y⟩ = ⟨x,Ay⟩`), and
  tower-compatible (`diagOp_cvInc`: `A_M ∘ ι ≈ ι ∘ A_N`, the index-intrinsic diagonal commuting with
  `0`-padding). SYMMETRY only — no domain/adjoint/closure, so NOT self-adjointness.
- `PreHilbertSymOp H`: a bundled symmetric operator on a finite pre-Hilbert space.
- `dlimDiagW w`: the descent of `diagOp w` to the direct-limit pre-Hilbert space `dlimPreHilbert`,
  well-defined and ℂ-linear and symmetric (`dlimDiagW_wd`/`_add`/`_smul`/`_herm`).
- The standard coordinate basis `dlimBasis i` (normalized, `dlimBasis_normalized`) and the EIGENPAIR
  `dlimDiagW_eigen`: `A eᵢ ≈ wᵢ · eᵢ` — the genuine operator-theoretic content tying the diagonal
  weights to `dlimDiagW` as eigenvalues on a normalized point spectrum.
- `OpNormBounded T C`: the operator-norm-bound predicate `⟨Tx,Tx⟩ ≤ C²·⟨x,x⟩`.

This is the reusable substrate for the ℓ² completion / adjoint / self-adjointness arc; it is generic
and carries no spectrum or Atlas provenance. Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`,
choice-free; the cone is `FinDirectLimit`'s zeta-free cone. Crux `none`.
-/

import F1Square.Square.FinDirectLimit
import F1Square.Square.DlimBasisCore

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

set_option maxHeartbeats 1000000

-- ===========================================================================
-- Local zeta-free trivialities (private; public copies live in Pi/ζ-tainted modules).
-- ===========================================================================

/-- `−0 ≈ 0` (local, zeta-free). -/
private theorem rneg_zero_loc : Req (Rneg zero) zero :=
  Req_of_seq_Qeq (fun _ => by show Qeq (neg (⟨0, 1⟩ : Q)) ⟨0, 1⟩; decide)

/-- `z · 0 ≈ 0` (local copy; the public `cmul_czero` is in `FinInnerProduct`, private). -/
private theorem cmul_czero_loc (z : Complex) : Ceq (Cmul z Czero) Czero :=
  ⟨Req_trans (Radd_congr (Rmul_zero z.re) (Rneg_congr (Rmul_zero z.im))) (Radd_neg zero),
   Req_trans (Radd_congr (Rmul_zero z.re) (Rmul_zero z.im)) (Radd_zero zero)⟩

/-- Left-commutativity `a·(c·b) ≈ c·(a·b)` (local copy). -/
private theorem cmul_left_comm_loc (a c b : Complex) :
    Ceq (Cmul a (Cmul c b)) (Cmul c (Cmul a b)) :=
  Ceq_trans (Ceq_symm (Cmul_assoc a c b))
    (Ceq_trans (Cmul_congr (Cmul_comm a c) (Ceq_refl b)) (Cmul_assoc c a b))

-- ===========================================================================
-- The real-scalar embedding and the diagonal operator `diagOp` (generic real weight).
-- ===========================================================================

/-- The embedding of a real scalar into `ℂ` as `⟨r, 0⟩`. -/
def Cofreal (r : Real) : Complex := ⟨r, zero⟩

/-- The conjugate of a real embedding is itself (`conj ⟨r,0⟩ = ⟨r,−0⟩ ≈ ⟨r,0⟩`). -/
private theorem Cconj_Cofreal (r : Real) : Ceq (Cconj (Cofreal r)) (Cofreal r) :=
  ⟨Req_refl _, rneg_zero_loc⟩

/-- **The diagonal operator** with an index-intrinsic real weight `w : ℕ → ℝ`: multiplies coordinate
    `i` by the real scalar `w i`. The weight is keyed by the GLOBAL index `i.val`, so the same `w`
    acts coherently across every stage of the inclusion tower. -/
def diagOp (w : Nat → Real) (N : Nat) (x : CVec N) : CVec N :=
  fun i => Cmul (Cofreal (w i.val)) (x i)

/-- The diagonal operator respects the vector setoid. -/
theorem diagOp_congr (N : Nat) (w : Nat → Real) {x y : CVec N} (h : CVecEq x y) :
    CVecEq (diagOp w N x) (diagOp w N y) := fun i => Cmul_congr (Ceq_refl _) (h i)

/-- The diagonal operator is additive (linearity, part 1). -/
theorem diagOp_add (N : Nat) (w : Nat → Real) (x y : CVec N) :
    CVecEq (diagOp w N (cvAdd x y)) (cvAdd (diagOp w N x) (diagOp w N y)) :=
  fun i => Cmul_distrib (Cofreal (w i.val)) (x i) (y i)

/-- The diagonal operator commutes with scalar multiplication (linearity, part 2). -/
theorem diagOp_smul (N : Nat) (w : Nat → Real) (c : Complex) (x : CVec N) :
    CVecEq (diagOp w N (cvSmul c x)) (cvSmul c (diagOp w N x)) :=
  fun i => cmul_left_comm_loc (Cofreal (w i.val)) c (x i)

/-- The Hermitian diagonal summand identity: `conj(w·a)·b ≈ conj(a)·(w·b)` for a REAL weight `w`
    (the conjugate of the real embedding is itself). -/
private theorem herm_term (r : Real) (a b : Complex) :
    Ceq (Cmul (Cconj (Cmul (Cofreal r) a)) b) (Cmul (Cconj a) (Cmul (Cofreal r) b)) :=
  Ceq_trans
    (Cmul_congr
      (Ceq_trans (Cconj_Cmul (Cofreal r) a)
        (Cmul_congr (Cconj_Cofreal r) (Ceq_refl (Cconj a))))
      (Ceq_refl b))
    (Ceq_trans
      (Cmul_congr (Cmul_comm (Cofreal r) (Cconj a)) (Ceq_refl b))
      (Cmul_assoc (Cconj a) (Cofreal r) b))

/-- **The diagonal operator is SYMMETRIC (Hermitian form)** w.r.t. the positive metric `cInner`:
    `⟨A x, y⟩ = ⟨x, A y⟩`. Termwise, `conj(w·xᵢ)·yᵢ ≈ conj(xᵢ)·(w·yᵢ)` because `w` is real. This is
    the genuine symmetry identity, PROVED. It is NOT self-adjointness: no domain / adjoint / closure
    is asserted. -/
theorem diagOp_herm (N : Nat) (w : Nat → Real) (x y : CVec N) :
    Ceq (cInner N (diagOp w N x) y) (cInner N x (diagOp w N y)) := by
  show Ceq (cvecSum N (fun i => Cmul (Cconj (Cmul (Cofreal (w i.val)) (x i))) (y i)))
           (cvecSum N (fun i => Cmul (Cconj (x i)) (Cmul (Cofreal (w i.val)) (y i))))
  exact cvecSum_congr N _ _ (fun i => herm_term (w i.val) (x i) (y i))

/-- **Tower compatibility** `A_M ∘ ι_{N,M} ≈ ι_{N,M} ∘ A_N`: the index-intrinsic diagonal commutes
    with the `0`-padding inclusion (on the padded coordinates it multiplies `0`). So the `diagOp`
    family is a morphism of the directed system — the property that lets it descend to the colimit. -/
theorem diagOp_cvInc {N M : Nat} (h : N ≤ M) (w : Nat → Real) (x : CVec N) :
    CVecEq (diagOp w M (cvInc h x)) (cvInc h (diagOp w N x)) := by
  intro i
  by_cases hi : i.val < N
  · simp only [diagOp, cvInc, dif_pos hi]; exact Ceq_refl _
  · simp only [diagOp, cvInc, dif_neg hi]; exact cmul_czero_loc _

-- ===========================================================================
-- The typed symmetric-operator object on a `FinPreHilbert`.
-- ===========================================================================

/-- A **bundled symmetric operator** on a finite pre-Hilbert space `H`: a setoid-respecting
    `ℂ`-linear map that is SYMMETRIC (`⟨Ax,y⟩ = ⟨x,Ay⟩`, `op_herm`). Symmetry only — this bundles no
    domain, adjoint, or closure, so it does NOT assert self-adjointness. The operator analogue of
    `LinIsometry`. -/
structure PreHilbertSymOp (H : FinPreHilbert) where
  op : H.V → H.V
  op_congr : ∀ {x y}, H.veq x y → H.veq (op x) (op y)
  op_add : ∀ x y, H.veq (op (H.add x y)) (H.add (op x) (op y))
  op_smul : ∀ c x, H.veq (op (H.smul c x)) (H.smul c (op x))
  op_herm : ∀ x y, Ceq (H.inner (op x) y) (H.inner x (op y))

-- ===========================================================================
-- The generic descent of a real-diagonal to the direct-limit pre-Hilbert space.
-- ===========================================================================

/-- The generic descent of `diagOp w` to a colimit representative (its own stage). -/
def dlimDiagW (w : Nat → Real) (a : DLimRaw) : DLimRaw := ⟨a.stage, diagOp w a.stage a.vec⟩

/-- The generic colimit diagonal is well-defined against `DLimEq` (tower compatibility). -/
theorem dlimDiagW_wd (w : Nat → Real) {a a' : DLimRaw} (h : DLimEq a a') :
    DLimEq (dlimDiagW w a) (dlimDiagW w a') := by
  obtain ⟨K, haK, ha'K, hAA⟩ := h
  refine ⟨K, haK, ha'K, ?_⟩
  exact CVecEq_trans (CVecEq_symm (diagOp_cvInc haK w a.vec))
    (CVecEq_trans (diagOp_congr K w hAA) (diagOp_cvInc ha'K w a'.vec))

/-- The generic colimit diagonal is additive. -/
theorem dlimDiagW_add (w : Nat → Real) (a b : DLimRaw) :
    DLimEq (dlimDiagW w (dlimAdd a b)) (dlimAdd (dlimDiagW w a) (dlimDiagW w b)) := by
  have ha : a.stage ≤ max a.stage b.stage := Nat.le_max_left _ _
  have hb : b.stage ≤ max a.stage b.stage := Nat.le_max_right _ _
  refine ⟨max a.stage b.stage, Nat.le_refl _, Nat.le_refl _, ?_⟩
  refine CVecEq_trans (cvInc_id _) (CVecEq_trans ?_ (CVecEq_symm (cvInc_id _)))
  refine CVecEq_trans (diagOp_add (max a.stage b.stage) w _ _) ?_
  exact cvAdd_congr (diagOp_cvInc ha w a.vec) (diagOp_cvInc hb w b.vec)

/-- The generic colimit diagonal commutes with scalar multiplication. -/
theorem dlimDiagW_smul (w : Nat → Real) (c : Complex) (a : DLimRaw) :
    DLimEq (dlimDiagW w (dlimSmul c a)) (dlimSmul c (dlimDiagW w a)) :=
  ⟨a.stage, Nat.le_refl _, Nat.le_refl _,
    CVecEq_trans (cvInc_id _)
      (CVecEq_trans (diagOp_smul a.stage w c a.vec) (CVecEq_symm (cvInc_id _)))⟩

/-- The generic colimit diagonal is SYMMETRIC on `dlimInner`. -/
theorem dlimDiagW_herm (w : Nat → Real) (a b : DLimRaw) :
    Ceq (dlimInner (dlimDiagW w a) b) (dlimInner a (dlimDiagW w b)) := by
  have haK : a.stage ≤ max a.stage b.stage := Nat.le_max_left _ _
  have hbK : b.stage ≤ max a.stage b.stage := Nat.le_max_right _ _
  refine Ceq_trans (Ceq_symm (dlimInner_eval (dlimDiagW w a) b haK hbK)) ?_
  refine Ceq_trans (cInner_congr (CVecEq_symm (diagOp_cvInc haK w a.vec)) (CVecEq_refl _)) ?_
  refine Ceq_trans (diagOp_herm (max a.stage b.stage) w (cvInc haK a.vec) (cvInc hbK b.vec)) ?_
  refine Ceq_trans (cInner_congr (CVecEq_refl _) (diagOp_cvInc hbK w b.vec)) ?_
  exact dlimInner_eval a (dlimDiagW w b) haK hbK

-- ===========================================================================
-- Normalized coordinate basis vectors and the EIGENPAIR `A eᵢ ≈ wᵢ · eᵢ` — the
-- operator-theoretic content connecting the diagonal weights to `dlimDiagW` as a
-- normalized point spectrum.
-- ===========================================================================

/-- `conj 1 ≈ 1`. -/
private theorem Cconj_Cone_loc : Ceq (Cconj Cone) Cone := ⟨Req_refl _, rneg_zero_loc⟩

/-- **THE EIGENPAIR** `A eᵢ ≈ wᵢ · eᵢ`: the generic real-diagonal operator `dlimDiagW w` sends the
    `i`-th basis vector to `wᵢ` times itself. At the spike both sides are `w·1`; off it both sides are
    `w·0 ≈ 0`. So every diagonal weight `wᵢ` is a genuine eigenvalue on the normalized vector `eᵢ`. -/
theorem dlimDiagW_eigen (w : Nat → Real) (i : Nat) :
    DLimEq (dlimDiagW w (dlimBasis i)) (dlimSmul (Cofreal (w i)) (dlimBasis i)) := by
  refine ⟨i + 1, Nat.le_refl _, Nat.le_refl _, ?_⟩
  refine CVecEq_trans (cvInc_id _) (CVecEq_trans ?_ (CVecEq_symm (cvInc_id _)))
  intro k
  show Ceq (Cmul (Cofreal (w k.val)) (if k.val = i then Cone else Czero))
           (Cmul (Cofreal (w i)) (if k.val = i then Cone else Czero))
  by_cases hk : k.val = i
  · rw [if_pos hk, hk]; exact Ceq_refl _
  · rw [if_neg hk]
    exact Ceq_trans (cmul_czero_loc _) (Ceq_symm (cmul_czero_loc _))

-- ===========================================================================
-- The operator-norm-bound predicate (for the ℓ²-completion / boundedness theory).
-- ===========================================================================

/-- **Operator norm bound**: `T` is bounded by `C` iff `⟨Tx, Tx⟩ ≤ C²·⟨x, x⟩` for every colimit
    vector (real parts; both are real by symmetry/positivity). The predicate whose FAILURE on the
    normalized eigenvectors is genuine operator-theoretic unboundedness. -/
def OpNormBounded (T : DLimRaw → DLimRaw) (C : Real) : Prop :=
  ∀ a, Rle (dlimInner (T a) (T a)).re (Rmul (Rmul C C) (dlimInner a a).re)

/-- **The squared norm of `A eᵢ` is `wᵢ²`**: from the eigenpair `A eᵢ ≈ wᵢ·eᵢ` and the normalization
    `⟨eᵢ,eᵢ⟩≈1`, `⟨A eᵢ, A eᵢ⟩ = conj(wᵢ)·wᵢ·⟨eᵢ,eᵢ⟩ = wᵢ²` (`wᵢ` real). The quantitative bridge from
    the operator's action on the unit vector `eᵢ` to the weight. -/
theorem dlimDiagW_eigen_normSq (w : Nat → Real) (i : Nat) :
    Req (dlimInner (dlimDiagW w (dlimBasis i)) (dlimDiagW w (dlimBasis i))).re
        (Rmul (w i) (w i)) := by
  have key : Ceq (dlimInner (dlimDiagW w (dlimBasis i)) (dlimDiagW w (dlimBasis i)))
                 (Cmul (Cofreal (w i)) (Cofreal (w i))) := by
    refine Ceq_trans (dlimInner_wd (dlimDiagW_eigen w i) (dlimDiagW_eigen w i)) ?_
    refine Ceq_trans (dlimInner_smul_right (Cofreal (w i))
      (dlimSmul (Cofreal (w i)) (dlimBasis i)) (dlimBasis i)) ?_
    refine Cmul_congr (Ceq_refl (Cofreal (w i))) ?_
    refine Ceq_trans (dlimInner_conj (dlimSmul (Cofreal (w i)) (dlimBasis i)) (dlimBasis i)) ?_
    refine Ceq_trans (Cconj_congr
      (dlimInner_smul_right (Cofreal (w i)) (dlimBasis i) (dlimBasis i))) ?_
    refine Ceq_trans (Cconj_Cmul (Cofreal (w i)) (dlimInner (dlimBasis i) (dlimBasis i))) ?_
    refine Ceq_trans (Cmul_congr (Cconj_Cofreal (w i))
      (Ceq_trans (Cconj_congr (dlimBasis_normalized i)) Cconj_Cone_loc)) ?_
    exact Cmul_one (Cofreal (w i))
  refine Req_trans key.1 ?_
  show Req (Rsub (Rmul (w i) (w i)) (Rmul zero zero)) (Rmul (w i) (w i))
  exact Req_trans (Rsub_congr (Req_refl _) (Rmul_zero zero)) (Rsub_zero _)

end UOR.Bridge.F1Square.Square
