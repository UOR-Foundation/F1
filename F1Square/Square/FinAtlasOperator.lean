/-
F1 square — **the first genuine SYMMETRIC (Hermitian) Atlas operator on the finite-support pre-Hilbert
core** (focus item 2 of the Atlas-derived Hilbert–Pólya construction). This is where the operator
first CONSUMES the Atlas: the sourced spectral operator `M = (O+2)I − T·Π_T − O·Π_O` (Atlas §5/§6.6,
`atlasEig`/`atlasM`) is realized as a DIAGONAL OBSERVABLE `A_N` on the genuine complex inner-product
space `CVec N`, SYMMETRIC with respect to the POSITIVE-DEFINITE metric `cInner` (the metric half
built in `FinInnerProduct`) — the Atlas is the observable, NOT the metric.

PRECISE SCOPE — SYMMETRY, NOT SELF-ADJOINTNESS. What is proved here is the symmetry (Hermitian-form)
identity `⟨Ax,y⟩ = ⟨x,Ay⟩` (`diagOp_herm`). This is NOT self-adjointness in the operator-theoretic
sense: there is no Hilbert completion, no operator domain, no adjoint, no domain equality
`D(A) = D(A*)`, and no closure here. Self-adjointness (and essential self-adjointness) are the LATER
focus items 3–4, and are not claimed by anything in this file. The genuine content is that the Atlas
observable is a bona fide SYMMETRIC operator on the positive metric — replacing the vacuous nominal
`NominalSelfAdjoint` predicate with a real (if partial) operator prerequisite.

THE HILBERT–PÓLYA FRAMING (as the operator contract demands). The Atlas signature `Σ = {10,7,2,−1}`
is INDEFINITE (`atlasM_indefinite`, in `AtlasSpectrum`), so `atlasM` cannot BE a Hilbert metric. Here
it is treated correctly: `cInner` (positive-definite, proved) is the Hilbert metric, and `atlasM` is a
SYMMETRIC operator (observable) on that space. A symmetric operator MAY be indefinite — symmetry is a
property of the form, separate from definiteness. The observable genuinely carries the indefinite
spectrum: within the sourced 24-carrier it has the Atlas signature `(10,14)` (`atlasObsEig_signature`
— ten positive, fourteen negative eigendirections), yet it is Hermitian on the positive metric. The
operator IS the sourced diagonal (`atlasWeight_eq_atlasM_diag`: on `i<24` the weight equals `atlasM
i i`).

WHAT IS PROVED (a real, if partial, operator prerequisite — not an interface):
- `diagOp w N` is a `ℂ`-linear, setoid-respecting operator (`diagOp_congr`/`diagOp_add`/`diagOp_smul`)
  and, for a REAL diagonal `w`, is SYMMETRIC w.r.t. `cInner` (`diagOp_herm`);
- it is COMPATIBLE with the inclusion tower — `A_M ∘ ι_{N,M} ≈ ι_{N,M} ∘ A_N` (`diagOp_cvInc`), the
  index-intrinsic diagonal commuting with `0`-padding;
- hence it DESCENDS to the direct-limit pre-Hilbert object `dlimPreHilbert` as a symmetric operator
  `dlimAtlas` (well-defined `dlimAtlas_wd`, linear `dlimAtlas_add`/`dlimAtlas_smul`, symmetric
  `dlimAtlas_herm`) — the FIRST downstream consumer of `dlimPreHilbert`. Both are packaged as the
  typed `PreHilbertSymOp` (`atlasFinOp`, `atlasDLimOp`).

THE EXPLICIT OPEN SEAM — THIS IS THE FINITE SEED `M₂₄ ⊕ 0`, NOT A SCALE LIFT. `atlasEig`'s `−1` tail is
NOT an unbounded Atlas spectrum; it is sourced only for the 24-dimensional carrier. So the observable
weight `atlasObsEig` is `atlasEig` on `i < 24` and `0` for `i ≥ 24`
(`atlasObsEig_sourced`/`atlasObsEig_seam`): the operator carries the genuine 24-carrier spectrum and
is the ZERO observable beyond, never a fabricated `−1` tail. It therefore VANISHES off the 24-carrier
(`atlasObs_vanishes_off_carrier`) — i.e. this is exactly the finite seed `M₂₄ ⊕ 0`, a BOUNDED,
finite-rank (rank ≤ 24) observable, NOT a plausible HP operator. The genuine UNBOUNDED, refinement-
sourced Atlas scale-lift (the addressing tower `A_∞`, itself degenerate as a fixture) is the exposed
open seam, not built here — and completing `M₂₄ ⊕ 0` cannot itself close the HP crux. There is no
spectral-reality → zero correspondence and no unbounded generator; the crux (RH) stays `none`.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Square.FinDirectLimit
import F1Square.Square.AtlasSpectralCore

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

/-- The embedding of a real `≈ 0` is the complex zero (`⟨r,0⟩ ≈ ⟨0,0⟩ = Czero`). -/
private theorem Cofreal_eq_zero {r : Real} (h : Req r zero) : Ceq (Cofreal r) Czero :=
  ⟨h, Req_refl zero⟩

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
    the genuine symmetry identity, PROVED — replacing the vacuous nominal predicate. It is NOT
    self-adjointness: no domain / adjoint / closure is asserted (those are focus items 3–4). -/
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
-- The sourced Atlas weight (with the explicit open seam) and its operator.
-- ===========================================================================

/-- **The Atlas observable weight**: the sourced spectrum `atlasEig` on the 24-carrier, and `0`
    beyond (the honest "not sourced" value, exposed as the open scale-lift seam — NOT the `−1` tail).
    Keyed by the global index, so it defines a coherent operator on every stage of the tower. -/
def atlasObsEig (i : Nat) : Int := if i < 24 then atlasEig i else 0

/-- On the sourced 24-carrier the observable weight IS the Atlas spectrum. -/
theorem atlasObsEig_sourced (i : Nat) (h : i < 24) : atlasObsEig i = atlasEig i := by
  show (if i < 24 then atlasEig i else (0 : Int)) = atlasEig i
  rw [if_pos h]

/-- **The exposed open seam**: beyond the sourced carrier (`i ≥ 24`) the weight is `0` — the genuine
    unbounded scale-lift is NOT built, so the observable does not act there. Making the boundary of
    what is sourced explicit, not silently extrapolating `atlasEig`'s `−1` tail. -/
theorem atlasObsEig_seam (i : Nat) (h : 24 ≤ i) : atlasObsEig i = 0 := by
  show (if i < 24 then atlasEig i else (0 : Int)) = 0
  rw [if_neg (Nat.not_lt.mpr h)]

/-- **The observable carries the genuine INDEFINITE Atlas signature `(10,14)`** on the sourced
    carrier: ten positive eigendirections (`λ = 10,7,2`) and fourteen negative (`λ = −1`). So the
    self-adjoint operator is genuinely indefinite (mirrors `atlasM_signature`), yet Hermitian on the
    POSITIVE metric `cInner` — the Hilbert–Pólya framing. Computed. -/
theorem atlasObsEig_signature :
    ((List.range 24).filter (fun i => decide (0 < atlasObsEig i))).length = 10
    ∧ ((List.range 24).filter (fun i => decide (atlasObsEig i < 0))).length = 14 := by decide

/-- The negative (reflection) eigenspace `−1` is genuinely carried WITHIN the sourced carrier
    (`i = 10, 23`), while the tail (`i = 24`) is honestly zeroed — the seam boundary, computed. -/
theorem atlasObsEig_carrier_and_seam :
    atlasObsEig 0 = 10 ∧ atlasObsEig 10 = -1 ∧ atlasObsEig 23 = -1 ∧ atlasObsEig 24 = 0 := by decide

/-- The real observable weight `w(i) = atlasObsEig i` as a `Real`. -/
def atlasWeight (i : Nat) : Real := ofQ ⟨atlasObsEig i, 1⟩ Nat.one_pos

/-- **Provenance**: on the sourced carrier the operator's weight equals the Atlas spectral-operator
    diagonal `atlasM i i` — the observable genuinely IS the sourced `M` (§5/§6.6), acting on the
    positive metric. -/
theorem atlasWeight_eq_atlasM_diag (i : Nat) (h : i < 24) : Req (atlasWeight i) (atlasM i i) := by
  have hM : atlasM i i = ofQ ⟨atlasEig i, 1⟩ Nat.one_pos := if_pos rfl
  show Req (ofQ ⟨atlasObsEig i, 1⟩ Nat.one_pos) (atlasM i i)
  rw [hM, atlasObsEig_sourced i h]
  exact Req_refl _

/-- Off the sourced carrier (`i ≥ 24`) the observable weight is the real `0` — the seam value as a
    real number (from `atlasObsEig_seam`). -/
theorem atlasWeight_seam (i : Nat) (h : 24 ≤ i) : Req (atlasWeight i) zero := by
  show Req (ofQ ⟨atlasObsEig i, 1⟩ Nat.one_pos) zero
  rw [atlasObsEig_seam i h]
  exact Req_of_seq_Qeq (fun _ => by show Qeq (⟨0, 1⟩ : Q) ⟨0, 1⟩; decide)

/-- **THE OPERATOR IS THE FINITE SEED `M₂₄ ⊕ 0`**: on every coordinate `i ≥ 24` the Atlas observable
    output VANISHES (`atlasWeight i · xᵢ ≈ 0`, since the seam weight is `0`). So `A_N` is supported on
    the first 24 coordinates — a BOUNDED, finite-rank (rank ≤ 24) diagonal, exactly the sourced seed,
    NOT an unbounded scale-lift. Turns the "finite seed" characterization from documentation into a
    theorem. -/
theorem atlasObs_vanishes_off_carrier (N : Nat) (x : CVec N) (i : Fin N) (h : 24 ≤ i.val) :
    Ceq ((diagOp atlasWeight N x) i) Czero := by
  show Ceq (Cmul (Cofreal (atlasWeight i.val)) (x i)) Czero
  refine Ceq_trans (Cmul_congr (Cofreal_eq_zero (atlasWeight_seam i.val h)) (Ceq_refl (x i))) ?_
  exact Ceq_trans (Cmul_comm Czero (x i)) (cmul_czero_loc (x i))

/-- **The Atlas observable on the finite stage `CVec N`**, packaged as a symmetric operator on
    `finPreHilbert N`. For `N = 24` this is the full sourced spectral operator; the same object at
    every `N` forms the compatible family (`diagOp_cvInc`). -/
def atlasFinOp (N : Nat) : PreHilbertSymOp (finPreHilbert N) where
  op := diagOp atlasWeight N
  op_congr := fun h => diagOp_congr N atlasWeight h
  op_add := diagOp_add N atlasWeight
  op_smul := diagOp_smul N atlasWeight
  op_herm := diagOp_herm N atlasWeight

-- ===========================================================================
-- The induced symmetric operator on the direct-limit pre-Hilbert object
-- `dlimPreHilbert` — the first downstream consumer of the colimit.
-- ===========================================================================

/-- The Atlas observable on the direct limit: act on the representative at its own stage. Well-defined
    (`dlimAtlas_wd`) because `diagOp` is tower-compatible. -/
def dlimAtlas (a : DLimRaw) : DLimRaw := ⟨a.stage, diagOp atlasWeight a.stage a.vec⟩

/-- The colimit operator is well-defined against `DLimEq`: representatives agreeing at a common stage
    map to representatives agreeing there (tower compatibility + `diagOp_congr`). -/
theorem dlimAtlas_wd {a a' : DLimRaw} (h : DLimEq a a') : DLimEq (dlimAtlas a) (dlimAtlas a') := by
  obtain ⟨K, haK, ha'K, hAA⟩ := h
  refine ⟨K, haK, ha'K, ?_⟩
  exact CVecEq_trans (CVecEq_symm (diagOp_cvInc haK atlasWeight a.vec))
    (CVecEq_trans (diagOp_congr K atlasWeight hAA)
      (diagOp_cvInc ha'K atlasWeight a'.vec))

/-- The colimit operator is additive. -/
theorem dlimAtlas_add (a b : DLimRaw) :
    DLimEq (dlimAtlas (dlimAdd a b)) (dlimAdd (dlimAtlas a) (dlimAtlas b)) := by
  have ha : a.stage ≤ max a.stage b.stage := Nat.le_max_left _ _
  have hb : b.stage ≤ max a.stage b.stage := Nat.le_max_right _ _
  refine ⟨max a.stage b.stage, Nat.le_refl _, Nat.le_refl _, ?_⟩
  refine CVecEq_trans (cvInc_id _) (CVecEq_trans ?_ (CVecEq_symm (cvInc_id _)))
  refine CVecEq_trans (diagOp_add (max a.stage b.stage) atlasWeight _ _) ?_
  exact cvAdd_congr (diagOp_cvInc ha atlasWeight a.vec) (diagOp_cvInc hb atlasWeight b.vec)

/-- The colimit operator commutes with scalar multiplication. -/
theorem dlimAtlas_smul (c : Complex) (a : DLimRaw) :
    DLimEq (dlimAtlas (dlimSmul c a)) (dlimSmul c (dlimAtlas a)) :=
  ⟨a.stage, Nat.le_refl _, Nat.le_refl _,
    CVecEq_trans (cvInc_id _)
      (CVecEq_trans (diagOp_smul a.stage atlasWeight c a.vec) (CVecEq_symm (cvInc_id _)))⟩

/-- **The colimit operator is SYMMETRIC** w.r.t. the colimit metric `dlimInner`: evaluate both
    pairings at the common stage `max`, push the operator through the inclusions (`diagOp_cvInc`),
    and apply the stagewise symmetry `diagOp_herm`. This is the FIRST genuine symmetric Atlas operator
    on the finite-support core, induced on the direct-limit pre-Hilbert object (symmetry only — not
    self-adjointness, which needs the completion and adjoint of focus items 3–4). -/
theorem dlimAtlas_herm (a b : DLimRaw) :
    Ceq (dlimInner (dlimAtlas a) b) (dlimInner a (dlimAtlas b)) := by
  have haK : a.stage ≤ max a.stage b.stage := Nat.le_max_left _ _
  have hbK : b.stage ≤ max a.stage b.stage := Nat.le_max_right _ _
  refine Ceq_trans (Ceq_symm (dlimInner_eval (dlimAtlas a) b haK hbK)) ?_
  refine Ceq_trans (cInner_congr (CVecEq_symm (diagOp_cvInc haK atlasWeight a.vec))
    (CVecEq_refl _)) ?_
  refine Ceq_trans (diagOp_herm (max a.stage b.stage) atlasWeight
    (cvInc haK a.vec) (cvInc hbK b.vec)) ?_
  refine Ceq_trans (cInner_congr (CVecEq_refl _) (diagOp_cvInc hbK atlasWeight b.vec)) ?_
  exact dlimInner_eval a (dlimAtlas b) haK hbK

/-- **The Atlas observable on the direct limit**, packaged as a symmetric operator on
    `dlimPreHilbert` — the first downstream mathematical consumer of the packaged colimit pre-Hilbert
    object. It is `ℂ`-linear and SYMMETRIC on the POSITIVE colimit metric, and indefinite as an
    observable (`atlasObsEig_signature`). It is the finite seed `M₂₄ ⊕ 0` (bounded, finite-rank); the
    unbounded scale-lift and self-adjointness remain the exposed open seams. -/
def atlasDLimOp : PreHilbertSymOp dlimPreHilbert where
  op := dlimAtlas
  op_congr := fun h => dlimAtlas_wd h
  op_add := dlimAtlas_add
  op_smul := dlimAtlas_smul
  op_herm := dlimAtlas_herm

end UOR.Bridge.F1Square.Square
