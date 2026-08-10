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
NOT an unbounded Atlas spectrum; it is sourced only for the 24-dimensional carrier. The seed is now
TYPED over `Fin 24` (`atlasSeedEig`/`atlasSeedWeight`/`atlasSeedOp`), so the unsourced tail is
UNREPRESENTABLE by construction; the `ℕ`-indexed tower weight `atlasObsEig` is `atlasEig` on `i < 24`
and `0` for `i ≥ 24` (`atlasObsEig_sourced`/`atlasObsEig_seam`), agreeing with the seed on the carrier
(`atlasSeedOp_eq`) and vanishing beyond (`atlasObs_vanishes_off_carrier`). The seed restricts `M` to
the carrier at the DIAGONAL-WEIGHT level (`atlasSeedWeight_eq_atlasM`: the weight equals `atlasM i i`;
a matrix-action agreement with `atlasSeedOp` is `atlasSeedOp_eq`), and its eigenvalue VALUES are
integer-bounded in `[−1,10]` (`atlasSeedEig_bounded`/`atlasEig_range` — an entry bound, not a
formalized operator-norm/finite-rank theorem). Being supported on the 24-carrier and bounded-valued,
it is not a plausible HP operator.

WHY NO UNBOUNDED SOURCED LIFT (verified, not assumed). A genuine Hilbert–Pólya operator must be
UNBOUNDED; the sourced Atlas supplies no such diagonal. The addressing/refinement tower is a finite
fixture that degenerates (`AtlasAddressing.atlasModulus_degenerate`); there is no unbounded prime
enumeration `ℕ → ℕ` with primality proofs in the repo (only Euclid's *lemma*); the one sourced
unbounded object, `Cohomology.orbitShift p k = k·log p`, is a single-prime scalar LENGTH ("not itself a
Hilbert-space operator") that is not aggregated into a diagonal; and `AtlasGenerator.atlasShiftDiag` is
an explicitly-INVENTED candidate, disconnected from the spectrum. So the unbounded, refinement-sourced
scale-lift is the exposed open seam — completing `M₂₄ ⊕ 0` cannot itself close the HP crux. There is no
spectral-reality → zero correspondence and no unbounded generator; the crux (RH) stays `none`.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Square.FinDirectLimit
import F1Square.Square.DiagonalOperatorCore
import F1Square.Square.AtlasSpectralCore

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

set_option maxHeartbeats 1000000

-- ===========================================================================
-- Local zeta-free trivialities retained for the atlas-specific results below (the generic
-- `Cofreal` / `diagOp` / `PreHilbertSymOp` / `dlimDiagW` machinery now lives in
-- `DiagonalOperatorCore`, imported above).
-- ===========================================================================

/-- `z · 0 ≈ 0` (local; used by `atlasObs_vanishes_off_carrier`). -/
private theorem cmul_czero_loc (z : Complex) : Ceq (Cmul z Czero) Czero :=
  ⟨Req_trans (Radd_congr (Rmul_zero z.re) (Rneg_congr (Rmul_zero z.im))) (Radd_neg zero),
   Req_trans (Radd_congr (Rmul_zero z.re) (Rmul_zero z.im)) (Radd_zero zero)⟩

/-- The embedding of a real `≈ 0` is the complex zero (`⟨r,0⟩ ≈ ⟨0,0⟩ = Czero`). -/
private theorem Cofreal_eq_zero {r : Real} (h : Req r zero) : Ceq (Cofreal r) Czero :=
  ⟨h, Req_refl zero⟩

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
    symmetric operator is genuinely indefinite (mirrors `atlasM_signature`), yet Hermitian on the
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

-- ===========================================================================
-- The finite seed `M₂₄`, TYPED over the sourced carrier `Fin 24` — the type itself forbids the
-- unsourced tail (reviewer's item 1: prevent accidental use of `atlasEig`'s `i ≥ 24` values).
-- ===========================================================================

/-- The sourced Atlas spectrum **typed over the 24-dimensional carrier `Fin 24`**: the seed eigenvalue
    at carrier index `i`. Because the domain is `Fin 24`, the unsourced tail (`atlasEig` on `i ≥ 24`)
    is UNREPRESENTABLE — the source boundary is enforced by the type, not merely guarded. -/
def atlasSeedEig (i : Fin 24) : Int := atlasEig i.val

/-- The seed observable weight over `Fin 24` (real). -/
def atlasSeedWeight (i : Fin 24) : Real := ofQ ⟨atlasSeedEig i, 1⟩ Nat.one_pos

/-- **The finite seed operator `M₂₄`, typed over `Fin 24`**: the diagonal Atlas observable on the
    sourced carrier `CVec 24`, whose weight CANNOT reference the unsourced tail. This is the genuine
    sourced finite object; the tower operator `diagOp atlasWeight N` agrees with it on the carrier
    (`atlasSeedOp_eq`) and is `0` beyond (`atlasObs_vanishes_off_carrier`). -/
def atlasSeedOp (x : CVec 24) : CVec 24 := fun i => Cmul (Cofreal (atlasSeedWeight i)) (x i)

/-- On the carrier the `Fin 24`-typed seed weight equals the `ℕ`-indexed observable weight (both are
    the sourced `atlasEig i`; the tower's weight goes through `atlasObsEig`, which agrees for `i<24`). -/
theorem atlasSeedWeight_eq_atlasWeight (i : Fin 24) : Req (atlasSeedWeight i) (atlasWeight i.val) := by
  show Req (ofQ ⟨atlasSeedEig i, 1⟩ Nat.one_pos) (ofQ ⟨atlasObsEig i.val, 1⟩ Nat.one_pos)
  rw [show atlasObsEig i.val = atlasEig i.val from atlasObsEig_sourced i.val i.isLt]
  exact Req_refl _

/-- **The seed agrees with the tower operator on the carrier**: `atlasSeedOp x ≈ (diagOp atlasWeight
    24) x`. So the `Fin 24`-typed presentation and the `ℕ`-indexed one coincide on `CVec 24`, and the
    seed inherits linearity/symmetry from `diagOp`. -/
theorem atlasSeedOp_eq (x : CVec 24) : CVecEq (atlasSeedOp x) (diagOp atlasWeight 24 x) :=
  fun i => Cmul_congr ⟨atlasSeedWeight_eq_atlasWeight i, Req_refl zero⟩ (Ceq_refl (x i))

/-- **BASE RESTRICTION TO `M₂₄`** (reviewer's item 3, base half): the `Fin 24`-typed seed weight IS the
    Atlas spectral-operator diagonal `atlasM i i` on the sourced carrier. So `atlasSeedOp` genuinely
    restricts the sourced `M` (§5/§6.6) to the finite carrier — typed so the tail cannot intrude. -/
theorem atlasSeedWeight_eq_atlasM (i : Fin 24) : Req (atlasSeedWeight i) (atlasM i.val i.val) :=
  Req_trans (atlasSeedWeight_eq_atlasWeight i) (atlasWeight_eq_atlasM_diag i.val i.isLt)

/-- **The seed operator is SYMMETRIC** on `cInner 24` — inherited from `diagOp_herm` through the
    carrier agreement `atlasSeedOp_eq`. (Symmetry only; not self-adjointness.) -/
theorem atlasSeedOp_herm (x y : CVec 24) :
    Ceq (cInner 24 (atlasSeedOp x) y) (cInner 24 x (atlasSeedOp y)) :=
  Ceq_trans (cInner_congr (atlasSeedOp_eq x) (CVecEq_refl y))
    (Ceq_trans (diagOp_herm 24 atlasWeight x y)
      (cInner_congr (CVecEq_refl x) (CVecEq_symm (atlasSeedOp_eq y))))

/-- **The seed eigenvalue VALUES are integer-bounded in `[−1, 10]`** (`atlasEig_range` on the
    carrier). This is an integer inequality on the diagonal ENTRIES — NOT a formalized operator-norm
    bound `⟨Ax,Ax⟩ ≤ 100⟨x,x⟩`, eigenpair, or finite-rank theorem. It records that the sourced seed
    takes only bounded values, the qualitative reason it cannot be the (necessarily unbounded) HP
    operator; a genuine operator-norm/finite-rank statement is not asserted here. -/
theorem atlasSeedEig_bounded (i : Fin 24) : -1 ≤ atlasSeedEig i ∧ atlasSeedEig i ≤ 10 :=
  atlasEig_range i.val

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

/-- The Atlas observable on the direct limit — the descent of `atlasWeight` via the generic
    `dlimDiagW` (from `DiagonalOperatorCore`). -/
def dlimAtlas (a : DLimRaw) : DLimRaw := dlimDiagW atlasWeight a

/-- The colimit operator is well-defined against `DLimEq` (from `dlimDiagW_wd`). -/
theorem dlimAtlas_wd {a a' : DLimRaw} (h : DLimEq a a') : DLimEq (dlimAtlas a) (dlimAtlas a') :=
  dlimDiagW_wd atlasWeight h

/-- The colimit operator is additive (from `dlimDiagW_add`). -/
theorem dlimAtlas_add (a b : DLimRaw) :
    DLimEq (dlimAtlas (dlimAdd a b)) (dlimAdd (dlimAtlas a) (dlimAtlas b)) :=
  dlimDiagW_add atlasWeight a b

/-- The colimit operator commutes with scalar multiplication (from `dlimDiagW_smul`). -/
theorem dlimAtlas_smul (c : Complex) (a : DLimRaw) :
    DLimEq (dlimAtlas (dlimSmul c a)) (dlimSmul c (dlimAtlas a)) :=
  dlimDiagW_smul atlasWeight c a

/-- **The colimit operator is SYMMETRIC** w.r.t. the colimit metric `dlimInner` (from
    `dlimDiagW_herm`). This is a genuine symmetric Atlas operator induced on the direct-limit
    pre-Hilbert object — symmetry only, not self-adjointness. -/
theorem dlimAtlas_herm (a b : DLimRaw) :
    Ceq (dlimInner (dlimAtlas a) b) (dlimInner a (dlimAtlas b)) :=
  dlimDiagW_herm atlasWeight a b

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
