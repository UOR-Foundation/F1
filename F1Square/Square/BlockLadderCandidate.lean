/-
F1 square — **the BLOCK-LADDER CANDIDATE: a locally-invented unbounded diagonal, formally REJECTED**
as a Hilbert–Pólya operator. The finite seed `M₂₄ ⊕ 0` (`FinAtlasOperator`) is bounded and cannot be
an HP operator (which must be UNBOUNDED). This module builds ONE concrete unbounded diagonal candidate,
tests it against the HP requirements, and rejects it — the research role of testing a candidate and
exposing its first failed bridge. It is NOT a warranted Atlas refinement (see NAMING).

THE CANDIDATE. The carrier is indexed `i = 24·ℓ + j` and split as a `BlockLadderAddr = (scale ℓ, block
j ∈ Fin 24)` — the `T·O = 24` block repeated per level. The weight is
    `blockLadderEval ⟨ℓ, j⟩ = (M₂₄ eigenvalue at block j) + ℓ·log 5`,
the block part from the `Fin 24` seed `atlasSeedWeight`, the per-scale shift `ℓ·log 5` from the
Frobenius-orbit length `orbitShift 5 ℓ` (`Cohomology`; `orbitShift 5 1 = Λ(5) = log 5`), with `p = 5`
the first chain prime (`atlasPrime 0 = 5`). The construction is zero-free (its cone avoids `ComplexZeta`
and the crux) but the `M₂₄ + ℓ·log 5` LAW itself is invented, not derived from an Atlas refinement map.

WHAT IS BUILT (all axiom-clean):
- Base agreement `blockLadderWeight_base` / `blockLadderOp_base_action`: `diagOp blockLadderWeight 24`
  acts as the seed `M₂₄` on `CVec 24`.
- A per-level shift identity `blockLadderEval_scale_succ` / `blockLadder_scale_gap` (each level adds
  exactly `log 5` — a CONSTANT scale gap).
- Descent to the direct-limit core `dlimBlockLadder` / `blockLadderDLimOp` (via the generic `dlimDiagW`
  from `DiagonalOperatorCore`), an unbounded symmetric operator on `dlimPreHilbert`.
- The OPERATOR-LEVEL eigenpair `dlimBlockLadder_eigen : dlimBlockLadder eᵢ ≈ wᵢ · eᵢ` on the normalized
  basis (`dlimBasis`/`dlimBasis_normalized` in the core) — tying each weight to `dlimBlockLadder` as a
  genuine eigenvalue.

HP PREREQUISITES PASSED (necessary features, NOT rejections). An HP operator must be UNBOUNDED and
SYMMETRIC; this candidate satisfies both: `dlimBlockLadder_not_normBounded_real` (unbounded by ANY real
`C`, via Archimedean domination `exists_nat_ge` + bound monotonicity) and `dlimDiagW_herm` (symmetric).
Passing these is a prerequisite, not evidence against the candidate.

NAMING — this is a **block-ladder candidate**, NOT a warranted Atlas refinement. The `(scale, block)`
address and the `M₂₄ + ℓ·log 5` law are locally constructed; no derived refinement map / coherence
warrant backs the infinite ladder. A genuine warrant SOURCE exists in principle: the addressing tower
(`AtlasAddressing`) is import-contaminated, but its pure-Nat core (e.g. `atlasPrime 0 = 5`) can be
extracted zero-free (`AtlasAddressingCore`, a near-term follow-up). What remains genuinely OPEN is the
unbounded refinement map, not the `p = 5` identity.

THE REJECTION — a CONSTRUCTIVE, zero-free SPECTRAL ASYMMETRY. `blockLadderSpec_not_neg_closed`: the
weight spectrum `blockLadderWeightSpec` (each weight is a realized eigenvalue by `dlimBlockLadder_eigen`,
so weights ⊆ point spectrum) is NOT closed under `μ ↦ −μ` — `10` is a weight but `−10` is not, since
every weight `≥ −1` (`blockLadderWeight_ge_neg_one`) so `w_i + 10 > 0` (`blockLadder_gt_neg_ten`). The HP
trace-symmetry requirement `NegClosed` therefore FAILS. (`blockLadder_scale_gap` — the scale-tower
spectrum is an arithmetic progression, constant gap `log 5`, unlike the zeros' shrinking gaps — is a
DIAGNOSTIC observation, NOT a formalized zero-spectrum contradiction; the formal rejection is the
asymmetry.) So the block-ladder is rejected — that rejects THIS construction, not the Atlas program or
RH. No spectral→zero correspondence is asserted; the crux (RH) stays `none`.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; the cone avoids `ComplexZeta`
and the crux modules. Audited by `scripts/honesty_audit.sh`.
-/

import F1Square.Square.DiagonalOperatorCore
import F1Square.Square.FinAtlasOperator
import F1Square.Square.Cohomology
import F1Square.Analysis.ComplexPow

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

set_option maxHeartbeats 1000000

-- ===========================================================================
-- Local naturals-to-reals trivialities (private; public copies are ζ-tainted).
-- ===========================================================================

private theorem RofNat_zero_loc : Req (RofNat 0) zero := Req_of_seq_Qeq (fun _ => Qeq_refl _)

private theorem RofNat_succ_loc (n : Nat) : Req (RofNat (n + 1)) (Radd (RofNat n) one) :=
  Req_of_seq_Qeq (fun _ => by
    show Qeq (⟨((n : Int) + 1), 1⟩) (add (⟨(n : Int), 1⟩) (⟨1, 1⟩))
    simp only [Qeq, add]; push_cast; ring_uor)

/-- **Archimedean domination**: every Bishop real `x` is `≤ RofNat B` for some natural `B` (the
    canonical bound `xBound x`): `x.seq n ≤ |x.seq n| ≤ xBound x ≤ xBound x + 2/(n+1)`. Upgrades a
    "not bounded by any nat" statement to "not bounded by any real". -/
private theorem exists_nat_ge (x : Real) : ∃ B : Nat, Rle x (RofNat B) := by
  refine ⟨xBound x, fun n => ?_⟩
  show Qle (x.seq n) (add (⟨(xBound x : Int), 1⟩ : Q) ⟨2, n + 1⟩)
  have h1 : Qle (x.seq n) (Qabs (x.seq n)) := by
    show (x.seq n).num * ((Qabs (x.seq n)).den : Int) ≤ (Qabs (x.seq n)).num * ((x.seq n).den : Int)
    simp only [Qabs]
    exact Int.mul_le_mul_of_nonneg_right Int.le_natAbs (by omega)
  have h2 : Qle (Qabs (x.seq n)) (⟨(xBound x : Int), 1⟩ : Q) := canon_bound x n
  have h3 : Qle (⟨(xBound x : Int), 1⟩ : Q) (add (⟨(xBound x : Int), 1⟩ : Q) ⟨2, n + 1⟩) :=
    Qle_self_add (by show (0 : Int) ≤ 2; decide)
  have h23 : Qle (Qabs (x.seq n)) (add (⟨(xBound x : Int), 1⟩ : Q) ⟨2, n + 1⟩) :=
    Qle_trans (b := (⟨(xBound x : Int), 1⟩ : Q)) (by show (0 : Nat) < 1; decide) h2 h3
  exact Qle_trans (b := Qabs (x.seq n)) (x.den_pos n) h1 h23

-- ===========================================================================
-- The per-scale shift `ℓ·log 5` (a Frobenius-orbit length) and the zero-free bound `log 5 ≥ 1`.
-- ===========================================================================

/-- The per-scale block-ladder shift: the Frobenius-orbit length `orbitShift 5 ℓ = ℓ·log 5`
    (`Cohomology`; `orbitShift 5 1 = Λ(5)`) for the chain prime `p = 5 = atlasPrime 0`. -/
def blockLadderShift (ℓ : Nat) : Real := orbitShift 5 (by decide) ℓ

/-- **`log 5 ≥ 1`, zero-free**: `5 ≥ 2²` gives `log 5 ≥ 2·log 2` (`logN_ge_k_log2`), and `log 2 ≥ 1/2`
    (`logN_2_ge_half`), so `log 5 ≥ 1`. The step size that makes the candidate unbounded, proved in the
    `ComplexZeta`-free `RealPow` cone (not the tainted `logN_ge_one`). -/
theorem log5_ge_one : Rle one (logN 5 (by decide)) := by
  have h1 : Rle (Rnsmul 2 (logN 2 (by decide))) (logN 5 (by decide)) :=
    logN_ge_k_log2 (by decide : 2 ^ 2 ≤ 5)
  have hhalf : Rle (ofQ (⟨1, 2⟩ : Q) (by decide)) (logN 2 (by decide)) := logN_2_ge_half
  have hone : Req one (Radd (ofQ (⟨1, 2⟩ : Q) (by decide)) (ofQ (⟨1, 2⟩ : Q) (by decide))) :=
    Req_of_seq_Qeq (fun _ => by show Qeq (⟨1, 1⟩ : Q) (add (⟨1, 2⟩ : Q) (⟨1, 2⟩ : Q)); decide)
  have hrn : Req (Radd (logN 2 (by decide)) (logN 2 (by decide))) (Rnsmul 2 (logN 2 (by decide))) :=
    Radd_congr (Req_refl _) (Req_symm (Radd_zero _))
  exact Rle_trans (Rle_of_Req hone)
    (Rle_trans (Rle_trans (Radd_le_add hhalf hhalf) (Rle_of_Req hrn)) h1)

-- ===========================================================================
-- The typed block-ladder address carrier and the candidate evaluator.
-- ===========================================================================

/-- A **typed block-ladder address**: a scale (level) index and a block position in the `T·O = 24`
    carrier. The infinite address tower the candidate operator lives on (locally invented). -/
structure BlockLadderAddr where
  scale : Nat
  block : Fin 24

/-- **The candidate evaluator**: `(M₂₄ eigenvalue at block j) + ℓ·log 5`. Block part from the `Fin 24`
    seed `atlasSeedWeight`; scale shift from the orbit length `blockLadderShift`. -/
def blockLadderEval (a : BlockLadderAddr) : Real := Radd (atlasSeedWeight a.block) (blockLadderShift a.scale)

/-- The address of a raw index `i = 24·ℓ + j`: scale `i / 24`, block `i % 24`. -/
def blockLadderAddrOfNat (i : Nat) : BlockLadderAddr := ⟨i / 24, ⟨i % 24, by omega⟩⟩

/-- **The candidate diagonal weight** on the raw carrier `ℕ` (for `diagOp`): evaluate the address of
    `i`. Routes the block spectrum through the TYPED seed (`atlasSeedWeight` on `Fin 24`), so the raw
    `atlasEig` tail is never touched (`i % 24 < 24` always). -/
def blockLadderWeight (i : Nat) : Real := blockLadderEval (blockLadderAddrOfNat i)

/-- The candidate weight in raw component form (definitional). -/
theorem blockLadderWeight_val (i : Nat) :
    blockLadderWeight i = Radd (ofQ ⟨atlasEig (i % 24), 1⟩ Nat.one_pos) (blockLadderShift (i / 24)) := rfl

/-- The candidate weight at a scale-tower index `24·ℓ` (block `0`): `M₂₄(0) + ℓ·log 5`. -/
theorem blockLadderWeight_mul24 (ℓ : Nat) :
    blockLadderWeight (24 * ℓ) = Radd (ofQ ⟨atlasEig 0, 1⟩ Nat.one_pos) (blockLadderShift ℓ) := by
  rw [blockLadderWeight_val]
  have hm : (24 * ℓ) % 24 = 0 := by omega
  have hd : (24 * ℓ) / 24 = ℓ := by omega
  rw [hm, hd]

-- ===========================================================================
-- Base-action agreement with the seed, and the per-level shift identity.
-- ===========================================================================

/-- **Base agreement**: on the carrier (`i < 24`, scale `0`) the candidate weight equals the `Fin 24`
    seed weight — the candidate restricts to `M₂₄` on the base block. -/
theorem blockLadderWeight_base (i : Nat) (h : i < 24) :
    Req (blockLadderWeight i) (atlasSeedWeight ⟨i, h⟩) := by
  rw [blockLadderWeight_val]
  have hm : i % 24 = i := Nat.mod_eq_of_lt h
  have hd : i / 24 = 0 := Nat.div_eq_of_lt h
  rw [hm, hd]
  have hs0 : blockLadderShift 0 = zero := rfl
  rw [hs0]
  exact Radd_zero _

/-- **Base-ACTION agreement with `atlasSeedOp`**: on `CVec 24` the candidate operator `diagOp
    blockLadderWeight 24` acts exactly as the finite seed `atlasSeedOp` (matrix-action equality, not just
    weight equality). So the candidate genuinely extends the seed. -/
theorem blockLadderOp_base_action (x : CVec 24) :
    CVecEq (diagOp blockLadderWeight 24 x) (atlasSeedOp x) := by
  intro i
  show Ceq (Cmul (Cofreal (blockLadderWeight i.val)) (x i)) (Cmul (Cofreal (atlasSeedWeight i)) (x i))
  exact Cmul_congr ⟨blockLadderWeight_base i.val i.isLt, Req_refl zero⟩ (Ceq_refl (x i))

/-- **Per-level shift identity**: lifting the scale by one level adds exactly `log 5` to the
    eigenvalue (`orbitShift 5 (ℓ+1) = log 5 + orbitShift 5 ℓ`). -/
theorem blockLadderEval_scale_succ (ℓ : Nat) (j : Fin 24) :
    Req (blockLadderEval ⟨ℓ + 1, j⟩) (Radd (blockLadderEval ⟨ℓ, j⟩) (logN 5 (by decide))) := by
  show Req (Radd (atlasSeedWeight j) (blockLadderShift (ℓ + 1)))
           (Radd (Radd (atlasSeedWeight j) (blockLadderShift ℓ)) (logN 5 (by decide)))
  refine Req_trans (Radd_congr (Req_refl _) (orbitShift_succ 5 (by decide) ℓ)) ?_
  refine Req_trans (Radd_congr (Req_refl _) (Radd_comm (logN 5 (by decide)) (blockLadderShift ℓ))) ?_
  exact Req_symm (Radd_assoc _ (blockLadderShift ℓ) (logN 5 (by decide)))

/-- **The scale gap is CONSTANT `= log 5`**: `blockLadderWeight(24(ℓ+1)) = blockLadderWeight(24ℓ) + log 5`.
    So the scale-tower spectrum is an ARITHMETIC PROGRESSION — a DIAGNOSTIC observation (the Riemann
    zeros' gaps shrink, they are not constant), NOT a formalized zero-spectrum contradiction. The formal
    rejection is the spectral asymmetry `blockLadderSpec_not_neg_closed`. -/
theorem blockLadder_scale_gap (ℓ : Nat) :
    Req (blockLadderWeight (24 * (ℓ + 1)))
        (Radd (blockLadderWeight (24 * ℓ)) (logN 5 (by decide))) := by
  rw [blockLadderWeight_mul24 ℓ, blockLadderWeight_mul24 (ℓ + 1)]
  refine Req_trans (Radd_congr (Req_refl _) (orbitShift_succ 5 (by decide) ℓ)) ?_
  refine Req_trans (Radd_congr (Req_refl _) (Radd_comm (logN 5 (by decide)) (blockLadderShift ℓ))) ?_
  exact Req_symm (Radd_assoc _ (blockLadderShift ℓ) (logN 5 (by decide)))

-- ===========================================================================
-- Genuine unboundedness (the property the finite seed lacked).
-- ===========================================================================

/-- **Each scale step adds `≥ 1`**: `blockLadderWeight(24ℓ) + 1 ≤ blockLadderWeight(24(ℓ+1))` (constant
    gap `log 5 ≥ 1`). The diagonal strictly increases without bound along the scale tower. -/
theorem blockLadder_scale_step (ℓ : Nat) :
    Rle (Radd (blockLadderWeight (24 * ℓ)) one) (blockLadderWeight (24 * (ℓ + 1))) :=
  Rle_trans (Radd_le_add (Rle_refl _) log5_ge_one)
    (Rle_of_Req (Req_symm (blockLadder_scale_gap ℓ)))

/-- The scale-tower diagonal dominates `blockLadderWeight 0 + ℓ` (each step adds `≥ 1`). -/
theorem blockLadderWeight_scale_ge :
    ∀ ℓ, Rle (Radd (blockLadderWeight 0) (RofNat ℓ)) (blockLadderWeight (24 * ℓ))
  | 0 => Rle_of_Req (Req_trans (Radd_congr (Req_refl _) RofNat_zero_loc) (Radd_zero _))
  | (ℓ + 1) => by
      refine Rle_trans (Rle_of_Req ?_)
        (Rle_trans (Radd_le_add (blockLadderWeight_scale_ge ℓ) (Rle_refl one)) (blockLadder_scale_step ℓ))
      refine Req_trans (Radd_congr (Req_refl _) (RofNat_succ_loc ℓ)) ?_
      exact Req_symm (Radd_assoc _ (RofNat ℓ) one)

/-- **WEIGHT UNBOUNDEDNESS**: for every nat `B` there is an index whose diagonal WEIGHT exceeds it —
    `∀ B, ∃ i, RofNat B ≤ blockLadderWeight i`. The seed-level input to the operator-level unboundedness
    `dlimBlockLadder_not_normBounded_real`. -/
theorem blockLadder_unbounded (B : Nat) : ∃ i, Rle (RofNat B) (blockLadderWeight i) := by
  have hcw0 : Rnonneg (blockLadderWeight 0) := by
    rw [blockLadderWeight_val]
    exact Rnonneg_Radd (Rnonneg_ofQ (by decide) (by decide)) Rnonneg_zero
  refine ⟨24 * B, ?_⟩
  refine Rle_trans (Rle_trans (Rle_self_Radd_right hcw0)
    (Rle_of_Req (Radd_comm (RofNat B) (blockLadderWeight 0)))) (blockLadderWeight_scale_ge B)

-- ===========================================================================
-- The block-ladder operator on the direct-limit core — the descent of the generic
-- `dlimDiagW` (from `DiagonalOperatorCore`) at the block-ladder weight.
-- ===========================================================================

/-- **The block-ladder operator on the direct-limit core** — the descent of the unbounded diagonal
    `blockLadderWeight` via the generic `dlimDiagW`. An unbounded symmetric operator on
    `dlimPreHilbert`, formally REJECTED below (its point spectrum is not closed under negation). -/
def dlimBlockLadder : DLimRaw → DLimRaw := dlimDiagW blockLadderWeight

/-- **The candidate as a typed symmetric operator on `dlimPreHilbert`** — CANDIDATE, not the HP
    operator: it is unbounded (`blockLadder_unbounded`) and symmetric, but its spectrum is an arithmetic
    progression (`blockLadder_scale_gap`), rejected at the spectral/zero bridge. Crux `none`. -/
def blockLadderDLimOp : PreHilbertSymOp dlimPreHilbert where
  op := dlimBlockLadder
  op_congr := fun h => dlimDiagW_wd blockLadderWeight h
  op_add := dlimDiagW_add blockLadderWeight
  op_smul := dlimDiagW_smul blockLadderWeight
  op_herm := dlimDiagW_herm blockLadderWeight

-- ===========================================================================
-- The constructive spectral rejection: the diagonal has floor −1 but peak 10, so
-- its point spectrum is NOT closed under μ ↦ −μ (fails HP trace-symmetry).
-- ===========================================================================

/-- `n·x ≥ 0` for `x ≥ 0`. -/
private theorem Rnonneg_Rnsmul (x : Real) (h : Rnonneg x) : ∀ ℓ, Rnonneg (Rnsmul ℓ x)
  | 0 => Rnonneg_zero
  | (ℓ + 1) => Rnonneg_Radd h (Rnonneg_Rnsmul x h ℓ)

/-- The per-scale shift is nonnegative (`ℓ·log 5 ≥ 0`). -/
private theorem blockLadderShift_nonneg (ℓ : Nat) : Rnonneg (blockLadderShift ℓ) :=
  Rnonneg_Rnsmul (logN 5 (by decide)) (Rnonneg_logN 5 (by decide)) ℓ

/-- `−1` as `ofQ`. -/
private theorem Rneg_one_eq_ofQ : Req (Rneg one) (ofQ (⟨-1, 1⟩ : Q) (by decide)) :=
  Req_of_seq_Qeq (fun _ => by show Qeq (neg (⟨1, 1⟩ : Q)) (⟨-1, 1⟩ : Q); decide)

/-- **WEIGHT FLOOR**: every block-ladder diagonal weight is `≥ −1` — the block eigenvalue is `≥ −1`
    (`atlasEig_range`) and the scale shift is `≥ 0`. The spectral floor that makes the point spectrum
    asymmetric under negation. -/
theorem blockLadderWeight_ge_neg_one (i : Nat) : Rle (Rneg one) (blockLadderWeight i) := by
  rw [blockLadderWeight_val]
  have hblock : Rle (Rneg one) (ofQ ⟨atlasEig (i % 24), 1⟩ Nat.one_pos) := by
    refine Rle_trans (Rle_of_Req Rneg_one_eq_ofQ) (Rle_ofQ_ofQ (by decide) Nat.one_pos ?_)
    have h1 := (atlasEig_range (i % 24)).1
    simp only [Qle]; push_cast; omega
  refine Rle_trans (Rle_of_Req (Req_symm (Radd_zero (Rneg one)))) ?_
  exact Radd_le_add hblock (Rle_zero_of_Rnonneg (blockLadderShift_nonneg _))

/-- `−1 + 10 = 9`. -/
private theorem neg_one_add_ten : Req (Radd (Rneg one) (ofQ (⟨10, 1⟩ : Q) Nat.one_pos))
    (ofQ (⟨9, 1⟩ : Q) Nat.one_pos) :=
  Req_trans (Radd_congr Rneg_one_eq_ofQ (Req_refl _))
    (Req_of_seq_Qeq (fun _ => by show Qeq (add (⟨-1, 1⟩ : Q) (⟨10, 1⟩ : Q)) (⟨9, 1⟩ : Q); decide))

/-- **SPECTRAL ASYMMETRY (`−10` below the whole diagonal)**: `w_i + 10 > 0` (strictly, `Pos`) for every
    `i` — since `w_i ≥ −1`, `w_i + 10 ≥ 9 ≥ 1`. So `−10` lies strictly below EVERY diagonal weight,
    while `w₀ = 10` IS a weight. A point spectrum with `10` but nothing near `−10` is not closed under
    `μ ↦ −μ` — the block-ladder fails the HP trace-symmetry requirement. Zero-free rejection. -/
theorem blockLadder_gt_neg_ten (i : Nat) :
    Pos (Radd (blockLadderWeight i) (ofQ (⟨10, 1⟩ : Q) Nat.one_pos)) := by
  have h9 : Rle one (ofQ (⟨9, 1⟩ : Q) Nat.one_pos) :=
    Rle_ofQ_ofQ (by decide) Nat.one_pos (by decide)
  have hstep : Rle (ofQ (⟨9, 1⟩ : Q) Nat.one_pos)
      (Radd (blockLadderWeight i) (ofQ ⟨10, 1⟩ Nat.one_pos)) :=
    Rle_trans (Rle_of_Req (Req_symm neg_one_add_ten))
      (Radd_le_add (blockLadderWeight_ge_neg_one i) (Rle_refl _))
  exact Pos_of_Rle_one (Rle_trans h9 hstep)

/-- **`w₀ = 10`** — a diagonal weight strictly exceeding `2` (the peak witnessing the asymmetry). -/
theorem blockLadderWeight_zero_eq_ten :
    Req (blockLadderWeight 0) (ofQ (⟨10, 1⟩ : Q) Nat.one_pos) := by
  show Req (Radd (ofQ ⟨10, 1⟩ Nat.one_pos) zero) (ofQ ⟨10, 1⟩ Nat.one_pos)
  exact Radd_zero _

-- ===========================================================================
-- The operator-level eigenpair, the weight spectrum, and the constructive
-- rejection: the point spectrum is NOT closed under μ ↦ −μ.
-- ===========================================================================

/-- **The operator-level EIGENPAIR** for the block-ladder operator: `dlimBlockLadder eᵢ ≈ wᵢ · eᵢ`
    (instantiating the generic `dlimDiagW_eigen` at `blockLadderWeight`). This connects each diagonal
    weight `blockLadderWeight i` to `dlimBlockLadder` as a genuine eigenvalue on the normalized vector
    `dlimBasis i` (`dlimBasis_normalized`). -/
theorem dlimBlockLadder_eigen (i : Nat) :
    DLimEq (dlimBlockLadder (dlimBasis i)) (dlimSmul (Cofreal (blockLadderWeight i)) (dlimBasis i)) :=
  dlimDiagW_eigen blockLadderWeight i

/-- The block-ladder weight **spectrum** as a predicate on reals: `μ` is a diagonal weight (hence, by
    `dlimBlockLadder_eigen` + `dlimBasis_normalized`, a genuine eigenvalue of `dlimBlockLadder`) iff it
    equals `blockLadderWeight i` for some carrier index `i`. -/
def blockLadderWeightSpec (μ : Real) : Prop := ∃ i, Req μ (blockLadderWeight i)

/-- **Negation-closure** of a real-predicate spectrum `S`: closed under `μ ↦ −μ`. This is the
    Hilbert–Pólya trace-symmetry requirement on a point spectrum (`μ ∈ σ ⟹ −μ ∈ σ`), stated
    purely — no operator, no completion. -/
def NegClosed (S : Real → Prop) : Prop := ∀ μ, S μ → S (Rneg μ)

/-- `−0 ≈ 0` (local, zeta-free). -/
private theorem rneg_zero_bl : Req (Rneg zero) zero :=
  Req_of_seq_Qeq (fun _ => by show Qeq (neg (⟨0, 1⟩ : Q)) ⟨0, 1⟩; decide)

/-- `¬ Pos 0` (local; built from the clean `not_Pos_of_Rnonneg_neg`). -/
private theorem not_Pos_zero_bl : ¬ Pos zero :=
  not_Pos_of_Rnonneg_neg (Rnonneg_congr (Req_symm rneg_zero_bl) Rnonneg_zero)

/-- **No weight equals `−10`**: from `blockLadder_gt_neg_ten` (`w_i + 10 > 0` strictly, `Pos`),
    `w_i ≈ −10` would force `w_i + 10 ≈ 0`, i.e. `Pos 0`, impossible. Turns the strict `Pos` lower
    bound into the apartness of every diagonal weight from `−10`. -/
private theorem not_Req_neg_ten (i : Nat) :
    ¬ Req (blockLadderWeight i) (Rneg (ofQ (⟨10, 1⟩ : Q) Nat.one_pos)) := by
  intro hi
  have hzero : Req (Radd (blockLadderWeight i) (ofQ (⟨10, 1⟩ : Q) Nat.one_pos)) zero :=
    Req_trans (Radd_congr hi (Req_refl _))
      (Req_trans
        (Radd_comm (Rneg (ofQ (⟨10, 1⟩ : Q) Nat.one_pos)) (ofQ (⟨10, 1⟩ : Q) Nat.one_pos))
        (Radd_neg (ofQ (⟨10, 1⟩ : Q) Nat.one_pos)))
  exact not_Pos_zero_bl (Pos_congr hzero (blockLadder_gt_neg_ten i))

/-- **THE BLOCK-LADDER WEIGHT SPECTRUM IS NOT CLOSED UNDER NEGATION** — the constructive spectral
    rejection. `blockLadderWeight 0 ≈ 10` is a weight (hence, by `dlimBlockLadder_eigen`, a realized
    eigenvalue of `dlimBlockLadder`), but `−10` is not a weight: every `w_i` is apart from `−10`
    (`not_Req_neg_ten`, i.e. `w_i + 10 > 0`). So the weight set — which is ⊆ the point spectrum, since
    each weight is realized as an eigenvalue (the converse, point spectrum ⊆ weights, is the standard
    diagonal fact, not formalized here) — cannot satisfy the HP trace-symmetry closure `NegClosed`.
    This REJECTS the block-ladder as an HP operator, zero-free; no spectral→zero correspondence is
    asserted, the crux (RH) stays `none`. -/
theorem blockLadderSpec_not_neg_closed : ¬ NegClosed blockLadderWeightSpec := by
  intro h
  obtain ⟨i, hi⟩ := h (blockLadderWeight 0) ⟨0, Req_refl _⟩
  exact not_Req_neg_ten i
    (Req_trans (Req_symm hi) (Rneg_congr blockLadderWeight_zero_eq_ten))

-- ===========================================================================
-- Genuine OPERATOR-THEORETIC unboundedness: the operator norm on the normalized
-- eigenvectors exceeds every nat bound, so `dlimBlockLadder` is not norm-bounded.
-- ===========================================================================

/-- `RofNat n ≥ 0`. -/
private theorem RofNat_nonneg (n : Nat) : Rnonneg (RofNat n) := by
  show Rnonneg (ofQ ⟨(n : Int), 1⟩ Nat.one_pos)
  exact Rnonneg_ofQ Nat.one_pos (by show (0 : Int) ≤ (n : Int); omega)

/-- **OPERATOR-THEORETIC UNBOUNDEDNESS (nat bounds)**: for every nat bound `B`, `dlimBlockLadder` is NOT
    norm-bounded by `RofNat B`. On the normalized eigenvector `eⱼ` with `wⱼ ≥ RofNat (B+1)`,
    `⟨A eⱼ, A eⱼ⟩ = wⱼ² ≥ (RofNat (B+1))² > (RofNat B)² = (RofNat B)²·⟨eⱼ,eⱼ⟩`, contradicting the bound.
    Upgraded to ALL real bounds in `dlimBlockLadder_not_normBounded_real`. This is the HP unboundedness
    PREREQUISITE (a necessary feature of an HP operator), proved at the OPERATOR level via
    `OpNormBounded` — not the rejection. -/
theorem dlimBlockLadder_not_normBounded (B : Nat) : ¬ OpNormBounded dlimBlockLadder (RofNat B) := by
  intro hb
  obtain ⟨i, hi⟩ := blockLadder_unbounded (B + 1)
  have hbnd := hb (dlimBasis i)
  have hval : Req (dlimInner (dlimBlockLadder (dlimBasis i)) (dlimBlockLadder (dlimBasis i))).re
                  (Rmul (blockLadderWeight i) (blockLadderWeight i)) :=
    dlimDiagW_eigen_normSq blockLadderWeight i
  have hself : Req (dlimInner (dlimBasis i) (dlimBasis i)).re one := dlimBasis_self_re i
  have hsq_le : Rle (Rmul (blockLadderWeight i) (blockLadderWeight i))
                    (Rmul (RofNat B) (RofNat B)) :=
    Rle_trans (Rle_of_Req (Req_symm hval))
      (Rle_trans hbnd (Rle_of_Req (Req_trans (Rmul_congr (Req_refl _) hself) (Rmul_one _))))
  have hB1nn : Rnonneg (RofNat (B + 1)) := RofNat_nonneg (B + 1)
  have hwnn : Rnonneg (blockLadderWeight i) :=
    Rnonneg_of_Rle_zero (Rle_trans (Rle_zero_of_Rnonneg hB1nn) hi)
  have hsq_mono : Rle (Rmul (RofNat (B + 1)) (RofNat (B + 1)))
                      (Rmul (blockLadderWeight i) (blockLadderWeight i)) :=
    Rle_trans (Rmul_le_Rmul_left hB1nn hi) (Rmul_le_Rmul_right hwnn hi)
  have hcontra : Rle (RofNat (B + 1)) (RofNat B) :=
    Rle_of_Rmul_self_le (RofNat_nonneg B) (Rle_trans hsq_mono hsq_le)
  -- The gap `RofNat (B+1) − RofNat B ≈ 1 > 0`, but `hcontra` forces `Rnonneg (−gap)` — impossible.
  have gap_eq_one : Req (Rsub (RofNat (B + 1)) (RofNat B)) one := by
    show Req (Radd (RofNat (B + 1)) (Rneg (RofNat B))) one
    refine Req_trans (Radd_congr (RofNat_succ_loc B) (Req_refl _)) ?_
    refine Req_trans (Radd_congr (Radd_comm (RofNat B) one) (Req_refl _)) ?_
    refine Req_trans (Radd_assoc one (RofNat B) (Rneg (RofNat B))) ?_
    exact Req_trans (Radd_congr (Req_refl _) (Radd_neg (RofNat B))) (Radd_zero one)
  have neg_gap : Req (Rsub (RofNat B) (RofNat (B + 1)))
                     (Rneg (Rsub (RofNat (B + 1)) (RofNat B))) := by
    show Req (Radd (RofNat B) (Rneg (RofNat (B + 1))))
             (Rneg (Radd (RofNat (B + 1)) (Rneg (RofNat B))))
    refine Req_symm (Req_trans (Rneg_Radd (RofNat (B + 1)) (Rneg (RofNat B))) ?_)
    refine Req_trans (Radd_congr (Req_refl _) (Rneg_neg (RofNat B))) ?_
    exact Radd_comm (Rneg (RofNat (B + 1))) (RofNat B)
  exact not_Pos_of_Rnonneg_neg
    (Rnonneg_congr neg_gap (Rnonneg_Rsub_of_Rle hcontra))
    (Pos_congr (Req_symm gap_eq_one) (Pos_of_Rle_one (Rle_refl one)))

/-- **ALL-REAL operator unboundedness**: `dlimBlockLadder` is not norm-bounded by ANY real `C ≥ 0`.
    From Archimedean domination (`exists_nat_ge`: `C ≤ RofNat B` for some nat `B`) and monotonicity of
    the norm-bound predicate in `C` (`C² ≤ (RofNat B)²`, and `⟨a,a⟩.re ≥ 0`), a real bound `C` would
    give the nat bound `RofNat B`, contradicting `dlimBlockLadder_not_normBounded`. This is the
    unbounded-spectrum HP PREREQUISITE, PASSED for every real bound — a necessary feature of an HP
    operator, NOT the rejection (the rejection is the spectral asymmetry `blockLadderSpec_not_neg_closed`). -/
theorem dlimBlockLadder_not_normBounded_real (C : Real) (hC : Rnonneg C) :
    ¬ OpNormBounded dlimBlockLadder C := by
  intro hb
  obtain ⟨B, hB⟩ := exists_nat_ge C
  refine dlimBlockLadder_not_normBounded B (fun a => ?_)
  refine Rle_trans (hb a) (Rmul_le_Rmul_right (dlimInner_self_nonneg a) ?_)
  exact Rle_trans (Rmul_le_Rmul_left hC hB) (Rmul_le_Rmul_right (RofNat_nonneg B) hB)

end UOR.Bridge.F1Square.Square
