/-
F1 square — **the Atlas refinement operator: a CANDIDATE unbounded symmetric operator** on the
direct-limit pre-Hilbert core (the research step the operator contract's item 2–4 demand). The finite
seed `M₂₄ ⊕ 0` (`FinAtlasOperator`) is bounded and cannot be the Hilbert–Pólya operator, which must be
UNBOUNDED. This module EXTRAPOLATES the strongest zero-free, UOR-native unbounded candidate from the
Atlas refinement structure, formalizes it, and TESTS it — exposing the first failed bridge.

THE CANDIDATE (a typed refinement-address evaluator). The infinite carrier is addressed as
`AtlasAddr = (scale ℓ, block j ∈ Fin 24)` — the scale-invariant `T·O = 24` block repeated per
refinement level (Atlas §5 scale-invariance), with `i = 24·ℓ + j`. The evaluator is
    `atlasCandEval ⟨ℓ, j⟩ = (M₂₄ eigenvalue at block j) + ℓ·log 5`,
where the per-scale shift is the sourced Frobenius-orbit length `orbitShift 5 ℓ = ℓ·log 5`
(`Cohomology`, Connes–Consani; `orbitShift 5 1 = Λ(5) = log 5`), and `p = 5 = atlasPrime 0` is the
first Atlas CHAIN prime (`AtlasAddressing`). This is zero-free (its whole cone avoids `ComplexZeta`
and the crux) and UOR-native (block = the sourced `atlasSeedEig`; shift = the sourced orbit length).

WHAT IS PROVED:
- **Base-action agreement with `atlasSeedOp`** (scale `0`): `atlasCandWeight` agrees with the `Fin 24`
  seed weight on the carrier (`atlasCandWeight_base`), so `diagOp atlasCandWeight 24` acts as the seed
  `M₂₄` on `CVec 24` (`atlasCandOp_base_action`).
- **Refinement intertwining**: lifting one scale level adds exactly `log 5`
  (`atlasCandEval_scale_succ`, `atlasCand_scale_gap`).
- **Genuine UNBOUNDEDNESS** (the property the seed lacked): the diagonal grows by `≥ 1` per scale
  (`atlasCand_scale_step`, since `log 5 ≥ 1` zero-free), hence exceeds every bound
  (`atlasCand_unbounded : ∀ B, ∃ i, B ≤ atlasCandWeight i`). So the operator is NON-finite-rank.
- **Descent to the direct-limit core**: the candidate descends to `dlimPreHilbert` as a symmetric
  operator `atlasCandDLimOp` (via the generic `dlimDiagW`), the first UNBOUNDED symmetric operator on
  the core.

NAMING — THIS IS A **BLOCK-LADDER CANDIDATE**, NOT A WARRANTED ATLAS REFINEMENT. The address structure
`(scale, block)` and the `M₂₄ + ℓ·log 5` law are a locally-constructed block-ladder: no derived Atlas
refinement map / coherence warrant backs them. A genuine warrant would be sourced from the addressing
tower (`AtlasAddressing`), but that module's cone is itself crux-contaminated (it reaches `ComplexZeta`
/`WeilPSD`/`Crux`), so it cannot be imported into this zero-free operator — there is no clean Atlas
refinement warrant available. Hence "block-ladder candidate," per the operator contract's default.

THE FIRST FAILED BRIDGE — A CONSTRUCTIVE SPECTRAL REJECTION. Two theorems reject this ladder as the HP
operator, zero-free: (1) `atlasCand_scale_gap` — the scale-tower spectrum is an ARITHMETIC PROGRESSION
(constant gap `log 5`), whereas the Riemann zeros' spacing shrinks; and (2) the SPECTRAL ASYMMETRY —
every diagonal weight is `≥ −1` (`atlasCandWeight_ge_neg_one`) while `w₀ = 10` (a weight `> 2`), so
`−10` lies STRICTLY BELOW the entire diagonal (`atlasCand_gt_neg_ten`: `w_i + 10 > 0` for every `i`).
The HP trace-symmetry requirement needs the point spectrum closed under `μ ↦ −μ`; a diagonal whose
entries are all `≥ −1` but include `10` cannot be (it would need `−10`, which is below its floor). So
the candidate is REJECTED. That rejects THIS construction, not the Atlas program or RH. No spectral→zero
correspondence is asserted; the crux (RH) stays `none`.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; the cone avoids `ComplexZeta`
and the crux modules. Audited by `scripts/honesty_audit.sh`.
-/

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

-- ===========================================================================
-- The sourced per-scale shift `ℓ·log 5` and the zero-free bound `log 5 ≥ 1`.
-- ===========================================================================

/-- The per-scale refinement shift: the sourced Frobenius-orbit length for the first Atlas chain
    prime `p = 5 = atlasPrime 0`, `orbitShift 5 ℓ = ℓ·log 5` (`Cohomology`; `orbitShift 5 1 = Λ(5)`). -/
def scaleShift (ℓ : Nat) : Real := orbitShift 5 (by decide) ℓ

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
-- The typed refinement-address carrier and the candidate evaluator.
-- ===========================================================================

/-- A **typed Atlas refinement address**: a scale (refinement) level and a block position in the
    scale-invariant `T·O = 24` carrier. The infinite address tower the candidate operator lives on. -/
structure AtlasAddr where
  scale : Nat
  block : Fin 24

/-- **The candidate evaluator**: `(M₂₄ eigenvalue at block j) + ℓ·log 5`. Block spectrum from the
    sourced `Fin 24` seed; scale shift from the sourced orbit length. -/
def atlasCandEval (a : AtlasAddr) : Real := Radd (atlasSeedWeight a.block) (scaleShift a.scale)

/-- The address of a raw index `i = 24·ℓ + j`: scale `i / 24`, block `i % 24`. -/
def addrOfNat (i : Nat) : AtlasAddr := ⟨i / 24, ⟨i % 24, by omega⟩⟩

/-- **The candidate diagonal weight** on the raw carrier `ℕ` (for `diagOp`): evaluate the address of
    `i`. Routes the block spectrum through the TYPED seed (`atlasSeedWeight` on `Fin 24`), so the raw
    `atlasEig` tail is never touched (`i % 24 < 24` always). -/
def atlasCandWeight (i : Nat) : Real := atlasCandEval (addrOfNat i)

/-- The candidate weight in raw component form (definitional). -/
theorem atlasCandWeight_val (i : Nat) :
    atlasCandWeight i = Radd (ofQ ⟨atlasEig (i % 24), 1⟩ Nat.one_pos) (scaleShift (i / 24)) := rfl

/-- The candidate weight at a scale-tower index `24·ℓ` (block `0`): `M₂₄(0) + ℓ·log 5`. -/
theorem atlasCandWeight_mul24 (ℓ : Nat) :
    atlasCandWeight (24 * ℓ) = Radd (ofQ ⟨atlasEig 0, 1⟩ Nat.one_pos) (scaleShift ℓ) := by
  rw [atlasCandWeight_val]
  have hm : (24 * ℓ) % 24 = 0 := by omega
  have hd : (24 * ℓ) / 24 = ℓ := by omega
  rw [hm, hd]

-- ===========================================================================
-- Base-action agreement with the seed, and refinement intertwining.
-- ===========================================================================

/-- **Base agreement**: on the carrier (`i < 24`, scale `0`) the candidate weight equals the `Fin 24`
    seed weight — the candidate restricts to `M₂₄` on the base block. -/
theorem atlasCandWeight_base (i : Nat) (h : i < 24) :
    Req (atlasCandWeight i) (atlasSeedWeight ⟨i, h⟩) := by
  rw [atlasCandWeight_val]
  have hm : i % 24 = i := Nat.mod_eq_of_lt h
  have hd : i / 24 = 0 := Nat.div_eq_of_lt h
  rw [hm, hd]
  have hs0 : scaleShift 0 = zero := rfl
  rw [hs0]
  exact Radd_zero _

/-- **Base-ACTION agreement with `atlasSeedOp`**: on `CVec 24` the candidate operator `diagOp
    atlasCandWeight 24` acts exactly as the finite seed `atlasSeedOp` (matrix-action equality, not just
    weight equality). So the candidate genuinely extends the seed. -/
theorem atlasCandOp_base_action (x : CVec 24) :
    CVecEq (diagOp atlasCandWeight 24 x) (atlasSeedOp x) := by
  intro i
  show Ceq (Cmul (Cofreal (atlasCandWeight i.val)) (x i)) (Cmul (Cofreal (atlasSeedWeight i)) (x i))
  exact Cmul_congr ⟨atlasCandWeight_base i.val i.isLt, Req_refl zero⟩ (Ceq_refl (x i))

/-- **Refinement intertwining**: lifting the scale by one level adds exactly `log 5` to the
    eigenvalue (the sourced refinement step `orbitShift 5 (ℓ+1) = log 5 + orbitShift 5 ℓ`). -/
theorem atlasCandEval_scale_succ (ℓ : Nat) (j : Fin 24) :
    Req (atlasCandEval ⟨ℓ + 1, j⟩) (Radd (atlasCandEval ⟨ℓ, j⟩) (logN 5 (by decide))) := by
  show Req (Radd (atlasSeedWeight j) (scaleShift (ℓ + 1)))
           (Radd (Radd (atlasSeedWeight j) (scaleShift ℓ)) (logN 5 (by decide)))
  refine Req_trans (Radd_congr (Req_refl _) (orbitShift_succ 5 (by decide) ℓ)) ?_
  refine Req_trans (Radd_congr (Req_refl _) (Radd_comm (logN 5 (by decide)) (scaleShift ℓ))) ?_
  exact Req_symm (Radd_assoc _ (scaleShift ℓ) (logN 5 (by decide)))

/-- **The scale gap is CONSTANT `= log 5`**: `atlasCandWeight(24(ℓ+1)) = atlasCandWeight(24ℓ) + log 5`.
    So the scale-tower spectrum is an ARITHMETIC PROGRESSION — the structural feature that rejects this
    candidate as the HP operator (the Riemann zeros' gaps shrink, they are not constant). -/
theorem atlasCand_scale_gap (ℓ : Nat) :
    Req (atlasCandWeight (24 * (ℓ + 1)))
        (Radd (atlasCandWeight (24 * ℓ)) (logN 5 (by decide))) := by
  rw [atlasCandWeight_mul24 ℓ, atlasCandWeight_mul24 (ℓ + 1)]
  refine Req_trans (Radd_congr (Req_refl _) (orbitShift_succ 5 (by decide) ℓ)) ?_
  refine Req_trans (Radd_congr (Req_refl _) (Radd_comm (logN 5 (by decide)) (scaleShift ℓ))) ?_
  exact Req_symm (Radd_assoc _ (scaleShift ℓ) (logN 5 (by decide)))

-- ===========================================================================
-- Genuine unboundedness (the property the finite seed lacked).
-- ===========================================================================

/-- **Each scale step adds `≥ 1`**: `atlasCandWeight(24ℓ) + 1 ≤ atlasCandWeight(24(ℓ+1))` (constant
    gap `log 5 ≥ 1`). The diagonal strictly increases without bound along the scale tower. -/
theorem atlasCand_scale_step (ℓ : Nat) :
    Rle (Radd (atlasCandWeight (24 * ℓ)) one) (atlasCandWeight (24 * (ℓ + 1))) :=
  Rle_trans (Radd_le_add (Rle_refl _) log5_ge_one)
    (Rle_of_Req (Req_symm (atlasCand_scale_gap ℓ)))

/-- The scale-tower diagonal dominates `atlasCandWeight 0 + ℓ` (each step adds `≥ 1`). -/
theorem atlasCandWeight_scale_ge :
    ∀ ℓ, Rle (Radd (atlasCandWeight 0) (RofNat ℓ)) (atlasCandWeight (24 * ℓ))
  | 0 => Rle_of_Req (Req_trans (Radd_congr (Req_refl _) RofNat_zero_loc) (Radd_zero _))
  | (ℓ + 1) => by
      refine Rle_trans (Rle_of_Req ?_)
        (Rle_trans (Radd_le_add (atlasCandWeight_scale_ge ℓ) (Rle_refl one)) (atlasCand_scale_step ℓ))
      refine Req_trans (Radd_congr (Req_refl _) (RofNat_succ_loc ℓ)) ?_
      exact Req_symm (Radd_assoc _ (RofNat ℓ) one)

/-- **GENUINE UNBOUNDEDNESS**: for every bound `B` there is an index whose diagonal entry exceeds it —
    `∀ B, ∃ i, RofNat B ≤ atlasCandWeight i`. So the candidate operator is UNBOUNDED and hence
    NON-finite-rank, unlike the seed `M₂₄ ⊕ 0`. -/
theorem atlasCand_unbounded (B : Nat) : ∃ i, Rle (RofNat B) (atlasCandWeight i) := by
  have hcw0 : Rnonneg (atlasCandWeight 0) := by
    rw [atlasCandWeight_val]
    exact Rnonneg_Radd (Rnonneg_ofQ (by decide) (by decide)) Rnonneg_zero
  refine ⟨24 * B, ?_⟩
  refine Rle_trans (Rle_trans (Rle_self_Radd_right hcw0)
    (Rle_of_Req (Radd_comm (RofNat B) (atlasCandWeight 0)))) (atlasCandWeight_scale_ge B)

-- ===========================================================================
-- The generic direct-limit descent of a real-diagonal, and the candidate operator.
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

/-- **The candidate operator on the direct-limit core** — the descent of the unbounded diagonal
    `atlasCandWeight`. This is the first UNBOUNDED symmetric operator on `dlimPreHilbert`. -/
def dlimCand : DLimRaw → DLimRaw := dlimDiagW atlasCandWeight

/-- **The candidate as a typed symmetric operator on `dlimPreHilbert`** — CANDIDATE, not the HP
    operator: it is unbounded (`atlasCand_unbounded`) and symmetric, but its spectrum is an arithmetic
    progression (`atlasCand_scale_gap`), rejected at the spectral/zero bridge. Crux `none`. -/
def atlasCandDLimOp : PreHilbertSymOp dlimPreHilbert where
  op := dlimCand
  op_congr := fun h => dlimDiagW_wd atlasCandWeight h
  op_add := dlimDiagW_add atlasCandWeight
  op_smul := dlimDiagW_smul atlasCandWeight
  op_herm := dlimDiagW_herm atlasCandWeight

-- ===========================================================================
-- The constructive spectral rejection: the diagonal has floor −1 but peak 10, so
-- its point spectrum is NOT closed under μ ↦ −μ (fails HP trace-symmetry).
-- ===========================================================================

/-- `n·x ≥ 0` for `x ≥ 0`. -/
private theorem Rnonneg_Rnsmul (x : Real) (h : Rnonneg x) : ∀ ℓ, Rnonneg (Rnsmul ℓ x)
  | 0 => Rnonneg_zero
  | (ℓ + 1) => Rnonneg_Radd h (Rnonneg_Rnsmul x h ℓ)

/-- The per-scale shift is nonnegative (`ℓ·log 5 ≥ 0`). -/
private theorem scaleShift_nonneg (ℓ : Nat) : Rnonneg (scaleShift ℓ) :=
  Rnonneg_Rnsmul (logN 5 (by decide)) (Rnonneg_logN 5 (by decide)) ℓ

/-- `−1` as `ofQ`. -/
private theorem Rneg_one_eq_ofQ : Req (Rneg one) (ofQ (⟨-1, 1⟩ : Q) (by decide)) :=
  Req_of_seq_Qeq (fun _ => by show Qeq (neg (⟨1, 1⟩ : Q)) (⟨-1, 1⟩ : Q); decide)

/-- **WEIGHT FLOOR**: every block-ladder diagonal weight is `≥ −1` — the block eigenvalue is `≥ −1`
    (`atlasEig_range`) and the scale shift is `≥ 0`. The spectral floor that makes the point spectrum
    asymmetric under negation. -/
theorem atlasCandWeight_ge_neg_one (i : Nat) : Rle (Rneg one) (atlasCandWeight i) := by
  rw [atlasCandWeight_val]
  have hblock : Rle (Rneg one) (ofQ ⟨atlasEig (i % 24), 1⟩ Nat.one_pos) := by
    refine Rle_trans (Rle_of_Req Rneg_one_eq_ofQ) (Rle_ofQ_ofQ (by decide) Nat.one_pos ?_)
    have h1 := (atlasEig_range (i % 24)).1
    simp only [Qle]; push_cast; omega
  refine Rle_trans (Rle_of_Req (Req_symm (Radd_zero (Rneg one)))) ?_
  exact Radd_le_add hblock (Rle_zero_of_Rnonneg (scaleShift_nonneg _))

/-- `−1 + 10 = 9`. -/
private theorem neg_one_add_ten : Req (Radd (Rneg one) (ofQ (⟨10, 1⟩ : Q) Nat.one_pos))
    (ofQ (⟨9, 1⟩ : Q) Nat.one_pos) :=
  Req_trans (Radd_congr Rneg_one_eq_ofQ (Req_refl _))
    (Req_of_seq_Qeq (fun _ => by show Qeq (add (⟨-1, 1⟩ : Q) (⟨10, 1⟩ : Q)) (⟨9, 1⟩ : Q); decide))

/-- **SPECTRAL ASYMMETRY (`−10` below the whole diagonal)**: `w_i + 10 > 0` (strictly, `Pos`) for every
    `i` — since `w_i ≥ −1`, `w_i + 10 ≥ 9 ≥ 1`. So `−10` lies strictly below EVERY diagonal weight,
    while `w₀ = 10` IS a weight. A point spectrum with `10` but nothing near `−10` is not closed under
    `μ ↦ −μ` — the block-ladder fails the HP trace-symmetry requirement. Zero-free rejection. -/
theorem atlasCand_gt_neg_ten (i : Nat) :
    Pos (Radd (atlasCandWeight i) (ofQ (⟨10, 1⟩ : Q) Nat.one_pos)) := by
  have h9 : Rle one (ofQ (⟨9, 1⟩ : Q) Nat.one_pos) :=
    Rle_ofQ_ofQ (by decide) Nat.one_pos (by decide)
  have hstep : Rle (ofQ (⟨9, 1⟩ : Q) Nat.one_pos)
      (Radd (atlasCandWeight i) (ofQ ⟨10, 1⟩ Nat.one_pos)) :=
    Rle_trans (Rle_of_Req (Req_symm neg_one_add_ten))
      (Radd_le_add (atlasCandWeight_ge_neg_one i) (Rle_refl _))
  exact Pos_of_Rle_one (Rle_trans h9 hstep)

/-- **`w₀ = 10`** — a diagonal weight strictly exceeding `2` (the peak witnessing the asymmetry). -/
theorem atlasCandWeight_zero_eq_ten :
    Req (atlasCandWeight 0) (ofQ (⟨10, 1⟩ : Q) Nat.one_pos) := by
  show Req (Radd (ofQ ⟨10, 1⟩ Nat.one_pos) zero) (ofQ ⟨10, 1⟩ Nat.one_pos)
  exact Radd_zero _

end UOR.Bridge.F1Square.Square
