/-
# The direct-limit completion as a `FinPreHilbert`

This file packages the constructive completion of the finite-stage colimit — the Bishop-Cauchy
setoid `(DLimCompletionRaw, DLimCompletionEq)` with its complex-module structure and the completed
inner product `completedInner ⟨X,Y⟩ := lim ⟨X_{σn}, Y_{σn}⟩` — as a single `FinPreHilbert` bundle.

Every field is discharged by an already-proven lemma:

* setoid / module / scalar-action (from `DlimHilbertCompletion`): `DLimCompletionEq_*`,
  `dlimCompletionAdd_*`, `dlimCompletionSmul_*`;
* inner product (from `DlimCompletedInner`): the six sesquilinear/Hermitian/positive-definite laws
  `completedInner_congr`, `_add_right`, `_smul_right`, `_conj`, `_self_im`, `_self_nonneg`,
  `_self_definite`.

This is a genuine PRE-Hilbert bundle (a complex inner-product space up to the setoid). It asserts NO
completeness of the setoid, NO dense isometry from the colimit, NO operator/adjoint/self-adjointness,
and NO Atlas provenance — those remain open.
-/
import F1Square.Square.DlimCompletedInner
import F1Square.Square.FinPreHilbert

namespace UOR.Bridge.F1Square.Square

/-- **The completed direct limit as a `FinPreHilbert`.** The carrier is `DLimCompletionRaw` modulo the
    norm-null setoid `DLimCompletionEq`; the inner product is the completed `completedInner`. All 27
    fields reduce to lemmas proven in `DlimHilbertCompletion` (module) and `DlimCompletedInner` (inner). -/
def dlimCompletionPreHilbert : FinPreHilbert where
  V := DLimCompletionRaw
  veq := DLimCompletionEq
  add := dlimCompletionAdd
  smul := dlimCompletionSmul
  vzero := dlimCompletionZero
  vneg := dlimCompletionNeg
  inner := completedInner
  -- setoid
  veq_refl := DLimCompletionEq_refl
  veq_symm := DLimCompletionEq_symm
  veq_trans := DLimCompletionEq_trans
  -- module congruence
  add_congr := dlimCompletionAdd_congr
  smul_congr := dlimCompletionSmul_congr
  -- additive group + scalar action
  add_comm := dlimCompletionAdd_comm
  add_assoc := dlimCompletionAdd_assoc
  add_zero := dlimCompletionAdd_zero
  add_neg := dlimCompletionAdd_neg
  smul_add := dlimCompletionSmul_add
  add_smul := dlimCompletionSmul_Cadd
  smul_assoc := dlimCompletionSmul_assoc
  one_smul := dlimCompletionSmul_one
  zero_smul := dlimCompletionZero_smul
  smul_zero := dlimCompletionSmul_zero
  -- inner product: sesquilinear, Hermitian, positive-definite
  inner_congr := completedInner_congr
  inner_add_right := completedInner_add_right
  inner_smul_right := completedInner_smul_right
  inner_conj := completedInner_conj
  inner_self_im := completedInner_self_im
  inner_self_nonneg := completedInner_self_nonneg
  inner_self_definite := fun _ h => completedInner_self_definite h

end UOR.Bridge.F1Square.Square
