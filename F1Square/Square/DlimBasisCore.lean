/-
# Neutral coordinate-basis core

The standard coordinate basis `dlimBasis i` of the finite-support direct limit, together with its
orthonormality seed (`dlimBasis_normalized`, `dlimBasis_self_re`).  Kept in a NEUTRAL module (imports
only `FinDirectLimit`) so the completion / coordinate layer does not have to import upward from the
operator core `DiagonalOperatorCore`.
-/
import F1Square.Square.FinDirectLimit

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

private theorem rneg_zero_loc : Req (Rneg zero) zero :=
  Req_of_seq_Qeq (fun _ => by show Qeq (neg (⟨0, 1⟩ : Q)) ⟨0, 1⟩; decide)

private theorem cmul_czero_loc (z : Complex) : Ceq (Cmul z Czero) Czero :=
  ⟨Req_trans (Radd_congr (Rmul_zero z.re) (Rneg_congr (Rmul_zero z.im))) (Radd_neg zero),
   Req_trans (Radd_congr (Rmul_zero z.re) (Rmul_zero z.im)) (Radd_zero zero)⟩

/-- The standard basis vector in `CVec N`: `1` at coordinate `j`, `0` elsewhere. -/
def stdBasisVec (N : Nat) (j : Fin N) : CVec N :=
  fun k => if k.val = j.val then Cone else Czero

/-- The `i`-th coordinate basis vector in the direct limit — presented at stage `i+1` with its spike
    at the LAST coordinate `i` (so the finite-sum head over coords `0..i-1` is entirely `0`). -/
def dlimBasis (i : Nat) : DLimRaw := ⟨i + 1, stdBasisVec (i + 1) ⟨i, Nat.lt_succ_self i⟩⟩

/-- `conj 1 ≈ 1`. -/
private theorem Cconj_Cone_loc : Ceq (Cconj Cone) Cone := ⟨Req_refl _, rneg_zero_loc⟩

/-- `z + 0 ≈ z`. -/
private theorem cadd_czero_r (z : Complex) : Ceq (Cadd z Czero) z :=
  ⟨Radd_zero z.re, Radd_zero z.im⟩

/-- A finite sum of entries each `≈ 0` is `≈ 0`. -/
private theorem cvecSum_eq_zero : ∀ (N : Nat) (g : CVec N), (∀ k, Ceq (g k) Czero) →
    Ceq (cvecSum N g) Czero
  | 0, _, _ => Ceq_refl _
  | (N + 1), g, h => by
      refine Ceq_trans (Cadd_congr
        (cvecSum_eq_zero N _ (fun k => h ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩))
        (h ⟨N, Nat.lt_succ_self N⟩)) ?_
      exact cadd_czero_r Czero

/-- **The basis vector is normalized**: `⟨eᵢ, eᵢ⟩ ≈ 1`. The spike (last coordinate) contributes
    `conj(1)·1 ≈ 1`; every other coordinate contributes `conj(0)·0 ≈ 0`. -/
theorem dlimBasis_normalized (i : Nat) : Ceq (dlimInner (dlimBasis i) (dlimBasis i)) Cone := by
  refine Ceq_trans (dlimInner_mk (i + 1) _ _) ?_
  show Ceq (Cadd
      (cvecSum i (fun k => Cmul (Cconj (if k.val = i then Cone else Czero))
                                (if k.val = i then Cone else Czero)))
      (Cmul (Cconj (if (i : Nat) = i then Cone else Czero)) (if (i : Nat) = i then Cone else Czero)))
    Cone
  have hhead : Ceq (cvecSum i (fun k => Cmul (Cconj (if k.val = i then Cone else Czero))
                                             (if k.val = i then Cone else Czero))) Czero := by
    refine cvecSum_eq_zero i _ (fun k => ?_)
    rw [if_neg (Nat.ne_of_lt k.isLt)]
    exact cmul_czero_loc _
  have hlast : Ceq (Cmul (Cconj (if (i : Nat) = i then Cone else Czero))
                         (if (i : Nat) = i then Cone else Czero)) Cone := by
    rw [if_pos rfl]
    exact Ceq_trans (Cmul_congr Cconj_Cone_loc (Ceq_refl Cone)) (Cmul_one Cone)
  refine Ceq_trans (Cadd_congr hhead hlast) ?_
  exact Ceq_trans (Cadd_comm Czero Cone) (cadd_czero_r Cone)

/-- **The basis vector's squared norm is `1`** (the real part of `⟨eᵢ,eᵢ⟩≈1`). -/
theorem dlimBasis_self_re (i : Nat) : Req (dlimInner (dlimBasis i) (dlimBasis i)).re one :=
  (dlimBasis_normalized i).1


-- ===========================================================================
-- ORTHONORMALITY + genuine COEFFICIENT RECOVERY (reviewer item 2).
-- ===========================================================================
/-- Turn a genuine equality of complex numbers into a `Ceq`. -/
private theorem Ceq_of_eq {a b : Complex} (h : a = b) : Ceq a b := by
  cases h; exact Ceq_refl a

-- ---------------------------------------------------------------------------
-- Single-coordinate extraction from a finite sum.
-- ---------------------------------------------------------------------------

/-- If `g` vanishes at every coordinate except `j`, the finite sum is `g j`. -/
private theorem cvecSum_single : ∀ (N : Nat) (g : CVec N) (j : Fin N),
    (∀ k : Fin N, k.val ≠ j.val → Ceq (g k) Czero) → Ceq (cvecSum N g) (g j)
  | 0, _, j, _ => j.elim0
  | (N + 1), g, j, hz => by
      by_cases hjN : j.val = N
      · -- `j` is the last coordinate: head sum vanishes, last term is `g j`.
        have hhead : Ceq (cvecSum N (fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)) Czero :=
          cvecSum_eq_zero N _ (fun k => hz ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩
            (by show k.val ≠ j.val; have h1 : k.val < N := k.isLt; omega))
        have heq : (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) = j := Fin.ext hjN.symm
        show Ceq (Cadd (cvecSum N (fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
                       (g ⟨N, Nat.lt_succ_self N⟩)) (g j)
        exact Ceq_trans (Cadd_congr hhead (Ceq_of_eq (congrArg g heq)))
          (Ceq_trans (Cadd_comm Czero (g j)) (cadd_czero_r (g j)))
      · -- `j` is not the last coordinate: last term vanishes, recurse on the head.
        have hjlt : j.val < N := by have h1 : j.val < N + 1 := j.isLt; omega
        have hlast : Ceq (g ⟨N, Nat.lt_succ_self N⟩) Czero :=
          hz ⟨N, Nat.lt_succ_self N⟩ (by show N ≠ j.val; omega)
        have hhead : Ceq (cvecSum N (fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
                         (g ⟨j.val, Nat.lt_succ_of_lt hjlt⟩) :=
          cvecSum_single N (fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) ⟨j.val, hjlt⟩
            (fun k hk => hz ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ hk)
        have hjeq : (⟨j.val, Nat.lt_succ_of_lt hjlt⟩ : Fin (N + 1)) = j := Fin.ext rfl
        show Ceq (Cadd (cvecSum N (fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
                       (g ⟨N, Nat.lt_succ_self N⟩)) (g j)
        exact Ceq_trans (Cadd_congr hhead hlast)
          (Ceq_trans (cadd_czero_r (g ⟨j.val, Nat.lt_succ_of_lt hjlt⟩))
                     (Ceq_of_eq (congrArg g hjeq)))

/-- Pointwise value of the included `i`-th basis vector at coordinate `k`: `1` if `k = i`, else `0`. -/
private theorem cvInc_stdBasis_apply {i K : Nat} (hiK : i + 1 ≤ K) (k : Fin K) :
    Ceq ((cvInc hiK (stdBasisVec (i + 1) ⟨i, Nat.lt_succ_self i⟩)) k)
        (if k.val = i then Cone else Czero) := by
  by_cases hk : k.val < i + 1
  · simp only [cvInc, stdBasisVec, dif_pos hk]
    exact Ceq_refl _
  · have hne : ¬ (k.val = i) := by intro hc; apply hk; rw [hc]; exact Nat.lt_succ_self i
    simp only [cvInc, stdBasisVec, dif_neg hk, if_neg hne]
    exact Ceq_refl _

-- ---------------------------------------------------------------------------
-- targets (leaf names end _bo)
-- ---------------------------------------------------------------------------

/-- **Genuine coefficient recovery**: pairing against `eᵢ` extracts the `i`-th coordinate. -/
theorem dlimBasis_coord_bo (i N : Nat) (h : i < N) (x : CVec N) :
    Ceq (dlimInner (dlimBasis i) (dlimMk x)) (x ⟨i, h⟩) := by
  refine Ceq_trans (Ceq_symm (dlimInner_eval (dlimBasis i) (dlimMk x) h (Nat.le_refl N))) ?_
  refine Ceq_trans (cInner_congr (CVecEq_refl _) (cvInc_id x)) ?_
  show Ceq (cvecSum N (fun k => Cmul (Cconj
      ((cvInc h (stdBasisVec (i + 1) ⟨i, Nat.lt_succ_self i⟩)) k)) (x k))) (x ⟨i, h⟩)
  refine Ceq_trans (cvecSum_single N
    (fun k => Cmul (Cconj ((cvInc h (stdBasisVec (i + 1) ⟨i, Nat.lt_succ_self i⟩)) k)) (x k))
    ⟨i, h⟩ (fun k hk => ?_)) ?_
  · -- off-diagonal terms vanish
    have hk' : k.val ≠ i := hk
    refine Ceq_trans (Cmul_congr (Cconj_congr (cvInc_stdBasis_apply h k)) (Ceq_refl (x k))) ?_
    rw [if_neg hk']
    exact Ceq_trans (Cmul_congr Cconj_Czero (Ceq_refl (x k)))
      (Ceq_trans (Cmul_comm Czero (x k)) (cmul_czero_loc (x k)))
  · -- the diagonal term equals `x ⟨i, h⟩`
    refine Ceq_trans (Cmul_congr (Cconj_congr (cvInc_stdBasis_apply h ⟨i, h⟩))
      (Ceq_refl (x ⟨i, h⟩))) ?_
    rw [if_pos (rfl : (⟨i, h⟩ : Fin N).val = i)]
    exact Ceq_trans (Cmul_congr Cconj_Cone_loc (Ceq_refl (x ⟨i, h⟩)))
      (Ceq_trans (Cmul_comm Cone (x ⟨i, h⟩)) (Cmul_one (x ⟨i, h⟩)))

/-- **Orthogonality** of the coordinate basis: `⟨eᵢ, eⱼ⟩ ≈ 0` for `i ≠ j`. -/
theorem dlimBasis_ortho_bo (i j : Nat) (h : i ≠ j) :
    Ceq (dlimInner (dlimBasis i) (dlimBasis j)) Czero := by
  have hiK : i + 1 ≤ max (i + 1) (j + 1) := Nat.le_max_left _ _
  have hjK : j + 1 ≤ max (i + 1) (j + 1) := Nat.le_max_right _ _
  refine Ceq_trans (Ceq_symm (dlimInner_eval (dlimBasis i) (dlimBasis j) hiK hjK)) ?_
  show Ceq (cvecSum (max (i + 1) (j + 1))
    (fun k => Cmul (Cconj ((cvInc hiK (stdBasisVec (i + 1) ⟨i, Nat.lt_succ_self i⟩)) k))
                   ((cvInc hjK (stdBasisVec (j + 1) ⟨j, Nat.lt_succ_self j⟩)) k))) Czero
  refine cvecSum_eq_zero _ _ (fun k => ?_)
  by_cases hki : k.val = i
  · -- `k = i`, so `k ≠ j`; the `eⱼ` factor is `0`.
    have hkj : ¬ (k.val = j) := fun hc => h (hki ▸ hc)
    refine Ceq_trans (Cmul_congr (Ceq_refl _) (cvInc_stdBasis_apply hjK k)) ?_
    rw [if_neg hkj]
    exact cmul_czero_loc _
  · -- `k ≠ i`; the `eᵢ` factor is `0`.
    refine Ceq_trans (Cmul_congr (Cconj_congr (cvInc_stdBasis_apply hiK k)) (Ceq_refl _)) ?_
    rw [if_neg hki]
    exact Ceq_trans (Cmul_congr Cconj_Czero (Ceq_refl _))
      (Ceq_trans (Cmul_comm Czero _) (cmul_czero_loc _))

end UOR.Bridge.F1Square.Square
