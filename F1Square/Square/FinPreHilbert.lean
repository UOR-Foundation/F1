/-
F1 square — **the packaged finite pre-Hilbert object** over the zeta-free complex inner-product
space of `FinInnerProduct`. This is the typed bundle the raw lemmas only gestured at: an actual
Lean `Setoid` on the scalars and on the vectors, a bundled constructive-ring record for the complex
scalars, and a `FinPreHilbert` record that carries the carrier, its setoid, the module operations,
the inner product, and ALL the sesquilinear/Hermitian/positivity/definiteness laws as fields —
instantiated at `(CVec N, CVecEq, cInner N)` by `finPreHilbert`.

New content beyond the raw laws: the `Setoid Complex` / `Setoid (CVec N)` instances, the missing
zero-action laws `cvSmul_zero` (`c·0 = 0`) and `cvZero_smul` (`0·x = 0`), the definiteness in bundled
form `cInner_self_definite_vec : ⟨x,x⟩ ≈ 0 → x ≈ 0` (setoid equality, not coordinatewise), and the
two records `CommRingoid`/`FinPreHilbert` with their genuine instances.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; fully zeta-free (import cone
is `FinInnerProduct`'s zero-free cone). Crux fields `none`.
-/

import F1Square.Square.FinInnerProduct

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- Local zeta-free ring trivialities (private; the public copies are Pi/ζ-tainted).
-- ===========================================================================

private theorem cadd_zero' (z : Complex) : Ceq (Cadd z Czero) z := ⟨Radd_zero z.re, Radd_zero z.im⟩

private theorem cadd_neg' (z : Complex) : Ceq (Cadd z (Cneg z)) Czero :=
  ⟨Radd_neg z.re, Radd_neg z.im⟩

private theorem cmul_czero' (z : Complex) : Ceq (Cmul z Czero) Czero :=
  ⟨Req_trans (Radd_congr (Rmul_zero z.re) (Rneg_congr (Rmul_zero z.im))) (Radd_neg zero),
   Req_trans (Radd_congr (Rmul_zero z.re) (Rmul_zero z.im)) (Radd_zero zero)⟩

private theorem czero_cmul' (z : Complex) : Ceq (Cmul Czero z) Czero :=
  Ceq_trans (Cmul_comm Czero z) (cmul_czero' z)

private theorem rneg_zero' : Req (Rneg zero) zero :=
  Req_of_seq_Qeq (fun _ => by show Qeq (neg (⟨0, 1⟩ : Q)) ⟨0, 1⟩; decide)

private theorem cneg_czero' : Ceq (Cneg Czero) Czero := ⟨rneg_zero', rneg_zero'⟩

-- ===========================================================================
-- Setoid instances: the actual Lean setoids on scalars and vectors.
-- ===========================================================================

/-- The complex numbers form a `Setoid` under Bishop equality `Ceq`. -/
instance : Setoid Complex where
  r := Ceq
  iseqv := ⟨Ceq_refl, fun h => Ceq_symm h, fun h₁ h₂ => Ceq_trans h₁ h₂⟩

/-- `CVec N` forms a `Setoid` under pointwise equivalence `CVecEq`. -/
instance (N : Nat) : Setoid (CVec N) where
  r := CVecEq
  iseqv := ⟨CVecEq_refl, fun h => CVecEq_symm h, fun h₁ h₂ => CVecEq_trans h₁ h₂⟩

-- ===========================================================================
-- The missing zero-action laws and bundled definiteness.
-- ===========================================================================

/-- `c · 0 = 0` (scalar action annihilates the zero vector). -/
theorem cvSmul_zero (N : Nat) (c : Complex) : CVecEq (cvSmul c (cvZero N)) (cvZero N) :=
  fun _ => cmul_czero' c

/-- `0 · x = 0` (the zero scalar annihilates every vector). -/
theorem cvZero_smul {N : Nat} (x : CVec N) : CVecEq (cvSmul Czero x) (cvZero N) :=
  fun i => czero_cmul' (x i)

/-- **Definiteness in bundled setoid form**: `⟨x, x⟩ ≈ 0 ⟹ x ≈ 0` (equality in the carrier's
    setoid, not merely coordinatewise). Directly `cInner_self_definite`, repackaged as `CVecEq`. -/
theorem cInner_self_definite_vec (N : Nat) (x : CVec N) (h : Ceq (cInner N x x) Czero) :
    CVecEq x (cvZero N) := cInner_self_definite N x h

-- ===========================================================================
-- The bundled constructive complex scalar ring (up to `Ceq`).
-- ===========================================================================

/-- A **commutative ring up to a Bishop-style equivalence** (`req`): the constructive-ring packaging
    the complex scalars satisfy, with every law stated modulo `req` and both operations congruent. -/
structure CommRingoid where
  /-- the carrier -/
  Car : Type
  /-- the equivalence relation -/
  req : Car → Car → Prop
  req_refl : ∀ a, req a a
  req_symm : ∀ {a b}, req a b → req b a
  req_trans : ∀ {a b c}, req a b → req b c → req a c
  add : Car → Car → Car
  mul : Car → Car → Car
  neg : Car → Car
  zero : Car
  one : Car
  add_congr : ∀ {a a' b b'}, req a a' → req b b' → req (add a b) (add a' b')
  mul_congr : ∀ {a a' b b'}, req a a' → req b b' → req (mul a b) (mul a' b')
  add_comm : ∀ a b, req (add a b) (add b a)
  add_assoc : ∀ a b c, req (add (add a b) c) (add a (add b c))
  add_zero : ∀ a, req (add a zero) a
  add_neg : ∀ a, req (add a (neg a)) zero
  mul_comm : ∀ a b, req (mul a b) (mul b a)
  mul_assoc : ∀ a b c, req (mul (mul a b) c) (mul a (mul b c))
  mul_one : ∀ a, req (mul a one) a
  distrib : ∀ a b c, req (mul a (add b c)) (add (mul a b) (mul a c))

/-- **The complex scalars, packaged as a `CommRingoid`** — a genuine constructive commutative ring
    up to `Ceq`, the scalar object the finite pre-Hilbert space is a module over. -/
def complexRingoid : CommRingoid where
  Car := Complex
  req := Ceq
  req_refl := Ceq_refl
  req_symm := fun h => Ceq_symm h
  req_trans := fun h₁ h₂ => Ceq_trans h₁ h₂
  add := Cadd
  mul := Cmul
  neg := Cneg
  zero := Czero
  one := Cone
  add_congr := fun ha hb => Cadd_congr ha hb
  mul_congr := fun ha hb => Cmul_congr ha hb
  add_comm := Cadd_comm
  add_assoc := Cadd_assoc
  add_zero := cadd_zero'
  add_neg := cadd_neg'
  mul_comm := Cmul_comm
  mul_assoc := Cmul_assoc
  mul_one := Cmul_one
  distrib := Cmul_distrib

-- ===========================================================================
-- The finite pre-Hilbert record and its instance at `cInner`.
-- ===========================================================================

/-- A **finite pre-Hilbert space** (constructive, up to a Bishop setoid `veq` on vectors and `Ceq` on
    the complex scalars): a carrier `V` with a setoid, complex-module operations obeying the module
    laws (congruence, additive group, scalar action including the zero-actions), and a sesquilinear
    Hermitian positive-DEFINITE inner product. Every axiom is a field; nothing is left implicit. -/
structure FinPreHilbert where
  /-- the vector carrier -/
  V : Type
  /-- the vector setoid -/
  veq : V → V → Prop
  add : V → V → V
  smul : Complex → V → V
  vzero : V
  vneg : V → V
  inner : V → V → Complex
  -- setoid
  veq_refl : ∀ x, veq x x
  veq_symm : ∀ {x y}, veq x y → veq y x
  veq_trans : ∀ {x y z}, veq x y → veq y z → veq x z
  -- module congruence
  add_congr : ∀ {x x' y y'}, veq x x' → veq y y' → veq (add x y) (add x' y')
  smul_congr : ∀ {c c' x x'}, Ceq c c' → veq x x' → veq (smul c x) (smul c' x')
  -- additive group + scalar action
  add_comm : ∀ x y, veq (add x y) (add y x)
  add_assoc : ∀ x y z, veq (add (add x y) z) (add x (add y z))
  add_zero : ∀ x, veq (add x vzero) x
  add_neg : ∀ x, veq (add x (vneg x)) vzero
  smul_add : ∀ c x y, veq (smul c (add x y)) (add (smul c x) (smul c y))
  add_smul : ∀ c d x, veq (smul (Cadd c d) x) (add (smul c x) (smul d x))
  smul_assoc : ∀ c d x, veq (smul c (smul d x)) (smul (Cmul c d) x)
  one_smul : ∀ x, veq (smul Cone x) x
  zero_smul : ∀ x, veq (smul Czero x) vzero
  smul_zero : ∀ c, veq (smul c vzero) vzero
  -- inner product: sesquilinear, Hermitian, positive-definite
  inner_congr : ∀ {x x' y y'}, veq x x' → veq y y' → Ceq (inner x y) (inner x' y')
  inner_add_right : ∀ x y z, Ceq (inner x (add y z)) (Cadd (inner x y) (inner x z))
  inner_smul_right : ∀ c x y, Ceq (inner x (smul c y)) (Cmul c (inner x y))
  inner_conj : ∀ x y, Ceq (inner x y) (Cconj (inner y x))
  inner_self_im : ∀ x, Req (inner x x).im zero
  inner_self_nonneg : ∀ x, Rnonneg (inner x x).re
  inner_self_definite : ∀ x, Ceq (inner x x) Czero → veq x vzero

/-- **The finite complex space `Fin N → ℂ` as a genuine `FinPreHilbert`** — every field discharged by
    the proved laws of `FinInnerProduct`, with the zero-actions and bundled definiteness from above.
    This is the typed pre-Hilbert object; `cInner` is its inner product. -/
def finPreHilbert (N : Nat) : FinPreHilbert where
  V := CVec N
  veq := CVecEq
  add := cvAdd
  smul := cvSmul
  vzero := cvZero N
  vneg := cvNeg
  inner := cInner N
  veq_refl := CVecEq_refl
  veq_symm := fun h => CVecEq_symm h
  veq_trans := fun h₁ h₂ => CVecEq_trans h₁ h₂
  add_congr := fun hx hy => cvAdd_congr hx hy
  smul_congr := fun hc hx => cvSmul_congr hc hx
  add_comm := cvAdd_comm
  add_assoc := cvAdd_assoc
  add_zero := cvAdd_zero
  add_neg := cvAdd_neg
  smul_add := cvSmul_cvAdd
  add_smul := cvSmul_Cadd
  smul_assoc := cvSmul_assoc
  one_smul := cvSmul_one
  zero_smul := cvZero_smul
  smul_zero := cvSmul_zero N
  inner_congr := fun hx hy => cInner_congr hx hy
  inner_add_right := cInner_add_right N
  inner_smul_right := cInner_smul_right N
  inner_conj := cInner_conj N
  inner_self_im := cInner_self_im_zero N
  inner_self_nonneg := cInner_self_re_nonneg N
  inner_self_definite := cInner_self_definite_vec N

-- ===========================================================================
-- Linear isometries `CVec N ↪ CVec M` for every `N ≤ M`, with identity and
-- composition coherence — the genuine directed system.
-- ===========================================================================

/-- Gap form: the sum over `Fin (N+k)` of a `0`-padding of `f : CVec N` equals the sum over `Fin N`
    of `f` (the `k` padded coordinates contribute nothing). Structural induction on `k`. -/
private theorem cvecSum_pad_gap {N : Nat} (f : CVec N) : ∀ (k : Nat),
    Ceq (cvecSum (N + k) (fun i => if hi : i.val < N then f ⟨i.val, hi⟩ else Czero)) (cvecSum N f)
  | 0 => cvecSum_congr N _ _ (fun i => by simp only [dif_pos i.isLt]; exact Ceq_refl _)
  | (k + 1) => by
      have hlast : ¬ (N + k < N) := by omega
      show Ceq
        (Cadd (cvecSum (N + k) (fun i => if hi : (i.val : Nat) < N then f ⟨i.val, hi⟩ else Czero))
              (if hi : (N + k : Nat) < N then f ⟨N + k, hi⟩ else Czero)) (cvecSum N f)
      rw [dif_neg hlast]
      exact Ceq_trans (cadd_zero' _) (cvecSum_pad_gap f k)

/-- The finite sum over `Fin M` of a `0`-padding of `f : CVec N` (`N ≤ M`) equals the sum over
    `Fin N` of `f`: the padded coordinates contribute nothing. -/
theorem cvecSum_pad {N M : Nat} (f : CVec N) (h : N ≤ M) :
    Ceq (cvecSum M (fun i => if hi : i.val < N then f ⟨i.val, hi⟩ else Czero)) (cvecSum N f) := by
  obtain ⟨k, rfl⟩ := Nat.le.dest h
  exact cvecSum_pad_gap f k

/-- The **inclusion isometry** `CVec N ↪ CVec M` for `N ≤ M`: pad by `0` on the new coordinates. -/
def cvInc {N M : Nat} (_h : N ≤ M) (x : CVec N) : CVec M :=
  fun i => if hi : i.val < N then x ⟨i.val, hi⟩ else Czero

/-- The inclusion respects the vector setoid. -/
theorem cvInc_congr {N M : Nat} (h : N ≤ M) {x y : CVec N} (hxy : CVecEq x y) :
    CVecEq (cvInc h x) (cvInc h y) := by
  intro i
  by_cases hi : i.val < N
  · simp only [cvInc, dif_pos hi]; exact hxy ⟨i.val, hi⟩
  · simp only [cvInc, dif_neg hi]; exact Ceq_refl _

/-- The inclusion is additive (linear, part 1). -/
theorem cvInc_add {N M : Nat} (h : N ≤ M) (x y : CVec N) :
    CVecEq (cvInc h (cvAdd x y)) (cvAdd (cvInc h x) (cvInc h y)) := by
  intro i
  by_cases hi : i.val < N
  · simp only [cvInc, cvAdd, dif_pos hi]; exact Ceq_refl _
  · simp only [cvInc, cvAdd, dif_neg hi]; exact Ceq_symm (cadd_zero' Czero)

/-- The inclusion commutes with scalar multiplication (linear, part 2). -/
theorem cvInc_smul {N M : Nat} (h : N ≤ M) (c : Complex) (x : CVec N) :
    CVecEq (cvInc h (cvSmul c x)) (cvSmul c (cvInc h x)) := by
  intro i
  by_cases hi : i.val < N
  · simp only [cvInc, cvSmul, dif_pos hi]; exact Ceq_refl _
  · simp only [cvInc, cvSmul, dif_neg hi]; exact Ceq_symm (cmul_czero' c)

/-- The inclusion commutes with negation. -/
theorem cvInc_neg {N M : Nat} (h : N ≤ M) (x : CVec N) :
    CVecEq (cvInc h (cvNeg x)) (cvNeg (cvInc h x)) := by
  intro i
  by_cases hi : i.val < N
  · simp only [cvInc, cvNeg, dif_pos hi]; exact Ceq_refl _
  · simp only [cvInc, cvNeg, dif_neg hi]; exact Ceq_symm cneg_czero'

/-- **The inclusion preserves the inner product** — it is a genuine isometry:
    `⟨ι x, ι y⟩_M = ⟨x, y⟩_N`. The padded coordinates pair to `0` (`cvecSum_pad`). -/
theorem cvInc_inner {N M : Nat} (h : N ≤ M) (x y : CVec N) :
    Ceq (cInner M (cvInc h x) (cvInc h y)) (cInner N x y) := by
  refine Ceq_trans (cvecSum_congr M _ _ (fun i => ?_))
    (cvecSum_pad (fun j => Cmul (Cconj (x j)) (y j)) h)
  by_cases hi : i.val < N
  · simp only [cvInc, dif_pos hi]; exact Ceq_refl _
  · simp only [cvInc, dif_neg hi]; exact cmul_czero' (Cconj Czero)

/-- **Identity coherence**: the inclusion `N ↪ N` is the identity. -/
theorem cvInc_id {N : Nat} (x : CVec N) : CVecEq (cvInc (Nat.le_refl N) x) x := by
  intro i; simp only [cvInc, dif_pos i.isLt]; exact Ceq_refl _

/-- **Composition coherence**: `ι_{M≤K} ∘ ι_{N≤M} = ι_{N≤K}`. -/
theorem cvInc_comp {N M K : Nat} (h₁ : N ≤ M) (h₂ : M ≤ K) (x : CVec N) :
    CVecEq (cvInc h₂ (cvInc h₁ x)) (cvInc (Nat.le_trans h₁ h₂) x) := by
  intro i
  by_cases hN : i.val < N
  · have hM : i.val < M := Nat.lt_of_lt_of_le hN h₁
    simp only [cvInc, dif_pos hM, dif_pos hN]; exact Ceq_refl _
  · by_cases hM : i.val < M
    · simp only [cvInc, dif_pos hM, dif_neg hN]; exact Ceq_refl _
    · simp only [cvInc, dif_neg hM, dif_neg hN]; exact Ceq_refl _

end UOR.Bridge.F1Square.Square
