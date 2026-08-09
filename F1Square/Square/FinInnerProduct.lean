/-
F1 square — **the genuine finite-dimensional complex inner-product space** `Fin N → ℂ` (the first
brick of the Atlas-derived Hilbert–Pólya construction that REPLACES the quarantined nominal
contract).

Unlike the axiom-free `HilbertPolyaSpec` bundle — whose `Nominal*` predicates are vacuous
(`zeroBundle_NominalSelfAdjoint`) precisely because it has no vector-space or inner-product structure
— this file builds an ACTUAL inner product on the genuinely finite carrier `CVec N := Fin N → ℂ`,
with the pointwise vector operations and the sesquilinear form

    ⟨x, y⟩ := Σ_{i<N} conj(xᵢ) · yᵢ    (`cInner`).

The three defining properties an inner product must have are PROVED here, not assumed:

  • SESQUILINEAR — additive in each slot (`cInner_add_left`, `cInner_add_right`), conjugate-linear in
    the first (`cInner_smul_left`: pulls out `conj c`) and linear in the second (`cInner_smul_right`:
    pulls out `c`);
  • HERMITIAN — `⟨x, y⟩ = conj⟨y, x⟩` (`cInner_conj`);
  • POSITIVE-DEFINITE — the diagonal `⟨x, x⟩` is a nonnegative REAL (`cInner_self_im_zero`,
    `cInner_self_re_nonneg`) and vanishes ONLY at `x = 0` (`cInner_self_definite`), the genuine
    definiteness the nominal contract lacked. Definiteness reuses the Bishop square-definiteness
    `Rmul_self_eq_zero_imp` and `Radd_eq_zero_split` from `HilbertPolyaMetric` (the positive real
    metric substrate).

Coherent embeddings `CVec N ↪ CVec (N+1)` (extend by `0`) preserve the inner product
(`cInner_embed`), so the finite spaces form a directed system — the substrate the constructive
completion (next brick) will complete.

This is the POSITIVE metric half; it is deliberately independent of any operator/generator (the
signed Atlas action is a separate object, built later), keeping the Hilbert metric separate from the
scaling generator. Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free. Crux `none`.
-/

import F1Square.Analysis.RealSquareDefinite
import F1Square.Analysis.ComplexCore

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

/-- `−(−x) ≈ x` (local, zeta-free — the public copy lives in `RealPow` whose cone is Pi/ζ-tainted). -/
private theorem Rneg_neg (x : Real) : Req (Rneg (Rneg x)) x :=
  Req_of_seq_Qeq (fun n => by
    show Qeq (neg (neg (x.seq n))) (x.seq n)
    simp only [Qeq, neg]; push_cast; ring_uor)

/-- `0 ≤ x` (as `Rle`) gives `Rnonneg x` (local, zeta-free copy of the `RealPow` lemma). -/
private theorem Rnonneg_of_Rle_zero {x : Real} (h : Rle zero x) : Rnonneg x := by
  intro n
  refine Qarch_gen (C := 3) (neg_den_pos (Qbound_den_pos n)) (x.den_pos n) (fun m => ?_)
  have hs2 : Qle (⟨0, 1⟩ : Q) (add (x.seq m) ⟨2, m + 1⟩) := h m
  have hs1 : Qle (x.seq m) (add (x.seq n) (add (Qbound m) (Qbound n))) :=
    Qle_add_of_Qabs_sub (x.den_pos m) (x.den_pos n)
      (add_den_pos (Qbound_den_pos m) (Qbound_den_pos n)) (x.reg m n)
  have hcomb : Qle (⟨0, 1⟩ : Q)
      (add (add (x.seq n) (add (Qbound m) (Qbound n))) ⟨2, m + 1⟩) :=
    Qle_trans (add_den_pos (x.den_pos m) (Nat.succ_pos _)) hs2 (Qadd_le_add hs1 (Qle_refl _))
  have hfinal := Qadd_le_add hcomb (Qle_refl (neg (Qbound n)))
  have hLHSeq : Qeq (neg (Qbound n)) (add (⟨0, 1⟩ : Q) (neg (Qbound n))) := by
    simp only [Qeq, add, neg, Qbound]; push_cast; ring_uor
  have hRHSeq : Qeq (add (add (add (x.seq n) (add (Qbound m) (Qbound n))) ⟨2, m + 1⟩)
      (neg (Qbound n))) (add (x.seq n) ⟨3, m + 1⟩) := by
    simp only [Qeq, add, neg, Qbound]; push_cast; ring_uor
  refine Qle_trans (add_den_pos (by decide) (neg_den_pos (Qbound_den_pos n))) (Qeq_le hLHSeq) ?_
  refine Qle_trans (add_den_pos (add_den_pos (add_den_pos (x.den_pos n)
      (add_den_pos (Qbound_den_pos m) (Qbound_den_pos n))) (Nat.succ_pos _))
      (neg_den_pos (Qbound_den_pos n))) hfinal (Qeq_le hRHSeq)

/-- `Rnonneg` respects `≈` (local, zeta-free — via the order bridge). -/
private theorem Rnonneg_congr {x y : Real} (h : Req x y) (hx : Rnonneg x) : Rnonneg y :=
  Rnonneg_of_Rle_zero (Rle_trans (Rle_zero_of_Rnonneg hx) (Rle_of_Req h))

/-- The genuine finite complex carrier: `N`-tuples of complex numbers. -/
abbrev CVec (N : Nat) : Type := Fin N → Complex

/-- Pointwise vector addition. -/
def cvAdd {N : Nat} (x y : CVec N) : CVec N := fun i => Cadd (x i) (y i)

/-- Pointwise scalar multiplication by a complex scalar. -/
def cvSmul {N : Nat} (c : Complex) (x : CVec N) : CVec N := fun i => Cmul c (x i)

/-- The zero vector. -/
def cvZero (N : Nat) : CVec N := fun _ => Czero

/-- Pointwise negation. -/
def cvNeg {N : Nat} (x : CVec N) : CVec N := fun i => Cneg (x i)

-- ===========================================================================
-- Local trivialities (kept local so the import cone carries no ζ-adjacent
-- algebra file — only generic Complex/Cconj lemmas are reused).
-- ===========================================================================

/-- `z + 0 ≈ z`. -/
private theorem cadd0 (z : Complex) : Ceq (Cadd z Czero) z := ⟨Radd_zero z.re, Radd_zero z.im⟩

/-- Four-term interchange `(a + b) + (p + q) ≈ (a + p) + (b + q)`. -/
private theorem cadd_regroup4 (a b p q : Complex) :
    Ceq (Cadd (Cadd a b) (Cadd p q)) (Cadd (Cadd a p) (Cadd b q)) :=
  Ceq_trans (Cadd_assoc a b (Cadd p q))
    (Ceq_trans (Cadd_congr (Ceq_refl a)
        (Ceq_trans (Ceq_symm (Cadd_assoc b p q))
          (Cadd_congr (Cadd_comm b p) (Ceq_refl q))))
      (Ceq_trans (Cadd_congr (Ceq_refl a) (Cadd_assoc p b q))
        (Ceq_symm (Cadd_assoc a p (Cadd b q)))))

/-- Right-distributivity `(a + b)·c ≈ a·c + b·c`. -/
private theorem cmul_distrib_right (a b c : Complex) :
    Ceq (Cmul (Cadd a b) c) (Cadd (Cmul a c) (Cmul b c)) :=
  Ceq_trans (Cmul_comm (Cadd a b) c)
    (Ceq_trans (Cmul_distrib c a b) (Cadd_congr (Cmul_comm c a) (Cmul_comm c b)))

/-- Left-commutativity `a·(c·b) ≈ c·(a·b)`. -/
private theorem cmul_left_comm (a c b : Complex) :
    Ceq (Cmul a (Cmul c b)) (Cmul c (Cmul a b)) :=
  Ceq_trans (Ceq_symm (Cmul_assoc a c b))
    (Ceq_trans (Cmul_congr (Cmul_comm a c) (Ceq_refl b)) (Cmul_assoc c a b))

/-- `z · 0 ≈ 0`. -/
private theorem cmul_czero (z : Complex) : Ceq (Cmul z Czero) Czero :=
  ⟨Req_trans (Radd_congr (Rmul_zero z.re) (Rneg_congr (Rmul_zero z.im))) (Radd_neg zero),
   Req_trans (Radd_congr (Rmul_zero z.re) (Rmul_zero z.im)) (Radd_zero zero)⟩

-- ===========================================================================
-- The finite sum over `Fin N`, by structural recursion (core Lean only).
-- ===========================================================================

/-- `Σ_{i<N} g i`, summing the first `N` entries then the last. Uses only `Fin.val`/`Fin.isLt`. -/
def cvecSum : (N : Nat) → (CVec N) → Complex
  | 0, _ => Czero
  | (N + 1), g =>
      Cadd (cvecSum N (fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)) (g ⟨N, Nat.lt_succ_self N⟩)

/-- Termwise congruence of the finite sum. -/
theorem cvecSum_congr : ∀ (N : Nat) (f g : CVec N), (∀ i, Ceq (f i) (g i)) →
    Ceq (cvecSum N f) (cvecSum N g)
  | 0, _, _, _ => Ceq_refl _
  | (N + 1), f, g, h =>
      Cadd_congr
        (cvecSum_congr N (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
                         (fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
                         (fun i => h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
        (h ⟨N, Nat.lt_succ_self N⟩)

/-- Additivity of the finite sum: `Σ (fᵢ + gᵢ) ≈ Σ fᵢ + Σ gᵢ`. -/
theorem cvecSum_add : ∀ (N : Nat) (f g : CVec N),
    Ceq (cvecSum N (fun i => Cadd (f i) (g i))) (Cadd (cvecSum N f) (cvecSum N g))
  | 0, _, _ => Ceq_symm (cadd0 Czero)
  | (N + 1), f, g => by
      show Ceq
        (Cadd (cvecSum N (fun i => Cadd (f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
                                        (g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)))
              (Cadd (f ⟨N, Nat.lt_succ_self N⟩) (g ⟨N, Nat.lt_succ_self N⟩)))
        (Cadd (Cadd (cvecSum N (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
                    (f ⟨N, Nat.lt_succ_self N⟩))
              (Cadd (cvecSum N (fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
                    (g ⟨N, Nat.lt_succ_self N⟩)))
      refine Ceq_trans (Cadd_congr (cvecSum_add N _ _) (Ceq_refl _)) ?_
      -- ((A + B) + (a + b))  ≈  ((A + a) + (B + b))
      exact cadd_regroup4 _ _ _ _

/-- Scalar pulls out of the finite sum: `c · Σ gᵢ ≈ Σ (c · gᵢ)`. -/
theorem cvecSum_smul : ∀ (N : Nat) (c : Complex) (g : CVec N),
    Ceq (Cmul c (cvecSum N g)) (cvecSum N (fun i => Cmul c (g i)))
  | 0, c, _ => cmul_czero c
  | (N + 1), c, g => by
      refine Ceq_trans (Cmul_distrib c _ _) ?_
      exact Cadd_congr (cvecSum_smul N c _) (Ceq_refl _)

/-- Conjugation pulls into the finite sum: `conj (Σ gᵢ) ≈ Σ conj gᵢ`. -/
theorem cvecSum_conj : ∀ (N : Nat) (g : CVec N),
    Ceq (Cconj (cvecSum N g)) (cvecSum N (fun i => Cconj (g i)))
  | 0, _ => Cconj_Czero
  | (N + 1), g => by
      refine Ceq_trans (Cconj_Cadd _ _) ?_
      exact Cadd_congr (cvecSum_conj N _) (Ceq_refl _)

/-- If every entry is real (`im ≈ 0`), the finite sum is real. -/
theorem cvecSum_im_zero : ∀ (N : Nat) (g : CVec N), (∀ i, Req (g i).im zero) →
    Req (cvecSum N g).im zero
  | 0, _, _ => Req_refl _
  | (N + 1), g, h => by
      show Req (Radd (cvecSum N (fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)).im
                     (g ⟨N, Nat.lt_succ_self N⟩).im) zero
      refine Req_trans (Radd_congr
        (cvecSum_im_zero N _ (fun i => h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
        (h ⟨N, Nat.lt_succ_self N⟩)) ?_
      exact Radd_zero zero

/-- If every entry has nonnegative real part, so does the finite sum. -/
theorem cvecSum_re_nonneg : ∀ (N : Nat) (g : CVec N), (∀ i, Rnonneg (g i).re) →
    Rnonneg (cvecSum N g).re
  | 0, _, _ => Rnonneg_zero
  | (N + 1), g, h =>
      Rnonneg_Radd
        (cvecSum_re_nonneg N (fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
          (fun i => h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
        (h ⟨N, Nat.lt_succ_self N⟩)

-- ===========================================================================
-- The inner product and its sesquilinear / Hermitian laws.
-- ===========================================================================

/-- **The genuine inner product** `⟨x, y⟩ = Σ_{i<N} conj(xᵢ)·yᵢ` — conjugate-linear in the first
    argument, linear in the second. -/
def cInner (N : Nat) (x y : CVec N) : Complex :=
  cvecSum N (fun i => Cmul (Cconj (x i)) (y i))

/-- **Additive in the second slot**: `⟨x, y + z⟩ = ⟨x, y⟩ + ⟨x, z⟩`. -/
theorem cInner_add_right (N : Nat) (x y z : CVec N) :
    Ceq (cInner N x (cvAdd y z)) (Cadd (cInner N x y) (cInner N x z)) :=
  Ceq_trans
    (cvecSum_congr N _ _ (fun i => Cmul_distrib (Cconj (x i)) (y i) (z i)))
    (cvecSum_add N _ _)

/-- **Additive in the first slot**: `⟨x + y, z⟩ = ⟨x, z⟩ + ⟨y, z⟩` (uses `conj (x+y) = conj x +
    conj y` and right-distributivity). -/
theorem cInner_add_left (N : Nat) (x y z : CVec N) :
    Ceq (cInner N (cvAdd x y) z) (Cadd (cInner N x z) (cInner N y z)) :=
  Ceq_trans
    (cvecSum_congr N _ _ (fun i =>
      Ceq_trans (Cmul_congr (Cconj_Cadd (x i) (y i)) (Ceq_refl (z i)))
        (cmul_distrib_right (Cconj (x i)) (Cconj (y i)) (z i))))
    (cvecSum_add N _ _)

/-- **Linear in the second slot**: `⟨x, c·y⟩ = c·⟨x, y⟩`. -/
theorem cInner_smul_right (N : Nat) (c : Complex) (x y : CVec N) :
    Ceq (cInner N x (cvSmul c y)) (Cmul c (cInner N x y)) :=
  Ceq_trans
    (cvecSum_congr N _ _ (fun i => cmul_left_comm (Cconj (x i)) c (y i)))
    (Ceq_symm (cvecSum_smul N c _))

/-- **Conjugate-linear in the first slot**: `⟨c·x, y⟩ = conj(c)·⟨x, y⟩`. -/
theorem cInner_smul_left (N : Nat) (c : Complex) (x y : CVec N) :
    Ceq (cInner N (cvSmul c x) y) (Cmul (Cconj c) (cInner N x y)) :=
  Ceq_trans
    (cvecSum_congr N _ _ (fun i =>
      Ceq_trans (Cmul_congr (Cconj_Cmul c (x i)) (Ceq_refl (y i)))
        (Cmul_assoc (Cconj c) (Cconj (x i)) (y i))))
    (Ceq_symm (cvecSum_smul N (Cconj c) _))

/-- **Hermitian symmetry**: `⟨x, y⟩ = conj⟨y, x⟩`. -/
theorem cInner_conj (N : Nat) (x y : CVec N) :
    Ceq (cInner N x y) (Cconj (cInner N y x)) :=
  Ceq_symm
    (Ceq_trans (cvecSum_conj N _)
      (cvecSum_congr N _ _ (fun i =>
        Ceq_trans (Cconj_Cmul (Cconj (y i)) (x i))
          (Ceq_trans (Cmul_congr (Cconj_Cconj (y i)) (Ceq_refl (Cconj (x i))))
            (Cmul_comm (y i) (Cconj (x i)))))))

-- ===========================================================================
-- Positive-definiteness of the diagonal `⟨x, x⟩`.
-- ===========================================================================

/-- The diagonal summand `conj(z)·z` is real: its imaginary part is `0`. -/
private theorem selfTerm_im_zero (z : Complex) : Req (Cmul (Cconj z) z).im zero := by
  show Req (Radd (Rmul z.re z.im) (Rmul (Rneg z.im) z.re)) zero
  refine Req_trans (Radd_congr (Req_refl _)
    (Req_trans (Rmul_neg_left z.im z.re) (Rneg_congr (Rmul_comm z.im z.re)))) ?_
  exact Radd_neg (Rmul z.re z.im)

/-- The diagonal summand `conj(z)·z` has real part `z.re² + z.im²`. -/
private theorem selfTerm_re_eq (z : Complex) :
    Req (Cmul (Cconj z) z).re (Radd (Rmul z.re z.re) (Rmul z.im z.im)) := by
  show Req (Rsub (Rmul z.re z.re) (Rmul (Rneg z.im) z.im))
           (Radd (Rmul z.re z.re) (Rmul z.im z.im))
  refine Radd_congr (Req_refl _) ?_
  exact Req_trans (Rneg_congr (Rmul_neg_left z.im z.im)) (Rneg_neg (Rmul z.im z.im))

/-- The diagonal summand has nonnegative real part. -/
private theorem selfTerm_re_nonneg (z : Complex) : Rnonneg (Cmul (Cconj z) z).re :=
  Rnonneg_congr (Req_symm (selfTerm_re_eq z))
    (Rnonneg_Radd (Rnonneg_Rmul_self_loc z.re) (Rnonneg_Rmul_self_loc z.im))

/-- **The diagonal `⟨x, x⟩` is real**. -/
theorem cInner_self_im_zero (N : Nat) (x : CVec N) : Req (cInner N x x).im zero :=
  cvecSum_im_zero N _ (fun i => selfTerm_im_zero (x i))

/-- **The diagonal `⟨x, x⟩` has nonnegative real part** (positive-semidefiniteness). -/
theorem cInner_self_re_nonneg (N : Nat) (x : CVec N) : Rnonneg (cInner N x x).re :=
  cvecSum_re_nonneg N _ (fun i => selfTerm_re_nonneg (x i))

/-- **POSITIVE-DEFINITENESS** — the genuine definiteness the nominal contract lacked: if the diagonal
    `⟨x, x⟩` vanishes, then every coordinate vanishes, `xᵢ = 0`. Peels the last summand with
    `Radd_eq_zero_split`, feeds the head back through the induction, and at the leaf uses the Bishop
    square-definiteness `Rmul_self_eq_zero_imp` on `xᵢ.re² + xᵢ.im² ≈ 0`. -/
theorem cInner_self_definite : ∀ (N : Nat) (x : CVec N),
    Ceq (cInner N x x) Czero → ∀ i : Fin N, Ceq (x i) Czero
  | 0, _, _, i => absurd i.isLt (Nat.not_lt_zero i.val)
  | (N + 1), x, h, i => by
      -- The head restriction and the last entry.
      -- `(⟨x,x⟩).re ≈ 0` splits into head-re ≈ 0 and last-term-re ≈ 0 (both nonnegative).
      have hre : Req (Radd (cInner N (fun j => x ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)
                                    (fun j => x ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)).re
                           (Cmul (Cconj (x ⟨N, Nat.lt_succ_self N⟩)) (x ⟨N, Nat.lt_succ_self N⟩)).re)
                     zero := h.1
      have hsplit := Radd_eq_zero_split
        (cInner_self_re_nonneg N _)
        (selfTerm_re_nonneg (x ⟨N, Nat.lt_succ_self N⟩)) hre
      -- Head vanishes: re ≈ 0 (hsplit.1) and im ≈ 0 (diagonal real) give `⟨head, head⟩ ≈ 0`.
      have hhead : Ceq (cInner N (fun j => x ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)
                                 (fun j => x ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)) Czero :=
        ⟨hsplit.1, cInner_self_im_zero N _⟩
      have ihead := cInner_self_definite N _ hhead
      -- Last entry vanishes: `xₙ.re² + xₙ.im² ≈ 0`, split, square-definiteness.
      have hlast_re : Req (Radd (Rmul (x ⟨N, Nat.lt_succ_self N⟩).re (x ⟨N, Nat.lt_succ_self N⟩).re)
                                (Rmul (x ⟨N, Nat.lt_succ_self N⟩).im (x ⟨N, Nat.lt_succ_self N⟩).im))
                          zero :=
        Req_trans (Req_symm (selfTerm_re_eq (x ⟨N, Nat.lt_succ_self N⟩))) hsplit.2
      have hlsplit := Radd_eq_zero_split
        (Rnonneg_Rmul_self_loc (x ⟨N, Nat.lt_succ_self N⟩).re)
        (Rnonneg_Rmul_self_loc (x ⟨N, Nat.lt_succ_self N⟩).im) hlast_re
      have hlast : Ceq (x ⟨N, Nat.lt_succ_self N⟩) Czero :=
        ⟨Rmul_self_eq_zero_imp hlsplit.1, Rmul_self_eq_zero_imp hlsplit.2⟩
      -- Assemble: split on whether `i.val < N`.
      rcases Nat.lt_or_ge i.val N with hlt | hge
      · exact ihead ⟨i.val, hlt⟩
      · have hval : i.val = N := Nat.le_antisymm (Nat.lt_succ_iff.mp i.isLt) hge
        have : i = ⟨N, Nat.lt_succ_self N⟩ := Fin.ext hval
        rw [this]; exact hlast

-- ===========================================================================
-- Coherent embeddings `CVec N ↪ CVec (N+1)` and inner-product preservation.
-- ===========================================================================

/-- The coherent embedding `CVec N ↪ CVec (N+1)`, extending by `0` at the new last coordinate. -/
def cvEmbed {N : Nat} (x : CVec N) : CVec (N + 1) :=
  fun i => if h : i.val < N then x ⟨i.val, h⟩ else Czero

/-- **The embedding preserves the inner product**: `⟨ι x, ι y⟩_{N+1} = ⟨x, y⟩_N`, so the finite
    spaces form a directed system of inner-product spaces (the substrate for the completion). -/
theorem cInner_embed (N : Nat) (x y : CVec N) :
    Ceq (cInner (N + 1) (cvEmbed x) (cvEmbed y)) (cInner N x y) := by
  show Ceq
    (Cadd (cvecSum N (fun i => Cmul (Cconj (cvEmbed x ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
                                    (cvEmbed y ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)))
          (Cmul (Cconj (cvEmbed x ⟨N, Nat.lt_succ_self N⟩)) (cvEmbed y ⟨N, Nat.lt_succ_self N⟩)))
    (cInner N x y)
  -- The last term is `conj 0 · 0 ≈ 0`; the head restriction is exactly `⟨x, y⟩_N`.
  have hlast : Ceq (Cmul (Cconj (cvEmbed x ⟨N, Nat.lt_succ_self N⟩))
                         (cvEmbed y ⟨N, Nat.lt_succ_self N⟩)) Czero := by
    have hx : cvEmbed x ⟨N, Nat.lt_succ_self N⟩ = Czero := dif_neg (Nat.lt_irrefl N)
    have hy : cvEmbed y ⟨N, Nat.lt_succ_self N⟩ = Czero := dif_neg (Nat.lt_irrefl N)
    rw [hx, hy]; exact cmul_czero (Cconj Czero)
  have hhead : Ceq (cvecSum N (fun i => Cmul (Cconj (cvEmbed x ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
                                             (cvEmbed y ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)))
                   (cInner N x y) :=
    cvecSum_congr N _ _ (fun i => by
      have hx : cvEmbed x ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ = x ⟨i.val, i.isLt⟩ := dif_pos i.isLt
      have hy : cvEmbed y ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ = y ⟨i.val, i.isLt⟩ := dif_pos i.isLt
      rw [hx, hy]; exact Ceq_refl _)
  exact Ceq_trans (Cadd_congr hhead hlast) (cadd0 (cInner N x y))

-- ===========================================================================
-- The setoid `CVecEq` and the complex-module + inner-product congruence laws
-- (the extensionality/vector-space structure the raw finite form lacked).
-- ===========================================================================

/-- **Pointwise vector equivalence** on `CVec N` — the setoid the finite space carries: `x ≈ y` iff
    every coordinate agrees under Bishop `Ceq`. -/
def CVecEq {N : Nat} (x y : CVec N) : Prop := ∀ i, Ceq (x i) (y i)

/-- Reflexivity of `CVecEq`. -/
theorem CVecEq_refl {N : Nat} (x : CVec N) : CVecEq x x := fun _ => Ceq_refl _

/-- Symmetry of `CVecEq`. -/
theorem CVecEq_symm {N : Nat} {x y : CVec N} (h : CVecEq x y) : CVecEq y x := fun i => Ceq_symm (h i)

/-- Transitivity of `CVecEq` (so `(CVec N, CVecEq)` is a setoid). -/
theorem CVecEq_trans {N : Nat} {x y z : CVec N} (h₁ : CVecEq x y) (h₂ : CVecEq y z) : CVecEq x z :=
  fun i => Ceq_trans (h₁ i) (h₂ i)

/-- Vector addition respects the setoid. -/
theorem cvAdd_congr {N : Nat} {x x' y y' : CVec N} (hx : CVecEq x x') (hy : CVecEq y y') :
    CVecEq (cvAdd x y) (cvAdd x' y') := fun i => Cadd_congr (hx i) (hy i)

/-- Scalar multiplication respects the setoid (in both scalar and vector). -/
theorem cvSmul_congr {N : Nat} {c c' : Complex} {x x' : CVec N} (hc : Ceq c c') (hx : CVecEq x x') :
    CVecEq (cvSmul c x) (cvSmul c' x') := fun i => Cmul_congr hc (hx i)

/-- Negation respects the setoid. -/
theorem cvNeg_congr {N : Nat} {x x' : CVec N} (hx : CVecEq x x') :
    CVecEq (cvNeg x) (cvNeg x') := fun i => ⟨Rneg_congr (hx i).1, Rneg_congr (hx i).2⟩

/-- Commutativity of vector addition. -/
theorem cvAdd_comm {N : Nat} (x y : CVec N) : CVecEq (cvAdd x y) (cvAdd y x) :=
  fun i => Cadd_comm (x i) (y i)

/-- Associativity of vector addition. -/
theorem cvAdd_assoc {N : Nat} (x y z : CVec N) :
    CVecEq (cvAdd (cvAdd x y) z) (cvAdd x (cvAdd y z)) := fun i => Cadd_assoc (x i) (y i) (z i)

/-- `0` is a right identity for vector addition. -/
theorem cvAdd_zero {N : Nat} (x : CVec N) : CVecEq (cvAdd x (cvZero N)) x := fun i => cadd0 (x i)

/-- `−x` is an additive inverse. -/
theorem cvAdd_neg {N : Nat} (x : CVec N) : CVecEq (cvAdd x (cvNeg x)) (cvZero N) :=
  fun i => ⟨Radd_neg (x i).re, Radd_neg (x i).im⟩

/-- Scalar multiplication distributes over vector addition. -/
theorem cvSmul_cvAdd {N : Nat} (c : Complex) (x y : CVec N) :
    CVecEq (cvSmul c (cvAdd x y)) (cvAdd (cvSmul c x) (cvSmul c y)) :=
  fun i => Cmul_distrib c (x i) (y i)

/-- Scalar multiplication distributes over scalar addition. -/
theorem cvSmul_Cadd {N : Nat} (c d : Complex) (x : CVec N) :
    CVecEq (cvSmul (Cadd c d) x) (cvAdd (cvSmul c x) (cvSmul d x)) :=
  fun i => cmul_distrib_right c d (x i)

/-- Scalar-multiplication associativity `c·(d·x) = (c·d)·x`. -/
theorem cvSmul_assoc {N : Nat} (c d : Complex) (x : CVec N) :
    CVecEq (cvSmul c (cvSmul d x)) (cvSmul (Cmul c d) x) :=
  fun i => Ceq_symm (Cmul_assoc c d (x i))

/-- `1·x = x`. -/
theorem cvSmul_one {N : Nat} (x : CVec N) : CVecEq (cvSmul Cone x) x :=
  fun i => Ceq_trans (Cmul_comm Cone (x i)) (Cmul_one (x i))

/-- **The inner product respects the setoid in both arguments** — so `cInner` descends to the
    quotient (the extensionality under pointwise `Ceq` the raw finite form lacked). -/
theorem cInner_congr {N : Nat} {x x' y y' : CVec N} (hx : CVecEq x x') (hy : CVecEq y y') :
    Ceq (cInner N x y) (cInner N x' y') :=
  cvecSum_congr N _ _ (fun i => Cmul_congr (Cconj_congr (hx i)) (hy i))

end UOR.Bridge.F1Square.Square
