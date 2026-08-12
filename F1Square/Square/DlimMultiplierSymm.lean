/-
# PARSEVAL for the Bishop completion + genuine SYMMETRY of the real-weight diagonal multiplier

Two ζ-free, sqrt-free, division-free upgrades living entirely in the completion cone, closing
reviewer multiplier-gate **item 5** (the multiplier is a genuine symmetric inner-product operator on
its maximal domain).

* `completedInner_finrank_sy` — the FINITE-RANK inner read: `⟨finProj N A, B⟩ ≈ Σ_{i<N} conj(A_i)·B_i`.
* `completedInner_finProj_tendsto_sy` — first-slot LIMIT continuity of the coordinate projections.
* `completedInner_parseval_sy` — **PARSEVAL**: the completion inner product is the limit of the finite
  coordinate sums, `Σ_{i<N} conj(A_i)·B_i → ⟨A, B⟩`.
* `mult_symm_sy` — **THE SYMMETRY (item 5)**: for the real-weight diagonal multiplier graph,
  `⟨M_w X, Y⟩ ≈ ⟨X, M_w Y⟩`.  Proved through PARSEVAL twice: each finite coordinate sum satisfies the
  termwise real-weight identity `conj(w_i·X_i)·Y_i = conj(X_i)·(w_i·Y_i)` (the weight is real, hence
  central and self-conjugate), so the two sequences of finite sums are termwise `≈`; sharing a sequence
  they share a limit, giving `⟨Xp, Y⟩ ≈ ⟨X, Yp⟩` by limit uniqueness.

No `completedInner`/`completedNormSq`/`completedDist2`/`coord`/`finProj` is ever unfolded by defeq
beyond the single `finProj` delta-step used to drive the induction — only the completion black-box
laws are used.  Choice-free; axioms `[propext, Quot.sound]`.
-/
import F1Square.Square.DlimMultiplierClosed
import F1Square.Square.DlimCompletionLimit

open UOR.Bridge.F1Square Square
open UOR.Bridge.F1Square.Analysis

namespace UOR.Bridge.F1Square.Square

-- ===========================================================================
-- Local ℝ / Q micro-helpers (leaf names end `_sy`), rebuilt from in-cone primitives.
-- ===========================================================================

/-- `0 ⊕ x ≈ x`. -/
private theorem Rzero_add_sy (x : Real) : Req (Radd zero x) x :=
  Req_trans (Radd_comm zero x) (Radd_zero x)

/-- `−0 ≈ 0`. -/
private theorem Rneg_zero_sy : Req (Rneg zero) zero :=
  Req_of_seq_Qeq (fun n => by
    show Qeq (neg (zero.seq n)) (zero.seq n)
    rw [zero_seq]; decide)

/-- `−(−x) ≈ x` (in-cone; `Rneg` is pointwise). -/
private theorem Rneg_neg_sy (x : Real) : Req (Rneg (Rneg x)) x :=
  Req_of_seq_Qeq (fun n => by
    show Qeq (neg (neg (x.seq n))) (x.seq n); simp only [Qeq, neg]; ring_uor)

/-- **Inverse uniqueness**: `a ⊕ b ≈ 0 ⟹ −a ≈ b`. -/
private theorem Rneg_unique_sy (a b : Real) (h : Req (Radd a b) zero) : Req (Rneg a) b :=
  Req_trans (Req_symm (Radd_zero (Rneg a)))
    (Req_trans (Radd_congr (Req_refl (Rneg a)) (Req_symm h))
      (Req_trans (Req_symm (Radd_assoc (Rneg a) a b))
        (Req_trans (Radd_congr (Req_trans (Radd_comm (Rneg a) a) (Radd_neg a)) (Req_refl b))
          (Rzero_add_sy b))))

/-- `−(x ⊕ y) ≈ (−x) ⊕ (−y)` (in-cone, via inverse uniqueness — `Radd` is not pointwise). -/
private theorem Rneg_Radd_sy (x y : Real) : Req (Rneg (Radd x y)) (Radd (Rneg x) (Rneg y)) :=
  Rneg_unique_sy (Radd x y) (Radd (Rneg x) (Rneg y))
    (Req_trans (Radd_swap x y (Rneg x) (Rneg y))
      (Req_trans (Radd_congr (Radd_neg x) (Radd_neg y)) (Radd_zero zero)))

/-- `x − y ≈ 0 ⟹ x ≈ y`. -/
private theorem Req_of_Rsub_zero_sy {a b : Real} (h : Req (Rsub a b) zero) : Req a b := by
  have hid : Req (Radd (Rsub a b) b) a :=
    Req_trans (Radd_assoc a (Rneg b) b)
      (Req_trans (Radd_congr (Req_refl a)
          (Req_trans (Radd_comm (Rneg b) b) (Radd_neg b)))
        (Radd_zero a))
  exact Req_trans (Req_symm hid) (Req_trans (Radd_congr h (Req_refl b)) (Rzero_add_sy b))

/-- `0 ≤ b ⟹ a ≤ a ⊕ b`. -/
private theorem Rle_add_nonneg_right_sy (a b : Real) (hb : Rnonneg b) : Rle a (Radd a b) :=
  Rle_of_Rnonneg_Rsub_loc
    (Rnonneg_congr_loc
      (Req_symm
        (Req_trans (Radd_congr (Radd_comm a b) (Req_refl (Rneg a)))
          (Req_trans (Radd_assoc b a (Rneg a))
            (Req_trans (Radd_congr (Req_refl b) (Radd_neg a)) (Radd_zero b)))))
      hb)

/-- `(−x)·(−x) ≈ x·x`. -/
private theorem Rneg_mul_neg_self_sy (x : Real) : Req (Rmul (Rneg x) (Rneg x)) (Rmul x x) :=
  Req_trans (Rmul_neg_left x (Rneg x))
    (Req_trans (Rneg_congr (Rmul_neg_right x x)) (Rneg_neg_sy (Rmul x x)))

/-- `(a−b)² ≈ (b−a)²`. -/
private theorem Rsub_swap_sq_sy (a b : Real) :
    Req (Rmul (Rsub a b) (Rsub a b)) (Rmul (Rsub b a) (Rsub b a)) := by
  have hsub : Req (Rsub a b) (Rneg (Rsub b a)) :=
    Req_symm
      (Req_trans (Rneg_Radd_sy b (Rneg a))
        (Req_trans (Radd_congr (Req_refl (Rneg b)) (Rneg_neg_sy a)) (Radd_comm (Rneg b) a)))
  exact Req_trans (Rmul_congr hsub hsub) (Rneg_mul_neg_self_sy (Rsub b a))

/-- `(−p − (−q))² ≈ (p−q)²` (the conjugate imaginary-part squared difference). -/
private theorem conj_im_sq_eq_sy (p q : Real) :
    Req (Rmul (Rsub (Rneg p) (Rneg q)) (Rsub (Rneg p) (Rneg q)))
        (Rmul (Rsub p q) (Rsub p q)) := by
  have hsub : Req (Rsub (Rneg p) (Rneg q)) (Rneg (Rsub p q)) := Req_symm (Rneg_Radd_sy p (Rneg q))
  exact Req_trans (Rmul_congr hsub hsub) (Rneg_mul_neg_self_sy (Rsub p q))

/-- Telescoping: `(a⊖c) ⊕ (c⊖b) ≈ a⊖b`. -/
private theorem Rsub_telescope_sy (a c b : Real) :
    Req (Radd (Rsub a c) (Rsub c b)) (Rsub a b) :=
  Req_trans (Radd_assoc a (Rneg c) (Radd c (Rneg b)))
    (Req_trans (Radd_congr (Req_refl a) (Req_symm (Radd_assoc (Rneg c) c (Rneg b))))
      (Req_trans (Radd_congr (Req_refl a)
          (Radd_congr (Req_trans (Radd_comm (Rneg c) c) (Radd_neg c)) (Req_refl (Rneg b))))
        (Radd_congr (Req_refl a) (Rzero_add_sy (Rneg b)))))

/-- **The sqrt-free two-square bound**: `(u+v)² ≤ 2u² + 2v²`. -/
private theorem two_sq_bound_sy (u v : Real) :
    Rle (Rmul (Radd u v) (Radd u v))
        (Radd (Radd (Rmul u u) (Rmul u u)) (Radd (Rmul v v) (Rmul v v))) := by
  have hE1 : Req (Rmul (Radd u v) (Radd u v))
      (Radd (Radd (Rmul u u) (Rmul u v)) (Radd (Rmul v u) (Rmul v v))) :=
    Req_trans (Rmul_distrib_right u v (Radd u v))
      (Radd_congr (Rmul_distrib u u v) (Rmul_distrib v u v))
  have hE2 : Req (Rmul (Rsub u v) (Rsub u v))
      (Radd (Radd (Rmul u u) (Rneg (Rmul u v))) (Radd (Rneg (Rmul v u)) (Rmul v v))) :=
    Req_trans (Rmul_distrib_right u (Rneg v) (Rsub u v))
      (Radd_congr
        (Req_trans (Rmul_distrib u u (Rneg v))
          (Radd_congr (Req_refl (Rmul u u)) (Rmul_neg_right u v)))
        (Req_trans (Rmul_distrib (Rneg v) u (Rneg v))
          (Radd_congr (Rmul_neg_left v u)
            (Req_trans (Rmul_neg_left v (Rneg v))
              (Req_trans (Rneg_congr (Rmul_neg_right v v)) (Rneg_neg_sy (Rmul v v)))))))
  have hAdd : Req
      (Radd (Radd (Radd (Rmul u u) (Rmul u v)) (Radd (Rmul v u) (Rmul v v)))
            (Radd (Radd (Rmul u u) (Rneg (Rmul u v))) (Radd (Rneg (Rmul v u)) (Rmul v v))))
      (Radd (Radd (Rmul u u) (Rmul u u)) (Radd (Rmul v v) (Rmul v v))) :=
    Req_trans
      (Radd_swap (Radd (Rmul u u) (Rmul u v)) (Radd (Rmul v u) (Rmul v v))
        (Radd (Rmul u u) (Rneg (Rmul u v))) (Radd (Rneg (Rmul v u)) (Rmul v v)))
      (Req_trans
        (Radd_congr
          (Radd_swap (Rmul u u) (Rmul u v) (Rmul u u) (Rneg (Rmul u v)))
          (Radd_swap (Rmul v u) (Rmul v v) (Rneg (Rmul v u)) (Rmul v v)))
        (Req_trans
          (Radd_congr
            (Radd_congr (Req_refl (Radd (Rmul u u) (Rmul u u))) (Radd_neg (Rmul u v)))
            (Radd_congr (Radd_neg (Rmul v u)) (Req_refl (Radd (Rmul v v) (Rmul v v)))))
          (Radd_congr (Radd_zero (Radd (Rmul u u) (Rmul u u)))
            (Rzero_add_sy (Radd (Rmul v v) (Rmul v v))))))
  have hSum : Req (Radd (Rmul (Radd u v) (Radd u v)) (Rmul (Rsub u v) (Rsub u v)))
      (Radd (Radd (Rmul u u) (Rmul u u)) (Radd (Rmul v v) (Rmul v v))) :=
    Req_trans (Radd_congr hE1 hE2) hAdd
  exact Rle_trans
    (Rle_add_nonneg_right_sy (Rmul (Radd u v) (Radd u v)) (Rmul (Rsub u v) (Rsub u v))
      (Rnonneg_Rmul_self_loc (Rsub u v)))
    (Rle_of_Req hSum)

/-- **Archimedean squeeze**: a nonnegative real `≤ 1/(k+1)` for every `k` is `≈ 0`. -/
private theorem Req_zero_of_nonneg_of_small_sy {x : Real} (hnn : Rnonneg x)
    (hall : ∀ k : Nat, Rle x (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k))) : Req x zero := by
  refine Rle_antisymm ?_ (Rle_zero_of_Rnonneg hnn)
  intro n
  refine Qarch_gen (C := 1) (x.den_pos n) (add_den_pos (zero.den_pos n) (Nat.succ_pos n)) (fun k => ?_)
  have hb : Qle (x.seq n) (add (⟨1, k + 1⟩ : Q) (⟨2, n + 1⟩ : Q)) := hall k n
  refine Qle_congr_right (add_den_pos (Nat.succ_pos k) (Nat.succ_pos n)) ?_ hb
  simp only [Qeq, add, zero_seq]; push_cast; ring_uor

/-- Two `ofQ`s of `Qeq` rationals are `≈`. -/
private theorem ofQ_Req_of_Qeq_sy {a b : Q} (ha : 0 < a.den) (hb : 0 < b.den) (h : Qeq a b) :
    Req (ofQ a ha) (ofQ b hb) := Req_of_seq_Qeq (fun _ => h)

/-- **Rational collapse** `4·(1/(4k+4)) ≤ 1/(k+1)`, in the `(t⊕t)⊕(t⊕t)` shape with `t = 1/(4k+3+1)`. -/
private theorem fin_collapse4_sy (k : Nat) :
    Rle (Radd (Radd (ofQ (⟨1, 4 * k + 3 + 1⟩ : Q) (Nat.succ_pos _))
                    (ofQ (⟨1, 4 * k + 3 + 1⟩ : Q) (Nat.succ_pos _)))
              (Radd (ofQ (⟨1, 4 * k + 3 + 1⟩ : Q) (Nat.succ_pos _))
                    (ofQ (⟨1, 4 * k + 3 + 1⟩ : Q) (Nat.succ_pos _))))
        (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k)) := by
  have hcollapse : Req
      (Radd (Radd (ofQ (⟨1, 4 * k + 3 + 1⟩ : Q) (Nat.succ_pos _))
                  (ofQ (⟨1, 4 * k + 3 + 1⟩ : Q) (Nat.succ_pos _)))
            (Radd (ofQ (⟨1, 4 * k + 3 + 1⟩ : Q) (Nat.succ_pos _))
                  (ofQ (⟨1, 4 * k + 3 + 1⟩ : Q) (Nat.succ_pos _))))
      (ofQ (⟨4, 4 * k + 3 + 1⟩ : Q) (Nat.succ_pos _)) := by
    refine Req_trans (Radd_congr (Radd_ofQ_loc (Nat.succ_pos _) (Nat.succ_pos _))
        (Radd_ofQ_loc (Nat.succ_pos _) (Nat.succ_pos _))) ?_
    refine Req_trans (Radd_ofQ_loc (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _))
        (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _))) ?_
    refine ofQ_Req_of_Qeq_sy _ _ ?_
    simp only [Qeq, add]; push_cast; ring_uor
  refine Rle_trans (Rle_of_Req hcollapse) ?_
  refine Rle_ofQ_of_Qle_loc (Nat.succ_pos _) (Nat.succ_pos k) ?_
  show (4 : Int) * (((k + 1 : Nat)) : Int) ≤ (1 : Int) * (((4 * k + 3 + 1 : Nat)) : Int)
  push_cast; omega

/-- **Real limit uniqueness (squared tolerance)**: if `(s n − a)² → 0` and `(s n − b)² → 0`, then
    `a ≈ b`.  Route: `(a−b)² ≤ 2(s n − a)² + 2(s n − b)²` for the max-index `n`, Archimedean-squeezed
    to `0`, then Bishop square-definiteness. -/
private theorem Rlim_sub_sq_unique_sy (s : Nat → Real) (a b : Real)
    (h1 : ∀ k, ∃ N, ∀ n, N ≤ n →
      Rle (Rmul (Rsub (s n) a) (Rsub (s n) a)) (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k)))
    (h2 : ∀ k, ∃ N, ∀ n, N ≤ n →
      Rle (Rmul (Rsub (s n) b) (Rsub (s n) b)) (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k))) :
    Req a b := by
  refine Req_of_Rsub_zero_sy (Rmul_self_eq_zero_imp
    (Req_zero_of_nonneg_of_small_sy (Rnonneg_Rmul_self_loc (Rsub a b)) (fun k => ?_)))
  obtain ⟨N, hN⟩ := h1 (4 * k + 3)
  obtain ⟨N', hN'⟩ := h2 (4 * k + 3)
  have hb1 := hN (max N N') (Nat.le_max_left N N')
  have hb2 := hN' (max N N') (Nat.le_max_right N N')
  have hid : Req (Rsub a b)
      (Radd (Rsub a (s (max N N'))) (Rsub (s (max N N')) b)) :=
    Req_symm (Rsub_telescope_sy a (s (max N N')) b)
  have hA : Rle (Rmul (Rsub a (s (max N N'))) (Rsub a (s (max N N'))))
      (ofQ (⟨1, 4 * k + 3 + 1⟩ : Q) (Nat.succ_pos _)) :=
    Rle_trans (Rle_of_Req (Rsub_swap_sq_sy a (s (max N N')))) hb1
  refine Rle_trans (Rle_of_Req (Rmul_congr hid hid)) ?_
  refine Rle_trans (two_sq_bound_sy (Rsub a (s (max N N'))) (Rsub (s (max N N')) b)) ?_
  refine Rle_trans (Radd_le_add_loc (Radd_le_add_loc hA hA) (Radd_le_add_loc hb2 hb2)) ?_
  exact fin_collapse4_sy k

-- ===========================================================================
-- Squared-tolerance complex convergence — congruence and uniqueness.
-- ===========================================================================

/-- **Convergence congruence** (sequence and limit): if `f n ≈ g n` for all `n`, `L ≈ L'`, and
    `g n → L`, then `f n → L'`. -/
private theorem ComplexTendsTo_congr {f g : Nat → Complex} {L L' : Complex}
    (hfg : ∀ n, Ceq (f n) (g n)) (hL : Ceq L L') (hg : ComplexTendsTo g L) :
    ComplexTendsTo f L' := by
  refine ⟨fun k => ?_, fun k => ?_⟩
  · obtain ⟨N, hN⟩ := hg.1 k
    refine ⟨N, fun n hn => ?_⟩
    have heq : Req (Rsub (f n).re L'.re) (Rsub (g n).re L.re) :=
      Rsub_congr (hfg n).1 (Req_symm hL.1)
    exact Rle_trans (Rle_of_Req (Rmul_congr heq heq)) (hN n hn)
  · obtain ⟨N, hN⟩ := hg.2 k
    refine ⟨N, fun n hn => ?_⟩
    have heq : Req (Rsub (f n).im L'.im) (Rsub (g n).im L.im) :=
      Rsub_congr (hfg n).2 (Req_symm hL.2)
    exact Rle_trans (Rle_of_Req (Rmul_congr heq heq)) (hN n hn)

/-- **Conjugate continuity**: `zs n → z ⟹ conj(zs n) → conj z`. The real coordinate is unchanged; the
    imaginary coordinate negates, and `(−p − (−q))² ≈ (p−q)²` transfers the bound. -/
private theorem ComplexTendsTo_conj {zs : Nat → Complex} {z : Complex}
    (h : ComplexTendsTo zs z) : ComplexTendsTo (fun n => Cconj (zs n)) (Cconj z) := by
  refine ⟨fun k => ?_, fun k => ?_⟩
  · obtain ⟨N, hN⟩ := h.1 k
    exact ⟨N, fun n hn => hN n hn⟩
  · obtain ⟨N, hN⟩ := h.2 k
    refine ⟨N, fun n hn => ?_⟩
    exact Rle_trans (Rle_of_Req (conj_im_sq_eq_sy (zs n).im z.im)) (hN n hn)

/-- **Limit uniqueness**: a complex sequence has at most one squared-tolerance limit. -/
private theorem ComplexTendsTo_unique {f : Nat → Complex} {L L' : Complex}
    (h1 : ComplexTendsTo f L) (h2 : ComplexTendsTo f L') : Ceq L L' :=
  ⟨Rlim_sub_sq_unique_sy (fun n => (f n).re) L.re L'.re h1.1 h2.1,
   Rlim_sub_sq_unique_sy (fun n => (f n).im) L.im L'.im h1.2 h2.2⟩

-- ===========================================================================
-- Completion inner-product LEFT laws (built from Hermitian symmetry + the right laws).
-- ===========================================================================

/-- `⟨0, R⟩ ≈ 0` (left-zero), via Hermitian symmetry. -/
private theorem completedInner_zero_left_sy (R : DLimCompletionRaw) :
    Ceq (completedInner dlimCompletionZero R) Czero :=
  Ceq_trans (completedInner_conj dlimCompletionZero R)
    (Ceq_trans (Cconj_congr (completedInner_zero_right_cpl R)) Cconj_Czero)

/-- `⟨c•U, V⟩ ≈ (conj c)·⟨U, V⟩` (left scalar), via Hermitian symmetry and `completedInner_smul_right`. -/
private theorem completedInner_smul_left_sy (c : Complex) (U V : DLimCompletionRaw) :
    Ceq (completedInner (dlimCompletionSmul c U) V) (Cmul (Cconj c) (completedInner U V)) :=
  Ceq_trans (completedInner_conj (dlimCompletionSmul c U) V)
    (Ceq_trans (Cconj_congr (completedInner_smul_right c V U))
      (Ceq_trans (Cconj_Cmul c (completedInner V U))
        (Cmul_congr (Ceq_refl (Cconj c)) (Ceq_symm (completedInner_conj U V)))))

-- ===========================================================================
-- The finite coordinate sum and the finite-rank inner read (TARGET A).
-- ===========================================================================

/-- `finCoordSum N A B = Σ_{i<N} conj(⟨e_i,A⟩)·⟨e_i,B⟩` — the finite Parseval partial sum. -/
def finCoordSum : Nat → DLimCompletionRaw → DLimCompletionRaw → Complex
  | 0, _, _ => Czero
  | (N + 1), A, B => Cadd (finCoordSum N A B) (Cmul (Cconj (coord N A)) (coord N B))

/-- **A — FINITE-RANK inner read**: `⟨finProj N A, B⟩ ≈ Σ_{i<N} conj(A_i)·B_i`. Induction on `N`,
    peeling `finProj (N+1) A = finProj N A ⊕ (A_N)•(of e_N)` through left-additivity and the left scalar
    law, using `⟨of e_N, B⟩ = coord N B` definitionally. -/
theorem completedInner_finrank_sy : ∀ (N : Nat) (A B : DLimCompletionRaw),
    Ceq (completedInner (finProj N A) B) (finCoordSum N A B)
  | 0, _, B => completedInner_zero_left_sy B
  | (N + 1), A, B => by
      refine Ceq_trans (completedInner_add_left_cpl (finProj N A)
        (dlimCompletionSmul (coord N A) (DLimCompletionRaw.of (dlimBasis N))) B) ?_
      exact Cadd_congr (completedInner_finrank_sy N A B)
        (completedInner_smul_left_sy (coord N A) (DLimCompletionRaw.of (dlimBasis N)) B)

-- ===========================================================================
-- First-slot LIMIT continuity of the coordinate projections (TARGET B).
-- ===========================================================================

/-- **B — first-slot continuity**: `⟨finProj N A, B⟩ → ⟨A, B⟩` in squared tolerance. Route: the
    projections converge to `A` (`finProj_converges_pj`), so the fixed-vector continuity
    `inner_fixed_tendsto_scs` gives `⟨B, finProj N A⟩ → ⟨B, A⟩`; conjugating (`ComplexTendsTo_conj`)
    and re-reading `⟨finProj N A, B⟩ ≈ conj⟨B, finProj N A⟩`, `conj⟨B,A⟩ ≈ ⟨A,B⟩` closes it. -/
theorem completedInner_finProj_tendsto_sy (A B : DLimCompletionRaw) :
    ComplexTendsTo (fun N => completedInner (finProj N A) B) (completedInner A B) := by
  have hconv : CompletionTendsTo (fun N => finProj N A) A := by
    intro k
    obtain ⟨N0, hN0⟩ := finProj_converges_pj A k
    refine ⟨N0, fun n hn => ?_⟩
    exact Rle_trans (Rle_of_Req (completedDist2_symm_cpl (finProj n A) A)) (hN0 n hn)
  have hBA : ComplexTendsTo (fun n => completedInner B (finProj n A)) (completedInner B A) :=
    inner_fixed_tendsto_scs B (fun N => finProj N A) A hconv
  refine ComplexTendsTo_congr
    (f := fun N => completedInner (finProj N A) B)
    (g := fun n => Cconj (completedInner B (finProj n A)))
    (L := Cconj (completedInner B A))
    (L' := completedInner A B)
    (fun n => completedInner_conj (finProj n A) B)
    (Ceq_symm (completedInner_conj A B))
    (ComplexTendsTo_conj hBA)

-- ===========================================================================
-- PARSEVAL (TARGET C).
-- ===========================================================================

/-- **C — PARSEVAL**: the completion inner product is the limit of the finite coordinate sums,
    `Σ_{i<N} conj(A_i)·B_i → ⟨A, B⟩`. Rewrite the convergent sequence of `B` through the finite-rank
    read `A`. -/
theorem completedInner_parseval_sy (A B : DLimCompletionRaw) :
    ComplexTendsTo (fun N => finCoordSum N A B) (completedInner A B) :=
  ComplexTendsTo_congr
    (f := fun N => finCoordSum N A B)
    (g := fun N => completedInner (finProj N A) B)
    (L := completedInner A B) (L' := completedInner A B)
    (fun n => Ceq_symm (completedInner_finrank_sy n A B))
    (Ceq_refl (completedInner A B))
    (completedInner_finProj_tendsto_sy A B)

-- ===========================================================================
-- The termwise real-weight identity and the finite-sum symmetry.
-- ===========================================================================

/-- Local real→complex embedding (matching the multiplier's private `cReal`, defeq `⟨r,0⟩`). -/
private def cReal (r : Real) : Complex := ⟨r, zero⟩

/-- `conj(r) ≈ r` for a real-embedded scalar. -/
private theorem Cconj_cReal_sy (r : Real) : Ceq (Cconj (cReal r)) (cReal r) :=
  ⟨Req_refl r, Rneg_zero_sy⟩

/-- `(r·a)·b ≈ a·(r·b)` — the real-scalar is central. -/
private theorem Cmul_comm_mid_sy (r a b : Complex) :
    Ceq (Cmul (Cmul r a) b) (Cmul a (Cmul r b)) :=
  Ceq_trans (Cmul_congr (Cmul_comm r a) (Ceq_refl b)) (Cmul_assoc a r b)

/-- **Finite-sum symmetry**: `Σ_{i<N} conj(Xp_i)·Y_i ≈ Σ_{i<N} conj(X_i)·Yp_i` for graph pairs
    `(X,Xp), (Y,Yp)`. Each term `conj(w_i·X_i)·Y_i = conj(X_i)·(w_i·Y_i)` because the weight `w_i` is
    real (self-conjugate) and central. -/
theorem finCoordSum_symm_weight_sy (w : Nat → Real) {X Xp Y Yp : DLimCompletionRaw}
    (hX : MulGraph w X Xp) (hY : MulGraph w Y Yp) (N : Nat) :
    Ceq (finCoordSum N Xp Y) (finCoordSum N X Yp) := by
  induction N with
  | zero => exact Ceq_refl Czero
  | succ N ih =>
      refine Cadd_congr ih ?_
      have hconj : Ceq (Cconj (coord N Xp)) (Cmul (cReal (w N)) (Cconj (coord N X))) :=
        Ceq_trans (Cconj_congr (hX N))
          (Ceq_trans (Cconj_Cmul (cReal (w N)) (coord N X))
            (Cmul_congr (Cconj_cReal_sy (w N)) (Ceq_refl (Cconj (coord N X)))))
      exact Ceq_trans (Cmul_congr hconj (Ceq_refl (coord N Y)))
        (Ceq_trans (Cmul_comm_mid_sy (cReal (w N)) (Cconj (coord N X)) (coord N Y))
          (Cmul_congr (Ceq_refl (Cconj (coord N X))) (Ceq_symm (hY N))))

-- ===========================================================================
-- THE SYMMETRY (reviewer gate item 5).
-- ===========================================================================

/-- **D — SYMMETRY of the real-weight diagonal multiplier** (reviewer gate item 5): for graph pairs
    `Xp = M_w X`, `Yp = M_w Y`, `⟨M_w X, Y⟩ ≈ ⟨X, M_w Y⟩`. By PARSEVAL both inner products are limits of
    finite coordinate sums; the two finite-sum sequences are termwise `≈` (`finCoordSum_symm_weight_sy`),
    so — being a single sequence up to `≈` — they share their limit (`ComplexTendsTo_unique`). -/
theorem mult_symm_sy (w : Nat → Real) {X Xp Y Yp : DLimCompletionRaw}
    (hX : MulGraph w X Xp) (hY : MulGraph w Y Yp) :
    Ceq (completedInner Xp Y) (completedInner X Yp) := by
  have hC1 : ComplexTendsTo (fun N => finCoordSum N Xp Y) (completedInner Xp Y) :=
    completedInner_parseval_sy Xp Y
  have hC2 : ComplexTendsTo (fun N => finCoordSum N X Yp) (completedInner X Yp) :=
    completedInner_parseval_sy X Yp
  have hC2' : ComplexTendsTo (fun N => finCoordSum N Xp Y) (completedInner X Yp) :=
    ComplexTendsTo_congr
      (f := fun N => finCoordSum N Xp Y)
      (g := fun N => finCoordSum N X Yp)
      (L := completedInner X Yp) (L' := completedInner X Yp)
      (fun N => finCoordSum_symm_weight_sy w hX hY N)
      (Ceq_refl (completedInner X Yp)) hC2
  exact ComplexTendsTo_unique hC1 hC2'

end UOR.Bridge.F1Square.Square
