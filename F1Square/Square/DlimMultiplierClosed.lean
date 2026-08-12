/-
# GRAPH CLOSEDNESS of the real-weight diagonal multiplier (reviewer gate item 4)

The multiplier GRAPH `MulGraph w` is CLOSED under completion-metric limits: if each pair
`(Xs n, Ys n)` lies in the graph and `Xs n → X`, `Ys n → Y` in the completion metric, then
`(X, Y)` lies in the graph.

The heart is a SQRT-FREE squared-difference squeeze (no radical / reciprocal primitives): fix a coordinate `i` and
a component (real or imaginary).  Writing `A − B = (A − coordYsₙ) + wᵢ·(coordXsₙ − X₀)` (the middle
bracket being `0` by membership `hG n`), we bound `(A−B)² ≤ 2·(A−coordYsₙ)² + 2·wᵢ²·(coordXsₙ−X₀)²`
via the sqrt-free `(u+v)² ≤ 2u²+2v²`, then feed the two coordinate-continuity bounds
`(coord diff)² ≤ d²` and let the Archimedean squeeze (constant-tolerating: `wᵢ²` is bounded by a
rational `xBound`) drive `(A−B)²` below every `1/(k+1)`.  Bishop square-definiteness
(`Rmul_self_eq_zero_imp`) then gives `A ≈ B`.

ZETA-FREE: imports only the completion cone `DlimMultiplier`; every "basic" (two-square bound,
Archimedean squeeze, real-upper-bound, double-negation, …) is rebuilt in-cone.  WHNF-safe: the
completion black boxes `completedDist2` / `coord` are never unfolded by defeq — only the
`coord_*continuity`, `completedDist2_*`, `coord_*` laws are used.
-/
import F1Square.Square.DlimMultiplier
import F1Square.Square.DlimCompletionLimit

open UOR.Bridge.F1Square Square
open UOR.Bridge.F1Square.Analysis

namespace UOR.Bridge.F1Square.Square

-- ===========================================================================
-- Local ℝ micro-helpers (leaf names end `_cl`), rebuilt from in-cone primitives.
-- ===========================================================================

/-- `0 ⊕ x ≈ x`. -/
private theorem Rzero_add_cl (x : Real) : Req (Radd zero x) x :=
  Req_trans (Radd_comm zero x) (Radd_zero x)

/-- `0 · x ≈ 0`. -/
private theorem Rzero_mul_cl (x : Real) : Req (Rmul zero x) zero :=
  Req_trans (Rmul_comm zero x) (Rmul_zero x)

/-- Double negation: `−(−x) ≈ x`. -/
private theorem Rneg_Rneg_cl (x : Real) : Req (Rneg (Rneg x)) x :=
  Req_of_seq_Qeq (fun n => by
    show Qeq (neg (neg (x.seq n))) (x.seq n); simp only [Qeq, neg]; push_cast; ring_uor)

/-- `x − y ≈ 0 ⟹ x ≈ y`. -/
private theorem Req_of_Rsub_zero_cl {a b : Real} (h : Req (Rsub a b) zero) : Req a b := by
  have hid : Req (Radd (Rsub a b) b) a :=
    Req_trans (Radd_assoc a (Rneg b) b)
      (Req_trans (Radd_congr (Req_refl a)
          (Req_trans (Radd_comm (Rneg b) b) (Radd_neg b)))
        (Radd_zero a))
  exact Req_trans (Req_symm hid) (Req_trans (Radd_congr h (Req_refl b)) (Rzero_add_cl b))

/-- `0 ≤ b ⟹ a ≤ a ⊕ b`. -/
private theorem Rle_add_nonneg_right_cl (a b : Real) (hb : Rnonneg b) : Rle a (Radd a b) :=
  Rle_of_Rnonneg_Rsub_loc
    (Rnonneg_congr_loc
      (Req_symm
        (Req_trans (Radd_congr (Radd_comm a b) (Req_refl (Rneg a)))
          (Req_trans (Radd_assoc b a (Rneg a))
            (Req_trans (Radd_congr (Req_refl b) (Radd_neg a)) (Radd_zero b)))))
      hb)

/-- `(a·t)·(a·t) ≈ (a·a)·(t·t)` — the real-scalar square factoring. -/
private theorem Rmul_self_mul_cl (a t : Real) :
    Req (Rmul (Rmul a t) (Rmul a t)) (Rmul (Rmul a a) (Rmul t t)) :=
  Req_trans (Rmul_assoc a t (Rmul a t))
    (Req_trans (Rmul_congr (Req_refl a) (Req_symm (Rmul_assoc t a t)))
      (Req_trans (Rmul_congr (Req_refl a) (Rmul_congr (Rmul_comm t a) (Req_refl t)))
        (Req_trans (Rmul_congr (Req_refl a) (Rmul_assoc a t t))
          (Req_symm (Rmul_assoc a a (Rmul t t))))))

/-- **The sqrt-free two-square bound**: `(u+v)² ≤ 2u² + 2v²`.  Route: `2u²+2v² − (u+v)² = (u−v)² ≥ 0`
    (`E1 ⊕ E2 ≈ 2u²+2v²` with the cross terms `±uv, ±vu` cancelling), so `(u+v)² ≤ (u+v)²⊕(u−v)²`. -/
private theorem two_sq_bound_cl (u v : Real) :
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
              (Req_trans (Rneg_congr (Rmul_neg_right v v)) (Rneg_Rneg_cl (Rmul v v)))))))
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
            (Rzero_add_cl (Radd (Rmul v v) (Rmul v v))))))
  have hSum : Req (Radd (Rmul (Radd u v) (Radd u v)) (Rmul (Rsub u v) (Rsub u v)))
      (Radd (Radd (Rmul u u) (Rmul u u)) (Radd (Rmul v v) (Rmul v v))) :=
    Req_trans (Radd_congr hE1 hE2) hAdd
  exact Rle_trans
    (Rle_add_nonneg_right_cl (Rmul (Radd u v) (Radd u v)) (Rmul (Rsub u v) (Rsub u v))
      (Rnonneg_Rmul_self_loc (Rsub u v)))
    (Rle_of_Req hSum)

/-- **Real upper bound by a rational**: `x ≤ ⟨K_x, 1⟩` (the canonical Bishop bound). -/
private theorem Rle_xBound_cl (x : Real) :
    Rle x (ofQ (⟨(xBound x : Int), 1⟩ : Q) Nat.one_pos) := by
  intro n
  show Qle (x.seq n) (add (⟨(xBound x : Int), 1⟩ : Q) (⟨2, n + 1⟩ : Q))
  have h1 : Qle (x.seq n) (⟨(xBound x : Int), 1⟩ : Q) :=
    Qle_trans (Qabs_den_pos (x.den_pos n)) (Qle_self_Qabs (x.seq n)) (canon_bound x n)
  exact Qle_trans Nat.one_pos h1 (Qle_self_add (by show (0 : Int) ≤ 2; decide))

/-- **Archimedean squeeze**: a nonnegative real `≤ 1/(k+1)` for every `k` is `≈ 0`. -/
private theorem Req_zero_of_nonneg_of_small_cl {x : Real} (hnn : Rnonneg x)
    (hall : ∀ k : Nat, Rle x (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k))) : Req x zero := by
  refine Rle_antisymm ?_ (Rle_zero_of_Rnonneg hnn)
  intro n
  refine Qarch_gen (C := 1) (x.den_pos n) (add_den_pos (zero.den_pos n) (Nat.succ_pos n)) (fun k => ?_)
  have hb : Qle (x.seq n) (add (⟨1, k + 1⟩ : Q) (⟨2, n + 1⟩ : Q)) := hall k n
  refine Qle_congr_right (add_den_pos (Nat.succ_pos k) (Nat.succ_pos n)) ?_ hb
  simp only [Qeq, add, zero_seq]; push_cast; ring_uor

/-- Two `ofQ`s of `Qeq` rationals are `≈`. -/
private theorem ofQ_Req_of_Qeq_cl {a b : Q} (ha : 0 < a.den) (hb : 0 < b.den) (h : Qeq a b) :
    Req (ofQ a ha) (ofQ b hb) := Req_of_seq_Qeq (fun _ => h)

/-- **The final rational collapse** of the squeeze: with `P = ⟨1, (2+2b)(k+1)+1⟩`, `cB = ⟨b,1⟩`,
    `(P⊕P) ⊕ (cB·P ⊕ cB·P) = (2+2b)/((2+2b)(k+1)+1) ≤ 1/(k+1)`. -/
private theorem fin_rat_collapse_cl (b k : Nat) :
    Rle (Radd (Radd (ofQ (⟨1, (2 + 2 * b) * (k + 1) + 1⟩ : Q) (Nat.succ_pos _))
                    (ofQ (⟨1, (2 + 2 * b) * (k + 1) + 1⟩ : Q) (Nat.succ_pos _)))
              (Radd (Rmul (ofQ (⟨(b : Int), 1⟩ : Q) Nat.one_pos)
                          (ofQ (⟨1, (2 + 2 * b) * (k + 1) + 1⟩ : Q) (Nat.succ_pos _)))
                    (Rmul (ofQ (⟨(b : Int), 1⟩ : Q) Nat.one_pos)
                          (ofQ (⟨1, (2 + 2 * b) * (k + 1) + 1⟩ : Q) (Nat.succ_pos _)))))
        (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k)) := by
  have hcollapse : Req
      (Radd (Radd (ofQ (⟨1, (2 + 2 * b) * (k + 1) + 1⟩ : Q) (Nat.succ_pos _))
                  (ofQ (⟨1, (2 + 2 * b) * (k + 1) + 1⟩ : Q) (Nat.succ_pos _)))
            (Radd (Rmul (ofQ (⟨(b : Int), 1⟩ : Q) Nat.one_pos)
                        (ofQ (⟨1, (2 + 2 * b) * (k + 1) + 1⟩ : Q) (Nat.succ_pos _)))
                  (Rmul (ofQ (⟨(b : Int), 1⟩ : Q) Nat.one_pos)
                        (ofQ (⟨1, (2 + 2 * b) * (k + 1) + 1⟩ : Q) (Nat.succ_pos _)))))
      (ofQ (⟨(2 + 2 * (b : Int)), (2 + 2 * b) * (k + 1) + 1⟩ : Q) (Nat.succ_pos _)) := by
    refine Req_trans (Radd_congr (Req_refl _)
        (Radd_congr (Rmul_ofQ_ofQ_loc Nat.one_pos (Nat.succ_pos _))
                    (Rmul_ofQ_ofQ_loc Nat.one_pos (Nat.succ_pos _)))) ?_
    refine Req_trans (Radd_congr (Radd_ofQ_loc (Nat.succ_pos _) (Nat.succ_pos _))
        (Radd_ofQ_loc (Qmul_den_pos Nat.one_pos (Nat.succ_pos _))
                      (Qmul_den_pos Nat.one_pos (Nat.succ_pos _)))) ?_
    refine Req_trans (Radd_ofQ_loc (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _))
        (add_den_pos (Qmul_den_pos Nat.one_pos (Nat.succ_pos _))
                     (Qmul_den_pos Nat.one_pos (Nat.succ_pos _)))) ?_
    refine ofQ_Req_of_Qeq_cl _ _ ?_
    simp only [Qeq, add, mul]; push_cast; ring_uor
  refine Rle_trans (Rle_of_Req hcollapse) ?_
  refine Rle_ofQ_of_Qle_loc (Nat.succ_pos _) (Nat.succ_pos k) ?_
  show (2 + 2 * (b : Int)) * ((k + 1 : Nat) : Int)
      ≤ (1 : Int) * (((2 + 2 * b) * (k + 1) + 1 : Nat) : Int)
  push_cast
  omega

-- ===========================================================================
-- Completion convergence notation.
-- ===========================================================================

-- ===========================================================================
-- The abstract component squeeze (used for the real AND imaginary component).
-- ===========================================================================

/-- **The component limit**: if `aₙ ≈ wᵢ·xₙ` for all `n`, both squared coordinate deviations are
    controlled by vanishing `dY, dX`, and `dY, dX → 0`, then `A ≈ wᵢ·X₀`.  The sqrt-free squeeze:
    `(A − wᵢ·X₀)² ≤ 2·dYₙ + 2·wᵢ²·dXₙ` for every `n`, Archimedean-squeezed to `0`. -/
private theorem component_limit_cl (wi A X0 : Real) (a x dY dX : Nat → Real)
    (hdXnn : ∀ n, Rnonneg (dX n))
    (hMid : ∀ n, Req (a n) (Rmul wi (x n)))
    (hcontY : ∀ n, Rle (Rmul (Rsub A (a n)) (Rsub A (a n))) (dY n))
    (hcontX : ∀ n, Rle (Rmul (Rsub (x n) X0) (Rsub (x n) X0)) (dX n))
    (htY : ∀ k, ∃ N, ∀ n, N ≤ n → Rle (dY n) (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k)))
    (htX : ∀ k, ∃ N, ∀ n, N ≤ n → Rle (dX n) (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k))) :
    Req A (Rmul wi X0) := by
  -- per-`n` two-square bound:  (A − wᵢX₀)² ≤ (dYₙ ⊕ dYₙ) ⊕ (⟨K,1⟩·dXₙ ⊕ ⟨K,1⟩·dXₙ)
  have hSb : ∀ n, Rle (Rmul (Rsub A (Rmul wi X0)) (Rsub A (Rmul wi X0)))
      (Radd (Radd (dY n) (dY n))
            (Radd (Rmul (ofQ (⟨(xBound (Rmul wi wi) : Int), 1⟩ : Q) Nat.one_pos) (dX n))
                  (Rmul (ofQ (⟨(xBound (Rmul wi wi) : Int), 1⟩ : Q) Nat.one_pos) (dX n)))) := by
    intro n
    have hv : Req (Rmul wi (Rsub (x n) X0)) (Rsub (Rmul wi (x n)) (Rmul wi X0)) :=
      Rmul_sub_distrib wi (x n) X0
    have hcancel : Req (Radd (Rsub A (a n)) (Rsub (a n) (Rmul wi X0)))
        (Rsub A (Rmul wi X0)) :=
      Req_trans (Radd_congr (Req_refl (Rsub A (a n))) (Radd_comm (a n) (Rneg (Rmul wi X0))))
        (Req_trans (Radd_swap A (Rneg (a n)) (Rneg (Rmul wi X0)) (a n))
          (Req_trans (Radd_congr (Req_refl (Radd A (Rneg (Rmul wi X0))))
              (Req_trans (Radd_comm (Rneg (a n)) (a n)) (Radd_neg (a n))))
            (Radd_zero (Radd A (Rneg (Rmul wi X0))))))
    have hAB : Req (Rsub A (Rmul wi X0))
        (Radd (Rsub A (a n)) (Rmul wi (Rsub (x n) X0))) :=
      Req_symm
        (Req_trans (Radd_congr (Req_refl (Rsub A (a n))) hv)
          (Req_trans (Radd_congr (Req_refl (Rsub A (a n)))
              (Rsub_congr (Req_symm (hMid n)) (Req_refl (Rmul wi X0))))
            hcancel))
    refine Rle_trans (Rle_of_Req (Rmul_congr hAB hAB)) ?_
    refine Rle_trans (two_sq_bound_cl (Rsub A (a n)) (Rmul wi (Rsub (x n) X0))) ?_
    refine Radd_le_add_loc (Radd_le_add_loc (hcontY n) (hcontY n)) ?_
    have hVV : Rle (Rmul (Rmul wi (Rsub (x n) X0)) (Rmul wi (Rsub (x n) X0)))
        (Rmul (ofQ (⟨(xBound (Rmul wi wi) : Int), 1⟩ : Q) Nat.one_pos) (dX n)) :=
      Rle_trans (Rle_of_Req (Rmul_self_mul_cl wi (Rsub (x n) X0)))
        (Rle_trans (Rmul_le_Rmul_left_loc (Rnonneg_Rmul_self_loc wi) (hcontX n))
          (Rmul_le_Rmul_right_loc (hdXnn n) (Rle_xBound_cl (Rmul wi wi))))
    exact Radd_le_add_loc hVV hVV
  -- Archimedean squeeze on (A − wᵢX₀)²
  refine Req_of_Rsub_zero_cl (Rmul_self_eq_zero_imp
    (Req_zero_of_nonneg_of_small_cl (Rnonneg_Rmul_self_loc (Rsub A (Rmul wi X0))) (fun k => ?_)))
  obtain ⟨NY, hNY⟩ := htY ((2 + 2 * xBound (Rmul wi wi)) * (k + 1))
  obtain ⟨NX, hNX⟩ := htX ((2 + 2 * xBound (Rmul wi wi)) * (k + 1))
  have hdYP := hNY (max NY NX) (Nat.le_max_left NY NX)
  have hdXP := hNX (max NY NX) (Nat.le_max_right NY NX)
  refine Rle_trans (hSb (max NY NX)) ?_
  refine Rle_trans (Radd_le_add_loc (Radd_le_add_loc hdYP hdYP)
      (Radd_le_add_loc
        (Rmul_le_Rmul_left_loc (Rnonneg_ofQ_loc Nat.one_pos (Int.ofNat_nonneg _)) hdXP)
        (Rmul_le_Rmul_left_loc (Rnonneg_ofQ_loc Nat.one_pos (Int.ofNat_nonneg _)) hdXP)))
    ?_
  exact fin_rat_collapse_cl (xBound (Rmul wi wi)) k

-- ===========================================================================
-- Reviewer gate item 4 — the graph is CLOSED under completion-metric limits.
-- ===========================================================================

/-- **Graph closedness of the real-weight diagonal multiplier**: the multiplier GRAPH `MulGraph w`
    is closed — if each `(Xs n, Ys n)` lies in the graph and `Xs n → X`, `Ys n → Y` in the
    completion metric, then `(X, Y)` lies in the graph.  Component-wise (`.re`/`.im`) the coordinate
    identity `coord i Y ≈ wᵢ·coord i X` is the sqrt-free squared-difference squeeze. -/
theorem MulGraph_closed_cl (w : Nat → Real) (Xs Ys : Nat → DLimCompletionRaw) (X Y : DLimCompletionRaw)
    (hX : CompletionTendsTo Xs X) (hY : CompletionTendsTo Ys Y)
    (hG : ∀ n : Nat, MulGraph w (Xs n) (Ys n)) :
    MulGraph w X Y := by
  intro i
  -- real component core
  have hcore_re : Req (coord i Y).re (Rmul (w i) (coord i X).re) :=
    component_limit_cl (w i) (coord i Y).re (coord i X).re
      (fun n => (coord i (Ys n)).re) (fun n => (coord i (Xs n)).re)
      (fun n => completedDist2 (Ys n) Y) (fun n => completedDist2 (Xs n) X)
      (fun n => completedDist2_nonneg (Xs n) X)
      (fun n => by
        refine Req_trans (hG n i).1 ?_
        show Req (Rsub (Rmul (w i) (coord i (Xs n)).re) (Rmul zero (coord i (Xs n)).im))
                 (Rmul (w i) (coord i (Xs n)).re)
        exact Req_trans (Rsub_congr (Req_refl _) (Rzero_mul_cl _)) (Rsub_zero _))
      (fun n => Rle_trans (coord_re_continuity i Y (Ys n))
        (Rle_of_Req (completedDist2_symm_cpl Y (Ys n))))
      (fun n => coord_re_continuity i (Xs n) X)
      hY hX
  -- imaginary component core
  have hcore_im : Req (coord i Y).im (Rmul (w i) (coord i X).im) :=
    component_limit_cl (w i) (coord i Y).im (coord i X).im
      (fun n => (coord i (Ys n)).im) (fun n => (coord i (Xs n)).im)
      (fun n => completedDist2 (Ys n) Y) (fun n => completedDist2 (Xs n) X)
      (fun n => completedDist2_nonneg (Xs n) X)
      (fun n => by
        refine Req_trans (hG n i).2 ?_
        show Req (Radd (Rmul (w i) (coord i (Xs n)).im) (Rmul zero (coord i (Xs n)).re))
                 (Rmul (w i) (coord i (Xs n)).im)
        exact Req_trans (Radd_congr (Req_refl _) (Rzero_mul_cl _)) (Radd_zero _))
      (fun n => Rle_trans (coord_im_continuity i Y (Ys n))
        (Rle_of_Req (completedDist2_symm_cpl Y (Ys n))))
      (fun n => coord_im_continuity i (Xs n) X)
      hY hX
  refine ⟨?_, ?_⟩
  · refine Req_trans hcore_re ?_
    show Req (Rmul (w i) (coord i X).re)
             (Rsub (Rmul (w i) (coord i X).re) (Rmul zero (coord i X).im))
    exact Req_symm (Req_trans (Rsub_congr (Req_refl _) (Rzero_mul_cl _)) (Rsub_zero _))
  · refine Req_trans hcore_im ?_
    show Req (Rmul (w i) (coord i X).im)
             (Radd (Rmul (w i) (coord i X).im) (Rmul zero (coord i X).re))
    exact Req_symm (Req_trans (Radd_congr (Req_refl _) (Rzero_mul_cl _)) (Radd_zero _))


/-- **Domain setoid-congruence** (reviewer gate item 3): `MulDom` descends to the completion setoid. -/
theorem MulDom_congr_mcl (w : Nat → Real) {X Xb : DLimCompletionRaw} (h : DLimCompletionEq X Xb)
    (hX : MulDom w X) : MulDom w Xb := by
  obtain ⟨Y, hY⟩ := hX
  exact ⟨Y, MulGraph_congr_mp w h (DLimCompletionEq_refl Y) hY⟩

end UOR.Bridge.F1Square.Square
