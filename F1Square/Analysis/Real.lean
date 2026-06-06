/-
F1 square — the second analysis brick: constructive ℝ as Bishop regular sequences over our exact ℚ
(the v0.3.0 continuation of the analysis roadmap).

Per the standing directive, the analytic substrate is built from first principles the UOR way. Brick
one was exact ℚ (`Analysis.Rat`); this is brick two: the real numbers as **regular sequences of
rationals** (Bishop), the constructive encoding that bakes the modulus of convergence into the data
so no choice principle is needed:

  a sequence `x : ℕ → ℚ` is *regular* iff `|xₘ − xₙ| ≤ 1/(m+1) + 1/(n+1)` for all `m, n`.

The index *is* the modulus. A real number is a regular sequence; equality is the (undecidable, but
Prop-valued) Bishop relation `x ≈ y  ⟺  |xₙ − yₙ| ≤ 2/(n+1) ∀ n`; positivity is the witnessed
`∃ n, xₙ > 1/(n+1)`. This is the standard no-Mathlib encoding (cf. Bishop–Bridges; the Agda
constructive-analysis development arXiv:2205.08354).

Scope (v0.4.0 — ℝ as an ordered additive group): on top of the v0.3.0 type/setoid, this release adds
**ℝ arithmetic with full regularity proofs** — negation `Rneg` and the (reindexed) Bishop addition
`Radd` — built on the new ℚ ordered-field library (`Analysis.QOrder`) and the from-scratch `ring_uor`
tactic. The `Real` structure now also carries `den_pos` (every term has a positive denominator), which
the order arguments need. Multiplication, `≈`-transitivity (a genuine limiting/Archimedean argument),
ℂ = ℝ×ℝ, and the transcendentals are the v0.5.0 continuation. None of this is the crux: making ζ/λₙ
exact-bounded objects is statable here; proving `λₙ ≥ 0 ∀n` is RH.

Pure Lean 4, no Mathlib, no `sorry`.
-/

import F1Square.Analysis.QOrder

namespace UOR.Bridge.F1Square.Analysis

/-- The modulus rational `1/(n+1) > 0` — both the regularity bound and the positivity threshold. -/
def Qbound (n : Nat) : Q := ⟨1, n + 1⟩

/-- The modulus rational has a positive denominator. -/
theorem Qbound_den_pos (k : Nat) : 0 < (Qbound k).den := Nat.succ_pos k

/-- The numerator of `a − a` is `0` (exact cancellation; via the additive structure). -/
theorem Qsub_self_num (a : Q) : (Qsub a a).num = 0 := by
  simp only [Qsub, add, neg]; rw [Int.neg_mul]; omega

/-- `b − a` has the negated numerator of `a − b`. -/
theorem Qsub_swap_num (a b : Q) : (Qsub b a).num = -(Qsub a b).num := by
  simp only [Qsub, add, neg]; rw [Int.neg_mul, Int.neg_mul]; omega

/-- `b − a` and `a − b` share a denominator (it is `dₐ·d_b` either way). -/
theorem Qsub_swap_den (a b : Q) : (Qsub b a).den = (Qsub a b).den := by
  simp only [Qsub, add, neg]; exact Nat.mul_comm b.den a.den

/-- **Regularity** (Bishop): `|xₘ − xₙ| ≤ 1/(m+1) + 1/(n+1)` for all `m, n`. -/
def IsRegular (x : Nat → Q) : Prop :=
  ∀ m n : Nat, Qle (Qabs (Qsub (x m) (x n))) (add (Qbound m) (Qbound n))

/-- A **constructive real number**: a regular sequence of rationals, every term with a positive
    denominator (so the ℚ order/equality cross-multiplications behave). -/
structure Real where
  seq : Nat → Q
  reg : IsRegular seq
  den_pos : ∀ n, 0 < (seq n).den

/-- The constant sequence at `q` is regular (its gaps are `0 ≤` a positive bound). -/
theorem const_regular (q : Q) : IsRegular (fun _ => q) := by
  intro m n
  unfold Qle Qabs
  rw [Qsub_self_num]
  simp only [Int.natAbs_zero, Int.ofNat_zero, Int.zero_mul]
  -- 0 ≤ (1/(m+1) + 1/(n+1)).num · (denominator)
  have hden : (0 : Int) ≤ ((Qsub q q).den : Int) := Int.ofNat_nonneg _
  have hnum : (0 : Int) ≤ (add (Qbound m) (Qbound n)).num := by
    simp only [add, Qbound]; omega
  exact Int.mul_nonneg hnum hden

/-- The canonical embedding ℚ ↪ ℝ as the constant sequence (needs a positive denominator). -/
def ofQ (q : Q) (hq : 0 < q.den) : Real := ⟨fun _ => q, const_regular q, fun _ => hq⟩

/-- Zero and one in ℝ. -/
def zero : Real := ofQ ⟨0, 1⟩ (by decide)
def one : Real := ofQ ⟨1, 1⟩ (by decide)

/-- **Bishop equality** on ℝ: `x ≈ y ⟺ |xₙ − yₙ| ≤ 2/(n+1)` for all `n`. -/
def Req (x y : Real) : Prop :=
  ∀ n : Nat, Qle (Qabs (Qsub (x.seq n) (y.seq n))) ⟨2, n + 1⟩

/-- `≈` is reflexive. -/
theorem Req_refl (x : Real) : Req x x := by
  intro n
  unfold Qle Qabs
  rw [Qsub_self_num]
  simp only [Int.natAbs_zero, Int.ofNat_zero, Int.zero_mul]
  have hden : (0 : Int) ≤ ((Qsub (x.seq n) (x.seq n)).den : Int) := Int.ofNat_nonneg _
  omega

/-- `≈` is symmetric (`|xₙ − yₙ| = |yₙ − xₙ|`). -/
theorem Req_symm {x y : Real} (h : Req x y) : Req y x := by
  intro n
  have hnum := Qsub_swap_num (x.seq n) (y.seq n)
  have hden := Qsub_swap_den (x.seq n) (y.seq n)
  have hx := h n
  unfold Qle Qabs at hx ⊢
  rw [hnum, Int.natAbs_neg, hden]
  exact hx

/-- `≈` is transitive — the genuine limiting argument. For each index `n`, the gap `|xₙ − zₙ|` is
    bounded, *for every auxiliary index `m`*, by `2/(n+1) + 6/(m+1)` (four triangle steps through
    `xₘ, yₘ, zₘ` plus the regularity/equality bounds); the Archimedean lemma then kills the `6/(m+1)`
    tail. Together with `Req_refl`/`Req_symm`, Bishop equality on ℝ is an equivalence relation. -/
theorem Req_trans {x y z : Real} (hxy : Req x y) (hyz : Req y z) : Req x z := by
  intro n
  apply Qarch (Qabs_den_pos (Qsub_den_pos (x.den_pos n) (z.den_pos n))) (Nat.succ_pos n)
  intro m
  have hxn := x.den_pos n; have hxm := x.den_pos m
  have hym := y.den_pos m; have hzm := z.den_pos m; have hzn := z.den_pos n
  have h2m : 0 < (⟨2, m + 1⟩ : Q).den := Nat.succ_pos m
  -- three triangle steps: |xₙ−zₙ| ≤ |xₙ−zₘ|+|zₘ−zₙ| ≤ |xₙ−yₘ|+|yₘ−zₘ|+… ≤ |xₙ−xₘ|+|xₘ−yₘ|+…
  have h1 := Qabs_sub_triangle (a := x.seq n) (b := z.seq m) (c := z.seq n) hxn hzm hzn
  have h2 := Qabs_sub_triangle (a := x.seq n) (b := y.seq m) (c := z.seq m) hxn hym hzm
  have h3 := Qabs_sub_triangle (a := x.seq n) (b := x.seq m) (c := y.seq m) hxn hxm hym
  -- the four pieces' bounds
  have c3 := Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos hxn hxm))
      (Qabs_den_pos (Qsub_den_pos hxm hym))) h3 (Qadd_le_add (x.reg n m) (hxy m))
  have c2 := Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos hxn hym))
      (Qabs_den_pos (Qsub_den_pos hym hzm))) h2 (Qadd_le_add c3 (hyz m))
  have c1 := Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos hxn hzm))
      (Qabs_den_pos (Qsub_den_pos hzm hzn))) h1 (Qadd_le_add c2 (z.reg m n))
  -- the assembled bound equals 2/(n+1) + 6/(m+1)
  have hfin : Qle (add (add (add (add (Qbound n) (Qbound m)) ⟨2, m + 1⟩) ⟨2, m + 1⟩)
                      (add (Qbound m) (Qbound n))) (add ⟨2, n + 1⟩ ⟨6, m + 1⟩) := by
    apply Qeq_le; simp only [Qeq, add, Qbound]; push_cast; ring_uor
  exact Qle_trans (add_den_pos (add_den_pos (add_den_pos (add_den_pos
      (Qbound_den_pos n) (Qbound_den_pos m)) h2m) h2m) (add_den_pos (Qbound_den_pos m)
      (Qbound_den_pos n))) c1 hfin

/-- The embedding respects ℚ value-equality: `q = r` (as rationals) ⟹ `ofQ q ≈ ofQ r`. -/
theorem ofQ_respects {q r : Q} (hq : 0 < q.den) (hr : 0 < r.den) (h : Qeq q r) :
    Req (ofQ q hq) (ofQ r hr) := by
  intro n
  unfold Qle Qabs ofQ
  simp only
  -- |q − r| = 0 since q = r (value), so ≤ 2/(n+1)
  have h0 : (Qsub q r).num = 0 := by
    simp only [Qsub, add, neg]; rw [Int.neg_mul]
    have := h; unfold Qeq at this; omega
  rw [h0]
  simp only [Int.natAbs_zero, Int.ofNat_zero, Int.zero_mul]
  have hden : (0 : Int) ≤ ((Qsub q r).den : Int) := Int.ofNat_nonneg _
  omega

/-- **Positivity** (Bishop): `x > 0 ⟺ ∃ n, xₙ > 1/(n+1)`. -/
def Pos (x : Real) : Prop := ∃ n : Nat, Qlt (Qbound n) (x.seq n)

/-- `1/2`, as a constructive real. -/
def half : Real := ofQ ⟨1, 2⟩ (by decide)

/-- `half` is positive — witnessed at `n = 2` (`1/3 < 1/2`). -/
theorem Pos_half : Pos half := ⟨2, by decide⟩

-- ===========================================================================
-- v0.4.0 — ℝ arithmetic with regularity proofs (ℝ as an ordered additive group).
-- ===========================================================================

/-- `|(−a) − (−b)| = |a − b|` exactly, as rationals (numerator negated, denominator preserved). -/
theorem Qabs_Qsub_neg (a b : Q) : Qabs (Qsub (neg a) (neg b)) = Qabs (Qsub a b) := by
  simp only [Qabs, Qsub, add, neg]
  congr 1
  have e : (-a.num) * (b.den : Int) + (- -b.num) * (a.den : Int)
      = -(a.num * (b.den : Int) + (-b.num) * (a.den : Int)) := by ring_uor
  rw [e, Int.natAbs_neg]

/-- **Negation** of a constructive real: `(−x)ₙ := −(xₙ)`. Regular, since negation is an isometry. -/
def Rneg (x : Real) : Real where
  seq := fun n => neg (x.seq n)
  reg := by
    intro m n
    rw [Qabs_Qsub_neg]
    exact x.reg m n
  den_pos := fun n => neg_den_pos (x.den_pos n)

/-- **Addition** of constructive reals (Bishop): `(x ⊕ y)ₙ := x₍₂ₙ₊₁₎ + y₍₂ₙ₊₁₎`. The factor-2
    reindexing is exactly what restores regularity (`2·1/(2k+2) = 1/(k+1)`). -/
def Radd (x y : Real) : Real where
  seq := fun n => add (x.seq (2 * n + 1)) (y.seq (2 * n + 1))
  reg := by
    intro m n
    have hxm := x.den_pos (2 * m + 1); have hxn := x.den_pos (2 * n + 1)
    have hym := y.den_pos (2 * m + 1); have hyn := y.den_pos (2 * n + 1)
    -- triangle: split the difference of sums coordinatewise
    have htri := Qabs_sub_add4 (a := x.seq (2 * m + 1)) (b := y.seq (2 * m + 1))
        (c := x.seq (2 * n + 1)) (d := y.seq (2 * n + 1)) hxm hym hxn hyn
    -- each coordinate ≤ its regularity bound; sum them monotonically
    have hsum := Qadd_le_add (x.reg (2 * m + 1) (2 * n + 1)) (y.reg (2 * m + 1) (2 * n + 1))
    -- the doubled bound equals 1/(m+1) + 1/(n+1)
    have hbound : Qle (add (add (Qbound (2 * m + 1)) (Qbound (2 * n + 1)))
                          (add (Qbound (2 * m + 1)) (Qbound (2 * n + 1)))) (add (Qbound m) (Qbound n)) := by
      apply Qeq_le; simp only [Qeq, add, Qbound]; push_cast; ring_uor
    have hpos1 : 0 < (add (Qabs (Qsub (x.seq (2 * m + 1)) (x.seq (2 * n + 1))))
                        (Qabs (Qsub (y.seq (2 * m + 1)) (y.seq (2 * n + 1))))).den :=
      add_den_pos (Qabs_den_pos (Qsub_den_pos hxm hxn)) (Qabs_den_pos (Qsub_den_pos hym hyn))
    have hpos2 : 0 < (add (add (Qbound (2 * m + 1)) (Qbound (2 * n + 1)))
                        (add (Qbound (2 * m + 1)) (Qbound (2 * n + 1)))).den :=
      add_den_pos (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _))
        (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _))
    exact Qle_trans hpos2 (Qle_trans hpos1 htri hsum) hbound
  den_pos := fun n => add_den_pos (x.den_pos (2 * n + 1)) (y.den_pos (2 * n + 1))

/-- `Rneg` is an involution on the underlying sequences (`−(−x) = x` pointwise in value). -/
theorem Rneg_Rneg_seq (x : Real) (n : Nat) : ((Rneg (Rneg x)).seq n).num = (x.seq n).num := by
  simp only [Rneg, neg]; omega

/-- Two reals are `≈` if their sequences agree in ℚ-value pointwise (the gap is exactly `0`). The
    workhorse for the pointwise additive-group laws below. -/
theorem Req_of_seq_Qeq {x y : Real} (h : ∀ n, Qeq (x.seq n) (y.seq n)) : Req x y := by
  intro n
  unfold Qle Qabs
  have h0 : (Qsub (x.seq n) (y.seq n)).num = 0 := by
    simp only [Qsub, add, neg]; rw [Int.neg_mul]; have := h n; unfold Qeq at this; omega
  rw [h0]
  simp only [Int.natAbs_zero, Int.ofNat_zero, Int.zero_mul]
  have hden : (0 : Int) ≤ ((Qsub (x.seq n) (y.seq n)).den : Int) := Int.ofNat_nonneg _
  omega

/-- A uniform integer bound on a regular sequence: `K_x := |x₀.num| + 2·x₀.den`, with `|xₙ| ≤ K_x`
    for all `n` (the canonical Bishop bound `|xₙ| ≤ |x₀| + 2`, cleared of denominators). -/
def xBound (x : Real) : Nat := (x.seq 0).num.natAbs + 2 * (x.seq 0).den

/-- The canonical bound holds at every index: `|xₙ| ≤ K_x`. -/
theorem canon_bound (x : Real) (n : Nat) : Qle (Qabs (x.seq n)) ⟨xBound x, 1⟩ := by
  have h0 := x.den_pos 0
  have t1 := Qabs_le_add (a := x.seq 0) (b := x.seq n) h0 (x.den_pos n)
  have hreg : Qle (Qabs (Qsub (x.seq n) (x.seq 0))) ⟨2, 1⟩ := by
    have hb : Qle (add (Qbound n) (Qbound 0)) ⟨2, 1⟩ := by
      simp only [Qle, add, Qbound]; push_cast; omega
    exact Qle_trans (add_den_pos (Qbound_den_pos n) (Qbound_den_pos 0)) (x.reg n 0) hb
  have t2 : Qle (add (Qabs (x.seq 0)) (Qabs (Qsub (x.seq n) (x.seq 0))))
                (add (Qabs (x.seq 0)) ⟨2, 1⟩) := Qadd_le_add (Qle_refl _) hreg
  have t3 : Qle (add (Qabs (x.seq 0)) ⟨2, 1⟩) ⟨xBound x, 1⟩ := by
    simp only [Qle, add, Qabs, xBound]; push_cast
    have hL : (0 : Int) ≤ ((x.seq 0).num.natAbs : Int) + 2 * ((x.seq 0).den : Int) := by omega
    have hD : (1 : Int) ≤ ((x.seq 0).den : Int) := by omega
    simpa using Int.mul_le_mul_of_nonneg_left hD hL
  exact Qle_trans
    (add_den_pos (Qabs_den_pos h0) (Qabs_den_pos (Qsub_den_pos (x.den_pos n) h0))) t1
    (Qle_trans (add_den_pos (Qabs_den_pos h0) Nat.one_pos) t2 t3)

/-- The common multiplication bound `K = max(K_x, K_y)`. -/
def RmulK (x y : Real) : Nat := max (xBound x) (xBound y)

/-- The canonical bound is positive. -/
theorem xBound_pos (x : Real) : 0 < xBound x := by
  unfold xBound; have := x.den_pos 0; omega

/-- `K = max(K_x, K_y)` is positive. -/
theorem RmulK_pos (x y : Real) : 0 < RmulK x y := by
  unfold RmulK; have := xBound_pos x; omega

/-- The multiplication reindex `r(n) = 2K(n+1) − 1`, chosen so that `r(n)+1 = 2K(n+1)`. -/
def Ridx (x y : Real) (n : Nat) : Nat := 2 * RmulK x y * (n + 1) - 1

/-- The defining property of the reindex: `r(n) + 1 = 2K(n+1)` (the `−1` is undone since `2K(n+1) ≥ 1`). -/
theorem Ridx_succ (x y : Real) (n : Nat) : Ridx x y n + 1 = 2 * RmulK x y * (n + 1) := by
  unfold Ridx
  have h : 0 < 2 * RmulK x y * (n + 1) :=
    Nat.mul_pos (Nat.mul_pos (by omega) (RmulK_pos x y)) (Nat.succ_pos n)
  omega

/-- **Multiplication** of constructive reals (Bishop): reindex both factors at `r(n) = 2K(n+1)−1`
    (with `K` bounding both `|xₙ|` and `|yₙ|`) and multiply. Regular because each factor is `≤ K` and
    the `2K` reindexing cancels it: `2K·(1/(2K(m+1)) + 1/(2K(n+1))) = 1/(m+1) + 1/(n+1)`. -/
def Rmul (x y : Real) : Real where
  seq := fun n => mul (x.seq (Ridx x y n)) (y.seq (Ridx x y n))
  reg := by
    intro m n
    have bxK : ∀ k, Qle (Qabs (x.seq k)) ⟨RmulK x y, 1⟩ := fun k =>
      Qle_trans Nat.one_pos (canon_bound x k)
        (by simp only [Qle, RmulK]; push_cast; omega)
    have byK : ∀ k, Qle (Qabs (y.seq k)) ⟨RmulK x y, 1⟩ := fun k =>
      Qle_trans Nat.one_pos (canon_bound y k)
        (by simp only [Qle, RmulK]; push_cast; omega)
    have hdiff := Qabs_mul_diff (xa := x.seq (Ridx x y m)) (ya := y.seq (Ridx x y m))
      (xb := x.seq (Ridx x y n)) (yb := y.seq (Ridx x y n))
      (x.den_pos _) (y.den_pos _) (x.den_pos _) (y.den_pos _)
    have t1 := Qmul_le_mul (a := Qabs (x.seq (Ridx x y m))) (b := ⟨RmulK x y, 1⟩)
      (c := Qabs (Qsub (y.seq (Ridx x y m)) (y.seq (Ridx x y n))))
      (d := add (Qbound (Ridx x y m)) (Qbound (Ridx x y n)))
      (Qabs_den_pos (x.den_pos _)) Nat.one_pos
      (Qabs_den_pos (Qsub_den_pos (y.den_pos _) (y.den_pos _)))
      (Qabs_num_nonneg _) (Qabs_num_nonneg _) (bxK _) (y.reg _ _)
    have t2 := Qmul_le_mul (a := Qabs (y.seq (Ridx x y n))) (b := ⟨RmulK x y, 1⟩)
      (c := Qabs (Qsub (x.seq (Ridx x y m)) (x.seq (Ridx x y n))))
      (d := add (Qbound (Ridx x y m)) (Qbound (Ridx x y n)))
      (Qabs_den_pos (y.den_pos _)) Nat.one_pos
      (Qabs_den_pos (Qsub_den_pos (x.den_pos _) (x.den_pos _)))
      (Qabs_num_nonneg _) (Qabs_num_nonneg _) (byK _) (x.reg _ _)
    have hsum := Qadd_le_add t1 t2
    have hbid : Qle (add (mul ⟨RmulK x y, 1⟩ (add (Qbound (Ridx x y m)) (Qbound (Ridx x y n))))
                         (mul ⟨RmulK x y, 1⟩ (add (Qbound (Ridx x y m)) (Qbound (Ridx x y n)))))
                    (add (Qbound m) (Qbound n)) := by
      apply Qeq_le
      simp only [Qeq, add, mul, Qbound]
      rw [Ridx_succ x y m, Ridx_succ x y n]
      push_cast
      ring_uor
    refine Qle_trans ?_ hdiff (Qle_trans ?_ hsum hbid)
    · exact add_den_pos
        (Qmul_den_pos (Qabs_den_pos (x.den_pos _))
          (Qabs_den_pos (Qsub_den_pos (y.den_pos _) (y.den_pos _))))
        (Qmul_den_pos (Qabs_den_pos (y.den_pos _))
          (Qabs_den_pos (Qsub_den_pos (x.den_pos _) (x.den_pos _))))
    · exact add_den_pos
        (Qmul_den_pos Nat.one_pos (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _)))
        (Qmul_den_pos Nat.one_pos (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _)))
  den_pos := fun n => Qmul_den_pos (x.den_pos _) (y.den_pos _)

/-- ℝ addition is commutative (up to `≈`): the summands commute coordinatewise in ℚ. -/
theorem Radd_comm (x y : Real) : Req (Radd x y) (Radd y x) :=
  Req_of_seq_Qeq (fun _ => add_comm _ _)

/-- The additive inverse law on ℝ (up to `≈`): `x ⊕ (−x) ≈ 0`. -/
theorem Radd_neg (x : Real) : Req (Radd x (Rneg x)) zero :=
  Req_of_seq_Qeq (fun _ => add_neg _)

/-- ℝ subtraction. -/
def Rsub (x y : Real) : Real := Radd x (Rneg y)

/-- The multiplication bound is symmetric (`max` is). -/
theorem RmulK_comm (x y : Real) : RmulK x y = RmulK y x := by unfold RmulK; omega

/-- The multiplication reindex is symmetric. -/
theorem Ridx_comm (x y : Real) (n : Nat) : Ridx x y n = Ridx y x n := by
  unfold Ridx; rw [RmulK_comm]

/-- ℝ multiplication is commutative (up to `≈`): the factors commute coordinatewise in ℚ (and the
    reindex is symmetric because `K = max(K_x,K_y)` is). -/
theorem Rmul_comm (x y : Real) : Req (Rmul x y) (Rmul y x) := by
  apply Req_of_seq_Qeq
  intro n
  simp only [Rmul]
  rw [Ridx_comm x y n]
  exact mul_comm _ _

-- ===========================================================================
-- v0.5.0 — operation-congruence over `≈` (so the operations are well-defined on the setoid, the
-- prerequisite for the ℂ ring laws). Negation and addition; multiplication-congruence is v0.6.0.
-- ===========================================================================

/-- Negation respects `≈` (it is an isometry, same index — no reindexing). -/
theorem Rneg_congr {x x' : Real} (h : Req x x') : Req (Rneg x) (Rneg x') := by
  intro n
  rw [show Qabs (Qsub ((Rneg x).seq n) ((Rneg x').seq n))
        = Qabs (Qsub (x.seq n) (x'.seq n)) from Qabs_Qsub_neg _ _]
  exact h n

/-- Addition respects `≈`: `x ≈ x', y ≈ y' ⟹ x ⊕ y ≈ x' ⊕ y'`. (Same `2n+1` reindex on both
    sides; the gap splits coordinatewise and `2/(2n+2) + 2/(2n+2) = 2/(n+1)`.) -/
theorem Radd_congr {x x' y y' : Real} (hx : Req x x') (hy : Req y y') :
    Req (Radd x y) (Radd x' y') := by
  intro n
  have hxn := x.den_pos (2 * n + 1); have hxn' := x'.den_pos (2 * n + 1)
  have hyn := y.den_pos (2 * n + 1); have hyn' := y'.den_pos (2 * n + 1)
  have htri := Qabs_sub_add4 (a := x.seq (2 * n + 1)) (b := y.seq (2 * n + 1))
      (c := x'.seq (2 * n + 1)) (d := y'.seq (2 * n + 1)) hxn hyn hxn' hyn'
  have hsum := Qadd_le_add (hx (2 * n + 1)) (hy (2 * n + 1))
  have hbound : Qle (add ⟨2, 2 * n + 1 + 1⟩ ⟨2, 2 * n + 1 + 1⟩) ⟨2, n + 1⟩ := by
    apply Qeq_le; simp only [Qeq, add]; push_cast; ring_uor
  refine Qle_trans ?_ htri (Qle_trans ?_ hsum hbound)
  · exact add_den_pos (Qabs_den_pos (Qsub_den_pos hxn hxn'))
      (Qabs_den_pos (Qsub_den_pos hyn hyn'))
  · exact add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)

/-- Subtraction respects `≈`. -/
theorem Rsub_congr {x x' y y' : Real} (hx : Req x x') (hy : Req y y') :
    Req (Rsub x y) (Rsub x' y') := Radd_congr hx (Rneg_congr hy)

end UOR.Bridge.F1Square.Analysis
