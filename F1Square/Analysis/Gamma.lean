/-
F1 square — **the Γ function via Spouge's approximation** (the archimedean `Γ′/Γ` place).

For the Li-coefficient / explicit-formula archimedean term we need `Γ` on the real line `z > 0`. Spouge's
approximation
  `Γ(z+1) = (z+a)^{z+½} · e^{−(z+a)} · (c₀ + Σ_{k=1}^{⌈a⌉−1} cₖ/(z+k) + ε_a(z))`,
  `c₀ = √(2π)`,  `cₖ = (−1)^{k−1}/(k−1)! · (a−k)^{k−½} · e^{a−k}`,
is built entirely from `exp` and `log` of POSITIVE reals — every power, including `√(2π) = exp(½·log 2π)`
and the half-integer `(a−k)^{k−½} = exp((k−½)·log(a−k))`, is `x^y := exp(y·log x)`. So NO dedicated
square-root primitive is required: the single real-power combinator `RrpowPos` is the whole foundation.

This file builds that combinator and its laws; Spouge's coefficients, the approximant, and the error
estimate follow.

Pure Lean 4, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Analysis.RealPow
import F1Square.Analysis.Log
import F1Square.Analysis.Pi
import F1Square.Analysis.RealDiv
import F1Square.Analysis.ComplexZeta

namespace UOR.Bridge.F1Square.Analysis

/-- **The real power `x^y := exp(y · log x)` for a positive base** `x` (positivity witnessed by `k, hk`).
    The single combinator behind every Spouge power: `√(2π) = RrpowPos 2π _ _ ½`,
    `(z+a)^{z+½} = RrpowPos (z+a) _ _ (z+½)`, `(a−k)^{k−½} = RrpowPos (a−k) _ _ (k−½)`. -/
def RrpowPos (x : Real) (k : Nat) (hk : Qlt (Qbound k) (x.seq k)) (y : Real) : Real :=
  RexpReal (Rmul y (RlogPos x k hk))

/-- **`x^y > 0` for a non-negative exponent** (`exp` of a non-negative real is `≥ 1 > 0`). The
    non-negative-exponent powers in Spouge — `√(2π) = exp(½·log 2π)` and `(z+a)^{z+½}` — are positive. -/
theorem Pos_RrpowPos_of_nonneg (x : Real) (k : Nat) (hk : Qlt (Qbound k) (x.seq k)) (y : Real)
    (hy : Rnonneg (Rmul y (RlogPos x k hk))) : Pos (RrpowPos x k hk y) :=
  Pos_RexpReal hy

/-- **The exponent law `x^{y+y'} = x^y · x^{y'}`**: powers add under multiplication, by `exp(a+b)=exp a·exp b`. -/
theorem RrpowPos_add (x : Real) (k : Nat) (hk : Qlt (Qbound k) (x.seq k)) (y y' : Real) :
    Req (RrpowPos x k hk (Radd y y')) (Rmul (RrpowPos x k hk y) (RrpowPos x k hk y')) := by
  show Req (RexpReal (Rmul (Radd y y') (RlogPos x k hk)))
        (Rmul (RexpReal (Rmul y (RlogPos x k hk))) (RexpReal (Rmul y' (RlogPos x k hk))))
  refine Req_trans (RexpReal_congr (Rmul_distrib_right y y' (RlogPos x k hk))) ?_
  exact RexpReal_add (Rmul y (RlogPos x k hk)) (Rmul y' (RlogPos x k hk))

-- ===========================================================================
-- **The digamma function `ψ = Γ′/Γ`** (the archimedean place) as a genuine constructive real, via the
-- convergent series  `ψ(z) = −γ + Σ_{n=0}^∞ [ 1/(n+1) − 1/(n+z) ]`  (valid for `z > 0`; `ψ(1) = −γ`,
-- `ψ(2) = 1−γ`). The architecture mirrors the committed `Ceta` build: a finite partial sum `D z N`, a
-- telescoping tail bound, a reindex absorbing the constant `B = |z−1|`, then `RReg_of_real_bound → Rlim`.
-- ===========================================================================

/-- **`1/x ≥ 0`**: the reciprocal of a positive real is non-negative (its sequence is `Qinv` of
    positive-numerator rationals, which are non-negative). -/
theorem Rnonneg_Rinv (x : Real) (k : Nat) (hk : Qlt (Qbound k) (x.seq k)) :
    Rnonneg (Rinv x k hk) := by
  intro n
  show Qle (neg (Qbound n)) (Qinv (x.seq (RinvR x k n)))
  have hnn : 0 ≤ (Qinv (x.seq (RinvR x k n))).num := Int.ofNat_nonneg _
  have hd : 0 < (Qinv (x.seq (RinvR x k n))).den := Qinv_den_pos (Rinv_num_pos hk (RinvR_ge n))
  have hbn : (0 : Int) ≤ ((n : Int) + 1) := by omega
  simp only [Qle, neg, Qbound]; push_cast
  have h1 : (0 : Int) ≤ (Qinv (x.seq (RinvR x k n))).num * ((n : Int) + 1) :=
    Int.mul_nonneg hnn hbn
  have h2 : (0 : Int) ≤ ((Qinv (x.seq (RinvR x k n))).den : Int) := by exact_mod_cast Nat.zero_le _
  omega

/-- **Targeted `Rinv` antitone bound**: if a positive rational `q` lower-bounds `w` (`ofQ q ≤ w`,
    `q.num > 0`), then `1/w ≤ 1/q = ofQ (Qinv q)`. Proof: `(1/w)·q ≤ (1/w)·w ≈ 1`, then multiply by
    `ofQ (Qinv q) ≥ 0` and use `q·(1/q) ≈ 1`. -/
theorem Rinv_le_ofQ_Qinv {w : Real} {kw : Nat} (hkw : Qlt (Qbound kw) (w.seq kw))
    {q : Q} (hqn : 0 < q.num) (hqd : 0 < q.den) (hqw : Rle (ofQ q hqd) w) :
    Rle (Rinv w kw hkw) (ofQ (Qinv q) (Qinv_den_pos hqn)) := by
  -- (1/w)·q ≤ (1/w)·w ≈ 1
  have hstep1 : Rle (Rmul (Rinv w kw hkw) (ofQ q hqd)) (Rmul (Rinv w kw hkw) w) :=
    Rmul_le_Rmul_left (Rnonneg_Rinv w kw hkw) hqw
  have hstep2 : Rle (Rmul (Rinv w kw hkw) (ofQ q hqd)) one :=
    Rle_trans hstep1 (Rle_of_Req (Req_trans (Rmul_comm (Rinv w kw hkw) w) (Rmul_Rinv_self hkw)))
  -- multiply both sides on the right by ofQ (Qinv q) ≥ 0
  have hQinvnn : Rnonneg (ofQ (Qinv q) (Qinv_den_pos hqn)) :=
    Rnonneg_ofQ (Qinv_den_pos hqn) (Int.le_of_lt (Qinv_num_pos hqd))
  have hstep3 : Rle (Rmul (Rmul (Rinv w kw hkw) (ofQ q hqd)) (ofQ (Qinv q) (Qinv_den_pos hqn)))
      (Rmul one (ofQ (Qinv q) (Qinv_den_pos hqn))) :=
    Rmul_le_Rmul_right hQinvnn hstep2
  -- left side ≈ (1/w)·(q·(1/q)) ≈ (1/w)·1 ≈ 1/w ; right side ≈ ofQ (Qinv q)
  have hqq : Req (Rmul (ofQ q hqd) (ofQ (Qinv q) (Qinv_den_pos hqn))) one :=
    Req_trans (Rmul_ofQ_ofQ hqd (Qinv_den_pos hqn))
      (Req_of_seq_Qeq (fun _ => Qmul_Qinv hqn))
  have hleft : Req (Rmul (Rmul (Rinv w kw hkw) (ofQ q hqd)) (ofQ (Qinv q) (Qinv_den_pos hqn)))
      (Rinv w kw hkw) :=
    Req_trans (Rmul_assoc (Rinv w kw hkw) (ofQ q hqd) (ofQ (Qinv q) (Qinv_den_pos hqn)))
      (Req_trans (Rmul_congr (Req_refl _) hqq) (Rmul_one (Rinv w kw hkw)))
  have hright : Req (Rmul one (ofQ (Qinv q) (Qinv_den_pos hqn))) (ofQ (Qinv q) (Qinv_den_pos hqn)) :=
    Req_trans (Rmul_comm one (ofQ (Qinv q) (Qinv_den_pos hqn))) (Rmul_one _)
  exact Rle_trans (Rle_of_Req (Req_symm hleft)) (Rle_trans hstep3 (Rle_of_Req hright))

-- ---------------------------------------------------------------------------
-- Two-sided product bound `−A·B ≤ x·y ≤ A·B` (local port of EtaVariation's `Rmul_le_mul_of_abs`/
-- `Rneg_mul_le_of_abs`; EtaVariation is downstream of this file, so the lemmas are reproved here).
-- ---------------------------------------------------------------------------

private theorem digamma_Radd_add_sub_self (D E : Real) :
    Req (Radd (Radd D E) (Rsub D E)) (Radd D D) :=
  Req_trans (Radd_swap D E D (Rneg E))
    (Req_trans (Radd_congr (Req_refl (Radd D D)) (Radd_neg E)) (Radd_zero (Radd D D)))

private theorem digamma_Radd_sub_add_self (D E : Real) :
    Req (Radd (Rsub D E) (Radd D E)) (Radd D D) :=
  Req_trans (Radd_swap D (Rneg E) D E)
    (Req_trans (Radd_congr (Req_refl (Radd D D))
        (Req_trans (Radd_comm (Rneg E) E) (Radd_neg E)))
      (Radd_zero (Radd D D)))

private theorem digamma_expand_minus_plus (A x B y : Real) :
    Req (Rmul (Rsub A x) (Radd B y))
        (Radd (Rsub (Rmul A B) (Rmul x y)) (Rsub (Rmul A y) (Rmul x B))) := by
  refine Req_trans (Rmul_sub_distrib_right A x (Radd B y)) ?_
  refine Req_trans (Rsub_congr (Rmul_distrib A B y) (Rmul_distrib x B y)) ?_
  apply Req_of_seq_Qeq; intro n
  simp only [Rsub, Radd, Rneg, Qeq, add, neg]; push_cast; ring_uor

private theorem digamma_expand_plus_minus (A x B y : Real) :
    Req (Rmul (Radd A x) (Rsub B y))
        (Rsub (Rsub (Rmul A B) (Rmul x y)) (Rsub (Rmul A y) (Rmul x B))) := by
  refine Req_trans (Rmul_distrib_right A x (Rsub B y)) ?_
  refine Req_trans (Radd_congr (Rmul_sub_distrib A B y) (Rmul_sub_distrib x B y)) ?_
  apply Req_of_seq_Qeq; intro n
  simp only [Rsub, Radd, Rneg, Qeq, add, neg]; push_cast; ring_uor

private theorem digamma_expand_minus_minus (A x B y : Real) :
    Req (Rmul (Rsub A x) (Rsub B y))
        (Rsub (Radd (Rmul A B) (Rmul x y)) (Radd (Rmul A y) (Rmul x B))) := by
  refine Req_trans (Rmul_sub_distrib_right A x (Rsub B y)) ?_
  refine Req_trans (Rsub_congr (Rmul_sub_distrib A B y) (Rmul_sub_distrib x B y)) ?_
  apply Req_of_seq_Qeq; intro n
  simp only [Rsub, Radd, Rneg, Qeq, add, neg]; push_cast; ring_uor

private theorem digamma_expand_plus_plus (A x B y : Real) :
    Req (Rmul (Radd A x) (Radd B y))
        (Radd (Radd (Rmul A B) (Rmul x y)) (Radd (Rmul A y) (Rmul x B))) := by
  refine Req_trans (Rmul_distrib_right A x (Radd B y)) ?_
  refine Req_trans (Radd_congr (Rmul_distrib A B y) (Rmul_distrib x B y)) ?_
  apply Req_of_seq_Qeq; intro n
  simp only [Rsub, Radd, Rneg, Qeq, add, neg]; push_cast; ring_uor

private theorem digamma_Rsub_neg_eq_add (B y : Real) :
    Req (Rsub y (Rneg B)) (Radd B y) := by
  apply Req_of_seq_Qeq; intro n
  simp only [Rsub, Radd, Rneg, Qeq, add, neg]; push_cast; ring_uor

private theorem digamma_Rsub_neg_mul_eq (A B x y : Real) :
    Req (Rsub (Rmul x y) (Rneg (Rmul A B))) (Radd (Rmul A B) (Rmul x y)) := by
  apply Req_of_seq_Qeq; intro n
  simp only [Rsub, Radd, Rneg, Qeq, add, neg]; push_cast; ring_uor

/-- **Two-sided product, upper**: `−A≤x≤A, −B≤y≤B ⟹ x·y ≤ A·B`. -/
theorem digamma_Rmul_le_mul_of_abs {x y A B : Real}
    (hx1 : Rle (Rneg A) x) (hx2 : Rle x A) (hy1 : Rle (Rneg B) y) (hy2 : Rle y B) :
    Rle (Rmul x y) (Rmul A B) := by
  have hAx : Rnonneg (Rsub A x) := Rnonneg_Rsub_of_Rle hx2
  have hBy : Rnonneg (Radd B y) :=
    Rnonneg_congr (digamma_Rsub_neg_eq_add B y) (Rnonneg_Rsub_of_Rle hy1)
  have hAx2 : Rnonneg (Radd A x) :=
    Rnonneg_congr (digamma_Rsub_neg_eq_add A x) (Rnonneg_Rsub_of_Rle hx1)
  have hBy2 : Rnonneg (Rsub B y) := Rnonneg_Rsub_of_Rle hy2
  have hP : Rnonneg (Rmul (Rsub A x) (Radd B y)) := Rnonneg_Rmul hAx hBy
  have hQ : Rnonneg (Rmul (Radd A x) (Rsub B y)) := Rnonneg_Rmul hAx2 hBy2
  have hPQ : Rnonneg (Radd (Rmul (Rsub A x) (Radd B y)) (Rmul (Radd A x) (Rsub B y))) :=
    Rnonneg_Radd hP hQ
  have hsum : Req (Radd (Rmul (Rsub A x) (Radd B y)) (Rmul (Radd A x) (Rsub B y)))
      (Radd (Rsub (Rmul A B) (Rmul x y)) (Rsub (Rmul A B) (Rmul x y))) :=
    Req_trans (Radd_congr (digamma_expand_minus_plus A x B y) (digamma_expand_plus_minus A x B y))
      (digamma_Radd_add_sub_self (Rsub (Rmul A B) (Rmul x y)) (Rsub (Rmul A y) (Rmul x B)))
  have hDD : Rnonneg (Radd (Rsub (Rmul A B) (Rmul x y)) (Rsub (Rmul A B) (Rmul x y))) :=
    Rnonneg_congr hsum hPQ
  have hD : Rnonneg (Rsub (Rmul A B) (Rmul x y)) :=
    Rnonneg_congr
      (Req_trans (Rhalf_Radd (Rsub (Rmul A B) (Rmul x y)) (Rsub (Rmul A B) (Rmul x y)))
        (Rhalf_double (Rsub (Rmul A B) (Rmul x y))))
      (Rhalf_nonneg hDD)
  exact Rle_of_Rnonneg_Rsub hD

/-- **Two-sided product, lower**: `−A≤x≤A, −B≤y≤B ⟹ −A·B ≤ x·y`. -/
theorem digamma_Rneg_mul_le_of_abs {x y A B : Real}
    (hx1 : Rle (Rneg A) x) (hx2 : Rle x A) (hy1 : Rle (Rneg B) y) (hy2 : Rle y B) :
    Rle (Rneg (Rmul A B)) (Rmul x y) := by
  have hAx : Rnonneg (Rsub A x) := Rnonneg_Rsub_of_Rle hx2
  have hBy : Rnonneg (Radd B y) :=
    Rnonneg_congr (digamma_Rsub_neg_eq_add B y) (Rnonneg_Rsub_of_Rle hy1)
  have hAx2 : Rnonneg (Radd A x) :=
    Rnonneg_congr (digamma_Rsub_neg_eq_add A x) (Rnonneg_Rsub_of_Rle hx1)
  have hBy2 : Rnonneg (Rsub B y) := Rnonneg_Rsub_of_Rle hy2
  have hP : Rnonneg (Rmul (Rsub A x) (Rsub B y)) := Rnonneg_Rmul hAx hBy2
  have hQ : Rnonneg (Rmul (Radd A x) (Radd B y)) := Rnonneg_Rmul hAx2 hBy
  have hPQ : Rnonneg (Radd (Rmul (Rsub A x) (Rsub B y)) (Rmul (Radd A x) (Radd B y))) :=
    Rnonneg_Radd hP hQ
  have hsum : Req (Radd (Rmul (Rsub A x) (Rsub B y)) (Rmul (Radd A x) (Radd B y)))
      (Radd (Radd (Rmul A B) (Rmul x y)) (Radd (Rmul A B) (Rmul x y))) :=
    Req_trans (Radd_congr (digamma_expand_minus_minus A x B y) (digamma_expand_plus_plus A x B y))
      (digamma_Radd_sub_add_self (Radd (Rmul A B) (Rmul x y)) (Radd (Rmul A y) (Rmul x B)))
  have hDD : Rnonneg (Radd (Radd (Rmul A B) (Rmul x y)) (Radd (Rmul A B) (Rmul x y))) :=
    Rnonneg_congr hsum hPQ
  have hD : Rnonneg (Radd (Rmul A B) (Rmul x y)) :=
    Rnonneg_congr
      (Req_trans (Rhalf_Radd (Radd (Rmul A B) (Rmul x y)) (Radd (Rmul A B) (Rmul x y)))
        (Rhalf_double (Radd (Rmul A B) (Rmul x y))))
      (Rhalf_nonneg hDD)
  exact Rle_of_Rnonneg_Rsub (Rnonneg_congr (Req_symm (digamma_Rsub_neg_mul_eq A B x y)) hD)

/-- `n` as a constructive real (local copy of `RofNat`, to avoid the `ComplexPow` dependency). -/
def RnatQ (n : Nat) : Real := ofQ ⟨(n : Int), 1⟩ Nat.one_pos

/-- The shifted argument `z + n` of the `n`-th digamma term. -/
def digammaArg (z : Real) (n : Nat) : Real := Radd z (RnatQ n)

/-- `RnatQ n ≥ 0`. -/
theorem Rnonneg_RnatQ (n : Nat) : Rnonneg (RnatQ n) :=
  Rnonneg_ofQ Nat.one_pos (by show (0 : Int) ≤ (n : Int); exact Int.ofNat_nonneg n)

/-- The rational floor `c` of `z` is also a floor of `z + n`. -/
theorem ofQ_le_digammaArg {z : Real} {c : Q} (hcd : 0 < c.den) (hcz : Rle (ofQ c hcd) z) (n : Nat) :
    Rle (ofQ c hcd) (digammaArg z n) :=
  Rle_trans hcz (Rle_self_Radd_right (Rnonneg_RnatQ n))

/-- The uniform positivity witness index for every shifted argument `z + n`: `3 · c.den`. -/
def digammaArgK (c : Q) : Nat := 3 * c.den

/-- The positivity witness for `z + n`, derived uniformly from the floor `c ≤ z`. -/
theorem digammaArg_witness {z : Real} {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcz : Rle (ofQ c hcd) z) (n : Nat) :
    Qlt (Qbound (digammaArgK c)) ((digammaArg z n).seq (digammaArgK c)) :=
  Rlt_Qbound_of_Rle_ofQ hcn hcd (ofQ_le_digammaArg hcd hcz n)

/-- **Abstract reciprocal-difference identity**: if `a·I ≈ 1` and `Q·P ≈ 1`, then
    `P − I ≈ (a − Q)·(P·I)`. Purely algebraic; the engine of the telescoping digamma term. -/
theorem Rsub_eq_mul_of_inv {a I P Q : Real} (haI : Req (Rmul a I) one) (hQP : Req (Rmul Q P) one) :
    Req (Rsub P I) (Rmul (Rsub a Q) (Rmul P I)) := by
  -- RHS = a·(P·I) − Q·(P·I)
  have hexpand : Req (Rmul (Rsub a Q) (Rmul P I))
      (Rsub (Rmul a (Rmul P I)) (Rmul Q (Rmul P I))) :=
    Rmul_sub_distrib_right a Q (Rmul P I)
  -- a·(P·I) ≈ P·(a·I) ≈ P·1 ≈ P
  have hL : Req (Rmul a (Rmul P I)) P :=
    Req_trans (Rmul_congr (Req_refl a) (Rmul_comm P I))
      (Req_trans (Req_symm (Rmul_assoc a I P))
        (Req_trans (Rmul_congr haI (Req_refl P)) (Req_trans (Rmul_comm one P) (Rmul_one P))))
  -- Q·(P·I) ≈ (Q·P)·I ≈ 1·I ≈ I
  have hR : Req (Rmul Q (Rmul P I)) I :=
    Req_trans (Req_symm (Rmul_assoc Q P I))
      (Req_trans (Rmul_congr hQP (Req_refl I)) (Req_trans (Rmul_comm one I) (Rmul_one I)))
  exact Req_symm (Req_trans hexpand (Rsub_congr hL hR))

/-- **The reciprocal-difference identity** `1/m − 1/a ≈ (a − m)·(1/m)·(1/a)` for a positive real `a`
    (witness `ka`) and positive `m`. The analogue of `Qinv_sub_eq`, the telescoping engine. -/
theorem Rinv_ofQ_sub_eq {a : Real} {ka : Nat} (hka : Qlt (Qbound ka) (a.seq ka)) {m : Nat} (hm : 0 < m) :
    Req (Rsub (ofQ ⟨1, m⟩ hm) (Rinv a ka hka))
      (Rmul (Rsub a (ofQ ⟨(m : Int), 1⟩ Nat.one_pos))
        (Rmul (ofQ ⟨1, m⟩ hm) (Rinv a ka hka))) := by
  have hQPq : ∀ _ : Nat, Qeq (mul (⟨(m : Int), 1⟩ : Q) (⟨1, m⟩ : Q)) (⟨1, 1⟩ : Q) := by
    intro _; simp only [Qeq, mul]; push_cast; ring_uor
  have hQP : Req (Rmul (ofQ (⟨(m : Int), 1⟩ : Q) Nat.one_pos) (ofQ (⟨1, m⟩ : Q) hm)) one :=
    Req_trans (Rmul_ofQ_ofQ Nat.one_pos hm) (Req_of_seq_Qeq hQPq)
  exact Rsub_eq_mul_of_inv (Rmul_Rinv_self hka) hQP

/-- **The `n`-th digamma term** `t_n(z) = 1/(n+1) − 1/(n+z)` (a genuine constructive real). -/
def digammaTerm (z : Real) {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den) (hcz : Rle (ofQ c hcd) z)
    (n : Nat) : Real :=
  Rsub (ofQ ⟨1, n + 1⟩ (Nat.succ_pos n))
    (Rinv (digammaArg z n) (digammaArgK c) (digammaArg_witness hcn hcd hcz n))

/-- `z ≥ 0` (from the positive rational floor `c ≤ z`). -/
theorem Rnonneg_of_ofQ_le {z : Real} {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcz : Rle (ofQ c hcd) z) : Rnonneg z :=
  Rnonneg_of_Pos (Pos_of_Rle_ofQ hcn hcd hcz)

/-- `n + (−(n+1)) ≈ −1` as constructive reals (the constant part of the term shift). -/
theorem digamma_const_shift (n : Nat) :
    Req (Radd (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos)
        (Rneg (ofQ (⟨((n : Int) + 1), 1⟩ : Q) Nat.one_pos))) (Rneg one) := by
  apply Req_of_seq_Qeq; intro k
  show Qeq (add (⟨(n : Int), 1⟩ : Q) (neg (⟨((n : Int) + 1), 1⟩ : Q))) (neg (⟨1, 1⟩ : Q))
  simp only [Qeq, add, neg]; push_cast; ring_uor

/-- `(z + n) − (n+1) ≈ z − 1` as constructive reals. -/
theorem digammaArg_sub_succ_eq (z : Real) (n : Nat) :
    Req (Rsub (digammaArg z n) (ofQ ⟨((n : Int) + 1), 1⟩ Nat.one_pos)) (Rsub z one) := by
  -- (z + n) − (n+1) ≈ z + (n − (n+1)) ≈ z + (−1) ≈ z − 1
  have hassoc : Req (Rsub (digammaArg z n) (ofQ (⟨((n : Int) + 1), 1⟩ : Q) Nat.one_pos))
      (Radd z (Radd (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos)
        (Rneg (ofQ (⟨((n : Int) + 1), 1⟩ : Q) Nat.one_pos)))) :=
    Radd_assoc z (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos)
      (Rneg (ofQ (⟨((n : Int) + 1), 1⟩ : Q) Nat.one_pos))
  refine Req_trans hassoc (Radd_congr (Req_refl z) (digamma_const_shift n))

/-- The positive product factor `P_n = 1/(n+1) · 1/(z+n)` of the `n`-th term. -/
def digammaPfac (z : Real) {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den) (hcz : Rle (ofQ c hcd) z)
    (n : Nat) : Real :=
  Rmul (ofQ ⟨1, n + 1⟩ (Nat.succ_pos n))
    (Rinv (digammaArg z n) (digammaArgK c) (digammaArg_witness hcn hcd hcz n))

/-- `0 < (n+1)·n` for `n ≥ 1` (denominator positivity of the per-term bound). -/
theorem digamma_succ_mul_pos {n : Nat} (hn : 1 ≤ n) : 0 < (n + 1) * n :=
  Nat.mul_pos (Nat.succ_pos n) (by omega)

/-- `1/(z+n) ≤ 1/n` for `n ≥ 1` (the reciprocal is below `1/n` since `z+n ≥ n`). -/
theorem digamma_Rinv_le (z : Real) {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den) (hcz : Rle (ofQ c hcd) z)
    {n : Nat} (hn : 1 ≤ n) :
    Rle (Rinv (digammaArg z n) (digammaArgK c) (digammaArg_witness hcn hcd hcz n))
        (ofQ ⟨1, n⟩ (show 0 < n by omega)) := by
  have hnn : 0 < (⟨(n : Int), 1⟩ : Q).num := by show (0 : Int) < (n : Int); exact_mod_cast hn
  -- ofQ⟨n,1⟩ ≤ z + n  (since z ≥ 0)
  have hle : Rle (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) (digammaArg z n) := by
    have hz : Rnonneg z := Rnonneg_of_ofQ_le hcn hcd hcz
    refine Rle_trans (Rle_self_Radd_right hz) ?_
    exact Rle_of_Req (Radd_comm (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) z)
  have hkey := Rinv_le_ofQ_Qinv (digammaArg_witness hcn hcd hcz n) hnn Nat.one_pos hle
  -- Qinv ⟨n,1⟩ = ⟨1,n⟩
  refine Rle_trans hkey (Rle_of_Req (ofQ_congr (Qinv_den_pos hnn) (show 0 < n by omega) ?_))
  show Qeq (Qinv (⟨(n : Int), 1⟩ : Q)) (⟨1, n⟩ : Q)
  simp only [Qinv, Qeq]; push_cast; omega

/-- `0 ≤ P_n` and `P_n ≤ 1/((n+1)·n)`. -/
theorem digammaPfac_bound (z : Real) {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcz : Rle (ofQ c hcd) z) {n : Nat} (hn : 1 ≤ n) :
    Rnonneg (digammaPfac z hcn hcd hcz n)
    ∧ Rle (digammaPfac z hcn hcd hcz n) (ofQ ⟨1, (n + 1) * n⟩ (digamma_succ_mul_pos hn)) := by
  have hfacnn : Rnonneg (ofQ (⟨1, n + 1⟩ : Q) (Nat.succ_pos n)) :=
    Rnonneg_ofQ (Nat.succ_pos n) (show (0 : Int) ≤ 1 by decide)
  have hInvnn : Rnonneg (Rinv (digammaArg z n) (digammaArgK c) (digammaArg_witness hcn hcd hcz n)) :=
    Rnonneg_Rinv _ _ _
  refine ⟨Rnonneg_Rmul hfacnn hInvnn, ?_⟩
  -- P_n = ofQ⟨1,n+1⟩ · Rinv ≤ ofQ⟨1,n+1⟩ · ofQ⟨1,n⟩ ≈ ofQ⟨1,(n+1)*n⟩
  refine Rle_trans (Rmul_le_Rmul_left hfacnn (digamma_Rinv_le z hcn hcd hcz hn)) ?_
  refine Rle_of_Req (Req_trans (Rmul_ofQ_ofQ (Nat.succ_pos n) (show 0 < n by omega)) ?_)
  exact ofQ_congr (Qmul_den_pos (Nat.succ_pos n) (show 0 < n by omega)) (digamma_succ_mul_pos hn)
    (by show Qeq (mul (⟨1, n + 1⟩ : Q) (⟨1, n⟩ : Q)) (⟨1, (n + 1) * n⟩ : Q)
        simp only [Qeq, mul]; push_cast; ring_uor)

/-- **Per-term two-sided bound** (`n ≥ 1`): `−B/((n+1)n) ≤ t_n(z) ≤ B/((n+1)n)`, where `B` is a
    rational enclosing `|z−1|` (`−ofQ B ≤ z−1 ≤ ofQ B`). The telescoping per-term estimate. -/
theorem digammaTerm_abs_le (z : Real) {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcz : Rle (ofQ c hcd) z) {B : Q} (hBd : 0 < B.den)
    (hBlo : Rle (Rneg (ofQ B hBd)) (Rsub z one)) (hBhi : Rle (Rsub z one) (ofQ B hBd))
    {n : Nat} (hn : 1 ≤ n) :
    Rle (Rneg (ofQ (mul B (⟨1, (n + 1) * n⟩ : Q)) (Qmul_den_pos hBd (digamma_succ_mul_pos hn))))
        (digammaTerm z hcn hcd hcz n)
    ∧ Rle (digammaTerm z hcn hcd hcz n)
        (ofQ (mul B (⟨1, (n + 1) * n⟩ : Q)) (Qmul_den_pos hBd (digamma_succ_mul_pos hn))) := by
  -- t_n ≈ (z−1) · P_n
  have hPbound := digammaPfac_bound z hcn hcd hcz hn
  have hPnn := hPbound.1
  have hPhi := hPbound.2
  have hPlo : Rle (Rneg (ofQ (⟨1, (n + 1) * n⟩ : Q) (digamma_succ_mul_pos hn)))
      (digammaPfac z hcn hcd hcz n) := by
    refine Rle_trans ?_ (Rle_zero_of_Rnonneg hPnn)
    -- −ofQ⟨1,(n+1)n⟩ ≤ 0  (since ofQ⟨1,(n+1)n⟩ ≥ 0)
    have h0 : Rle zero (ofQ (⟨1, (n + 1) * n⟩ : Q) (digamma_succ_mul_pos hn)) :=
      Rle_zero_of_Rnonneg (Rnonneg_ofQ (digamma_succ_mul_pos hn) (show (0 : Int) ≤ 1 by decide))
    have hnz : Req (Rneg zero) zero :=
      Req_of_seq_Qeq (fun _ => by simp only [Rneg, zero, ofQ, Qeq, neg]; decide)
    exact Rle_trans (Rle_Rneg h0) (Rle_of_Req hnz)
  -- identity: t_n ≈ (z−1)·P_n
  have hid : Req (digammaTerm z hcn hcd hcz n)
      (Rmul (Rsub z one) (digammaPfac z hcn hcd hcz n)) := by
    have h1 : Req (digammaTerm z hcn hcd hcz n)
        (Rmul (Rsub (digammaArg z n) (ofQ (⟨((n : Int) + 1), 1⟩ : Q) Nat.one_pos))
          (digammaPfac z hcn hcd hcz n)) := by
      show Req (Rsub (ofQ (⟨1, n + 1⟩ : Q) (Nat.succ_pos n))
          (Rinv (digammaArg z n) (digammaArgK c) (digammaArg_witness hcn hcd hcz n)))
        (Rmul (Rsub (digammaArg z n) (ofQ (⟨((n : Int) + 1), 1⟩ : Q) Nat.one_pos))
          (digammaPfac z hcn hcd hcz n))
      have hsub := Rinv_ofQ_sub_eq (digammaArg_witness hcn hcd hcz n) (m := n + 1) (Nat.succ_pos n)
      -- the literal ⟨(n:Int)+1,1⟩ vs ⟨((n+1:Nat)),1⟩ agree
      refine Req_trans ?_ hsub
      exact Req_refl _
    exact Req_trans h1 (Rmul_congr (digammaArg_sub_succ_eq z n) (Req_refl _))
  -- product bounds
  have hBlo' : Rle (Rneg (ofQ B hBd)) (Rsub z one) := hBlo
  have hupper : Rle (Rmul (Rsub z one) (digammaPfac z hcn hcd hcz n))
      (Rmul (ofQ B hBd) (ofQ (⟨1, (n + 1) * n⟩ : Q) (digamma_succ_mul_pos hn))) :=
    digamma_Rmul_le_mul_of_abs hBlo' hBhi hPlo hPhi
  have hlower : Rle (Rneg (Rmul (ofQ B hBd) (ofQ (⟨1, (n + 1) * n⟩ : Q) (digamma_succ_mul_pos hn))))
      (Rmul (Rsub z one) (digammaPfac z hcn hcd hcz n)) :=
    digamma_Rneg_mul_le_of_abs hBlo' hBhi hPlo hPhi
  -- ofQ B · ofQ⟨1,(n+1)n⟩ ≈ ofQ (mul B ⟨1,(n+1)n⟩)
  have hprodeq : Req (Rmul (ofQ B hBd) (ofQ (⟨1, (n + 1) * n⟩ : Q) (digamma_succ_mul_pos hn)))
      (ofQ (mul B (⟨1, (n + 1) * n⟩ : Q)) (Qmul_den_pos hBd (digamma_succ_mul_pos hn))) :=
    Rmul_ofQ_ofQ hBd (digamma_succ_mul_pos hn)
  refine ⟨?_, ?_⟩
  · refine Rle_trans (Rle_Rneg (Rle_of_Req hprodeq)) ?_
    exact Rle_trans hlower (Rle_of_Req (Req_symm hid))
  · exact Rle_trans (Rle_of_Req hid) (Rle_trans hupper (Rle_of_Req hprodeq))

-- ---------------------------------------------------------------------------
-- The partial sum `D z N = Σ_{n<N} t_n(z)` and the telescoping tail bound.
-- ---------------------------------------------------------------------------

/-- `(a + t) − b ≈ (a − b) + t` (local copy of `Rsub_Radd_left`). -/
theorem digamma_Rsub_Radd_left (a t b : Real) : Req (Rsub (Radd a t) b) (Radd (Rsub a b) t) :=
  Req_trans (Radd_assoc a t (Rneg b))
    (Req_trans (Radd_congr (Req_refl a) (Radd_comm t (Rneg b)))
      (Req_symm (Radd_assoc a (Rneg b) t)))

/-- A generic finite partial sum `Σ_{i<d} V i`. -/
def digammaRsum (V : Nat → Real) : Nat → Real
  | 0 => zero
  | (d + 1) => Radd (digammaRsum V d) (V d)

/-- **The digamma partial sum** `D z N = Σ_{n<N} t_n(z)`. -/
def digammaSum (z : Real) {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den) (hcz : Rle (ofQ c hcd) z) :
    Nat → Real
  | 0 => zero
  | (N + 1) => Radd (digammaSum z hcn hcd hcz N) (digammaTerm z hcn hcd hcz N)

/-- **The contiguous difference is a range sum**: `D(N+d) − D(N) ≈ Σ_{i<d} t_{N+i}`. -/
theorem digammaSum_diff_eq (z : Real) {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcz : Rle (ofQ c hcd) z) (N : Nat) :
    ∀ d, Req (Rsub (digammaSum z hcn hcd hcz (N + d)) (digammaSum z hcn hcd hcz N))
        (digammaRsum (fun i => digammaTerm z hcn hcd hcz (N + i)) d)
  | 0 => Radd_neg _
  | (d + 1) =>
      Req_trans (digamma_Rsub_Radd_left (digammaSum z hcn hcd hcz (N + d))
          (digammaTerm z hcn hcd hcz (N + d)) (digammaSum z hcn hcd hcz N))
        (Radd_congr (digammaSum_diff_eq z hcn hcd hcz N d) (Req_refl _))

/-- The telescoping rational tail `B·(1/N − 1/(N+d))`, with positive denominator. The `1 ≤ N`
    requirement is carried at the type for the downstream denominator-positivity proofs. -/
def digammaTailQ (B : Q) (N d : Nat) (_hN : 1 ≤ N) : Q :=
  mul B (Qsub (⟨1, N⟩ : Q) (⟨1, N + d⟩ : Q))

theorem digammaTailQ_den_pos (B : Q) (N d : Nat) (hN : 1 ≤ N) (hBd : 0 < B.den) :
    0 < (digammaTailQ B N d hN).den :=
  Qmul_den_pos hBd (Qsub_den_pos (show 0 < N by omega) (show 0 < N + d by omega))

/-- **The telescoping tail bound** (`1 ≤ N`): `−ofQ(B·(1/N − 1/(N+d))) ≤ Σ_{i<d} t_{N+i} ≤
    ofQ(B·(1/N − 1/(N+d)))`. By induction on `d`: the per-term bound `1/((m+1)m) = 1/m − 1/(m+1)`
    telescopes. -/
theorem digammaTail_two_sided (z : Real) {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcz : Rle (ofQ c hcd) z) {B : Q} (hBd : 0 < B.den)
    (hBlo : Rle (Rneg (ofQ B hBd)) (Rsub z one)) (hBhi : Rle (Rsub z one) (ofQ B hBd))
    {N : Nat} (hN : 1 ≤ N) :
    ∀ d, Rle (Rneg (ofQ (digammaTailQ B N d hN) (digammaTailQ_den_pos B N d hN hBd)))
          (digammaRsum (fun i => digammaTerm z hcn hcd hcz (N + i)) d)
        ∧ Rle (digammaRsum (fun i => digammaTerm z hcn hcd hcz (N + i)) d)
          (ofQ (digammaTailQ B N d hN) (digammaTailQ_den_pos B N d hN hBd))
  | 0 => by
    -- d=0: sum = 0, tail = B·(1/N − 1/N) = 0
    have heq0 : Req (ofQ (digammaTailQ B N 0 hN) (digammaTailQ_den_pos B N 0 hN hBd)) zero := by
      refine ofQ_congr (digammaTailQ_den_pos B N 0 hN hBd) (by decide) ?_
      show Qeq (mul B (Qsub (⟨1, N⟩ : Q) (⟨1, N + 0⟩ : Q))) (⟨0, 1⟩ : Q)
      simp only [Qeq, mul, Qsub, add, neg]; push_cast; ring_uor
    have hz0 : Req (Rneg (ofQ (digammaTailQ B N 0 hN) (digammaTailQ_den_pos B N 0 hN hBd))) zero := by
      refine Req_trans (Rneg_congr heq0) ?_
      exact Req_of_seq_Qeq (fun _ => by simp only [Rneg, zero, ofQ, Qeq, neg]; decide)
    exact ⟨Rle_of_Req hz0, Rle_of_Req (Req_symm heq0)⟩
  | (d + 1) => by
    obtain ⟨hlo, hhi⟩ := digammaTail_two_sided z hcn hcd hcz hBd hBlo hBhi hN d
    have hnN : 1 ≤ N + d := by omega
    obtain ⟨htlo, hthi⟩ := digammaTerm_abs_le z hcn hcd hcz hBd hBlo hBhi hnN
    -- the per-term denominator (N+d+1)*(N+d)
    -- sum (d+1) = sum d + t_{N+d}
    -- upper:  ≤ ofQ(tail d) + ofQ(B·1/((N+d+1)(N+d))) ≈ ofQ(tail (d+1))
    have hkeyU : Req (Radd (ofQ (digammaTailQ B N d hN) (digammaTailQ_den_pos B N d hN hBd))
        (ofQ (mul B (⟨1, (N + d + 1) * (N + d)⟩ : Q)) (Qmul_den_pos hBd (digamma_succ_mul_pos hnN))))
        (ofQ (digammaTailQ B N (d + 1) hN) (digammaTailQ_den_pos B N (d + 1) hN hBd)) := by
      refine Req_trans (Radd_ofQ_ofQ (digammaTailQ_den_pos B N d hN hBd)
        (Qmul_den_pos hBd (digamma_succ_mul_pos hnN))) ?_
      refine ofQ_congr _ (digammaTailQ_den_pos B N (d + 1) hN hBd) ?_
      show Qeq (add (mul B (Qsub (⟨1, N⟩ : Q) (⟨1, N + d⟩ : Q)))
          (mul B (⟨1, (N + d + 1) * (N + d)⟩ : Q)))
        (mul B (Qsub (⟨1, N⟩ : Q) (⟨1, N + (d + 1)⟩ : Q)))
      simp only [Qeq, mul, Qsub, add, neg]; push_cast; ring_uor
    have hupper : Rle (digammaRsum (fun i => digammaTerm z hcn hcd hcz (N + i)) (d + 1))
        (ofQ (digammaTailQ B N (d + 1) hN) (digammaTailQ_den_pos B N (d + 1) hN hBd)) := by
      show Rle (Radd (digammaRsum (fun i => digammaTerm z hcn hcd hcz (N + i)) d)
          (digammaTerm z hcn hcd hcz (N + d))) _
      exact Rle_trans (Radd_le_add hhi hthi) (Rle_of_Req hkeyU)
    -- lower:  ≥ −ofQ(tail d) − ofQ(B·1/(..)) ≈ −ofQ(tail (d+1))
    have hkeyL : Req (Rneg (ofQ (digammaTailQ B N (d + 1) hN) (digammaTailQ_den_pos B N (d + 1) hN hBd)))
        (Radd (Rneg (ofQ (digammaTailQ B N d hN) (digammaTailQ_den_pos B N d hN hBd)))
          (Rneg (ofQ (mul B (⟨1, (N + d + 1) * (N + d)⟩ : Q))
            (Qmul_den_pos hBd (digamma_succ_mul_pos hnN))))) :=
      Req_trans (Rneg_congr (Req_symm hkeyU)) (Rneg_Radd _ _)
    have hlower : Rle (Rneg (ofQ (digammaTailQ B N (d + 1) hN) (digammaTailQ_den_pos B N (d + 1) hN hBd)))
        (digammaRsum (fun i => digammaTerm z hcn hcd hcz (N + i)) (d + 1)) := by
      show Rle _ (Radd (digammaRsum (fun i => digammaTerm z hcn hcd hcz (N + i)) d)
          (digammaTerm z hcn hcd hcz (N + d)))
      exact Rle_trans (Rle_of_Req hkeyL) (Radd_le_add hlo htlo)
    exact ⟨hlower, hupper⟩

-- ---------------------------------------------------------------------------
-- The reindex absorbing `B`, the regularity, and the limit `digammaCore` / `Digamma`.
-- ---------------------------------------------------------------------------

/-- The reindex `Midx j = (B.num.toNat + 1)·(j+1)` absorbing the constant `B` (mirror `czetaMidx`). -/
def digammaMidx (B : Q) (j : Nat) : Nat := (B.num.toNat + 1) * (j + 1)

/-- `Midx j ≥ 1`. -/
theorem digammaMidx_ge_one (B : Q) (j : Nat) : 1 ≤ digammaMidx B j := by
  unfold digammaMidx; have : 0 < (B.num.toNat + 1) * (j + 1) := Nat.mul_pos (by omega) (by omega)
  omega

/-- `Midx` is monotone. -/
theorem digammaMidx_mono (B : Q) {j k : Nat} (hjk : j ≤ k) : digammaMidx B j ≤ digammaMidx B k :=
  Nat.mul_le_mul_left _ (by omega)

/-- **The reindexed tail is `≤ 1/(j+1)`**: `B·(1/Midx j − 1/(Midx j + d)) ≤ 1/(j+1)` (for `0 ≤ B.num`). -/
theorem digammaTailQ_Midx_le (B : Q) (hBd : 0 < B.den) (hB0 : 0 ≤ B.num) (j d : Nat) :
    Qle (digammaTailQ B (digammaMidx B j) d (digammaMidx_ge_one B j)) (⟨1, j + 1⟩ : Q) := by
  -- B·(1/N − 1/(N+d)) ≤ B·(1/N) ≤ 1/(j+1)
  have hNpos : 0 < digammaMidx B j := digammaMidx_ge_one B j
  -- first:  tail ≤ B·(1/N)   (subtract a non-negative reciprocal, multiply by B ≥ 0)
  have hsuble : Qle (Qsub (⟨1, digammaMidx B j⟩ : Q) (⟨1, digammaMidx B j + d⟩ : Q))
      (⟨1, digammaMidx B j⟩ : Q) := by
    show (Qsub (⟨1, digammaMidx B j⟩ : Q) (⟨1, digammaMidx B j + d⟩ : Q)).num
        * (((⟨1, digammaMidx B j⟩ : Q).den : Int))
      ≤ (1 : Int) * ((Qsub (⟨1, digammaMidx B j⟩ : Q) (⟨1, digammaMidx B j + d⟩ : Q)).den : Int)
    simp only [Qsub, add, neg]; push_cast
    -- goal:  (1·(N+d) + (-1)·N) · N ≤ 1 · (N · (N+d))
    have hN : (0 : Int) ≤ ((digammaMidx B j : Nat) : Int) := Int.ofNat_nonneg _
    have hsq : (0 : Int) ≤ ((digammaMidx B j : Nat) : Int) * ((digammaMidx B j : Nat) : Int) :=
      Int.mul_nonneg hN hN
    have eL : (1 * (((digammaMidx B j : Nat) : Int) + ((d : Nat) : Int))
          + -1 * ((digammaMidx B j : Nat) : Int)) * ((digammaMidx B j : Nat) : Int)
        = ((d : Nat) : Int) * ((digammaMidx B j : Nat) : Int) := by ring_uor
    have eR : (1 : Int) * (((digammaMidx B j : Nat) : Int)
          * (((digammaMidx B j : Nat) : Int) + ((d : Nat) : Int)))
        = ((digammaMidx B j : Nat) : Int) * ((digammaMidx B j : Nat) : Int)
          + ((d : Nat) : Int) * ((digammaMidx B j : Nat) : Int) := by ring_uor
    rw [eL, eR]; omega
  have hstep1 : Qle (digammaTailQ B (digammaMidx B j) d (digammaMidx_ge_one B j))
      (mul B (⟨1, digammaMidx B j⟩ : Q)) :=
    Qmul_le_mul_left hB0 hsuble
  -- second:  B·(1/N) ≤ 1/(j+1)   since  B.num·(j+1) ≤ N·B.den
  have hstep2 : Qle (mul B (⟨1, digammaMidx B j⟩ : Q)) (⟨1, j + 1⟩ : Q) := by
    show (mul B (⟨1, digammaMidx B j⟩ : Q)).num * (((j + 1 : Nat)) : Int)
      ≤ (1 : Int) * ((mul B (⟨1, digammaMidx B j⟩ : Q)).den : Int)
    simp only [mul]
    push_cast
    -- B.num·1·(j+1) ≤ 1·(B.den·N) ,  N = (B.num.toNat+1)(j+1)
    have hNeq : ((digammaMidx B j : Nat) : Int) = ((B.num.toNat : Int) + 1) * ((j : Int) + 1) := by
      unfold digammaMidx; push_cast; ring_uor
    have hBtoNat : (B.num.toNat : Int) = B.num := Int.toNat_of_nonneg hB0
    have hBden1 : (1 : Int) ≤ (B.den : Int) := by exact_mod_cast hBd
    rw [hNeq, hBtoNat]
    -- goal:  B.num * 1 * (j+1) ≤ 1 * (B.den * ((B.num+1)*(j+1)))
    have hj1 : (0 : Int) ≤ (j : Int) + 1 := by omega
    have hfac : B.num * ((j : Int) + 1) ≤ (B.num + 1) * ((j : Int) + 1) :=
      Int.mul_le_mul_of_nonneg_right (by omega) hj1
    have hBden_mul : (B.num + 1) * ((j : Int) + 1)
        ≤ (B.den : Int) * ((B.num + 1) * ((j : Int) + 1)) := by
      have hpos : (0 : Int) ≤ (B.num + 1) * ((j : Int) + 1) :=
        Int.mul_nonneg (by omega) hj1
      have := Int.mul_le_mul_of_nonneg_right hBden1 hpos
      rw [Int.one_mul] at this; exact this
    have : B.num * ((j : Int) + 1) ≤ (B.den : Int) * ((B.num + 1) * ((j : Int) + 1)) :=
      Int.le_trans hfac hBden_mul
    -- reconcile the explicit `* 1` / `1 *`
    have e1 : B.num * 1 * ((j : Int) + 1) = B.num * ((j : Int) + 1) := by ring_uor
    have e2 : (1 : Int) * ((B.den : Int) * ((B.num + 1) * ((j : Int) + 1)))
        = (B.den : Int) * ((B.num + 1) * ((j : Int) + 1)) := by ring_uor
    rw [e1, e2]; exact this
  exact Qle_trans (Qmul_den_pos hBd hNpos) hstep1 hstep2

/-- **The reindexed digamma partial sums form a regular sequence** (`RReg`), the input to `Rlim`. -/
theorem digammaCore_RReg (z : Real) {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcz : Rle (ofQ c hcd) z) {B : Q} (hBd : 0 < B.den) (hB0 : 0 ≤ B.num)
    (hBlo : Rle (Rneg (ofQ B hBd)) (Rsub z one)) (hBhi : Rle (Rsub z one) (ofQ B hBd)) :
    RReg (fun j => digammaSum z hcn hcd hcz (digammaMidx B j)) := by
  refine RReg_of_real_bound _ (fun j k => add ⟨1, j + 1⟩ ⟨1, k + 1⟩)
    (fun j k => add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)) (fun j k => Qle_refl _) ?_
  intro j k
  rcases Nat.le_total j k with hjk | hkj
  · -- j ≤ k:  D(Midx j) − D(Midx k) = −Σ ;  −Σ ≤ ofQ(tail) ≤ ofQ⟨1,j+1⟩
    have hM : digammaMidx B j ≤ digammaMidx B k := digammaMidx_mono B hjk
    obtain ⟨d, hd⟩ : ∃ d, digammaMidx B k = digammaMidx B j + d := ⟨_, (Nat.add_sub_cancel' hM).symm⟩
    have hdiff := digammaSum_diff_eq z hcn hcd hcz (digammaMidx B j) d
    rw [← hd] at hdiff
    obtain ⟨hlo, _⟩ := digammaTail_two_sided z hcn hcd hcz hBd hBlo hBhi (digammaMidx_ge_one B j) d
    -- Rsub (D(Midx j)) (D(Midx k)) = −(D(Midx k) − D(Midx j))
    have hneg : Req (Rsub (digammaSum z hcn hcd hcz (digammaMidx B j))
        (digammaSum z hcn hcd hcz (digammaMidx B k)))
        (Rneg (digammaRsum (fun i => digammaTerm z hcn hcd hcz (digammaMidx B j + i)) d)) :=
      Req_trans (Req_symm (Rneg_Rsub _ _)) (Rneg_congr hdiff)
    -- −Σ ≤ ofQ(tail)   (from −ofQ(tail) ≤ Σ)
    have hle : Rle (Rneg (digammaRsum (fun i => digammaTerm z hcn hcd hcz (digammaMidx B j + i)) d))
        (ofQ (digammaTailQ B (digammaMidx B j) d (digammaMidx_ge_one B j))
          (digammaTailQ_den_pos B (digammaMidx B j) d (digammaMidx_ge_one B j) hBd)) := by
      refine Rle_trans (Rle_Rneg hlo) (Rle_of_Req ?_)
      exact Req_of_seq_Qeq (fun n => by
        simp only [Rneg, ofQ, Qeq, neg]; push_cast; ring_uor)
    refine Rle_trans (Rle_of_Req hneg) (Rle_trans hle ?_)
    refine Rle_trans (Rle_ofQ_ofQ (digammaTailQ_den_pos B (digammaMidx B j) d _ hBd)
      (Nat.succ_pos _) (digammaTailQ_Midx_le B hBd hB0 j d)) ?_
    exact Rle_ofQ_ofQ (Nat.succ_pos _) _ (Qle_self_add (by show (0 : Int) ≤ 1; decide))
  · -- k ≤ j:  D(Midx j) − D(Midx k) = Σ ;  Σ ≤ ofQ(tail) ≤ ofQ⟨1,k+1⟩
    have hM : digammaMidx B k ≤ digammaMidx B j := digammaMidx_mono B hkj
    obtain ⟨d, hd⟩ : ∃ d, digammaMidx B j = digammaMidx B k + d := ⟨_, (Nat.add_sub_cancel' hM).symm⟩
    have hdiff := digammaSum_diff_eq z hcn hcd hcz (digammaMidx B k) d
    rw [← hd] at hdiff
    obtain ⟨_, hhi⟩ := digammaTail_two_sided z hcn hcd hcz hBd hBlo hBhi (digammaMidx_ge_one B k) d
    refine Rle_trans (Rle_of_Req hdiff) (Rle_trans hhi ?_)
    refine Rle_trans (Rle_ofQ_ofQ (digammaTailQ_den_pos B (digammaMidx B k) d _ hBd)
      (Nat.succ_pos _) (digammaTailQ_Midx_le B hBd hB0 k d)) ?_
    exact Rle_ofQ_ofQ (Nat.succ_pos _) _
      (Qle_add_self (by show (0 : Int) ≤ 1; decide))

/-- **The digamma core** `Σ_{n=0}^∞ [1/(n+1) − 1/(n+z)]`, as a genuine constructive real (`Rlim`). -/
def digammaCore (z : Real) {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcz : Rle (ofQ c hcd) z) {B : Q} (hBd : 0 < B.den) (hB0 : 0 ≤ B.num)
    (hBlo : Rle (Rneg (ofQ B hBd)) (Rsub z one)) (hBhi : Rle (Rsub z one) (ofQ B hBd)) : Real :=
  Rlim (fun j => digammaSum z hcn hcd hcz (digammaMidx B j))
    (digammaCore_RReg z hcn hcd hcz hBd hB0 hBlo hBhi)

/-- **The digamma function `ψ(z) = Γ′/Γ(z)`** (the archimedean place), as a genuine constructive real:
    `ψ(z) = −γ + Σ_{n=0}^∞ [1/(n+1) − 1/(n+z)]`  (`ψ(1) = −γ`, `ψ(2) = 1 − γ`). -/
def Digamma (z : Real) {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcz : Rle (ofQ c hcd) z) {B : Q} (hBd : 0 < B.den) (hB0 : 0 ≤ B.num)
    (hBlo : Rle (Rneg (ofQ B hBd)) (Rsub z one)) (hBhi : Rle (Rsub z one) (ofQ B hBd)) : Real :=
  Radd (Rneg Rgamma_h) (digammaCore z hcn hcd hcz hBd hB0 hBlo hBhi)

-- ===========================================================================
-- **Spouge's Γ approximant** (the computational `Γ` object on the real line `z > 0`).
--
-- Spouge's approximation (Spouge 1994, *SIAM J. Numer. Anal.* **31**(3), 931–944; cf. Pugh's thesis,
-- *An Analysis of the Lanczos Gamma Approximation*, 2004, eqns 2.18–2.19):
--
--   `Γ(z+1) = (z+a)^{z+½} · e^{−(z+a)} · ( c₀ + Σ_{k=1}^{N} cₖ/(z+k) ) + ε_S(a,z)`,
--     `N = ⌈a⌉ − 1`,
--     `c₀ = √(2π) = exp(½·log 2π)`,
--     `cₖ = ((−1)^{k−1}/(k−1)!) · (a−k)^{k−½} · e^{a−k}`     (real; `a−k > 0` for `k ≤ N`),
--
-- with the KNOWN explicit RELATIVE error bound (`a ≥ 3`, `Re z ≥ 0`)
--
--   `|ε_S(a,z)| < √a · (2π)^{−(a+½)} · 1/Re(z+a)`.
--
-- The bound is DOCUMENTED here only; we do **not** state it as a Lean theorem, because a rigorous proof
-- presupposes an independent construction of `Γ` against which to compare. The approximant `SpougeGamma`
-- below is an axiom-clean `def`, built entirely from `exp`/`log`/reciprocal of positive reals — every
-- power is `x^y := RrpowPos x _ _ y = exp(y·log x)`, so NO square-root primitive is needed.
-- ===========================================================================

/-- **`√(2π) = exp(½·log 2π)`** (Spouge's `c₀`), built from `exp`/`log` only (`log 2π = log 2 + log π`). -/
def spougeSqrt2pi : Real :=
  RexpReal (Rmul (ofQ ⟨1, 2⟩ (by decide)) (Radd Rlog2c Rlogπc))

/-- The rational scalar `(−1)^{k−1}/(k−1)!` of Spouge's `cₖ` (numerator `±1` via `(-1)^{k-1} : Int`,
    denominator `(k−1)!`). -/
def spougeSign (k : Nat) : Q := ⟨(-1 : Int) ^ (k - 1), fct (k - 1)⟩

/-- The denominator `(k−1)!` of `spougeSign k` is positive. -/
theorem spougeSign_den_pos (k : Nat) : 0 < (spougeSign k).den := fct_pos (k - 1)

/-- `(a − k).den = a.den` (used for the `ofQ` denominator positivity of `a−k`). -/
theorem Qsub_nat_den_pos {a : Q} (hadp : 0 < a.den) (k : Nat) :
    0 < (Qsub a (⟨(k : Int), 1⟩ : Q)).den := by
  show 0 < a.den * 1; omega

/-- **Spouge's coefficient** `cₖ = ((−1)^{k−1}/(k−1)!) · (a−k)^{k−½} · e^{a−k}` (real), for a rational
    parameter `a` (denominator positive `hadp`) with `a − k > 1` (so the positive base `a−k` of the
    half-integer power `(a−k)^{k−½} = exp((k−½)·log(a−k))` has the immediate positivity witness
    `Qbound 0 = ⟨1,1⟩ < a−k` at index `0`). The exponent `k − ½ = (2k−1)/2` is the rational `⟨2k−1, 2⟩`. -/
@[irreducible] def spougeCoeff (a : Q) (hadp : 0 < a.den) (k : Nat)
    (hak : Qlt (⟨1, 1⟩ : Q) (Qsub a ⟨(k : Int), 1⟩)) : Real :=
  Rmul
    (Rmul
      (ofQ (spougeSign k) (spougeSign_den_pos k))
      (RrpowPos (ofQ (Qsub a ⟨(k : Int), 1⟩) (Qsub_nat_den_pos hadp k)) 0 hak
        (ofQ ⟨2 * (k : Int) - 1, 2⟩ (show 0 < 2 by decide))))
    (RexpReal (ofQ (Qsub a ⟨(k : Int), 1⟩) (Qsub_nat_den_pos hadp k)))

/-- The Spouge bracket `c₀ + Σ_{k=1}^{N} cₖ · 1/(z+k)`, accumulated downward over `k = N, N−1, …, 1`.
    The hypothesis `ha k _ _` supplies the per-`k` positivity `a − k > 1`; each reciprocal `1/(z+k)`
    reuses the `digammaArg`/`digammaArg_witness` enclosure machinery (`z ≥ c > 0 ⟹ z+k > 0`). -/
def spougeBracketAux (z : Real) {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcz : Rle (ofQ c hcd) z) (a : Q) (hadp : 0 < a.den)
    (ha : ∀ (k : Nat), 1 ≤ k → Qlt (⟨1, 1⟩ : Q) (Qsub a ⟨(k : Int), 1⟩)) : Nat → Real
  | 0 => spougeSqrt2pi
  | (k + 1) =>
      Radd (spougeBracketAux z hcn hcd hcz a hadp ha k)
        (Rmul (spougeCoeff a hadp (k + 1) (ha (k + 1) (Nat.le_add_left 1 k)))
          (Rinv (digammaArg z (k + 1)) (digammaArgK c) (digammaArg_witness hcn hcd hcz (k + 1))))

/-- **Spouge's bracket** `c₀ + Σ_{k=1}^{N} cₖ/(z+k)`. -/
def spougeBracket (z : Real) {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcz : Rle (ofQ c hcd) z) (a : Q) (hadp : 0 < a.den)
    (ha : ∀ (k : Nat), 1 ≤ k → Qlt (⟨1, 1⟩ : Q) (Qsub a ⟨(k : Int), 1⟩)) (N : Nat) : Real :=
  spougeBracketAux z hcn hcd hcz a hadp ha N

/-- The base `z + a` of Spouge's leading power, as a constructive real. -/
def spougeBase (z : Real) (a : Q) (hadp : 0 < a.den) : Real := Radd z (ofQ a hadp)

/-- `z + a ≥ c` (the floor `c ≤ z` plus `a > 0`), hence the positivity witness for the base power. -/
theorem ofQ_le_spougeBase {z : Real} {c : Q} (hcd : 0 < c.den) (hcz : Rle (ofQ c hcd) z)
    {a : Q} (hadp : 0 < a.den) (han : 0 ≤ a.num) : Rle (ofQ c hcd) (spougeBase z a hadp) :=
  Rle_trans hcz (Rle_self_Radd_right (Rnonneg_ofQ hadp han))

/-- The positivity witness for `z + a` at index `digammaArgK c`. -/
theorem spougeBase_witness {z : Real} {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcz : Rle (ofQ c hcd) z) {a : Q} (hadp : 0 < a.den) (han : 0 ≤ a.num) :
    Qlt (Qbound (digammaArgK c)) ((spougeBase z a hadp).seq (digammaArgK c)) :=
  Rlt_Qbound_of_Rle_ofQ hcn hcd (ofQ_le_spougeBase hcd hcz hadp han)

/-- **Spouge's Γ approximant** `Γ(z+1) ≈ (z+a)^{z+½} · e^{−(z+a)} · (c₀ + Σ_{k=1}^{N} cₖ/(z+k))`, a
    genuine constructive real for real `z > 0` (enclosed by the rational floor `c`, `0 < c ≤ z`).

    Built from `exp`/`log`/reciprocal of positive reals ONLY:
    * `(z+a)^{z+½} = RrpowPos (z+a) _ _ (z + ½)`  (base `z+a > 0`; exponent `z + ½`),
    * `e^{−(z+a)} = RexpReal (−(z+a))`,
    * the bracket `c₀ + Σ cₖ/(z+k)` from `spougeBracket`.

    `a : Q` is a free rational parameter `≥ 3` (denominator positive `hadp`, numerator non-negative `han`),
    `N = ⌈a⌉ − 1`, and `ha` certifies `a − k > 1` for every `1 ≤ k ≤ N` (needed for `(a−k)^{k−½}`).

    The relative error obeys Spouge's bound `|ε_S(a,z)| < √a · (2π)^{−(a+½)} / Re(z+a)` (`a ≥ 3`,
    `Re z ≥ 0`); see the section header. That bound is documented, not asserted, as a rigorous proof
    presupposes an independent `Γ`. -/
def SpougeGamma (z : Real) {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcz : Rle (ofQ c hcd) z) (a : Q) (hadp : 0 < a.den) (han : 0 ≤ a.num)
    (ha : ∀ (k : Nat), 1 ≤ k → Qlt (⟨1, 1⟩ : Q) (Qsub a ⟨(k : Int), 1⟩)) (N : Nat) : Real :=
  Rmul
    (Rmul
      (RrpowPos (spougeBase z a hadp) (digammaArgK c)
        (spougeBase_witness hcn hcd hcz hadp han)
        (Radd z (ofQ ⟨1, 2⟩ (by decide))))
      (RexpReal (Rneg (spougeBase z a hadp))))
    (spougeBracket z hcn hcd hcz a hadp ha N)

end UOR.Bridge.F1Square.Analysis
