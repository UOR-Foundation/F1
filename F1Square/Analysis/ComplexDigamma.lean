/-
F1 square — v0.22.0 Track 1, item 1 (the Γ place on the strip): **the complex digamma term**
`ψ(s) = −γ + Σ_{n≥0} [1/(n+1) − 1/(s+n)]` lifted to complex `s` with `Re s ≥ c > 0` (the strip).

This is the archimedean `Γ′/Γ` place generalized off the real line — the piece of item 1 the
real-line `Gamma.lean` construction does not yet provide. Crucially it is built from the complex
reciprocal `Cinv` ALONE (no `Cpow`/`Clog`), so it is entirely free of the `1/16` value-identity
barrier that gates the argument/power axis; each term `1/(s+n)` is a genuine constructive complex
number with `|s+n|² ≥ c² > 0`.

This file (increment 1) builds the term layer: the shifted complex argument `s+n` (`CdigammaArg`),
its modulus-squared floor `|s+n|² ≥ c²` (`ofQ_le_CnormSq_CdigammaArg`) and the resulting positivity
witness (`CdigammaArg_witness`, mirroring `digammaArg_witness`), and the complex term `CdigammaTerm`.
The per-term bounds, the regular partial sums, and the limit object `CDigamma` follow in later
increments through the generic `RReg_of_real_bound` convergence engine.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/
import F1Square.Analysis.ComplexInv
import F1Square.Analysis.Gamma

namespace UOR.Bridge.F1Square.Analysis

/-- **The shifted complex argument** `s + n` of the `n`-th digamma term, as the explicit pair
    `⟨Re s + n, Im s⟩` (definitionally `s + n` up to `≈`; the explicit form keeps `Re`/`Im`
    projections clean). Its real part is exactly `digammaArg (Re s) n`, so the real-line floor
    machinery transfers verbatim. -/
def CdigammaArg (s : Complex) (n : Nat) : Complex := ⟨Radd s.re (RofNat n), s.im⟩

@[simp] theorem CdigammaArg_re (s : Complex) (n : Nat) :
    (CdigammaArg s n).re = Radd s.re (RofNat n) := rfl
@[simp] theorem CdigammaArg_im (s : Complex) (n : Nat) : (CdigammaArg s n).im = s.im := rfl

/-- **The modulus-squared floor** `|s+n|² ≥ c²` (from the real-part floor `Re s ≥ c > 0`):
    `|s+n|² = (Re s + n)² + (Im s)² ≥ (Re s + n)² ≥ c²` since `Re s + n ≥ c ≥ 0` and `(Im s)² ≥ 0`.
    The complex analogue of the floor `c ≤ z` behind `digammaArg_witness`. -/
theorem ofQ_le_CnormSq_CdigammaArg {s : Complex} {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcs : Rle (ofQ c hcd) s.re) (n : Nat) :
    Rle (ofQ (mul c c) (Qmul_den_pos hcd hcd)) (CnormSq (CdigammaArg s n)) := by
  -- σn := Re s + n, with floor ofQ c ≤ σn (reusing the real-line `digammaArg` floor) and σn ≥ 0
  have hfloor : Rle (ofQ c hcd) (Radd s.re (RofNat n)) := ofQ_le_digammaArg hcd hcs n
  have cnn : Rnonneg (ofQ c hcd) := Rnonneg_ofQ hcd (Int.le_of_lt hcn)
  have σnn : Rnonneg (Radd s.re (RofNat n)) := Rnonneg_of_ofQ_le hcn hcd hfloor
  -- c² ≤ c·σn ≤ σn·σn
  have ha : Rle (Rmul (ofQ c hcd) (ofQ c hcd)) (Rmul (ofQ c hcd) (Radd s.re (RofNat n))) :=
    Rmul_le_Rmul_left cnn hfloor
  have hb : Rle (Rmul (ofQ c hcd) (Radd s.re (RofNat n)))
      (Rmul (Radd s.re (RofNat n)) (Radd s.re (RofNat n))) :=
    Rle_trans (Rle_of_Req (Rmul_comm (ofQ c hcd) (Radd s.re (RofNat n))))
      (Rmul_le_Rmul_left σnn hfloor)
  -- c² ≈ ofQ(c·c), and σn² ≤ σn² + (Im s)² = |s+n|²
  have hchain : Rle (ofQ (mul c c) (Qmul_den_pos hcd hcd))
      (Rmul (Radd s.re (RofNat n)) (Radd s.re (RofNat n))) :=
    Rle_trans (Rle_of_Req (Req_symm (Rmul_ofQ_ofQ hcd hcd))) (Rle_trans ha hb)
  exact Rle_trans hchain (Rle_self_Radd_right (Rnonneg_Rmul_self s.im))

/-- The uniform positivity witness index for `|s+n|²`, `3·(c·c).den` (the squared-floor analogue of
    `digammaArgK`). -/
def CdigK (c : Q) : Nat := digammaArgK (mul c c)

/-- **The positivity witness for `|s+n|²`**, derived uniformly from the real-part floor `c ≤ Re s`
    (so `Cinv (s+n)` is well-formed for every `n`). The complex analogue of `digammaArg_witness`. -/
theorem CdigammaArg_witness {s : Complex} {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcs : Rle (ofQ c hcd) s.re) (n : Nat) :
    Qlt (Qbound (CdigK c)) ((CnormSq (CdigammaArg s n)).seq (CdigK c)) :=
  Rlt_Qbound_of_Rle_ofQ (show 0 < (mul c c).num from Int.mul_pos hcn hcn) (Qmul_den_pos hcd hcd)
    (ofQ_le_CnormSq_CdigammaArg hcn hcd hcs n)

/-- **The `n`-th complex digamma term** `1/(n+1) − 1/(s+n)`, a genuine constructive complex number
    for `Re s ≥ c > 0`. The first summand is the real rational `1/(n+1)` (embedded via `ofReal`); the
    second is the complex reciprocal `1/(s+n)` (`Cinv`, well-formed by `CdigammaArg_witness`). Built
    from `Cinv` only — no `Cpow`/`Clog`, hence no `1/16` barrier. -/
def CdigammaTerm (s : Complex) {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcs : Rle (ofQ c hcd) s.re) (n : Nat) : Complex :=
  Cadd (ofReal (ofQ ⟨1, n + 1⟩ (Nat.succ_pos n)))
    (Cneg (Cinv (CdigammaArg s n) (CdigK c) (CdigammaArg_witness hcn hcd hcs n)))

/-- The real part of the `n`-th term: `1/(n+1) − (Re s + n)/|s+n|²`. -/
@[simp] theorem CdigammaTerm_re (s : Complex) {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcs : Rle (ofQ c hcd) s.re) (n : Nat) :
    (CdigammaTerm s hcn hcd hcs n).re =
      Radd (ofQ ⟨1, n + 1⟩ (Nat.succ_pos n))
        (Rneg (Rmul (Radd s.re (RofNat n))
          (Rinv (CnormSq (CdigammaArg s n)) (CdigK c) (CdigammaArg_witness hcn hcd hcs n)))) := rfl

/-- The imaginary part of the `n`-th term: `Im s/|s+n|²` (up to `≈`), here in the raw
    `0 + −(−(Im s·I))` form. -/
@[simp] theorem CdigammaTerm_im (s : Complex) {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcs : Rle (ofQ c hcd) s.re) (n : Nat) :
    (CdigammaTerm s hcn hcd hcs n).im =
      Radd zero (Rneg (Rneg (Rmul s.im
        (Rinv (CnormSq (CdigammaArg s n)) (CdigK c) (CdigammaArg_witness hcn hcd hcs n))))) := rfl

/-- **The complex digamma term is non-vacuous** (instantiation witness at `s = 1`, `c = 1`,
    `n = 0`). Confirms the floor/witness hypotheses are satisfiable. -/
noncomputable def cdigammaTermWitness : Complex :=
  CdigammaTerm Cone (c := ⟨1, 1⟩) (by decide) (by decide)
    (Rle_of_Req (Req_of_seq_Qeq (fun _ => Qeq_refl _))) 0

-- ===========================================================================
-- The factored identity `Cterm = (s−1)·P`, the telescoping engine (complex analogue of
-- `Rsub_eq_mul_of_inv`/`digammaTerm_eq_factored`). It captures the `1/(n+1) − 1/(s+n)`
-- cancellation that makes the term `O(1/n²)` rather than the `O(1/n)` of either summand alone.
-- ===========================================================================

/-- `ℂ`-negation congruence (componentwise `Rneg_congr`). -/
private theorem cdig_Cneg_congr {z z' : Complex} (h : Ceq z z') : Ceq (Cneg z) (Cneg z') :=
  ⟨Rneg_congr h.1, Rneg_congr h.2⟩

/-- `ℂ`-addition congruence (componentwise `Radd_congr`). -/
private theorem cdig_Cadd_congr {z z' w w' : Complex} (hz : Ceq z z') (hw : Ceq w w') :
    Ceq (Cadd z w) (Cadd z' w') :=
  ⟨Radd_congr hz.1 hw.1, Radd_congr hz.2 hw.2⟩

/-- `ℂ`-multiplication congruence (componentwise from the `Cmul` formula). -/
private theorem cdig_Cmul_congr {z z' w w' : Complex} (hz : Ceq z z') (hw : Ceq w w') :
    Ceq (Cmul z w) (Cmul z' w') :=
  ⟨Rsub_congr (Rmul_congr hz.1 hw.1) (Rmul_congr hz.2 hw.2),
   Radd_congr (Rmul_congr hz.1 hw.2) (Rmul_congr hz.2 hw.1)⟩

/-- **Right distributivity over `Cadd`** `(a + b)·X ≈ a·X + b·X` (from `Cmul_comm` + the left
    `Cmul_distrib`). -/
private theorem cdig_Cmul_add_distrib_right (a b X : Complex) :
    Ceq (Cmul (Cadd a b) X) (Cadd (Cmul a X) (Cmul b X)) :=
  Ceq_trans (Cmul_comm (Cadd a b) X)
    (Ceq_trans (Cmul_distrib X a b) (cdig_Cadd_congr (Cmul_comm X a) (Cmul_comm X b)))

/-- **Negation pulls out of the left factor** `(−z)·w ≈ −(z·w)` (componentwise, as in
    `Cneg_Cmul_left`). -/
private theorem cdig_Cmul_neg_left (z w : Complex) : Ceq (Cmul (Cneg z) w) (Cneg (Cmul z w)) := by
  refine ⟨?_, ?_⟩
  · show Req (Rsub (Rmul (Rneg z.re) w.re) (Rmul (Rneg z.im) w.im))
      (Rneg (Rsub (Rmul z.re w.re) (Rmul z.im w.im)))
    refine Req_trans (Rsub_congr (Rmul_neg_left z.re w.re) (Rmul_neg_left z.im w.im)) ?_
    exact Req_symm (Rneg_Radd (Rmul z.re w.re) (Rneg (Rmul z.im w.im)))
  · show Req (Radd (Rmul (Rneg z.re) w.im) (Rmul (Rneg z.im) w.re))
      (Rneg (Radd (Rmul z.re w.im) (Rmul z.im w.re)))
    refine Req_trans (Radd_congr (Rmul_neg_left z.re w.im) (Rmul_neg_left z.im w.re)) ?_
    exact Req_symm (Rneg_Radd (Rmul z.re w.im) (Rmul z.im w.re))

/-- **Abstract reciprocal-difference identity (ℂ)**: if `a·I ≈ 1` and `Q·P ≈ 1`, then
    `P − I ≈ (a − Q)·(P·I)`. The complex analogue of `Rsub_eq_mul_of_inv`; the engine of the
    telescoping complex digamma term. (`P − I` and `a − Q` are written in the `Cadd _ (Cneg _)`
    form `CdigammaTerm` uses.) -/
theorem Cadd_neg_eq_mul_of_inv {a I P Q : Complex} (haI : Ceq (Cmul a I) Cone)
    (hQP : Ceq (Cmul Q P) Cone) :
    Ceq (Cadd P (Cneg I)) (Cmul (Cadd a (Cneg Q)) (Cmul P I)) := by
  -- RHS ≈ a·(P·I) + (−Q)·(P·I)
  have hexpand : Ceq (Cmul (Cadd a (Cneg Q)) (Cmul P I))
      (Cadd (Cmul a (Cmul P I)) (Cmul (Cneg Q) (Cmul P I))) :=
    cdig_Cmul_add_distrib_right a (Cneg Q) (Cmul P I)
  -- a·(P·I) ≈ P·(a·I) ≈ P·1 ≈ P
  have hL : Ceq (Cmul a (Cmul P I)) P :=
    Ceq_trans (cdig_Cmul_congr (Ceq_refl a) (Cmul_comm P I))
      (Ceq_trans (Ceq_symm (Cmul_assoc a I P))
        (Ceq_trans (cdig_Cmul_congr haI (Ceq_refl P))
          (Ceq_trans (Cmul_comm Cone P) (Cmul_one P))))
  -- (−Q)·(P·I) ≈ −(Q·(P·I)) ≈ −((Q·P)·I) ≈ −(1·I) ≈ −I
  have hQPI : Ceq (Cmul Q (Cmul P I)) I :=
    Ceq_trans (Ceq_symm (Cmul_assoc Q P I))
      (Ceq_trans (cdig_Cmul_congr hQP (Ceq_refl I)) (Ceq_trans (Cmul_comm Cone I) (Cmul_one I)))
  have hR : Ceq (Cmul (Cneg Q) (Cmul P I)) (Cneg I) :=
    Ceq_trans (cdig_Cmul_neg_left Q (Cmul P I)) (cdig_Cneg_congr hQPI)
  exact Ceq_symm (Ceq_trans hexpand (cdig_Cadd_congr hL hR))

/-- **The positive product factor** `P_n = 1/(n+1) · 1/(s+n)` of the `n`-th complex term
    (complex analogue of `digammaPfac`). -/
def CdigammaPfac (s : Complex) {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcs : Rle (ofQ c hcd) s.re) (n : Nat) : Complex :=
  Cmul (ofReal (ofQ ⟨1, n + 1⟩ (Nat.succ_pos n)))
    (Cinv (CdigammaArg s n) (CdigK c) (CdigammaArg_witness hcn hcd hcs n))

/-- **`(n+1)·(1/(n+1)) ≈ 1` as complex numbers** — the second reciprocal hypothesis of the factored
    identity. `n+1` and `1/(n+1)` are real embeddings, so this reduces to the rational
    `(n+1)·1/(n+1) = 1`. -/
theorem Cmul_natSucc_inv (n : Nat) :
    Ceq (Cmul ⟨RofNat (n + 1), zero⟩ (ofReal (ofQ ⟨1, n + 1⟩ (Nat.succ_pos n)))) Cone := by
  refine ⟨?_, ?_⟩
  · -- Re: (n+1)·(1/(n+1)) − 0·0 ≈ 1
    show Req (Rsub (Rmul (RofNat (n + 1)) (ofQ ⟨1, n + 1⟩ (Nat.succ_pos n))) (Rmul zero zero)) one
    refine Req_trans (Rsub_congr (Rmul_ofQ_ofQ Nat.one_pos (Nat.succ_pos n)) (Rmul_zero zero)) ?_
    refine Req_trans (Rsub_zero _) ?_
    exact Req_of_seq_Qeq (fun _ => by
      show Qeq (mul (⟨((n + 1 : Nat) : Int), 1⟩ : Q) (⟨1, n + 1⟩ : Q)) (⟨1, 1⟩ : Q)
      simp only [Qeq, mul]; push_cast; ring_uor)
  · -- Im: (n+1)·0 + 0·(1/(n+1)) ≈ 0
    show Req (Radd (Rmul (RofNat (n + 1)) zero) (Rmul zero (ofQ ⟨1, n + 1⟩ (Nat.succ_pos n)))) zero
    refine Req_trans (Radd_congr (Rmul_zero (RofNat (n + 1)))
      (Req_trans (Rmul_comm zero (ofQ ⟨1, n + 1⟩ (Nat.succ_pos n))) (Rmul_zero _))) ?_
    exact Radd_zero zero

/-- **`(s+n) − (n+1) ≈ s − 1` as complex numbers** (componentwise from `digammaArg_sub_succ_eq` on the
    real part and `Im s − 0 ≈ Im s` on the imaginary part). -/
theorem CdigammaArg_sub_succ_eq (s : Complex) (n : Nat) :
    Ceq (Cadd (CdigammaArg s n) (Cneg ⟨RofNat (n + 1), zero⟩)) (Cadd s (Cneg Cone)) := by
  refine ⟨?_, ?_⟩
  · -- (Re s + n) + (−(n+1)) ≈ Re s + (−1)  [from digammaArg_sub_succ_eq, written additively]
    show Req (Radd (Radd s.re (RofNat n)) (Rneg (RofNat (n + 1)))) (Radd s.re (Rneg one))
    have h := digammaArg_sub_succ_eq s.re n
    -- bridge the cast ⟨↑(n+1),1⟩ (RofNat (n+1)) ≈ ⟨(↑n)+1,1⟩ (the literal in digammaArg_sub_succ_eq)
    have hcast : Req (RofNat (n + 1)) (ofQ (⟨((n : Int) + 1), 1⟩ : Q) Nat.one_pos) :=
      Req_of_seq_Qeq (fun _ => by
        show Qeq (⟨((n + 1 : Nat) : Int), 1⟩ : Q) (⟨((n : Int) + 1), 1⟩ : Q)
        simp only [Qeq]; push_cast; ring_uor)
    exact Req_trans (Radd_congr (Req_refl _) (Rneg_congr hcast)) h
  · -- Im s + (−0) ≈ Im s + (−0); Cone.im = 0
    show Req (Radd s.im (Rneg zero)) (Radd s.im (Rneg zero))
    exact Req_refl _

/-- **The factored complex term** `Cterm_n = (s−1)·P_n` (complex analogue of `digammaTerm_eq_factored`).
    Via the abstract identity `Cadd_neg_eq_mul_of_inv` with `a = s+n` (`a·(1/(s+n)) = 1`, `Cmul_Cinv`)
    and `Q = n+1` (`(n+1)·(1/(n+1)) = 1`, `Cmul_natSucc_inv`), then `(s+n)−(n+1) ≈ s−1`
    (`CdigammaArg_sub_succ_eq`). This is the telescoping form that exhibits the `O(1/n²)` decay. -/
theorem CdigammaTerm_factored (s : Complex) {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcs : Rle (ofQ c hcd) s.re) (n : Nat) :
    Ceq (CdigammaTerm s hcn hcd hcs n)
      (Cmul (Cadd s (Cneg Cone)) (CdigammaPfac s hcn hcd hcs n)) := by
  have hid := Cadd_neg_eq_mul_of_inv
    (a := CdigammaArg s n) (I := Cinv (CdigammaArg s n) (CdigK c) (CdigammaArg_witness hcn hcd hcs n))
    (P := ofReal (ofQ ⟨1, n + 1⟩ (Nat.succ_pos n))) (Q := ⟨RofNat (n + 1), zero⟩)
    (Cmul_Cinv (CdigammaArg s n) (CdigK c) (CdigammaArg_witness hcn hcd hcs n))
    (Cmul_natSucc_inv n)
  -- CdigammaTerm = Cadd P (Cneg I), CdigammaPfac = Cmul P I
  refine Ceq_trans hid ?_
  exact cdig_Cmul_congr (CdigammaArg_sub_succ_eq s n) (Ceq_refl _)

-- ===========================================================================
-- Per-term bounds. The factored form `Cterm = (s−1)·P` with `P = F·(1/(s+n))`, `F = 1/(n+1)`,
-- reduces the bound to bounding `P`'s components. The key inverse comparison is `σ_n·(1/N) ≤ 1/σ_n`
-- (from `σ_n² ≤ N = |s+n|²`), giving `P.re = F·σ_n·(1/N) ≤ F·(1/n) = 1/((n+1)n)` and similarly
-- `|P.im| = F·|t|·(1/N) ≤ |t|/((n+1)n)` — the `O(1/n²)` decay made rational.
-- ===========================================================================

/-- **`x·(1/N) ≤ 1/x`** when `0 < x`, `0 < N`, and `x² ≤ N` — the inverse comparison behind the
    per-term bounds (`σ_n/|s+n|² ≤ 1/σ_n`). No cancellation: from `x² ≤ N`, `x ≈ (1/x)·x² ≤ (1/x)·N`,
    then multiplying by `1/N ≥ 0` gives `x·(1/N) ≤ ((1/x)·N)·(1/N) ≈ 1/x`. -/
private theorem Rmul_Rinv_le_Rinv_of_sq_le {x N : Real} {kx : Nat} (hkx : Qlt (Qbound kx) (x.seq kx))
    {kN : Nat} (hkN : Qlt (Qbound kN) (N.seq kN)) (hsq : Rle (Rmul x x) N) :
    Rle (Rmul x (Rinv N kN hkN)) (Rinv x kx hkx) := by
  have hRxnn : Rnonneg (Rinv x kx hkx) := Rnonneg_Rinv x kx hkx
  have hRNnn : Rnonneg (Rinv N kN hkN) := Rnonneg_Rinv N kN hkN
  -- (1/x)·(x·x) ≈ x
  have h3 : Req (Rmul (Rinv x kx hkx) (Rmul x x)) x :=
    Req_trans (Req_symm (Rmul_assoc (Rinv x kx hkx) x x))
      (Req_trans (Rmul_congr (Req_trans (Rmul_comm (Rinv x kx hkx) x) (Rmul_Rinv_self hkx))
          (Req_refl x))
        (Req_trans (Rmul_comm one x) (Rmul_one x)))
  -- x ≤ (1/x)·N
  have hx_le : Rle x (Rmul (Rinv x kx hkx) N) :=
    Rle_trans (Rle_of_Req (Req_symm h3)) (Rmul_le_Rmul_left hRxnn hsq)
  -- x·(1/N) ≤ ((1/x)·N)·(1/N) ≈ 1/x
  have h5 : Req (Rmul (Rmul (Rinv x kx hkx) N) (Rinv N kN hkN)) (Rinv x kx hkx) :=
    Req_trans (Rmul_assoc (Rinv x kx hkx) N (Rinv N kN hkN))
      (Req_trans (Rmul_congr (Req_refl _) (Rmul_Rinv_self hkN)) (Rmul_one _))
  exact Rle_trans (Rmul_le_Rmul_right hRNnn hx_le) (Rle_of_Req h5)

/-- `Re P_n ≈ (1/(n+1))·(σ_n·(1/N))` (the `0·(Im (1/(s+n)))` cross-term vanishes). Here
    `σ_n = Re s + n`, `N = |s+n|²`. -/
theorem CdigammaPfac_re_eq (s : Complex) {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcs : Rle (ofQ c hcd) s.re) (n : Nat) :
    Req (CdigammaPfac s hcn hcd hcs n).re
      (Rmul (ofQ ⟨1, n + 1⟩ (Nat.succ_pos n))
        (Rmul (Radd s.re (RofNat n))
          (Rinv (CnormSq (CdigammaArg s n)) (CdigK c) (CdigammaArg_witness hcn hcd hcs n)))) := by
  have hz : Req (Rmul zero (Rneg (Rmul s.im
      (Rinv (CnormSq (CdigammaArg s n)) (CdigK c) (CdigammaArg_witness hcn hcd hcs n))))) zero :=
    Req_trans (Rmul_comm zero _) (Rmul_zero _)
  exact Req_trans (Rsub_congr (Req_refl _) hz) (Rsub_zero _)

/-- **`Re P_n` two-sided** (`n ≥ 1`): `0 ≤ Re P_n ≤ 1/((n+1)n)`. Upper bound:
    `Re P_n ≈ F·(σ_n·(1/N)) ≤ F·(1/σ_n) ≤ F·(1/n) = 1/((n+1)n)`, via `Rmul_Rinv_le_Rinv_of_sq_le`
    (`σ_n² ≤ N`) and the real-line `digamma_Rinv_le` (`1/σ_n ≤ 1/n`). -/
theorem CdigammaPfac_re_bound (s : Complex) {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcs : Rle (ofQ c hcd) s.re) {n : Nat} (hn : 1 ≤ n) :
    Rnonneg (CdigammaPfac s hcn hcd hcs n).re
    ∧ Rle (CdigammaPfac s hcn hcd hcs n).re (ofQ ⟨1, (n + 1) * n⟩ (digamma_succ_mul_pos hn)) := by
  have heq := CdigammaPfac_re_eq s hcn hcd hcs n
  have hFnn : Rnonneg (ofQ (⟨1, n + 1⟩ : Q) (Nat.succ_pos n)) :=
    Rnonneg_ofQ (Nat.succ_pos n) (show (0 : Int) ≤ 1 by decide)
  have hσnn : Rnonneg (Radd s.re (RofNat n)) :=
    Rnonneg_of_ofQ_le hcn hcd (ofQ_le_digammaArg hcd hcs n)
  have hRinvNnn : Rnonneg (Rinv (CnormSq (CdigammaArg s n)) (CdigK c)
      (CdigammaArg_witness hcn hcd hcs n)) := Rnonneg_Rinv _ _ _
  -- σ_n² ≤ N = σ_n² + (Im s)²
  have hsq : Rle (Rmul (Radd s.re (RofNat n)) (Radd s.re (RofNat n))) (CnormSq (CdigammaArg s n)) :=
    Rle_self_Radd_right (Rnonneg_Rmul_self s.im)
  -- σ_n·(1/N) ≤ 1/σ_n
  have hstep1 : Rle (Rmul (Radd s.re (RofNat n)) (Rinv (CnormSq (CdigammaArg s n)) (CdigK c)
        (CdigammaArg_witness hcn hcd hcs n)))
      (Rinv (Radd s.re (RofNat n)) (digammaArgK c) (digammaArg_witness hcn hcd hcs n)) :=
    Rmul_Rinv_le_Rinv_of_sq_le (digammaArg_witness hcn hcd hcs n)
      (CdigammaArg_witness hcn hcd hcs n) hsq
  -- 1/σ_n ≤ 1/n
  have hstep2 : Rle (Rinv (Radd s.re (RofNat n)) (digammaArgK c) (digammaArg_witness hcn hcd hcs n))
      (ofQ (⟨1, n⟩ : Q) (show 0 < n by omega)) := digamma_Rinv_le s.re hcn hcd hcs hn
  refine ⟨?_, ?_⟩
  · exact Rnonneg_congr (Req_symm heq) (Rnonneg_Rmul hFnn (Rnonneg_Rmul hσnn hRinvNnn))
  · -- F·(σ_n·(1/N)) ≤ F·(1/n) ≈ 1/((n+1)n)
    refine Rle_trans (Rle_of_Req heq) ?_
    refine Rle_trans (Rmul_le_Rmul_left hFnn (Rle_trans hstep1 hstep2)) ?_
    refine Rle_of_Req (Req_trans (Rmul_ofQ_ofQ (Nat.succ_pos n) (show 0 < n by omega)) ?_)
    exact ofQ_congr (Qmul_den_pos (Nat.succ_pos n) (show 0 < n by omega)) (digamma_succ_mul_pos hn)
      (by show Qeq (mul (⟨1, n + 1⟩ : Q) (⟨1, n⟩ : Q)) (⟨1, (n + 1) * n⟩ : Q)
          simp only [Qeq, mul]; push_cast; ring_uor)

/-- **`|s+n|² ≥ n`** (`n ≥ 1`): `N = σ_n² + t² ≥ σ_n² ≥ n` (since `σ_n ≥ n ≥ 1` gives `σ_n² ≥ σ_n·1 ≥
    n`). The rational floor behind `1/N ≤ 1/n`. -/
theorem CnormSq_CdigammaArg_ge (s : Complex) {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcs : Rle (ofQ c hcd) s.re) {n : Nat} (hn : 1 ≤ n) :
    Rle (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) (CnormSq (CdigammaArg s n)) := by
  have hsre : Rnonneg s.re := Rnonneg_of_ofQ_le hcn hcd hcs
  -- n ≤ σ_n
  have hσn_ge_n : Rle (RofNat n) (Radd s.re (RofNat n)) :=
    Rle_trans (Rle_self_Radd_right hsre) (Rle_of_Req (Radd_comm (RofNat n) s.re))
  -- 1 ≤ σ_n  (from 1 ≤ n ≤ σ_n)
  have h1_le_σn : Rle (ofQ (⟨1, 1⟩ : Q) Nat.one_pos) (Radd s.re (RofNat n)) :=
    Rle_trans (Rle_ofQ_ofQ Nat.one_pos Nat.one_pos
      (show Qle (⟨1, 1⟩ : Q) (⟨(n : Int), 1⟩ : Q) by simp only [Qle]; push_cast; omega)) hσn_ge_n
  -- σ_n² ≥ σ_n·1 ≥ n·1 = n
  have ha : Rle (Rmul (RofNat n) (Radd s.re (RofNat n)))
      (Rmul (Radd s.re (RofNat n)) (Radd s.re (RofNat n))) :=
    Rmul_le_Rmul_right (Rnonneg_of_ofQ_le hcn hcd (ofQ_le_digammaArg hcd hcs n)) hσn_ge_n
  have hb : Rle (Rmul (RofNat n) (ofQ (⟨1, 1⟩ : Q) Nat.one_pos))
      (Rmul (RofNat n) (Radd s.re (RofNat n))) :=
    Rmul_le_Rmul_left (Rnonneg_RofNat n) h1_le_σn
  have hnle : Rle (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos)
      (Rmul (Radd s.re (RofNat n)) (Radd s.re (RofNat n))) := by
    refine Rle_trans (Rle_of_Req ?_) (Rle_trans hb ha)
    -- n ≈ n·1
    exact Req_trans (Req_symm (Rmul_one (RofNat n)))
      (Rmul_congr (Req_refl _) (Req_of_seq_Qeq (fun _ => Qeq_refl _)))
  exact Rle_trans hnle (Rle_self_Radd_right (Rnonneg_Rmul_self s.im))

/-- `Im P_n ≈ (1/(n+1))·((−Im s)·(1/N))` (the `0·(Re (1/(s+n)))` cross-term vanishes; the inner
    `−(Im s·(1/N))` is rewritten as `(−Im s)·(1/N)`). -/
theorem CdigammaPfac_im_eq (s : Complex) {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcs : Rle (ofQ c hcd) s.re) (n : Nat) :
    Req (CdigammaPfac s hcn hcd hcs n).im
      (Rmul (ofQ ⟨1, n + 1⟩ (Nat.succ_pos n))
        (Rmul (Rneg s.im)
          (Rinv (CnormSq (CdigammaArg s n)) (CdigK c) (CdigammaArg_witness hcn hcd hcs n)))) := by
  have hz : Req (Rmul zero (Rmul (Radd s.re (RofNat n))
      (Rinv (CnormSq (CdigammaArg s n)) (CdigK c) (CdigammaArg_witness hcn hcd hcs n)))) zero :=
    Req_trans (Rmul_comm zero _) (Rmul_zero _)
  refine Req_trans (Radd_congr (Req_refl _) hz) (Req_trans (Radd_zero _) ?_)
  -- F·(−(Im s·(1/N))) ≈ F·((−Im s)·(1/N))
  exact Rmul_congr (Req_refl _) (Req_symm (Rmul_neg_left s.im
    (Rinv (CnormSq (CdigammaArg s n)) (CdigK c) (CdigammaArg_witness hcn hcd hcs n))))

set_option maxHeartbeats 800000 in
/-- **Abstract two-sided product bound**: `F ≥ 0`, `|u| ≤ A`, `|I| ≤ D` (`I` two-sided about 0) ⟹
    `|F·(u·I)| ≤ F·(A·D)`. Stated on opaque reals so the heavy `Rinv (CnormSq …)` term is substituted
    only at the application site (keeping `whnf` cheap). -/
private theorem cdig_Rmul_two_sided_prod {F A D u I : Real} (hF : Rnonneg F)
    (hulo : Rle (Rneg A) u) (huhi : Rle u A) (hIlo : Rle (Rneg D) I) (hIhi : Rle I D) :
    Rle (Rneg (Rmul F (Rmul A D))) (Rmul F (Rmul u I))
    ∧ Rle (Rmul F (Rmul u I)) (Rmul F (Rmul A D)) := by
  refine ⟨?_, Rmul_le_Rmul_left hF (Rmul_le_mul_of_abs hulo huhi hIlo hIhi)⟩
  refine Rle_trans (Rle_of_Req (Req_symm (Rmul_neg_right F (Rmul A D)))) ?_
  exact Rmul_le_Rmul_left hF (Rneg_mul_le_of_abs hulo huhi hIlo hIhi)

set_option maxHeartbeats 1200000 in
/-- **`Im P_n` two-sided** (`n ≥ 1`, `|Im s| ≤ B`): `−B/((n+1)n) ≤ Im P_n ≤ B/((n+1)n)`. From
    `Im P_n ≈ F·((−Im s)·(1/N))` with `−B ≤ −Im s ≤ B` and `0 ≤ 1/N ≤ 1/n` (`CnormSq_CdigammaArg_ge`),
    via the abstract `cdig_Rmul_two_sided_prod`. -/
theorem CdigammaPfac_im_bound (s : Complex) {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcs : Rle (ofQ c hcd) s.re) {B : Q} (hBd : 0 < B.den)
    (hBlo : Rle (Rneg (ofQ B hBd)) s.im) (hBhi : Rle s.im (ofQ B hBd)) {n : Nat} (hn : 1 ≤ n) :
    Rle (Rneg (ofQ (mul B (⟨1, (n + 1) * n⟩ : Q)) (Qmul_den_pos hBd (digamma_succ_mul_pos hn))))
        (CdigammaPfac s hcn hcd hcs n).im
    ∧ Rle (CdigammaPfac s hcn hcd hcs n).im
        (ofQ (mul B (⟨1, (n + 1) * n⟩ : Q)) (Qmul_den_pos hBd (digamma_succ_mul_pos hn))) := by
  have heq := CdigammaPfac_im_eq s hcn hcd hcs n
  have hFnn : Rnonneg (ofQ (⟨1, n + 1⟩ : Q) (Nat.succ_pos n)) :=
    Rnonneg_ofQ (Nat.succ_pos n) (show (0 : Int) ≤ 1 by decide)
  have hRinvNnn : Rnonneg (Rinv (CnormSq (CdigammaArg s n)) (CdigK c)
      (CdigammaArg_witness hcn hcd hcs n)) := Rnonneg_Rinv _ _ _
  -- two-sided on u = −Im s
  have hulo : Rle (Rneg (ofQ B hBd)) (Rneg s.im) := Rle_Rneg hBhi
  have huhi : Rle (Rneg s.im) (ofQ B hBd) :=
    Rle_trans (Rle_Rneg hBlo) (Rle_of_Req (Rneg_neg (ofQ B hBd)))
  -- 0 ≤ 1/N ≤ 1/n
  have hqn : 0 < (⟨(n : Int), 1⟩ : Q).num := by show (0 : Int) < (n : Int); exact_mod_cast hn
  have hRhi : Rle (Rinv (CnormSq (CdigammaArg s n)) (CdigK c) (CdigammaArg_witness hcn hcd hcs n))
      (ofQ (⟨1, n⟩ : Q) (show 0 < n by omega)) := by
    refine Rle_trans (Rinv_le_ofQ_Qinv (CdigammaArg_witness hcn hcd hcs n) hqn Nat.one_pos
      (CnormSq_CdigammaArg_ge s hcn hcd hcs hn)) ?_
    exact Rle_of_Req (ofQ_congr (Qinv_den_pos hqn) (show 0 < n by omega)
      (by show Qeq (Qinv (⟨(n : Int), 1⟩ : Q)) (⟨1, n⟩ : Q); simp only [Qinv, Qeq]; push_cast; omega))
  have hRlo : Rle (Rneg (ofQ (⟨1, n⟩ : Q) (show 0 < n by omega)))
      (Rinv (CnormSq (CdigammaArg s n)) (CdigK c) (CdigammaArg_witness hcn hcd hcs n)) := by
    have h0 : Rle zero (ofQ (⟨1, n⟩ : Q) (show 0 < n by omega)) :=
      Rle_zero_of_Rnonneg (Rnonneg_ofQ (show 0 < n by omega) (show (0 : Int) ≤ 1 by decide))
    refine Rle_trans ?_ (Rle_zero_of_Rnonneg hRinvNnn)
    refine Rle_trans (Rle_Rneg h0) (Rle_of_Req ?_)
    exact Req_of_seq_Qeq (fun _ => by simp only [Rneg, zero, ofQ, Qeq, neg]; decide)
  -- the rational product bound E = B/((n+1)n)
  have hEeq : Req (Rmul (ofQ (⟨1, n + 1⟩ : Q) (Nat.succ_pos n))
        (Rmul (ofQ B hBd) (ofQ (⟨1, n⟩ : Q) (show 0 < n by omega))))
      (ofQ (mul B (⟨1, (n + 1) * n⟩ : Q)) (Qmul_den_pos hBd (digamma_succ_mul_pos hn))) := by
    refine Req_trans (Rmul_congr (Req_refl _) (Rmul_ofQ_ofQ hBd (show 0 < n by omega))) ?_
    refine Req_trans (Rmul_ofQ_ofQ (Nat.succ_pos n)
      (Qmul_den_pos hBd (show 0 < n by omega))) ?_
    exact ofQ_congr (Qmul_den_pos (Nat.succ_pos n) (Qmul_den_pos hBd (show 0 < n by omega)))
      (Qmul_den_pos hBd (digamma_succ_mul_pos hn))
      (by show Qeq (mul (⟨1, n + 1⟩ : Q) (mul B (⟨1, n⟩ : Q))) (mul B (⟨1, (n + 1) * n⟩ : Q))
          simp only [Qeq, mul]; push_cast; ring_uor)
  have key := cdig_Rmul_two_sided_prod hFnn hulo huhi hRlo hRhi
  refine ⟨?_, ?_⟩
  · -- lower: −E ≈ −(F·(B·1/n)) ≤ F·((−Im s)·(1/N)) ≈ Im P_n
    refine Rle_trans (Rle_of_Req (Req_symm (Rneg_congr hEeq))) (Rle_trans key.1 (Rle_of_Req (Req_symm heq)))
  · -- upper: Im P_n ≈ F·((−Im s)·(1/N)) ≤ F·(B·1/n) ≈ E
    exact Rle_trans (Rle_of_Req heq) (Rle_trans key.2 (Rle_of_Req hEeq))

-- ===========================================================================
-- The full per-term bounds. `Cterm = (s−1)·P`, so each component is a sum/difference of two
-- products of the bounded pieces `(Re s−1), Im s` and `Re P, Im P`. Both components are
-- `≤ K/((n+1)n)` with `K = (B1+B2²) + (B1B2+B2)` (`|Re s−1| ≤ B1`, `|Im s| ≤ B2`).
-- ===========================================================================

/-- Abstract: `Rsub` of two `±`-bounded products is `±`-bounded by the sum of the product bounds. -/
private theorem cdig_Rsub_prod_bound {a b pR pI A A2 PR PI : Real}
    (hAa1 : Rle (Rneg A) a) (hAa2 : Rle a A) (hAb1 : Rle (Rneg A2) b) (hAb2 : Rle b A2)
    (hPr1 : Rle (Rneg PR) pR) (hPr2 : Rle pR PR) (hPi1 : Rle (Rneg PI) pI) (hPi2 : Rle pI PI) :
    Rle (Rneg (Radd (Rmul A PR) (Rmul A2 PI))) (Rsub (Rmul a pR) (Rmul b pI))
    ∧ Rle (Rsub (Rmul a pR) (Rmul b pI)) (Radd (Rmul A PR) (Rmul A2 PI)) := by
  refine ⟨?_, ?_⟩
  · refine Rle_trans (Rle_of_Req (Rneg_Radd (Rmul A PR) (Rmul A2 PI))) ?_
    exact Radd_le_add (Rneg_mul_le_of_abs hAa1 hAa2 hPr1 hPr2) (Rle_Rneg (Rmul_le_mul_of_abs hAb1 hAb2 hPi1 hPi2))
  · exact Radd_le_add (Rmul_le_mul_of_abs hAa1 hAa2 hPr1 hPr2)
      (Rle_trans (Rle_Rneg (Rneg_mul_le_of_abs hAb1 hAb2 hPi1 hPi2)) (Rle_of_Req (Rneg_neg (Rmul A2 PI))))

/-- Abstract: `Radd` of two `±`-bounded products is `±`-bounded by the sum of the product bounds. -/
private theorem cdig_Radd_prod_bound {a b pR pI A A2 PR PI : Real}
    (hAa1 : Rle (Rneg A) a) (hAa2 : Rle a A) (hAb1 : Rle (Rneg A2) b) (hAb2 : Rle b A2)
    (hPr1 : Rle (Rneg PR) pR) (hPr2 : Rle pR PR) (hPi1 : Rle (Rneg PI) pI) (hPi2 : Rle pI PI) :
    Rle (Rneg (Radd (Rmul A PI) (Rmul A2 PR))) (Radd (Rmul a pI) (Rmul b pR))
    ∧ Rle (Radd (Rmul a pI) (Rmul b pR)) (Radd (Rmul A PI) (Rmul A2 PR)) := by
  refine ⟨?_, ?_⟩
  · refine Rle_trans (Rle_of_Req (Rneg_Radd (Rmul A PI) (Rmul A2 PR))) ?_
    exact Radd_le_add (Rneg_mul_le_of_abs hAa1 hAa2 hPi1 hPi2) (Rneg_mul_le_of_abs hAb1 hAb2 hPr1 hPr2)
  · exact Radd_le_add (Rmul_le_mul_of_abs hAa1 hAa2 hPi1 hPi2) (Rmul_le_mul_of_abs hAb1 hAb2 hPr1 hPr2)

/-- The `±` two-sided bound for `Im s` lifted to `(s−1).im = Im s + (−0)`. -/
private theorem cdig_sm1_im_bounds (s : Complex) {B2 : Q} (hB2d : 0 < B2.den)
    (hB2lo : Rle (Rneg (ofQ B2 hB2d)) s.im) (hB2hi : Rle s.im (ofQ B2 hB2d)) :
    Rle (Rneg (ofQ B2 hB2d)) (Radd s.im (Rneg zero)) ∧ Rle (Radd s.im (Rneg zero)) (ofQ B2 hB2d) := by
  have hsm : Req (Radd s.im (Rneg zero)) s.im :=
    Req_trans (Radd_congr (Req_refl _)
      (Req_of_seq_Qeq (fun _ => by simp only [Rneg, zero, ofQ, Qeq, neg]; decide))) (Radd_zero s.im)
  exact ⟨Rle_trans hB2lo (Rle_of_Req (Req_symm hsm)), Rle_trans (Rle_of_Req hsm) hB2hi⟩

/-- The `±` two-sided bound for `Re P_n` (from `0 ≤ Re P_n ≤ 1/((n+1)n)`). -/
private theorem cdig_Pre_bounds (s : Complex) {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcs : Rle (ofQ c hcd) s.re) {n : Nat} (hn : 1 ≤ n) :
    Rle (Rneg (ofQ (⟨1, (n + 1) * n⟩ : Q) (digamma_succ_mul_pos hn))) (CdigammaPfac s hcn hcd hcs n).re
    ∧ Rle (CdigammaPfac s hcn hcd hcs n).re (ofQ (⟨1, (n + 1) * n⟩ : Q) (digamma_succ_mul_pos hn)) := by
  have hb := CdigammaPfac_re_bound s hcn hcd hcs hn
  have hPRnn : Rnonneg (ofQ (⟨1, (n + 1) * n⟩ : Q) (digamma_succ_mul_pos hn)) :=
    Rnonneg_ofQ (digamma_succ_mul_pos hn) (show (0 : Int) ≤ 1 by decide)
  refine ⟨?_, hb.2⟩
  refine Rle_trans ?_ (Rle_zero_of_Rnonneg hb.1)
  refine Rle_trans (Rle_Rneg (Rle_zero_of_Rnonneg hPRnn)) (Rle_of_Req ?_)
  exact Req_of_seq_Qeq (fun _ => by simp only [Rneg, zero, ofQ, Qeq, neg]; decide)

set_option maxHeartbeats 1600000 in
/-- **Per-term Re bound** (`n ≥ 1`, `|Re s−1| ≤ B1`, `|Im s| ≤ B2`): `|Re Cterm_n| ≤ K/((n+1)n)` with
    `K = B1 + B2²`. From `Cterm = (s−1)·P`, `Re Cterm = (Re s−1)·Re P − Im s·Im P`, bounded by
    `B1·(1/((n+1)n)) + B2·(B2/((n+1)n))`. -/
theorem CdigammaTerm_re_bound (s : Complex) {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcs : Rle (ofQ c hcd) s.re) {B1 B2 : Q} (hB1d : 0 < B1.den) (hB2d : 0 < B2.den)
    (hB1lo : Rle (Rneg (ofQ B1 hB1d)) (Rsub s.re one)) (hB1hi : Rle (Rsub s.re one) (ofQ B1 hB1d))
    (hB2lo : Rle (Rneg (ofQ B2 hB2d)) s.im) (hB2hi : Rle s.im (ofQ B2 hB2d)) {n : Nat} (hn : 1 ≤ n) :
    Rle (Rneg (ofQ (mul (add B1 (mul B2 B2)) (⟨1, (n + 1) * n⟩ : Q))
          (Qmul_den_pos (add_den_pos hB1d (Qmul_den_pos hB2d hB2d)) (digamma_succ_mul_pos hn))))
        (CdigammaTerm s hcn hcd hcs n).re
    ∧ Rle (CdigammaTerm s hcn hcd hcs n).re
        (ofQ (mul (add B1 (mul B2 B2)) (⟨1, (n + 1) * n⟩ : Q))
          (Qmul_den_pos (add_den_pos hB1d (Qmul_den_pos hB2d hB2d)) (digamma_succ_mul_pos hn))) := by
  have hPre := cdig_Pre_bounds s hcn hcd hcs hn
  have hPim := CdigammaPfac_im_bound s hcn hcd hcs hB2d hB2lo hB2hi hn
  have hbim := cdig_sm1_im_bounds s hB2d hB2lo hB2hi
  -- abstract product-sum bound (a=(s−1).re, b=(s−1).im, pR=Re P, pI=Im P)
  have hkey := cdig_Rsub_prod_bound hB1lo hB1hi hbim.1 hbim.2 hPre.1 hPre.2 hPim.1 hPim.2
  -- the rational bound: B1·(1/((n+1)n)) + B2·(B2·(1/((n+1)n))) ≈ (B1+B2²)·(1/((n+1)n))
  have hBeq : Req (Radd (Rmul (ofQ B1 hB1d) (ofQ (⟨1, (n + 1) * n⟩ : Q) (digamma_succ_mul_pos hn)))
        (Rmul (ofQ B2 hB2d)
          (ofQ (mul B2 (⟨1, (n + 1) * n⟩ : Q)) (Qmul_den_pos hB2d (digamma_succ_mul_pos hn)))))
      (ofQ (mul (add B1 (mul B2 B2)) (⟨1, (n + 1) * n⟩ : Q))
        (Qmul_den_pos (add_den_pos hB1d (Qmul_den_pos hB2d hB2d)) (digamma_succ_mul_pos hn))) := by
    refine Req_trans (Radd_congr (Rmul_ofQ_ofQ hB1d (digamma_succ_mul_pos hn))
      (Rmul_ofQ_ofQ hB2d (Qmul_den_pos hB2d (digamma_succ_mul_pos hn)))) ?_
    refine Req_trans (Radd_ofQ_ofQ (Qmul_den_pos hB1d (digamma_succ_mul_pos hn))
      (Qmul_den_pos hB2d (Qmul_den_pos hB2d (digamma_succ_mul_pos hn)))) ?_
    exact ofQ_congr _ _ (by
      show Qeq (add (mul B1 (⟨1, (n + 1) * n⟩ : Q)) (mul B2 (mul B2 (⟨1, (n + 1) * n⟩ : Q))))
        (mul (add B1 (mul B2 B2)) (⟨1, (n + 1) * n⟩ : Q))
      simp only [Qeq, mul, add]; push_cast; ring_uor)
  have hfac := (CdigammaTerm_factored s hcn hcd hcs n).1
  refine ⟨?_, ?_⟩
  · refine Rle_trans (Rle_of_Req (Req_symm (Rneg_congr hBeq))) (Rle_trans hkey.1 (Rle_of_Req (Req_symm hfac)))
  · exact Rle_trans (Rle_of_Req hfac) (Rle_trans hkey.2 (Rle_of_Req hBeq))

set_option maxHeartbeats 1600000 in
/-- **Per-term Im bound** (`n ≥ 1`, `|Re s−1| ≤ B1`, `|Im s| ≤ B2`): `|Im Cterm_n| ≤ K/((n+1)n)` with
    `K = B1·B2 + B2`. From `Im Cterm = (Re s−1)·Im P + Im s·Re P`, bounded by
    `B1·(B2/((n+1)n)) + B2·(1/((n+1)n))`. -/
theorem CdigammaTerm_im_bound (s : Complex) {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcs : Rle (ofQ c hcd) s.re) {B1 B2 : Q} (hB1d : 0 < B1.den) (hB2d : 0 < B2.den)
    (hB1lo : Rle (Rneg (ofQ B1 hB1d)) (Rsub s.re one)) (hB1hi : Rle (Rsub s.re one) (ofQ B1 hB1d))
    (hB2lo : Rle (Rneg (ofQ B2 hB2d)) s.im) (hB2hi : Rle s.im (ofQ B2 hB2d)) {n : Nat} (hn : 1 ≤ n) :
    Rle (Rneg (ofQ (mul (add (mul B1 B2) B2) (⟨1, (n + 1) * n⟩ : Q))
          (Qmul_den_pos (add_den_pos (Qmul_den_pos hB1d hB2d) hB2d) (digamma_succ_mul_pos hn))))
        (CdigammaTerm s hcn hcd hcs n).im
    ∧ Rle (CdigammaTerm s hcn hcd hcs n).im
        (ofQ (mul (add (mul B1 B2) B2) (⟨1, (n + 1) * n⟩ : Q))
          (Qmul_den_pos (add_den_pos (Qmul_den_pos hB1d hB2d) hB2d) (digamma_succ_mul_pos hn))) := by
  have hPre := cdig_Pre_bounds s hcn hcd hcs hn
  have hPim := CdigammaPfac_im_bound s hcn hcd hcs hB2d hB2lo hB2hi hn
  have hbim := cdig_sm1_im_bounds s hB2d hB2lo hB2hi
  have hkey := cdig_Radd_prod_bound hB1lo hB1hi hbim.1 hbim.2 hPre.1 hPre.2 hPim.1 hPim.2
  have hBeq : Req (Radd (Rmul (ofQ B1 hB1d)
          (ofQ (mul B2 (⟨1, (n + 1) * n⟩ : Q)) (Qmul_den_pos hB2d (digamma_succ_mul_pos hn))))
        (Rmul (ofQ B2 hB2d) (ofQ (⟨1, (n + 1) * n⟩ : Q) (digamma_succ_mul_pos hn))))
      (ofQ (mul (add (mul B1 B2) B2) (⟨1, (n + 1) * n⟩ : Q))
        (Qmul_den_pos (add_den_pos (Qmul_den_pos hB1d hB2d) hB2d) (digamma_succ_mul_pos hn))) := by
    refine Req_trans (Radd_congr (Rmul_ofQ_ofQ hB1d (Qmul_den_pos hB2d (digamma_succ_mul_pos hn)))
      (Rmul_ofQ_ofQ hB2d (digamma_succ_mul_pos hn))) ?_
    refine Req_trans (Radd_ofQ_ofQ (Qmul_den_pos hB1d (Qmul_den_pos hB2d (digamma_succ_mul_pos hn)))
      (Qmul_den_pos hB2d (digamma_succ_mul_pos hn))) ?_
    exact ofQ_congr _ _ (by
      show Qeq (add (mul B1 (mul B2 (⟨1, (n + 1) * n⟩ : Q))) (mul B2 (⟨1, (n + 1) * n⟩ : Q)))
        (mul (add (mul B1 B2) B2) (⟨1, (n + 1) * n⟩ : Q))
      simp only [Qeq, mul, add]; push_cast; ring_uor)
  have hfac := (CdigammaTerm_factored s hcn hcd hcs n).2
  refine ⟨?_, ?_⟩
  · refine Rle_trans (Rle_of_Req (Req_symm (Rneg_congr hBeq))) (Rle_trans hkey.1 (Rle_of_Req (Req_symm hfac)))
  · exact Rle_trans (Rle_of_Req hfac) (Rle_trans hkey.2 (Rle_of_Req hBeq))

end UOR.Bridge.F1Square.Analysis
