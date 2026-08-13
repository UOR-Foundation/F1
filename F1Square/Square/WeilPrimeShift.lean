/-
F1 square — **the WeilPrimeShift layer** (`WeilPrimeShift.lean`): the finite-place Weil prime
side realized as a fold of GENUINE multiplicative-dilation/shift local terms, proved equal to
the point-value functional `weilPrimePart` — NOT the Mellin-Gram shortcut.

This is the first proof-bearing brick of the operator-valued finite-place Weil/Sonine program.
The prime-power generator acts by the genuine multiplicative dilation `dilateTest` (whose log-line
form is the additive shift `logPull_dilate_shift`, dilation-by-`n` = shift-by-`log n`); the local
term carries the von Mangoldt weight `Λ(n)` on the UNSYMMETRIZED Connes–Consani place value
`f(n) + n⁻¹·f(1/n)` (rational weights — the `n^{-1/2}` symmetric Burnol normalization is a DIFFERENT
printing; the bridge between them is the OPEN next-commit item, not yet built here).

SPINE (this section): the multiplicative dilation/shift REALIZES the point value the Weil term
consumes — `logPull (dilateTest (n+1) φ) 0 ≈ φ(n+1)` (`dilateShift_realize_pos`), the log-line
origin of the dilation-by-`(n+1)` action equals the point value at `n+1` (via
`logPull_dilate_shift` + `Rexp_logN`: `e^{log(n+1)} = n+1`). This ties the built multiplicative
group action to the point evaluations the finite-place side is a sum over.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/
import F1Square.Square.MultShift
import F1Square.Analysis.Weil

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

/-- The rational point `n+1` as a `Q` (denominator `1`). -/
private def qNat (n : Nat) : Q := ⟨((n : Nat) : Int), 1⟩

private theorem qNat_num_pos (n : Nat) : (0 : Int) < (qNat (n + 1)).num := by
  show (0 : Int) < ((n + 1 : Nat) : Int); omega

/-- `0 < (1/(n+1)).num` (`= 0 < 1`); project the numerator first so `decide` sees no free `n`. -/
private theorem qrecip_num_pos (n : Nat) : (0 : Int) < (⟨1, n + 1⟩ : Q).num := by
  show (0 : Int) < 1; decide

private theorem qint_num_pos (m : Nat) (hm : 1 ≤ m) : (0 : Int) < (⟨(m : Int), 1⟩ : Q).num := by
  show (0 : Int) < (m : Int); omega

/-- **The dilation/shift REALIZES the point value at `n+1`.** Reading the log-line origin (`u = 0`)
    of the multiplicative dilation of `φ` by `n+1` returns the point value `φ(n+1)` — the value the
    Weil prime term `weilPrimeTerm` consumes on the positive side. The dilation-by-`(n+1)` becomes
    the additive shift by `log(n+1)` (`logPull_dilate_shift`), and `e^{log(n+1)} = n+1`
    (`Rexp_logN`) collapses the shifted origin to the rational point `n+1`. -/
theorem dilateShift_realize_pos (φ : L2Test) (n : Nat) :
    Req (logPull (dilateTest (qNat (n + 1)) (qNat_num_pos n) Nat.one_pos φ) zero)
        (φ.f (ofQ (qNat (n + 1)) Nat.one_pos)) := by
  have hn : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
  refine Req_trans (logPull_dilate_shift (n + 1) hn φ zero) ?_
  -- goal: Req (logPull φ (Radd (logN (n+1) hn) zero)) (φ.f (ofQ (qNat (n+1)) _))
  -- logPull φ u = φ.f (RexpReal u); push Req through φ.f via hfc
  refine φ.hfc _ _ ?_
  -- RexpReal (log(n+1) + 0) ≈ ofQ (n+1)
  exact Req_trans (RexpReal_congr (Radd_zero (logN (n + 1) hn))) (Rexp_logN (n + 1) hn)

/-- **The dilation at the log-origin realizes the point value at any rational scale.** For any
    positive rational `q`, reading the log-line origin (`u = 0`) of the multiplicative dilation of
    `φ` by `q` returns the point value `φ(q)` — the multiplicative group action `x ↦ q·x` at the
    unit `x = e⁰ = 1` is exactly `φ(q·1) = φ(q)`. This is the general realization used for BOTH the
    positive place value `φ(n+1)` and the reciprocal place value `φ(1/(n+1))`. -/
theorem dilateShift_realize (q : Q) (hqn : 0 < q.num) (hqd : 0 < q.den) (φ : L2Test) :
    Req (logPull (dilateTest q hqn hqd φ) zero) (φ.f (ofQ q hqd)) := by
  -- logPull (dilateTest q φ) 0 = (dilateTest q φ).f (e⁰) = φ.f (ofQ q · e⁰)
  show Req (φ.f (Rmul (ofQ q hqd) (RexpReal zero))) (φ.f (ofQ q hqd))
  refine φ.hfc _ _ ?_
  exact Req_trans (Rmul_congr (Req_refl (ofQ q hqd)) RexpReal_zero) (Rmul_one (ofQ q hqd))

-- ===========================================================================
-- Bundling an L2Test as a point-value WeilTest, and the local shift term.
-- ===========================================================================

/-- Total point-evaluation of an `L2Test` at a rational (junk `0` at the impossible `den = 0`). -/
private def l2pt (φ : L2Test) (q : Q) : Real :=
  if h : 0 < q.den then φ.f (ofQ q h) else zero

private theorem l2pt_pos (φ : L2Test) (q : Q) (h : 0 < q.den) :
    Req (l2pt φ q) (φ.f (ofQ q h)) := by
  show Req (if h : 0 < q.den then φ.f (ofQ q h) else zero) (φ.f (ofQ q h))
  rw [dif_pos h]; exact Req_refl _

/-- **Bundle an L2Test into a point-value WeilTest**: the finite-place side reads the rational point
    values `φ(n)`, `φ(1/n)`; the support cutoff `X` and the vanishing above it are supplied by the
    caller (a compactly-supported `g` — e.g. a constructed autocorrelation). This is the genuine
    point-value test the Weil functional consumes, NOT a Mellin transform. -/
def weilTestOfL2 (φ : L2Test) (X : Nat) (hX : 1 ≤ X)
    (hsh : ∀ n : Nat, X < n → Req (l2pt φ ⟨(n : Int), 1⟩) zero)
    (hsl : ∀ n : Nat, X < n → Req (l2pt φ ⟨1, n⟩) zero) : WeilTest where
  f := l2pt φ
  X := X
  hX := hX
  supp_high := hsh
  supp_low := hsl

/-- **The local dilation/shift prime term**: `Λ(n+1)·(shift_{n+1}φ + (n+1)⁻¹·shift_{1/(n+1)}φ)`,
    where `shift_q φ = logPull (dilateTest q φ) 0` is the multiplicative dilation of `φ` by `q` read
    at the log-origin (`≈ φ(q)` by `dilateShift_realize`). The genuine local generator action with
    the von Mangoldt weight `Λ(n+1)` and the UNSYMMETRIZED `(n+1)⁻¹` reflection weight. -/
def weilPrimeShiftTerm (φ : L2Test) (n : Nat) : Real :=
  Rmul (vonMangoldt (n + 1))
    (Radd (logPull (dilateTest (qNat (n + 1)) (qNat_num_pos n) Nat.one_pos φ) zero)
      (Rmul (ofQ (⟨1, n + 1⟩ : Q) (Nat.succ_pos n))
        (logPull (dilateTest (⟨1, n + 1⟩ : Q) (qrecip_num_pos n) (Nat.succ_pos n) φ) zero)))

/-- **The local shift term REALIZES the Weil prime term.** `weilPrimeShiftTerm φ n` — the
    von-Mangoldt-weighted fold of the two multiplicative dilations — equals `weilPrimeTerm` of the
    bundled point-value test, because each dilation/shift realizes the point value it consumes
    (`dilateShift_realize`). This is a POINT-VALUE identity, not the Mellin-Gram shortcut. -/
theorem weilPrimeShiftTerm_eq (φ : L2Test) (X : Nat) (hX : 1 ≤ X)
    (hsh : ∀ n : Nat, X < n → Req (l2pt φ ⟨(n : Int), 1⟩) zero)
    (hsl : ∀ n : Nat, X < n → Req (l2pt φ ⟨1, n⟩) zero) (n : Nat) :
    Req (weilPrimeShiftTerm φ n) (weilPrimeTerm (weilTestOfL2 φ X hX hsh hsl) n) := by
  refine Rmul_congr (Req_refl _) (Radd_congr ?_ (Rmul_congr (Req_refl _) ?_))
  · exact Req_trans (dilateShift_realize (qNat (n + 1)) (qNat_num_pos n) Nat.one_pos φ)
      (Req_symm (l2pt_pos φ ⟨((n + 1 : Nat) : Int), 1⟩ Nat.one_pos))
  · exact Req_trans (dilateShift_realize (⟨1, n + 1⟩ : Q) (qrecip_num_pos n) (Nat.succ_pos n) φ)
      (Req_symm (l2pt_pos φ ⟨1, n + 1⟩ (Nat.succ_pos n)))

/-- **THE FINITE FOLD OF LOCAL SHIFT TERMS EQUALS `weilPrimePart`** — the finite-place Weil
    functional, realized as a fold of genuine multiplicative-dilation/shift local terms. Point-value
    equality (via `weilPrimeShiftTerm_eq` under `RsumN_congr`), NOT the Mellin-Gram shortcut. -/
theorem weilPrimeShiftFold (φ : L2Test) (X : Nat) (hX : 1 ≤ X)
    (hsh : ∀ n : Nat, X < n → Req (l2pt φ ⟨(n : Int), 1⟩) zero)
    (hsl : ∀ n : Nat, X < n → Req (l2pt φ ⟨1, n⟩) zero) :
    Req (RsumN (weilPrimeShiftTerm φ) X) (weilPrimePart (weilTestOfL2 φ X hX hsh hsl)) :=
  RsumN_congr X (fun i _ => weilPrimeShiftTerm_eq φ X hX hsh hsl i)

/-- **Stabilization past the cutoff**: extending the shift fold beyond `X` does not change it — the
    local terms vanish past the support (via `weilPrimeShiftTerm_eq` + `weilPrimeTerm_past_support`).
    Every test sees only finitely many places. -/
theorem weilPrimeShift_stable (φ : L2Test) (X : Nat) (hX : 1 ≤ X)
    (hsh : ∀ n : Nat, X < n → Req (l2pt φ ⟨(n : Int), 1⟩) zero)
    (hsl : ∀ n : Nat, X < n → Req (l2pt φ ⟨1, n⟩) zero) (d : Nat) :
    Req (RsumN (weilPrimeShiftTerm φ) (X + d)) (RsumN (weilPrimeShiftTerm φ) X) := by
  refine Req_trans
    (RsumN_congr (X + d) (fun i _ => weilPrimeShiftTerm_eq φ X hX hsh hsl i)) ?_
  refine Req_trans (weilPrimePart_stable (weilTestOfL2 φ X hX hsh hsl) d) ?_
  exact Req_symm (weilPrimeShiftFold φ X hX hsh hsl)

/-- **The local dilation actions COMMUTE (pairwise).** Composing the prime-power dilations by `m`
    then `n` equals composing by `n` then `m` (on the log line, both are the same additive shift
    `log m + log n = log n + log m`). HONEST SCOPE: this is PAIRWISE commutation of two dilation
    actions — the algebraic prerequisite for order-independence — NOT itself permutation invariance
    of the finite refinement fold (that is a separate theorem over `RsumN`, not proved here). Proved
    from `logPull_dilate_shift_comp` + `Radd_comm`. -/
theorem dilateShift_comm (m n : Nat) (hm : 1 ≤ m) (hn : 1 ≤ n) (φ : L2Test) (u : Real) :
    Req (logPull (dilateTest (⟨(m : Int), 1⟩ : Q) (qint_num_pos m hm) Nat.one_pos
            (dilateTest (⟨(n : Int), 1⟩ : Q) (qint_num_pos n hn) Nat.one_pos φ)) u)
        (logPull (dilateTest (⟨(n : Int), 1⟩ : Q) (qint_num_pos n hn) Nat.one_pos
            (dilateTest (⟨(m : Int), 1⟩ : Q) (qint_num_pos m hm) Nat.one_pos φ)) u) := by
  refine Req_trans (logPull_dilate_shift_comp m n hm hn φ u) ?_
  refine Req_trans ?_ (Req_symm (logPull_dilate_shift_comp n m hn hm φ u))
  exact φ.hfc _ _ (RexpReal_congr (Radd_congr (Radd_comm (logN n hn) (logN m hm)) (Req_refl u)))

end UOR.Bridge.F1Square.Square
