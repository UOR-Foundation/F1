/-
F1 square — **the window-aware reciprocal covariance** (`WeilPrimeShiftRecip.lean`).

The strongest HONEST reciprocal covariance that holds, relating a reflected/reciprocal
evaluation to the DIRECT one, carrying the window as an explicit hypothesis (window-aware,
the pattern of `logPull_reflect_neg`/`logPull_selfDualTest_self_dual`).

HEADLINE (genuinely reciprocal): reflecting a test and reading it at the DIRECT log-point
`log n` returns the DIRECT test's value at the RECIPROCAL rational `1/n`:

    logPull (reflectTest a g) (log n)  ≈  g(1/n)          (on the window  exp(log n) = n ≥ a)

This is the honest place-value form of the reflection covariance `M[g^τ](s)=M[g](−s)`: the
multiplicative inversion `x ↦ 1/x` = the additive negation `u ↦ −u` under `logPull`, evaluated
at the concrete shift `u = log n`, whose negation lands on the reciprocal point `1/n`.

HONESTY NOTE on the suggested target (i). Target shape (i) as literally written —
`logPull (reflectTest a (dilateTest ⟨n,1⟩ g)) 0 ≈ logPull g (Rneg (log n))` (RHS = g(1/n)) —
is FALSE-signed. At the log-origin `u = 0` the reflection is INERT (`1/exp 0 = 1/1 = 1`), so
`logPull_reflect_dilate` at `u = 0` gives `log n − 0 = +log n`, i.e. the value collapses to the
DIRECT place value g(n), NOT the reciprocal g(1/n). The correctly-signed statement is Theorem 2
below; the genuine reciprocal covariance needs the reflection evaluated OFF the origin
(Theorem 1, at `u = log n`), which is why the window hypothesis is load-bearing.
-/
import F1Square.Square.LogReflect
import F1Square.Analysis.RealPow

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

/-- **Window-aware reciprocal place-value covariance (HEADLINE).** Reflecting `g` and reading the
    reflected test at the DIRECT log-point `log n` returns the DIRECT test's value at the RECIPROCAL
    rational `1/n`:  `logPull (reflectTest a g) (log n) ≈ g(1/n)`, on the window `exp(log n) = n ≥ a`
    (carried as the explicit hypotheses `hkx`, `hx` — the reflection generator's clamp is inert there).
    Composes `logPull_reflect_neg` (reflect ↦ negation of the log-argument) at `u = log n` with
    `exp(−log n) = 1/n` (`RexpReal_neg_eq_recip` ∘ `Rexp_logN`), lifted through `g.hfc`. This is the
    honest, genuinely-reciprocal covariance: a reflected DIRECT-point evaluation equals the DIRECT
    RECIPROCAL-point value; the reflection is NOT inert here (unlike the origin). -/
theorem logPull_reflect_at_logN_eq_recip
    (a : Q) (han : 0 < a.num) (had : 0 < a.den) (n : Nat) (hn : 1 ≤ n) (g : L2Test)
    {kx : Nat} (hkx : Qlt (Qbound kx) ((RexpReal (logN n hn)).seq kx))
    (hx : Rle (ofQ a had) (RexpReal (logN n hn))) :
    Req (logPull (reflectTest a han had g) (logN n hn))
        (g.f (ofQ (⟨1, n⟩ : Q) hn)) :=
  Req_trans
    (logPull_reflect_neg a han had g (logN n hn) hkx hx)
    (g.hfc _ _ (RexpReal_neg_eq_recip n hn (Rexp_logN n hn)))

/-- **Origin covariance (the correctly-signed form of target (i)).** At the log-origin `u = 0` the
    reflected DILATION collapses to the DIRECT place value `g(n)` — NOT `g(1/n)` — because the
    reflection is inert at `exp 0 = 1` (`1/1 = 1`): `logPull_reflect_dilate` gives shift `log n − 0
    = +log n`, and `exp(log n) = n` (`Rexp_logN`). Window: `exp 0 = 1 ≥ a` (hypotheses `hk0`, `hx`).
    This is the honest replacement for the wrong-signed suggested target (i); it certifies that the
    reciprocal value canNOT be read at the origin. -/
theorem logPull_reflect_dilate_origin_eq_direct
    (a : Q) (han : 0 < a.num) (had : 0 < a.den) (n : Nat) (hn : 1 ≤ n) (g : L2Test)
    {k0 : Nat} (hk0 : Qlt (Qbound k0) ((RexpReal zero).seq k0))
    (hx : Rle (ofQ a had) (RexpReal zero)) :
    Req (logPull (reflectTest a han had
            (dilateTest (⟨(n : Int), 1⟩ : Q) (by show (0:Int) < (n:Int); omega) Nat.one_pos g)) zero)
        (g.f (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos)) :=
  Req_trans
    (logPull_reflect_dilate a han had n hn g zero hk0 hx)
    (g.hfc _ _
      (Req_trans
        (RexpReal_congr
          (Req_trans (Radd_congr (Req_refl (logN n hn)) Rneg_zero) (Radd_zero (logN n hn))))
        (Rexp_logN n hn)))

end UOR.Bridge.F1Square.Square

