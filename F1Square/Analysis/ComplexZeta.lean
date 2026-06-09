/-
F1 square — the complex Riemann zeta function `ζ(s) = Σ_{n≥1} n⁻ˢ` for `Re s > 1`, built on the
dyadic-geometric tail. The per-term modulus `|n⁻ˢ| = exp(−Re s · log n)` decays geometrically across
dyadic blocks `B_k = [2ᵏ, 2ᵏ⁺¹)`, giving a rational regularity modulus for each (real, imaginary)
component — the honest route for *real* `σ = Re s > 1` (the integer-`s` telescoping of `Zeta.lean`
fails for `1 < σ < 2`). This brick: the per-term component bounds `−exp(Re z) ≤ Re/Im(eᶻ) ≤ exp(Re z)`.
-/
import F1Square.Analysis.RealPow
import F1Square.Analysis.ComplexPow

namespace UOR.Bridge.F1Square.Analysis

/-- `Re(eᶻ) ≤ exp(Re z)` (`Re(eᶻ) = exp(Re z)·cos(Im z)` and `cos ≤ 1`, `exp ≥ 0`). -/
theorem Cexp_re_le (z : Complex) : Rle ((Cexp z).re) (RexpReal z.re) :=
  Rle_trans (Rmul_le_Rmul_left (RexpReal_nonneg z.re) (Rcos_le_one z.im))
    (Rle_of_Req (Rmul_one (RexpReal z.re)))

/-- `−exp(Re z) ≤ Re(eᶻ)` (`cos ≥ −1`). -/
theorem Cexp_re_ge (z : Complex) : Rle (Rneg (RexpReal z.re)) ((Cexp z).re) :=
  Rle_trans (Rle_of_Req (Req_symm (Req_trans (Rmul_neg_right (RexpReal z.re) one)
      (Rneg_congr (Rmul_one (RexpReal z.re))))))
    (Rmul_le_Rmul_left (RexpReal_nonneg z.re) (Rneg_one_le_Rcos z.im))

/-- `Im(eᶻ) ≤ exp(Re z)` (`Im(eᶻ) = exp(Re z)·sin(Im z)` and `sin ≤ 1`). -/
theorem Cexp_im_le (z : Complex) : Rle ((Cexp z).im) (RexpReal z.re) :=
  Rle_trans (Rmul_le_Rmul_left (RexpReal_nonneg z.re) (Rsin_le_one z.im))
    (Rle_of_Req (Rmul_one (RexpReal z.re)))

/-- `−exp(Re z) ≤ Im(eᶻ)` (`sin ≥ −1`). -/
theorem Cexp_im_ge (z : Complex) : Rle (Rneg (RexpReal z.re)) ((Cexp z).im) :=
  Rle_trans (Rle_of_Req (Req_symm (Req_trans (Rmul_neg_right (RexpReal z.re) one)
      (Rneg_congr (Rmul_one (RexpReal z.re))))))
    (Rmul_le_Rmul_left (RexpReal_nonneg z.re) (Rneg_one_le_Rsin z.im))

/-- **The `n`-th term `n⁻ˢ = exp(−s·log n)`** of `ζ(s)`, for `n ≥ 1` (`log 1 = 0`, so `1⁻ˢ = e⁰ = 1`).
    Built on `logN` (the natural-log of `ComplexZeta`/`RealPow`) so the dyadic bounds apply directly. -/
def czetaTerm (s : Complex) (n : Nat) (hn : 1 ≤ n) : Complex :=
  Cexp ⟨Rmul (Rneg s.re) (logN n hn), Rmul (Rneg s.im) (logN n hn)⟩

/-- The term's modulus exponent `−Re s · log n` (`= Re` of the `Cexp` argument). -/
def czetaExpArg (s : Complex) (n : Nat) (hn : 1 ≤ n) : Real := Rmul (Rneg s.re) (logN n hn)

theorem czetaTerm_re_le (s : Complex) (n : Nat) (hn : 1 ≤ n) :
    Rle ((czetaTerm s n hn).re) (RexpReal (czetaExpArg s n hn)) := Cexp_re_le _

theorem czetaTerm_re_ge (s : Complex) (n : Nat) (hn : 1 ≤ n) :
    Rle (Rneg (RexpReal (czetaExpArg s n hn))) ((czetaTerm s n hn).re) := Cexp_re_ge _

theorem czetaTerm_im_le (s : Complex) (n : Nat) (hn : 1 ≤ n) :
    Rle ((czetaTerm s n hn).im) (RexpReal (czetaExpArg s n hn)) := Cexp_im_le _

theorem czetaTerm_im_ge (s : Complex) (n : Nat) (hn : 1 ≤ n) :
    Rle (Rneg (RexpReal (czetaExpArg s n hn))) ((czetaTerm s n hn).im) := Cexp_im_ge _

end UOR.Bridge.F1Square.Analysis
