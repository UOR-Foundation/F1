/-
F1 square — Track 1, item-0 brick: **the complex argument on the FAR sector** (near the positive
imaginary axis) — `argFar(z) = π/2 − arctan(Re z / Im z)` for `Im z > 0` and `|Re z / Im z| < 1/16`.

The companion of `Carg` (`ComplexArg.lean`, the PRINCIPAL sector `arg = arctan(Im/Re)`, valid where
`|Im/Re|` is small, i.e. `z` near the positive REAL axis). As `z` rotates toward the imaginary axis
the ratio `Im/Re → ∞` leaves the `arctan` value-identity radius, so the principal formula degrades.
The classical remedy is the reciprocal reduction `arctan t = π/2 − arctan(1/t)`: near the positive
IMAGINARY axis the reciprocal ratio `Re/Im` IS small, and `argFar z = π/2 − arctan(Re z / Im z)`
carries the argument there. Its tangent is `Im/Re` again — the content of `RarctanR_recip_value`
(`RArctanRecip.lean`), consumed here division-free.

Two properties:
* `CargFar_tan_value` — `(Re/Im)·sin(argFar z) = cos(argFar z)`, i.e. `tan(argFar z) = Im/Re`, the
  defining tangent (immediate from `RarctanR_recip_value` with `s = Re z / Im z`).
* `CargFar_pure_imag` — on the positive imaginary axis (`Re = 0`, `Im > 0`) the argument is `π/2`
  (the ratio numerators vanish, so `arctan = 0` and `argFar = π/2 − 0`). The far-sector anchor,
  mirroring `Carg_ofReal_pos`'s `arg = 0` on the positive real axis.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`. RH-independent (the full-range `arg` substrate toward `log ξ`); crux
fields stay `none`, RH open.
-/
import F1Square.Analysis.RArctanRecip
import F1Square.Analysis.RArctan
import F1Square.Analysis.Inv
import F1Square.Analysis.Complex

namespace UOR.Bridge.F1Square.Analysis

/-- **The complex argument on the far sector** (near the positive imaginary axis):
    `argFar(z) = π/2 − arctan(Re z / Im z)` for `Im z > 0` (witness `k`) and `|Re z / Im z| ≤ ρ < 1`.
    The reciprocal-reduction companion of `Carg`. -/
def CargFar (z : Complex) (k : Nat) (hk : Qlt (Qbound k) (z.im.seq k))
    (ρ : Q) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den) (hρlt : ρ.num.toNat < ρ.den)
    (hb : ∀ n, Qle (Qabs ((Rdiv z.re z.im k hk).seq n)) ρ) : Real :=
  Rsub Rpi_half (RarctanR (Rdiv z.re z.im k hk) ρ hρ0 hρd hρlt hb)

/-- **★ the far-sector tangent value identity** — `(Re z / Im z) · sin(argFar z) = cos(argFar z)`,
    i.e. `tan(argFar z) = Im z / Re z`, the argument's defining tangent. Immediate from the
    reciprocal-arctan reduction `RarctanR_recip_value` at the small ratio `s = Re z / Im z` (the far
    sector demands `|Re/Im| < 1/16`, the value-identity radius — the seven `ρ`-hypotheses). -/
theorem CargFar_tan_value (z : Complex) (k : Nat) (hk : Qlt (Qbound k) (z.im.seq k))
    (ρ : Q) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den) (hρlt : ρ.num.toNat < ρ.den)
    (hb : ∀ n, Qle (Qabs ((Rdiv z.re z.im k hk).seq n)) ρ)
    (hlt16 : (mul ⟨16, 1⟩ ρ).num.toNat < (mul ⟨16, 1⟩ ρ).den)
    (h2ρ : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul ⟨2, 1⟩ ρ)).num)
    (hhalf : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ⟨2, 1⟩ ρ))) (hρ4 : Qle (mul ⟨4, 1⟩ ρ) ⟨1, 1⟩)
    (hρ2 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ρ ρ))) (hρ8 : Qle (mul ⟨2, 1⟩ ρ) ⟨1, 1⟩)
    (hρ1 : Qle ρ ⟨1, 1⟩) :
    Req (Rmul (Rdiv z.re z.im k hk) (Rsin (CargFar z k hk ρ hρ0 hρd hρlt hb)))
        (Rcos (CargFar z k hk ρ hρ0 hρd hρlt hb)) := by
  unfold CargFar
  exact RarctanR_recip_value (Rdiv z.re z.im k hk) ρ hρ0 hρd hρlt hb hlt16 h2ρ hhalf hρ4 hρ2 hρ8 hρ1

/-- **★ the far-sector anchor** — `argFar(⟨0, b⟩) = π/2` for `b > 0`: a point on the positive
    imaginary axis has argument `π/2`. The ratio `Re/Im = 0/b` has vanishing numerators, so
    `RarctanR_of_num_zero` gives `arctan = 0` and `argFar = π/2 − 0 = π/2`. Mirrors `Carg_ofReal_pos`
    (`arg = 0` on the positive real axis). -/
theorem CargFar_pure_imag (b : Real) (k : Nat) (hk : Qlt (Qbound k) ((⟨zero, b⟩ : Complex).im.seq k))
    (ρ : Q) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den) (hρlt : ρ.num.toNat < ρ.den)
    (hb : ∀ n, Qle (Qabs ((Rdiv (⟨zero, b⟩ : Complex).re (⟨zero, b⟩ : Complex).im k hk).seq n)) ρ) :
    Req (CargFar (⟨zero, b⟩ : Complex) k hk ρ hρ0 hρd hρlt hb) Rpi_half := by
  unfold CargFar
  have hz : Req (RarctanR (Rdiv (⟨zero, b⟩ : Complex).re (⟨zero, b⟩ : Complex).im k hk)
      ρ hρ0 hρd hρlt hb) zero := by
    refine RarctanR_of_num_zero
      (Rdiv (⟨zero, b⟩ : Complex).re (⟨zero, b⟩ : Complex).im k hk) ?_ ρ hρ0 hρd hρlt hb
    intro n
    show ((Rmul zero (Rinv b k hk)).seq n).num = 0
    show (mul (zero.seq (Ridx zero (Rinv b k hk) n))
          ((Rinv b k hk).seq (Ridx zero (Rinv b k hk) n))).num = 0
    rw [zero_seq]; simp [mul]
  exact Req_trans (Rsub_congr (Req_refl Rpi_half) hz) (Rsub_zero Rpi_half)

end UOR.Bridge.F1Square.Analysis
