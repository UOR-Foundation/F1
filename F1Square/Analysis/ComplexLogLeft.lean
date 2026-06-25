/-
F1 square — Track 1, item-0 brick (argument axis): **the complex logarithm on the left half-plane**
`ClogLeft z = ½·log|z|² + i·CargLeft z`, for `Re z < 0` and `|Im z / Re z| ≤ ρ < 1` — the `+π` shift
sector, completing the four-sector complex logarithm over the punctured plane near the four axes.

The principal `Clog` covers `Re z > 0`; `ClogUpper`/`ClogLower` the `±` imaginary-axis sectors. For
`Re z < 0`, `−z` lies in the right half-plane and `arg(z) = arg(−z) + π`, so the imaginary part is the
left-sector argument `CargLeft z = Carg(−z) + π` (`ComplexArgLeft.lean`, `CargLeft_tan : tan = Im/Re`).
The real part is the same modulus log `½·log|z|²`.

The characterization `ClogLeft z = Clog(−z) + iπ` (`ClogLeft_eq_Clog_Cneg_add_pi`) is exact: the
imaginary part is definitional (`CargLeft z = Carg(−z) + π`), and the modulus part `½·log|z|² =
½·log|−z|²` is the cheap `hre` congruence (`|−z|² = |z|²`), carried as a hypothesis exactly as
`Clog_conj` carries its modulus congruence.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/
import F1Square.Analysis.ComplexLog
import F1Square.Analysis.ComplexArgLeft

namespace UOR.Bridge.F1Square.Analysis

/-- **The complex logarithm on the left half-plane**: `ClogLeft z = ½·log|z|² + i·CargLeft z`, for
    `Re z < 0` (witness `k` for `Re(−z) = −Re z > 0`) and `|Im z / Re z| ≤ ρ < 1`. The `+π`-shift
    extension of `Clog` to the left half-plane. -/
def ClogLeft (z : Complex) (kn : Nat) (hkn : Qlt (Qbound kn) ((cnormSq z).seq kn))
    (k : Nat) (hk : Qlt (Qbound k) ((Cneg z).re.seq k))
    (ρ : Q) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den) (hρlt : ρ.num.toNat < ρ.den)
    (hb : ∀ n, Qle (Qabs ((Rdiv (Cneg z).im (Cneg z).re k hk).seq n)) ρ) : Complex :=
  ⟨Rmul half (RlogPos (cnormSq z) kn hkn), CargLeft z k hk ρ hρ0 hρd hρlt hb⟩

/-- The real part of `ClogLeft z` is `½·log|z|²` (definitional) — the same modulus log as `Clog`. -/
theorem ClogLeft_re (z : Complex) (kn : Nat) (hkn : Qlt (Qbound kn) ((cnormSq z).seq kn))
    (k : Nat) (hk : Qlt (Qbound k) ((Cneg z).re.seq k))
    (ρ : Q) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den) (hρlt : ρ.num.toNat < ρ.den)
    (hb : ∀ n, Qle (Qabs ((Rdiv (Cneg z).im (Cneg z).re k hk).seq n)) ρ) :
    (ClogLeft z kn hkn k hk ρ hρ0 hρd hρlt hb).re = Rmul half (RlogPos (cnormSq z) kn hkn) := rfl

/-- The imaginary part of `ClogLeft z` is the left-sector argument `CargLeft z` (definitional). -/
theorem ClogLeft_im (z : Complex) (kn : Nat) (hkn : Qlt (Qbound kn) ((cnormSq z).seq kn))
    (k : Nat) (hk : Qlt (Qbound k) ((Cneg z).re.seq k))
    (ρ : Q) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den) (hρlt : ρ.num.toNat < ρ.den)
    (hb : ∀ n, Qle (Qabs ((Rdiv (Cneg z).im (Cneg z).re k hk).seq n)) ρ) :
    (ClogLeft z kn hkn k hk ρ hρ0 hρd hρlt hb).im = CargLeft z k hk ρ hρ0 hρd hρlt hb := rfl

/-- **`ClogLeft z = Clog(−z) + iπ`** — the left-sector log is the principal log of `−z` shifted by `iπ`
    (`arg(z) = arg(−z) + π`). The imaginary part is definitional (`CargLeft z = Carg(−z) + π`, matched
    by the `iπ = ⟨0, π⟩` shift); the modulus part `½·log|z|² = ½·log|−z|²` is the cheap `hre`
    congruence (`|−z|² = |z|²`), carried as a hypothesis exactly as `Clog_conj` does. -/
theorem ClogLeft_eq_Clog_Cneg_add_pi (z : Complex)
    (kn : Nat) (hkn : Qlt (Qbound kn) ((cnormSq z).seq kn))
    (knc : Nat) (hknc : Qlt (Qbound knc) ((cnormSq (Cneg z)).seq knc))
    (k : Nat) (hk : Qlt (Qbound k) ((Cneg z).re.seq k))
    (ρ : Q) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den) (hρlt : ρ.num.toNat < ρ.den)
    (hb : ∀ n, Qle (Qabs ((Rdiv (Cneg z).im (Cneg z).re k hk).seq n)) ρ)
    (hre : Req (RlogPos (cnormSq z) kn hkn) (RlogPos (cnormSq (Cneg z)) knc hknc)) :
    Ceq (ClogLeft z kn hkn k hk ρ hρ0 hρd hρlt hb)
        (Cadd (Clog (Cneg z) knc hknc k hk ρ hρ0 hρd hρlt hb) ⟨zero, Rpi_full⟩) :=
  ⟨Req_trans (Rmul_congr (Req_refl half) hre) (Req_symm (Radd_zero _)), Req_refl _⟩

end UOR.Bridge.F1Square.Analysis
