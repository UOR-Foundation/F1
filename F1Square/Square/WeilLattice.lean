/-
F1 square — v0.20.0 stage F, bricks A2 + A3: **the intrinsic trace datum and the FORCED
dictionary** — `⟨Cₙ,Cₙ⟩ = −2λₙ` derived from an intersection pairing, not assumed.

Companion ROADMAP §F (Group A, bricks A2/A3). v0.18.0's `Square.SpectralSquare` carried the
dictionary `⟨Cₙ,Cₙ⟩ = −2λₙ` as a structure FIELD (`dict`). The two-slice inhabitant supplied
it definitionally (`cSq := −2λ`, `dict := rfl`) — an assumption, not a derivation. These two
bricks remove that assumption, exactly the way `BridgeFF.primDG_sq` derives the Hodge-index
form `D°² = −2(x²+axy+qy²)` from the function-field Gram by computation.

A2 — THE INTRINSIC TRACE DATUM (breaking pencil-blindness). The `H¹`-enrichment of `𝕊`'s
`{Δ, Γ}`-plane is the symmetric bilinear pairing `hPair dd gg dg` with intersection data
`Δ² = dd`, `Γ² = gg`, `Δ·Γ = dg`. On the coarse numerical lattice the diagonal meets the
pencil with `Δ·Γₙ = 0` (`Square.square_hodge_pencil_blind`) — pencil-blind. The `H¹`
enrichment carries the trace datum `Δ·Γₙ = λₙ` (the explicit-formula value, the genuine
`Square.genuineLamSeq` closed form built from the prime weights `Λ` and the archimedean
kernel) — `vanCyc_blind` vs `vanCyc_selfpair` is the exact contrast: the SAME class is null
on the coarse lattice and `−2λₙ` on the enrichment.

A3 — THE FORCED DICTIONARY. The primitive spectral class is the **vanishing cycle**
`Cₙ = Δ − Γₙ` (coordinates `(1, −1)`): it is automatically orthogonal to the ample/ruling
directions, and its self-pairing is `Δ² − 2(Δ·Γₙ) + Γₙ² = dd − 2·dg + gg`. With the genuine
geometric inputs `Δ² = Γₙ² = 0` (the diagonal and the pencil members are translates of curves
of self-intersection 0) and the trace datum `Δ·Γₙ = λₙ`, this is `−2λₙ` — DERIVED
(`vanCyc_selfpair`), the `−2` being the lattice's own cross term (`BridgeFF.primDG_sq`'s `−2`,
mirrored). `genuineSpectralSquare` is then a `SpectralSquare` whose `dict` is this THEOREM, not
a field assumption — the line that converts the v0.18.0 bridge from interface to construction.

HONEST SCOPE. The trace datum `dg = λₙ` is the genuine closed-form Li value modulo the
Stieltjes tail (`Square.GenuineLi`); its identification with the genuine ζ explicit-formula
trace is [CLASSICAL], and the open content (the tail / the zeros) is untouched. NOTHING here
asserts positivity: `⟨Cₙ,Cₙ⟩ = −2λₙ` is a sign-free identity. The forced signature (= RH) is
Group B; the crux fields stay `none`.

Pure Lean 4 core, no Mathlib, no `sorry`, choice-free; audited by `scripts/honesty_audit.sh`.
-/

import F1Square.Square.Spectral
import F1Square.Square.Cohomology
import F1Square.Analysis.GenuineLi

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- Integer scaling of a constructive real (the bilinear-form coefficients).
-- ===========================================================================

/-- Integer scaling `m • x` of a real, built on `nsmulR` (no scalar layer): non-negative
    coefficients fold through `nsmulR`, negative ones through `Rneg`. -/
def zmulR : Int → Real → Real
  | Int.ofNat n, x => nsmulR n x
  | Int.negSucc n, x => Rneg (nsmulR (n + 1) x)

/-- `0 • x = 0`. -/
theorem zmulR_zero (x : Real) : zmulR 0 x = zero := rfl

/-- `1 • x = x`. -/
theorem zmulR_one (x : Real) : zmulR 1 x = x := rfl

/-- `(−2) • x = −(x + x)` — the cross-term coefficient of the vanishing cycle. -/
theorem zmulR_negTwo (x : Real) : zmulR (-2) x = Rneg (Radd x x) := rfl

/-- The coefficient may be rewritten when two integers are equal (the scaling depends only on
    the integer value). -/
theorem zmulR_congr_coeff {m m' : Int} (h : m = m') (x : Real) : zmulR m x = zmulR m' x := by
  rw [h]

-- ===========================================================================
-- A2: the intrinsic H¹ pairing on the {Δ, Γ}-plane and the trace datum.
-- ===========================================================================

/-- A class on the `H¹`-enriched `{Δ, Γ}`-plane: coordinates `(c, g)` for `c·Δ + g·Γ`. -/
abbrev HCls : Type := Int × Int

/-- The **intrinsic `H¹` pairing** with intersection data `Δ² = dd`, `Γ² = gg`, `Δ·Γ = dg`:
    the symmetric bilinear form `(c·Δ+g·Γ)·(c'·Δ+g'·Γ) = cc'·dd + gg'·gg + (cg'+gc')·dg`. -/
def hPair (dd gg dg : Real) (u v : HCls) : Real :=
  Radd (Radd (zmulR (u.1 * v.1) dd) (zmulR (u.2 * v.2) gg))
    (zmulR (u.1 * v.2 + u.2 * v.1) dg)

/-- The pairing is symmetric (the Gram is). -/
theorem hPair_symm (dd gg dg : Real) (u v : HCls) :
    hPair dd gg dg u v = hPair dd gg dg v u := by
  simp only [hPair]
  rw [zmulR_congr_coeff (show u.1 * v.1 = v.1 * u.1 by ring_uor) dd,
      zmulR_congr_coeff (show u.2 * v.2 = v.2 * u.2 by ring_uor) gg,
      zmulR_congr_coeff (show u.1 * v.2 + u.2 * v.1 = v.1 * u.2 + v.2 * u.1 by ring_uor) dg]

/-- **The vanishing cycle** `Cₙ = Δ − Γₙ` (coordinates `(1, −1)`) — the primitive spectral
    class. -/
def vanCyc : HCls := (1, -1)

/-- The vanishing-cycle self-pairing, in general intersection data:
    `⟨Δ−Γ, Δ−Γ⟩ = Δ² − 2(Δ·Γ) + Γ² = dd + gg − (dg + dg)`. -/
theorem vanCyc_selfpair_gen (dd gg dg : Real) :
    Req (hPair dd gg dg vanCyc vanCyc) (Radd (Radd dd gg) (Rneg (Radd dg dg))) := by
  show Req (Radd (Radd (zmulR ((1 : Int) * 1) dd) (zmulR ((-1) * (-1)) gg))
      (zmulR ((1 : Int) * (-1) + (-1) * 1) dg))
    (Radd (Radd dd gg) (Rneg (Radd dg dg)))
  rw [zmulR_congr_coeff (show (1 : Int) * 1 = 1 by ring_uor) dd,
      zmulR_congr_coeff (show (-1 : Int) * (-1) = 1 by ring_uor) gg,
      zmulR_congr_coeff (show (1 : Int) * (-1) + (-1) * 1 = -2 by ring_uor) dg,
      zmulR_one dd, zmulR_one gg, zmulR_negTwo dg]
  exact Req_refl _

/-- **A2, pencil-blindness on the coarse lattice**: with the coarse intersection data
    `Δ² = Γ² = Δ·Γ = 0` (`Square.square_hodge_pencil_blind`: `Δ·Γₙ = 0` for all `n`), the
    vanishing cycle is NULL — `⟨Δ−Γ, Δ−Γ⟩ = 0`. No spectral content. -/
theorem vanCyc_blind : Req (hPair zero zero zero vanCyc vanCyc) zero := by
  refine Req_trans (vanCyc_selfpair_gen zero zero zero) ?_
  refine Req_trans (Radd_congr (Radd_zero zero) ?_) (Radd_zero zero)
  exact Req_trans (Rneg_congr (Radd_zero zero)) Rneg_zero

-- ===========================================================================
-- A3: the FORCED dictionary `⟨Cₙ,Cₙ⟩ = −2λₙ` and `genuineSpectralSquare`.
-- ===========================================================================

/-- **A3, the forced dictionary at the trace datum**: with the genuine geometric inputs
    `Δ² = Γ² = 0` and the trace datum `Δ·Γₙ = t`, the vanishing-cycle self-pairing is
    `−2t` — DERIVED from the intersection pairing (`dd − 2dg + gg` at `dd = gg = 0`), the
    `−2` being the lattice's own cross term. This is the dictionary, as a computation. -/
theorem vanCyc_selfpair (t : Real) :
    Req (hPair zero zero t vanCyc vanCyc) (Rneg (Radd t t)) := by
  refine Req_trans (vanCyc_selfpair_gen zero zero t) ?_
  -- `(0 + 0) + (−2t) ≈ 0 + (−2t) ≈ (−2t) + 0 ≈ −2t`
  refine Req_trans (Radd_congr (Radd_zero zero) (Req_refl (Rneg (Radd t t)))) ?_
  exact Req_trans (Radd_comm zero (Rneg (Radd t t))) (Radd_zero (Rneg (Radd t t)))

/-- **THE GENUINE SPECTRAL SQUARE** — the `H¹` enrichment as a CONSTRUCTION: `lam` is the
    genuine closed-form Li sequence (`Square.genuineLamSeq`, built from `Λ` + archimedean
    kernel modulo the Stieltjes tail), `cSq` is the **diagonal of the intrinsic `hPair`** at
    the trace datum `Δ·Γₙ = λₙ`, and the dictionary `dict` is the THEOREM `vanCyc_selfpair`,
    not a field assumption. This is the v0.18.0 bridge's interface converted to construction
    (ROADMAP §F, A3): `⟨Cₙ,Cₙ⟩ = −2λₙ` is now derived. -/
def genuineSpectralSquare (E : StieltjesEta) : SpectralSquare where
  lam := genuineLamSeq E.eta
  cSq := fun n => hPair zero zero (genuineLamSeq E.eta n) vanCyc vanCyc
  dict := fun n _ => vanCyc_selfpair (genuineLamSeq E.eta n)

/-- The construction's `lam` IS the genuine closed-form Li sequence (definitional check). -/
theorem genuineSpectralSquare_lam (E : StieltjesEta) (n : Nat) :
    (genuineSpectralSquare E).lam n = genuineLamSeq E.eta n := rfl

/-- **THE DICTIONARY IS DERIVED, not assumed**: on `genuineSpectralSquare`, the geometric
    self-intersection of the vanishing cycle equals `−2λₙ` BY the pairing computation
    `vanCyc_selfpair` — the `cSq` is the `hPair` diagonal at the trace datum, never the
    sequence `−2λ` plugged in by hand. -/
theorem genuineSpectralSquare_dict (E : StieltjesEta) (n : Nat) :
    Req ((genuineSpectralSquare E).cSq n)
      (Rneg (Radd (genuineLamSeq E.eta n) (genuineLamSeq E.eta n))) :=
  vanCyc_selfpair (genuineLamSeq E.eta n)

end UOR.Bridge.F1Square.Square
