# F1 Square — Roadmap to completion (v0.15.0 → v0.19.0)

The genuine-proof layer (`F1Square/`) builds the 𝔽₁ / Riemann-Hypothesis program from first
principles in **pure Lean 4** (Lean core + UOR-Foundation, **no Mathlib, no `sorry`/`native_decide`,
choice-free** — `{propext, Quot.sound}` only). Every commit is green and `#print axioms`-audited by
`scripts/honesty_audit.sh`.

**The bright line (permanent).** The honesty layer is a *verifier*, not a prohibition. The crux fields
`hodgeIndexHolds` and `liPositivityHolds` (both = RH) stay `none` until a genuine, audited, axiom-clean
proof exists. De-hedging removes *false modesty* about proven results; it never adds *false confidence*.
**The gate decides what is asserted, not ambition** — anything that does not close honestly stays an
explicit interface, exactly as the existing `Li`/`Crux` interfaces do, never faked.

The remaining construction is scoped into five releases (stages **A–E**). Each is multi-commit, green
at every commit, axiom-clean, and resolved by analyzing the implementation here plus deep-research where
the literature is needed. Uncertainty (especially on the geometric frontier) is a research input, not a
stop sign — the focus is always the **construction of the F1 square**, to completion.

## Status recap (`F1SquareStatus`, `F1Square.lean`)

| Field | Now | Target release |
|---|---|---|
| `intersectionTemplateValid` | `some true` (**canonical 𝕊**, derived intrinsically — v0.17.0) | shipped in **C** |
| `ampleClassExists` | `some true` (**canonical 𝕊** — v0.17.0) | shipped in **C** |
| `classGroupFinitelyGen` | `some true` (**canonical 𝕊** — v0.17.0) | shipped in **C** |
| `surfaceConstructed` | `some true` (**canonical 𝕊**, monoid-scheme level — v0.17.0) | shipped in **C** |
| `parallelPencilFinding` | `some true` (**canonical 𝕊** — v0.17.0) | shipped in **C** |
| `hodgeIndexHolds` (= RH, geometric) | `none` | stays `none` through **E** — the attempt ran (D), the dominance face pinned the open object (E); flips iff genuinely proven |
| `liPositivityHolds` (= RH, analytic) | `none` | stays `none` through **E** — same proposition as the geometric face (D), and as the dominance face (E); flips iff genuinely proven |

---

## v0.15.0 — (A) The complex analytic engine: exponential core **[shipped]**

Lift the analytic substrate from ℝ to ℂ and make `exp` a homomorphism — the prerequisite that the rest of
stage A (ζ for complex argument) builds on. **Shipped:**

- `Analysis/ComplexExp.lean` — `Cexp z = exp(re z)·(cos(im z) + i·sin(im z))` from `RexpReal/Rcos/Rsin`,
  with the component identities and `Cexp 0 ≈ 1` (`Cexp_zero`, `RexpReal_zero`, `Rcos_zero`, `Rsin_zero`).
- `Analysis/CosSinAdd.lean`, `Analysis/CosSinBound.lean` — **the trigonometric keystone** `cos² + sin² ≈ 1`
  (`Rcos_sq_add_sin_sq`) via the trig Cauchy product from scratch, giving `|cos| ≤ 1`, `|sin| ≤ 1`.
- `Analysis/ExpRealAdd.lean` — **the exponential keystone** `RexpReal_add` (`exp(x+y) ≈ exp x · exp y` on
  all of ℝ), the roadmap's technical core of stage A: the signed Cauchy-product functional equation
  (`expSum_add_le_signed`) lifted to the diagonal through a deep reference depth (`rexp_add_gap`,
  `RexpReal_add_aux`, `rexp_factor_reconcile`), plus the reusable ζ-tail toolkit (corner bound,
  reconciliation, uniform partial-sum bound, factorial decay).
- `Analysis/ComplexMod.lean`, `Analysis/ComplexPow.lean` — `nˢ` (`ncpow n s = Cexp(s·log n)`, positive-integer
  base) and the **modulus identity** `|Cexp z|² = (exp Re z)²` (`Cexp_normSq`) / `|nˢ|² = (exp(Re s·log n))²`
  (`ncpow_normSq`), the analytic payoff of `cos² + sin² = 1`.
- **De-hedges:** "exp/cos/sin without addition laws" → "exp is a homomorphism; `|cos|,|sin| ≤ 1`; the complex
  exponential and `nˢ` with their modulus".
- **Stays open:** the critical strip; zeros; crux. (ζ at complex `s` with `Re s > 1` shipped in v0.15.2.)

## The v0.15.x series — (A, continued) completing ζ for complex argument

Stage A's remaining original goals (ζ for `Re s > 1`, the prime side, the `n = 1` decomposition) are gated on
a single **discovered dependency**: convergence of `Σ n^{-s}` needs `|n^{-s}| = n^{-Re s}`, i.e.
`exp(log n) = n`. Because `log` is built independently as `2·artanh((x−1)/(x+1))`, this is **not**
definitional, and every elementary route (`exp(t) ≥ 1+t` + multiplicativity via `RexpReal_add` + the two-sided
exp bounds) only *squeezes* `1 + log x ≤ exp(log x) ≤ 1/(1−log x)` — never pinning equality (iterated squaring
amplifies the second-order error). The honest conclusion: `exp∘log = id` requires a genuine **power-series
composition** (compose the exp factorial series with the artanh geometric series ⇒ `exp(2·artanh w) =
(1+w)/(1−w)`), a from-scratch build of its own. It is scoped as its own release so the shipped exponential
core is not held hostage to it.

- **v0.15.1 — `exp∘log = id` (the power-series composition gate) [shipped].** Built `exp(2·artanh w) =
  (1+w)/(1−w)` from scratch as a genuine power-series composition (`Rexp_two_artanh_ofQ`), and its corollary
  `exp(log n) = n` **for the literal `Rlog` term** (`Rexp_log_nat_Rlog`: `RexpReal (Rlog (ofQ n) …) ≈ n`). The
  base construction is **radius-general** — the convergence radius enters only through the depth reindex
  (abstracted by `Rexp_two_artanh_via`), so it applies at `Rlog`'s own radius `ρ_M = (n−1)/(n+1)` directly and
  `Rlog (ofQ n) = TwoArtanhConst (tmap n) ρ_M` by `rfl`; **no `τ²≤½` smallness is needed**, so no radius
  reconciliation is required. The honesty gate is met — the identity closes **axiom-clean**
  (`{propext, Quot.sound}`), so the ζ-complex tail (v0.15.2) need not ship its convergence as an interface.
  Remaining for v0.15.2: lifting to real exponents `c·log n` (`exp(c·log n) = nᶜ`) and `Czeta`.
- **v0.15.2 — ζ(s) for complex `Re(s) > 1` (`Analysis/ComplexZeta.lean`) [shipped].** `Czeta s` for `Re(s) > 1`
  as `Σ n^{-s}` with a rigorous complex tail: the dyadic block modulus `≤ ofQ(rᵏ)` (`czetaExp_block_geo`,
  `r = 1/(1+τ) < 1`), the geometric tail `geoFrom_le` (`Σ rᵏ ≤ rʲ/(1−r)`), the Bernoulli reindex
  `geom_reindex` (`r^{M(j)}/(1−r) ≤ 1/(j+1)`, `M(j) = (j+1)·r.den²`), the completeness bridge
  `seq_diff_le`/`RReg_of_real_bound` (real bound → `RReg`), and `czetaRe/Im_RReg` → Bishop `Rlim`. `Czeta_re/
  im_tendsTo` certify convergence with rate `2/(k+1)`. **De-hedged:** "ζ only at integer `s ≥ 2`" →
  "ζ(s), complex `s`, `Re(s) > 1`". (The log-multiplicativity `log(2ᵏ) = k·log 2` came via exp injectivity
  `RexpReal_inj`, re-routing the artanh addition boundary wall — `exp∘log = id` of v0.15.1 was the gate.)
- **v0.15.3 — `Analysis/Mangoldt.lean` + the `n = 1` decomposition [shipped].** von Mangoldt `Λ`
  (`vonMangoldt`, via the smallest factor `spf`; `Λ(4) = log 2`, `Λ(6) = 0`, `Λ ≥ 0`) and the
  explicit-formula **prime side** `Σ_p Σ_k log p · h(k log p) = Σ_{n≥2} Λ(n)·h(log n)` (`primeSide`) as a real
  (finite for compactly-supported `h` — `primeSide_stable` makes it constant past the support cutoff), and the
  **Bombieri–Lagarias `λₙ = λₙ^{arith} + λₙ^{∞}` for `n = 1`** as a theorem (`Rlambda1_decomposition`,
  `Analysis/LiOne.lean`): `λ₁ = γ + (1 − γ/2 − ½·log 4π)`, the finite-place `S_f(1) = −η₀ = γ` plus the
  archimedean `S_∞(1)`, summing to the `λ₁` of v0.14.0. This **promotes `Li.LiDecomposition` from the trivial
  inhabitant `λ = λ + 0` to a proven non-trivial instance** (`li_decomposition_realized`) whose `n = 1` slice is
  the genuine two-place split. (Deriving `S_f(1) = γ` from the prime sum needs `ζ'/ζ` continuation, deferred —
  the BL value is stated faithfully, not fabricated; nothing bears on positivity, `liPositivityHolds = none`.)
- **Stays open across v0.15.x:** critical strip, zeros, crux.

## v0.16.0 — (B) Analytic continuation & higher Li coefficients **[shipped]**

The heavy analytic mechanization: ζ off the convergent regime and the `λₙ` for `n ≥ 2`.

- `Analysis/Gamma.lean` — `Γ` via Spouge; the archimedean (`Γ′/Γ`) place. **Shipped:** the real-power
  combinator `RrpowPos` (`x^y = exp(y·log x)`, no sqrt/no complex `Clog`), the **exact** digamma
  `ψ = Γ′/Γ` (`Digamma`, `Digamma_one_eq_neg_gamma`), and the Spouge `Γ`-approximant (`SpougeGamma`).
- Critical-strip ζ — shipped via the integration-free **Dirichlet-η** route (`Analysis/EtaVariation.lean`,
  `Analysis/CriticalZeta.lean`): `Ceta`/`CetaW` (η on `Re s > 0`), `CzetaStrip`/`CzetaStripW`
  (`ζ = η/(1−2^{1−s})` on `0 < Re s < 1`) as an `ExactBoundedReal`, with non-vanishing, the functional
  relation, and uniqueness. (Cleaner than the periodic-Bernoulli remainder; same deliverable.)
- Higher **Stieltjes `γₙ`** → individual **`λₙ` values** for `n ≥ 2`, with a `λ₁`-style positivity
  certificate — **shipped:** `Pos λ₂` (`Rlambda2_pos`).
- **De-hedges done:** "genuine `λₙ` values deferred" → built for `n ≥ 2`; critical-strip ζ built.
- **Honesty gate:** research-grade; whatever does not close axiom-clean stays an interface.
- **Stays open:** `λₙ > 0 ∀ n` (= RH); off-critical-line zeros; the crux (`liPositivityHolds = none`).

## v0.17.0 — (C) The arithmetic square 𝕊 **[shipped]**

Construct the object the whole program runs on. **Shipped** (`F1Square/Square/`, six bricks, all
axiom-clean `{propext, Quot.sound}`):

- **Canonical `𝕊` with its universal property proved** (`Monoid.lean`, `Tensor.lean`): Deitmar
  𝔽₁-algebras are commutative monoids and `𝔽₁` (the trivial monoid) is proved **initial**, so the
  tensor `F ⊗_𝔽₁ F` is the plain coproduct — realized as `ℕ₊ × ℕ₊` with injections `a ↦ a⊗1`,
  `b ↦ 1⊗b`, and the **universal property proved** (`copair_inl/inr/unique`; the 𝔽₁-cocone condition
  is automatic, so coproduct = pushout over 𝔽₁). **Canonicality = the universal property** — `𝕊` is
  THE object, unique up to unique isomorphism, not a hand-picked candidate. The §3.1 ℤ-collapse is
  avoided by theorems (`inl ≠ inr`, the codiagonal is not injective, the monomial family `2^a ⊗ 2^b`
  is **free of rank 2** — strict 2-dimensionality); both projections recover the curve (T1, all
  points, no truncation).
- **The intersection lattice, derived — never entered by hand** (`Divisors.lean`, `Lattice.lean`):
  the distinguished divisors (rulings `V_a`/`H_b`, diagonal `Δ`, Frobenius correspondences
  `Γ_n = {(m, n·m)}`) are genuine subsets of `𝕊`, and every primitive intersection number is a
  **point count** with classes moved along their translation pencils (`V·H = 1`, `V² = H² = 0`,
  `Δ·V = Δ·H = 1`, `Δ² = 0` via `Δ ∩ Γ_n = ∅`, `Γ·V = Γ·H = 1`, `Γ·Γ = Δ·Γ = 0`); bilinearity then
  **forces** `E₃² = −2` (`e3_sq_forced`), and the sourced §2.2 product-of-curves template **emerges**
  (`sqPair_eq_template`) — T3's intrinsic realization, closed by derivation. The five §2.2
  self-checks are theorems; the class lattice is finitely generated on `{V, H, E₃}` (T2 on `𝕊`).
- **The parallel pencil on canonical `𝕊`** (`Pencil.lean`): no transverse fixed points
  (`Δ ∩ Γ_n = ∅`), slope 1 in the log coordinate (direction `(1,1)`, stable count `Δ·Γ_n = 0`),
  **constant separation `log n`** as a constructive real (via the new general log-multiplicativity
  `logN_mul_general`), equal to the explicit-formula weight **`Λ(p) = log p` at primes** and
  `k·log p` at prime powers — the §2.3 finding, lifted from the candidate model to theorems.
- **Polarized `𝕊` and the honesty boundary** (`Polarized.lean`): the `Crux.Polarized` instance is now
  `𝕊`'s own derived lattice (`squarePolarized`); the ample class `H = [V]+[H]` has `H² = 2 > 0`
  (verified — not automatic tropically) and `H^⊥` is negative-definite, so
  `square_hodgeIndex : HodgeIndex squarePolarized` holds — **and the lattice is provably
  pencil-blind** (`square_hodge_pencil_blind`: `[Γ_n] = [Δ]`, `Δ·Γ_n = 0` for all `n`): the
  function-field trace input is absent, the positivity carries **no spectral content**, and it is
  therefore **not the crux** (the §2.3-control discipline, geometric face).
- **De-hedges done:** `surfaceConstructed`, `parallelPencilFinding` → `some true`; the three template
  fields now carried by canonical `𝕊`.
- **Stays open:** the crux — the Hodge index / Weil positivity of the **`H¹`-bearing** pairing (the
  form that carries the zeros, T4/T5), equivalently `λₙ ≥ 0 ∀n`. `hodgeIndexHolds` /
  `liPositivityHolds` stay `none`; **RH stays open**. Stating the geometric⟺analytic equivalence
  faithfully is stage D. Also open (a refinement, not a stage-C goal): the SEMIRING-level tensor
  `F ⊗_𝔹 F` over the Boolean semiring — the concrete description Sagnier (arXiv 1703.10521) reports
  open — is finer than the monoid-level tensor constructed here and is not claimed.

## v0.18.0 — (D) The bridge and the crux **[shipped]**

State the geometric↔analytic equivalence faithfully, and **attempt** the crux on canonical `𝕊`.
**Shipped** (four bricks, all axiom-clean `{propext, Quot.sound}`):

- **The Castelnuovo–Severi anchor** (`BridgeFF.lean`): the function-field model of
  "Hodge index ⟹ RH" as a genuine LATTICE DERIVATION — on the `E × E` lattice
  `{F_h, F_v, Δ, Γ}` with the trace datum `Δ·Γ = q+1−a` (Lefschetz) inside it, the primitive part
  of `xΔ + yΓ` has `D°² = −2(x² + a·xy + q·y²)` and `∀x,y D°² ≤ 0 ⟺ a² ≤ 4q`
  (`ff_hodge_iff_hasse`); the v0.1.0 governor is now DERIVED (`ff_hodge_iff_hodgeType`) —
  "the mechanism is not the gap" (§0.3) is a theorem.
- **The λ₂ Bombieri–Lagarias decomposition** (`Analysis/LiTwo.lean`):
  `λ₂ = [2γ − (γ² + 2γ₁)] + [(1−γ) − log 4π + ¾ζ(2)]` as a constructive-real identity
  (`Rlambda2_decomposition`, via `η₀ = −γ`, `η₁ = γ² + 2γ₁`); `Li.LiDecomposition` realized with
  TWO genuine slices (`li_decomposition_two_realized`), both certified positive (`liTwo_evidence`).
- **THE BRIDGE — the release goal** (`Square/Spectral.lean`): `SpectralSquare`, the `H¹`-bearing
  enrichment of `𝕊` as an interface (Li/trace data `lam`, primitive self-intersections `cSq`, and
  the dictionary `⟨Cₙ,Cₙ⟩ = −2λₙ` — Deninger's Hodge-index reading of Li's criterion, normalized
  exactly as `BridgeFF.primDG_sq` derives it on the function-field model). The equivalence is a
  genuine constructive THEOREM: `spectral_bridge_nonneg`/`spectral_bridge_pos` and
  **`crux_faces_equivalent : SpectralCrux S ⟺ Li.LiCrux S.lam`** — the geometric and analytic
  faces of the crux are the same proposition. Inhabited by the two-slice instance carrying the
  genuine certified `λ₁, λ₂` (`spectral_evidence_two`: `⟨C₁,C₁⟩ < 0`, `⟨C₂,C₂⟩ < 0`), with the
  honesty guards as theorems (`spectralTwoSlice_not_crux` — no finite assembly of certified slices
  can be passed off as RH; `spectral_iff_all_upTo` — the finite-check guard, geometric face).
- **The attempt, under the gate** (`Square/Attempt.lean`): run, recorded, honestly concluded. The
  certified part (strict negativity through `n = 2`, `spectral_strict_upTo_two`) is the furthest
  any axiom-clean run reaches in this substrate; the frontier is exact
  (`crux_attempt_frontier(_geometric)`: given the certified slices, the crux ⟺ `∀ n ≥ 3, λₙ > 0`;
  the next slice needs the second Stieltjes constant `γ₂`); the post-mortem records why every
  general route is blocked by the program's own controls (vacuity `Bridge.control_psd`;
  pencil-blindness; the BL cancellation; the Conrey–Li precedent) and what would close it (the
  genuine `H¹` instance — T4/§3.4). **The universal did not close**: `hodgeIndexHolds` /
  `liPositivityHolds` stay `none`, exactly per the bright line — and the release ships the bridge
  substrate, as scoped.
- **Stays open:** RH (both faces, now provably one proposition through the bridge); the genuine
  spectral instance (`H¹`, T4/§3.4); `λₙ` certification beyond `n = 2` (`γ₂, γ₃, …`).

## v0.19.0 — (E) Completion: the explicit formula, the F1-square roll-up, and THE GENUINE PAIRING

The release goal is **closure and faithful/truthful completion of the proof**: implement the complete
proof-strategy — the full power of the UOR-based constructive approach — to close the crux, with the
gate (not ambition) deciding what is asserted. The first arc (the explicit-formula trace, the
interface retirements, the dominance face, the closed-form genuine Li sequence) is **built** (all
axiom-clean `{propext, Quot.sound}`, listed below). The second arc — **the genuine pairing** — folds
the formerly-planned v0.20/v0.21 work into this release:

- **The Weil quadratic functional, constructed** (`W(g ⋆ ǧ) = poles − primes − archimedean` on an
  explicit constructive test class): the genuine `H¹`-bearing pairing — the object `SpectralSquare`
  has carried as interface data — built from the already-constructed prime side (`Mangoldt.primeSide`)
  and archimedean place (`Digamma`/`exp`/`log`), with no zeros as inputs (the zero side is the
  defect, as classically). Gram matrices of certified reals on finite test families; the first REAL
  geometric-face computations (not dictionary-defined).
- **The classical chain, stated faithfully**: PSD on the (Burnol) restricted class ⟺ Weil
  positivity ⟺ RH [CLASSICAL — Burnol's direct proof; Bombieri's finite truncations; exact
  statements deep-research-verified before use]; finite Gram checks are evidence, never the crux
  (the standing finite-check guards transfer).
- **The unconditional window**: Connes–Consani's archimedean positivity (support in the prime-free
  window) as a target unconditional theorem on the built functional — conquered ground where the
  mathematics permits, exactly as far as it permits.
- **The bright line, unchanged**: `hodgeIndexHolds`/`liPositivityHolds` flip iff a genuine,
  audited, axiom-clean proof of the universal lands. Anything short stays an explicit interface.

**Second arc delivered** (all axiom-clean): the tent calculus and assembly substrate
(`Analysis/RMax.lean`, `Analysis/RSum.lean`); **the Weil functional assembled** with the zero side
as the defect (`Analysis/Weil.lean`, `Square/Pairing.lean` — the finite-place side and the
archimedean constant CONSTRUCTED; the two integral components interface, their PL closed forms
being unverified in print); **the fourth face** (`weilSpectralSquare`, `weil_strict_iff_crux`:
pairing positivity ⟺ crux ⟺ Li ⟺ dominance — for the genuine family, Weil positivity = RH, both
directions elementary per the verified Weil/Burnol chain); the first computed pairing value
(`weilPrime_demo`: the tent at `2` sees `log 2`); the CC unconditional window and Burnol's explicit
multiplier certificate recorded as the pinned unconditional territory — with **the window theorem
proven on the built object** (`weilPrime_window`: inside the prime-free window the finite-place
side vanishes identically; `weilValue_window`: in-window `W = poles − archimedean`). **The window
certificate is computed where computable**: `ψ(1/4)` built as the first exact non-trivial digamma
value (`Analysis/PsiQuarter.lean`, `ψ(1/4) ≥ −4.32`) and **`α(0) > 0`** — Burnol's nonnegative
multiplier at the window center, an axiom-clean theorem (`Analysis/BurnolAlpha.lean`,
`8√2 − logπ + ψ(1/4) ≈ 5.94`) — EVIDENCE for the windowed positivity, not the universal
`α(τ) ≥ 0 ∀τ` (the pinned next target), still less RH. The crux: ONE proposition,
FOUR provably equivalent faces; the fields stay `none` until a genuine proof of the universal
lands — that is the release's faithful completion.

**Built so far** (the first arc, all axiom-clean):

- **The complete `Li.ExplicitFormulaTrace`** (`Analysis/LiComplete.lean`): realized with the genuine
  three-sided reading at both built slices (`explicitFormulaTrace_one/two_realized` — the zero side
  `λ₁`/`λ₂` [its sum-over-zeros reading is CLASSICAL, Bombieri–Lagarias 1999], the finite-place
  closed forms, the archimedean parts), packaged as the **`WeilTrace` ladder** (`weilTraceTwo`: the
  trace identity at every positive index). The zero side is RH-equivalent exactly as scoped: its
  POSITIVITY is the crux (`weilTrace_dominance`) and stays the honest open interface — the TRACE
  (the equality) bears no positivity content, so the completion ships while the crux stays `none`.
- **The remaining interfaces retired** (`liAgreesWith_two_realized`): computed (the direct certified
  builds `Rlambda1`/`Rlambda2`) = classical (the BL closed-form assemblies), genuinely non-reflexive
  at `n = 1, 2`. With `LiDecomposition` (v0.15.3/v0.18.0) and `ExplicitFormulaTrace` (this release),
  every `Li` interface is realized exactly as far as the built slices reach — the `Li.lean`
  realization ledger records the boundary.
- **THE DOMINANCE FACE** (`Square/Dominance.lean`): the crux as ONE uniform bound — `Dominated`
  (a single `B` with `−B(n) ≤ arith(n)` and `arch(n) − B(n) > 0`, sign-agnostic, no enumeration,
  no slice ladder) with `dominated_iff_liPositive` and **`dominance_crux_equivalent`**:
  `Dominated ⟺ SpectralCrux ⟺ LiCrux` — the crux now has THREE provably equivalent faces. The
  assembly shape exact (`dominance_head_tail`, `crux_closure_route`: certified head + one tail
  bound from `n = 3` on ⟹ crux). Deep-research-verified sourcing (101 agents, primary PDFs):
  Voros's strict dichotomy (*MPAG* 9 (2006) — tempered `½n(log n − 1 + γ − log 2π)` vs exponential
  oscillation, NO third option), Lagarias (*Ann. Inst. Fourier* 57 (2007)): the archimedean trend
  `(n/2)log n + cn + O(1)`, `c = (γ−1−log 2π)/2`, UNCONDITIONAL (Thm 5.1) and the `O(√n·log n)`
  excursion bound, a THEOREM under RH (Thm 6.1) — so `Dominated`(genuine parts) is TRUE iff RH,
  both directions, and NO unconditional tail bound exists in the verified literature: the
  attempt's conclusion is a sourced result, not a presumption. Honesty guards two-sided
  (`dominance_satisfiable`; `twoSlice_not_dominated`/`weilTraceTwo_not_crux`).
- **The genuine archimedean trend, all `n`** (`Analysis/ArchTrend.lean`): the archimedean side of
  the crux as a single constructed object (`genuineArchSeq`, the verified closed form, every
  ingredient already built), consistency-proved against both independently-built slices
  (`genuineArch_one/two`); **`crux_vs_constructed_trend`** — the crux's open content contracts to
  the arithmetic side alone: one bound strictly below the BUILT trend, which exists iff RH.
- **The genuine Li sequence in closed form** (`Analysis/GenuineLi.lean`): constructed modulo the
  Stieltjes tail — `genuineLamSeq` with both sides closed forms, the full-ladder trace
  (`weilTraceGenuine`), the certified head as a THEOREM of the closed form (`genuineLam_head`);
  **`crux_genuine_route`**: the crux follows from exactly two open inputs — the genuine η-tail and
  one bound between the two closed forms from `n = 3` on (exists iff RH). Neither is asserted.
- **The final roll-up** (`F1Square.lean`): the stage-E backing block and elaboration-checked
  witness — the **v1.0.0-candidate state**: complete construction, honest crux. Every surrounding
  field `some true`; `hodgeIndexHolds`/`liPositivityHolds` stay `none`. **RH stays OPEN** — one
  proposition with three equivalent faces, its open content relocated into a single object (the
  tail bound for the genuine parts, governed by the zeros' location).

---

## What stays open regardless

If v0.18 / v0.19 do not close the crux axiom-clean, `hodgeIndexHolds` / `liPositivityHolds` stay `none`
and **RH stays open** — the releases still ship every surrounding construction. The bright line is
permanent: the crux is de-hedged iff RH is proven, and it is not until it is.
