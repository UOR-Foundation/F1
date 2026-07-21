# Changelog

All notable changes to this project are documented here. The format is based on
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and this project adheres to
[Semantic Versioning](https://semver.org/spec/v2.0.0.html), starting at `v0.0.1`.

## [Unreleased]

Post-v0.21.0 research thread — the constructive **RH witness**, the **ξ-zero symmetry group**, the
**Bombieri–Lagarias pipeline** wiring the witness to the genuine `λ` (Li's criterion, both
directions), the **arithmetic Hodge index ⟺ RH** equivalence stated about the *constructed* ζ, the
**Voros off-line** analysis, and the **Burnol-multiplier obstruction** — the Riemann–Siegel angle's
non-monotone window and its capstone `α(2) < 0` (the archimedean multiplier is pointwise *indefinite*,
so single-place positivity provably does not extend — the obstruction, never a false `α ≥ 0`). All
axiom-clean (`{propext, Quot.sound}`), no `sorry`/`native_decide`, choice-free; the no-smuggling audit
passes; the crux fields stay `none` (RH open throughout — every classical input is an explicit,
audit-visible hypothesis, never an axiom).

- **`t4B12/23/34/h/q` — the `t4PoleB` pieces, part 4: constructed and evaluated** (in
  `Analysis/T4PoleBPieces.lean`): the five interval integrals of `t4F(x)/x` over
  `[1/4, 4]`, each a genuine constructed `riemannIntegral` — the three unit pieces
  `t4H·recip − ½·gLx` at shared modulus `2 + LxQ c`, the `[1/2,1]` piece
  `log2·recip + ½·gLx`, the `[1/4,1/2]` piece `½·gLx` (the substitution constant
  cancels the cone height, as in poleA) — with values `t4H·Δlog_c − ½ΔHn_c`,
  `log2·Δlog₁ + ½ΔHn₁`, `½ΔHn₁`. `t4PoleB` (the five-piece sum) is defined; the
  `4(log2)² = t4H·t4H` assembly is the companion brick. Axiom-clean; crux fields
  `none`.
- **`t4PoleB_eq` — `t4PoleB ≈ (2log2)² = 4(log2)²`, EXACT** (in
  `Analysis/T4PoleBPieces.lean`): the cone tent\'s `∫ f/x` pole component evaluates to
  the exact square `t4H·t4H`. The five constructed pieces (`t4B12/23/34/h/q`, part 4)
  telescope: the upper `A`-cluster gives `t4H·(log4 − log1) = t4H·t4H` and the
  `B`-cluster `−(1/2)·(Hn4 − Hn1) = −(1/2)·t4H·t4H` (both `log3`/`Hn3` drop without
  expansion), the lower pieces give `log2² + log2² = (1/2)·t4H·t4H`, and the halves
  cancel to the square. The SECOND `t4` slot component pinned (after `t4PoleA = 9/4`);
  remaining for `W(t4)`: the archimedean tail (recipC pieces + the dilog bracket) and
  the sign theorem. Axiom-clean; crux fields `none`.
- **`t4B_lower_eval` — the `t4PoleB` pieces, part 3: the lower pieces** (in
  `Analysis/T4PoleBPieces.lean`): `∫₀¹ (C·(1/(c+t)) + (1/2)·gLx c) dt ≈ C·Δlog_c +
  (1/2)·ΔHn_c`, generic in the bounded real constant — the `[1/2, 1]` piece at
  `C = log 2` and the `[1/4, 1/2]` piece\'s scaffold. The simplifying observation:
  the poleB measure `dx/x` is scale-INVARIANT, so the sub-unit pieces pull back with
  NO outer weight (`[1/2,1] ↦ (log2 + log(1+t))/(1+t) dt` exactly). Next: the five
  instances and the `4(log2)²` assembly. Axiom-clean; crux fields `none`.
- **`t4B_upper_eval` — the `t4PoleB` pieces, part 2: the upper pieces** (in
  `Analysis/T4PoleBPieces.lean`): `∫₀¹ (t4H·(1/(c+t)) + (−1/2)·gLx c) dt ≈
  t4H·(log(c+1) − log c) − (1/2)·(Hn(c+1) − Hn(c))` — the pulled-back
  `∫_c^{c+1} (2log2 − log x)/x dx`, general in the base (`1 ≤ c ≤ 3`) with the
  weakening certificates (`Qle` to the shared modulus) as decidable hypotheses;
  through `riemannIntegral_add`, the real-scalar reciprocal engine at `B = 2`, and
  the `gLx` engine. Next: the three upper instances, the two lower pieces
  (`(1/2)`, `(1/4)`-weighted), and the `4(log2)²` assembly. Axiom-clean; crux fields
  `none`.
- **`smul_lip`/`add_lip` + `t4H_abs` — the `t4PoleB` pieces, part 1: the combinators**
  (new `Analysis/T4PoleBPieces.lean`): the generic Lipschitz combinators the poleB
  piece integrands (`C·gRecipC + q·gLx`) consume — `|C| ≤ B` gives `C·f` at `B·L_f`;
  `f + g` at `L_f + L_g` — plus the cone-height bounds `0 ≤ t4H = 2log2 ≤ 2` and
  `|log 2| ≤ 1`, feeding `riemannIntegral_recipC_smul` at `B = 2` resp. `B = 1`.
  Next: the five piece definitions and evaluations, then the `4(log2)²` assembly.
  Axiom-clean; crux fields `none`.
- **`riemannIntegral_recipC_smul` — the real-scalar reciprocal evaluation** (new
  `Analysis/RecipSmulEval.lean`): `∫₀¹ C·(1/(c+t)) dt ≈ C·(log(c+1) − log c)` for a
  REAL constant `C` with `|C| ≤ B`, `B.num ≤ 5` — the first real-scalar integral
  evaluation, possible because the reciprocal family\'s Riemann sums are EXACT
  rationals (`riemannSum_gRecipC = hFold`), so the dyadic sums scale by `C` exactly
  (`riemannSum_smul` is real-scalar) and the defect is `|C|·wedge ≤ B/(c(c+1)2^m)`.
  This is the engine the `t4` poleB pieces need for their `2log2·(1/x)` halves; the
  `(1/2)·gLx` halves use the rational-scalar API. Next: the five poleB pieces and the
  `4(log2)²` assembly. Axiom-clean; crux fields `none`.
- **`riemannIntegral_gLx1/2/3` — the `∫ log/x` layer COMPLETE: the evaluation** (in
  `Analysis/LogOverXEval.lean`): `∫₀¹ 2·log(c+t)/(c+t) dt ≈ Hn(c+1) − Hn(c)`
  (`= log²(c+1) − log²c`), certified for `c = 1, 2, 3` at the product-Lipschitz datum
  `2c+2` — the THIRD certified evaluation family (after the harmonic `recipC` and the
  `∫log` `Gn` families), and the engine `poleB = 4(log2)²` consumes. Assembly: the
  anchor `D₀ = (1/c)·2·log c`, the schedule rate at any `midx ≥ 5(j+1)` (discharged
  per instance: `2c+3 ≥ 5`), `Rlim_eval_real`. Next: the five `t4` poleB pieces and
  the `4(log2)²` assembly (mirror of `t4PoleA`). Axiom-clean; crux fields `none`.
- **`dyadicR_gLx_defect` — the `∫ log/x` layer, part 8b-ii: the dyadic defect** (new
  `Analysis/LogOverXEval.lean`): `|D_m − (Hn(c+1) − Hn(c))| ≤ (5m+5)/2^m` — the
  convergence core of `∫₀¹ 2log(c+t)/(c+t) dt`. The deviation decomposes exactly
  (`lxe_insert`) into the sample-bracket slack (`≤ (2m+5)·2^m/A²`, capped gap + the
  `M/A²` reverse) plus the cross term `2·log(2^m)·(Δlog − hFold)` (`≤ 2m/(c(c+1)2^m)`,
  the harmonic wedge absorbing the scale identity\'s cross term), totalling
  `(4m+5)/2^m`. GOTCHA confirmed: `ring_uor` mis-atomizes repeated cast occurrences
  (`↑2^m` thrice) — use core `Int.add_mul`/`Int.mul_assoc` on cast-heavy goals.
  Remaining: the `digammaMidx` rate + `Rlim_eval_real` + instances. Axiom-clean; crux
  fields `none`.
- **`lxr_cap` + `Hn_sample_upper_cap` — the `∫ log/x` layer, part 8b-i: the rate
  ingredients** (new `Analysis/LogOverXRate.lean`): the schedule arithmetic
  `5(j+1) ≤ m ⟹ (5m+5)(j+1) ≤ 2^m` (via `m(m+1) ≤ 2^m`, `m ≥ 5`), the per-cell
  log-sum cap `≤ 2m + 4` at `M = 2^m` (`logN_mono` into `(c+1)2^m`, split by
  `logN_mul_gen`, `log(c+1) ≤ 2`, `log(2^m) ≤ m`), the capped sample bracket
  `hsSample ≤ ΔHn + gapQE`, and the rational collapse `gapQE ≤ E·c/A²`. What remains
  for `∫₀¹ 2log(c+t)/(c+t) = Hn(c+1) − Hn(c)`: the rate core (triangle over the
  three slack terms + `Hn_scale_diff` + `hFoldC_defect`) and the `Rlim` wiring.
  Axiom-clean; crux fields `none`.
- **`hsFold_gap_cap` + `logN_two_pow_le` — the `∫ log/x` layer, part 8a: the
  log-aware gap** (in `Analysis/LogSqStep.lean`): the rate ledger showed the part-3
  crude cap does NOT decay once unscaled (the sample fold is already the scaled
  Riemann sum), so the fold gap is re-proven with an arbitrary per-cell log-sum cap
  `E` (`hsFold_gap_cap`, cells `E/((A+j)(A+j+1))`), fed by the new magnitude bounds
  `log 2 ≤ 1` (`Rlog_le_sub_one` at the rational base) and `log(2^m) ≤ m`
  (`logN_pow_two` + the `k·x ≤ k` fold) — at `M = 2^m` the cap is `E ~ 2m + 4` and
  the telescoped gap is `~ m/M`, which the `digammaMidx` schedule absorbs
  (`m² ≤ 2^m`). Axiom-clean; crux fields `none`.
- **`Hn_scale_diff` — the `∫ log/x` layer, part 7: the scale identity** (in
  `Analysis/LogSqStep.lean`): `Hn(kM) ≈ Hn(k) + (2·log M·log k + Hn(M))`
  (`Hn_scale_expand`, the `(a+b)²` expansion over `logN_mul_gen`) and the difference
  `Hn((c+1)M) − Hn(cM) ≈ (Hn(c+1) − Hn(c)) + 2·log M·(log(c+1) − log c)` — `Hn(M)`
  and `log²M` cancel, leaving exactly the cross term that the collapse\'s
  `−2·log(N+1)·hFold` will absorb (`hFoldC_defect`: `hFold ≈ log(c+1) − log c` within
  `1/(c(c+1)M)`). All pieces for the `gLx` rate are now on the table. Axiom-clean;
  crux fields `none`.
- **`riemannSum_gLx` — the `∫ log/x` layer, part 6: the point values and the Riemann
  fold** (new `Analysis/LogOverXSum.lean`): `gLx c (j/(N+1)) ≈ 2(log(c(N+1)+j) −
  log(N+1))·(N+1)/(c(N+1)+j)` (`gLx_point`, free from `gLog_point` + `gRecipC_point`),
  the fold `Σ_{i<k} gLx ≈ (N+1)·hsSample(c(N+1), k) − 2log(N+1)·harmTermFoldC(k)`
  (`RsumN_gLx` — the log² content lands in `LogSqStep`'s sample fold, the cross term in
  `HarmonicLogC`'s harmonic fold), and the collapse `riemannSum (gLx c) N ≈
  hsSample(c(N+1), N+1) − 2log(N+1)·hFold(c(N+1), N+1)` (`riemannSum_gLx`). Next: the
  `Hn` scale identity (`(a+b)²` expansion over `logN_mul_gen`) and the rate.
  Axiom-clean; crux fields `none`.
- **`gLx` + `gLx_lip_of` — the `∫ log/x` layer, part 5: the integrand family** (new
  `Analysis/LogOverX.lean`): the totalized integrand
  `gLx c t = (gLog c t + gLog c t)·gRecipC c t` (`= 2·log(c+t)/(c+t)` on `[0,1]`) with
  the full gateway data — the uniform bounds `0 ≤ gLog c ≤ c` (`gLog_le`, the first
  consumer of `RlogPos_le_sub_one`: `log x ≤ x − 1` at the presented band modulus) and
  `|gRecipC| ≤ 1` (`Rinv_le_ofQ_inv` over the clamp floor), the doubled-integrand
  `2`-Lipschitz combinator `twoF_lip` (generic in the `1`-Lipschitz factor), and the
  product-Lipschitz certificate `gLx_lip_of` at constant `2c·1 + 1·2 = 2c + 2`
  (`Rmul_lipschitz` — its first gateway consumer). The objects
  `riemannIntegral (gLx c)` construct for `c = 1, 2, 3`. Next: the point values and
  the rate against `Hn(c+1) − Hn(c)`. Axiom-clean; crux fields `none`.
- **`Hn_sample_upper/lower` — the `∫ log/x` layer, part 4b: the two-sided sample
  bracket** (in `Analysis/LogSqStep.lean`): the reverse slack `hsFoldHi ≤ hsSample +
  c/A²` (per cell the weighted log step `δ/(A+k) ≤ 1/(A+k)² ≤ 1/A²`, summed at the
  common denominator `A²`), and the combined bracket
  `(Hn(A+M) − Hn(A)) − M/A² ≤ hsSample ≤ (Hn(A+M) − Hn(A)) + gapQ` — the sample fold
  (the exact `log/x` Riemann-sum shape) is now two-sided against the `log²`
  antiderivative difference, with both slacks decaying like `1/M` after scaling. Next:
  the `log/x` integrand family and the rate wiring. Axiom-clean; crux fields `none`.
- **`hsSample_le_foldHi` — the `∫ log/x` layer, part 4a: the sample fold** (in
  `Analysis/LogSqStep.lean`): `hsSample = Σ_{j<c} 2·log(A+j)/(A+j)` — the exact shape
  the `log/x` Riemann sums take — with the cell-wise comparison
  `hsSample ≤ hsFoldHi` (`2·log(A+j) ≤ log(A+j) + log(A+j+1)` by `logN_mono`, same
  weight). With the telescopes and the fold gap this brackets the sample fold against
  `Hn(A+c) − Hn(A)` from above; the reverse slack (`foldHi ≤ sample + c/A²`, via the
  step bracket squared) is the next brick. Axiom-clean; crux fields `none`.
- **`hsFold_gap` — the `∫ log/x` layer, part 3: the fold gap** (in
  `Analysis/LogSqStep.lean`): `hsFoldHi ≤ hsFoldLo + Σ_{j<c} 2(K+1)/((A+j)(A+j+1))`
  for any cap `A + c ≤ K` — the KEY insight verified in the kernel: the crude
  `log n ≤ n` bound (`logN_le_self`) suffices, because the harmonic cells
  `1/((A+j)(A+j+1))` telescope to `≤ c/A²`, killing a factor of `A ~ cM` (the scaled
  defect decays like `1/M` with no log-precision anywhere). Per-cell:
  `Rmul_sub_distrib_right` collapses the weight difference to the harmonic cell.
  Next: the `log/x` Riemann fold comparison and the eval
  `∫₀¹ 2log(c+t)/(c+t) = Hn(c+1) − Hn(c)`. Axiom-clean; crux fields `none`.
- **`Hn_tele_lower/upper` — the `∫ log/x` layer, part 2: the telescopes** (in
  `Analysis/LogSqStep.lean`; toward `poleB = 4(log2)²`): the step-folds
  `hsFoldLo/hsFoldHi` (`Σ_{j<c} (log(A+j) + log(A+j+1))·w` at the lower/upper step
  weights `w = 1/(A+j+1), 1/(A+j)`) and the two-sided telescope
  `Hn(A) + foldLo ≤ Hn(A+c) ≤ Hn(A) + foldHi`, general in the base and the count —
  the `Gn_tele` pattern one level up. Next: the fold gap and the `log/x` Riemann
  comparison. Axiom-clean; crux fields `none`.
- **`Hn_step_lower/upper` — the `∫ log/x` layer, part 1: the `log²` step bracket** (new
  `Analysis/LogSqStep.lean`; Sonine route, step 2 — the `W(t4)` campaign, toward
  `poleB = 4(log2)²`): the antiderivative object `Hn(n) = (log n)²` (`= 2·∫₁ⁿ log x/x`)
  with `Hn(1) ≈ 0` and the two-sided unit-step bracket
  `(log i + log(i+1))/(i+1) ≤ Hn(i+1) − Hn(i) ≤ (log i + log(i+1))/i`, GENERAL in `i` —
  the difference of squares collapses the step (`Rmul_sub_add_self`), the certified
  per-step log bracket (`ExpBounds`) bounds the first factor, and `Rnonneg_logN` carries
  the product. The exact mirror of `LogStep`'s `Gn` engine one level up; the telescopes
  over `i = c·2^m + j` and the `log/x` Riemann comparison are the next bricks.
  Axiom-clean; crux fields `none`.
- **`t4PoleA_eq` — `t4PoleA ≈ 9/4`, EXACT** (`Analysis/T4PoleAAssembly.lean` part 2;
  Sonine route, step 2 — the `W(t4)` campaign): the cone tent's `∫ f` pole component
  evaluates to the exact rational `9/4` — the `log 2` coefficient cancels
  (`−2 + 3/2 + 1/2 = 0`) and the rationals total `1 + 2 − 1/2 − 1/4 = 9/4`. Assembly
  through a normal form `a·log2 + q` (rational `a, q`): `Gn 2 − Gn 1 ≈ 2log2 − 1`
  (`gn21_nf`), `Gn 4 − Gn 2 ≈ 6log2 − 2` (`gn42_nf`, via `logN 4 ≈ 2·logN 2`), the
  telescoped middle `t4A23 + t4A34 ≈ −2log2 + 2`, `t4Ah ≈ (3/2)log2 − 1/2`,
  `t4Aq ≈ (1/2)log2 − 1/4`, summed by the NF kit (`ta_nf_add`/`ta_nf_smul` +
  scalar-collapse privates). First of the three `t4` slot components pinned; next:
  poleB (`= 4(log2)²`) and the archimedean tail (the dilog bracket). Axiom-clean;
  crux fields `none`.
- **`t4A12_val` + `t4A2334_val` — the `t4PoleA` assembly, part 1** (new
  `Analysis/T4PoleAAssembly.lean`; Sonine route, step 2 — the `W(t4)` campaign): the
  first *exact* piece value — `t4A12 ≈ 1` (`∫₁² (2log2 − log x) dx = 1`: the cone
  height is `Gn 2`'s own log term definitionally, so the logs cancel inside the
  piece) — and the middle-piece telescope `t4A23 + t4A34 ≈ (t4H + t4H) − (Gn 4 − Gn 2)`,
  which drops `Gn 3` (the assembly's only `log 3` carrier) without ever expanding it.
  Remaining for `t4PoleA ≈ 9/4`: expand `Gn 4 − Gn 2` through `logN 4 ≈ 2·logN 2`,
  fold in `t4Ah`/`t4Aq`, cancel the `log 2` coefficient (`6 − 8 + 3/2 + 1/2 = 0`).
  Axiom-clean; crux fields `none`.
- **`t4A12/23/34/h/q` — the `t4PoleA` pieces, constructed and evaluated** (new
  `Analysis/T4PoleAPieces.lean`; Sonine route, step 2 — the `W(t4)` campaign): the five
  interval integrals of the cone tent `t4F(x) = 2log2 − |log x|` over `[1/4, 4]`, each
  a genuine constructed `riemannIntegral` in pulled-back unit form (`x = c + t` on
  `[c, c+1]` at `c = 1, 2, 3`; `x = (1+t)/2` and `x = (1+t)/4` on the sub-unit
  intervals, the substitution constants split by `log((1+t)w) = log(1+t) + log w` —
  on `[1/4, 1/2]` the split *exactly cancels* the cone height, leaving the bare
  `∫₀¹ log(1+t)`). Piece values kernel-evaluated against the `∫log` layer:
  `2log2 − (Gn(c+1) − Gn(c))` for the three unit pieces, `(1/2)(log2 + (Gn2 − Gn1))`,
  `(1/4)(Gn2 − Gn1)`. The generic vehicles `int_const_sub_eval`/`int_const_add_eval`
  (`∫(C ∓ f) = C ∓ ∫f`, any Real constant, any modulus) and the certificate
  combinators `lip_const_sub/add`, `lip_neg` (+ congr forms) are new reusable gateway
  API. `t4PoleA` (the five-piece sum) is defined; the assembly `t4PoleA ≈ 9/4` (the
  logs cancel exactly) is the companion brick. Axiom-clean; crux fields `none`.
- **`riemannIntegral_logC1/2/3` — the `∫ log` layer, part 2c(v): the evaluation — THE
  `∫ log` LAYER IS COMPLETE** (new `Analysis/LogIntegralEval.lean`; Sonine route,
  step 2 — the `W(t4)` campaign): `∫₀¹ log(c+t) dt ≈ Gn(c+1) − Gn(c)`
  (`= (c+1)log(c+1) − c·log c − 1`), certified for `c = 1, 2, 3` on the `1`-Lipschitz
  data — the second non-rational family of certified integral evaluations (after the
  harmonic `recipC` family), and the values the five `t4PoleA` pieces consume. The
  assembly: the dyadic defect `|D_m − (Gn(c+1) − Gn(c))| ≤ (1/2^m)·hFold(c·2^m, 2^m)
  ≤ 1/2^m` (`dyadicR_gLog_defect`, from the part 2c(iv) collapse + bracket + scale
  identity, with `hFold_le_ratio`: the harmonic block is at most `M/A`); the anchor
  `D₀ = gLog c (0) ≈ log c`; the `digammaMidx` schedule (`genSum_gLog_rate`) and
  `Rlim_eval_real` — the `HarmonicLogC` template end to end. General-base engine
  `riemannIntegral_logC_gen` (Lipschitz datum a hypothesis); root witness clauses for
  the three instances; audit entries. Next: the five `t4PoleA` pieces (`[k, k+1]` at
  `c = 1, 2, 3` direct; `[1/4, 1/2]`, `[1/2, 1]` by affine substitution with the log
  constants split off), whose logs cancel to the exact `9/4`. Axiom-clean; crux
  fields `none`.
- **`riemannSum_gLog` + `Gn_scale_identity` — the `∫ log` layer, part 2c(iv): the Riemann
  sums and the scale identity** (new `Analysis/LogRiemann.lean`; Sonine route, step 2 —
  the `W(t4)` campaign): the four structural facts turning the point values and the
  `LogStep` telescopes into the dyadic rate for `∫₀¹ log(c+t) dt` — the fold
  (`RsumN_gLog`: `Σ_{i<k} gLog c (i/(N+1)) ≈ logFold(c(N+1), k) − k·log(N+1)`, `k ≤ N+1`),
  the collapse (`riemannSum_gLog`: the full sum
  `≈ (1/(N+1))·logFold(c(N+1), N+1) − log(N+1)`), the two-sided bracket
  (`logFold_le_Gn`/`Gn_le_logFold`: `ΔGn − hFold(A,M) ≤ logFold(A,M) ≤ ΔGn`, closing
  `LogStep`'s telescopes into `Rle` pairs against `ΔGn = Gn(A+M) − Gn(A)`), and the
  scale identity (`Gn_scale_identity`:
  `(1/M)·(Gn((c+1)M) − Gn(cM)) ≈ (Gn(c+1) − Gn(c)) + log M`, via `Gn_scale_expand` —
  `logN_mul_gen` driven through the antiderivative). The `− log(N+1)` of the collapse
  exactly absorbs the `+ log M` of the identity, so the Riemann sums converge to
  `Gn(c+1) − Gn(c)` with defect `(1/M)·hFold(cM,M) ≤ 1/(cM)` — the rate at the
  `digammaMidx` schedule and `Rlim_eval_real` are the next brick. Axiom-clean; crux
  fields `none`.
- **`RlogPos_ofQ_eq_logN` + `gLog_point` — the `∫ log` layer, parts 2c(ii)–(iii): the
  log-of-rational bridge and the point values** (new `Analysis/LogRatBridge.lean`,
  `Analysis/LogPointVal.lean`; Sonine route, step 2 — the `W(t4)` campaign): (2c-ii)
  `RlogPos (ofQ ⟨a,d⟩) ≈ logN a − logN d` on the band `d ≤ a ≤ 4d`, by
  **exp-injectivity** — `exp(RlogPos(a/d) + logN d) ≈ (a/d)·d ≈ a ≈ exp(logN a)`
  (`RexpReal_add`, `Rexp_log_ratQ`, `Rexp_logN`), cancelled by the general
  `RexpReal_inj_gen` (no nonnegativity side conditions, so no `logN` monotonicity
  needed); the radius certificate consumed is exactly part 2c(i)'s `radius_half_proj`,
  fed to `RlogPos_eq_Rlog` at the presented modulus `B = a/d`. No new series, no new
  integral — an identity between two already-constructed logarithms. (2c-iii) the point
  values `gLog c (j/(N+1)) ≈ logN(c(N+1)+j) − logN(N+1)` for `1 ≤ c ≤ 3`, `j ≤ N+1`,
  GENERAL in the dyadic sample — every fold of every Riemann sum of `∫₀¹ log(c+t) dt`
  routes through this single theorem: the constant-real sum collapses
  (`c + j/(N+1) ≈ (c(N+1)+j)/(N+1)`), the band clamp is inert on the sample
  (`qBandQ_eq_of_band`), `RlogPos_congr` fires at `B = c+1`
  (`radius_half_proj (c+1) 1` — the two `c ≤ 3` constraints, the modulus certificate
  and the bridge band, are the same constraint), and the bridge lands the `logN`
  difference that `LogStep`'s telescopes speak. Root witness clause added (the ∀-shape
  point-value fact); audit entries added. Remaining for `riemannIntegral_logC`: the
  `genSum` rate (the `HarmonicLogC` schedule over `Gn`'s telescopes) and
  `Rlim_eval_real` wiring. Axiom-clean; crux fields `none`.
- **`qBandQ` + `gLog` + `radius_half_of_le4` — the `∫ log` layer, parts 2a–2c(i)** (new
  `Analysis/BandClamp.lean`, `Analysis/LogIntegrand.lean`, `Analysis/LogRatCert.lean`;
  Sonine route, step 2 — the `W(t4)` campaign): (2a) the two-sided per-index band clamp
  `qBandQ a b x` (`seqₙ = min(b, max(xₙ, a))`) with the new `Qmin` suite, `1`-Lipschitz,
  congruent, inert on the band, uniform positivity witness — the totalizer manufacturing
  exactly the seq-wise facts `RlogPos`'s lemmas consume; (2b) the totalized `log`
  integrand `gLog c t = RlogPos(band_{[1,c+1]}(c+t))`, its congruence and `1`-Lipschitz
  data general in the base with decidable certificate hypotheses, and the instances
  `c = 1, 2, 3` (budgets `K_B = 42/64/90`, `K_BB = 90/280/714`, all certs by `decide`;
  the presented-radius certs provably fail for `c ≥ 5` — concrete instances are the
  design). The gateway objects `riemannIntegral (gLog c)` now construct; (2c-i) the
  uniform small-radius certificate `2(a−d)² ≤ (a+d)²` for `d ≤ a ≤ 4d`, GENERAL in the
  dyadic sample via the witness identity `(a+d)² − 2(a−d)² = (4d−a)(a−d) + ad + 3d²`
  (`ring_uor` + `Int.mul_nonneg`, no size bound) — what lets `RlogPos_eq_Rlog` fire at
  every sample of `∫₀¹ log(c+t)` uniformly. Remaining for the evaluation: the
  log-of-rational bridge (exp-injectivity assembly), the `genSum` rate from `LogStep`'s
  telescopes, `riemannIntegral_logC`. Axiom-clean; crux fields `none`.
- **`Gn_step_lower`/`Gn_step_upper` + telescopes — the `∫ log` layer, part 1** (new
  `Analysis/LogStep.lean`; Sonine route, step 2 — the engine for the `W(t4)` campaign):
  with `Gn(n) = n·log n − n` (the `log` antiderivative at integer arguments,
  `Gn_one ≈ −1`), the unit step is bracketed by the endpoint samples,
  `Gn(i) + log i ≤ Gn(i+1) ≤ Gn(i) + log(i+1)` — PURE ALGEBRA over the per-step
  logarithm bracket (`ExpBounds.lean`): multiply `1/(i+1) + log i ≤ log(i+1)` by `i+1`
  (resp. `log(i+1) ≤ 1/i + log i` by `i`) and the rational parts collapse to `1`.
  Telescoping (`Gn_tele_lower`/`Gn_tele_upper`) gives the two-sided Riemann bound
  `Gn(A) + Σ_{j<c} log(A+j) ≤ Gn(A+c) ≤ Gn(A) + Σ_{j<c} log(A+j+1)`, and the fold gap
  is bounded by the EXISTING rational harmonic fold (`logFold_gap`:
  `Σ log(A+j+1) ≤ Σ log(A+j) + hFold A c`). Since the dyadic Riemann samples of a `log`
  integrand at rational points ARE `logN` differences at integer arguments
  (`log(c + j/2^m) = logN(c·2^m + j) − logN(2^m)`), this is exactly the rate content for
  `∫₀¹ log(c+t) dt = (c+1)·log(c+1) − c·log c − 1` at defect `hFold(c·2^m, 2^m) ≤ 1/(c·2^m)`
  — part 2 wires it into the gateway. Verified target (30-digit numeric check recorded):
  `W(t4) = 9/4 + 4(log 2)² − [primes + (log 4π + γ)·2 log 2 + tail] ≈ +0.0981 > 0`, the
  sign RH demands on the cone; the tail's dilog piece (`−Li₂(−3)`) will be certified by
  brackets, not closed form. Root witness extended with the step-bracket pair (∀-clause);
  axiom-clean; crux fields `none`.
- **`t4Test` + `t4PrimePart_eq` — THE FIRST CONE-SHAPED TEST DATUM WITH A LIVE PRIME SIDE**
  (new `Square/ConeTent.lean`; Sonine route, step 2 — toward the autocorrelation cone): the
  square-scale symmetric log-tent `t4F(x) = 2·log 2 − |log x|` on `[1/4, 4]` realized as a
  genuine `WeilTest` (`X = 4`). The key unblocking observation: in the log variable the
  test is the autocorrelation of the box on `[−log 2, log 2]` — the box with RATIONAL knots
  `[1/2, 2]` in `x` — so at SQUARE scales `X = c²` the `√2` obstruction (recorded against
  the scale-2 tent, generating box knots `2^{∓1/2}`) vanishes. The datum is log-valued at
  rational points (`f(a/b) = 2·log 2 ∓ (log a − log b)`), which `WeilTest.f : Q → Real`
  carries natively; `f(1) = 2·log 2 > 0` (`t4F_one`) is the on-cone marker `∫|g|²` that the
  off-cone bump lacked. The finite-place side is EVALUATED in closed form
  (`t4PrimePart_eq`): `primes(t4) ≈ log 2·(3/2·log 2) + log 3·(4/3·(2·log 2 − log 3))`
  `≈ 1.1421` — the prime `2` enters with the test's own log-weight (`Λ(2)·f(2) = (log 2)²`),
  the prime `3` through the symmetric pair `f(3) = f(1/3)`, and the `Λ(4) = log 2` term
  dies on the knot `f(4) = 0` by `log`-multiplicativity. HONEST SCOPE: datum + prime side
  only — the slot integrals need the certified `∫ log` layer (not yet built), and the exact
  CC weight normalization of the cone element is deliberately not asserted (`t4F` is
  claimed as the log-coordinate autocorrelation shape only). Root witness extended with
  `t4F_one` and `t4PrimePart_eq`; axiom-clean; crux fields `none`.
- **`bumpSlot` + `bumpWeilValue_neg` — THE FIRST REALIZED SLOT WITH A LIVE PRIME SIDE, and
  the first certified NEGATIVE Weil value: `W(bump) < 0`** (new `Analysis/BumpPieces.lean` +
  `Square/BumpSlot.lean`; Sonine route, step 2 — the frontier past the prime-free window):
  the off-center tent with knots `1, 2, 3` (peak AT the prime `2`) is realized as a genuine
  `WeilTest` (`bumpF : Q → Real`, `X = 3` — the first test whose support MEETS the primes;
  it is the genuine function whose consumed evaluations `demoWeilTest` records), and its
  `WeilSlot` is inhabited with every field a kernel-evaluated integral: poles
  `= bumpPoleA + bumpPoleB ≈ 1 + (3·log 3 − 4·log 2)` (`bump_pieceA1/A2` the affine edges,
  `bump_pieceB1/B2` the `f̃(0)` pieces `1 − 1/x` and `3/x − 1` through the reciprocal
  bridges), archimedean tail `= bumpArchTail ≈ 6·log 2 − 3·log 3` — COMPACT for this test:
  `f(1) = 0` kills both the `(2/x)f(1)` subtraction and the improper remainder, and the
  PV-cancelled integrand reduces by exact rational algebra (`x/(x+1) = 1 − 1/(x+1)` on
  `[1,2]`; partial fractions `−1 + 1/(x−1) + 2/(x+1)` on `[2,3]`, consuming the base-3
  bridge `∫₀¹ dx/(3+x) ≈ log 4 − log 3`). The finite-place side is NONZERO
  (`bumpPrimePart_eq ≈ log 2` — the prime `2` enters the assembled functional through the
  peak, `Λ(3)` dying on the right knot), the archimedean constant vanishes (`f(1) = 0`),
  and the value reduces to closed form (`bumpWeilValue_eq`):
  `W(bump) = 1 + 6·log 3 − 11·log 2 ≈ −0.0329`. **`bumpWeilValue_neg` certifies
  `W(bump) < 0`** via the harmonic wedges at `M = 128` (`bmp_L2`/`bmp_U32`/`bmp_L43`;
  worst-case wedge error `7/256 ≈ 0.027` against margin `0.033`, realized margin `≈ 0.024`;
  one closing bignum `decide`). WHAT THE SIGN MEANS: the Weil criterion is positivity on
  the AUTOCORRELATION cone `g ⋆ g^τ`, and the bump is admissible but NOT an autocorrelation
  (`f(1) = ∫|g|² = 0` forces `g = 0`) — so a certified `W < 0` is CONSISTENT with RH and is
  the honest counterpart of `tentWeilValue_pos`: kernel-checked proof that Weil positivity
  is NOT a pointwise feature of the admissible class — the `f, f̂` coupling structure
  (Sonine steps 3–4) is load-bearing. The cancellation-not-magnitude finding (`α(2) < 0`,
  `arch(1) < 0`), now at the level of the assembled functional. Root witness extended with
  both facts; axiom-clean; crux fields `none`.
- **`tentSlot` + `tentWeilValue_pos` — THE FIRST REALIZED WEIL SLOT, and the first realized
  window-positivity instance: `W(tent) > 0`** (new `Square/TentSlot.lean`; Sonine route,
  step 2 boundary crossed for one genuine test): `Pairing.lean`'s `WeilSlot` interface is
  INHABITED with every field a kernel-evaluated constructed integral — the tent test datum
  `tentF : Q → Real` (piecewise-linear, knots `1/2, 1, 2`, Bombieri-admissible, support
  proofs kernel-checked), poles `= tentPoleA + tentPoleB ≈ 3/4 + log 2`, archimedean tail
  `= tentArchTail ≈ −1 − 6·log 2 + 3·log 3`. The finite-place side VANISHES
  (`tentPrimePart_eq` — the `X = 2` prime-free window realized: the knots sit exactly at
  the prime-2 evaluation points), the archimedean constant collapses (`f(1) = 1`), and the
  Weil functional reduces to closed form (`tentWeilValue_eq`):
  `W(tent) ≈ (3/4 + log 2) − ((log 4π + γ) + (−1 − 6·log 2 + 3·log 3))
   = 7/4 + 7·log 2 − 3·log 3 − log 4π − γ ≈ +0.198`. **`tentWeilValue_pos` certifies
  `W(tent) > 0`** — rational brackets for `log 2` and `log 3 − log 2` come from the
  harmonic wedges at `M = 32` (`tent_L2`/`tent_U32`/`tent_L32`/`tent_L3`: the fold values
  are exact rationals with ~10⁵⁰-digit-product denominators; ONE closing `decide` performs
  the bignum arithmetic), `log 4π`/`γ` from the standing brackets. This is what
  window-supported Weil positivity LOOKS like when realized — one test, one certified sign;
  the pairing-family positivity (`∀` tests) remains the crux and is RH. Axiom-clean; crux
  fields `none`.
- **`tentArchTail_eq` — the tent's full archimedean tail ≈ `−1 − 6·log 2 + 3·log 3`: THE
  THIRD EVALUATED WEIL-SLOT COMPONENT, completing all three tent slot fields** (new
  `Analysis/TentArchTail.lean`; Sonine route, step 2): the improper part past the support,
  `∫₁^∞ (1/w − 1/(w+2)) dw = ∫₂^∞ 2/(x²−1) dx ≈ log 3` (`improperTail_eq`), is the FIRST
  EVALUATED `improperIntegral1` — a certified half-line integral reduced in the kernel. Each
  unit block `T m = ∫_{m+1}^{m+2} hTail` is two instances of the general-base bridge
  (`integralTerm_hTail : T m ≈ [log(m+2)−log(m+1)] − [log(m+4)−log(m+3)]`); the `K = 3`
  decay hypothesis comes from the per-step logarithm bracket (`T m ∈ [1/(m+2) − 1/(m+3),
  1/(m+1) − 1/(m+4)] ⊆ [0, 3/((m+1)m)]`, `tail_decay`); the partial sums TELESCOPE
  (`genSum_hTail : Σ_{i<N} T i ≈ (log(N+1) − log 1) − (log(N+3) − log 3)`, a three-line
  additive rearrangement per step, `tail_step_alg`); the defect `log(N+3) − log(N+1) ≤
  2/(N+1)` (the bracket twice) beats the schedule `digammaMidx 3 j = 4(j+1)`, and
  `Rlim_eval_real` evaluates the limit. Assembled: `tentArchTail = tent_arch12 −
  improperTail ≈ −(1 + 2·log 2 − 4·(log 3 − log 2)) − log 3 = −1 − 6·log 2 + 3·log 3`.
  With `tentPoleA_eq` (3/4), `tentPoleB_eq` (log 2), and `weilArchConst` already
  constructed, ALL `WeilSlot` interface fields for the tent test are now kernel-evaluated —
  the realized slot instance and `weilValue` are the next (assembly) brick. Axiom-clean;
  crux fields `none`.
- **`riemannIntegral_recipC` — the GENERAL-BASE harmonic bridge: `∫₀¹ dx/(c+x) ≈
  log(c+1) − log c` for EVERY natural base `c ≥ 1`** (new `Analysis/HarmonicLogC.lean`;
  Sonine route, step 2): the `HarmonicLog32` construction with the base as a parameter —
  left sums are `H_{(c+1)M} − H_{cM}`, the wedge telescopes `cM → (c+1)M` with width
  `1/(c(c+1)M)` (both cancellations by `logN_mul_gen`), anchor `D₀ = 1/c`. This is the
  block engine the improper archimedean tail needs: `∫₂^∞ −2/(x²−1) dx = −log 3` is a
  `genSum` of unit blocks `∫_{m+1}^{m+2}(1/w − 1/(w+2))` (`ImproperIntegral.lean`), and each
  block is `[log(m+2)−log(m+1)] − [log(m+4)−log(m+3)]` — two instances of this theorem;
  the partial sums telescope to `log 3 − (log(N+3) − log(N+1))` with defect `≤ 2/(N+1)` by
  the per-step bracket, so `Rlim_eval_real` will close the tail. Wired into the root witness
  as a universally-quantified clause (`∀ c ≥ 1`). Axiom-clean; crux fields `none`.
- **`tent_arch12` — the archimedean tail's compact `[1,2]` piece ≈ `−1 − 6·log 2 + 4·log 3`,
  and general log-additivity** (new `Analysis/HarmonicLog32.lean`,
  `Analysis/TentArchPiece.lean`; Sonine route, step 2): the PV-cancelled tail integrand on
  the tent's support, `∫₁² −(1 + 2/x − 4/(x+1)) dx`, is CONSTRUCTED (floor-1 clamp only —
  `x ≥ 1`, `x+1 ≥ 2` on the domain) and EVALUATED:
  `≈ −(1 + 2·log 2 − 4·(log 3 − log 2))`. The new core is
  **`riemannIntegral_recip32`: `∫₀¹ dx/(2+x) ≈ log 3 − log 2`** — the base-`2M` harmonic
  bridge (left sums are `H_{3M} − H_{2M}`, the wedge telescopes the per-step bracket from
  `2M` to `3M` with width `1/(6M)`), whose only new analytic input is
  **`logN_mul_gen`: `log(k·m) = log k + log m`** (the `logN_mul` doubling proof at an
  arbitrary factor, via `exp` injectivity — `HarmonicLog`'s folds and telescopes were
  already general in base and count). The pullback is pointwise congruent to
  `−(1 + 2·gRecip − 4·gRecip32)` (`tent_arch_pull`) and gateway linearity reduces the value
  to the two certified reciprocal integrals. Remaining for the full tail
  `−1 − 6·log 2 + 3·log 3`: the improper piece past the support,
  `∫₂^∞ −2/(x²−1) = −log 3`. Axiom-clean; crux fields `none`.
- **`tentPoleB_eq` — the tent's `f̃(0)` component ≈ `log 2`: THE SECOND EVALUATED WEIL-SLOT
  COMPONENT, and the first integral evaluation to a NON-RATIONAL value** (new
  `Analysis/ExpBounds.lean`, `Analysis/HarmonicLog.lean`, `Analysis/TentLogPiece.lean`;
  Sonine route, step 2): the tent test's `∫₀^∞ f(x)/x dx` pole part is CONSTRUCTED as two
  certified interval integrals and EVALUATED in the kernel:
  `∫_{1/2}^{1}(2 − 1/x) + ∫_{1}^{2}(2/x − 1) ≈ (1 − log 2) + (2·log 2 − 1) = log 2`.
  With `tentPoleA_eq` this completes the tent's pole block `f̃(1) + f̃(0) = 3/4 + log 2`.
  The chain, bottom-up: (i) **`ExpBounds.lean`** — the series bounds `1 + q ≤ exp q`
  (`RexpReal_ofQ_ge_one_add`) and the exact geometric cap `exp(1/(e+1)) ≤ (e+1)/e`
  (`RexpReal_unit_le`, strengthened-induction closed form `expSum_unit_le_geom`), giving the
  **per-step logarithm bracket** `1/(i+1) ≤ log(i+1) − log i ≤ 1/i` (`logN_step_lower/upper`,
  via `RexpReal_reflects_le` — the constructive derivative of `log` at the integers);
  (ii) **`HarmonicLog.lean`** — the telescoped wedge `log 2 ≤ Σ_{j<M} 1/(M+j) ≤ log 2 + 1/(2M)`
  (`log2_le_hFold`/`hFold_le_log2_add`, through `logN_mul` and the exact telescoping defect
  `hFold_eq_hFoldLo`), the harmonic Riemann-sum identity `R_N(1/(1+t)) = Σ_{j<M} 1/(M+j)`
  (`riemannSum_gRecip`, per-point `clampedInv` evaluation + ℚ-fold), the new limit engine
  `Rlim_eval_real` (rate-convergent Bishop limits evaluate to a REAL target — `Rlim_eval`
  generalized, one extra regularity step of the target), and the headline
  **`riemannIntegral_recip`: `∫₀¹ dx/(1+x) ≈ log 2`** — the constructive
  fundamental-theorem step for `1/x`; (iii) **`TentLogPiece.lean`** — the two tent pieces
  totalized with the FLOOR-1 clamp only (on `[1/2,1]` via `1/x = 2·(1/(2x))`, `2x ∈ [1,2]` —
  no second clamp floor, no scaling identity), affine pullbacks POINTWISE congruent to
  `2 − 2·gRecip` and `2·gRecip − 1` (`tent_pull1/2`), evaluated by gateway linearity
  (`_const/_smul/_neg/_add`) over `riemannIntegral_recip`, assembled in `tentPoleB_eq`.
  Also: order helpers (`Rsub_le_of_le_Radd`, `Radd_le_cancel_right`, `Rsub_shift_drop`,
  `Rneg_involutive`, `Rmul_two_eq`). Root witness extended with `riemannIntegral_recip` and
  `tentPoleB_eq`. Axiom-clean; crux fields `none`; RH open.
- **`clampedInv` — the clamped-reciprocal gadget: the totalized `1/x` integrand** (new
  `Analysis/ClampedInv.lean`; Sonine route, the recorded next brick after `tentPoleA_eq`):
  `clampedInv a x := 1/max(x, a)` (rational floor `a > 0`) is a genuine TOTAL function of `x`
  carrying exactly the certified-integration gateway's data — congruence (`clampedInv_congr`),
  the globally-Lipschitz bound with the RATIONAL constant `(1/a)²` (`clampedInv_lipschitz`),
  non-negativity, inertness `≈ 1/x` on `[a, ∞)` (`clampedInv_eq_of_ge`), and seq-exact rational
  evaluation `clampedInv a (ofQ q) ≈ ofQ (1/q)` for `q ≥ a` (`clampedInv_ofQ`, via the new
  `Rinv_ofQ`). The design resolves `Rinv`'s witness-as-data obstruction to totality: the
  per-index clamp `qClampQ a x` (seq `n ↦ max(xₙ, a)`, the floor-`a` generalization of
  `qClampOne`; `1`-Lipschitz via `Qmax_const_lip`, inert on `[a,∞)`) keeps the argument `≥ a`
  at EVERY index, so ONE witness (`k = 2·a.den`, `Qbound_lt_pos`) serves every `x`
  (`qClampQ_witness`). The reciprocal side is fully algebraic over the `Rinv` laws — no
  per-index reasoning about `Rmul`'s reindex: the Real-level difference identity
  `1/u − 1/v ≈ (v−u)·((1/u)·(1/v))` (`Rinv_sub_Rinv`), the floor cap `1/u ≤ 1/a`
  (`Rinv_le_ofQ_inv`), and the two-leg absolute assembly (`Rinv_abs_lipschitz`, the
  `Rlog_abs_lipschitz` pattern). Plus `lip_mono` (Lipschitz-modulus upgrade, for aligning
  the shared `L` that `riemannIntegral_add` requires) and `Qlt_of_Qlt_Qle`. With this,
  partial fractions reduce every remaining tent-slot integrand (`2 − 1/x`,
  `−(1 + 2/x − 4/(x+1))`, the shifted tail `−2/(u(u+2))`) to affine combinations the gateway
  integrates. Wired into the root witness (`F1Square.lean`): the `(1/a)²` Lipschitz datum at
  `a = 1/2` and the evaluation `clampedInv (1/2) 2 ≈ 1/2`. Axiom-clean; crux fields `none`.
- **`tentPoleA_eq` — THE FIRST EVALUATED WEIL-SLOT COMPONENT** (new
  `Analysis/AffineIntegral.lean`; Sonine route, step 2 boundary moving): the tent test
  (piecewise-linear, knots `1/2, 1, 2` — the `X = 2` prime-free window, all prime-side
  evaluations vanishing) has its `∫₀^∞ f(x) dx` pole part CONSTRUCTED as certified interval
  integrals AND evaluated in the kernel:
  `∫_{1/2}^{1} (2x−1) dx + ∫_{1}^{2} (2−x) dx ≈ 1/4 + 1/2 = 3/4` (`tent_piece1`/`tent_piece2`/
  `tentPoleA_eq`) — a `WeilSlot` interface integral reduced, not carried as data. Built on the
  new affine evaluation layer: `lip_const`/`lip_scaled`/`lip_affine` (Lipschitz data for any
  modulus dominating the slope), `riemannIntegral_scaled` (`∫₀¹ q·x = q/2`),
  `riemannIntegral_affine` (`∫₀¹ (α + qx) = α + q/2`), `affine_pullback_eq` (the interval
  pullback of an affine map is affine), and the schedule-general `riemannIntegral_id_gen`
  (the value `1/2` for EVERY valid Lipschitz datum — the L-irrelevance the `smul` route
  needs). RECORDED for the next brick: the tent's remaining components (`f̃(0) = log 2`, the
  archimedean tail `−1 − 6log2 + 3log3`) have rational-function integrands
  (`2 − 1/x`, `−(x²−x+2)/(x(x+1))`, `−2/(x²−1)` past support — the PV singularity cancels
  exactly against the `f(1)`-subtraction); their construction needs a globally-Lipschitz
  clamped-reciprocal gadget over `Rinv` (the `RmaxZero` clamp keeps the argument `≥ a > 0`
  pointwise, so the `Rinv` witness is uniform). Axiom-clean; crux fields `none`.
- **`riemannIntegral_id` — `∫₀¹ x dx ≈ 1/2`, the first NON-CONSTANT certified integral
  evaluation, and `Rlim_eval`, the limit-evaluation engine** (new `Analysis/IntegralEval.lean`;
  Sonine route, step 1): the Weil pairing's interface fields are integrals whose
  piecewise-polynomial closed forms are "routine but unverified in print" (`Weil.lean`) —
  reducing them in the kernel bottoms out in evaluating the gateway's integrals on explicit
  integrands, and the gateway had only `riemannIntegral_const`. Now built: `Rlim_eval` (a
  Bishop limit whose terms sit within `1/(j+1)` of a rational `c` IS `ofQ c` — proof at the
  diagonal, where the rate hypothesis at index `m = 2n+1` lands the `Radd`-inflated sample
  exactly on the limit's `4n+3` approximant), the `ℚ`-level Gauss fold `sumIota`,
  `riemannSum_id` (`R_N(id) = N/(2(N+1))`), `genSum_id_eval`/`genSum_id_rate` (the telescoped
  dyadic sums sit within `1/(2·2^M)` of `1/2`), and the evaluation itself. With the existing
  `_const`/`_add`/`_smul`/`_neg` linear API, every piecewise-LINEAR integrand now evaluates in
  closed form over rational intervals — the stratum the tent-window Weil tests live in; the
  realized `WeilSlot` (tent test, `X = 2`, prime-free window) is the recorded next brick.
  Mechanization note: a flipped `Req_symm` on an `Rneg_ofQ` congruence sent the unifier into
  structure-eta defeq on symbolic-`2^M` rationals (a `whnf` timeout) — congruence direction
  matters even between defeq-close terms. Axiom-clean; crux fields `none`.
- **`Rlambda3_lt_Rlambda4` — `λ₃ < λ₄`, the Li head certified strictly increasing through
  `n = 4`, and `convexClass3_pruned` — THE FIRST KILL AT ORDER 3** (new
  `Analysis/LambdaFourThreeGap.lean`): `λ₄ − λ₃ ≥ 0.035` (true `0.178`). The route is the
  DIFFERENCE, not the endpoints: bounding `λ₄` below and `λ₃` above separately fails
  (`0.2185 < 0.2486`) because each `ηⱼ` bracket width is then paid twice, and at binomial
  weights `3..6` that doubling swamps the true gap. The archimedean sides ARE cheap separately
  (cost `≈ 0.008`, since the constant `1` cancels exactly and the `ζ` weights are small), so only
  the arithmetic side needs an identity — `lambda4_arith_split`:
  `λ₄^{arith} − λ₃^{arith} = −(η₀ + 3η₁ + 3η₂ + η₃)`, obtained from the `nsmulR` splits
  (`nsmulR6_split`, `nsmulR4_split_left`) plus ONE 7-atom `RsumL` rearrangement whose
  permutation is built STRUCTURALLY from `List.Perm.swap`/`cons`/`trans` (`decide` on
  `List.Perm` is barred — it pulls `Classical.choice`). Two supporting brackets: the TIGHT
  `reta3_le_t` (`η₃ ≤ 0.0462725`, on `γ₃ ≤ 1/40` and `γ₂ ≤ −0.003`; the stock `reta3_le`'s
  `0.145303` rests on the loose `γ₃ ≤ 1/8` and is far too weak) and `genuineArchSeq4_ge_t`
  (`arch(4) ≥ −1.024325`, the `ζ(3) ≤ 1.205` sharpening of the stock `−1.066325`, which misses
  by `0.042`). `convexClass3_pruned` then kills the order-3 convex class — unreachable by the
  contraction lever, whose order-3 form is true by only `1.3%`, whereas the convex lever needs
  just `λ₃ < λ₄`, a `34%` margin. Axiom-clean; crux fields `none`, RH open.
- **`convexClass12_pruned` / `convex_lamRec_fails` — the CONVEX-COMBINATION lever (sixth prune),
  general in the order** (`Square/GateAFiniteList.lean`): non-negative coefficients with
  `Σ aᵢ ≤ 1` cap `s K` by the maximum of the window (`convex_cap`, stated for arbitrary `K`), so
  a sequence strictly exceeding that maximum kills the class. Against the doubled Li sequence the
  numeric input is only `λ_K < λ_{K+1}` — certified at `K = 1, 2` by `Rlambda_head_increasing` —
  instead of the contraction lever's far heavier `λ_{K+1} > λ₁ + … + λ_K`. Supporting substrate:
  `RsumN_mul_right`, `Rle_Rsub_zero_of_Rle`, `Rsub_double`/`Pos_Rsub_double` (a strict gap
  doubles). RECORDED for the next session: the `K = 3` instance is a one-liner once
  `Pos (λ₄ − λ₃)` is certified, and an exact rational check confirms
  **`λ₄ − λ₃ ≥ 0.047033` is already reachable from brackets IN STOCK** through the difference
  identity `λ₄ − λ₃ = γ − 3η₁ − 3η₂ − η₃ − ½(γ+log4π) + (9/4)ζ(2) − (21/8)ζ(3) + (15/16)ζ(4)`;
  the outstanding work is purely the additive-cancellation mechanization (a 7-atom `RsumL`
  rearrangement after `nsmulR` splitting — note `decide` on `List.Perm` is barred, it pulls
  `Classical.choice`). Bounding `λ₄` and `λ₃` separately does NOT suffice (`0.2185 < 0.2486`):
  it pays each `η` bracket width twice, which is exactly what the difference avoids.
- **`gateA_prune_ledger` — the Gate-A prune ledger as one kernel-checked statement, plus two
  new order-uniform kills** (`Square/GateAFiniteList.lean`):
  - **`nonPositiveClass_pruned` (fifth prune, uniform in the order)**: no Gate-A finite list has
    ALL coefficients `≤ 0`, at EVERY order `K = 1..4` — for every η₄-anchored η-data, rule, and
    dimension. Unlike the contraction prunes this needs NO numerics: a combination of
    non-negative terms with non-positive coefficients is non-positive (`RsumN_nonpos`), while
    every doubled Li value in reach is strictly positive. The general core
    (`nonPositive_lamRec_fails`) is stated for arbitrary `K`; the `K ≤ 4` ceiling is exactly the
    reach of the certified `Pos λₙ` rungs, so each future rung widens this prune by one order
    for free.
  - **`orderZeroClass_pruned`**: the degenerate order `K = 0` is dead for free (the empty
    recurrence forces `2λₙ ≈ 0`, refuted by `Pos λ₁`).
  - **`gateA_prune_ledger`** bundles all four killed classes and records the surviving space:
    order `2` with an expanding coefficient, orders `3, 4` with some positive coefficient, and
    every order `K ≥ 5`.
  - RECORDED BOUNDARY (so the route is not re-attempted): the contraction lever
    `λ_{K+1} > λ₁ + … + λ_K` is TRUE at `K = 1, 2`, true-but-razor-thin at `K = 3`
    (`0.3858` vs `0.3230`, needing the `λ₄` lower to ~1% of truth), and **FALSE from `K = 4`**
    (`λ₅ ≈ 0.518 < λ₁+λ₂+λ₃+λ₄ ≈ 0.7088`) — mathematically exhausted, not under-certified.
  Axiom-clean; crux fields `none`, RH open.
- **`Rlambda_head_increasing` — the certified Li head is STRICTLY INCREASING** (`λ₁ < λ₂ < λ₃`,
  `Analysis/LambdaTwoThreePrecision.lean`): `Rlambda1_lt_Rlambda2` (gap `≥ 0.05589`) and
  `Rlambda2_lt_Rlambda3` (gap `≥ 0.042`), from the now-disjoint brackets. Sharpens
  `Rlambda1_ne_Rlambda2` from *distinct* to *ordered*, and is the shape the cheaper
  convex-combination prune consumes (`Σaᵢ = 1, aᵢ ≥ 0` forces `λ_{K+1} ≤ λ_K`); extending it to
  `λ₃ < λ₄` needs a `λ₄` lower above `0.2554` — blocked on the `γ₁` bracket, whose 12%-wide
  spread dominates the `η₁` slack at coefficient `6`.
- **`Rlambda4_le` — the `λ₄` UPPER bracket (`λ₄ ≤ 0.563`), the fourth two-sided Li
  coefficient** (new `Analysis/LambdaFourUpper.lean`): `λ₄^{arith} = −(4η₀+6η₁+4η₂+η₃) ≤
  1.5458115` via the `η₃` floor `η₃ ≥ −0.0313379`, which needed four product LOWER bounds —
  each the `ge`-mirror of a stock upper: `Rgamma_pow4_ge` (`γ⁴ ≥ 0.577⁴`),
  `Rgamma_sq_gamma1_ge` (`γ²γ₁ ≥ 0.578²·(−0.0762)`, mixed sign), `Rgamma1_sq_ge`
  (`γ₁² ≥ 0.0677²`, via the double-negation square identity), `Rgamma_gamma2_ge`
  (`γγ₂ ≥ 0.578·(−0.014)`); and `arch(4) = 1 − 2(γ+log4π) + (9/2)ζ(2) − (7/2)ζ(3) +
  (15/16)ζ(4) ≤ −0.9828225` (`genuineArchSeq4_le`, the third `log 4π`-lower consumer). True
  value `λ₄ ≈ 0.385812`. The `λ₅` upper — the last 3×3-Hankel ingredient for the order-2
  expansion kill — runs through the unbuilt `γ₄` upper, the next numeric campaign.
  Axiom-clean; crux fields `none`, RH open.
- **`contractionClass2_pruned` — the order-2 CONTRACTION class is dead (fourth prune)**
  (`Square/GateAFiniteList.lean`): no Gate-A finite list exists at order 2 with BOTH
  coefficients `≤ 1` (any reals), for every η₂-anchored η-data, rule, and dimension — the
  recurrence forces `2λ₃ ≈ a₀·2λ₁ + a₁·2λ₂ ≤ 2λ₁ + 2λ₂ ≤ 0.25082`, refuted by
  `2λ₃ ≥ 0.2872` (witness `n = 100`). Contains the canonical shift class `(0, 1)`
  (period-one-from-`n = 2` diagonals). The doubled Li sequence certifiably outruns any
  sub-unit combination of its two predecessors: `λ₁ + λ₂ ≤ 0.12541 < 0.1436 ≤ λ₃`.
  Surviving order-2 candidates need a coefficient `> 1`; their kill (the 3×3 Hankel
  determinant on `λ₁..λ₅`) needs `λ₄, λ₅` uppers — the `γ₄`-upper campaign. Axiom-clean;
  crux fields `none`.
- **`Rlambda2_le` / `Rlambda3_ge` — the third two-sided Li coefficient and the tightened `λ₃`
  lower** (new `Analysis/LambdaTwoThreePrecision.lean`): `λ₂ ≤ 1016/10⁴` (true `0.0923457`;
  the `log 4π`-lower consumer, joining `Rlambda2_pos`/`Rlambda2_ge` — λ₂ two-sided), and
  `λ₃ ≥ 1436/10⁴` (true `0.207639`; the stock positivity lower was `0.0584`): arithmetic side
  tightened to `λ₃^{arith} ≥ 1.173914` (`Rlambda3_arith_ge_t`, via `reta1_le4`,
  `Rgamma_cube_ge`, the sharp `Rgamma_gamma1_ge`, `Rgamma2_ge_neg0014`), archimedean side
  reused (`archLoR_le`). Axiom-clean; crux fields `none`.
- **`order1Class_pruned` — the ENTIRE order-1 candidate family is dead (third prune)**
  (`Square/GateAFiniteList.lean`): for every η-data anchored through `η₂` (`StieltjesEta3`),
  every atlas rule, every dimension, and EVERY real coefficient `c`, no Gate-A finite list of
  order 1 exists. The two one-step relations at `n = 0, 1` force the coefficient-free product
  identity `(2λ₂)² ≈ (2λ₃)(2λ₁)` (associativity/commutativity eliminate `c`), and the certified
  brackets refute it outright: `(2λ₂)² ≥ 0.1594² = 0.02540836 > 0.02432430 ≥ 0.5108·0.04762 ≥
  (2λ₃)(2λ₁)` (via `Rlambda2_ge`, `Rlambda3_le`, `Rlambda1_le`; refuted at witness index
  `n = 2000` through the new `not_Rle_ofQ_of_witness`). Subsumes both earlier order-1 prunes on
  η₂-anchored data, and records the structural law: order-K classes consume the first K+1 λ's
  (anchors through `η_K`). The surviving Gate-A candidate frontier is order `K ≥ 2`.
  Axiom-clean; crux fields `none`, RH open.
- **`Rlambda3_le` — the `λ₃` UPPER bracket (`λ₃ ≤ 0.2554`), the second two-sided Li
  coefficient** (new `Analysis/LambdaThreeUpper.lean`): consumes the fresh `log 4π` lower
  (`arch(3) = 1 − (3/2)(γ+log4π) + (9/4)ζ(2) − (7/8)ζ(3) ≤ −1.008445`, `genuineArchSeq3_le`)
  and two forced sharp ingredients on the arithmetic side (`λ₃^{arith} = −(3η₀+3η₁+η₂) ≤
  1.2638249`, `Rlambda3_arith_le`): the MIXED-SIGN product upper `γγ₁ ≤ 0.577·(−0.0677) =
  −0.0390629` (`Rgamma_gamma1_le` — its negativity is load-bearing; the two-sided abs bound
  `|γγ₁| ≤ 0.044` overshoots the kill budget by 0.25) and the tight `γ₂ ≤ −3/1000`
  (`Rgamma2_le_neg0003`, v0.22). Plus `Rgamma_cube_le` (`γ³ ≤ 0.578³`) and the named
  `Rlambda2_ge` (`λ₂ ≥ 0.0797`, from the LambdaGap atoms). True values: `λ₃ ≈ 0.207639`,
  `λ₂ ≈ 0.0923457`. Axiom-clean; crux fields `none`.
- **`contractionClass_pruned` — the SECOND candidate class killed: the entire contraction class**
  (`Square/GateAFiniteList.lean`): no Gate-A finite list exists with order 1 and ANY real
  coefficient `c ≤ 1`, for every anchored η-data, rule, and dimension — `lamRec` forces
  `2λ₂ ≈ c·2λ₁ ≤ 2λ₁` (via `satisfiesRec_order1_step`, `Pos λ₁`, and `Rmul` monotonicity),
  clashing with the certified gap through the new order-clash lemma `not_Pos_of_Rnonneg_Rneg`
  (`Pos z` and `Rnonneg (−z)` are contradictory at the approximant level) and
  `lambda_gap_pos_double` (`Pos (2λ₂ − (λ₁+λ₁))`, from `lambda_gap_pos` via
  `Rlambda1_double_eq`). Strictly generalizes `constantClass_pruned` (`c = 1`): the doubled Li
  sequence certifiably EXPANDS at its first step, so no non-expanding order-1 rule can carry the
  Gate-A diagonal. The surviving order-1 candidates are the strict expansions `c > 1`; their kill
  (`λ₃λ₁ vs λ₂²`) needs a `λ₃` upper — the next bracket. Axiom-clean; crux fields `none`.
- **`Rlog4pic_ge` — the `log 4π` LOWER bracket (`log 4π ≥ 2.53038`) and the first TWO-SIDED Li
  coefficient (`Rlambda1_le : λ₁ ≤ 0.02381`)** (new `Analysis/LogFourPiLower.lean`): the substrate
  carried only upper log brackets (built for the λ-positivity proofs) plus the crude `log π ≥ 1`;
  every λ UPPER bound — what the next Gate-A prunes consume — needs `log 4π` from below. Built:
  `artSum_le_base` (NEW substrate lemma — artanh partial sums are monotone in the base, via
  `qpow_le_base`), `Rpi_seq_ge_314` (every Machin approximant `≥ 3.14`, the depth-6 sharpening of
  `Rpi_seq_ge_three`: `arctan(1/5) ≥ 0.197354`, `arctan(1/239) ≤ 0.004226`, tail `(1/2)¹⁵`),
  `tmap_ge_314` (`q ≥ 3.14 ⟹ tmap q ≥ 107/207`, exactly `tmap(3.14)`), hence
  `RpiTmap ≥ 107/207` pointwise; then `log 2 ≥ 2·artSum(1/3,8) ≥ 0.69314` (`Rlog2c_ge_69314`) and
  `log π ≥ 2·artSum(107/207,5) ≥ 1.1441` (`Rlogpic_ge_11441`, base- then depth-monotonicity
  through the artanh diagonal), assembling to `log 4π ≥ 253038/10⁵` (true `2.531024`; upper
  companion `2.5316`). From it `2λ₁ ≤ 0.04762` (`Rtwolambda1_le`) and `λ₁ ≤ 2381/10⁵`
  (true `0.0230957`) — with `Rlambda1_pos` the first Li coefficient is bracketed two-sidedly.
  Axiom-clean; crux fields `none`, RH open.
- **`GateA_of_finiteList` — the Gate-A finite-list template (certificate front, workstream 2)**
  (new `Square/GateAFiniteList.lean`): Gate A specified as a finite exact hypothesis list around a
  generating recurrence, exactly as the certificate front prescribes — fix `D`, an order `K` and
  coefficients `a`, and require the `K` base identities `gramOf ι D (1+i) (1+i) ≈ 2λ_{1+i}`, the
  order-`K` recurrence on the embedding's squared-norm diagonal (`gramRec`), and the SAME
  recurrence on the doubled genuine Li sequence (`lamRec`) — bundled as `GateAList`. The reduction
  theorem `GateA_of_finiteList` proves the list implies `RealizesDiag` (hence, Gate B being free,
  `LiNonneg (genuineLamSeq)` — `finiteList_is_liNonneg`, the honest ledger: a satisfied list IS the
  crux content, and satisfiability is NEVER asserted). Engine: `linRec_unique` — two sequences
  under one order-`K` linear recurrence over the constructive reals with `≈`-equal initial window
  coincide (course-of-values induction, fully kernel-checked). Two-sided guards in the
  `GateA.lean` discipline: `finiteList_satisfiable` (at the template square the constant rule
  passes the WHOLE list and the reduction delivers `RealizesDiag` end to end) and
  `finiteList_can_fail` (the zero rule satisfies both recurrences yet its base identity is
  refuted — the base carries content). Every candidate `(ι, D, K, a)` is henceforth checked
  against this one list. Axiom-clean; crux fields `none`, RH open.
- **`constantClass_pruned` — the first candidate class killed through the template (workstream 1
  record)**: the order-1 constant class `(K, a) = (1, 1)` — every rule whose Gate-A diagonal is
  period-one from `n = 1` — is refuted for EVERY anchored η-data, every atlas rule `ι`, and every
  dimension `D` at once: its `lamRec` forces `2λ₂ ≈ 2λ₁` (`constantClass_lamRec_fails`, via
  `satisfiesRec_const_step` + `Rdouble_inj`), contradicting the certified gap. One finite
  certified fact kills the infinite class — the template doing its prune job.
- **`Rlambda1_ne_Rlambda2` — the first certified SEPARATION of two Li coefficients** (new
  `Analysis/LambdaGap.lean`): `2λ₂ − 2λ₁ ≥ 1130/10⁴ = 0.113` (`lambda_gap_lower`, true value
  `≈ 0.1385`), hence `Pos (2λ₂ − 2λ₁)` and `λ₁ ≉ λ₂`. The route dodges the missing `log 4π`
  LOWER bracket entirely: in `(λ₂ + λ₂) − Rtwolambda1` the `log 4π` atoms cancel
  ALGEBRAICALLY (one `RsumL_cancel_anywhere` pair in the `RAddNF` normalizer), and every
  surviving atom enters with the sign whose certified bracket already exists (`γ ≥ 0.577`,
  `γ² ≤ 0.578²`, `γ₁ ≤ −0.0677`, `log 4π ≤ 2.5316`, `ζ(2) ≥ 1.644`) — no new numerics. KEY
  mechanization gotcha, recorded for reuse: equating two differently-associated `RsumL`
  list spellings by defeq sends the unifier through transient comparisons of DIFFERENT `Real`
  atoms into the Bishop-reindexed `.seq` towers (observed 11 GB OOM); the fix is to bridge each
  `++`-spelling to the common cons literal by an ALIGNED `List`-level `rfl` and `rw` the
  composed equations into the goal — element comparisons stay syntactic (6 MB). Axiom-clean;
  crux fields `none`.
- **`coupling_n5_positive` — the `n = 5` prime–archimedean coupling is positive** (new
  `Square/CruxN5Closed.lean`): composes `coupling_n5_iff_pos_lambda5` (the reduction of the coupling's
  `n = 5` instance to the closed form `Rlambda5`) with `Rlambda5_pos`, conquering the `n = 5` coefficient
  of `atlas_crux_localization`'s `∀ n, coupling(n) > 0` — the first new rung beyond `n = 4`, matching the
  `coupling_head_positive` / `Rlambda2_pos` / `coupling_n3_positive` / `Rlambda4_pos` family. Does NOT close
  the crux (the uniform `∀ n`, = RH). Axiom-clean; crux fields `none`.
- **`Pos Rlambda5` — the fifth Li coefficient is positive** (new `Analysis/LambdaFivePos.lean`): the
  `n = 5` prime–archimedean coupling coefficient is conquered — the FIRST new rung beyond `n = 4`, and the
  first to carry `γ₄`. Certified `λ₅ ≥ 83316/10⁶ ≈ +0.0833` (true `λ₅ ≈ 0.518`), assembled from
  `Rlambda5_arith ≥ 1018316/10⁶ ≈ +1.0183` (the η-anchor uppers `reta1_le5`…`reta4_le5` on the TIGHT
  brackets of `LambdaFivePrecision`, via `Rlambda5_S_le`/`Rlambda5_arith_ge_r`) and
  `genuineArchSeq 5 ≥ −935000/10⁶ = −0.935` (`genuineArchSeq5_ge`: `arch(5) = 1 − (5/2)(γ+log4π) +
  (15/2)ζ(2) − (35/4)ζ(3) + (75/16)ζ(4) − (31/32)ζ(5)`, using the tightened `ζ(3) ≤ 1.205`). This required
  the full n=5 constant-precision campaign: `γ₄` was NOT the sole gate — the margin (−0.652 with the n≤4
  brackets) is dominated by `η₃`'s `choose(5,4) = ×5` amplification of the loose `γ₃ ≤ 1/8`, so the closure
  needed the tighter `γ₃ ≤ 1/40`, `γ₂ ∈ [−0.014, −0.003]`, `γ₁ ≤ −69/1000`, `ζ(3) ≤ 1.205` (STEP 1), then
  the direct η-by-η `λ₅^arith` lower bound + `arch(5)` lower bound + the `Pos` assembly (STEP 2-4, mirroring
  `LambdaFourPos`). Axiom-clean (`{propext, Quot.sound}`), no `sorry`/`native_decide`, choice-free,
  no-smuggling audited; crux fields `none`, RH open.
- **n=5 constant-precision brackets** (new `Analysis/LambdaFivePrecision.lean`, STEP 1 of the `Pos λ₅`
  closure): the tightened Stieltjes/ζ brackets the n=5 margin needs — `γ₃ ≤ 1/40` (`Rgamma3_le_1_40`),
  `γ₂ ≤ −3/1000` (`Rgamma2_le_neg0003`), `γ₂ ≥ −14/1000` (`Rgamma2_ge_neg0014`), `γ₁ ≤ −69/1000`
  (`Rgamma1_le_neg069`), `ζ(3) ≤ 1.205` (`zeta3_le_1205`) — each a one-degree-up-precision mirror of the
  existing bracket theorem at larger `N` and higher log-cap depth `T` (γ₃: T=21,N=650,j=500; γ₂/γ₁:
  T=12,N=600/256,j=400), with the large-N `decide` accumulators reduced under the lakefile `--tstack`
  and the correction-weakening lemmas (`corr_weaken500` etc.) handling the `2^1014`-scale middle terms
  via a raised `exponentiation.threshold`. WHY: the `Pos λ₅` margin (−0.652 with the n≤4 brackets) is
  dominated by `η₃`'s `choose 5 4 = ×5` amplification of the loose `γ₃ ≤ 1/8` — so n=5 needs these
  tighter constants (not `γ₄`, whose bracket contributes only ±0.04). With them the margin turns
  positive (+0.083). Axiom-clean (`{propext, Quot.sound}`), no `sorry`/`native_decide`, no-smuggling
  audited; crux fields `none`, RH open.
- **`Rgamma4_ge_neg02` — the certified `γ₄` LOWER bracket `γ₄ ≥ −1/5`** (new `Analysis/GammaFourLower.lean`):
  the numeric heart of the `n = 5` gate, completing the `decompForm4` ladder. The one-degree-up mirror of
  `GammaThreeLower`: rational partial-sum lower bound `lnQuartSumLo` (Σ(ln k)⁴/k), the `logBound⁵`/`logBound⁴`
  upper bounds for the subtracted `(1/5)(ln N)⁵` and `½(ln N)⁴/N` corrections, the five per-step LOWER
  part-bounds against `decompForm4` (`b4C2_ge ≥ 0`, `b3R3_ge ≥ −27/D`, `b2R2_ge4 ≥ −16/D`, `bR1_ge4 ≥ −2/D`,
  `R0_ge4 ≥ −1/D`, `D = p(p+1)`; via the polynomial-log caps `(ln p)²≤4p`/`(ln p)³≤27p`), telescoped to
  `sStep4 ≥ −46/(p(p+1))` and `γ₄ ≥ hSeq4(N) − 46/(N+1)` (`Rgamma4_ge_hSeq4`, via `Rgamma4 = Rlim g4SeqDyadic`),
  collapsed to the rational `gBound4lo` and closed by one big-integer kernel `decide` at `N = 245`. The target
  is the LOOSE `−1/5` (not `−1/20`): `γ₄` enters `λ₅` only through the small favourable `−(5/24)γ₄` term, so
  `−1/5` is amply sufficient for `Pos λ₅` while keeping the `decide` inside the default kernel stack (the tight
  `−1/20` would force N ≳ 830, past the C-stack ceiling). Axiom-clean (`{propext, Quot.sound}`), no
  `sorry`/`native_decide`, choice-free, no-smuggling audited; crux fields `none`, RH open.
- **`sStep4_decomp` — the trapezoidal residual identity `sStep4 ≈ decompForm4`** (`Analysis/GammaFourBracket.lean`,
  the keystone of the `decompForm4` machinery): `decompForm4_eq_RsumL` / `lhsForm4_eq_RsumL` each expand to the
  same 11 canonical signed `RprodL` monomials (`b⁴C2`→3, `b³R3`→2, `b²R2`→2, `bR1`→2, `R0`→2), matched by
  `decomp_generic4` (the keystone `Req (lhsForm4 …) (decompForm4 …)`, via a kernel-verified 11-element
  `List.Perm` `[n2,n4,n6,n8,n10,n1,n3,n5,n7,n9,n11] ~ [n1..n11]`), and `sStep4_decomp` lands it at the log
  atoms (`a=ln(p+1)`, `b=ln p`, `u0=1/p`, `u1=1/(p+1)`) by rewriting the quintic difference
  `(ln(p+1))⁵−(ln p)⁵` through `quintic_diff_identity`. With this, the per-step trapezoidal residual `sStep4`
  is now an exact `b`-power decomposition — the bound-ready form the `γ₄` lower bracket telescopes. New
  degree-5/6 normalizers `Rmul_eq_RprodL6L`/`quart_times_pair`/`cube_times_triple`/`pair_times_sqpair`/
  `single_times_cubepair`. Axiom-clean (`{propext, Quot.sound}`), no `sorry`/`native_decide`, no-smuggling audited.
- **`decompForm4` — the bound-ready trapezoidal residual decomposition** (`Analysis/GammaFourBracket.lean`,
  defs `lhsForm4`/`decompForm4` + theorems `partA4_eq`/`partC4_eq`): the third `decompForm4` brick, the
  degree-4 mirror of `decompForm3`. `lhsForm4 = ½a⁴u1 + ½b⁴u0 − (1/5)·δ·W₄` (the stage-1 residual after
  `quintic_diff_identity`) is grouped by powers of `b` into `decompForm4 = b⁴·C2 + b³·R3 + b²·R2 + b·R1 + R0`
  with `C2 = ½(u0+u1)−δ`, `R3 = 2δ(u1−δ)`, `R2 = δ²(3u1−2δ)`, `R1 = δ³(2u1−δ)`, `R0 = ½δ⁴u1 − (1/5)δ⁵`
  (`δ = a−b`) — the coefficients that will make `b²·R2 ≤ 0` drop and leave the clean-telescoping terms.
  `partA4_eq` expands `½a⁴u1` (via `quartic_binom`) and `partC4_eq` expands `(1/5)·δ·W₄` (via `W4_expand`),
  each into 5 canonical `RprodL` monomials, with the coefficient-collapse helpers `half_four`/`half_six`/
  `fifth_five`/`fifth_ten`. Axiom-clean (`{propext, Quot.sound}`), no `sorry`/`native_decide`, choice-free,
  no-smuggling audited.
- **`W4_expand` — the quintic-factor expansion `W₄(b+δ, b)`** (`Analysis/GammaFourBracket.lean`,
  `a⁴+a³b+a²b²+ab³+b⁴ ≈ 5b⁴ + 10b³δ + 10b²δ² + 5bδ³ + δ⁴`, `δ = a−b`): the second `decompForm4` algebra
  brick — the `(a−b)·W₄` factor of the quintic difference `a⁵−b⁵` (`quintic_diff_identity`), with `a = b+δ`
  substituted. Built by the clean factoring `W₄ = a⁴ + (a³+a²b+ab²+b³)·b`, reusing `quartic_binom` for `a⁴`
  and the degree-3 `W_expand` for the inner cubic factor, then an aligned 5-term + 4-term collection
  (`W4_collect`) — flatten to one 9-element `RsumL`, a kernel-verified `List.Perm` to bring like terms
  adjacent, merge (new `one_plus_four`/`four_plus_one`/`four_plus_six`/`six_plus_four` coefficient lemmas,
  `Radd_eq_RsumL4`/`RsumL5` flatteners), reassociate to the left-nested target. Axiom-clean
  (`{propext, Quot.sound}`), no `sorry`/`native_decide`, choice-free, no-smuggling audited.
- **`quartic_binom` — the degree-4 binomial identity over the constructive reals** (`Analysis/GammaFourBracket.lean`,
  `(b+d)⁴ ≈ b⁴ + 4·b³d + 6·b²d² + 4·bd³ + d⁴`): the first reusable algebra brick of the `decompForm4`
  trapezoidal decomposition that the `γ₄` numeric bracket rests on (the sole remaining `n = 5` gate
  toward `Pos λ₅`). Built as a one-degree-up mirror of `cube_binom` — `cube_binom·(b+d)`, eight monomials
  normalized to canonical coefficient-first form via `Rmul_swap_last`/`Rmul_comm`/`Rmul_assoc`, collected
  through the `RsumL` append/permute machinery (a kernel-verified 8-element `List.Perm`), and merged with
  `three_plus_one`/`three_plus_three`/`one_plus_three`. Elaborates in ~1 s at the default heartbeat budget
  (the degree-4 explicit congruence is fast *when structurally exact*: any single mismatch triggers a
  `whnf` blow-up, since the `Real` ops are reducible structure defs — the diagnostic lesson of this brick).
  Axiom-clean (`{propext, Quot.sound}`), no `sorry`/`native_decide`, choice-free, no-smuggling audited.
- **The fifth Li coefficient `λ₅` as a closed-form constructive object** (new `Analysis/LambdaFive.lean`
  + `Square/CruxFrontierN5.lean`, `Rlambda5`, `coupling_n5_iff_pos_lambda5`): the next rung of the
  genuine λ-ladder, the FIRST to carry `γ₄` (`Rgamma4`). The new η-anchor is **`η₄ = −γ⁵ − 5γ³γ₁ − 5γγ₁²
  − (5/2)γ²γ₂ − (5/2)γ₁γ₂ − (5/6)γγ₃ − (5/24)γ₄`**, derived from the `−ζ′/ζ` Laurent data via
  `ηⱼ = (j+1)gⱼ₊₁` (`−log F = Σ gⱼuʲ`, `F = (s−1)ζ`) — the same recursion that reproduces `η₀..η₃`
  exactly, and numerically confirmed (`η₄ ≈ −0.005539`, `λ₅^{arith} ≈ +1.45906`, `λ₅^{∞} ≈ −0.94094`,
  `λ₅ ≈ +0.51812`, the standard Li value). `λ₅^{arith} = −(5η₀+10η₁+10η₂+5η₃+η₄)` and the closed form
  meets the genuine ladder at `n = 5` (`genuineLam_five`), so the `n = 5` coupling conquest reduces
  exactly to `Pos Rlambda5` (`coupling_n5_iff_pos_lambda5`/`crux_frontier_n5`), mirroring `n = 4`. This
  builds the λ₅ OBJECT; it does NOT prove `Pos λ₅` (which awaits the `γ₄` numeric bracket + the
  multi-constant assembly). `γ₄` enters `λ₅` only via `η₄` with the tiny FAVOURABLE coefficient
  `+(5/24)γ₄ ≈ +0.0015`. Axiom-clean (`{propext, Quot.sound}`), choice-free, no-smuggling audited; the
  crux fields stay `none`, RH open.

- **The fourth Stieltjes constant `γ₄` as a genuine constructive real** (new `Analysis/GammaFour.lean`,
  `Rgamma4 := Rlim g4SeqDyadic g4SeqDyadic_RReg`, `γ₄ ≈ +0.00722`): the arithmetic-side prerequisite for the
  `n = 5` coupling rung (`λ₅`), built as the full degree-5 mirror of `GammaThree`'s `γ₃`. The
  EM-accelerated defining sequence `g₄(j) = Σ_{k≤j+1}(ln k)⁴/k − (1/5)(ln(j+1))⁵`, whose per-step
  trapezoidal residual `e₄` is summable-enveloped `e₄ ∈ [−a⁴/(p(p+1)), 4a³/(p(p+1))]` (`a = ln(p+1)`),
  then dyadic-block-telescoped to a Bishop-regular sequence (`g4SeqDyadic_RReg`, reindex `M(j)=2j+22`)
  whose limit is `γ₄`. New degree-5 algebra: the **quintic factoring** `a⁵−b⁵ = (a−b)(a⁴+a³b+a²b²+ab³+b⁴)`
  (`quintic_diff_identity`, via the reusable `Rmul_swap_outer`/`Rmul_swap_last` monomial-reassociation
  helpers), the `W₄ ∈ [5b⁴, 5a⁴]` envelopes, and the degree-3/degree-4 discrete-antiderivative domination
  chains (`Q_U(m)=8m³+72m²+264m+408`, `Q_L(m)=2m⁴+24m³+132m²+408m+598`, each verified by `ring_uor` to
  satisfy `2Q_U(m)−Q_U(m+1)=8(m+2)³` / `2Q_L(m)−Q_L(m+1)=2(m+2)⁴`). The cubic/quartic infrastructure
  (`logCube`, `logQuartic`, `quartic_diff_identity`, `W3_le_4a3`, `Csum`, the block caps) is reused from
  `GammaThree`. With `γ`, `γ₁`, `γ₂`, `γ₃` (bracketed) and `ζ(5)`, this is the last unbuilt Stieltjes
  constant for the `η₄` Taylor data behind `λ₅`. Axiom-clean (`{propext, Quot.sound}`), choice-free,
  no-smuggling audited; the crux fields stay `none`, RH open. The two-sided `γ₄` bracket + the `λ₅` rung
  are the remaining `n = 5` steps.

- **ζ-value brackets — `ζ(5) ∈ [1.036, 1.052]`** (`Analysis/ZetaTwo.lean`, `zeta5_lower`/`zeta5_upper`):
  the next ζ-constituent for the future `n = 5` coupling rung, mirroring the `ζ(4)` block (partial-sum
  lower `zetaSum_five_70_ge` and decreasing-upper `zetaU_five_70_le`, each one rational `decide` at
  `N = 70`, lifted through the generic `zeta_ge_partial`/`zeta_le_partial`). Just as `ζ(4)` feeds
  `Pos Rlambda4`, this is the `ζ(5)` prerequisite for a `Pos Rlambda5`. Axiom-clean, crux `none`.

- **Stieltjes brackets — the γ₃ LOWER bracket `γ₃ ≥ −1/20`, completing the two-sided `−1/20 ≤ γ₃ ≤ 1/8`**
  (new `Analysis/GammaThreeLower.lean`, `Rgamma3_ge_neg005`): the companion of `GammaThreeBracket`'s
  `Rgamma3_le` (`γ₃ ≤ 1/8`), filling the documented gap (`γ₃` had an upper bracket but "no lower bracket
  yet"). Same discrete Euler–Maclaurin construction as the other brackets — the accelerated sequence
  `hSeq3 j = g₃(j) − ½·(ln(j+1))³/(j+1)` whose per-step trapezoidal residual `sStep3` is now bounded
  *below* (`sStep3 ≥ −6/(p(p+1))`, `sStep3_lower_tele`) by mirroring the four-part decomposition
  `decompForm3 = b³C2 + b²R2 + b·R1 + R0` downward: `b³C2 ≥ 0`, `b²R2 ≥ −3/(p(p+1))` (via the square-cap
  `(ln p)² ≤ 4p`), `b·R1 ≥ −2/(p(p+1))`, `R0 ≥ −1/(p(p+1))` (via the new quartic self-bound `d⁴ ≤ 1/p⁴`).
  Telescoped to `γ₃ ≥ hSeq3(N) − 6/(N+1)` (`Rgamma3_ge_hSeq3`), then certified at `N = 199` with the
  LOWER-direction rational evaluators — the new cubed-log sum lower bound `lnCubeSumLo`/`lnCubeSum_ge`
  (`logLowBound` cubed, round-down) against the `logBound`-upper corrections `logQuartic_le`/
  `halfCubeOver_le` — collapsed to the single `gBound3lo` and one big-integer kernel `decide`
  (`gamma3_lo_decide`). This is the `γ₃` prerequisite for the future `λ₅` rung (the `η₄` Taylor data needs
  a two-sided `γ₃`). Axiom-clean (`{propext, Quot.sound}`), choice-free, no-smuggling audited; the crux
  fields stay `none`, RH open.

- **Track 1 (item 0) — the LARGE-argument end of the arctangent range extension** (new
  `Analysis/RArctanExt.lean`, `RarctanExt` / `RarctanExt_value_eq` / `RarctanR_add_RarctanExt`): the
  constructive `arctan` at large argument `|t| ≥ 16`, via the complementary-angle reduction
  `arctan(1/s) = π/2 − arctan s`. `RarctanR s` (`RArctan.lean`) is defined only for `|s| ≤ ρ < 1/16`, so its
  reciprocal `1/s` (`≥ 16`) lies far outside the radius; `arctanExt s := π/2 − arctan s` supplies that value
  through the complementary angle — sidestepping the `1 − s·(1/s) = 0` singularity that blocks the
  tangent-addition route. The value identity `RarctanExt_value_eq` (`tan(arctanExt s) = 1/s`) composes the
  real-argument value identity `RarctanR_value_eq` (`RArctanValue.lean`) with the complementary-tangent
  formula `Rsin_cos_pi_half_sub_tan_real` (`TanPiQuarter.lean`) — the real-level form of the reduction
  `ComplexArgUpper.CargUpper_tan` already applies for the complex argument; the genuinely-new piece is the
  explicit *real* reflection identity `RarctanR_add_RarctanExt` (`arctan s + arctan(1/s) = π/2`).
  **Honest scope:** this closes only the large-argument end; the middle band `1/16 < |t| < 16` (where `1/t`
  is also outside `1/16`) remains the open part of the *full* range extension `Carg`/`Clog` need toward
  `log ξ` — closing it needs a larger value-identity radius or an addition-law stepping argument. Crux
  `none`. Axiom-clean, grep-novel.

- **Track 1 (item 6) — the Hadamard/`bl` witness sum in reciprocal-moment-order form**
  (`Analysis/MomentCayley.lean`, `hadamard_witnessSum_moment`): the item-6 object, assembled on the
  *genuine* zeros. For a `HadamardXi` enumeration of the nontrivial zeros, the `bl` witness sum over its
  `s = 1` factors equals `−Σ_{k=1}^{n} Re(M_k)` with `M_k = Σ_j C(n,k)(−1/ρⱼ)ᵏ` the order-`k` reciprocal
  moment over the reciprocals `1/ρⱼ`: `Σ_j (1 − Re((1 − 1/ρⱼ)ⁿ)) = −Σ_{k} Re(M_k)`. Chains
  `witnessSum_hadFactor_eq_liRatio` (Hadamard `s=1` factors = Cayley factors), the per-zero
  `liRatio_eq_one_sub_inv` lifted across the list (`witnessSum_mapidx_congr` + `List.map_map`), and the
  moment decomposition `witnessSum_moment_order` — `λₙ`'s zero-sum decomposed by moment order over the
  actual Hadamard zero enumeration. The remaining classical content (`Σ_ρ ρ^{−k}` as the `ζ`-data with its
  archimedean place; the `HadamardXi` convergence seam) is unchanged; crux `none`. Axiom-clean, grep-novel.

- **Track 1 (item 6) — the moment expansion lands on the genuine Cayley object** (new
  `Analysis/MomentCayley.lean`, `liRatio_witnessTerm_moment` / `liRatio_npow_moment` /
  `liRatio_eq_one_sub_inv`): the abstract binomial moment machinery (`ComplexBinomial.lean`, for any
  `w = 1 − u`) is instantiated at the *actual* Bombieri–Lagarias Cayley factor `liRatio ρ = 1 − 1/ρ`
  (`CayleyMap.lean`), with `u = 1/ρ = Cinv ρ`. `liRatio_eq_one_sub_inv` puts `liRatio ρ` in the exact
  `1 + (−u)` form (via `hadFactor_one_eq_liRatio` + `1·(1/ρ) ≈ 1/ρ`); then the per-zero witness term on
  the real object follows directly: `1 − Re((1 − 1/ρ)ⁿ) = −Re(Σ_{k=1}^{n} C(n,k)(−1/ρ)ᵏ)` — the per-zero
  summand of `RHWitness.witnessSum` over the explicit-formula reciprocal moments `(1/ρ)ᵏ`. Closes the
  loop: the whole moment-expansion arc is now consumed by the genuine Cayley/Li object behind `bl`, not an
  abstract `w`. The remaining classical content (`Σ_ρ ρ^{−k}` as the `ζ`-data with its archimedean place)
  is unchanged; crux `none`. Axiom-clean, grep-novel.

- **Track 1 (item 6) — the two Li-term linearizations agree `reciprocalMomentPoly_eq_neg_u_cgeomSum`**
  (`Analysis/ComplexBinomial.lean`): the binomial reciprocal-moment polynomial equals `−u` times the
  geometric sum of `LiLinearize.lean`. For `w = 1 − u` (so `u = 1/ρ`), both `reciprocalMomentPoly u n`
  (`Σ_{k=1}^{n} C(n,k)(−u)ᵏ`, from the binomial) and `−u·Σ_{k<n} wᵏ` (`cone_sub_npow_factor`) are exactly
  `wⁿ − 1`, hence equal: `reciprocalMomentPoly u n ≈ −(u·Σ_{k<n} wᵏ)`. Pins the new binomial-moment
  representation to the pre-existing geometric one — no representation drift between `ComplexBinomial.lean`
  and `LiLinearize.lean`, the same per-zero Li contribution in two algebraic forms. Pure algebra,
  axiom-clean, grep-novel.

- **Track 1 (item 6) — moment-side closure `momentListPoly_append` / `momentListPoly_snoc`**
  (`Analysis/ComplexBinomial.lean`): the summed reciprocal-moment polynomial is additive over
  concatenation of the zero list (`momentListPoly (l₁++l₂) n = momentListPoly l₁ n + momentListPoly l₂ n`,
  pure `Cadd_assoc` fold), with the `snoc` increment. The moment-side analogues of the proven
  `witnessSum_append`/`_snoc`: splitting the zero enumeration (the incremental `bl` partial sums
  `List.range M`, or the conjugate-pair grouping `{ρ, 1−ρ, ρ̄, 1−ρ̄}`) splits the moment sum. Pure algebra,
  axiom-clean, grep-novel.

- **Track 1 (item 6) — a structural shape-match `witnessSum_eq_genuineArith`** (new
  `Analysis/MomentEta.lean`): the constructive moment-expansion form of a finite witness sum
  (`witnessSum_moment_order`, `ComplexBinomial.lean`) and the constructive arithmetic `η`-form
  (`genuineArithSeq`, `GenuineLi.lean`) carry the *same* binomial-weighted shape (`−Σ_k` of
  `C(n,k)`-weighted terms), so they are equal term-by-term under one per-order coefficient hypothesis
  `Re(M_k) = C(n,k)·η_{k−1}` (`seam`, an explicit audit-visible hypothesis, never an axiom, never
  discharged): `Σ_w (1 − Re(wⁿ)) = −Σ_{j=1}^{n} C(n,j)·η_{j−1}` (clean induction `moment_re_eq_arithTail`,
  matching the `(CsumN …).re`/`arithTail` recursions). **Honesty scope:** this is a shape-level identity
  between two constructed representations, **not** a discharge or relocation of `bl`. `genuineArithSeq` is
  only the *arithmetic* piece of `λₙ` (`λₙ = genuineArithSeq + genuineArchSeq`; `λ₁^{arith} = γ ≈ 0.577`
  vs the full `λ₁ ≈ 0.023`), while the genuine Bombieri–Lagarias zero-sum limit equals the *full* `λₙ`; and
  the true explicit formula relates the zero moments to the `−ζ′/ζ` data **plus** the archimedean place,
  which the per-order `seam` omits. So the `seam` is not asserted for the genuine zeros, and `bl` is not
  shrunk — closing it constructively (explicit formula + archimedean term + Hadamard convergence) remains
  the open Track-1 work. Crux fields `none`; RH open. Axiom-clean, no-smuggling audited, grep-novel.

- **Track 1 (item 6) — `λₙ` decomposed by reciprocal-moment order** (`Analysis/ComplexBinomial.lean`,
  `witnessSum_moment_order`, `momentListPoly_swap`, `momentList`): the Fubini interchange of the sum over
  zeros with the sum over orders. `momentListPoly_swap` swaps `Σ_{u∈us} Σ_{k=1}^{n} C(n,k)·(−u)ᵏ ≈
  Σ_{k=1}^{n} Σ_{u∈us} C(n,k)·(−u)ᵏ` (list induction, `CsumN_add` regrouping). Combined with
  `witnessSum_eq_neg_momentList`, `witnessSum_moment_order` gives `λₙ`'s zero-sum (`bl`) as
  `Σ_w (1 − Re(wⁿ)) = −Σ_{k=1}^{n} Re(M_k)` with `M_k = Σ_{u∈us} C(n,k)·(−u)ᵏ` the order-`k` reciprocal
  moment — `λₙ`'s explicit decomposition into the per-order moments `Σ_ρ ρ^{−k}`. This is the structural
  endpoint of the constructive moment expansion: the sole remaining classical input is the per-order
  identity of each `M_k` with the `−ζ′/ζ` Taylor data (the single labelled `bl` seam), reduced from a
  monolithic limit to one clean identity per order. Axiom-clean, grep-novel.

- **Track 1 (item 6) — the witness sum in reciprocal-moment form** (`Analysis/ComplexBinomial.lean`,
  `witnessSum_eq_neg_momentList`, `momentListPoly`): the per-zero `witnessTerm_moment` summed over the
  zero list. Over the Cayley factors `w = 1 − u` of a moment list `us = {1/ρ}`, the Li witness sum
  `Σ_w (1 − Re(wⁿ))` equals `−Re(Σ_{u∈us} Σ_{k=1}^{n} C(n,k)·(−u)ᵏ)` — `λₙ`'s zero-sum (`bl`) written
  entirely over the explicit-formula reciprocal moments `(1/ρ)ᵏ`. With the order-`k` moment
  `M_k = Σ_ρ Re(ρ^{−k})` factored out, `λₙ = Σ_{k=1}^{n} (−1)^{k+1} C(n,k)·M_k`, leaving the sole classical
  seam as the per-order identity `M_k = η`-data (`−ζ′/ζ` Taylor coefficients). Clean list induction
  (`Rneg_Radd` regrouping), axiom-clean, grep-novel.

- **Track 1 (item 6) — the per-zero witness term in reciprocal-moment form** (`Analysis/ComplexBinomial.lean`,
  `witnessTerm_moment` / `Cnpow_one_sub_momentPoly`, `reciprocalMomentPoly`): the forced consumer of the
  complex binomial. For `w = 1 − u` the per-zero Li witness term `1 − Re(wⁿ)` equals `−Re(Σ_{k=1}^{n}
  C(n,k)·(−u)ᵏ)` — the binomial expansion of `wⁿ` with the leading `1` cancelling the outer `1` (front-split
  via `CsumN_shift` + `binTermC_zero`), leaving exactly the negated reciprocal-moment polynomial. With
  `u = 1/ρ` this is the per-zero summand of `witnessSum` (`RHWitness.lean`) written over the explicit-formula
  moments `(1/ρ)ᵏ`; summing over the zeros and interchanging the two finite sums gives `λₙ` as
  `Σ_{k=1}^{n} (−1)^{k+1} C(n,k)·M_k` with `M_k = Σ_ρ Re(ρ^{−k})` the order-`k` reciprocal moment — isolating
  the single classical seam `M_k = η`-data. Axiom-clean, grep-novel.

- **Track 1 (item 6, pure algebra) — the binomial theorem over the constructive `Complex` API**
  `(1 + b)ⁿ ≈ Σ_{k=0}^{n} C(n,k)·bᵏ` (`Cnpow_one_add_eq`, new `Analysis/ComplexBinomial.lean`), and its
  Cayley-factor consequence `Cnpow_one_sub_eq`: `w = 1 − u ⟹ wⁿ ≈ Σ_k C(n,k)·(−u)ᵏ`. For the
  Bombieri–Lagarias factor `w = 1 − 1/ρ` the moment is `u = 1/ρ`, so this writes each per-zero power
  `(1 − 1/ρ)ⁿ` over the explicit-formula **reciprocal moments** `(1/ρ)ᵏ = Σ_ρ ρ^{−k}` — the binomial
  expansion applied to exactly the object the `bl` witness sum `Σ_w (1 − Re(wⁿ))` is built from,
  extending the `witnessSum_eq_linear` moment-factoring line one step further (full moment polynomial,
  not just the single `1/ρ`). The remaining classical content (moments `Σ_ρ ρ^{−k}` as the `η`-polynomial)
  stays the single labelled seam; crux fields `none`. Built choice-free with nat-scalar `Cnsmul` (so
  Pascal's rule `C(n+1,k)=C(n,k)+C(n,k−1)` is the clean complex additivity `Cnsmul_add`, no `ofReal`
  embedding of coefficients), plus the supporting `Cmul_Cnsmul`, `Cmul_CsumN` (mult over finite sum),
  `CsumN_congr_le` (bounded congruence), and the subtraction-free index shift `CsumN_shift`. Grep-verified
  novel (the existing `Binomial.lean` is the ℚ binomial; this is the genuinely-complex one), axiom-clean.

- **Track 1 (`bl` witness) — partial-sum telescoping `witnessSum_append`/`witnessSum_snoc`** (`Analysis/RHWitness.lean`):
  the Li/zero-sum witness `Σ_w (1 − Re(wⁿ))` is additive over concatenation of the zero list
  (`witnessSum (l₁++l₂) = witnessSum l₁ + witnessSum l₂`, pure `Radd_assoc` fold), with the `snoc`
  increment `witnessSum (l ++ [w]) = witnessSum l + (1 − Re(wⁿ))`. This is the analogue, on the
  explicit-formula/`bl` side, of the integral's additive linearity, and the exact shape of the `bl`
  partial sums `witnessSum ((List.range M).map zeroCayley) n` as `M` grows by one — the increment the
  convergence seam `reg` is stated over. Grep-verified novel, axiom-clean.

- **Track 2 (integration) — scalar linearity lifted up the full Mellin stack** (`Analysis/IntervalIntegral.lean`,
  `Analysis/ImproperIntegral.lean`, `Analysis/ComplexIntegral.lean`): `riemannIntegralI_smul`
  (interval `∫ₐ^{a+w}`, left-commuting `q` past the width `w`), `integralTerm_smul`, `improperIntegral1_smul`
  (the half-line tail, via `Rlim_ofQ_mul_of_approx` directly), `halfLineIntegral_smul` (`∫₀^∞ (q·f)=q·∫₀^∞ f`),
  and `ChalfLineIntegral_smul` (complex Mellin, componentwise, real-rational scalar → explicit pair
  `⟨q·∫gr, q·∫gi⟩`). **With `_add` and `_neg` at every layer, the constructive integral — through the complex
  Mellin domain — is now a full real-rational-linear functional**, the form the Weil pairing's real test
  coefficients act through. The re/im-mixing complex `Cmul` scalar remains the one deferred (downstream) case.
- **Track 2 (integration) — scalar linearity `riemannIntegral_smul` (`∫(q·f)=q·∫f`)** via
  `Rlim_ofQ_mul_of_approx` (`Analysis/RlimProps.lean`, `Analysis/RiemannSum.lean`,
  `Analysis/DyadicIntegral.lean`): the scalar half of integral linearity — with `_add`/`_neg`, the
  full **linear-functional** structure of the certified integral (`∫(α·f + β·g) = α·∫f + β·∫g` for
  rational `α,β`). `Rlim_ofQ_mul` is generalized to `Rlim_ofQ_mul_of_approx` (`W ≈ q·X` pointwise, `W`'s
  regularity given — one `happ`-triangle over the core, exactly the `Rlim_add → Rlim_add_of_approx`
  move, since `RReg(q·X)` is not derivable when `|q|>1`). The finite chain: new `RsumN_Rmul_const`,
  `riemannSum_smul`, `genSum_Rmul_of_termwise`, `Rmul_Rsub_distrib_loc` — dyadic sums scale at every
  level — then `Rlim_ofQ_mul_of_approx` + `Rmul_distrib` carry the scalar through the limit (shared
  Lipschitz `L`, so the reindexes align). Grep-verified novel, axiom-clean.
- **Track 1 (limit substrate) — scalar-multiple limit `Rlim_ofQ_mul`** (`Analysis/RlimProps.lean`):
  `lim (q·X) = q·lim X` for a constant `q : ℚ` — the scalar half of limit linearity, and the genuinely
  hard one. `Rmul`'s reindex `Ridx q y n = 2·RmulK(q,y)·(n+1)−1` is magnitude-dependent (varies across
  the meta-sequence), so `Rlim_add`'s clean `8n+7` alignment does not port. The UOR insight that makes it
  tractable: **`q` is a CONSTANT**, so its sequence is invariant and the `Qabs_mul_diff` cross term
  vanishes, leaving only `|q|·|X-difference|`; and `RmulK ≥ 1` forces every reindex `≥ 8(n+1)`, so each
  regularity term is `≤ const/(n+1)` *regardless* of the (varying) magnitude bound. `Req_of_lin_bound`
  absorbs the `|q|` constant (`C = |q.num|`). The substrate for the scalar half of integral linearity
  (`∫(q·f) = q·∫f`). Grep-verified novel, axiom-clean.
- **Track 2 (integration) — complex integral congruence `Cintegral_congr` / `ChalfLineIntegral_congr`**
  (`Analysis/ComplexIntegral.lean`): `∫ z ≈ ∫ z'` when the real/imaginary integrand parts agree pointwise,
  for the complex line integral `∫_a^{a+w}` and the complex Mellin integral `∫₀^∞` — componentwise from
  the real `riemannIntegralI_congr`/`halfLineIntegral_congr`. The integrand-congruence the Weil/theta
  complex-integrand rewrites need; completes the complex integral's `_congr` alongside `_add`/`_neg`.
  Grep-verified novel, axiom-clean.
- **Track 2 (integration) — integral negation up the full stack `halfLineIntegral_neg` / `ChalfLineIntegral_neg`**
  (`Analysis/IntervalIntegral.lean`, `Analysis/ImproperIntegral.lean`, `Analysis/ComplexIntegral.lean`):
  `∫(−f) = −∫f` lifted from the base through `riemannIntegralI_neg` (interval, affine + `Rmul_neg_right`)
  → `integralTerm_neg` → `improperIntegral1_neg` (`∫₁^∞`, `genSum_Rneg_of_termwise` + `Rlim_neg` via the
  now-public `RReg_Rneg`) → `halfLineIntegral_neg` (`∫₀^∞`) → `ChalfLineIntegral_neg` (complex Mellin,
  componentwise). **With the `_add` chain this completes the full additive-GROUP linearity of the entire
  integral stack** (real + complex Mellin: `∫(f−g)=∫f−∫g`), the substrate the signed Weil functional
  `poles − primes − arch` needs. Grep-verified novel, axiom-clean.
- **Track 2 (integration) — integral negation `riemannIntegral_neg` (base)** (`Analysis/RiemannSum.lean`,
  `Analysis/DyadicIntegral.lean`): `∫₀¹ (−f) = −∫₀¹ f`, the `−1`-scalar case completing (with
  `riemannIntegral_add`) the additive-GROUP linearity of the base integral (`∫(f−g)=∫f−∫g`, for the
  signed Weil functional). The dyadic sums negate at every finite level — new primitives `RsumN_Rneg`
  (`Σ(−F)=−ΣF`), `riemannSum_neg`, `genSum_Rneg_of_termwise` — and `Rlim_neg` (with `RReg_neg`, inlined
  locally) carries it through the limit; `dyadicTerm` negation via `Rsub_Rneg_Rneg`. Modulus-safe
  (negation doesn't inflate the index). Grep-verified novel, axiom-clean.
- **Track 2 (integration) — base-integral congruence `riemannIntegral_congr` / `riemannIntegralI_congr`**
  (`Analysis/DyadicIntegral.lean`, `Analysis/IntervalIntegral.lean`): `∫f ≈ ∫g` for `f ≈ g` pointwise on
  `[0,1]` and `[a,a+w]` — the integral respects `≈` of the integrand, completing the `_congr` family
  (the improper/half-line congruences already existed; the two base integrals were the gap). Each is
  `Rle_antisymm` of the corresponding `_le` both ways. Axiom-clean. (The integrand-congruence substrate
  any future integral rewrite — including a negation/subtraction zero-trick — needs.)
- **Track 2 (integration) — complex Mellin integral linearity `ChalfLineIntegral_add`** (additive part)
  (`Analysis/ComplexIntegral.lean`): `∫₀^∞ ((gfr+ggr) + i(gfi+ggi)) = ∫₀^∞(gfr+i·gfi) + ∫₀^∞(ggr+i·ggi)`
  — the additive half of linearity for the constructive **complex** Mellin integral, the object the
  windowed Weil pairing and the Mellin transform of the theta relation (item 3) inhabit. Componentwise
  from the real `halfLineIntegral_add` (real and imaginary parts, each at its own shared Lipschitz
  constant `Lr`/`Li` and decay rate `Kr`/`Ki`). Grep-verified novel, axiom-clean.
- **Track 2 (integration) — half-line/Mellin integral linearity `halfLineIntegral_add`** (additive part)
  (`Analysis/IntervalIntegral.lean`, `Analysis/ImproperIntegral.lean`): `∫₀^∞ (f+g) = ∫₀^∞ f + ∫₀^∞ g`,
  the substrate the Weil/theta Mellin integrals live on (Track-2 step 2), lifted up the integral stack
  from `riemannIntegral_add`: `riemannIntegralI_add` (interval `[a,a+w]`, via the affine rescaling +
  `Rmul_distrib`) → `integralTerm_add` (the unit tail increment) → `improperIntegral1_add`
  (`∫₁^∞`, the tail increments add ⟹ partials add via `genSum_Radd_of_termwise`, then
  `Rlim_add_of_approx` joins the limits) → `halfLineIntegral_add` (`∫₀^∞ = ∫₀¹ + ∫₁^∞`, `Radd_swap`).
  All at a shared Lipschitz constant `L` so the dyadic reindexes align. Grep-verified novel, axiom-clean.
- **Track 2 (integration) — Riemann-integral linearity `riemannIntegral_add`** (`Analysis/DyadicIntegral.lean`):
  `∫₀¹ (f+g) = ∫₀¹ f + ∫₀¹ g` — the additive half of linearity for the certified Bishop-limit integral,
  and the first genuine consumer of `Rlim_add_of_approx` (validating the limit-additivity layer end to
  end). The three integrals share a Lipschitz constant `L` (caller supplies `L ≥ L_f + L_g` with all
  three Lipschitz proofs at `L`), so they use the same dyadic reindex `digammaMidx L` and the limits
  align — no integral-`L`-independence lemma needed. The dyadic sums add at every finite level
  (`riemannSum_add` ⟹ `dyadicR` ⟹ `dyadicTerm` via `Rsub_Radd_Radd` ⟹ `genSum` via the new
  `genSum_Radd_of_termwise`), so the integral sequences satisfy `Z_{f+g} ≈ Z_f + Z_g` pointwise; the
  combined convergence is GIVEN (its own `dyadicSum_RReg`), so `Rlim_add_of_approx` joins the limits
  without a (non-derivable) combined regularity. Grep-verified novel, axiom-clean.
- **Track 1 (item 6 — series substrate) — series additivity `Cseries_add`, via `Rlim_add_of_approx`**
  (`Analysis/RlimProps.lean`, `Analysis/ComplexLimit.lean`, `Analysis/ComplexSeries.lean`):
  `Σ_k (Fₖ + Gₖ) ≈ (Σ_k Fₖ) + (Σ_k Gₖ)` — linearity of the complex infinite sum, the forced tool for
  splitting a log-derivative / witness series into its component series (item 6). This had appeared
  *blocked* (the fixed `RReg` modulus is not preserved under summation, so a combined regularity is not
  derivable) — the unblock is the **generalization `Rlim_add_of_approx`** (`lim W ≈ lim X + lim Y` when
  `W ≈ X + Y` pointwise): it takes `W`'s regularity as GIVEN rather than deriving the sum's, so the
  caller's `CsumConv (F+G)` carries `W = CsumN (F+G)`, which is pointwise `≈ CsumN F + CsumN G` by
  `CsumN_add`. Proof of `Rlim_add_of_approx`: the `Rlim_add` `8n+7` diagonal alignment plus one triangle
  for the `happ` error (`2/(4n+4) + 10/(8n+8) = 14/(8n+8) ≤ 2/(n+1)`, still absorbed by
  `Req_of_lin_bound`); `Rlim_add` becomes its `happ = refl` corollary. `Clim_add_of_approx` is the
  componentwise lift; `Cseries_add` a 1-liner over it. Grep-verified novel, axiom-clean.
- **Track 1 (item 5 — product substrate) — finite-product multiplicativity `CprodN_mul`**
  (`Analysis/ComplexSeries.lean`): `∏_{k<N} (Fₖ·Gₖ) ≈ (∏_{k<N} Fₖ)·(∏_{k<N} Gₖ)` — the complex finite
  product distributes over a factorwise product, the algebraic substrate for factoring the Hadamard
  product `∏(1 − s/ρ)` (item 5; e.g. splitting a factor across the product). Proved by induction on `N`
  over a new four-term product interchange `(a·b)·(c·d) ≈ (a·c)·(b·d)` (`Cmul_mul_mul_comm`, from
  `Cmul_assoc`/`Cmul_comm`) — the multiplicative mirror of `CsumN_add`'s `Cadd_add_add_comm`. Completes
  the multiplicative half of the `CprodN` API alongside `CprodN_congr`/`CprodN_succ_one`. Grep-verified
  novel, axiom-clean.
- **Track 1 (item 0 — limit/series substrate) — negation closure `Clim_neg` / `CsumN_neg`**
  (`Analysis/ComplexLimit.lean`, `Analysis/ComplexSeries.lean`): `lim (−X) ≈ −lim X` and
  `Σ_{n<N} (−Fₙ) ≈ −(Σ_{n<N} Fₙ)` — the negation half of the complex limit/finite-sum linearity (with
  `Clim_add`/`CsumN_add`, the full additive-group structure; subtraction pervades the log-derivative
  `1 − Re(·)` / `−ζ′/ζ`). Both modulus-SAFE — negation does not inflate the sequence index, so `RReg` is
  preserved exactly (no rate doubling, unlike `Clim_add`). `Clim_neg` lifts the real `Rlim_neg`
  componentwise (still threading the transformed regularity as a hypothesis, the codebase idiom);
  `CsumN_neg` is an induction over the new `Cneg_Cadd` (`−(a+b) ≈ (−a)+(−b)`, from `Rneg_Radd`).
  Grep-verified novel, axiom-clean.
- **Track 1 (item 0 — limit substrate) — Bishop-limit additivity `Rlim_add` / `Clim_add`**
  (`Analysis/RlimProps.lean`, `Analysis/ComplexLimit.lean`): `lim (X + Y) ≈ lim X + lim Y` over ℝ and ℂ —
  the forced gateway to complex series linearity (`Cseries_add`) for splitting a witness / log-derivative
  series into its two component series (Hadamard `bl`, item 6). The real `Rlim_add` is the substantive
  piece: the `RTendsTo` rate would *double* under `Radd` (the known "modulus not closed under `Radd`"
  obstruction), so the canonical `RTendsTo_add` is false; instead the proof goes through
  `Req_of_lin_bound` (which absorbs the constant) and the key alignment that **both** diagonals land at the
  same sequence position `8n+7` — `lim(X+Y)` at `(X (4n+3))_{8n+7}` (the `Radd` index inflation
  `2·(4n+3)+1`), `(lim X)_{2n+1}` at `(X (8n+7))_{8n+7}` — so the gap is pure meta-regularity `RReg`,
  giving `5/(8(n+1)) ≤ 2/(n+1)` per component. `Clim_add` is then the clean componentwise lift. Both
  grep-verified novel, axiom-clean.
- **Track 1 (item 0 — complex-limit substrate) — zero limit `Clim_zero`**
  (`Analysis/ComplexLimit.lean`): a regular complex sequence pointwise `≈ 0` has limit `≈ 0` — the
  complex lift of the real `Rlim_zero` (`RlimProps.lean`, used real-side in the dyadic telescoping
  convergence proofs), the convergence side of a telescoped complex series of differences vanishing.
  Componentwise (both `Rlim_zero` halves), the companion of the existing `Clim_congr`. Grep-verified
  novel. Axiom-clean.
- **Track 1 (item 0/6 — complex-series substrate) — finite-sum linearity `CsumN_add`**
  (`Analysis/ComplexSeries.lean`): `Σ_{n<N} (Fₙ + Gₙ) ≈ (Σ_{n<N} Fₙ) + (Σ_{n<N} Gₙ)` — additivity of the
  complex partial sum, the forced algebraic substrate for splitting a witness / log-derivative series
  into its two component series (toward the Hadamard `bl` expansion, item 6). Proved by induction on `N`
  over a new four-term addition interchange `(a+b)+(c+d) ≈ (a+c)+(b+d)` (`Cadd_add_add_comm`, from
  `Cadd_assoc`/`Cadd_comm`); no real `RsumN_add` is needed — the swap is done directly over `Cadd`.
  Completes the additive half of the `CsumN` API alongside the existing `CsumN_congr`. Axiom-clean.
- **Crux frontier (`n = 3`) — tighter γ₁ upper `≤ −0.055`** (`Analysis/GammaOne.lean`, `Rgamma1_le_neg055`):
  the dominant `−6γ₁` contribution to the `Pos Rlambda3` (`λ₃`) certificate, tightened from `−0.0445`
  (`Rgamma1_le_neg445`, artanh depth `T = 2`) to `−0.055` at depth `T = 4` (`gBound200_T4_le_neg055`,
  a kernel `decide`). Diagnosis recorded: the residual gap to the true `γ₁ ≈ −0.0728` is the `gSeq`
  Euler–Maclaurin overshoot `+(ln N)/(2N)` (a *convergence* limit, not bound depth — raising `T`
  further plateaus), whose removal is the remaining `GammaTwoBracket`-scale acceleration (the single
  hardest `λ₃` brick).
- **Crux frontier (`n = 3`) — ζ(2)/ζ(3) brackets toward `Pos Rlambda3`** (`Analysis/ZetaTwo.lean`):
  the named-missing `ζ(2)` upper bound and two-sided `ζ(3)` for the `λ₃` positivity certificate. The
  reusable `zeta_le_partial` (`ζ(s) ≤ S(N) + 1/(N+1)`, the mirror of `zeta_ge_partial`, via the
  decreasing upper sequence `zetaU` and the rigorous tail-overestimate `Σ_{k>N+1} 1/kˢ ≤ 1/(N+1)`)
  gives `ζ(2) ≤ 1.646` (`zeta2_upper`; with `zeta2_lower ≥ 1.63` brackets the Basel constant) and
  `ζ(3) ∈ [1.201, 1.217]` (`zeta3_lower`/`zeta3_upper`, two-sided Apéry). These discharge two of the
  constant-precision inputs the `n = 3` coupling coefficient `Pos Rlambda3` needs (the dominant
  remaining gap is the tight two-sided `γ₁`). Axiom-clean.

- **Track 1 (item 1 — the Γ place on the strip) — the complex digamma term**
  (`Analysis/ComplexDigamma.lean`, increment 1): the archimedean `Γ′/Γ` series
  `ψ(s) = −γ + Σ_{n≥0} [1/(n+1) − 1/(s+n)]` lifted to complex `s` with `Re s ≥ c > 0` (the strip) —
  the piece of item 1 the real-line `Gamma.lean` does not provide. Built from the complex reciprocal
  `Cinv` ALONE (no `Cpow`/`Clog`), so it is entirely free of the `1/16` value-identity barrier. The
  term layer: the shifted argument `s+n` (`CdigammaArg`), its modulus-squared floor `|s+n|² ≥ c²`
  (`ofQ_le_CnormSq_CdigammaArg`, from `(Re s+n)² ≥ c²` and `(Im s)² ≥ 0`) and the resulting positivity
  witness `CdigammaArg_witness` (squared-floor analogue of the real `digammaArg_witness`), and the
  complex term `CdigammaTerm = 1/(n+1) − 1/(s+n)`. Per-term bounds, regular partial sums, and the
  limit object `CDigamma` follow in later increments via the generic `RReg_of_real_bound` engine.
  Axiom-clean.
  - **Increment 2a — the factored telescoping identity** `Cterm_n = (s−1)·P_n` with
    `P_n = 1/(n+1)·1/(s+n)` (`CdigammaTerm_factored`, complex analogue of the real
    `digammaTerm_eq_factored`). The engine is the abstract reciprocal-difference identity
    `Cadd_neg_eq_mul_of_inv` (`P − I ≈ (a−Q)·(P·I)` whenever `a·I ≈ 1`, `Q·P ≈ 1`, the ℂ analogue of
    `Rsub_eq_mul_of_inv`), instantiated with `a = s+n` (`Cmul_Cinv`) and `Q = n+1`
    (`Cmul_natSucc_inv`), then `(s+n)−(n+1) ≈ s−1` (`CdigammaArg_sub_succ_eq`). This factorization
    exposes the `O(1/n²)` decay (the `1/(n+1)` and `1/(s+n)` summands each only `O(1/n)`), the
    prerequisite for the per-term bounds.
  - **Increment 2b/2c — the per-term component bounds** `|Re P_n| ≤ 1/((n+1)n)` and
    `|Im P_n| ≤ B/((n+1)n)` (`|Im s| ≤ B`), via the inverse-comparison helper `x·(1/N) ≤ 1/x` when
    `x² ≤ N` (no cancellation), the modulus-squared floors `|s+n|² ≥ σ_n²` and `|s+n|² ≥ n`
    (`CnormSq_CdigammaArg_ge`), and the real-line `digamma_Rinv_le`. `Re P_n = F·(σ_n/N) ≤ F·(1/n)`
    and `Im P_n = F·((−Im s)/N)` bounded two-sidedly via an abstract product lemma. This is the
    `O(1/n²)` decay made rational — the input the generic `RReg_of_real_bound` engine needs.
  - **Increment 2d — the full term-component bounds** `|Re Cterm_n| ≤ (B1+B2²)/((n+1)n)` and
    `|Im Cterm_n| ≤ (B1·B2+B2)/((n+1)n)` (`|Re s−1| ≤ B1`, `|Im s| ≤ B2`), via
    `CdigammaTerm_re_bound`/`_im_bound`. From `Cterm = (s−1)·P`, each component is a sum/difference of
    two `±`-bounded products (combined by abstract `cdig_Rsub_prod_bound`/`cdig_Radd_prod_bound` over
    `Rmul_le_mul_of_abs`/`Rneg_mul_le_of_abs`), then collapsed to a single `K/((n+1)n)`. Both
    components are now summable `O(1/n²)` — the regular-partial-sums and `CDigamma` limit follow.
  - **Increment 3 — the limit object `CDigamma`** (the complex digamma on the strip). A generic
    convergence layer (`genSum`/`genTail_two_sided`/`genSum_RReg`) — any real term sequence with
    `|T n| ≤ K/((n+1)n)` has regular `K`-reindexed partial sums — reusing the real-line telescoping
    infrastructure (`digammaRsum`/`digammaMidx`/`digammaTailQ_Midx_le`) and the generic
    `RReg_of_real_bound` engine. Instantiated for both `Re Cterm` and `Im Cterm`
    (`CdigammaReSum_RReg`/`CdigammaImSum_RReg`), giving the **constructive complex
    `ψ(s) = −γ + Σ_{n≥0}[1/(n+1) − 1/(s+n)]`** as `⟨Rlim Re-sums, Rlim Im-sums⟩` (the `Ceta`/`Czeta`
    componentwise-limit pattern), with `−γ` on the real part. This is **item 1's barrier-free
    archimedean piece complete**: the real-line `Digamma` lifted to complex `s` on the strip, built
    from `Cinv` alone.
  - **Increment 4 — the complex Spouge bracket** `c₀ + Σ_{k=1}^N cₖ/(s+k)` (`CspougeBracket`), the
    `Cinv`-sum core of the complex Spouge `Γ` on the strip. Mirrors the real `spougeBracketAux` with
    `Rinv → Cinv` and the real coefficients scaled in via `ofReal`, reusing the `CdigammaArg`
    reciprocal-witness machinery — barrier-free (no `Cpow`/`Clog`). Non-vacuity `cspougeBracketWitness`
    at `s=1, a=4, N=2`. Note: the complex `Cpow`/`Clog` *definition* needs only the argument ratio
    `< 1` (not the `1/16` value identity, which is only for additivity *properties*), so the base power
    `(s+a)^{s+½}` and the full `Γ` assembly are buildable barrier-free by choosing the Spouge shift `a`
    large enough to keep the base's argument small — the remaining item-1 pieces.
  - **Increment 5 — the complex Spouge `Γ` approximant `CSpougeGamma`** (item 1's `Γ(s/2)`-on-the-strip
    object). The faithful complex lift of the real `SpougeGamma`: `Γ(s+1) ≈ (s+a)^{s+½}·e^{−(s+a)}·[c₀ +
    Σ_{k=1}^N cₖ/(s+k)]` for complex `s` (`Re s ≥ c > 0`), assembled from `Cpow` (base power), `Cexp`,
    and the `CspougeBracket`. The base power's `Clog`/`Carg` need only the argument-ratio bound `< 1`
    (a caller hypothesis, satisfied by taking the shift `a` large relative to `|Im s|`) — not the
    `1/16` value identity — so the construction is barrier-free; positivity witnesses
    (`CspougeBase_cnormSq_witness`/`_re_witness`, floor `|s+a|² ≥ c²`) come from the floor `c`. As for
    the real `SpougeGamma`, this is the constructive approximant object (no `Ceq` to the true `Γ`
    asserted). **Item 1's complex `Γ` on the strip is now built** (object-level), alongside the
    barrier-free complex digamma `CDigamma`.
  - **Increment 6 — the direct `Γ(w)` Spouge variant `CSpougeGammaW`** (`Re w > 0`), the
    strip-applicable form for `Γ(s/2)` (`Re(s/2) ∈ (0,½)`). `Γ(w) ≈ (w+b)^{w−½}·e^{−(w+b)}·[c₀ +
    Σ_{k=1}^N cₖ/(w+(k−1))]` (Spouge with `z = w−1`, base shift `b = a−1`, terms `1/(w+(k−1))`). Unlike
    `CSpougeGamma(w−1)`, every node (`w+b`, `w+(k−1)` for `k ≥ 1`) keeps `Re > 0` for `Re w > 0`,
    `b ≥ 0`, so it is valid throughout the strip — the prerequisite for assembling
    `ξ(s) = ½ s(s−1) π^{−s/2} Γ(s/2) ζ(s)` (item 2; the other factors `π^{−s/2}` via `Cpow` over the
    real `Rpi` base, and `ζ` via `CzetaStrip`, are in hand).
- **Track 1 (item 2 — the completed ξ, assembled)** (`Analysis/ComplexXi.lean`). The conductor factor
  `π^{−s/2} = exp((−s/2)·log π)` (`CpiPow`) built from the *real* `log π = Rlog_pi` (`Pi.lean`) embedded
  as `⟨log π, 0⟩` — sidestepping the complex `Clog`/`Carg`/`cnormSq` of `π` entirely (no `1/16` barrier,
  and no infeasible `Rpi²` `whnf`; `Rlog_pi` stays an opaque atom). The polynomial prefactor `½·s·(s−1)`
  (`CxiPoly`, entire, taming `ζ`'s pole at `s=1`), and the **product assembly**
  `Cxi s gammaHalf zeta = ½s(s−1)·π^{−s/2}·Γ(s/2)·ζ(s)` (`Cxi`), with the heavy-data factors `Γ(s/2)`
  (via `CSpougeGammaW` at `s/2`) and `ζ(s)` (via `CzetaStrip`) passed as already-built values to keep
  the interface clean. This is the constructive **assembly** of ξ from the item-1 / Track-1 pieces; the
  analytic *properties* (functional equation, order-1 bound, Hadamard) of items 3–5 are separate and
  not asserted. Axiom-clean.
- **Track 1 — `Rlim` congruence infrastructure** (`Analysis/RlimProps.lean`): `Rlim_congr` (pointwise
  `≈` regular sequences have `≈` diagonal limits — from `Req` at index `4n+3`, since `2/(4n+4) ≤
  2/(n+1)`) and `Rlim_neg` (`lim(−X) ≈ −lim X`, seq-equal hence definitional). The limit-level
  congruences any property/convergence argument over `Rlim`-built objects needs — e.g. the complex
  digamma's symmetries and the eventual `CSpougeGamma → Γ` convergence. Axiom-clean. Also
  `Rinv_congr` (`1/x ≈ 1/y` from `x ≈ y`, across different positivity witnesses — via the cancellation
  `1/x ≈ (1/x)(y/y) ≈ (1/x)(x/y) ≈ 1/y`, no witness-dependent reindexing), filling a previously-missing
  reciprocal congruence.
- **Track 1 — real-part conjugation invariance of the complex digamma** `Re ψ(s̄) = Re ψ(s)`
  (`CDigamma_re_conj`, `Analysis/ComplexDigammaConj.lean`), a genuine *property* of the constructed
  `CDigamma`. Since `Re(1/(s+n)) = (Re s+n)/|s+n|²` and `|s+n|²` is conjugation-invariant (`Im` enters
  only squared, `CnormSq_CdigammaArg_conj`), every term's real part agrees (`CdigammaTerm_re_conj`, via
  `Rinv_congr`), so the two real-part partial-sum sequences are pointwise `≈` (`genSum_congr`) and their
  diagonal limits agree (`Rlim_congr`). This is the archimedean face of ξ's conjugate-pair zero
  symmetry; the line `Re ψ(1/4 + iτ/2)` of Track 2 is its instance. The first verified analytic
  property atop the item-1 objects (advancing beyond the approximant constructions). Axiom-clean.
  Now extended to the **full conjugation symmetry** `ψ(s̄) = conj ψ(s)` (`CDigamma_conj`, a `Ceq`):
  the imaginary part flips, `Im ψ(s̄) = −Im ψ(s)` (`CDigamma_im_conj`), since `Im(1/(s+n)) = −Im s/|s+n|²`
  negates under `s ↦ s̄` while `|s+n|²` stays fixed — proved via the new generic `genSum_neg`
  (`Σ(−T) = −ΣT`) and `RReg_neg` (regularity preserved under negation), then `Rlim_neg`. This is the
  archimedean place's reflection symmetry (ξ's conjugate-pair zero structure), and it exercises the
  full `Rlim_congr`/`Rlim_neg`/`Rinv_congr` toolkit.
- **Track 1 — conjugation symmetry of the completed ξ, reduced to the Γ/ζ factor symmetries**
  (`Analysis/ComplexXiConj.lean`): `ξ(s̄) = conj ξ(s)` (`Cxi_conj`) — the structural symmetry behind
  ξ's conjugate-pair zeros. Two factors are conjugation-symmetric outright: the conductor `π^{−s/2}`
  (`CpiPow_conj`, via the reusable `Cexp_conj`, no `Clog`/modulus baggage) and the polynomial
  `½s(s−1)` (`CxiPoly_conj`, pure ℂ-ring algebra). The `Γ(s/2)` and `ζ(s)` factors enter `Cxi` as
  supplied values, so their conjugation is taken as explicit hypotheses and `Cxi_conj` distributes
  `Cconj` through the product — isolating the genuine remaining content (the Γ conjugation, a large
  `Clog`/`Cpow` chain; the ζ conjugation) as named audit-visible hypotheses, the program's standard
  relocation. Axiom-clean.
- **Track 1 — the complex digamma value anchor** `ψ(1) = −γ` (`CDigamma_one`,
  `Analysis/ComplexDigammaValue.lean`): the convention witness that the constructed `CDigamma` is
  genuinely `Γ′/Γ` (complex lift of the real `Digamma_one_eq_neg_gamma`). At `s = 1` the factored term
  `Cterm_n = (s−1)·P_n` vanishes (`CdigammaTerm_one_eq_zero`, since `s−1 = 0` via `Cadd_neg` and
  `0·P = 0`), so both real and imaginary partial sums are pointwise `≈ 0` and their limits vanish
  (`CDigammaCore_one_eq_zero`, via `genSum_congr` to the all-zero sequence + the reusable `Rlim_zero`),
  giving `ψ(1) = −γ + 0 = −γ`. Also adds the reusable `Rlim_zero` (pointwise-`0` regular sequence ⟹
  limit `0`) and `genSum_const_zero`. Axiom-clean.
- **Track 1 — left-sector argument additivity** `CargLeft(zw) = CargLeft z + Carg w`
  (`Analysis/ComplexArgLeftAdd.lean`): left-half-plane `z` (`Re z < 0`) times principal `w`, the
  product again left. Reflects the principal `Carg_add` through the `+π` shift via `−(zw) = (−z)·w`
  (`Cneg_Cmul_left`): both `−z` and `w` are right half-plane, so `arg(−(zw)) = arg(−z) + arg w` and
  the `+π` regroups to `(arg(−z) + π) + arg w = CargLeft z + Carg w`. With this, the cross-sector
  additivity `arg(zw) = arg z + arg w` is now proved in all four sectors (principal, upper, lower,
  left) — argument additivity over the whole punctured plane. Axiom-clean.
- **Track 1 — the left-half-plane argument (full-plane atan2)** `CargLeft` (`Analysis/ComplexArgLeft.lean`)
  with the `π` values (`Analysis/TanPiQuarter.lean`): `cos π = −1`, `sin π = 0` (`Rcos_pi`/`Rsin_pi`,
  double-angle on `π/2 = Rpi_half`), the π-shift formulas `sin(x+π) = −sin x`, `cos(x+π) = −cos x`
  (`Rsin_add_pi`/`Rcos_add_pi`), and `CargLeft z = arg(−z) + π` for `Re z < 0` with genuine tangent
  `tan(CargLeft z) = Im z/Re z` (`CargLeft_tan`, value identity on `−z` + π-shift, `tan(A+π) = tan A`).
  With the principal `Carg`, `CargUpper`, and `CargLower`, the argument is now defined over the whole
  punctured plane near the four axes — the `Re z < 0` quadrants of `atan2`. Axiom-clean.
- **Track 1 — the general complex power** `z^w = exp(w·log z)` (`Analysis/ComplexPowGen.lean`,
  `Cpow`), the bridge from item 0's complex logarithm to item 1's complex Γ. Where `ncpow` gives only
  `n^s` for a *natural* base `n ≥ 2` (the ζ Dirichlet terms), `Cpow` raises a *complex* base on the
  principal sector — needed for Spouge's `(z+a)^{z+1/2}` in `Γ(s/2)` and `π^{−s/2}` in `ξ`. Defined as
  `Cexp(w·Clog z)`; the exponent law `z^{w₁+w₂} = z^{w₁}·z^{w₂}` (`Cpow_add_exp`) is immediate from
  `Cexp_add` + distributivity, and the **base law `(zw)^v = z^v·w^v`** (`Cpow_mul_base`) follows from
  the `Clog` additivity of item 0 (`Clog_add`) + distributivity + `Cexp_add` — concretely bridging
  item 0 to item 1. Axiom-clean (`{propext, Quot.sound}`).
- **Track 1 — the lower-sector argument + its additivity** `CargLower` (`Analysis/ComplexArgLower.lean`):
  for `Im z < 0`, `arg(z) = −arg(z̄)` (`CargLower z = −CargUpper(Cconj z)`, `z̄` upper). Genuine
  tangent `tan(CargLower z) = Im z/Re z` (`CargLower_tan`, from `CargUpper_tan` of `z̄` + sin-oddness /
  cos-evenness), and additivity `CargLower(zw) = Carg z + CargLower w` (`CargLower_add`) — the
  conjugate reflection of `CargUpper_add` through `Cconj_Cmul` (`z̄w̄ = (zw)‾`) and `CargUpper_congr`.
  Completes the argument across all four wedges near the axes (ξ's zeros are conjugate pairs).
  Axiom-clean (`{propext, Quot.sound}`).
- **Track 1 — ★★ cross-sector complex-logarithm additivity** `Clog(zw) = Clog z + Clog w` past
  `|arg| < π/4` (`Analysis/ComplexLogUpperAdd.lean`, `ClogUpper_add`): `ClogUpper(zw) = Clog z +
  ClogUpper w` for principal `z` × upper `w` (product upper). Real half from the modulus hypothesis
  `hmod` + `Rmul_distrib` (as in `Clog_add`); imaginary half the *fully discharged* cross-sector
  argument additivity `CargUpper_add`. The complex logarithm is now additive across the
  principal/upper boundary — the second-sector capstone of substrate item 0. Axiom-clean.
- **Track 1 — ★★ cross-sector argument additivity** `arg(zw) = arg z + arg w` across the
  principal/upper boundary (`Analysis/ComplexArgUpperAdd.lean`, `CargUpper_add`):
  `CargUpper(zw) = Carg z + CargUpper w` for principal `z` (`Re z > 0`) × upper `w` (`Im w > 0`),
  product upper, all ratios `< 1/16`. The clean reduction via the coordinate swap `swapC z =
  ⟨Im z, Re z⟩`: `CargUpper z = π/2 − Carg(swapC z)` and the exact identity `swapC(zw) = swapC w · z̄`
  (`swapC_Cmul_Cconj`, componentwise), so `CargUpper(zw) = π/2 − Carg(swapC w · z̄) =
  π/2 − Carg(swapC w) − Carg(z̄) = CargUpper w + Carg z` — reusing the principal `Carg_add` and the
  conjugate symmetry `Carg_conj`. Reusable congruence gaps filled: `Rdiv_congr` (division respects
  `≈`, via denominator cancellation `Rdiv_mul_cancel`/`Rmul_right_cancel` — no `Rinv`-congruence
  needed) and `Carg_congr` (the argument respects `≈`). Axiom-clean (`{propext, Quot.sound}`). The
  argument is now additive across `|arg| < π/4`, not only within it.
- **Track 1 — ★ argument conjugate symmetry** `arg(z̄) = −arg z` (`Analysis/ComplexArgUpper.lean`,
  `Carg_conj`): `Carg(Cconj z) = −Carg z`. Since `Cconj z = ⟨Re z, −Im z⟩` has ratio `−(Im z/Re z)` and
  `arctan` is odd (`RarctanR_neg`, via `RarctanR_congr` on the ratio `Rmul_neg_left`). A building block
  of cross-sector additivity (it turns a subtracted angle into a conjugate factor). Axiom-clean.
- **Track 1 — `arctan` is odd** `arctan(−t) = −arctan t` (`Analysis/RArctanValue.lean`,
  `RarctanR_neg`, with rational `arctanTerm_neg`/`arctanSum_neg`) — the conjugate symmetry of the
  argument (`arg(z̄) = −arg z`), since `arctan` sums only odd powers. From the artanh-term oddness
  `artTerm_neg` (`(−1)ⁿ` factor preserved). A foundational reusable property toward the cross-sector
  argument additivity. Axiom-clean (`{propext, Quot.sound}`).
- **Track 1 — the complex logarithm past `|arg| < π/4`** (`Analysis/ComplexLogUpper.lean`,
  `ClogUpper`): `ClogUpper z = ½·log|z|² + i·(π/2 − arctan(Re/Im))` on the upper sector (`Im z > 0`,
  `|Re/Im| ≤ ρ < 1`, i.e. `|arg| ∈ (π/4, π/2]`) — the extension of the principal `Clog` past its
  `|arg| < π/4` domain. Real part = the same genuine modulus log `½·log|z|²`; imaginary part = the
  genuine second-sector argument `CargUpper` (`CargUpper_tan`). Anchored by `Im (ClogUpper i) = π/2`
  (`ClogUpper_I_im`, i.e. `log i = i·π/2`). Axiom-clean (`{propext, Quot.sound}`). (Cross-sector
  additivity — the full-plane atan2 — is the following brick.)
- **Track 1 — ★ the upper-half argument is genuine** `tan(CargUpper z) = Im z/Re z`
  (`Analysis/ComplexArgUpper.lean`, `CargUpper_tan`): `sin(CargUpper z) = (Im/Re)·cos(CargUpper z)`
  for `Im z > 0`, `Re z` apart from `0`, `|Re/Im| ≤ ρ < 1/16` (the steep wedge off the imaginary
  axis). Confirms the second-sector argument `CargUpper z = π/2 − arctan(Re/Im)` is the genuine
  argument (not just a definition): the reciprocal reduction gives `tan(π/2 − arctan(Re/Im)) =
  1/(Re/Im) = Im/Re`. Built from the real-argument value identity `RarctanR_value_eq`
  (`tan(arctan(Re/Im)) = Re/Im`), the real complementary tangent `Rsin_cos_pi_half_sub_tan_real`, and
  the reciprocal `(Im/Re)·(Re/Im) = 1` (`Rmul_Rinv_self`). The second-sector analogue of the
  principal-sector `tan(Carg z) = Im/Re`. Axiom-clean (`{propext, Quot.sound}`).
- **Track 1 — ★★ the real-argument value identity** `sin(arctan t) = t·cos(arctan t)` for a REAL
  argument `t` (`Analysis/RArctanValue.lean`, `RarctanR_value_eq`) — the keystone lifting the
  rational `Rsin_arctan_value_eq` (fixed `t₀`, the heart of `tan(arctan t₀)=t₀`) to a real ratio, as
  `Carg z = arctan(Im z/Re z)` and its reciprocal extension require. The lift is NOT naive
  approximation (which blows up the Lipschitz constant via the approximants' denominators): it clones
  the nested-diagonal bridge directly for `RarctanR t`, sampling the argument at one deep index
  `q = t.seq(Rartanh_R ρ D)` per diagonal step, where the `t₀`-parametric composition lemmas
  (`cos_nested_general`/`sin_nested_general`, `|t₀| ≤ ρ`) apply — so all bounds stay `ρ.den`-based.
  `Rcos_RarctanR_nested` / `Rsin_RarctanR_nested` are the cos/sin real-argument nested bounds (the
  `Rmul` reconciliation is `X`-regularity, argument-agnostic). The capstone triangle:
  `sin(arctan t).seq n →[Rsin nested] peval(sin∘arctan) q (2D+1) →[degree shift, exact]
  q·peval(cos∘arctan) q (2D) →[Rcos nested] q·(Rcos(arctan t)).seq R →[reg] t·cos`, the new leg over
  the rational case being the factor reconciliation `q ↦ t` (sin-shift factor `q` vs `Rmul` factor
  `t`), discharged by `t`-regularity and the `|Rcos| ≤ expM_U 1 2` bound (`altSum_abs_le_U`). The
  sqrt-free real-argument `tan∘arctan = id` — the substrate of the reciprocal `Carg`/`Clog` lift.
  Axiom-clean (`{propext, Quot.sound}`).
- **Track 1 — ★ the reciprocal/complementary tangent** `tan(π/2 − A) = 1/tan A`
  (`Analysis/TanPiQuarter.lean`, `Rsin_cos_pi_half_sub_tan` + `TanReal.compl`) — the value-level
  engine of the reciprocal reduction `arctan t = π/2 − arctan(1/t)`, which is how the argument axis
  reaches `|arg| ≥ π/4`. From the complementary formulas `sin(π/2 − x) = cos x`, `cos(π/2 − x) = sin x`
  (`Rsin_pi_half_sub` / `Rcos_pi_half_sub`, themselves from `Rsin_sub` / the new `Rcos_sub` and the
  `π/2` values) and `sin A = s·cos A`: if `A` has tangent `s` and `t·s = 1`, then `π/2 − A` has
  tangent `t` (`t·cos(π/2−A) = t·sin A = t·s·cos A = cos A = sin(π/2−A)`). `TanReal.compl` packages
  this as a bundle operation, so a small-argument leaf (`|s| < 1/16`) yields a LARGE-tangent angle
  that still composes with `.add`/`.step` — tangents beyond the value-identity radius are now
  constructible (`tan_pi_half_sub_arctan_eighteen`: `tan(π/2 − arctan(1/18)) = 18`). Axiom-clean
  (`{propext, Quot.sound}`). (The full-plane `Carg` atan2 with quadrant `±π` shifts is the next brick.)
- **Track 1 — ★ `tan(π/4) = 1` and the `π/2` values `cos(π/2) = 0`, `sin(π/2) = 1`**
  (`Analysis/TanPiQuarter.lean`, `sin_eq_cos_pi4` / `Rcos_pi_half` / `Rsin_pi_half`) — the anchors of
  the **full-range complex argument** (`Carg`/`Clog` past the principal sector `|arg| < π/4`, via the
  reciprocal reduction `arctan t = π/2 − arctan(1/t)`). The obstacle this clears: the value identity
  `sin(arctan t) = t·cos(arctan t)` (`Rsin_arctan_value_eq`) holds only for `|t| < 1/16` (the
  nested-composition radius forced by `DN_arctan_decay`), but Machin's
  `π = 16·arctan(1/5) − 4·arctan(1/239)` uses `1/5 > 1/16`. The fix is **Gauss's Machin-like formula**
  `π/4 = 12·arctan(1/18) + 8·arctan(1/57) − 5·arctan(1/239)`, all three arguments `< 1/16` (common
  radius `ρ = 1/18`): the value identity applies to each leaf, and the 25-leaf chain is built through
  `Rsin_cos_add_tan` (which needs only `1 − ab > 0`, never that the *output* tangent is small), so the
  running tangent climbs to exactly `1` while every step's `|running·leaf| ≤ 0.039`. A `TanReal` bundle
  (`angle`, rational `tan`, `sin = tan·cos`) with `.add`/`.retag`/`.step` carries the chain (each
  step's tangent relabelled to a `Qeq`-equal literal to keep the positivity `decide`s shallow); the
  exact rational tangent of the combination is `vval`-checked to be `1`, giving `sin(π/4) = cos(π/4)`.
  Double-angle on `π/2 = 2·(π/4)` (`Rcos_add_of_tan`, `Rsin_add_of_tan`) then yields
  `cos(π/2) = 1 − 1·1 = 0` and, via Pythagoras, `sin(π/2) = 2·cos²(π/4) = 1`. Axiom-clean
  (`{propext, Quot.sound}`). (Consistency `Rpi = 4·Spi4.angle` with the Machin `Rpi` of `Pi.lean`, and
  the reciprocal arctan reduction + lift to `Carg`/`Clog`, are the following bricks.)
- **Track 1 — ★ the arctan addition law** `arctan a + arctan b = arctan((a+b)/(1−ab))`
  (`Analysis/ArctanTan.lean`, `Rarctan_add` / `Rarctan_add_of_small`): the imaginary half of `Clog`
  additivity, built on the value-level `tan` substrate below. The chain: the abstract
  tangent-addition capstone `Req_add_of_tan_values` (the arctan analog of `Req_add_of_exp_values` —
  `A+B=C` from the tangent *values* via `Rsin_cos_add_tan` + tangent-injectivity `Rtan_inj`); the
  `RsinAux` apartness `Pos_RsinAux_of_small` (`sin w/w ≥ 1/2` for `|w| ≤ 1`, since the degree-2 head
  `1−w²/6+w⁴/120 ≥ 5/6` by `altSum_sin_two_ge` and the tail is `≤ 2/6` by `altSum_trunc_bound`); and
  the angle-difference magnitude bound `Rarctan_diff_seq_le` (each angle `≤ 2ρ` via `Rarctan_seq_abs_le`
  + `geoSum_le_two`, so the `Radd`/`Rsub`-reindexed difference is `≤ 6ρ ≤ 1` via `Qmul_two_le_third`
  from `16ρ < 1`). `Rarctan_add_of_small` then makes the apartness automatic — the law holds for any
  `|a|, |b|, |(a+b)/(1−ab)| ≤ ρ` with the shared `ρ < 1/16` thicket and `1 − ab > 0`. **Lifted to real
  arguments** (`RarctanR_add_real_via`): `arctan s + arctan t = arctan((s+t)/(1−st))` for reals `s, t`
  with `Y = RarctanR(vvalReal s t)` — the arctan analog of `Rartanh_add_real_via`, cleaner since the
  `vval` denominator is sign-robust (no `wvalR`-style split). Two legs through
  `W = arctanSum(vval(s_P,t_P),·)`: the argument-variation `arctanSum_vval_argdiff`
  (`≤ 12(|a−a'|+|b−b'|)`) and the combination `RarctanConst_add_vval_rho` (= `Rarctan_add_of_small`
  read at the diagonal index). **Packaged as complex argument additivity** `arg(zw) = arg z + arg w`
  (`Analysis/ComplexArgAdd.lean`, `Carg_add`): for `z, w` with `Re z, Re w, Re(zw)` apart from `0` and
  the three ratios `Im/Re ≤ ρ < 1/16`, `Carg(zw) = Carg z + Carg w`. The bridge is the complex-division
  **ratio identity** `Im(zw)/Re(zw) ≈ vvalReal(ratio z, ratio w)`, proved by cross-multiplication: the
  `vvalReal` defining relation `vvalReal_rel_via` (`V·(1−st) ≈ s+t`, the rational `vval_rel` lifted to
  the diagonal by regularity) feeds the real-algebra cross-identity `ratio_cross_via`
  (`vvalReal(r_z,r_w)·Re(zw) = Im(zw)`), which together with `Rdiv_mul_cancel` and `Rmul_right_cancel`
  gives the identity; then `RarctanR_congr` + `RarctanR_add_real_via` close it. **This completes the
  imaginary (harder) half of `Clog` additivity.**
- **Track 1 — ★ complex logarithm additivity** `Clog(zw) = Clog z + Clog w` (`ComplexArgAdd.lean`,
  `Clog_add`): the capstone of substrate item 0. `Clog z = ½·log|z|² + i·arg z`, so additivity splits
  into the modulus half (`RlogPos`-multiplicativity) and the imaginary half (`Carg_add`, fully
  discharged). `Clog(zw).re = ½·log|zw|² ≈ ½(log|z|²+log|w|²) = Clog z.re + Clog w.re` (`Rmul_distrib`),
  `Clog(zw).im = Carg(zw) = Carg z + Carg w` (`Carg_add`). The general positive-real
  log-multiplicativity `log|zw|² = log|z|²+log|w|²` (via `cnormSq_mul` + `Rlog_mul` + integer-part
  telescoping) is the one explicit audit-visible hypothesis, isolated exactly as the program isolates
  each heavy input — RH-*independent*, no smuggling. Crux fields stay `none`.
- **Track 1 — ★ the `Clog_add` modulus seam discharged for bounded moduli** (`Analysis/RlogMulPos.lean`,
  `Analysis/ClogAddBounded.lean`): the `hmod` hypothesis of `Clog_add` is now a **theorem**, not an
  assumption, in the small-radius regime (squared moduli `1 ≤ |z|², |w|² ≤ B`). The substrate stack:
  `reindex_Req` (a regular sequence reindexed past its tail presents the same real); `Rlog_congr`
  (`Rlog` is a congruence in its argument at small radius, `tmap_lip` lifted through `Rartanh_congr`);
  `RlogPos_unfold` (`RlogPos x k = Rlog (reindexed x) Mx` at the auto-derived radius, definitional);
  the **`RlogPos → Rlog` bridge** `RlogPos_eq_Rlog` (auto-radius log = presented-radius `Rlog x B`,
  routed through `Rartanh_radius_indep` `Mx→B` then `Rlog_congr` along `reindex_Req` — crucially only
  `B` need be small, not the loose auto-radius); `RlogPos_mul` (`log(xy) = log x + log y` for positive
  reals in `[1,B]`, bridging all three `RlogPos` calls into `Rlog_mul`); and `RlogPos_congr` (carrying
  `RlogPos` across `≈`). Assembled in `RlogPos_cnormSq_mul` — exactly the `hmod` proposition,
  `log|zw|² = log|z|²+log|w|²`, from elementary positivity/bound data via `cnormSq_mul`. The capstone
  `Clog_add_bounded` then states `Clog(zw) = Clog z + Clog w` with **no** `RlogPos`-multiplicativity
  hypothesis. Crux fields stay `none`.
- **Track 1 — ★★ symmetric-band `Clog` additivity (signed-τ)** (`Analysis/RlogMulSigned.lean`):
  `Clog_add_signed` extends the modulus-seam discharge from `[1,B]` to the **symmetric band**
  `[1/B, B]` — squared moduli on *either* side of 1 (the realistic Hadamard regime, where the
  `artanh` argument `tmap(x.seq)` turns negative). The signed substrate, built bottom-up via the
  **oddness route** that sidesteps re-deriving the `t≥0` corner bounds: `exp(2·artanh τ)=(1+τ)/(1−τ)`
  for `τ<0` follows from the nonneg case by `artanh(−σ)=−artanh σ` (`Rartanh_neg`) + exp-of-negation
  (`Rexp_TwoArtanh_of_neg`), unified sign-agnostically (`Rexp_TwoArtanh_signed_rho`). Then the signed
  addition law `TwoArtanh_add_wvalR_rho` (three signed exp-identities through `Req_add_of_exp_values_gen`
  + the signed multiplicativity `wvalR_hg`), its `×2`-strip `RartanhConst_add_wvalR_rho`, the signed
  real lift `Rartanh_add_real_via_signed` (the arg-variation/`wvalR` den-positivity legs were already
  sign-agnostic), the signed real log-multiplicativity `Rlog_mul_signed` (`tmap_abs_lt_one` two-sided
  + `wvalR_tmap_seq_bound_signed`), `RlogPos_mul_signed`, and the assembly
  `RlogPos_cnormSq_mul_signed`/`Clog_add_signed` (witness from a lower bound, `pos_witness_of_mulM_ge`,
  since the squared-modulus product may dip below 1). Crux fields stay `none`.
- **Track 1 — ★★★ general-modulus complex `Clog` additivity (`ρ<1` relaxation)** (`Analysis/RadiusGen.lean`):
  `Clog_add_gen` removes the small-radius cap entirely — `Clog(zw) = Clog z + Clog w` with the modulus
  seam `hmod` discharged for squared moduli in `[1/B, B]` at **any** `B ≥ 1`. The load-bearing
  finding: `ρ²≤1/2` was never needed for convergence, only for the clean constant `2`; the artanh
  reindex `(ρ.den²+4ρ.den)(n+1)` already absorbs the general even-sum bound `Σρ^{2k} ≤ 1/(1−ρ²) ~
  ρ.den/2`, with the **canonical `K = ρ.den`** valid for every `ρ<1`. The full `_gen` stack (~20
  lemmas): `geoEvenSum_le_gen` → `Rartanh_congr_gen`/`artSum_depth_recip_gen`/`Rartanh_radius_indep_gen`
  (continuity) → `Rlog_congr_gen`/`RlogPos_eq_Rlog_gen`/`RlogPos_congr_gen` (bridge) →
  `wval_halfbound_gen` (denominator factor `ρ.den` vs `2`)/`wval_lip1_gen`/`wval_lip2_gen`
  (Lipschitz constant `ρ.den²` vs `4`)/`wval_inner_pos_gen` → `artSum_wval_argdiff_gen`
  (constant `Kσ·ρ.den²`) → `Rartanh_add_real_via_gen` (the real artanh addition diagonal; combination
  leg already radius-agnostic) → `wvalReal_gen`/`tmul_wvalReal_via_gen` (reindex `2ρ.den²(n+1)`
  absorbing the larger constant) → `Rlog_mul_via_gen` → `Rlog_mul_gen` → `RlogPos_mul_gen` →
  `RlogPos_cnormSq_mul_gen` → `Clog_add_gen`. Substrate item 0's modulus seam is now closed at full
  generality. Crux fields stay `none`.
- **Track 1 — ★ value-level `sin(arctan t) = t·cos(arctan t)`** (`Analysis/ArctanODE.lean`,
  `Rsin_arctan_value_eq`): `Req (Rsin (Rarctan t₀)) (Rmul (ofQ t₀) (Rcos (Rarctan t₀)))` for
  `|t₀| ≤ ρ < 1/16`. This **completes the formal-PS → value (FTC) bridge** that lifts the formal
  identity `sin∘arctan = t·(cos∘arctan)` (`sin_arctan_eq`) to the constructive reals — the sole
  remaining gap for argument-additivity, and the `artanh`-free analog of the real `artanh` doubling.
  The full stack, built from scratch on the corner-decay machinery: the closed `C/(n+1)` decay rate
  `DN_arctan_decay` (the `(M+1)²` polynomial absorbs into the geometric base only at `ρ < 1/16`, via
  `sq_le_four_pow`), the reciprocal composition bounds `DN_{sin,cos}_recip`, the degree-shift identity
  `peval_sin_arctan_shift : peval(sin∘arctan,t,m+1) = t·peval(cos∘arctan,t,m)` (no division — `sin =
  t·cos` directly), the diagonal↔peval identifications (`Rcos_seq_eq_peval`, `RsinAux_seq_eq_peval`),
  the argument-Lipschitz bounds (`peval_cosCoeff_Lip`, `peval_{cos,sin}Coeff_arctan_argdiff_recip`,
  via `altSum_Lip_le` + `qsq_diff_le` with `LipS` bounded uniformly by `LipS_le_U`), the geometric
  arctan tail `geoSum_diff_recip`, and the nested-diagonal cores `cos_nested_general`/`sin_nested_general`
  with their real wrappers `Rcos_arctan_nested`/`Rsin_arctan_nested` — the latter handling the **`Rmul`
  reconciliation** (`Rsin = Rmul X (RsinAux X)` evaluates `X` at the outer reindex but `RsinAux`
  internally at a deeper one; the gap `|X.seq R − X.seq D|·|RsinAux|` is killed by `X`'s regularity).
  The final `Req_of_lin_bound` is a 3-term triangle through `peval(sin∘arctan)` and the shift.
  RH-*independent* analytic infrastructure; crux fields stay `none`.

- **The RH witness** (`F1Square/Analysis/RHWitness.lean`) — the constructive witness of RH's forward
  direction (`RH ⟹ λₙ ≥ 0`), exhibited as an object. On the critical line a zero's Cayley factor
  `w = 1−1/ρ` has unit modulus; unit modulus survives every power via the Atlas composition norm
  (`cnormSq_npow` over `cnormSq_mul`, the Brahmagupta–Fibonacci / Hurwitz two-square identity), so
  `|wⁿ|² = 1`, hence `Re(wⁿ) ≤ 1` with NO `sqrt` (`Rle_of_Rmul_self_le`). Each Li term `1 − Re(wⁿ)` is
  thus manifestly `≥ 0` (`witnessTerm_nonneg`), and the finite witness sum `Σ (1 − Re(wⁿ))` is `≥ 0`
  for every `n` (`witnessSum_nonneg`, `rh_witness`). Strengthened from unit modulus to the **closed
  half-plane** `|w|² ≤ 1` (`Re ρ ≥ ½`, `cnormSq_Cnpow_le_one` via `Rnpow_le_Rnpow`); `rh_witness_onLine`
  is the boundary (on-line) face. The hypothesis IS RH (`onLine_is_unit_modulus`) and is never
  discharged — producing the witness unconditionally is RH itself.
- **The functional-equation reflection + conjugation symmetry** (`F1Square/Analysis/Reflection.lean`)
  — the completed-ζ 4-fold zero symmetry `{ρ, ρ̄, 1−ρ, 1−ρ̄}` realized on the Li growth ratio as exact
  `Real` algebra. Reflection `ρ↦1−ρ`: `cnormSq(1−ρ) = csubOneNormSq ρ`, `csubOneNormSq(1−ρ) = cnormSq ρ`
  (via `Rneg_sq`/`Rneg_Rsub`), so the mirror Cayley ratios are reciprocal (`r(ρ)·r(1−ρ) = 1`), and
  `mirror_both_in_disk_iff`: a zero and its mirror are both in the closed Cayley disk iff `|ρ−1|² = |ρ|²`
  (unit modulus, on the line). Conjugation `ρ↦ρ̄` (`Cconj`) preserves both moduli, hence disk-membership
  (`inClosedDisk_Cconj`); `symmetry_orbit_in_disk_iff` shows the whole orbit lies in the disk iff on the
  line — the structural reason RH's "all zeros in the disk" equals "all zeros on the line". Does not
  prove the zeros are there (RH, untouched).
- **The Voros off-line branch, constructively** (`Reflection.lean`, `Analysis/OffLineGrowth.lean`) —
  `offLine_left_not_inClosedDisk`: a zero left of the line leaves the closed Cayley disk
  (`liRatio_left_of_line` ⟹ `|w|² > 1`), the geometric seed of the off-line branch, *proven*.
  `offLine_term_grows`: its witness term's squared modulus then strictly grows (`|wⁿ⁺¹|²−|wⁿ|² > 0`);
  `witnessTerm_tempered`: on the closed disk the term is bounded in `[0,2]`; `voros_term_dichotomy`
  packages the tempered-vs-exponential alternative at the term level. The step from exponential growth
  to a negative coefficient (phase + saddle-point over the sum) stays the classical interface.
- **The Bombieri–Lagarias pipeline + Li's criterion, both directions** (`Square/BLPipeline.lean`) —
  `Rnonneg_Rlim` (non-negativity passes to a Bishop limit) is the new constructive core. `BLZeroSum`
  carries the BL zero-sum representation and the on-line unit-modulus fact as explicit hypotheses;
  `bl_rh_implies_liNonneg` is the forward direction `RH ⟹ LiNonneg(genuineLamSeq)`. `LiBridge` adds
  the Voros dichotomy (a constructive `∨`, choice-free — grounded as an *asymptotic* theorem,
  Voros/Lagarias + the `n ≳ T²/t` threshold); `liNonneg_implies_onLine` is the reverse; `li_criterion`
  is the full equivalence `LiNonneg(genuineLamSeq) ⟺ AllZerosOnLine`. Both classical inputs are
  explicit `LiBridge` fields, audit-visible; the equivalence is axiom-clean.
- **The constructive Cayley transform — the `onLine_unit` leg DISCHARGED** (`Analysis/CayleyMap.lean`,
  `Square/BLPipeline.lean`). The BL pipeline had carried the on-line unit-modulus fact `|1−1/ρ|² = 1`
  as an explicit `BLZeroSum` hypothesis; it is not independent content — it is forced by the Li
  growth-ratio geometry. `CayleyMap.lean` builds the genuine map `liRatio ρ = (ρ−1)·(1/ρ)` over the
  constructive complex reciprocal (`Cinv`) and proves its modulus law: `cnormSq_recip`
  (`|ρ|²·|1/ρ|² = 1`, from `Cmul_Cinv` through `cnormSq_mul`, no explicit `Rinv` algebra) and
  `cnormSq_liRatio_on_line` (`Re ρ = ½ ⟹ |liRatio ρ|² = 1`, via `liRatio_on_line`). `blZeroSum_ofZeros`
  then builds a `BLZeroSum` from genuine zero data with `onLine_unit` **derived**, not assumed — so the
  BL interface is shrunk to its irreducible classical core (the explicit-formula zero-sum `bl` + its
  convergence `reg`); `bl_rh_implies_liNonneg_ofZeros` is the forward direction from that shrunk
  interface. No `sqrt`, choice-free.
- **The per-zero Li contribution, linearized — the explicit-formula framework's algebraic core**
  (`Analysis/LiLinearize.lean`). `cone_sub_npow_factor` — the geometric factorization
  `1 − wⁿ = (1−w)·Σ_{k<n} wᵏ` for complex `w`, by induction; with `w = 1−1/ρ` (`liRatio`), `1−w = 1/ρ`,
  so it exhibits the first moment `1/ρ` as an explicit factor of every per-zero Li contribution.
  `witnessTerm_eq_linear` — the real part: the `RHWitness` per-zero term
  `1 − Re(wⁿ) = Re((1−w)·Σ_{k<n} wᵏ)`; `witnessSum_eq_linear` lifts it to the pipeline object,
  `witnessSum ws n = Σ_w Re((1−w)·Σ_{k<n} wᵏ)` (the sum the BL `bl` interface equates to `λₙ`).
  Summed over zeros this expresses `λₙ` through the power moments
  `Σ_ρ ρ^{−k}`; that those moments equal the `−ζ′/ζ` Taylor data `ηⱼ` plus the archimedean place (the
  explicit formula / Hadamard factorization) stays the classical interface. Also adds the small complex
  commutative-ring lemmas the substrate had not yet needed (`cmul_czero`, `cadd_zero`, `cmul_cneg`, the
  local congruences) — reusable for any future complex algebra. No zeros placed, no positivity asserted.
- **The closed-disk witness hypothesis IS RH (set-level closure)** (`Analysis/Reflection.lean`,
  `Square/BLPipeline.lean`). `rh_witness_onLine` carried, in prose, that the half-plane (closed Cayley
  disk) witness does not secretly weaken RH; this upgrades it to a theorem. `double_inj` — doubling is
  injective (`x+x = y+y ⟹ x = y`, the constructive "divide by 2" via `half_double`); `onLine_of_ratios_eq`
  / `onLine_iff_ratios_eq` — the converse of `liRatio_on_line` (`|ρ−1|² = |ρ|² ⟹ Re ρ = ½`), so unit
  Cayley modulus is EQUIVALENT to being on the line; `ReflClosed` + `allInClosedDisk_iff_allOnLine` —
  for a reflection-closed zero set, "every Cayley factor in the closed disk" (the witness hypothesis)
  ⟺ `AllZerosOnLine`. Composed in `li_criterion_disk`: `λₙ ≥ 0 ∀n ⟺ every zero's Cayley factor lies in
  the closed unit disk` — Li's criterion in the witness's own geometry, the most natural geometric
  phrasing of RH on this substrate.
- **RH stated about the constructed ζ** (`Analysis/RiemannZero.lean`) — `NontrivialZero` bundles a
  strip point with its `CzetaStrip` convergence certificate and a vanishing proof, making the genuine
  zero set a clean predicate (`isZeroOfZeta`); `RiemannHypothesisStrip := ∀ Z, Re Z.s = ½` is RH for
  the ζ this repo builds, formalized as the open statement it is; `riemannHypothesisStrip_iff` ties it
  to the pipeline's `AllZerosOnLine`.
- **The arithmetic Hodge index ⟺ RH** (`Square/AtlasAnalyticFace.lean`) — `hodgeIndex_iff_RH`:
  `SpectralHodgeNeg(𝕊) ⟺ AllZerosOnLine` (via `genuine_hodgeNeg_iff` + `li_criterion`);
  `hodgeIndex_iff_riemannHypothesis`: `SpectralHodgeNeg(𝕊) ⟺ RiemannHypothesisStrip` — the F1-square
  Hodge index equated end to end to RH about the constructed ζ. `atlas_coupling_analytic_face` bundles
  the geometric and analytic faces. `hodgeIndex_iff_closedDisk` (this release): the same Hodge index ⟺
  every zero's Cayley factor in the closed unit disk (via `li_criterion_disk`) — so the geometric
  Hodge index, Li-positivity, the on-line condition, and the witness's closed-disk geometry are ONE
  connected proposition.
- **Track 1 — ★ REAL log-multiplicativity `Rlog(x·y) = Rlog x + Rlog y`** (`Analysis/ArtanhAdd.lean`,
  `Rlog_mul`), what `Clog` additivity needs (`Re Clog(zw) = Re Clog z + Re Clog w` via
  `log(|z|²|w|²) = log|z|² + log|w|²`). The full binary analog of the doubling `Rlog_sq`, built from
  scratch over many bricks: the rational addition law (below) → the sign-robust division-free addition
  map `wvalR a b = (a+b)/(1+ab)` with its full Lipschitz machinery (`wval_lip1`/`wval_lip2` via the
  certified cleared identities + the constant-`4` denominator estimate `wval_lip1_den` and radius
  half-bound `wval_halfbound`) → the two rational identities `wvalR_rel` and `tmap_mul_wvalR`
  (`tmap(x·y) = wvalR(tmap x, tmap y)`, the bridge `log(xy)↔` the addition map) → the real binary map
  `wvalReal` with regularity → the ★ **capstone** `Rartanh_add_real_via` (the real-argument `artanh`
  addition, binary analog of `Rartanh_double_real_via`: the doubling's single-variable polynomial bound
  `Dterm_recip` has *no* binary analog, so its combination leg is the exact rational law itself,
  `RartanhConst_add_wval_rho`, which inherently relates the depth-`n` `wval` to the depth-`(2n+1)`
  summands; arg-variation by `artSum_wval_argdiff`) → the wiring `Rlog_mul_via`/`Rlog_mul_algebra` →
  `Rlog_mul`, mirroring `Rlog_sq`'s radius bookkeeping (common bound `B`, `x,y ∈ [1,B]` *pointwise* so
  the `artanh` arguments `tmap(·)` are non-negative — `tmap_nonneg_lt_one`; `hbw` via
  `wvalR_tmap_seq_bound`; radius alignment `ρ_B → ρ_{B²}` via `Rartanh_radius_indep`). RH-independent
  interface-shrinking toward `bl`; the crux fields stay `none`.
- **Track 1 — the real `arctan` addition map `vvalReal = (s+t)/(1−s·t)`** (`Analysis/ArtanhAdd.lean`),
  the argument-addition substrate for `Clog`'s imaginary half (`arg(zw) = arg z + arg w`). The full
  `arctan` analog of the `wval`/`artanh` Lipschitz stack: the division-free map `vval a b` with its
  cleared one-sided differences (`vval_argdiff1`/`vval_argdiff2`, factor `1+c²` vs `artanh`'s `1−c²`),
  the radius half-bound `vval_halfbound` (denominator `1−ac`), the strengthened `2c² ≤ 1`
  (`vval_csq_le`, which the `arctan` Lipschitz core needs vs `artanh`'s `c² ≤ 1`), symmetry `vval_comm`,
  inner-positivity `vval_inner_pos` (`1−ab > 0`), the binary Lipschitz bounds `vval_lip1`/`vval_lip2`
  (constant `6`, vs `artanh`'s `4`, on the certified denominator estimate `vval_lip1_den`), and the real
  map `vvalReal` with regularity (`12n+11` reindex absorbing the two Lipschitz-`6` terms, since
  `12·Qbound(12n+11) = Qbound n`). RH-independent; the crux fields stay `none`.
- **Track 1 — ★ the formal identity `sin∘arctan = t·(cos∘arctan)`** (`Analysis/ArctanODE.lean`,
  `sin_arctan_eq`), the formal-power-series shadow of `tan(arctan t) = t` (the sole remaining gap for
  argument-additivity). A complete constructive formal-PS ODE toolkit, built from scratch on the
  `fderiv`/`fmul`/`fcomp` calculus (`ExpLog.lean`): the `sin`/`cos` coefficient ODEs
  (`sin_fderiv : sin′=cos`, `cos_fderiv : cos′=−sin`), the composition chain-rule ODEs
  (`sinComp_deriv : (sin∘arctan)′=(cos∘arctan)·A′`, `cosComp_deriv : (cos∘arctan)′=−(sin∘arctan)·A′`,
  via `fcomp_chain`), the convolution evaluators (`fmul_Xident : (t·H)(k+1)=H(k)`,
  `fmul_onePlusSq : ((1+t²)·H)(k+2)=H(k+2)+H(k)`, `onePlusSq_geomAlt : (1+t²)·A′=1`,
  `absorb_onePlusSq_geomAlt : (1+t²)·(P·A′)=P`, `X_sq_eq_sq2 : X²=t²`), and the **formal ODE-uniqueness
  lemma** `ode_unique` (the discrete `(1+t²)H′=t·H ∧ H(0)=0 ⟹ H=0`, via the coefficient recurrence
  `(k+3)H(k+3)=−k·H(k+1)` and a triple-invariant induction). The capstone applies `ode_unique` to
  `G = sin∘arctan − t·(cos∘arctan)`: `Gseq_ode` shows `(1+t²)G′ = t·G` (both sides collapse to the
  common form `X·S − t²·C`), `Gseq_zero` gives `G(0)=0`, so `G ≈ 0`. **Finding:** this is the formal
  half; lifting it to the value identity `Rsin(arctan t) = t·Rcos(arctan t)` needs the composition-series
  value bridge (convergence/rearrangement, template `Rartanh_double_real_via`/`dcomp_artSum`). RH-*independent*
  analytic infrastructure; crux fields stay `none`.
- **Track 1 — the formal `arctan` ODE `A′(t) = 1/(1+t²)`** (`Analysis/ArctanODE.lean`), the
  alternating sibling of `dgeom_ode`: the arctan coefficient sequence `arctanCoeff` has formal
  derivative `fderiv arctanCoeff = geomAlt` (`arctan_fderiv`, the `1/(1+t²)` coefficients), with the
  `(1+t²)`-annihilation `geomAlt(k+2) + geomAlt(k) ≈ 0` (`geomAlt_recurrence`) and boundary
  `geomAlt 0 = 1`, `geomAlt 1 = 0`. Built on the `fderiv`/`fmul` formal-power-series calculus
  (`ExpLog.lean`). **Finding (sharp diagnosis):** unlike the `artanh` exp engine — whose geometric
  series is *exactly rational-summable* to `(1+w)/(1−w)`, giving an exact value identity — the `arctan`
  series is *not* rational-summable, so this formal ODE does **not** collapse to a value identity. The
  one remaining gap for argument-addition (hence `Clog`'s imaginary half) is precisely the value-level
  inverse-function fact `tan(arctan t) = t` (equivalently `Rsin(arctan t) = t·Rcos(arctan t)`); the
  `vval` algebra, `Rsin_add`/`Rcos_add`, and `Rcos_sq_add_sin_sq` are all already in place around it, so
  only the formal-PS → value (fundamental-theorem-of-calculus) bridge — seeded by `arctan_fderiv` —
  remains. RH-*independent* analytic infrastructure; the crux fields stay `none`.
- **Track 1 — the rational `artanh` addition law** (`Analysis/ArtanhAdd.lean`), the arithmetic heart of
  log-multiplicativity `log(xy) = log x + log y` (hence of `Clog` additivity, hence of the Hadamard
  `log ξ`). `Rexp_twoArtanh_general` packages the heavy `Rexp_two_artanh_ofQ` parameter thicket **once**
  for an arbitrary rational `0 ≤ τ < 1` (the radius-`ρ = τ` analog of `Rexp_twoArtanhRecip`, now at a
  *general* base): with `τ = p/q`, `d = q−p`, the target `g = (q+p)/d = (1+τ)/(1−τ)` and the budget
  `C = (2L+4)q²` clears with slack `(2L+4)q²·d(j+1)²·(d−1) ≥ 0` — clean because `d ≥ 1` (two private
  `Int` lemmas `twoArtanhGen_hM2_int`/`_hBC_int`, the `ring_uor`-slack + `omega` pattern). Then
  `TwoArtanh_add_rat` proves `2·artanh c = 2·artanh a + 2·artanh b` for rationals `0 ≤ a,b,c < 1`,
  gated on the multiplicativity side-condition `(1+c)/(1−c) = ((1+a)/(1−a))·((1+b)/(1−b))` (which is
  exactly `c = (a+b)/(1+ab)`): three instances of `Rexp_twoArtanh_general` feed the exp-injectivity
  additivity core `Req_add_of_exp_values` (`RArctanCongr.lean`). With the continuity `RarctanR_congr`
  (rational→real lift) this is the route to real log-multiplicativity. `Rnonneg_TwoArtanhConst` records
  `2·artanh τ ≥ 0` for `τ ≥ 0`.
  - **`wval` — the division-free addition map** `(a+b)/(1+ab)` (numerator `pa·qb+pb·qa`, denominator
    `qa·qb+pa·pb`), with `wval_den_pos`/`wval_num_nonneg`/`wval_lt` (the last via the slack
    `(qa−pa)(qb−pb) > 0`, the `a,b < 1` margins) and the multiplicativity identity `wval_hg`
    (`(1+wval)/(1−wval) = ((1+a)/(1−a))·((1+b)/(1−b))`, both sides clearing to
    `(qa+pa)(qb+pb)(qa−pa)(qb−pb)` — a pure-`Int` `ring_uor` identity once the `Nat.cast`/`toNat`
    bridges are discharged). `TwoArtanh_add_wval` then gives the addition law in directly-usable form
    `2·artanh(wval a b) = 2·artanh a + 2·artanh b` with the `hg` side-condition discharged once and the
    sum-argument `c = wval a b` computed — leaving only trivial positivity obligations for callers.
  - **Binary Lipschitz core for the real lift** (`wval_argdiff1_cleared`/`wval_argdiff2_cleared`,
    `wvalR`/`wvalR_den_pos`/`wvalR_argdiff1`/`wvalR_argdiff2`). Structural finding: the unary doubling
    lift `Rartanh_double_real_via` works through a *single-variable* polynomial composition
    (`dcomp_artSum`/`peval (fcomp acoef kdbl)`), which binary addition lacks — so its real lift needs a
    genuine two-variable continuity argument over a sign-robust binary map. The certified algebraic
    heart: each one-sided variation of `(s+t)/(1+st)` factors as `(Δ-cross)·(1 − other²)` — pure-`Int`
    `ring_uor` identities, the analog of `uval_diff_cleared`. The sign-robust real-map basis `wvalR`
    (the *whole* `1+ab` numerator under `.toNat`, positive for `|a|,|b| < 1`, unlike `wval` which is
    `≥0`-only) is wired to those identities by `wvalR_argdiff1`/`_argdiff2`: the `Qsub` numerator of a
    one-sided map difference equals `(Qsub a b).num·(qc²−pc²)` resp. `(Qsub c d).num·(qa²−pa²)`.
  - **The binary Lipschitz bound** `|wvalR a c − wvalR b c| ≤ 4·|a − b|` (`wval_lip1`), the analog of
    `uval_lip` for the addition map. Its certified cores: `wval_lip1_den` (the constant-`4` denominator
    estimate `(qc²−pc²)·qa·qb ≤ 4·D(a,c)·D(b,c)`, via `(qa·qc)(qb·qc) ≤ (2D_ac)(2D_bc)`), `wval_halfbound`
    (the radius half-bound `qa·qc ≤ 2(qa·qc+pa·pc)` from `|a|,|c| ≤ ρ`, `ρ² ≤ ½` — the small-radius the
    unary doubling also needed), and `wval_csq_le` (`|c| < 1`, i.e. `pc² ≤ qc²`, from the radius). The
    wrapper composes `wvalR_argdiff1` (numerator `(a−b)(1−c²)`) over the denominator estimate via
    `n·d ≤ n·e` (`n = |a−b|`-cross). (The `wvalReal` regularity and the two-variable diagonal addition
    build on this.)
  RH-independent interface-shrinking toward discharging `bl`; the crux fields stay `none`.
- **Track 1, brick 1 — arctan at a general REAL argument** (`Analysis/RArctan.lean`). The forced-first
  prerequisite of the `Γ(s/2) → ξ → Hadamard` stack that discharges the `bl` seam: complex `Clog` on
  the right half-plane needs `arg(z) = arctan(Im z / Re z)` at a general real ratio, and the repo had
  only rational-argument `Rarctan` (truncation-only). `RarctanR t ρ` lifts arctan to a real argument
  (`|t| ≤ ρ < 1`), mirroring the real-argument `Rartanh`: since `arctanTerm t n = (−1)ⁿ·artTerm t n`,
  the sign vanishes under `Qabs`, so `arctanTerm_diff_bound`, `arctanSum_Lip_le`, and the diagonal
  `RarctanR_diag_le` reuse the shared sign-independent machinery (`Rartanh_R`, `geoEvenSum`,
  `geoEven_bound`, `artanh_reindex`, `qpow_geom_bound`, `arctanSum_trunc`). RH-independent
  interface-shrinking toward discharging `bl`; the crux fields stay `none`.
- **Burnol's correction — the sharpest UNCONDITIONAL Weil-positivity mechanism** (`Square/SonineProjection.lean`).
  A deep-research survey (101 agents, 3-vote adversarial verification) identified the sharpest
  unconditional (NOT RH-equivalent) Weil-positivity theorem: Burnol's support-restricted positivity
  (arXiv math/0101068). Since `α(τ) → +∞` at `±∞` the negative band is bounded, so `∃Aε>0` with
  `Aε·cos(ετ) + α(τ) ≥ 0 ∀τ`, and `cos(ετ)` integrates to zero on the window `[1/c,c]` —
  positivity recovered on the window, unconditionally. Discretized here: `multForm_psd_via_correction`
  (a correction making the multiplier pointwise `≥0` and vanishing on the support of the test family
  ⟹ the pairing is `≥0`, unconditional), and the Burnol instance `burnolCorr` /
  `burnol_corrected_nonneg` (the `α(2)<0` band lifted to `α(2)+(−α(2))=0`, the corrected multiplier
  pointwise nonneg) / `burnol_pairing_psd_via_correction` (window positivity via the correction).
  The unconditional ceiling is the single archimedean place; full positivity (the multi-place /
  `f↔f̂` coupling) is RH and stays open. (Verified context: Connes–Consani Selecta 2021 single-place
  bound `W∞ ≥ Tr(ϑ(g)Sϑ(g)*) − c|ĝ(0)|²`, `c=4γ/log2`; the precise gap is the Beurling
  inner-function condition — the ratio-of-local-factors multipliers are not inner.)
- **The Sonine projection — Weil positivity recovered on the band complement**
  (`Square/SonineProjection.lean`). The crux frontier, formalized. With the natural finite routes
  foreclosed (component isolation RH-equivalent; pointwise single-place positivity refuted; free SOS
  for `2λₙ` = RH), what is left standing is a PROJECTION: positivity of the *whole* Weil pairing
  recovered on the Sonine complement (Connes–Consani / Burnol). Extrapolated from the proven
  α-indefiniteness and the Atlas signature geometry: `multForm α` is the discrete Weil multiplier form
  `Σ_τ α(τ)|g(τ)|²` diagonalized; `weilQuad_multForm` collapses it to `Σ_i c_i² α(i)` (via `RsumN_sift`);
  `multForm_psd_iff` — the whole form is PSD ⟺ the multiplier has no negative band; and the load-bearing
  **`multForm_psd_on_complement`** — UNCONDITIONALLY, if the test family vanishes on the negative band,
  the pairing is `≥ 0` (positivity recovered on the Sonine complement, a theorem, no RH). The Burnol
  instance (`burnol_pairing_indefinite` / `burnol_pairing_psd_on_sonine` / `burnol_sonine_dichotomy`):
  the bare pairing is indefinite (the `α(2)<0` band is real), but projecting off the band (`c(1)=0`)
  recovers positivity via `α(0)>0`. What is unconditional (band-complement positivity) vs what is RH
  (extending it to the whole space via the genuine Sonine `f↔f̂` coupling) is now explicit. Crux `none`.
- **The Burnol multiplier is indefinite — pointwise single-place positivity REFUTED**
  (`Analysis/BurnolAlphaTwo.lean`). `α(0) > 0` (`burnolAlphaZero_pos`, window center) and `α(2) < 0`
  (`burnolAlphaTwo_neg`, off-center) were both proven; this packages the frontier statement they
  jointly establish. `burnol_multiplier_indefinite` — the bare archimedean multiplier takes both
  signs; `burnolAlphaSample` + `burnolAlpha_not_pointwise_nonneg` / `burnolAlpha_not_pointwise_nonpos`
  — on its computed samples it is neither everywhere `≥ 0` nor everywhere `≤ 0`, so pointwise
  single-place positivity is refuted (both directions). The Connes–Consani / Burnol Sonine-space
  projection (positivity after projecting onto the prime-free window), NOT a pointwise `α ≥ 0`, is the
  genuine Track-2 resolution; the obstruction (Burnol "a further idea seems necessary") is now a named
  theorem. Crux fields stay `none`.
- **The prime-free window is maximal** (`Square/Pairing.lean`) — `prime_window_maximal`: the conquered
  prime-free window is at `X = 1`; the prime `2` enters at the next term (`Λ(2) = log 2`), the discrete
  Connes–Consani interval `(1/2, 2)`.
- **The atlas spectral signature** (`Square/AtlasSpectrum.lean`) — `atlasM_signature`: signature
  `(10,14)`; `atlasM_not_hodge_signature`: ten positive directions ≠ the Hodge form's one, so the
  spectral operator is structurally distinct from the crux's intersection form.
- **Literature reconnaissance — the frontier, sourced (2020–2026 survey, adversarially verified).** A
  deep multi-source survey (102 agents, 3-vote verification per claim) confirms the program's honest
  frontier with citations: **every** Li/Keiper-coefficient positivity statement is *exactly equivalent
  to RH* — Li's criterion `RH ⟺ λₙ ≥ 0` (Bombieri–Lagarias 1999; Lagarias, *Ann. Inst. Fourier* 57,
  2007; Selberg class, Mazhouda 2015; model-space/de Branges reformulation, Suzuki 2023, arXiv
  2301.05779) — so there is **no known unconditional bridge** to global positivity. The off-line ⟹
  `λₙ < 0` step is *asymptotic*, via steepest descents/Darboux on a superzeta integral (Voros, arXiv
  1403.4558 / 2204.01036 / math/0404213), with the violation regime astronomically far out (`n ≳ T²/t
  ≈ 10²⁵` given RH verified to `T₀ ≈ 2.4·10¹²`) — confirming the `LiBridge.dichotomy` grounding. The
  ONLY unconditional positivity is the **single archimedean-place** Weil positivity (Connes–Consani,
  *Selecta* 2021, arXiv 2006.13771) — the prime-free Sonine window, which this repo formalizes as
  `prime_window_maximal` / `archimedean_center_positive`; its semi-local generalization *implies* RH
  (no unconditional route), CC noting an obstruction (non-monotonic Riemann–Siegel angle). Net: the
  crux's open content is genuinely-new mathematics, and the unconditional boundary is exactly the
  single-place window already implemented here. Crux fields stay `none`.
- **The Riemann–Siegel angle obstruction, formalized** (`Analysis/RiemannSiegel.lean`) — the survey's
  named barrier to the single-place → semi-local extension, made an axiom-clean theorem. The
  Riemann–Siegel angle `θ(t) = arg Γ(1/4 + i t/2) − (t/2)·log π` (the phase of the completed-ζ
  functional equation) has center slope `θ′(0) = ½·(ψ(1/4) − log π)`, and `rsCenterSlope_neg :
  Pos (Rneg rsCenterSlope)` proves it strictly negative — `ψ(1/4) < log π`, so `θ` *decreases* through
  the symmetry point `t = 0`. This non-monotonicity is exactly the obstruction Connes–Consani note to
  a monotonicity-based propagation of the single-archimedean-place positivity across further places.
  The proof uses `psiQuarter_upper` (`ψ(1/4) ≤ −3`, the value bounded *above* — the opposite direction
  to the α(0) certificate, whose `psiQuarter_lower` bounds it below) and `Rnonneg_Rlogπc` (`log π ≥ 0`,
  via `Rnonneg_Rartanh_of_nonneg` on the repo's canonical `Rlogπc = 2·artanh((π−1)/(π+1))`, the same
  `log π` of α(0)/λ₁/λ₂). The **obstruction formalized faithfully — not a route through it**.
- **The archimedean kernel `Re ψ(1/4 + iτ/2)` ASSEMBLED, and the angle is non-monotone two-sidedly**
  (`Analysis/PsiLine.lean`) — a large construction. `DigammaWindow.lean` had built the `τ`-parameterized
  kernel *term* and its monotonicity but not the assembled kernel; this builds it at the frontier point
  `τ = 10` (`s = τ²/4 = 25`), the first value of `Re ψ` along the critical line off the center `ψ(1/4)`.
  The window term splits exactly as `windowTerm n 25 = windowTerm n 0 + cₙ`,
  `cₙ = 1600/[(4n+1)((4n+1)²+400)] ≥ 0` (`corrT_eq_windowTerm_gain`, the faithfulness bridge to
  `DigammaWindow`), so `Re ψ(1/4 + 5i) = ψ(1/4) + Σ cₙ`. `corrCore` is `Σ cₙ` as a **genuine
  constructive real** — a manifestly positive convergent series, with regularity proved *from scratch*
  via the telescoping `cₙ ≤ tel(n) − tel(n+1)`, `tel(n) = 100/(4n+1)`, holding for all `n` through the
  manifest square `(4n−1)² + 380 ≥ 0` (depth schedule `j ↦ 25(j+1)`). `psiLineRe5 := ψ(1/4) + corrCore`,
  with lower bracket `psiLineRe5_lower : Re ψ(1/4 + 5i) ≥ 1.28` (true value `≈ 1.61`) from
  `psiQuarter_lower` and `corrCore_lower` (`Σ cₙ ≥ 5.6`, the certified 12-term partial sum). Consequence:
  `rsLineSlope10_pos : θ′(10) > 0` (`Re ψ(1/4+5i) > log π`, using `Rlogπc_le`), and the capstone
  `rsAngle_non_monotone : θ′(0) < 0 ∧ θ′(10) > 0` — for one `θ` (one `log π = Rlogπc`), the slope changes
  sign, so the Riemann–Siegel angle is **non-monotone, two-sided**: the bounded-negative-band structure
  Burnol / Connes–Consani must work around. The obstruction completed as a theorem; it sharpens the
  barrier, it does not cross it. Crux fields stay `none`.
- **The kernel parameterized, and the monotone climb (θ convex on the window)** (`Analysis/PsiLine.lean`)
  — `corrCoreP sn sd` / `psiLineReP sn sd` assemble `Re ψ(1/4 + iτ/2) = ψ(1/4) + Σ cₙ(s)` for *every*
  rational `s = τ²/4 = sn/sd ∈ [0, 25]`, not just `s = 25`. The key reductions are exact: `cₙ` is
  monotone in `s` with `cₙ(s) ≤ cₙ(25) ⟺ sn ≤ 25·sd` (each divides out `(4n+1)³`), so the `s = 25`
  telescoping dominates every `s ≤ 25` uniformly — the *same* depth schedule `j ↦ 25(j+1)` gives
  regularity for all of them, and the climb is then a termwise comparison. `psiLineReP_mono`:
  `s ≤ s' ⟹ Re ψ(1/4 + i√s) ≤ Re ψ(1/4 + i√s')` — `Re ψ(1/4 + iτ/2)` is **monotone increasing in `τ`**,
  the analytic heart `DigammaWindow` recorded, now a theorem about the *assembled* kernel. Combined with
  `rsAngle_non_monotone`, the slope `θ′ = ½(Re ψ − log π)` is monotone increasing from `θ′(0) < 0` to
  `θ′(10) > 0` — so `θ` is **convex on the window with a unique minimum**, and the negative-`α` band is a
  single bounded interval. The obstruction's exact shape, made a theorem; crux fields stay `none`.
- **`θ′ > 0` on the whole upper band** (`Analysis/PsiLine.lean`) — `rsAngle_increasing_on_band`: for
  *every* rational `s = τ²/4 ∈ [16, 25]`, `θ′ > 0` (`Re ψ(1/4 + i√s) > log π`). The monotone climb
  carries a single sharper positive point — `rsLineSlope16_pos : θ′(8) > 0` (`Re ψ(1/4 + 4i) ≥ 1.18`
  from `ψ(1/4) ≥ −4.32` and the certified `Σ cₙ(16) ≥ 5.5`) — to the entire interval `s ≥ 16`. So the
  Riemann–Siegel angle's unique minimum sits at `τ < 8`, and beyond it `θ` rises monotonically: a genuine
  interval of positivity, not a single point. (`corrCoreP_ge_partial` generalizes the partial-sum lower
  bracket to any cutoff `N ≤ 25`.) Crux fields stay `none`.
- **The kernel reduces to `ψ(1/4)` at the center** (`Analysis/PsiLine.lean`) — `psiLineReP_zero`:
  `Re ψ(1/4 + i·0) = ψ(1/4)`, the assembled-level analog of `DigammaWindow.windowTerm_zero` (`corrCoreP_zero`:
  `Σ cₙ(0) = 0`, every `s=0` correction term vanishes). With `psiLineRe5 = psiLineReP 25 1` at the far end,
  the parameterized assembled kernel is now verified-correct at **both endpoints** of the window — a
  faithfulness anchor closing the construction. Crux fields stay `none`.
- **`α(2) < 0` — Burnol's archimedean multiplier is pointwise INDEFINITE** (`Analysis/BurnolAlphaTwo.lean`,
  with a new lower-bound substrate). The bare multiplier `α(τ) = 8√2·cos(τ·log2)/(1+4τ²) + h₊(τ)`,
  `h₊(τ) = Re ψ(1/4+iτ/2) − log π`, is shown **negative at `τ = 2`** (`burnolAlphaTwo_neg :
  Pos (Rneg burnolAlphaTwo)`) — the honest kernel analog of Burnol's "a further idea seems necessary":
  single-place positivity does *not* extend across the band, which is exactly why the Sonine projection
  is needed. We prove the **obstruction**, never a (false) `α ≥ 0`. The pieces, all axiom-clean
  (`{propext, Quot.sound}`), each its own bracket added to the substrate:
  - `Rpi_lower_three : π ≥ 3` (`Analysis/Pi.lean`) — sharp `π` *lower* bound via depth-parameterized
    arctan brackets (`arctanSum_diag_ge_at`/`_le_at`, tail `ρ^(2a+3)`); the repo had only `π ≤ …`.
  - `Rlogpi_ge_one : log π ≥ 1` (`Analysis/LogPiLower.lean`) — `log π = 2·artanh((π−1)/(π+1)) ≥ 2·½`,
    resting on `π ≥ 3`; the first positive *lower* bound on a log in the substrate (companion to
    `Rlogπc_le`).
  - `psiQuarter_upper_tight : ψ(1/4) ≤ −4` (`Analysis/PsiQuarter.lean`) — the sharp upper bracket
    (a two-branch `n<6` / `n≥6` Int case split on the digamma series).
  - `corrCoreP_one_upper : Σ cₙ(1) ≤ 4.22`, `psiLineReP_one_upper : Re ψ(1/4+i) ≤ 0.22`,
    `archKernel_at_two_below_logpi : Pos (Rsub Rlogπc (psiLineReP 1 1 …))` — i.e. `h₊(2) < 0`
    (`Analysis/PsiLine.lean`), from `Re ψ(1/4+i) = ψ(1/4) + Σcₙ(1) ≤ −4 + 4.22 = 0.22` and `log π ≥ 1`.
  - `sqrt2_mul_self : √2·√2 = 2` and `sqrt2_le_three_halves : √2 ≤ 3/2` (`Analysis/BurnolAlphaTwo.lean`)
    — the **exp∘log inverse** (`RrpowPos_add` + `Rexp_RlogNat`), no `sqrt` primitive.
  Assembled: with `|cos| ≤ 1`, `8√2 ≤ 12` and `1/(1+16) = 1/17` bound the oscillating term by `12/17`,
  so `α(2) ≤ 12/17 + (0.22 − 1) = 12/17 − 78/100 = 126/1700` negated, i.e. `−α(2) ≥ 1/100 > 0`. The
  obstruction to extending single-place positivity, mechanized at a point. Crux fields stay `none`.
- **Erratum** — corrected the stale `λ₃ ≈ 0.0173` / `λ₃^∞ ≈ −1.20` (a computational error) to the
  standard Li value `λ₃ ≈ 0.2076` / `λ₃^∞ ≈ −1.013` across `LambdaThree.lean`, `CruxFrontierN3.lean`,
  `Attempt.lean`, `ROADMAP.md`, and the v0.20.0 changelog entry; recorded the precision analysis (the
  binding constraint is `γ₁`, not `γ`; six constants need ~0.1–0.3% relative precision).

## [0.21.0] - 2026-06-16

Stage G — the arithmetic Hodge-index crux via the missing-object embedding, and the UOR Atlas
formalized. **Outcome: LOCALIZED** — the route is built end to end and the Atlas is formalized to
its frontier, but the crux did not close; `hodgeIndexHolds` / `liPositivityHolds` stay `none`,
RH OPEN. Every commit green, axiom-clean `{propext, Quot.sound}`, no `sorry`/`native_decide`.

### Added — the embedding route
- `Square/WeilPSD.lean` — the finite-truncation PSD predicate `WeilPSD`; `WeilPSD_rankOne` (a
  rank-one Gram is the manifest square); `WeilPSD_gramOf` (Gate B free for any embedding into ℝ^D);
  the embedding bridge `embeds_to_hodgeNeg` / `realizesDiag_genuine_iff`.
- `Square/FrobForm.lean` — the full primitive form `FullForm` on the Frobenius carrier; the
  diagonal forced to `−2λₙ`; `negPSD_to_hodgeNeg`; a non-trivial shift-length off-diagonal.
- `Square/AtlasRule.lean` — the zero-free `AtlasRule`; `atlasRule_growth_filter`; **`cayley_relocation`**
  (the §6 recorded negative result: a zero-built candidate's match ⟺ RH).
- `Square/KillTest.lean` — the decidable finite-Gram kill-test (throwaway pre-filter).
- `Square/GateA.lean` — the λ-free pairing `atlasPair`; `gateA_is_liNonneg` (Gate A under free
  Gate B is RH); two-sided no-smuggling guards (`gateA_satisfiable`, `gateA_can_fail`).
- `Square/E8Seed.lean` — the E₈ Gram as an embedding Gram (PSD free), verified `= 4×` the standard
  E₈ Cartan matrix (`e8_is_cartan`), strictly positive diagonal.
- `Square/GaugeTower.lean` — the gauge tower carrying a metric; `not_WeilPSD_of_neg_diag` and the
  make-or-break obstruction `limit_indefinite_of_neg_signature`.
- `Square/StageG.lean` — `stageG_frontier_located` (the adjudication); the **conditional closure**
  `strictRealizes_closes_crux` / `strictRealizes_is_liCrux`.
- `Square/GateSanity.lean` — `crux_gate_faithful`: the crux gate discriminates and **closes on a
  genuine witness** (it does not arbitrarily fail).

### Added — the UOR Atlas (from the `uor-atlas.md` formalization document)
- `Square/AtlasSpectrum.lean` — the spectral operator `M = (O+2)I − T·Π_T − O·Π_O` (§5/§6.6),
  sourcing `Σ = {10,2,7,−1}`; verified multiplicities `{1,2,7,14}` and trace `24`; `atlasM_indefinite`;
  the Hurwitz norm `atlasNorm_psd` (a different, definite object — §9).
- `Square/AtlasCharacteristics.lean` — the convergence tower (§1), the Euler–Lefschetz
  self-intersection `χ(Sᵏ)=1+(−1)ᵏ` vanishing at the process levels (§11), the spectral balance
  (§5), and the §10 connections (`dim G₂ = 14`, `24 = dim E₈^T`, `θ_{E₈}=E₄`).
- `Square/AtlasAddressing.lean` — the addressing inverse system (§5), parametric generation (§8),
  and the prime skeleton = explicit-formula prime side `Λ(p)=log p` (§10/§12).
- `Square/AtlasClasses.lean` — the class structure (§2) and the transforms `σ,τ,μ` as finite-order
  class permutations (§3).
- `Square/AtlasConservation.lean` — no-loss, round-trip identity, scale-invariance (§4/§5).

### Added — Atlas discovery program (exploration; following discoveries to their next threads)
- `Square/AtlasForcing.lean` — what makes a value NOT a coincidence: parametric identity
  (`multSum_eq_dim`: dimension `= T·O` for all `T,O`) or over-determination; the discovery
  `trace_eq_dim_at_T3` (trace = dimension forced by the extremal `T = 3`).
- `Square/AtlasRHConnection.lean` — `atlas_shift_eq_weight` (addressing prime ↔ Frobenius orbit ↔
  `Λ(p)=log p`); `atlas_feeds_rh` (three live points where the Atlas feeds the RH program).
- `Square/LefschetzCoupling.lean` — the crux refined to its Lefschetz shape: `H² > 0`
  (`eH_sq_pos`), `vanCyc` primitive (`vanCyc_perp_H`), and `genuine_crux_arch_coupling` (crux ⟺
  sign of the prime–archimedean coupling `arith(n)+arch(n)`, the `ff_hodge_iff_hasse` shape over ℤ).
- `Square/ArchimedeanPlace.lean` — the `arch(n)` facet: conquered at the head (`n=1,2`) and in the
  Connes–Consani window (`α(0) > 0`); open outside (the tail bound).
- `Square/AtlasModular.lean` — `θ_{E₈^T} = E₄³ = E₆² + 1728·Δ` through order `q⁵` by power-series
  convolution; `Δ = η²⁴`, the `24 = dim E₈^T` = the modular `24`.
- `Square/AtlasExceptional.lean` — the Freudenthal–Tits magic square (`R,C,H,O → F₄,E₆,E₇,E₈`); the
  `dim 𝔤 = rank·(h+1)` law; `dim G₂ = (T−1)(O−1) = 14`; `240 = dim E₈ − rank E₈`.
- `Square/AtlasCoxeter.lean` — the E₈ exponents are the totatives of the Coxeter number `30`;
  `rank E₈ = φ(30) = 8 = O`; the `30/8/120/240/248` forced web.
- `Square/AtlasSynthesis.lean` — `atlas_forced_web`: every Atlas constant a function of `{T,O}=(3,8)`,
  no coincidences; `atlas_web_and_open_crux`: the honest boundary (the web does not force RH).
- `Square/AtlasCruxSynthesis.lean` — `atlas_crux_localization`: the Atlas forces the prime side, the
  crux is the prime–archimedean coupling sign, conquered at head + window, no shortcut.
- `Square/CruxFrontierN3.lean` — the next coefficient pinned: the `n=3` coupling `> 0 ⟺ Pos Rlambda3`.
- `Square/UniformClosure.lean` — closure is ONE structural fact, not enumeration (§2 thesis):
  `enumeration_insufficient` + `uniform_fact_closes`.
- `Square/CoxeterCandidate.lean` — a §7 named uniform-rule candidate (Coxeter iteration, order 30)
  tested and KILLED by the growth pre-filter (periodic ⟹ bounded ⟹ cannot match `2λₙ ~ n log n`).
- `Square/SinglePrime.lean` — the Single Prime Hypothesis: the Atlas as one Prime object emanating
  all structure (`single_generator_emanates`); unity ⟹ uniform closure.
- `Square/AtlasGenerator.lean` — the shift-length uniform-rule candidate `atlasShiftDiag`; survives
  the growth filter (unbounded `n log n` class) where Coxeter died.
- `Square/AtlasCoherence.lean` — coherence (the conserved zero-state) is the closure condition, not
  a single facet (`atlas_coherent`, `coherent_closure_not_single_facet`).
- `Square/AtlasComposition.lean` — the composition-algebra norm (§6.3/§9/§10): the 2-, 4-, 8-square
  identities (`two/four/eight_square`, Hurwitz) — Degen's octonion identity verified by `ring_uor`.
- `Square/AtlasTopology.lean` — the Betti signature (§6.5) and Bott/Clifford periodicity (§10); the
  tower forced four ways.
- `Square/AtlasCalculus.lean` — the seven operators, the free-monoid `Term`, and the catamorphism
  with its universal property (§3/§4): form determines function (`op_count`, `cata_unique`).
- `Square/AtlasComplete.lean` — `atlas_complete`: the roll-up witnessing every facet (§1–§15)
  formalized, as facets of one `{T,O}` object, with the crux honestly open.

### Changed
- `scripts/honesty_audit.sh` — new **no-smuggling** check (the metric analog of `intrinsicH1_dict`):
  the Gate-A pairing must be λ-free.
- `F1Square.lean` — v0.21.0 notes on the crux fields; a witness binding the stage-G route, crux none.

## [0.20.0] - 2026-06-15

### Added — stage F: the UOR construction of the crux (`H¹`-object + FORCED dictionary) and the certified `γ₂ ≥ −0.02` bracket (pure Lean 4, no Mathlib, no `sorry`, choice-free)

The v0.18.0 bridge carried the dictionary `⟨Cₙ,Cₙ⟩ = −2λₙ` as INTERFACE DATA — a `SpectralSquare`
field that any instance supplied definitionally (`cSq := −2λ`, `dict := rfl`). Stage F removes
that assumption and **derives** the dictionary, mirroring `BridgeFF`'s dictionary column over ℤ: a
genuine rank-4 Néron–Severi-style lattice, the primitive projection with PROVEN orthogonality, and
the self-pairing computed from the Gram. **The gate then ran on the constructed object and LOCATED
THE FRONTIER** — the forced signature did *not* come out positive (proving `λₙ > 0 ∀n` *is* RH), so
the construction is complete down to one irreducible input (the genuine Stieltjes η-tail = the
zeros) and `hodgeIndexHolds`/`liPositivityHolds` stay `none` — the gate flips the instant a
faithful, axiom-clean proof of the criterion lands; until then **RH stays OPEN**. Stage F also
delivers the constructive second Stieltjes constant `γ₂` and **closes its numeric bracket
`γ₂ ≥ −0.02`** (`Rgamma2_ge_neg002`) — the documented open computational frontier from v0.18.0 — via
a discrete Euler–Maclaurin construction with a new Real "ring engine" (`RAddNF`+`RMulNF`); this is a
certified constant bound (evidence), NOT a positivity-of-all-`λₙ` (= RH) claim. Every theorem is
choice-free (`{propext, Quot.sound}`), audited; the build is warning-free; the gate passes.

- **A1 — the `H¹` carrier by universal property** (`F1Square/Square/Cohomology.lean`): a
  `FrobSys` is a carrier with a scaling/Frobenius action `φ` and a fundamental class `g`; the
  canonical `H¹` is `H1 = (ℕ, succ, 0)`, the **free / initial Frobenius system on one generator**
  — a morphism out of it is FORCED (`H1_universal`, `H1_isFree`, `freeFrob_unique_upto_iso`),
  exactly as the coproduct forced `𝕊` (v0.17.0). The Frobenius orbit **realizes the built
  prime-power pencil** as ONE equivariant identification (`orbit_realizes_pencil` — the orbit
  position's log-separation from the diagonal equals the built `pencil_separation_pow`;
  `orbitShift_succ` — each Frobenius step adds `log p = Λ(pᵏ)`, the Connes–Consani closed orbit).
  Honest scope: this builds the ABSTRACT carrier of the action, NOT the genuine spectral `H¹`
  (whose spectrum is the zeros) — that is the open frontier.
- **A2 — the intrinsic lattice and the trace datum** (`F1Square/Square/WeilLattice.lean`): `hPair`
  is the symmetric bilinear form on the rank-4 lattice `{F_h, F_v, Δ, Γ}` with the sourced/derived
  ruling intersections and the spectral data `Δ², Γ², Δ·Γ` as parameters. The vanishing cycle
  `Cₙ = Δ − Γₙ` is **proven GENUINELY PRIMITIVE** — orthogonal to both rulings for every spectral
  datum (`vanCyc_perp_Fh`, `vanCyc_perp_Fv`, the `BridgeFF.primDG_perp` analog) — not hand-picked.
  On `𝕊`'s coarse lattice the spectral data is `Δ²=Γ²=Δ·Γ=0` (pencil-blind, `vanCyc_blind`); the
  `H¹` enrichment lifts `Δ·Γₙ` to the explicit-formula value `λₙ`.
- **A3 — THE FORCED DICTIONARY**: the vanishing-cycle self-pairing is `Δ²−2(Δ·Γ)+Γ² = dd+gg−2dg`
  (`vanCyc_selfpair_gen`, the `BridgeFF.primDG_sq` analog), the `−2` being the lattice's own cross
  term. The geometric inputs `Δ²=Γ²=0` are **TIED to the v0.17.0 derived lattice**
  (`vanCyc_selfpair_built`, from `pair_diag_self_derived`/`pair_graph_self_derived`), not plugged.
  `IntrinsicH1` is **assumption-free by construction** — its only datum is `lam`; `cSq` is FORCED
  to the pairing diagonal, so no false dictionary CAN be inhabited; `intrinsicH1_dict` is a
  theorem. `genuineSpectralSquare` routes through it, so `⟨Cₙ,Cₙ⟩ = −2λₙ` is now DERIVED
  (`genuineSpectralSquare_dict`), not a field — the v0.18.0 interface converted to construction.
- **B — the forced signature and the located frontier** (`F1Square/Square/Forced.lean`):
  `genuine_vanCyc_normal` (`−⟨Cₙ,Cₙ⟩ = 2λₙ`, the completed-square normal form);
  `genuine_crux_equivalent` (the geometric crux on the constructed object ⟺ `LiCrux genuineLamSeq`
  = RH, now on an object whose dictionary is a theorem); `genuine_evidence_head` (`⟨C₁,C₁⟩ < 0`,
  `⟨C₂,C₂⟩ < 0` on the DERIVED object). **`genuine_crux_frontier_located` pins the FRONTIER** as
  one proposition: the forced criterion is exactly `∀n, Pos (genuineLamSeq n)`, the head `λ₁,λ₂`
  is discharged, no finite run reaches it (`genuine_iff_all_upTo`), and it is satisfiable
  (`genuine_signature_satisfiable`, no hidden impossibility) — the remaining input is the genuine
  Stieltjes η-tail (the zeros; the truncated `etaTwoSlice` is not it), and the gate flips the
  instant a faithful proof of the criterion lands. **Which
  `BridgeFF` column is done, which is open**: the DICTIONARY column (`primDG_sq`) is now a genuine
  theorem; the SIGNATURE-FORCING column (`ff_hodge_iff_hasse`, where the function field's `4q−a²`
  completed square forces the bound) has no unconditional analog over ℤ — the forced criterion is
  RH.
- **The roll-up** (`F1Square.lean`): the stage-F backing block and elaboration-checked witness
  (the carrier's universal property, the proven primitivity, the built-tied dictionary, the forced
  criterion, the located frontier); the crux fields stay `none`. The dictionary is a theorem;
  the construction is complete down to its one honest input (the η-tail / the zeros); the
  positivity does not close from anything built. **RH stays OPEN.**
- **The Voros growth dichotomy, mechanized** (`F1Square/Analysis/Voros.lean`) — a frontier brick.
  Voros (*Math. Phys. Anal. Geom.* 9 (2006)) is the sharpest statement of the RH-hardness of Li
  positivity: `λₙ` has exactly two mutually-exclusive asymptotic forms — tempered `∼ (n/2)log n`
  (RH) vs exponentially oscillating `∼ Σ((τₖ+i/2)/(τₖ−i/2))ⁿ` (¬RH), no third option. The genuine
  CONSTRUCTIVE skeleton is built unconditionally: `tempered_not_exp`/`exp_not_tempered` — a
  polynomially-bounded sequence (`|λₙ| ≤ C(n+1)²`) can NEVER exceed `2ⁿ` infinitely often (the
  regimes are disjoint), via `cube_le_pow2` (`(n+1)³ ≤ 2ⁿ`, `n ≥ 11`) → `quad_lt_pow2`. The
  RH-equivalent *identification* of a regime (the saddle-point content) stays faithful interface.
  Deep-research-confirmed (104 agents) against the primary Voros/Coffey/Lagarias/Yoshida sources,
  which pin the genuine unconditional levers (Coffey's `λₙ ≥ trend − |S2|`, math-ph/0505052;
  Yoshida–Bombieri small-support Weil positivity) — all bottoming out at the same `|S2|`/RH-hard
  step, so no unconditional closure exists.
- **The second Stieltjes constant `γ₂ ≈ −0.00969` as a genuine constructive real**
  (`F1Square/Analysis/GammaTwo.lean`) — `Rgamma2 := Rlim g2SeqDyadic`, the `H¹`-object ingredient
  feeding `λ₃`. The defining sequence `g₂(N) = Σ_{k≤N}(ln k)²/k − ⅓(ln N)³` telescopes to `Σ eₖ`,
  `eₖ = (ln k)²/k − ⅓((ln k)³−(ln(k−1))³)`; the cubic-difference algebra (`cube_diff_identity`,
  `tri_sum_3a2` — discharged by the new UOR **`RAddNF`** signed-atom normalizer, the κ-form solution
  to the absent Real ring/abel tactic) yields the two-sided per-step envelopes
  `−ln(p+1)²/(p(p+1)) ≤ eₖ ≤ ln(p+1)/p²`. These are summed over dyadic blocks (log/log² caps
  `logN(j+2) ≤ a+2`) and telescoped with the discrete antiderivatives `T_U(m)=(4m+12)/2^m` and the
  QUADRATIC `T_L(m)=(2m²+12m+22)/2^m` — the new ingredient over `γ₁`, whose outer sum was linear.
  Reindex `M(j)=2j+8` with domination `(j+1)(2M²+12M+22) ≤ 2^M` (via `8j²+88j+246 ≤ 2^{j+8}`) gives
  pairwise Cauchy `±1/(j+1)` → `RReg_of_real_bound` → `Rlim`. Choice-free (`{propext, Quot.sound}`),
  audited. Mirrors the `GammaOne`/`γ₁` regularity endgame column-for-column.
- **THE CERTIFIED BRACKET `γ₂ ≥ −0.02` via DISCRETE Euler–Maclaurin** (`Rgamma2_ge_neg002`,
  `F1Square/Analysis/GammaTwoBracket.lean`) — **complete**. The corrected route needs NO constructive
  integration: the trapezoidal anchor `½f(N)` (`f(x)=ln²x/x`) captures the leading `½ln²N/N` tail,
  leaving `hSeq(N)=g₂(N)−½f(N) → γ₂` whose per-step increment is the trapezoidal residual `s_p =
  ½[ln²(p+1)/(p+1)+ln²p/p] − ⅓[ln³(p+1)−ln³p] = O(ln²p/p³)` (`hSeq`, `sStep`, `hSeq_step_eq`). The
  chain, end to end:
  - **The keystone decomposition** `sStep p ≈ b²·C2 + b·R1 + R0` (`sStep_decomp`) — `C2 = ½(1/p+1/(p+1))
    − d` the trapezoidal error of `1/x`, `R1 = d·u1 − d²`, `R0 = ½d²u1 − ⅓d³` (`b=ln p`, `d=ln(p+1)−ln
    p`). A free polynomial identity in 4 atoms, proved by reducing both sides to the SAME 7 canonical
    monomials with the `RAddNF`+`RMulNF` ring engine (`sq_binom2`, `inner_merge`, `partA_eq`/`partC_eq`,
    the `½·2=1`/`⅓·3=1` collapses) matched by an explicit choice-free 7-element permutation.
  - **`C2 ≥ 0` (trapezoid ≥ integral)** dissolved by a clean coincidence — `dPlusQ(0,p) = M = ½(1/p+1/(p+1))`
    EXACTLY (`dPlusQ_zero_eq_mid`, a `ring_uor` identity: the trapezoidal midpoint *is* the `T=0` artanh
    upper bound), so `δ ≤ M` with no series comparison (`C2_nonneg`).
  - **Per-step lower bound** `s_{j+1} ≥ −1/((j+1)(j+2))` (`sStep_lower_tele`) — all coefficient pieces
    bounded by rationals (`d ≤ 1/p`, `d − u1 ≤ M − u1 = 1/(2p(p+1))`, `ln p ≤ p`), then `cube_dom_nat`
    collapses the two terms to one TELESCOPING term (no dyadic machinery needed for the tail).
  - **Telescoping tail** `hSeq(N+k) ≥ hSeq(N) − (1/(N+1) − 1/(N+k+1))` (`hSeq_tele`, induction) ⟹
    `hSeq(M) ≥ hSeq(199) − 1/200` for all `M` (`hSeq_lower_const`).
  - **The limit** `γ₂ ≥ hSeq(199) − 1/200` (`Rgamma2_ge_hSeq`) — each `g2SeqDyadic k = g2Seq(2^{2k+8}) ≥
    hSeq(2^{2k+8}) ≥ hSeq(199) − 1/200`, so the limit `γ₂ = Rlim g2SeqDyadic` is too (one-sided
    Archimedean via the `RTendsTo` rate); mirrors `γ₁`'s `Rgamma1_le_gSeq`.
  - **The numeric heart** — `hSeq(199) ≥ ofQ(gBound2 3 10⁸ 199)` (`hSeq_ge_gBound2`, from
    `lnSqSumLo_le`/`logCube_le`/`halfSqOver_le`) and `gBound2 3 10⁸ 199 − 1/200 ≥ −1/50`
    (`gamma2_decide`, one big-integer kernel `decide`, ≈3s, depth `T=3`, denominator `D=10⁸`). The
    lower bound is wrapped as a `def` (`gBound2`) so the deep evaluator term stays opaque in the flat
    final proof — the `γ₁`/`gBound` pattern. Choice-free (`{propext, Quot.sound}`), audited.
- **The third Li coefficient `λ₃` in closed form** (`F1Square/Analysis/LambdaThree.lean`) — the next
  rung of the genuine λ-ladder, the first to carry `γ₂` (`Rgamma2`). The genuine `λₙ = λₙ^{arith} +
  λₙ^{∞}` is already general; this adds the next η-anchor (deep-research-confirmed
  Bombieri–Lagarias / Keiper–Li): **`η₂ = −γ³ − 3γγ₁ − (3/2)γ₂`** (`Reta2`, the first anchor needing
  `γ₂`), the `StieltjesEta3` structure extending `StieltjesEta` with it, and `λ₃^{arith} = −(3η₀ +
  3η₁ + η₂)` (`Rlambda3_arith`). The archimedean side `λ₃^{∞} = genuineArchSeq 3` (already general,
  via `ζ(2), ζ(3)`) needs no new work, so `Rlambda3 = λ₃^{arith} + λ₃^{∞}` is a closed-form
  constructive real. For ANY η-data anchored through `η₂` the genuine ladder meets it at `n = 3`
  (`genuineArith_three`, `genuineLam_three`) exactly as at `n = 1, 2` — the closed form is faithful,
  not ad hoc. `Pos λ₃` is NOT claimed: the `γ₂` bracket that gates the `η₂` term is now closed
  (`γ₂ ≥ −0.02`, above), but `λ₃ ≈ 0.2076` (`λ₃^{arith} ≈ +1.22`, `λ₃^{∞} ≈ −1.013`; margin ≈ 0.21) is
  a heavily-cancelled combination of `Θ(1)` terms, so a positivity certificate needs all of
  `γ, γ₁, γ₂, ζ(2), ζ(3), log 4π` to ~0.1–0.3% relative precision (the binding constraint is `γ₁`) —
  the full `λ₃`-formula numeric assembly, the remaining open work. Choice-free, audited. The crux
  fields stay `none`. (Erratum: earlier drafts of this entry stated `λ₃ ≈ 0.0173` / `λ₃^{∞} ≈ −1.20`,
  a computational error; the correct standard Li value is `0.2076`.)
- **The Li-term modulus growth law** (`F1Square/Analysis/LiGrowth.lean`) — ties Lever 1 to the Voros
  dichotomy, and is the first end-to-end use of the `RAddNF`+`RMulNF` "ring" engine. `cnormSq_mul`
  proves the Brahmagupta–Fibonacci multiplicativity `|zw|² = |z|²·|w|²` constructively: expand both
  squared parts into degree-4 monomials, the cross terms `±abcd` cancel (`cancelC`, one pair after
  `regroupX`/`add4_perm1`), the four surviving squares match `(a²+b²)(c²+d²)` (`prod_sq_reassoc` +
  `add4_perm2`). Hence the power law `|zⁿ|² = (|z|²)ⁿ` (`cnormSq_npow`) and **the growth seed**
  (`liTerm_dominates`): a zero LEFT of the critical line (`Re ρ < ½`) makes its Li numerator `(ρ−1)ⁿ`
  dominate `ρⁿ` in modulus for EVERY `n` — `(cnormSq ρ)ⁿ ≤ (csubOneNormSq ρ)ⁿ` — so
  `|(1−1/ρ)ⁿ| ≥ 1` grows geometrically, the constructive heart of the exponential (¬RH) regime. The
  SUM aggregation (Voros's saddle-point) and WHERE the zeros sit stay [CLASSICAL] interface; crux
  fields stay `none`. Choice-free, audited.
- **Lever 1 — the Li/zero growth geometry** (`F1Square/Analysis/ZeroGeometry.lean`): the constructive
  bridge from a zero's POSITION to the GROWTH of its Li contribution, feeding the Voros dichotomy and
  the de la Vallée-Poussin zero-free region. Each Riemann zero `ρ` contributes `1 − (1−1/ρ)ⁿ` to
  `λₙ`, whose growth is governed by the squared ratio `|1−1/ρ|² = |ρ−1|²/|ρ|²`. The genuine
  constructive nugget, proved unconditionally and without `sqrt` (`liRatio_diff_eq`):
  **`|ρ−1|² − |ρ|² = 1 − 2·Re ρ`** — the `Im ρ` terms cancel exactly, so the regime is fixed by which
  side of the critical line the zero lies on: `Re ρ = ½` ⟹ ratio `1` (bounded, Voros's tempered/RH
  seed, `liRatio_on_line`); `Re ρ < ½` ⟹ ratio `> 1` (an exponentially growing Li term, the ¬RH seed,
  `liRatio_left_of_line`); `Re ρ > ½` ⟹ ratio `< 1` (`liRatio_right_of_line`). The dVP band
  (`DVPBand δ`) does NOT collapse to the line — `dvp_band_admits_off_line` exhibits a band-resident
  off-line zero (ratio `> 1` AND band membership coexisting), so `DVPBand δ` for `δ > 0` is strictly
  weaker than `AllZerosOnLine`; that residual gap (band ⟹ line) is RH itself. The additive
  rearrangements run through the genuine abelian-group laws (`Req_of_seq_Qeq` can't see through
  `Rmul`'s nor reshape `Radd`'s Bishop reindexing). WHERE the zeros sit, and that the SUM `λₙ`
  inherits a single term's growth (Voros's saddle-point), stay [CLASSICAL] interface; the crux fields
  stay `none`.
- **The UOR Real additive-group normalizer `RAddNF`** (`F1Square/Analysis/RAddNF.lean`) — the κ-form
  solution to the central mechanization blocker. `ring_uor` is Int/ℚ-only and the pointwise Real
  route clears denominators multiplicatively (any atom occurring 3+ times explodes), so additive
  Real identities had no tactic. `RsumL` canonicalizes a `Radd`/`Rneg`/`Rsub` tree to a list of
  signed-atom summands; equality is decided by the multiset (`RsumL_perm` permutation-invariance +
  `RsumL_cancel_anywhere` choice-free positional cancellation — no `List.Perm` `decide`, which pulls
  `Classical.choice`). The reusable abelian-group analogue of `ring_uor`; it drives the `γ₂` cubic
  telescoping and every `λₙ` assembly.
- **The UOR Real multiplicative normalizer `RMulNF`** (`F1Square/Analysis/RMulNF.lean`) — the κ-form
  companion of `RAddNF`, the second half of a `Real` "ring" engine. Real MULTIPLICATIVE identities had
  no tactic for the same reason additive ones didn't (`ring_uor` is ℤ/ℚ-only; the pointwise route
  can't see through `Rmul`'s Bishop reindexing). `RprodL` canonicalizes a `Rmul`-tree to the product
  of a factor LIST; equality is decided by the multiset (`RprodL_perm`, from the genuine `Rmul`
  commutativity/associativity). Permutation-only — `Real` has no universal multiplicative inverse, so
  there is no cancellation layer (all degree-`d` monomial normalization needs is permutation).
  `Rmul_pair_eq_RprodL4` is the degree-4 flatten; `prod_sq_reassoc` (`(ac)² ≈ a²c²`) and
  `prod_cross_reassoc` (`(ac)(bd) ≈ (ad)(bc)`) are the validated monomial atoms (the square and the
  cross-term of `|zw|² = |z|²|w|²`), with the permutations built EXPLICITLY via `List.Perm`
  constructors (`decide` on `List.Perm` pulls `Classical.choice`). With `RAddNF` this stands in for a
  `Real` `ring` tactic: expand to monomials, normalize each with `RprodL_perm`, match the sum with
  `RsumL_perm`. Choice-free, audited.
- **Honesty-gate rigor fix** (`scripts/honesty_audit.sh`) — load-bearing. Checks 3 (no
  `sorry`/`native_decide`) and 4 (choice-free) used `… | grep -q …` inside an `if`-condition
  under `set -o pipefail`: a matching `grep -q` exits early, SIGPIPEs the upstream `grep`, and
  pipefail makes the pipeline's status that non-zero code — which `if` reads as FALSE, so the
  FAIL branch never ran. **The forbidden-axiom and choice-free gates were effectively disabled.**
  Fixed (capture-then-test, no `grep -q`); verified the gate now FIRES on violations and PASSES
  clean. The fix exposed and removed a pre-existing `Classical.choice` leak (`graph_one_diag`,
  `omega` on an `↔`; reproved `Nat.one_mul`+`eq_comm`) — so the choice-free claim
  (`{propext, Quot.sound}` only) is now genuinely *enforced*, not merely asserted.

## [0.19.0] - 2026-06-13

### Added — stage E: completion — the explicit formula, the dominance face, the roll-up (pure Lean 4, no Mathlib, no `sorry`, choice-free)

The three stage-E release goals are delivered: **the explicit-formula trace is completed** (the zero
side realized at the Bombieri–Lagarias slices), **the remaining `Li` interfaces are retired** at the
built slices, and **the final F1-square roll-up** records the v1.0.0-candidate state — plus **THE
DOMINANCE FACE**: the crux as a single uniform bound, proven equivalent to both prior faces. The
crux did not close — now a *sourced* result, not a presumption — so `hodgeIndexHolds`/
`liPositivityHolds` stay `none` and **RH stays OPEN**. Every theorem is choice-free
(`{propext, Quot.sound}`), audited; the build is warning-free; the gate passes.

- **The completed explicit-formula trace** (`F1Square/Analysis/LiComplete.lean`) —
  `Li.ExplicitFormulaTrace`, until now inhabited only by the trivial split `z = z + 0`, is REALIZED
  with the genuine three-sided reading at both built slices (`explicitFormulaTrace_one_realized`,
  `explicitFormulaTrace_two_realized`): zero side `λ₁`/`λ₂` (the sum-over-zeros reading is
  [CLASSICAL], BL 1999 — the zeros are not constructed and nothing pretends they are), finite-place
  closed forms `γ` and `2γ − (γ² + 2γ₁)`, archimedean parts — all three reals built. Packaged as the
  **`WeilTrace` ladder** (`weilTraceTwo`, the trace identity at every positive index;
  `weilTraceTwo_evidence`). Convention notes pinned (deep-research-verified): the Lagarias⟷BL
  grouping (`λₙ = S∞(n) − S_f(n) + 1` vs `λₙ^{arith} = −S_f`, `λₙ^{∞} = S∞ + 1`, confirmed against
  both built slices to 30 digits); the arithmetic closed form sourced from the η-polynomial form
  (the arXiv print of Lagarias eq. (4.13) carries a sign typo — not used); unconditionally the
  finite-place part equals the zero sum truncated at height `√n` up to `O(√n·log n)` (Lagarias
  Thm 6.1) — the precise sense in which the prime side IS an incomplete zero side.
- **`Li.LiAgreesWith` retired at the built slices** (`liAgreesWith_two_realized`) — computed (the
  direct certified builds `Rlambda1` via the accelerated-γ assembly, `Rlambda2` via the
  Stieltjes/ζ(2) assembly) agrees with classical (the BL closed-form assemblies,
  `liClassicalSeqTwo`) — genuinely non-reflexive at `n = 1, 2`, the agreement being the content of
  `Rlambda1_decomposition`/`Rlambda2_decomposition`. A REALIZATION LEDGER in `Li.lean` records the
  boundary: every `Li` interface is realized exactly as far as the built slices reach, no further.
- **THE DOMINANCE FACE** (`F1Square/Square/Dominance.lean`) — the crux as ONE uniform bound:
  `Dominates B arith arch` (`−B(n) ≤ arith(n)` — the bound controls the oscillation's negative
  excursions — and `arch(n) − B(n) > 0` — it stays strictly below the archimedean trend),
  `Dominated` its single existential. Sign-agnostic in both parts: no case split between the
  small-`n` regime (archimedean part NEGATIVE: `λ₁^{∞} ≈ −0.5541`, `λ₂^{∞} ≈ −0.8745`, re-verified
  to 30 digits) and the asymptotic regime (roles swapped); the dichotomy is clean, no third option.
  **The theorems**: `dominated_liPositive` / `liPositive_dominated` / `dominated_iff_liPositive`
  (under the trace, "some single bound dominates" ⟺ `λₙ > 0 ∀n` — genuinely universal WITHOUT
  enumeration; the necessity witness is the tight bound `B(n) = arch(n) − λₙ`), and
  **`dominance_crux_equivalent`**: `Dominated ⟺ SpectralCrux ⟺ LiCrux` through the v0.18.0 bridge —
  **the crux now has THREE provably equivalent faces** (geometric `⟨Cₙ,Cₙ⟩ < 0 ∀n`, analytic
  `λₙ > 0 ∀n`, dominance `∃ one bound under which oscillation loses`); `weilTrace_dominance` reads
  the completed trace ladder through it. **The assembly shape, exact**: `dominance_head_tail` +
  `crux_closure_route` — the certified head (today `n ≤ 2`) plus ONE tail bound from `n = 3` on
  yields the crux; the tail bound for the genuine parts is the single remaining object, provably
  equivalent to the v0.18.0 frontier. **Honesty guards, two-sided**: `dominance_satisfiable` (no
  hidden impossibility; the loose existential is NOT RH), `twoSlice_not_dominated` +
  `weilTraceTwo_not_crux` (the finite-assembly guard transfers to this face).
- **The classical sourcing, deep-research-verified** (101 agents, 23 claims confirmed 3-0 against
  the primary PDFs, 2 refuted): **Voros's strict dichotomy** (*Math. Phys. Anal. Geom.* 9 (2006)
  53–63, arXiv math/0506326 — "two sharply distinct and mutually exclusive asymptotic forms", NO
  third option): RH ⟺ `λₙ ~ ½n(log n − 1 + γ − log 2π)` mod `o(n)`; ¬RH ⟺ exponential oscillation
  `Σ((τₖ+i/2)/(τₖ−i/2))ⁿ + c.c.`, rate `|1 − 1/ρ| > 1` for the `Re ρ < 1/2` member of each
  off-line pair (rigorous via Darboux in the 2006 paper; the 2004 note's sign erratum pinned as a
  convention trap). **Lagarias** (*Ann. Inst. Fourier* 57 (2007) 1689–1740): the archimedean trend
  `(n/2)log n + cn + O(1)`, `c = (γ − 1 − log 2π)/2`, **unconditional** (Thm 5.1; Voros pins the ζ
  `O(1)` to `+3/4`); the `O(√n·log n)` excursion bound on the arithmetic part — a THEOREM under RH
  (Thm 6.1). The general-`n` archimedean closed form
  `λₙ^{∞} = 1 − (n/2)(γ + log 4π) + Σ_{j=2}^n (−1)ʲ C(n,j)(1 − 2^{−j})ζ(j)` matches the built
  slices exactly. Net: `Dominated`(genuine parts) is TRUE iff RH — both directions confirmed at the
  asymptotic level — and **no unconditional tail bound exists in the verified literature** (the
  one-sided shape is published only as Coffey's sufficiency Conjectures 2–3, math-ph/0505052); the
  equivalence-by-regrouping is this release's theorem, per the Conrey–Li relocation discipline.
- **THE GENUINE ARCHIMEDEAN TREND, ALL `n`** (`F1Square/Analysis/ArchTrend.lean`) — the closure
  push: the archimedean side of the crux as a single constructed object, `genuineArchSeq n =
  1 − (n/2)(γ + log 4π) + Σ_{j=2}^n (−1)ʲC(n,j)(1 − 2^{−j})ζ(j)` for EVERY `n` — one definition, no
  enumeration; every ingredient already built (`γ`, `log 4π`, `ζ(j)` for all `j ≥ 2`, binomials).
  Consistency THEOREMS at both independently-built slices (`genuineArch_one`/`genuineArch_two` —
  genuine reconciliations of distinct constructions). **`crux_vs_constructed_trend`** — the sharpest
  honest statement of RH this substrate provides: for any spectral square whose trace splits against
  the BUILT trend, the crux ⟺ "the arithmetic part admits one bound strictly below
  `genuineArchSeq`". The open content of RH contracts to the arithmetic side alone; the trend's
  classical growth is sourced, not mechanized; nothing touches positivity of the genuine `λₙ`.
- **THE GENUINE LI SEQUENCE IN CLOSED FORM** (`F1Square/Analysis/GenuineLi.lean`) — the
  implementation's deepest open question ("the genuine sequences are unconstructed") closed modulo
  the Stieltjes tail: `StieltjesEta` (η-data with the BUILT anchors `η₀ = −γ`, `η₁ = γ² + 2γ₁` as
  proof fields), `genuineArithSeq` (`λₙ^{arith} = −Σ_{j=1}^n C(n,j)·η_{j−1}`, every `n` — the
  verified non-alternating closed form, anchored to BOTH mechanized slices as theorems
  `genuineArith_one/two`; the Coffey recursion deliberately NOT used, convention guard), and
  **`genuineLamSeq` — the genuine Li sequence with both sides closed forms** (`weilTraceGenuine`:
  the full-ladder trace, definitional at every positive index, exactly as classically `λₙ` is
  defined through the explicit formula). The closed form MEETS the certified values
  (`genuineLam_one/two`), so **the head is a THEOREM** (`genuineLam_head`: `Pos` at `n = 1, 2` for
  ANY anchored η-data). `etaTwoSlice` inhabits the structure; its `n ≥ 3` outputs are flagged
  TRUNCATIONS (caution (d)). **`crux_genuine_form`** + **`crux_genuine_route`** (the maximal honest
  reduction): the crux follows from exactly TWO open inputs — the genuine η-tail (`γ₂, γ₃, …`,
  constructible one at a time by the `GammaOne` pattern) and ONE bound between the two closed forms
  from `n = 3` on, a bound that exists iff RH. The head is DISCHARGED; neither input is asserted.
- **The final roll-up** (`F1Square.lean`) — the stage-E backing block, the elaboration-checked
  v0.19.0 witness (both trace realizations, the retirement, the ∀-form three-face equivalence, the
  dominance reading, both guards, crux fields `none`), and the **v1.0.0-candidate state**: complete
  construction, honest crux. Workspace hygiene: warning-free build; `Li.lean` realization ledger;
  `Attempt.lean` frontier cross-pointer.

- **THE GENUINE-PAIRING ARC** (the closure push, continued — the formerly-planned v0.20/v0.21
  work folded into this release; deep-research #4: 99 agents, 21 claims confirmed 3-0 against the
  primary PDFs, 4 refuted):
  - *Substrate*: `Analysis/RMax.lean` — `Rabs` (Bishop-regular with no reindex, via the reverse
    triangle inequality on exact ℚ), `RmaxZero = ½(t+|t|)`, and the tent calculus (non-negativity,
    vanishing off support, identity on support) — compactly-supported piecewise-linear test
    functions as total `Real → Real` functions; `Analysis/RSum.lean` — finite real sums with the
    congruence/PSD/monotonicity transports.
  - **THE WEIL FUNCTIONAL, assembled** (`Analysis/Weil.lean`, `Square/Pairing.lean`): in the pinned
    CC unsymmetrized normalization (arXiv 2006.13771 App. B; the three-normalization trap and the
    `dx` vs `dx/x` involution trap recorded), `W(f) = poles − (primes + archimedean)` — **the zero
    side is the DEFECT of the built sides; no zeros are inputs**. CONSTRUCTED: the whole
    finite-place side `weilPrimePart = Σ_{n≤X} Λ(n)(f(n) + n⁻¹f(1/n))` (rational weights, finite by
    support, stable past the cutoff) and the archimedean constant `(log 4π + γ)·f(1)` (both factors
    built). INTERFACE (the faithful boundary): the pole terms and the archimedean integral — their
    piecewise-linear closed forms are routine but **unverified in print** (the deep-research open
    question), so transcribing them would breach the gate. Piecewise-linear test data is ADMISSIBLE
    to Weil's criterion directly (Bombieri's class `W`, the official Clay problem description §V).
  - **THE FOURTH FACE** : `weilSpectralSquare` — the FIRST `SpectralSquare` whose `cSq` comes from a
    pairing-valued assembly (the dictionary holds by construction) — with `weil_psd_iff_hodge` and
    `weil_strict_iff_crux`: positivity of the pairing family ⟺ the crux ⟺ Li positivity ⟺
    dominance. For the genuine family this is Weil positivity = RH — **elementary in both
    directions** (Weil 1952; Burnol math/9810169 proves the Lemma directly, no density argument —
    the presumed 'hard direction' was adversarially refuted). Guard: `weil_template_crux`.
  - **The first computed pairing value** (`weilPrime_demo`): the finite-place side at the
    piecewise-linear tent peaked at `2` is exactly `log 2` — the pairing sees the prime through the
    test function (the §2.3 "separation = Λ" finding, now on the pairing side, as a theorem).
  - **The unconditional territory, recorded** (pinned, not asserted): Connes–Consani (Selecta
    Math. 27 (2021), Thm 1) — Weil positivity is UNCONDITIONAL for test support in
    `[2^{−1/2}, 2^{1/2}]` (the prime-free window — where the constructed finite-place side vanishes
    by `weilPrimePart_stable`'s discipline); the certificate is the Sonine-space projection
    (infinite-dimensional). Burnol's precursor window carries an EXPLICIT nonnegative spectral
    multiplier `α(τ) = 8√2·cos(τ log 2)/(1+4τ²) + h₊(τ)`, `h₊ = −log π + Re ψ(1/4 + iτ/2)` — the
    natural constructive SOS target (needs uniform-in-τ digamma bounds; the pinned next
    mechanization). **The window theorem holds on the built object** (`weilPrime_window`/
    `weilValue_window`): a test datum with support inside the prime-free window has identically
    vanishing finite-place side at every truncation depth, so the assembled `W` reduces in-window
    to `poles − archimedean` — the exact statement the certificate program starts from, as a
    theorem of the assembly. Bombieri's Lincei truncations were verified to be ZERO-INDEXED (not
    zero-free certification targets) — that route is honestly closed.
  - **THE WINDOW CERTIFICATE, computed** (`Analysis/PsiQuarter.lean`, `Analysis/BurnolAlpha.lean`):
    Burnol's spectral multiplier `α(τ) = 8√2·cos(τ log2)/(1+4τ²) + h₊(τ)`,
    `h₊(τ) = −logπ + Re ψ(1/4 + iτ/2)`, evaluated at the center of the prime-free window. **ψ(1/4)**
    is built as the FIRST exact non-trivial digamma value — at `z = 1/4` the digamma series has
    exact-rational terms `1/(n+1) − 1/(n+1/4) = −3/[(n+1)(4n+1)]`, a sign-definite series with a
    telescoping tail, giving a genuine direct-sequence constructive real with `ψ(1/4) ≥ −4.32`
    (true `≈ −4.2270`, via `Rgamma_h_upper` and a uniform partial-sum bound). **`α(0) > 0`**
    (`burnolAlphaZero_pos`, true `≈ 5.94`) is then an axiom-clean theorem — `8√2 − logπ + ψ(1/4)`,
    with `√2 = exp(½ log2) ≥ 1` (`RrpowPos`, no sqrt primitive) — certified from the wide margin
    `8·1 − 1.15 − 4.32 = 2.53 > 0`. This is EVIDENCE for the windowed Weil positivity (the
    multiplier at one point), exactly as `weilPrime_demo` / the certified `λ`-slices are evidence —
    NOT the universal `α(τ) ≥ 0 ∀τ` (needs the uniform-in-τ complex-digamma bound), still less RH
    (the window excludes every prime). The universal window theorem stays the pinned next target.
  - **THE τ-PARAMETERIZED KERNEL + THE HONEST INDEFINITENESS FINDING** (`Analysis/DigammaWindow.lean`):
    the kernel `Re ψ(1/4 + iτ/2)` has exact-rational terms (even in `τ`); `windowKernel`
    `g_n(s) = (n+1/4)/((n+1/4)²+s)` is proven ANTITONE in `s = τ²/4` (`windowKernel_antitone`), so
    `windowTerm = 1/(n+1) − g_n` is MONOTONE INCREASING in `τ²` (`windowTerm_mono`) — hence `h₊(τ)`
    increases from `h₊(0) ≈ −5.37` toward `+∞`; `windowTerm_zero` reduces the kernel at `τ = 0` to
    `ψ(1/4)`'s summand. **The load-bearing finding** (recorded faithfully): the BARE multiplier `α`
    is **NOT** pointwise non-negative — `α(0) ≈ 5.94 > 0` but `α` is INDEFINITE, dipping to `≈ −1.0`
    near `τ ≈ 2.27`. This is exactly why Burnol needs the restricted-class `A_ε`-correction and
    Connes–Consani need the Sonine projection: **`α(τ) ≥ 0 ∀τ` is NOT a theorem**, so the
    unconditional window positivity stays the honest interface — the monotone kernel (which bounds
    the negative band) is the correct object the genuine window theorem is built from (v0.20.0).

### Honest scope (the bright line, unchanged)
- The dominance face RELOCATES the difficulty (Conrey–Li); it does not remove it. The open content
  of RH is now ONE object: a single bound sequence dominating the genuine arithmetic part strictly
  below the genuine archimedean trend — which exists iff RH (verified both directions). Nothing
  asserts it; `hodgeIndexHolds`/`liPositivityHolds` stay `none`; **RH stays OPEN**. The certified
  slices remain `n = 1, 2`; the next slice needs `γ₂`.

## [0.18.0] - 2026-06-12

### Added — stage D: the bridge and the crux attempt (pure Lean 4, no Mathlib, no `sorry`, choice-free)

The two stage-D release goals are delivered: **the geometric and analytic faces of the crux are proven
equivalent**, and **the crux attempt ran under the gate** — it did not close the universal, so
`hodgeIndexHolds`/`liPositivityHolds` stay `none` and **RH stays OPEN**, with the bridge substrate shipped
exactly as scoped. Every theorem is choice-free (`{propext, Quot.sound}`), audited; the gate passes.

- **The Castelnuovo–Severi anchor** (`F1Square/BridgeFF.lean`) — the function-field model of
  "Hodge index ⟹ RH" as a genuine lattice derivation, no governor shortcut: the `E × E` lattice
  `{F_h, F_v, Δ, Γ}` with the standard Gram (`Γ` bidegree `(1, q)`; `Δ² = Γ² = 0`, genus-1 adjunction;
  the **trace datum** `Δ·Γ = q+1−a` by Lefschetz — `ff_trace_datum`); the primitive projection
  `D° = D − (D·F_v)F_h − (D·F_h)F_v` of `D = xΔ + yΓ` (`primDG_perp_h/v`); the computation
  **`primDG_sq`**: `D°² = −2(x² + a·xy + q·y²)` — the Hodge-index form IS the binary quadratic form of
  discriminant `a² − 4q`; and **`ff_hodge_iff_hasse`**: `∀x,y D°² ≤ 0 ⟺ a² ≤ 4q` (forward: instantiate
  `(a, −2)`; backward: `4(x²+axy+qy²) = (2x+ay)² + (4q−a²)y²`). `ff_hodge_iff_hodgeType` derives the
  v0.1.0 governor from lattice positivity — "§0.3: the mechanism is not the gap" is now a theorem.
- **The λ₂ Bombieri–Lagarias decomposition** (`F1Square/Analysis/LiTwo.lean`) —
  `λ₂^{arith} = −(2η₀ + η₁) = 2γ − (γ² + 2γ₁)` (the prime side, via the Stieltjes `γ₁`) and
  `λ₂^{∞} = (1−γ) − log 4π + ¾ζ(2)` (the Γ-factor place); **`Rlambda2_decomposition`** proves
  `λ₂ = λ₂^{arith} + λ₂^{∞}` as a constructive-real identity. **`li_decomposition_two_realized`**:
  `Li.LiDecomposition` realized with BOTH genuine slices (`n = 1` from v0.15.3, `n = 2` new), both
  certified positive (`liTwo_evidence`).
- **THE BRIDGE** (`F1Square/Square/Spectral.lean`) — the release goal. `SpectralSquare`: the `H¹`-bearing
  enrichment of `𝕊` as an interface — the Li/trace data `lam`, the primitive-class self-intersections
  `cSq`, and the **dictionary** `⟨Cₙ,Cₙ⟩ = −2λₙ` (Deninger's Hodge-index reading of Li's criterion,
  Proc. Symp. Pure Math. 55 (1994); normalized exactly as `BridgeFF.primDG_sq` derives it on the
  function-field model; the classical chain "RH ⟺ Weil positivity ⟺ λₙ ≥ 0" is Weil 1952 / Li 1997 /
  Bombieri–Lagarias 1999 / Bombieri 2000). The equivalence is a genuine constructive **theorem**:
  `spectral_bridge_nonneg` (`⟨Cₙ,Cₙ⟩ ≤ 0 ∀n ⟺ Li.LiNonneg`), `spectral_bridge_pos(_slice)` (strict ⟺
  `Li.LiPositive`), and **`crux_faces_equivalent : SpectralCrux S ⟺ Li.LiCrux S.lam`** — via new
  doubling lemmas (`Pos_of_Radd_self` at the sequence level: a witness `1/(n+1) < 2x_{2n+1}` halves to
  `1/(2n+2) < x_{2n+1}`). Inhabited by `spectralTwoSlice` (the genuine certified `λ₁, λ₂`;
  `spectral_evidence_two`: `⟨C₁,C₁⟩ < 0` and `⟨C₂,C₂⟩ < 0` — the geometric face's first genuine
  negativity slices). **Honesty guards as theorems**: `spectralTwoSlice_not_crux` (the finite-slice
  instance provably FAILS the crux — its `n = 3` slice vanishes) and `spectral_iff_all_upTo` (no finite
  run of negativity checks reaches the crux — the finite-check guard, geometric face).
- **The crux attempt, under the gate** (`F1Square/Square/Attempt.lean`) — run, recorded, honestly
  concluded. Certified: strict Hodge negativity through `n = 2` (`spectral_strict_upTo_two`), the
  furthest any axiom-clean run reaches in this substrate. The frontier, exact:
  **`crux_attempt_frontier(_geometric)`** — given the certified slices, the crux ⟺ `∀ n ≥ 3, λₙ > 0`
  (the next slice needs `γ₂`, a fresh `GammaOne`-scale mechanization). The post-mortem records why the
  general routes are blocked, with the program's own controls as evidence (vacuous-kernel control
  `Bridge.control_psd`; pencil-blindness `square_hodge_pencil_blind`; the BL cancellation, companion
  §8.1; the Conrey–Li precedent) and what would close it (the genuine `H¹` instance, T4/§3.4 —
  Connes–Consani's archimedean/semilocal Weil positivity, Selecta Math. 27 (2021), being the strongest
  partial result). **Conclusion: the universal did not close; the fields stay `none`.**

### Honest scope (the bright line, unchanged)
- The bridge makes the two crux faces ONE proposition; it does not make that proposition easier. The
  certified slices are `n = 1, 2`; `λₙ > 0 ∀n` (= RH, both faces) stays open;
  `hodgeIndexHolds`/`liPositivityHolds` stay `none`. The genuine spectral instance (`H¹` with spectrum =
  the zeros) remains the program's single open object (T4/§3.4), now with the exact shape of what
  carrying it buys (`BridgeFF`).

## [0.17.0] - 2026-06-12

### Added — stage C: the canonical arithmetic square `𝕊 = Spec ℤ ×_𝔽₁ Spec ℤ` with its derived intersection lattice (pure Lean 4, no Mathlib, no `sorry`, choice-free)

The stage-C release goals are delivered (`F1Square/Square/`, six bricks). Every theorem is choice-free
(`#print axioms` = `{propext, Quot.sound}`), audited in `scripts/audit_axioms.lean`; the build is green and the
honesty gate passes. The crux fields stay `none` — **RH stays open**.

- **Canonical `𝕊` = the tensor `F ⊗_𝔽₁ F`, with its universal property PROVED**
  (`Square/Monoid.lean`, `Square/Tensor.lean`). Deitmar 𝔽₁-algebras are commutative monoids (realized as a
  bundled `CMon` record — the pure-core substitute for the typeclass hierarchy); the curve is the
  multiplicative monoid `ℕ₊` (free commutative on the primes — the canonical form of an element is its prime
  factorization, the UOR content-address); `𝔽₁` is the trivial monoid, proved **initial** (`f1_initial`), so
  the fiber coproduct over it is the plain coproduct: `𝕊 = ℕ₊ × ℕ₊` with injections `a ↦ a⊗1`, `b ↦ 1⊗b` and
  the **universal property** `copair_inl`/`copair_inr`/`copair_unique` (uniqueness via the tensor
  decomposition `z = z₁⊗z₂`, `sq_factor`); the 𝔽₁-cocone condition is automatic (`square_base_cocone`), so
  coproduct = pushout over `𝔽₁`. **Canonicality = the universal property** — `𝕊` is THE object, unique up to
  unique isomorphism, not a candidate model. Non-collapse of §3.1 (`ℤ ⊗_ℤ ℤ = ℤ`) by theorems: `inl ≠ inr`,
  the codiagonal identifies distinct points (`codiag_not_injective`, `gen2_codiag_collapse`), and the
  monomial family `2^a ⊗ 2^b` is **free of rank 2** (`gen2_injective`) — strict 2-dimensionality (T1 for all
  points, not a finite truncation); both projections recover the curve (`proj1_inl`, `proj_faithful`). The
  power Frobenius `frobPow k : a ↦ aᵏ` (a genuine hom) is distinguished from the Connes–Consani scaling flow
  `mScale n : a ↦ n·a` (NOT a hom, `mScale_not_hom` — a correspondence; its graphs are the pencil).
- **The distinguished divisors and their point counts** (`Square/Divisors.lean`): rulings `V_a = {a}×C`,
  `H_b = C×{b}`, diagonal `Δ`, Frobenius correspondences `Γ_n = {(m, n·m)}` as genuine subsets of `𝕊`;
  transverse singletons (`vFiber_inter_hFiber`, `diag_inter_vFiber/_hFiber`, `graph_inter_vFiber/_hFiber`),
  moving disjointness (`vFiber_disjoint`, `hFiber_disjoint`, `graph_disjoint`), the translate structure
  (`graph_translate_diag` — `Γ_n` is the flow translate of `Δ`; `vFiber_translate`), and the §2.3 finding at
  the point level: **`Δ ∩ Γ_n = ∅` for `n ≥ 2`** (`diag_inter_graph_empty`) — the scaling Frobenius has no
  transverse fixed points on canonical `𝕊`.
- **The parallel pencil with its shift lengths `log n`** (`Square/Pencil.lean`) — the §2.3 structural finding
  lifted from the candidate bi-tropical model to theorems on `𝕊`: **`logN_mul_general`**
  (`log(ab) = log a + log b` for ALL positive naturals, by exp injectivity — generalizing the v0.15.2 base-2
  keystone) and `logN_pow_general` (`log pᵏ = k·log p`); **`pencil_shift`** (`log y = log x + log n` on `Γ_n`
  — the affine shift, exact), **`pencil_parallel`** (slope 1 ⇒ recession direction `(1,1)`, the diagonal's
  own), **`pencil_det_zero`** (stable count `Δ·Γ_n = |det((1,1),(1,1))| = 0`, tied to the mechanized
  `Tropical.Signature.parallel_pencil`), **`pencil_separation`** (constant separation `log n`),
  **`pencil_separation_vonMangoldt`** (at a prime the separation IS `Λ(p) = log p`, the explicit-formula
  prime weight of `Analysis/Mangoldt.lean`), and `pencil_separation_pow` (`k·log p` — the closed orbit of
  length `log p` traversed `k` times). **The arithmetic content provably relocates to the shift lengths.**
- **The intersection lattice, DERIVED — never entered by hand** (`Square/Lattice.lean`, the §2.2 declarative
  discipline mechanized): every primitive number is a point count with classes moved along their translation
  pencils (`pair_*_derived`: `V·H = 1`, `V² = H² = 0`, `Δ·V = Δ·H = 1`, **`Δ² = 0` from the parallel-pencil
  disjointness itself**, `Γ·V = Γ·H = 1` — degree-1 translation correspondences, `Γ·Γ = Δ·Γ = 0`);
  bilinearity (`sqPair_add_left`, `sqPair_smul_left`) **forces `E₃² = −2`** (`e3_sq_forced`); the sourced
  §2.2 product-of-curves template **emerges** (`sqPair_eq_template`) — **T3's "realize the pairing
  intrinsically" is closed by derivation**, agreement with the template is now a consistency theorem. The
  five §2.2 gate self-checks are theorems (`sqPair_symm`, `sq_boundary_checks`, `sq_adjunction_checks`,
  `sq_signature_diag` — signature `(1,2)` by explicit diagonalization `{V+H, V−H, E₃} → diag(2,−2,−2)` with
  complementarity). The class lattice is **finitely generated** on the derived basis (`cls_generated`,
  T2 on `𝕊`); the graph class is **forced** (`graph_class_unique`), so `[Γ_n] = [Δ]` for all `n`
  (`pencil_numerically_trivial`).
- **Polarized `𝕊`, the Hodge index of the derived lattice, and the faithfulness boundary**
  (`Square/Polarized.lean`): `squarePolarized` — the `Crux.Polarized` instance is now `𝕊`'s own derived
  lattice (the stage-C lift); the ample class `H = [V]+[H]` has `H² = 2 > 0` (`sq_ample_pos` — verified, NOT
  automatic for a tropical surface) with Nakai-style meets (`sq_ample_meets`); `H^⊥` is negative-definite
  (`sq_hperp_neg_semidef`, `sq_hperp_definite`); **`square_hodgeIndex : HodgeIndex squarePolarized`** holds.
  **And the boundary** (`square_hodge_pencil_blind`): the lattice is **pencil-blind** — `[Γ_n] = [Δ]` and
  `Δ·Γ_n = 0` for ALL `n`, so the function-field trace input (`Δ·Γ_q = q+1−a`, `Mechanism.hodgeType`) is
  provably absent and the positivity carries **no spectral content** — the geometric face of the §2.3
  control (`Bridge.control_psd`). It is therefore **NOT the crux**.
- **Manifest de-hedge** (`F1Square.lean`, `Crux.lean`): `surfaceConstructed` and `parallelPencilFinding`
  flip `none → some true` (honest scope documented: canonical at the monoid-scheme / T1–T3 level; the
  `H¹`-bearing spectral enrichment is NOT constructed); `classGroupFinitelyGen` /
  `intersectionTemplateValid` / `ampleClassExists` are now carried by canonical `𝕊`; the
  `parallelPencilStructure` identity flips to universally valid; two new elaboration-checked witness
  examples bind the layer to the manifest; the `Crux` faithfulness caution is sharpened with the proven
  pencil-blindness boundary.

### Honest scope (the bright line, unchanged)
- The crux is the Hodge index / Weil positivity of the **`H¹`-bearing** pairing — the form on which the
  scaling flow acts with spectrum = the zeta zeros (T4/T5), equivalently `λₙ ≥ 0 ∀n` (Li). `𝕊`'s coarse
  numerical lattice provably does not carry it (`square_hodge_pencil_blind`), so `square_hodgeIndex` is a
  result about the constructed object and **not** an RH claim. `hodgeIndexHolds` / `liPositivityHolds` stay
  `none` — **RH stays open**. Stating the geometric⟺analytic equivalence faithfully is stage D (v0.18.0).

## [0.16.0] - 2026-06-11

### Added — stage B: critical-strip `ζ`, the archimedean `Γ′/Γ` place, and `Pos λ₂` (pure Lean 4, no Mathlib, no `sorry`, choice-free)

The three v0.16.0 release goals are delivered. Every theorem below is choice-free
(`#print axioms` = `{propext, Quot.sound}`), audited in `scripts/audit_axioms.lean`; the build is green
and the honesty gate passes. The crux `liPositivityHolds`/`hodgeIndexHolds` stay `none` — **RH stays open**.

- **(B) `ζ(s)` on the critical strip `0 < Re s < 1`** — built the integration-free way, via the **Dirichlet
  eta** `η(s) = Σ (−1)^{n−1} n⁻ˢ`, which converges by **bounded variation** across the whole strip where the
  raw `ζ` series diverges.
  - `F1Square/Analysis/EtaVariation.lean` — **`Ceta`**: `η(s)` for every `Re s > 0` as a genuine constructive
    `ℂ`, the Bishop diagonal limit (`Rlim`) of the reindexed paired partial sums. The convergence is the full
    dyadic-geometric `RReg` stack adapted to `σ > 0`: the per-term variation bound (a new alternating-series
    quadratic remainder `altSum_quad`, the `RlogNat ↔ logN` bridge, a two-sided product keystone), the pairing
    identity, the geometric block bound `≤ ofQ(Vconst·rᵏ)` (`r = 1/(1+τ) < 1`), the telescoping tail
    `EtaVSum_tail_full → ofQ(Vconst/(j+1))`, the odd-offset subsum, and the reindex `etaMidx` (absorbing the
    `Vconst` prefactor) → `RReg_of_real_bound` → `Rlim`.
  - `F1Square/Analysis/CriticalZeta.lean` — **`CzetaStrip`**: `ζ(s) = η(s) / (1 − 2^{1−s})` for `0 < Re s < 1`,
    a genuine constructive `ℂ`. `cpowNeg_normSq` (`|n⁻ˢ|² = n⁻²ᴿᵉˢ`), the denominator
    `1 − 2^{1−s} = 1 − 2·cpowNeg s 2` (reusing `cpowNeg`, no new `Cexp`), its **non-vanishing**
    `etaDenom_Pos_normSq` (`|1 − 2^{1−s}|² ≥ (2^{1−σ} − 1)² > 0`, the spurious zeros all sit on `Re s = 1`),
    the constructive inverse `Cinv`, and the certificate `CzetaStrip_functional : (1 − 2^{1−s})·ζ ≈ η`. Since
    `ExactBoundedReal = Real`, the real and imaginary parts are exact-bounded objects automatically.
- **(A) The Gamma function via Spouge; the archimedean `Γ′/Γ` place** (`F1Square/Analysis/Gamma.lean`).
  - **`RrpowPos`** — the real power `x^y := exp(y·log x)` for a positive base, the single combinator behind
    every Spouge power (`√(2π) = exp(½·log 2π)`, `(z+a)^{z+½}`, the half-integer `(a−k)^{k−½}`). **No sqrt
    primitive and no complex `Clog` are needed.**
  - **`Digamma`** — the archimedean place `ψ = Γ′/Γ` as a genuine constructive real (the **exact** object, not an
    approximation), via the convergent series `ψ(z) = −γ + Σ_{n≥0}[1/(n+1) − 1/(n+z)]`. Architecture mirrors
    `Ceta`: per-term two-sided bound `|t_n| ≤ B/((n+1)n)` (`Rinv_le_ofQ_Qinv` + a two-sided product bound),
    the telescoping tail `digammaTail_two_sided`, the reindex `digammaMidx` absorbing `B = |z−1|`, then
    `RReg_of_real_bound` → `Rlim`; reuses the Euler–Mascheroni constant `Rgamma_h`.
  - **`SpougeGamma`** — Spouge's approximant of `Γ(z+1) = (z+a)^{z+½}·e^{−(z+a)}·(c₀ + Σ_{k=1}^{N} c_k/(z+k))`,
    `c₀ = √(2π)`, `c_k = ((−1)^{k−1}/(k−1)!)(a−k)^{k−½}e^{a−k}`, as a constructive real built entirely from
    `exp`/`log`/reciprocal of positive reals (general rational parameter `a`). Spouge's explicit **relative**-error
    bound `|ε_S(a,z)| < √a·(2π)^{−(a+½)}/Re(z+a)` (`a ≥ 3`; Spouge 1994 SIAM J. Numer. Anal. 31(3); Pugh thesis
    eqns 2.18–2.19) is **documented, not asserted as a Lean theorem** — a rigorous proof presupposes an
    independent `Γ`, so the *exact* archimedean place is carried by the `Digamma` series instead.
- **(C) `Pos λ₂`** (`F1Square/Analysis/LambdaTwo.lean`) — the second Li/Keiper coefficient is positive
  (`Rlambda2_pos : Pos Rlambda2`, certified lower bound `λ₂ ≥ 0.0043`; true value `λ₂ ≈ 0.0923457`),
  the higher-Stieltjes-`γₙ` → `λₙ` capstone, a
  `λ₁`-style positivity certificate for `n = 2`.

### Honest scope (unchanged)
- `Pos λ₂` is **evidence** for Li's criterion at `n = 2`, **not** the crux: `liPositivityHolds` stays `none`
  and **RH stays open**. `λₙ > 0 ∀ n` (= RH), the off-critical-line zeros, and the arithmetic square remain
  deferred. The Spouge `Γ`-value's error bound is cited, not formalized; the archimedean place used downstream
  is the exact `Digamma`.

## [0.15.3] - 2026-06-10

### Added — the explicit formula's arithmetic ingredient: von Mangoldt `Λ`, the prime side, and the Bombieri–Lagarias `n = 1` decomposition (pure Lean 4, no Mathlib, no `sorry`)
- **The von Mangoldt function `Λ`** (`F1Square/Analysis/Mangoldt.lean`) — `vonMangoldt n`: `log p` when
  `n = pᵏ` is a prime power, else `0`. Built with no primality predicate beyond the **smallest factor**
  `spf n` (least `d ≥ 2` dividing `n`) and a prime-power test (strip `spf` to `1`). Everything is
  computable, so the defining values hold by reduction: `Λ(1) = 0`, `Λ(2) = Λ(4) = Λ(8) = log 2`,
  `Λ(3) = Λ(9) = log 3`, `Λ(6) = 0`; and `Λ ≥ 0` everywhere (`vonMangoldt_nonneg`).
- **`spf` is proved to be the least PRIME factor** — `spf_dvd` (it divides `n`), `spf_two_le` (`≥ 2`),
  and `spf_prime` (its only divisors are `1` and itself), via the fuel-sufficient search specification
  `spfFrom_spec`. So `Λ` is genuinely the von Mangoldt function (not a table matching at sampled
  points): `vonMangoldt_prime` gives `Λ(p) = log p` for **every** prime `p`.
- **The explicit-formula prime side** — `primeSide h N = Σ_{n=2}^N Λ(n)·h(log n)`, the prime side
  `Σ_p Σ_k log p · h(k·log p)` reindexed through `k·log p = log(pᵏ) = log n`. A finite sum, hence a
  genuine constructive real with **no convergence hypothesis**; `primeSide_stable` proves it is constant
  past the support cutoff, so a **compactly supported** `h` gives a single well-defined real
  (`primeTerm_zero_of_h` derives term-support from `h`-support).
- **The Bombieri–Lagarias decomposition of `λ₁`** (`F1Square/Analysis/LiOne.lean`) —
  `Rlambda1_decomposition : λ₁ ≈ λ₁^{arith} + λ₁^{∞}`, the two-place split of the explicit formula:
  - `Rlambda1_arith = γ` — the **finite/arithmetic place** `S_f(1) = −η₀` (`η₀ = −γ`; the regularized
    von Mangoldt / prime-power contribution).
  - `Rlambda1_arch = 1 − γ/2 − ½·log(4π)` — the **archimedean Gamma-factor place** `S_∞(1)` (incl. the
    trivial-pole "1").
  - proved by reducing both `λ₁ = ½·(2 + γ − log 4π)` and `arith + arch` to the canonical form
    `(1 + γ/2) − ½·log(4π)` via the pointwise `Rhalf` distribution (`Rhalf_Radd`, `Rhalf_Rneg`,
    `Rhalf_two`) and `γ − γ/2 ≈ γ/2` (`Rhalf_double`).
- **`Li.LiDecomposition` is now realized non-trivially** — `li_decomposition_realized`:
  `LiDecomposition liLamSeq liArithSeq liArchSeq`, a proven instance whose `n = 1` slice is the genuine
  arithmetic/archimedean split (`Rlambda1_decomposition`), promoting the interface from the trivial
  inhabitant `λ = λ + 0` (`Li.liDecomposition_genuine`).

### Honest scope (unchanged)
- Deriving the value `S_f(1) = γ` *from* the prime sum needs `ζ'/ζ` and its analytic continuation
  (v0.16.0+), so the Bombieri–Lagarias value is stated faithfully and **not** identified with the
  built `primeSide` — nothing is fabricated. None of this bears on positivity: the crux
  `liPositivityHolds` stays `none` and **RH stays open**. Critical strip, zeros, and the genuine `λₙ`
  for `n ≥ 2` remain deferred.
- All new theorems are choice-free (`{propext, Quot.sound}`), audited in `scripts/audit_axioms.lean`;
  the build is green and the honesty gate passes (coverage: 1211 proof-layer theorems).

## [0.15.2] - 2026-06-10

### Added — ζ(s) = Σ n⁻ˢ for **complex** s with Re s > 1, as a genuine constructive ℂ (pure Lean 4, no Mathlib, no `sorry`)
- **The Riemann zeta function for complex argument** (`F1Square/Analysis/ComplexZeta.lean`) — `Czeta s hσ … hθ`:
  for any complex `s` with `Re s ≥ 0` and a rational witness `τ > 0` of `Re s > 1` (`τ ≤ (Re s − 1)·log 2`),
  `ζ(s) = Σ_{n≥1} n⁻ˢ` is a genuine constructive complex number — its real and imaginary parts are Bishop
  diagonal limits (`Rlim`) of the reindexed dyadic partial sums `Σ_{n<2^{M(j)}} Re/Im(n⁻ˢ)`. This replaces
  the previous integer-only `ζ(s)` (`Σ 1/iˢ`, `s ≥ 2`): convergence now holds across the **full half-plane
  `Re s > 1`**, with `s` genuinely complex.
- **Convergence with a rate** — `Czeta_re_tendsTo` / `Czeta_im_tendsTo`: the partial sums converge to
  `Re/Im ζ(s)` with the canonical Bishop modulus `2/(k+1)` (`Rlim_tendsTo`). The rigorous complex geometric
  tail, certified.
- **The dyadic-geometric convergence proof**, built from scratch:
  - **exp injectivity → log-multiplicativity** (`F1Square/Analysis/RealPow.lean`) — `RexpReal_inj`,
    `logN_mul`, `logN_pow_two` (`log(2ᵏ) = k·log 2`), re-routing around the artanh addition boundary wall.
  - **dyadic block bound** — `czetaExp_block_geo`: the `[2ᵏ, 2ᵏ⁺¹)` block modulus `≤ ofQ(rᵏ)`,
    `r = 1/(1+τ) < 1` (the ratio `2·exp(−σ log2) = exp(−θ) ≤ r`, from `Re s > 1`).
  - **geometric tail** — `geoFrom_telescope` (`Σ_{k=j}^{j+d−1} rᵏ·(1−r) = rʲ − r^{j+d}`), `geoFrom_le`
    (`≤ rʲ/(1−r)`), and the dyadic telescoping `czetaExp_tail` (`E(2^{j+d}) − E(2ʲ) ≤ ofQ(Σ rᵏ)`).
  - **the geometric reindex** — `geom_reindex`: the Bernoulli `1/(linear)` decay `qpow_geom_bound` with the
    quadratic index `M(j) = (j+1)·r.den²` collapses `r^{M(j)}/(1−r) ≤ 1/(j+1)` (`czetaExp_tail_reindex`).
  - **the completeness bridge** — `seq_diff_le` (a real upper bound `a − b ≤ c` gives the same-index rational
    bound `aₙ − bₙ ≤ c + 2/(n+1)`, via regularity + the generalized Archimedean lemma) and `RReg_of_real_bound`
    (pairwise real differences `≤ 1/(j+1)+1/(k+1)` ⟹ a regular sequence of reals), feeding Bishop's `Rlim`.
  - **the Cauchy partial sums** — `czetaRe_RReg` / `czetaIm_RReg`: the reindexed real/imaginary partial sums
    are regular sequences of reals (the four two-sided tail bounds `czetaRe/Im_tail_le/ge`, case-split on `j ≤ k`).
- **Non-vacuity** — `czeta_two_theta` + a fully-closed `F1Square.lean` instance: `ζ(2) = Σ 1/n²` is built as
  `Czeta` and its partial sums converge (the `Re s > 1` hypothesis is satisfiable, `τ = 1/2 ≤ log 2`).
- **Full-sequence convergence** (not just the dyadic subsequence) — `czetaExp_mono` (E monotone),
  `czetaExp_tail_full` / `czetaRe`,`czetaIm_tail_full(_neg)` (the tail bound for *arbitrary* `N ≥ 2^{M(j)}`),
  `czetaRe`/`czetaIm_cauchy_full` (the **whole** partial-sum sequence is uniformly Cauchy: `|S(N) − S(N')| ≤
  2/(j+1)` for all `N, N' ≥ 2^{M(j)}`), and `czetaRe`/`czetaIm_full_tendsTo` (`|S(N) − ζ(s)| ≤ 3/(k+1)`). So
  `Σ_{n=1}^N n⁻ˢ` converges as a genuine series for every `N`, not merely along `2^{M(k)}`.
- **Canonicity** — `Czeta_re_canonical` / `Czeta_im_canonical`: `ζ(s)` is independent of the convergence
  witness `τ` (any two witnesses give `≈`-equal values — both are the limit of the same full sequence, via
  `RTendsTo_to_Rle` and the real-level Archimedean `Req_of_Rle_ofQ_all`). So `ζ(s)` is a well-defined function
  of `s` alone on `Re s > 1`.
- **`F1Square.lean` witnesses** binding `Czeta_re/im_tendsTo`, the concrete `ζ(2)`, the full-sequence Cauchy
  property, and canonicity — all for complex `s` with `Re s > 1`.
- Choice-free throughout (`{propext, Quot.sound}` only), `sorry`-free, `#print axioms`-audited at every commit.

### Unchanged — the honesty audit
- The crux `liPositivityHolds = none` (= RH) stays open; ζ ships in its convergent half-plane `Re s > 1`
  (where it has no zeros), and the analytic continuation to the critical strip is not built.

## [0.15.1] - 2026-06-09

### Added — the ζ-convergence gate `exp∘log = id` via genuine power-series composition (pure Lean 4, no Mathlib, no `sorry`)
- **`exp(2·artanh τ) = (1+τ)/(1−τ)` at the real level** (`F1Square/Analysis/ExpLog.lean`) —
  `Rexp_two_artanh_ofQ`: `RexpReal (TwoArtanhConst τ) ≈ (1+τ)/(1−τ)` for a constant rational `τ` (`0 ≤ τ < 1`).
  This is the roadmap's **research-grade base identity** (v0.15.1), built from scratch as a power-series
  composition — the elementary squeeze `1 + log x ≤ exp(log x) ≤ 1/(1−log x)` never pins equality, so the
  exp factorial series is composed with the artanh geometric series directly. The analytic core: the
  composition **corner bound** `exp_corner_le` (via finite-support truncation `truncTo`, the no-corner power
  `peval_fpow_pow_eq`, and the corner inequality `qpow_peval_le`), the formal-ODE identity `formal_exp_geom`
  (`fcomp ecoef (2·acoef) = dgeom`, by multiplicative-ODE uniqueness `fderiv_mul_inj`), the geometric closed
  form (`dgeom_geom_gap_le`), and the **rational identity** `exp_artanh_rat_cleared`. Lifted to the reals by
  the **diagonal reconciliation** `Rexp_two_artanh_via` (mirrors `RexpReal_congr`: a Lipschitz `P_match`
  matching the artanh inner depth to the exp outer depth via `peval_twoacoef_cauchy` + `expSum_Lip_le`/
  `LipS_le_U`, plus the `exp_artanh_recip` tail), with the argument-magnitude bounds `peval_twoacoef_abs_le_gpow`
  and `two_gPow_le`, and the clearing-division helper `mul_div_gen`.
- **`exp(log n) = n` for the *literal* `Rlog` term** (`F1Square/Analysis/ExpLog.lean`) — `Rexp_log_nat_Rlog`:
  `RexpReal (Rlog (ofQ n) …) ≈ n`, where `Rlog (ofQ n)` is the actual constructive logarithm
  `2·artanh((n−1)/(n+1))`. The base construction `RartanhConst`/`TwoArtanhConst`/`Rexp_two_artanh_ofQ` is
  **radius-general** (the convergence radius enters only through the depth reindex, which `Rexp_two_artanh_via`
  abstracts), so it applies directly at `Rlog`'s own smaller radius `ρ_M = (n−1)/(n+1)`, and
  `Rlog (ofQ n) = TwoArtanhConst (tmap n) ρ_M` holds by `rfl` (definitional equality of the constant-sequence
  artanh arguments). No `τ²≤½` smallness is needed. (`Rexp_log_nat` gives the same at the convenience radius
  `ρ = τ`.) The `tmap`-arithmetic (`1−τ = 2/(n+1)`, `g·(1−τ) = 1+τ`, `K·(1−τ) = 1`) is pure ℚ (`tmap_nat_den`/`num`).
- **Why it matters.** This closes the discovered dependency of stage A: `Σ n^{-s}` converges because
  `|n^{-s}| = n^{-Re s}`, i.e. `exp(log n) = n`. The honesty gate is met — the identity closes **axiom-clean**
  (`{propext, Quot.sound}` only), so the ζ-complex tail (v0.15.2) need not ship its convergence as an interface.
- **The crux stays `none`; RH is open.** `liPositivityHolds`/`hodgeIndexHolds` remain `none`.

## [0.15.0] - 2026-06-08

### Added — the complex analytic engine (stage A, exponential core): `exp` is a homomorphism, `nˢ` and its modulus (pure Lean 4, no Mathlib, no `sorry`)
- **The exponential functional equation on all of ℝ** (`F1Square/Analysis/ExpRealAdd.lean`) — `RexpReal_add`:
  `exp(x+y) ≈ exp x · exp y` for arbitrary constructive reals, the roadmap's technical core of stage A.
  Built from scratch as the diagonal lift of the rational Cauchy-product functional equation: the
  general-argument corner bound (`expSum_corner_le_gen`), its **signed** generalization
  (`expSum_corner_le_gen_signed`, `expSum_add_le_signed` — constructive-real samples dip negative even for
  positive reals), the exp diagonal reconciliations (`expSum_reconcile`, `rexp_factor_reconcile`), the uniform
  partial-sum bound (`expSum_abs_le_Un`), the factorial decay at the diagonal depth (`RexpReal_trunc_le`), and
  the deep-reference assembly (`rexp_add_gap`, `RexpReal_add_aux`). General exp-tail decay lemmas
  (`npow_fct_decay`, `truncCoef_Q/QE`) relocated to `ExpReal` for shared use.
- **The Pythagorean identity `cos² + sin² ≈ 1`** (`F1Square/Analysis/CosSinAdd.lean`) — `Rcos_sq_add_sin_sq`
  via the trigonometric Cauchy product from scratch, and its corollary **`|cos| ≤ 1`, `|sin| ≤ 1`**
  (`F1Square/Analysis/CosSinBound.lean`, `Rcos_sq_le_one`/`Rsin_sq_le_one`, through `Rnonneg_Rmul_self`).
- **The complex exponential `e^z`** (`F1Square/Analysis/ComplexExp.lean`) — `Cexp z = exp(re z)·(cos(im z) +
  i·sin(im z))` with component identities and `Cexp 0 ≈ 1` (`Cexp_zero`, `RexpReal_zero`, `Rcos_zero`,
  `Rsin_zero`).
- **`nˢ` and the modulus identity** (`F1Square/Analysis/ComplexMod.lean`, `ComplexPow.lean`) — `ncpow n s =
  Cexp(s·log n)` (positive-integer base via the real `RlogNat`), and `|Cexp z|² = (exp Re z)²` (`Cexp_normSq`,
  the analytic payoff of `cos²+sin²=1`) / `|nˢ|² = (exp(Re s·log n))²` (`ncpow_normSq`) — the squared modulus
  depends only on `Re s`, the basis of the future ζ tail bound.
- **The crux stays `none`; RH is open.** This release ships the *exponential core* of stage A. ζ for complex
  argument is **not** shipped: its convergence is gated on `exp(log n) = n` (`exp∘log = id`), a power-series
  composition that — because `log` is built independently as `2·artanh((x−1)/(x+1))` — is not definitional and
  is scoped to the **v0.15.x** series (see `ROADMAP.md`). `liPositivityHolds`/`hodgeIndexHolds` remain `none`.

## [0.14.0] - 2026-06-07

### Added — the analytic constants of the Li/Keiper bridge, and a positivity certificate for λ₁ (pure Lean 4, no Mathlib, no `sorry`)
- **π as a constructive real** (`F1Square/Analysis/Pi.lean`) — `Rpi` via Machin's formula
  `π = 16·arctan(1/5) − 4·arctan(1/239)` as a single Bishop-regular diagonal (`Arctan.lean` supplies the
  alternating arctan series on `[−ρ,ρ]`, `ρ<1`). Lower bracket `Rpi_lower` (π ≥ 6/5) gives `Pos Rpi`;
  the tight `Rpi_seq_ub_tight` (π ≤ 3.142) comes from the one-sided arctan truncation
  `arctanSum_deep_le`/`arctanSum_deep_ge` at the tightest radius `ρ = t`.
- **`log 2`, `log π`, `log 4π`** (`F1Square/Analysis/GammaAccel.lean`) — clean `2·artanh((x−1)/(x+1))`
  logs `Rlog2c`, `Rlogπc`, with kernel-certified upper bounds `Rlog2c_le` (`log 2 ≤ 0.6931`) and
  `Rlogπc_le` (`log π ≤ 1.1453`). The varying `π`-argument is dominated by the constant `15/29 = tmap(22/7)`
  (`artSum_base_mono`, since `π ≤ 22/7`), then truncated with an explicit geometric tail (`artSum_le_value`).
- **Euler–Mascheroni γ, convergence-accelerated** (`F1Square/Analysis/GammaAccel.lean`) — `Rgamma_h`, the
  harmonic-telescoped `γ = Σ(1/i − 2·artanh(1/(2i+1)))`, with the kernel-certified lower bracket
  `Rgamma_h_lower` (γ ≥ 0.54). This route is *feasible* where the alternating-ζ-series γ is not: that
  series carries the running `lcm` denominator (already `gammaSeq 2` has ~7000 digits), so a positivity
  certificate from it was out of computational reach.
- **`Pos λ₁` — the first Li coefficient is a positivity-certified constructive real**
  (`F1Square/Analysis/LambdaOne.lean`) — `Rlambda1 = ½·(2 + γ − log 4π)` (Bombieri–Lagarias), with
  `Rlambda1_pos : Pos Rlambda1`. Proven through `2λ₁ = 2 + γ − log 4π` (integer coefficients):
  `2λ₁ ≥ (2 + 0.54) − (2·0.6931 + 1.1453) = 0.0084 > 0`, hence `λ₁ ≥ 0.0042 > 0`. The ℝ-order bridges
  `Radd_le_add`, `Rneg_le`, `Rhalf`/`Rhalf_ge` carry the rational bounds through the ring operations.
- **The crux stays `none`; RH is open.** `λ₁ > 0` is the `n = 1` slice of Li's criterion realized as
  **evidence** — it does **not** assert `λₙ > 0 ∀ n` (which *is* RH). `liPositivityHolds` and
  `hodgeIndexHolds` remain `none`, never asserted. De-hedging here removes false modesty about the proven
  `λ₁` result (its certificate was previously documented as computationally infeasible); it adds no
  confidence about RH.
- All new theorems are `#print axioms`-audited and choice-free (`{propext, Quot.sound}`).

## [0.13.0] - 2026-06-07

### Added — the transcendentals on ℝ: `cos`, `sin`, and `log` on positive reals (pure Lean 4, no Mathlib, no `sorry`)
- **`cos` / `sin` on ℝ** (`F1Square/Analysis/CosSin.lean`) — the alternating power series as a directly
  Bishop-regular diagonal `RaltReal x off = ⟨Σ (−x²)ⁿ/(2n+off)!⟩`. The alternating term is dominated by
  the exponential of `M²` (`altTerm_abs_le`, `fct_mono`, `qsq_abs_le`), giving the truncation bound
  `altSum_trunc_bound` (geometric/factorial tail) and the Lipschitz bound `altSum_Lip_le`; the diagonal
  is regular (`RaltReal_regular`). `Rcos = RaltReal x 0`, `Rsin = x · RaltReal x 1`.
- **`log` on positive reals, positivity-as-data** (`F1Square/Analysis/Log.lean`) —
  `RlogPos x k = 2·artanh((x−1)/(x+1))` from a positivity witness `x_k > 1/(k+1)`, the *same* idiom as
  the reciprocal `Rinv`: the rational modulus `1/M ≤ x ≤ M` (`M = |x₀| + 2 + 1/L`, `L = δ/2` the witness
  floor via `Rinv_lb`) is **derived**, not demanded of the caller. (Constructively a modulus *is*
  necessary — `log` has no uniform modulus of continuity on `(0,∞)`.) The explicit-modulus engine
  `Rlog x M` takes `M` directly (`Rlog_two_ok` exhibits it on `x ≡ 2`):
  - **`artanh` on every `[−ρ,ρ]`, `ρ<1`** (`Rartanh`): the odd series `Σ t^{2n+1}/(2n+1)` as a regular
    diagonal, via the geometric telescoping `geo_diff_bound`, the truncation `artSum_trunc`, the
    Lipschitz `artSum_Lip_le` (with `geoEven_bound`), and the **general Bernoulli reindex**
    `qpow_geom_bound` (`ρᵐ ≤ q/(q+m(q−p))`) that tames the geometric tail.
  - **the t-map `q ↦ (q−1)/(q+1)`**: its cleared difference identity `tmap_diff_cleared`
    (`(tmap a − tmap b)·(a+1)(b+1) = 2(a−b)`), the Lipschitz bound `tmap_lipschitz`
    (`|tmap a − tmap b| ≤ (2/(L+1)²)·|a−b|`), and the range bound `tmap_abs_le`
    (`|tmap q| ≤ tmap M` for `q ∈ [1/M, M]`, keeping the artanh argument inside `[−ρ,ρ]`).
  - the diagonal `t.seq n = tmap(x_{2(n+1)})` is regular because the t-map is 2-Lipschitz on `x ≥ 0`
    (`Rlog_regular`); `tmap_M_eq` identifies the radius `ρ = tmap M < 1`.

### Changed — axiom-minimization (the axiom footprint cannot be a peer-review weakness)
- The entire proof layer is now **choice-free**: `Classical.choice` is eliminated. The only remaining
  axioms are `{propext, Quot.sound}`, both forced by `omega`/`simp`/`Int` core internals and
  constructively uncontroversial. (The two theorems that pulled choice did so only because `omega`
  discharged an `↔` goal directly; splitting into `Iff.intro` per direction is choice-free.)
- `scripts/honesty_audit.sh` tightened: the allowlist drops `Classical.choice`, so any future
  re-introduction of choice (or any other named axiom) fails CI. Coverage 399/399, enforced.

### Unchanged — the honest demarcation
- The crux stays `none` on both faces (`hodgeIndexHolds`, `liPositivityHolds`); RH is **open**
  (June 2026) and is never asserted. The transcendentals make more of the analytic half *statable and
  checkable*; they do not touch the crux.

## [0.12.0] - 2026-06-06

### Added — ℝ as a constructive field with powers, and `exp` on all of ℝ (pure Lean 4, no Mathlib, no `sorry`)
- **Real field / powers** (the multiplicative substrate the transcendentals need):
  - `F1Square/Analysis/Pow.lean` — real powers `Rpow` (iterated `Rmul`) with `Rpow_one`, `Rpow_congr`
    (powers respect `≈`).
  - `F1Square/Analysis/Inv.lean` — the reciprocal `1/x` of a positive real, **positivity-as-data**: from
    a witness `k` with `x_k > 1/(k+1)`, floor `x` by `L = δ/2 > 0` on the tail and reindex
    `R n = 4δ.den²(n+1) + 2δ.den`; `RinvSeq_regular` assembles full Bishop regularity. Plus the rational
    reciprocal `Qinv` (inverse law `a·(1/a) ≈ 1`, antitonicity, the difference identity
    `1/a − 1/b = (b−a)·(1/a)·(1/b)`) and division `Rdiv`.
  - `QOrder.lean` gains `Qmul_congr` and `Qmul_add_right` (ℚ multiplication respects `≈`; right
    distributivity).
- **`exp` on ℝ** (`F1Square/Analysis/ExpReal.lean`) — the everywhere-defined real exponential, as the
  **diagonal of rational partial sums**: `exp(x)_j = S_{R j}(x_{R j})` with `S_N(q) = Σ_{i≤N} qⁱ/i!`
  and a single reindex `R j` for both argument index and truncation depth. The diagonal sequence of
  rationals is itself Bishop-regular (`RexpReal_regular`: `|exp(x)_j − exp(x)_k| ≤ 1/(j+1)+1/(k+1)`), so
  it *is* a constructive real directly. Its three rational ingredients, all axiom-clean:
  - **truncation bound** `expSum_trunc_bound` — `|S_q(b) − S_q(a)| ≤ 2Mᵃ⁺¹/(a+1)!` for `|q| ≤ M`,
    `2M ≤ a ≤ b` (the dominating `M`-series `expSumM` with its telescoping tail `expM_diff_bound`, and
    termwise domination of the general-`q` gap);
  - **Lipschitz bound** `expSum_Lip_le` + `LipS_le_U` — `|S_q(N) − S_{q'}(N)| ≤ C·|q − q'|` with `C`
    uniform in `N` (per-power `|qⁱ − q'ⁱ| ≤ i·Mⁱ⁻¹·|q−q'|`, summed);
  - **factorial-growth** `fct_ge_geom` + `trunc_reindex` — the super-fast factorial tail converts to a
    `1/(j+1)` reindex.
- `F1Square.lean` gains the v0.12.0 manifest mapping + an elaboration-checked `example` (real powers
  `x¹ ≈ x`; `exp` is genuinely constructed with its rigorous diagonal gap bound).
  `scripts/audit_axioms.lean` extended (coverage 341/341, enforced); honesty audit PASS, axiom-clean.

### Note
- This completes the field/powers + `exp` substrate. Next: **v0.13.0** `cos`/`sin` + `log` (prereqs —
  `Rinv`, `qpow` with its bounds, ℝ-completeness — are all in place). Then the next phase: ζ's
  continuation into the critical strip (needs complex exp/log), the genuine `λₙ` realizing the v0.10.0
  interfaces, and the explicit-formula trace, ending at `λₙ > 0 ∀n` = RH (the open frontier). RH remains
  open (June 2026); no 𝔽₁-square construction exists.

## [0.11.0] - 2026-06-06

### Added — the order `≤` on constructive ℝ (pure Lean 4, no Mathlib, no `sorry`): the foundation for the transcendentals
- `F1Square/Analysis/ROrder.lean` — **`Rle`**, the Bishop order `x ≤ y ⟺ ∀ n, xₙ ≤ yₙ + 2/(n+1)`,
  with the genuine order laws: `Rle_refl`, `Rle_of_Req` (`≈ ⟹ ≤`), `Rle_antisymm` (`x ≤ y` and
  `y ≤ x` ⟹ `x ≈ y`), and **`Rle_trans`** — the one genuine limiting step: chaining `x ≤ y ≤ z`
  through an auxiliary index `m` gives `xₙ ≤ zₙ + 2/(n+1) + 6/(m+1)` for every `m`, and the generalized
  Archimedean lemma `Qarch_gen` kills the `6/(m+1)` tail (the argument behind `Req_trans`).
- **`Rnonneg` canonicalized** here (moved from `Li`): Bishop `x ≥ 0` (`−1/(n+1) ≤ xₙ`), with
  `Rnonneg_zero`/`Rnonneg_one`/`Rnonneg_Radd`, and `Rle_zero_of_Rnonneg` (`x ≥ 0 ⟹ 0 ≤ x`).
- ℚ signed-bound helpers (`Qle_self_Qabs`, `Qabs_le_of_both`, `Qle_add_of_Qabs_sub`,
  `Qsub_le_of_le_add`); `Qle_self_add`/`Qle_add_self` moved to `QOrder` (their natural home).
- `F1Square.lean` gains a v0.11.0 `example`; `scripts/audit_axioms.lean` extended (coverage 288/288,
  enforced); the honesty gate is hardened to also fail on **duplicate proof-layer theorem short-names**;
  honesty audit PASS, axiom-clean and choice-free.

### Note
- This is the foundation the transcendentals build on. The roadmap for the rest, concretely (no open
  `+`): **v0.12.0** reciprocal `Rinv` + `exp` on ℝ; **v0.13.0** `cos`/`sin` + `log`; then the next
  phase — ζ's continuation into the critical strip (needs complex exp/log), the genuine `λₙ` realizing
  the v0.10.0 interfaces, and the explicit-formula trace, which ends at `λₙ > 0 ∀n` = RH (the open
  frontier). RH remains open (June 2026); no 𝔽₁-square construction exists.

## [0.10.0] - 2026-06-06

### Added — the λₙ / Riemann-Hypothesis proof boundary, locked faithfully (pure Lean 4, no Mathlib, no `sorry`)
- `F1Square/Li.lean` — the **analytic face** of the same crux `Crux.lean` states geometrically. By
  **Li's criterion** (Li 1997), RH ⟺ `λₙ > 0` for all `n ≥ 1` (the paired sum over the nontrivial
  zeros; the non-strict `≥ 0` form is the general Bombieri–Lagarias 1999 multiset criterion, also
  ⟺ RH). This brick states that boundary precisely, before ζ is built, so the proof boundary is pinned.
- **Bishop ℝ order**: `Rnonneg` (the non-strict `x ≥ 0`, companion to the existing strict `Pos`), with
  `Rnonneg_zero`, `Rnonneg_one`, `Pos_one`, and the generic `Rnonneg_Radd` (sum of non-negatives is
  non-negative — *explicitly disclaimed* as **not** the mechanism behind Li-positivity, since the
  Bombieri–Lagarias parts `λₙ^{arith} = −Σ Λ(m)wₙ(m)` and `λₙ^{∞}` have opposite signs and `λₙ > 0` is
  a delicate cancellation, which is the open difficulty).
- **The Li-positivity property** `LiPositive` (strict, ζ-specific) and `LiNonneg` (BL non-strict),
  proven genuine/satisfiable by `template_liPositive`/`template_liNonneg` (the constant-`1` sequence) —
  the analytic analogue of `Crux.template_hodgeIndex`.
- **The finite-check guard** `liPositive_iff_all_upTo`: `LiPositive lam ↔ ∀ N, LiPositiveUpTo lam N`.
  This encodes precisely why the numerical positivity of the first ~10⁵ Li coefficients (computed to
  n = 100 000, Feb 2025) is **not** a proof: the theorem is the universal `∀ N`, which no finite
  `decide` reaches.
- **THE CRUX (analytic face)** `LiCrux λ` for the unconstructed genuine ζ-derived Li sequence — OPEN,
  never asserted, never axiomatized. A detailed **faithfulness caution** forbids the standard traps
  (existential witness, manifestly-positive definition, finite/truncated `decide`); `LiPositive λ ⟺ RH`
  is [CLASSICAL] (Li 1997), and positivity reformulations do not make RH easier (Conrey–Li 2000).
- **ζ-layer substrate as honest interfaces** (genuine/inhabited, never asserted for the real `λ`):
  `LiDecomposition` (Bombieri–Lagarias), `ExplicitFormulaTrace` (Weil 1952 / Connes 1999), `LiAgreesWith`.

### Added — ζ and λₙ as exact-bounded objects
- `F1Square/Analysis/ExactBounded.lean` — **`ExactBoundedReal`**: a constructive real presented as a
  stream of certified rational enclosures `[xₙ − 1/(n+1), xₙ + 1/(n+1)]`, with the exact-width identity
  `enclosure_width` (`upperB − lowerB = 2/(n+1)`), `lowerB_le_upperB`, and the regularity `certificate`.
  The Li coefficients are typed `λ : Nat → ExactBoundedReal`.
- `F1Square/Analysis/Zeta.lean` — **`ζ(s)` for integer `s ≥ 2` as a genuine exact-bounded constructive
  real**: `Σ_{i≥1} 1/iˢ` (natural powers `npow` from scratch), with the rigorous rational tail bound
  `zetadiff_bound` (`S(b) − S(a) ≤ 1/(a+1)` for `a ≤ b`) via the telescoping decreasing
  `U(N) := S(N) + 1/(N+1)` (the added term `1/(N+2)ˢ ≤ 1/((N+1)(N+2))` since `(N+1)(N+2) ≤ (N+2)ˢ`).
  The bound is already the Bishop modulus, so the partial sums are directly regular (`zetaSeq_regular`,
  no reindex). `zeta_pos`: `ζ(s) > 0`. **Honest scope:** this is ζ in the convergent half-plane
  `Re(s) > 1` at integer points — where ζ has **no zeros** and RH does **not** live; the analytic
  continuation to the critical strip (and ζ at complex `s`) is **not** built, and the genuine `λₙ`
  *values* (needing the continuation + `log`) are not fabricated — only their exact-bounded *type* and
  the boundary are shipped.
- `F1Square.lean`: the status roll-up `F1SquareStatus` gains `liPositivityHolds := none` — the analytic
  face of RH, alongside the geometric `hodgeIndexHolds := none`. Both crux faces are `none`. New v0.10.0
  mapping + two elaboration-checked `example`s (the Li boundary; ζ as an exact-bounded object);
  `scripts/audit_axioms.lean` extended (coverage now 279/279, enforced); honesty audit PASS,
  axiom-clean and choice-free.

### Note
- RH remains **open** (June 2026); Li-positivity is unproven for all `n` (only finite ranges checked
  numerically). No 𝔽₁-square construction exists. This brick makes the analytic boundary *statable and
  checkable* — it does not, and cannot here, prove `λₙ > 0 ∀n`, which is RH.

## [0.9.0] - 2026-06-06

### Added — the general exponential `exp(q)` on the rational interval `[0,1]` (pure Lean 4, no Mathlib, no `sorry`, choice-free)
- `F1Square/Analysis/ExpGen.lean` — **`exp(q) = Σ qⁱ/i!` for rational `q ∈ [0,1]`, as a constructive
  real**, with a rigorous rational error bound. This continues the transcendentals arc opened by
  `e = exp(1)` (v0.8.0) and reuses its machinery almost verbatim — the only genuinely new input is
  **termwise domination**: for `q ∈ [0,1]` every power `qⁱ ≤ 1`, so each term `qⁱ/i! ≤ 1/i!`.
- **Rational powers from scratch** `qpow` (core has no `q^i`), with `qpow_le_one` (`q ∈ [0,1] ⇒ qⁱ ≤ 1`),
  `qpow_nonneg`, `qpow_den_pos`.
- **The domination bridge** `expTerm_le` (`qⁱ/i! ≤ 1/i!`) and `expdiff_dom` (the `exp(q)` partial-sum
  gaps are dominated termwise by those of `e`), giving the rigorous error bound `expdiff_bound`: for
  `a ≤ b`, `S_q(b) − S_q(a) ≤ 2/(a+1)!` — the *same* rational tail bound as `e`, no new tail analysis.
  The reindex `n ↦ S_q(n+1)` reuses `efct_reindex` verbatim, so `expSeq q` is regular
  (`expSeq_regular`) and `Rexp q` is a genuine constructive real.
- **Correctness anchors**: `Rexp_zero` (`exp 0 ≈ 1`), `Rexp_one_pos` (`exp 1 > 0`), and
  `Rexp_one_eq_e` (`exp 1 ≈ e` — the general construction specializes to v0.8.0's Euler number, a
  genuine regression anchor).
- `F1Square/Analysis/QOrder.lean` gains `Qeq_trans` (ℚ value-equality is an equivalence — the
  cross-multiplied identities are linear-combined and cancelled via `b.den > 0`), reusable infrastructure.
- `scripts/audit_axioms.lean` extended; the honesty gate stays green (every theorem
  `⊆ {propext, Classical.choice, Quot.sound}`; in fact choice-free; no `sorry`/`native_decide`/stray axiom).
  `F1Square.lean` gains a v0.9.0 `example`.

### Hardened (peer-review readiness)
- **Self-enforcing audit coverage.** `scripts/honesty_audit.sh` now mechanically checks that *every*
  non-private proof-layer `theorem`/`lemma` (248 of them) is `#print axioms`-audited in
  `audit_axioms.lean`, and fails CI otherwise. Previously the audit list was hand-maintained and ~30
  declarations (4 of them un-reachable leaf `rfl`-lemmas) were unlisted; all are now audited and the
  "every theorem is checked" invariant can no longer silently drift.
- **Honest prose pass.** Tightened documentation wording so sub-result status is unambiguous: T1 is
  scoped to "point-set level, surface unbuilt" (no longer "the 2D surface exists"); the §2.3
  shift-length finding leads with its *vacuity* (it equals RH, not a step toward it); the §9.1 lift is
  labelled as re-verification on genuine product surfaces `C × C` (not the unbuilt `𝕊`); the
  characteristic-1 status block distinguishes Lean kernel-checked (R1–R6, R9–R16) from
  numerically-checked (R7/R8). Stale `v0.0.1` publishing/citation instructions in `README.md` updated.

### Changed
- `docs/` roadmap re-paced within the transcendentals arc: v0.9.0 delivers `exp(q)` on `[0,1]`; the
  everywhere-defined `exp` on ℝ (via the halving/squaring identity `exp x = exp(x/2ᵏ)^{2ᵏ}`), `cos`/`sin`
  (alternating series with the even/odd sandwich remainder — genuinely new machinery), and `log`
  (positivity-as-data + the artanh series) follow in v0.10.0+.

### Note
- RH remains **open** (June 2026), and no construction of the 𝔽₁-square exists (fresh mid-2026
  synthesis: the Feb-2026 Connes–Consani *On the Jacobian of Spec ℤ̄* [arXiv:2602.15941] is a
  Jacobian/adele-class-space construction — a monoidal extension of the Picard group of the arithmetic
  curve — **not** the square and **not** an intrinsic intersection theory; nothing newer on that axis
  was found). The transcendentals make more of the analytic half *statable and checkable*, never
  proven — proving `λₙ ≥ 0 ∀n` / the Hodge index on 𝕊 is RH.

## [0.8.0] - 2026-06-06

### Added — the first transcendental: Euler's number `e` via the exponential series (pure Lean 4, no Mathlib, no `sorry`)
- `F1Square/Analysis/Exp.lean` — **`e = Σ 1/i!` as a constructive real**, with a rigorous rational
  error bound. Standing on completeness (a convergent series is a regular sequence of its partial
  sums); since the partial sums are *rational*, the reindexed partial-sum sequence is directly a
  regular sequence of rationals — a `Real`. Factorial is built from scratch (`fct`) because Lean core
  has no `Nat.factorial`.
- **The rigorous error bound** `ediff_bound`: for `a ≤ b`, the partial-sum gap `S(b) − S(a) ≤ 2/(a+1)!`,
  via the telescoping observation that `U(n) := S(n) + 2/(n+1)!` is **decreasing** (`eU_step`, since
  `2/(n+2)! ≤ 1/(n+1)!`) — a fully rational, explicitly computable tail bound. The reindex `n ↦ S(n+1)`
  makes `2/(n+2)! ≤ 1/(n+1)`, so `eSeq` is regular (`eSeq_regular`) and `e` is a genuine real.
- **`e_pos`**: `e` is positive (witnessed at index 0, where its approximant is `2`).
- `scripts/audit_axioms.lean` extended; the honesty gate stays green (every theorem
  `⊆ {propext, Classical.choice, Quot.sound}`; no `sorry`/`native_decide`/stray axiom).

### Changed
- `docs/` roadmap re-paced: the transcendentals are a multi-release **arc** — v0.8.0 delivers the
  exponential-series machinery and `e`; the general `exp(q)` (on `[0,1]`), `cos`/`sin` (alternating
  series), and `log` follow in v0.9.0+. `F1Square.lean` gains a v0.8.0 `example`.

### Note
- RH remains **open**, and no construction of the 𝔽₁-square exists (fresh mid-2026 synthesis: the
  Feb-2026 Connes–Consani *On the Jacobian of Spec ℤ̄* is an Arakelov–Picard reinterpretation, not the
  square; there is still no accepted 𝔽₁-scheme theory realizing `Spec ℤ ×_𝔽₁ Spec ℤ` with an intrinsic
  intersection theory). The transcendentals make more of the analytic half *statable and checkable*,
  never proven — proving `λₙ ≥ 0 ∀n` / the Hodge index on 𝕊 is RH.

## [0.7.0] - 2026-06-06

### Added — Cauchy completeness of ℝ (pure Lean 4, no Mathlib, no `sorry`, choice-free)
- `F1Square/Analysis/Complete.lean` — **every regular sequence of reals converges**. A sequence
  `X : ℕ → Real` is **regular** (`RReg`) when `X j` and `X k` agree within `1/(j+1) + 1/(k+1)` as reals
  (`|(X j)ₙ − (X k)ₙ| ≤ 1/(j+1) + 1/(k+1) + 2/(n+1)`, the canonical modulus). The limit `Rlim X` is
  **Bishop's diagonal** `n ↦ (X(4n+3))_{4n+3}` — the `4n+3` reindex reads each real far enough out that
  the diagonal is itself a regular sequence of rationals (`RlimSeq_regular`), so `Rlim X` is a genuine
  constructive real. **Convergence with a rate** `Rlim_tendsTo`: `X k → Rlim X` within `1/(k+1)` (gap
  `≤ 2/(k+1) + 2/(n+1)`). **Uniqueness** `RTendsTo_unique`: limits are unique up to `≈` (via the
  generalized Archimedean lemma `Qarch_gen` + the linear-bound criterion `Req_of_lin_bound`).
- Supporting ℚ lemmas: `Qfrac_le` / `Qcollapse_le` (collapse a scaled-denominator sum to a unit
  fraction) and `Qabs_Qsub_comm` (`|a−b| = |b−a|`).
- The construction is **choice-free**: because the regular-sequence data carries its own modulus, the
  diagonal needs no countable choice (the `#print axioms` audit shows no `Classical.choice` — only
  `propext`, `Quot.sound`). `scripts/audit_axioms.lean` extended; the honesty gate stays green.

### Changed
- `docs/` roadmap re-paced: the **transcendentals** (exp/log/cos via convergent series with rigorous
  rational error bounds) — which stand directly on this completeness brick (a power series is a regular
  sequence of its partial sums) — move to v0.8.0. `F1Square.lean` gains a v0.7.0 `example`.

### Note
- RH remains **open**, and no construction of the 𝔽₁-square exists (fresh mid-2026 synthesis: the
  Feb-2026 Connes–Consani *On the Jacobian of Spec ℤ̄* is an Arakelov–Picard reinterpretation, not the
  square; there is still no accepted 𝔽₁-scheme theory realizing `Spec ℤ ×_𝔽₁ Spec ℤ` with an intrinsic
  intersection theory). Completeness makes the analytic half *statable and checkable*, never proven —
  proving `λₙ ≥ 0 ∀n` / the Hodge index on 𝕊 is RH.

## [0.6.0] - 2026-06-06

### Added — ℝ and ℂ are commutative rings up to `≈`; ℝ multiplication well-defined on the setoid (pure Lean 4, no Mathlib, no `sorry`)
- `F1Square/Analysis/QOrder.lean` — the **generalized Archimedean lemma** `Qarch_gen`: if
  `p ≤ q + C/(m+1)` for every `m` (any fixed coefficient `C : ℕ`), then `p ≤ q`. Plus `Qscale_le`,
  the bound-fraction monotonicity `c ≤ d, j ≤ k ⟹ c/(k+1) ≤ d/(j+1)`.
- `F1Square/Analysis/Real.lean` — **the linear-bound criterion** `Req_of_lin_bound` (Lemma A): if
  `|xₙ − yₙ| ≤ C/(n+1)` for every `n` (any constant `C`), then `x ≈ y` — our packaging of the Bishop
  ε-shift transitivity argument into one reusable engine that converts every reindex-mismatch into a
  clean `≈`. Supporting product-gap engine: `Rmul_gap` (`|x_a y_a − x_b y_b| ≤ L(s+t)/(n+1)`),
  `Rgap_le`/`Rcross_le` (collapse same/`≈`-cross gaps to scale `1/(n+1)`), `canon_bound_mul`/`canon_bound_le`.
- `F1Square/Analysis/Real.lean` — **ℝ is a commutative ring up to `≈`**: `Rmul_congr` (multiplication
  is well-defined on the Bishop setoid — the v0.5.0-deferred congruence, now proved), `Rmul_assoc`
  (triple product, nested product-gaps), `Rmul_distrib`, `Rmul_one`, `Radd_assoc`, `Rmul_zero`,
  `Radd_zero`, `Rsub_zero`; plus `Rmul_neg_left/right`, `Rmul_sub_distrib(_right)`, `Rmul_distrib_right`
  and the pointwise re-association lemmas (`Rsub_Radd_Radd`, `Radd_swap`, `Rreassoc_sub`, `Rreassoc_add`).
- `F1Square/Analysis/Complex.lean` — **ℂ is a commutative ring up to `≈`**: `Cadd_assoc`, `Cmul_one`,
  `Cmul_distrib`, and `Cmul_assoc` (the bilinear expansion of `(a+bi)(c+di)`, reduced via the ℝ ring
  laws to pointwise additive re-associations). Together with v0.5.0's `Cadd_comm`/`Cadd_neg`/`Cmul_comm`,
  ℂ now satisfies all commutative-ring axioms up to `≈`.
- `scripts/audit_axioms.lean` extended to all new theorems; the honesty gate stays green
  (every theorem `⊆ {propext, Classical.choice, Quot.sound}`; no `sorry`/`native_decide`/stray axiom).

### Changed
- `docs/` roadmap re-paced: **completeness** (every regular sequence of reals converges) and the
  **transcendentals** (exp/cos via convergent series with rigorous error bounds) move to v0.7.0, now
  that ℝ/ℂ are verified commutative rings. `F1Square.lean` gains a v0.6.0 `example`.

### Note
- RH remains **open**, and no construction of the 𝔽₁-square exists (fresh mid-2026 synthesis: the
  Feb-2026 Connes–Consani *On the Jacobian of Spec ℤ̄* is an Arakelov–Picard reinterpretation of the
  adele class space, not the square; tropical Hodge-index theory is mature geometrically but unbridged
  to the arithmetic setting). v0.6.0 finishes the ℝ/ℂ algebraic substrate (commutative rings up to
  `≈`); it makes the analytic half *statable and checkable*, never proven — proving `λₙ ≥ 0 ∀n` / the
  Hodge index on 𝕊 is RH.

## [0.5.0] - 2026-06-06

### Added — ℝ's equality is an equivalence, ℝ multiplication, ℂ = ℝ×ℝ (pure Lean 4, no Mathlib, no `sorry`)
- `F1Square/Analysis/QOrder.lean` — the **Archimedean lemma** `Qarch` (if `p ≤ q + 6/(m+1)` for all
  `m`, then `p ≤ q`), the 3-point triangle inequality, ℚ order totality, and the **ℚ
  multiplication-order library**: `Qabs_mul` (|ab|=|a||b|), non-negative product monotonicity
  `Qmul_le_mul`, and the product-difference triangle `Qabs_mul_diff`
  (`|x_a y_a − x_b y_b| ≤ |x_a||y_a−y_b| + |y_b||x_a−x_b|`).
- `F1Square/Analysis/Real.lean` — **`≈` is now a full equivalence**: transitivity `Req_trans` via the
  Archimedean lemma (the `2/(n+1) + 6/(m+1)` four-triangle argument). **ℝ multiplication** `Rmul`:
  reindex both factors at `r(n) = 2K(n+1)−1` with `K` the canonical bound `|xₙ| ≤ |x₀|+2`
  (`canon_bound`), regularity proved (the `2K` reindexing cancels the bound, via `ring_uor`);
  commutativity `Rmul_comm`. Plus `Rsub` and the additive-group laws `Radd_comm`, `Radd_neg`.
- `F1Square/Analysis/Real.lean` — **operation-congruence over `≈`**: `Rneg_congr`, `Radd_congr`,
  `Rsub_congr` (the operations are well-defined on the Bishop setoid — the prerequisite for the ℂ ring
  laws).
- `F1Square/Analysis/Complex.lean` — **ℂ = ℝ×ℝ** with componentwise Bishop equality (an equivalence,
  `Ceq_refl/symm/trans`) and **all four operations**: `Cadd`, `Cneg`, `Cmul` (`(ac−bd, ad+bc)`), the
  constants `0, 1, i`, and the embedding ℝ ↪ ℂ; the additive-group laws (`Cadd_comm`, `Cadd_neg`) and
  **commutative multiplication** `Cmul_comm` (up to `≈`, via the operation-congruences + `Rmul_comm`).
- `scripts/audit_axioms.lean` extended to all new theorems; the honesty gate stays green.

### Changed
- `Qsub`/`Qabs`/`Qlt` and the denominator-positivity helpers now live in `Analysis/Rat.lean` (basic
  ℚ operations). `docs/` roadmap advances; `F1Square.lean` gains a v0.5.0 `example`.

### Note
- RH remains **open**. v0.5.0 completes the ℝ/ℂ field arithmetic, makes Bishop equality an
  equivalence, and gives ℂ a commutative multiplication up to `≈`. The remaining ℂ ring laws
  (associativity, distributivity) need `Rmul`-congruence and `Rmul`-associativity — a reindex-
  reconciliation theorem — which, with completeness and the transcendentals, is the v0.6.0
  continuation. The substrate makes the analytic half *statable and checkable*, never proven —
  proving `λₙ ≥ 0 ∀n` / the Hodge index on 𝕊 is RH.

## [0.4.0] - 2026-06-06

### Added — a from-scratch `ring` tactic; ℚ as an ordered field; ℝ as an ordered additive group (pure Lean 4, no Mathlib, no `sorry`)
- `F1Square/Analysis/RingTac.lean` — **`ring_uor`, a from-scratch commutative-ring decision
  procedure**, the capstone of the v0.3.0 normalizer. A real Lean tactic (core metaprogramming,
  `Lean.Elab.Tactic` — *not* Mathlib): it reifies an integer equality goal into the `PExpr` syntax,
  applies the soundness lemma `nf_eq`, and discharges the residual `norm lhs = norm rhs` by `decide`.
  Reification is fuel-bounded (no `partial def`); the tactic only *builds* a `nf_eq` proof, so every
  goal it closes is as axiom-clean as `nf_eq`. (`ring` is confirmed absent from core; `push_cast` and
  `omega` are core and are used for cast/linear steps.)
- `F1Square/Analysis/QOrder.lean` — **ℚ as a verified ordered field**: reflexivity, transitivity
  (`Qle_trans`), `Qeq → Qle`, additive monotonicity (`Qadd_le_add`), the absolute-value triangle
  inequality (`Qabs_add_le`), `|·|` respects value-equality (`Qabs_Qeq`), order transport along `≈`
  (`Qle_congr_left/right`), and the telescoping triangle `|(a+b)−(c+d)| ≤ |a−c|+|b−d|`
  (`Qabs_sub_add4`) — the exact bound real addition consumes. Built from the core ℤ order/`natAbs`
  lemmas and `ring_uor`.
- `F1Square/Analysis/Real.lean` — **ℝ arithmetic with full regularity proofs**: negation `Rneg`
  (an isometry) and the reindexed **Bishop addition** `Radd` (`(x⊕y)ₙ = x₍₂ₙ₊₁₎+y₍₂ₙ₊₁₎`, regular
  because `2·1/(2k+2) = 1/(k+1)`, proved via the telescoping triangle + monotonicity + `ring_uor`).
  The `Real` structure now carries `den_pos` (every term has a positive denominator). With
  denominator-positivity helpers added to `Analysis/Rat.lean`.
- `scripts/audit_axioms.lean` extended to all new theorems; the honesty gate stays green.

### Changed
- `Real` gains the `den_pos` field; `ofQ` now takes a positivity proof (`zero`/`one`/`half` supply it
  by `decide`). `Qsub`/`Qabs` moved from `Real.lean` to `Analysis/Rat.lean` (basic ℚ operations).
- `docs/`: the analysis-substrate roadmap advances (ℝ is now an ordered additive group with a
  from-scratch `ring`); ℝ multiplication, `≈`-transitivity (an Archimedean argument), ℂ = ℝ×ℝ, and
  the transcendentals are the v0.5.0 continuation. `F1Square.lean` gains a v0.4.0 `example`.

### Note
- RH remains **open**. v0.4.0 makes ℝ an ordered additive group and gives the project a genuine
  `ring`; it does not resolve λₙ / Weil-positivity / the crux. The substrate makes the analytic half
  *statable and checkable*, never proven — proving `λₙ ≥ 0 ∀n` / the Hodge index on 𝕊 is RH.

## [0.3.0] - 2026-06-06

### Added — the analysis substrate, brick two: a ℤ ring normalizer + constructive ℝ (pure Lean 4, no Mathlib, no `sorry`)
- `F1Square/Analysis/RingNF.lean` — a **reflective commutative-ring normalizer over ℤ**: polynomial
  expressions (`PExpr`) get a **canonical form** (a sorted, merged `(monomial, coefficient)` list —
  their content-address), with a single soundness theorem `norm_sound : pden ρ (norm e) = denote ρ e`
  and the decision lemma `nf_eq` (equal canonical forms ⇒ equal as ℤ-functions). This lifts the
  no-`ring` ceiling: general nonlinear identities — `(a+b)² = a²+2ab+b²`, `(a+b)(a−b) = a²−b²`,
  `(a+b+c)²`, commuted distributivity — are now genuine theorems for ALL integers, proved by `decide`
  on the finite normal form. Soundness is built from the core ℤ ring lemmas, never assumed.
- `F1Square/Analysis/Rat.lean` — the v0.2.0 ℚ brick's field laws are now **general** (all rationals,
  not just numerals): `add_comm`, `mul_comm`, `add_assoc`, `mul_assoc`, `mul_add` (distributivity),
  `mul_one`, `add_zero`, `add_neg` — each discharged by the ring normalizer after pushing the
  `Nat → Int` casts to the leaves. Dogfooding the v0.3.0 tool.
- `F1Square/Analysis/Real.lean` — **constructive ℝ** as **Bishop regular sequences** over the exact ℚ
  (`|xₘ − xₙ| ≤ 1/(m+1) + 1/(n+1)`): the `Real` type, the regularity predicate, the canonical
  embedding ℚ ↪ ℝ (proved regular and value-respecting, `const_regular` / `ofQ_respects`), the Bishop
  equality setoid (`Req_refl`, `Req_symm`), and the witnessed positivity predicate (`Pos`, `Pos_half`).
- `scripts/audit_axioms.lean` extended to all 29 new theorems; the honesty gate stays green.

### Changed
- `docs/`: the analysis-substrate roadmap advances one brick (ℚ → **ℤ ring normalizer + ℝ** →
  ℂ+transcendentals → ζ/λₙ); the v0.3.0 status is recorded. `F1Square.lean` gains a v0.3.0
  elaboration-checked `example`. Literature note refreshed (the Feb-2026 Connes–Consani *Jacobian of
  `Spec ℤ̄`*, arXiv:2602.15941, is Arakelov–Picard — it does **not** construct the square or prove
  Hodge positivity; RH remains open as of mid-2026).

### Note
- RH remains **open**. v0.3.0 builds the algebraic tool (the ring normalizer) and the ℝ foundation;
  ℝ arithmetic (`+`, `·`), `≈`-transitivity (a limiting argument), and completeness are the v0.4.0
  continuation. The substrate makes the analytic half *statable and checkable*, never proven —
  proving `λₙ ≥ 0 ∀n` / the Hodge index on 𝕊 is RH.

## [0.2.0] - 2026-06-06

### Added — finite tropical stack mechanized + first analysis brick (pure Lean 4, no Mathlib, no `sorry`)
- `F1Square/Tropical/Closure.lean` — tropical (max-plus) matrix closure: the canonical `W*` (matches
  the companion) and **R2** Kleene-star idempotence `W* ⊗ W* = W*`, by `decide`.
- `F1Square/Tropical/Spectrum.lean` — the content-address κ and the cycle-mean spectrum: **R3** κ
  permutation-invariance, **R4** the cycle spectrum, and the headline **R9/R10** κ⊥spectrum
  counterexample (same κ, different spectrum) with **R11** the κ-fiber.
- `F1Square/Tropical/Siblings.lean` — the boolean sibling carrier: **R14** κ permutation-invariance,
  **R15** the faceted `(κ_trop, κ_bool)` address, **R16** boolean-facet degeneracy on a
  strongly-connected graph.
- `F1Square/Tropical/Signature.lean` — tropical Hodge-index signatures: the §2.3 parallel pencil
  `Δ·Γ_n = 0` (`det((1,1),(1,1)) = 0`), the fan-vs-fiber correction (fan recession form degenerate,
  so `(1,ρ−1)` is the fiber form), and a Babaee–Huh counterexample (the signature is NOT automatic).
- `F1Square/Analysis/Rat.lean` — the first analysis brick: exact rationals ℚ from ℤ, the **UOR way**
  (canonical reduced form = content-address; decidable exact equality/order; idempotent `reduce`).
  The analysis-substrate roadmap (ℚ → constructive ℝ → ℂ+transcendentals → ζ/λₙ) is documented.
- `scripts/audit_axioms.lean` extended to all new theorems; the honesty gate stays green.

### Changed
- `docs/`: the finite R1–R16 stack is marked kernel-checked (was runtime-verified); the analysis
  roadmap and the v0.2.0 mechanization status are recorded. `F1Square.lean` gains a v0.2.0
  elaboration-checked `example`.

### Note
- RH remains **open**. v0.2.0 resolves the finite/decidable open questions and lays the ℚ brick; it
  does not resolve λₙ / Weil-positivity / the crux (those are RH). The analysis substrate makes them
  *statable and checkable*, not proven.

## [0.1.0] - 2026-06-06

### Added — the genuine-proof layer (real Lean 4 theorems, no Mathlib, no `sorry`)
- `F1Square/Mechanism.lean` — the function-field Hodge mechanism as the square-root-free integer
  Hasse condition (`hodgeType_iff : hodgeType q a ↔ a² ≤ 4q`) with the §9.1 flip cases at
  `q = 4, 9, 25`; tropical intersection-positivity `mult = mu·mv·|det| ≥ 0` and tropical Bézout (R13).
- `F1Square/Template.lean` — the product-of-curves intersection template (§2.2): pairing symmetry,
  the sourced numbers `E₁·E₂ = 1`, `E₃² = −2`, the ample class `H² = 2 > 0`, and genuine
  negative-definiteness on the primitive complement `H^⊥` (`diag(−2,−2)`, nondegenerate) — the §1.4
  Hodge-type `(1,2)` decomposition.
- `F1Square/CharOne.lean` — the characteristic-1 (max-plus) base: idempotency (R1), the semiring
  laws, and the reversal theorem (R12: cycle weight/length invariant under reversal).
- `F1Square/CycleCounts.lean` — the Bowen–Lanford trace identity (R6) `N_m = tr(Bᵐ)` for the example
  graph, `N₁…N₈ = 0,2,6,2,10,14,14,34`, kernel-checked by `decide` on exact integer `Bᵐ`.
- `F1Square/Bridge.lean` — the mechanism bridge (Hodge type ⟹ spectral bound) and the §2.3 control
  mechanized (a rank-1 cos/sin Gram is PSD for ANY spectrum, so its positivity is vacuous w.r.t. RH).
- `F1Square/Crux.lean` — the crux stated faithfully: `HodgeIndex` proved for the Template
  (`template_hodgeIndex`); `CruxFor 𝕊` left OPEN (not forbidden) for the unconstructed square.
- `scripts/honesty_audit.sh` + `scripts/audit_axioms.lean` — the mechanized-honesty gate:
  `#print axioms` over every proof-layer theorem must show only `{propext, Classical.choice,
  Quot.sound}` — no `sorry` (sorryAx), no `native_decide` (ofReduceBool), no stray axioms. Wired into CI.
- `F1Square.lean` now imports the proof layer and carries an elaboration-checked `example` tying the
  manifest's established status fields to the genuine theorems; the crux field stays `none`.

### Changed
- `docs/f1_square_intersection_theory.md` §2 — citation corrections from an independent full-text
  verification (2026-06-06): Pietromonaco (not "Bryan et al.") for 1905.07085; Sagnier (not
  Connes–Consani) for 1703.10521; Moscovici added to the prolate paper; 2310.15367 is a 2023
  "tropical fans" preprint; the Feb-2026 *Jacobian of `Spec ℤ̄`* (2602.15941) proves moduli, **not**
  positivity; the deferred Hermitian-Jacobi computation (critical path to T5) has not appeared.

### Note
- The Riemann Hypothesis remains **open**. The crux (the Hodge index theorem for the 𝔽₁ square) is
  proved nowhere; the honesty audit is a *verifier*, not a prohibition.

## [0.0.1] - 2026-06-06

Initial research base for the 𝔽₁-square / Riemann Hypothesis program.

### Added
- `F1Square.lean` — Lean 4 formalization of the target object
  `Spec ℤ ×_{𝔽₁} Spec ℤ` and its intersection theory, in the `UOR.Bridge.F1Square`
  namespace. Encodes each result's honest epistemic status: verified/classical results
  carry their established status (`universallyValid := some true`); the RH crux (the
  Hodge index theorem) is encoded as not-asserted (`universallyValid := none`) and is
  **never** asserted true. Includes the `F1SquareStatus` roll-up record.
- `docs/` — the three research documents that this formalization companions:
  - `f1_square_intersection_theory.md` — precise specification of the target object,
    the candidate-construction gap table, the named obstructions, and the T1–T5
    verification ladder.
  - `missing_object_over_Q.md` — the four equivalent solution routes and the
    `λₙ` / Hodge-index convergence map.
  - `characteristic_1_constructions.md` — the verified characteristic-1 / tropical
    stack (R1–R16) supplying the 1-dimensional arithmetic-site curve.
- Lake project: `lakefile.lean`, `lean-toolchain` (`leanprover/lean4:v4.16.0`), and
  `lake-manifest.json` pinning the `uor` dependency to UOR-Framework **v0.5.2**
  (`392c7f91e202cf7d119997ac14497444416ed2ce`) — the latest UOR-Framework release that
  ships the `lean4/` library. `lake build` compiles cleanly against this pin.
- Repository infrastructure: `README.md`, `CITATION.cff`, this changelog, `.gitignore`,
  and a GitHub Actions CI workflow that runs `lake build`.

### Notes
- The Riemann Hypothesis remains **open**. This release builds the research *base*, not a
  solution: the formalization compiles and states the construction problem precisely; it
  does not assert the crux.

[0.12.0]: https://github.com/afflom/F1/releases/tag/v0.12.0
[0.11.0]: https://github.com/afflom/F1/releases/tag/v0.11.0
[0.10.0]: https://github.com/afflom/F1/releases/tag/v0.10.0
[0.9.0]: https://github.com/afflom/F1/releases/tag/v0.9.0
[0.8.0]: https://github.com/afflom/F1/releases/tag/v0.8.0
[0.7.0]: https://github.com/afflom/F1/releases/tag/v0.7.0
[0.6.0]: https://github.com/afflom/F1/releases/tag/v0.6.0
[0.5.0]: https://github.com/afflom/F1/releases/tag/v0.5.0
[0.4.0]: https://github.com/afflom/F1/releases/tag/v0.4.0
[0.3.0]: https://github.com/afflom/F1/releases/tag/v0.3.0
[0.2.0]: https://github.com/afflom/F1/releases/tag/v0.2.0
[0.1.0]: https://github.com/afflom/F1/releases/tag/v0.1.0
[0.0.1]: https://github.com/afflom/F1/releases/tag/v0.0.1
