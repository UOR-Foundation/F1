/-
Mechanized-honesty audit (P4). `#print axioms` for every theorem in the genuine-proof layer.

A theorem proved with `sorry` shows `sorryAx`; one proved with `native_decide` shows
`Lean.ofReduceBool`; a stray `axiom` shows its own name. So this single pass is the authoritative
check that the proof layer is genuine. `scripts/honesty_audit.sh` runs this and fails CI if any
output mentions `sorryAx` / `ofReduceBool` / `trustCompiler`, or any axiom outside the minimal,
choice-free pair `{propext, Quot.sound}` (both forced by `omega`/`simp`/`Int` core internals).

This file is NOT part of the `F1Square` library target; it is run directly via `lake env lean`.
-/

import F1Square

open UOR.Bridge.F1Square

-- Mechanism (the function-field Hasse mechanism; tropical positivity).
#print axioms Mechanism.hodgeType_iff
#print axioms Mechanism.hasse_q25_a10
#print axioms Mechanism.hasse_q25_a12
#print axioms Mechanism.hasse_q4_a4
#print axioms Mechanism.hasse_q4_a5
#print axioms Mechanism.hasse_q9_a6
#print axioms Mechanism.hasse_q9_a7
#print axioms Mechanism.tropMult_nonneg
#print axioms Mechanism.bezout_line_line
#print axioms Mechanism.bezout_line_conic

-- Template (the product-of-curves Hodge-index template).
#print axioms Template.pair_symm
#print axioms Template.sq_nonneg
#print axioms Template.E1_dot_E2
#print axioms Template.E3_sq
#print axioms Template.H_sq
#print axioms Template.H_sq_pos
#print axioms Template.f1_perp
#print axioms Template.f2_perp
#print axioms Template.Hperp_gram_11
#print axioms Template.Hperp_gram_12
#print axioms Template.Hperp_gram_22
#print axioms Template.Hperp_value
#print axioms Template.Hperp_neg_semidef
#print axioms Template.int_sq_eq_zero
#print axioms Template.Hperp_definite

-- CharOne (the characteristic-1 / max-plus base; R1, R12).
#print axioms CharOne.tAdd_idem
#print axioms CharOne.tAdd_comm
#print axioms CharOne.tAdd_none_left
#print axioms CharOne.tAdd_none_right
#print axioms CharOne.tMul_comm
#print axioms CharOne.tMul_none_left
#print axioms CharOne.tMul_one_left
#print axioms CharOne.csum_append
#print axioms CharOne.csum_reverse
#print axioms CharOne.cycle_reversal_invariant

-- Bridge (the mechanism bridge; the §2.3 control).
#print axioms Bridge.hodge_implies_spectral_bound
#print axioms Bridge.control_psd

-- CycleCounts (R6, exact Bowen–Lanford trace identity).
#print axioms CycleCounts.N1
#print axioms CycleCounts.N2
#print axioms CycleCounts.N3
#print axioms CycleCounts.N4
#print axioms CycleCounts.N5
#print axioms CycleCounts.N6
#print axioms CycleCounts.N7
#print axioms CycleCounts.N8

-- Crux (the property; proved on the Template, OPEN on the square).
#print axioms Crux.template_hodgeIndex

-- v0.18.0 stage D — the Castelnuovo–Severi bridge at the lattice level (BridgeFF.lean):
-- Hodge-index negativity on the primitive {Δ,Γ}-span ⟺ the Hasse bound (= RH for the curve).
#print axioms BridgeFF.ffPair_symm
#print axioms BridgeFF.ff_gamma_bidegree
#print axioms BridgeFF.ff_trace_datum
#print axioms BridgeFF.primDG_perp_h
#print axioms BridgeFF.primDG_perp_v
#print axioms BridgeFF.primDG_sq
#print axioms BridgeFF.ff_hodge_iff_hasse
#print axioms BridgeFF.ff_hodge_iff_hodgeType
#print axioms BridgeFF.ff_hasse_q25_a10
#print axioms BridgeFF.ff_hasse_q25_a12_fails

-- v0.18.0 stage D — the Bombieri–Lagarias decomposition of λ₂ and the two-slice
-- realization of Li.LiDecomposition (Analysis/LiTwo.lean).
#print axioms Analysis.Rlambda2_decomposition
#print axioms Analysis.li_decomposition_two_realized
#print axioms Analysis.liTwo_evidence

-- v0.18.0 stage D — the spectral-square interface and THE BRIDGE: the geometric and
-- analytic faces of the crux are equivalent (Square/Spectral.lean). Crux stays OPEN.
#print axioms Square.Pos_Radd_self
#print axioms Square.Pos_of_Radd_self
#print axioms Square.Rnonneg_Radd_self
#print axioms Square.Rnonneg_of_Radd_self
#print axioms Square.spectral_bridge_nonneg
#print axioms Square.spectral_bridge_pos_slice
#print axioms Square.spectral_bridge_pos
#print axioms Square.crux_faces_equivalent
#print axioms Square.spectral_evidence_two
#print axioms Square.not_Pos_zero_double
#print axioms Square.spectralTwoSlice_not_crux
#print axioms Square.spectral_template_crux
#print axioms Square.spectral_iff_all_upTo

-- v0.18.0 stage D — the crux ATTEMPT under the gate (Square/Attempt.lean): the certified
-- part, the exact frontier, and the honest conclusion. Fields stay none; RH OPEN.
#print axioms Square.crux_attempt_frontier
#print axioms Square.crux_attempt_frontier_geometric
#print axioms Square.spectral_strict_upTo_two

-- v0.19.0 stage E — THE DOMINANCE FACE: the crux as a single uniform bound (oscillation
-- loses), equivalent to both prior faces (Square/Dominance.lean). Crux stays OPEN.
#print axioms Square.dominated_liPositive
#print axioms Square.liPositive_dominated
#print axioms Square.dominated_iff_liPositive
#print axioms Square.dominance_crux_equivalent
#print axioms Square.weilTrace_dominance
#print axioms Square.dominance_head_tail
#print axioms Square.crux_closure_route

-- v0.19.0 stage E — the genuine archimedean trend, all n (Analysis/ArchTrend.lean), and
-- the crux against the constructed trend (Square/Dominance.lean). Crux stays OPEN.
#print axioms Analysis.genuineArch_one
#print axioms Analysis.genuineArch_two
#print axioms Square.crux_vs_constructed_trend

-- v0.19.0 stage E — the genuine Li sequence in closed form, modulo the Stieltjes tail
-- (Analysis/GenuineLi.lean), and the closure route with the head DISCHARGED
-- (Square/Dominance.lean). Crux stays OPEN — the open data is the genuine η-tail + the bound.
#print axioms Analysis.genuineArith_one
#print axioms Analysis.genuineArith_two
#print axioms Analysis.genuineLam_one
#print axioms Analysis.genuineLam_two
#print axioms Analysis.genuineLam_head
#print axioms Analysis.weilTraceGenuine
#print axioms Analysis.etaTwoSlice
#print axioms Square.crux_genuine_form
#print axioms Square.crux_genuine_route

-- v0.19.0 the genuine-pairing arc, substrate P1 — |x| and max(0,·) on the constructive
-- reals: the tent-function calculus for the Weil functional's test class (Analysis/RMax.lean).
#print axioms Analysis.Qabs_abs_sub
#print axioms Analysis.Rabs
#print axioms Analysis.Rabs_congr
#print axioms Analysis.Rnonneg_Rabs
#print axioms Analysis.RmaxZero_congr
#print axioms Analysis.Rnonneg_RmaxZero
#print axioms Analysis.RmaxZero_of_nonpos
#print axioms Analysis.RmaxZero_of_nonneg

-- v0.19.0 the genuine-pairing arc, substrate P2a — finite sums of constructive reals
-- (Analysis/RSum.lean): the quadratic-form assembly substrate.
#print axioms Analysis.RsumN_congr
#print axioms Analysis.Rnonneg_RsumN
#print axioms Analysis.RsumN_le

-- v0.19.0 the genuine-pairing arc — THE WEIL FUNCTIONAL: the constructed finite-place
-- side and archimedean constant (Analysis/Weil.lean), the assembled pairing, the
-- pairing-induced spectral square, and the first computed pairing value
-- (Square/Pairing.lean). Crux stays OPEN; nothing asserts PSD for the genuine family.
#print axioms Analysis.weilPrimeTerm_past_support
#print axioms Analysis.weilPrimePart_stable
#print axioms Square.weilSpectralSquare
#print axioms Square.weil_psd_iff_hodge
#print axioms Square.weil_strict_iff_crux
#print axioms Square.weil_template_crux
#print axioms Square.demoWeilTest
#print axioms Square.weilPrime_demo
#print axioms Square.weilPrime_window
#print axioms Square.weilValue_window
#print axioms Square.weilPrimeTerm_one_carries_prime_two
#print axioms Square.prime_window_maximal

-- v0.19.0 the genuine-pairing arc — ψ(1/4), the archimedean kernel value at the window
-- center, as a constructive real with a certified lower bracket (Analysis/PsiQuarter.lean).
#print axioms Analysis.psiQuarterCore
#print axioms Analysis.psiQuarterCore_lower
#print axioms Analysis.psiQuarter
#print axioms Analysis.psiQuarter_lower
#print axioms Analysis.psiQuarterCore_upper
#print axioms Analysis.psiQuarter_upper
#print axioms Analysis.psiQuarterCore_upper_tight
#print axioms Analysis.psiQuarter_upper_tight

-- v0.19.0 the genuine-pairing arc — α(0) > 0: Burnol's window-center positivity
-- certificate, computed (Analysis/BurnolAlpha.lean). Evidence, not the universal; crux none.
#print axioms Analysis.sqrt2
#print axioms Analysis.one_le_sqrt2
#print axioms Analysis.burnolAlphaZero
#print axioms Analysis.burnolAlphaZero_pos

-- v0.19.0 the genuine-pairing arc — the τ-parameterized archimedean kernel Re ψ(1/4+iτ/2)
-- and its monotonicity; the honest record that the bare multiplier is INDEFINITE
-- (Analysis/DigammaWindow.lean). Pointwise α(τ)≥0 ∀τ is NOT a theorem; crux none.
#print axioms Analysis.windowKernel_den_pos
#print axioms Analysis.windowKernel_antitone
#print axioms Analysis.windowTerm_mono
#print axioms Analysis.windowTerm_zero
#print axioms Square.weilTraceTwo_not_crux
#print axioms Square.twoSlice_not_dominated
#print axioms Square.dominance_satisfiable

-- v0.19.0 stage E — the completed explicit-formula trace (zero side at the BL slices)
-- and the retirement of Li.LiAgreesWith at the built slices (Analysis/LiComplete.lean).
#print axioms Analysis.explicitFormulaTrace_one_realized
#print axioms Analysis.explicitFormulaTrace_two_realized
#print axioms Analysis.weilTraceTwo
#print axioms Analysis.weilTraceTwo_evidence
#print axioms Analysis.liAgreesWith_two_realized


-- v0.17.0 stage C — the 𝔽₁ curve at the monoid level (Square/Monoid.lean).
#print axioms Square.one_le_mul
#print axioms Square.mMul_assoc
#print axioms Square.mMul_comm
#print axioms Square.mOne_mul
#print axioms Square.mMul_one
#print axioms Square.cmon_mul_one
#print axioms Square.cmon_mul_mul_comm
#print axioms Square.f1_initial
#print axioms Square.f1_initial_unique
#print axioms Square.mScale_not_hom
#print axioms Square.mScale_comp

-- v0.17.0 stage C — the canonical square 𝕊 = F ⊗_𝔽₁ F with its universal property
-- (Square/Tensor.lean): coproduct laws, canonicality, non-collapse, strict 2-dimensionality.
#print axioms Square.copair_inl
#print axioms Square.copair_inr
#print axioms Square.sq_factor
#print axioms Square.copair_unique
#print axioms Square.square_base_cocone
#print axioms Square.inl_ne_inr
#print axioms Square.gen2_injective
#print axioms Square.gen2_codiag_collapse
#print axioms Square.codiag_not_injective
#print axioms Square.proj1_inl
#print axioms Square.proj2_inr
#print axioms Square.proj_faithful
#print axioms Square.sq_isCoproduct
#print axioms Square.coproduct_unique_upto_iso

-- v0.17.0 stage C — distinguished divisors of 𝕊 and their point-count intersections
-- (Square/Divisors.lean): the intrinsic input the lattice is derived from.
#print axioms Square.graph_one_diag
#print axioms Square.vFiber_inter_hFiber
#print axioms Square.vFiber_disjoint
#print axioms Square.hFiber_disjoint
#print axioms Square.diag_inter_vFiber
#print axioms Square.diag_inter_hFiber
#print axioms Square.graph_inter_vFiber
#print axioms Square.graph_inter_hFiber
#print axioms Square.diag_inter_graph_empty
#print axioms Square.graph_disjoint
#print axioms Square.graph_translate_diag
#print axioms Square.vFiber_translate
#print axioms Square.graph_zero_empty
#print axioms Square.graph_inter_hFiber_empty
#print axioms Square.vFiber_translate_unit
#print axioms Square.hFiber_translate

-- v0.17.0 stage C — the parallel pencil on canonical 𝕊 with shift lengths log n
-- (Square/Pencil.lean): the §2.3 finding as theorems on the constructed object.
#print axioms Square.logN_mul_general
#print axioms Square.logN_pow_general
#print axioms Square.pencil_shift
#print axioms Square.pencil_parallel
#print axioms Square.pencil_det_zero
#print axioms Square.pencil_separation
#print axioms Square.pencil_separation_vonMangoldt
#print axioms Square.pencil_separation_pow
#print axioms Square.pencil_separation_pow_vonMangoldt

-- v0.17.0 peer-review hardening — Euclid's lemma from scratch and Λ on ALL prime powers
-- (Analysis/Mangoldt.lean).
#print axioms Analysis.prime_dvd_mul
#print axioms Analysis.prime_dvd_pow
#print axioms Analysis.spf_prime_pow
#print axioms Analysis.isPrimePow_pow
#print axioms Analysis.vonMangoldt_prime_pow

-- v0.17.0 stage C — the intersection lattice of 𝕊, derived from point counts
-- (Square/Lattice.lean): the §2.2 declarative discipline mechanized; T3 intrinsic.
#print axioms Square.pair_rulings_derived
#print axioms Square.pair_v_self_derived
#print axioms Square.pair_h_self_derived
#print axioms Square.pair_diag_v_derived
#print axioms Square.pair_diag_h_derived
#print axioms Square.pair_diag_self_derived
#print axioms Square.pair_graph_v_derived
#print axioms Square.pair_graph_h_derived
#print axioms Square.pair_graph_self_derived
#print axioms Square.pair_diag_graph_derived
#print axioms Square.sqPair_add_left
#print axioms Square.sqPair_smul_left
#print axioms Square.e3_sq_forced
#print axioms Square.sqPair_eq_template
#print axioms Square.sqPair_symm
#print axioms Square.sq_boundary_checks
#print axioms Square.sq_adjunction_checks
#print axioms Square.sq_signature_diag
#print axioms Square.cls_generated
#print axioms Square.clsDiag_in_lattice
#print axioms Square.graph_class_unique
#print axioms Square.pencil_numerically_trivial

-- v0.17.0 stage C — polarized 𝕊: ample class, Hodge index of the derived lattice,
-- and the pencil-blindness boundary (Square/Polarized.lean). The crux stays OPEN.
#print axioms Square.clsAmple_eq
#print axioms Square.sq_ample_pos
#print axioms Square.sq_ample_meets
#print axioms Square.sq_hperp_span
#print axioms Square.sq_hperp_value
#print axioms Square.sq_hperp_neg_semidef
#print axioms Square.sq_hperp_definite
#print axioms Square.square_hodgeIndex
#print axioms Square.square_hodge_pencil_blind

-- v0.2.0 — Tropical closure / κ / spectrum (R2, R3, R4, R9, R10, R11).
#print axioms Tropical.star_matches
#print axioms Tropical.R2_kleene_idempotent
#print axioms Tropical.R3_kappa_perm_invariant
#print axioms Tropical.R4_cycle_spectrum
#print axioms Tropical.R9_same_kappa
#print axioms Tropical.R10_diff_spectrum
#print axioms Tropical.R11_kappa_fiber

-- Bowen–Lanford closed-walk trace identity (R6, new Tropical/WalkCounts.lean). N_m = tr(Bᵐ) for the
-- 0/1 adjacency B = support of W: N_1..N_8 = 0,2,6,2,10,14,14,34 (power sums of adjacency eigenvalues,
-- the counting companion of the tropical cycle spectrum R4). RH-independent embeddings-model realization
-- (no λ/zeros/StieltjesEta). Crux none.
#print axioms Tropical.adjOfW_eq
#print axioms Tropical.R6_closed_walk_counts

-- §8's four further constructions, completed in Lean (R10,R11 already in Spectrum; R12,R13 new
-- Tropical/FurtherConstructions.lean). R12 reversal symmetry spectrum(W)=spectrum(Wᵀ) (tropical
-- functional equation); R13 tropical intersection-positivity is free — mult=mᵤmᵥ|det(u,v)| is a Nat
-- (R13_intersection_nonneg) + tropical Bézout (R13_bezout: line∩line=1, line∩conic=2). The manifest
-- characteristic-1 shadow of the Hodge positivity the ℚ-object lacks; RH-independent. Crux none.
#print axioms Tropical.R12_reversal_symmetry
#print axioms Tropical.R13_intersection_nonneg
#print axioms Tropical.R13_bezout

-- Dynamical zeta / Euler product (R5, new Tropical/EulerProduct.lean). det(I−tB)=1−t²−2t³ (R5_det,
-- a 4×4 integer-polynomial determinant of B=adjOfW) and 1/det(I−tB)=1+t²+2t³+t⁴+4t⁵+5t⁶+6t⁷+13t⁸+…
-- (R5_euler_product: det·zeta ≡ 1 mod t⁹) — the Artin–Mazur/Bowen–Lanford rational dynamical zeta
-- factoring over the tropical primes (cycles), the characteristic-1 Euler-product SHADOW. RH-independent
-- (no λ/zeros/StieltjesEta). Crux none.
#print axioms Tropical.R5_det
#print axioms Tropical.R5_euler_product
-- entropy_pole_bracket (R8 fragment): the dynamical zeta's leading pole (topological-entropy base) is
-- the smallest positive root t*=1/ρ(B) of det(I−tB)=1−t²−2t³; sign change of the (cleared) determinant
-- between t=13/20 (226>0) and t=33/50 (−1324<0) brackets t*∈(0.65,0.66), h=log ρ(B)≈0.4196. RH-independent
-- (full π(L)~e^{hL}/L asymptotic NOT formalized). Crux none.
#print axioms Tropical.entropy_pole_bracket

-- v0.2.0 — sibling carriers (R14, R15, R16).
#print axioms Tropical.R14_kappaBool_perm_invariant
#print axioms Tropical.R15_faceted_address
#print axioms Tropical.R16_boolean_facet_degenerate

-- v0.2.0 — tropical Hodge-index signatures (§2.3, Babaee–Huh).
#print axioms Tropical.Signature.parallel_pencil
#print axioms Tropical.Signature.delta_gamma_zero
#print axioms Tropical.Signature.fan_degenerate
#print axioms Tropical.Signature.fan_kernel
#print axioms Tropical.Signature.fan_basis_nonpos
#print axioms Tropical.Signature.bh_two_positive_dirs

-- v0.2.0 — exact ℚ analysis brick.
#print axioms Analysis.Qeq_refl
#print axioms Analysis.reduce_6_8
#print axioms Analysis.reduce_idem
#print axioms Analysis.reduce_idem_neg
#print axioms Analysis.reduce_preserves_value
#print axioms Analysis.same_address_iff_eq
#print axioms Analysis.add_sample
#print axioms Analysis.mul_sample
#print axioms Analysis.Qle_sample

-- v0.3.0 — the ℤ ring normalizer (reflective canonical polynomial form) and its soundness.
#print axioms Analysis.RingNF.minsert_sound
#print axioms Analysis.RingNF.mmul_sound
#print axioms Analysis.RingNF.pinsert_sound
#print axioms Analysis.RingNF.padd_sound
#print axioms Analysis.RingNF.pscaleMono_sound
#print axioms Analysis.RingNF.pmul_sound
#print axioms Analysis.RingNF.pneg_sound
#print axioms Analysis.RingNF.norm_sound
#print axioms Analysis.RingNF.nf_eq
#print axioms Analysis.RingNF.sq_add
#print axioms Analysis.RingNF.mul_diff
#print axioms Analysis.RingNF.sq_add3
#print axioms Analysis.RingNF.distrib_comm

-- v0.3.0 — general ℚ field laws (via the normalizer).
#print axioms Analysis.add_comm
#print axioms Analysis.mul_comm
#print axioms Analysis.mul_assoc
#print axioms Analysis.add_assoc
#print axioms Analysis.mul_add
#print axioms Analysis.mul_one
#print axioms Analysis.add_zero
#print axioms Analysis.add_neg

-- v0.3.0 — constructive ℝ (Bishop regular sequences over ℚ).
#print axioms Analysis.Qsub_self_num
#print axioms Analysis.Qsub_swap_num
#print axioms Analysis.Qsub_swap_den
#print axioms Analysis.const_regular
#print axioms Analysis.Req_refl
#print axioms Analysis.Req_symm
#print axioms Analysis.ofQ_respects
#print axioms Analysis.Pos_half

-- v0.4.0 — the from-scratch `ring_uor` tactic (sample theorems it discharges, axiom-clean).
#print axioms Analysis.RingNF.ring_uor_sq
#print axioms Analysis.RingNF.ring_uor_cube
#print axioms Analysis.RingNF.ring_uor_telescope

-- v0.4.0 — ℚ as a verified ordered field.
#print axioms Analysis.Qle_refl
#print axioms Analysis.Qeq_le
#print axioms Analysis.Qle_trans
#print axioms Analysis.Qabs_Qeq
#print axioms Analysis.Qle_congr_left
#print axioms Analysis.Qle_congr_right
#print axioms Analysis.Qadd_le_add
#print axioms Analysis.Qabs_add_le
#print axioms Analysis.Qabs_sub_add4

-- v0.4.0 — denominator-positivity helpers.
#print axioms Analysis.add_den_pos
#print axioms Analysis.Qsub_den_pos
#print axioms Analysis.Qabs_den_pos

-- v0.4.0 — ℝ arithmetic (negation + Bishop addition, regularity proved).
#print axioms Analysis.Qbound_den_pos
#print axioms Analysis.Qabs_Qsub_neg
#print axioms Analysis.Rneg
#print axioms Analysis.Radd
#print axioms Analysis.Rneg_Rneg_seq

-- v0.5.0 — ℚ Archimedean + strict order (for ≈-transitivity).
#print axioms Analysis.Qle_or_Qlt
#print axioms Analysis.Qabs_sub_triangle
#print axioms Analysis.Qarch

-- v0.5.0 — ℚ multiplication and order (consumed by ℝ multiplication).
#print axioms Analysis.Qabs_mul
#print axioms Analysis.Qmul_le_mul_left
#print axioms Analysis.Qmul_le_mul_right
#print axioms Analysis.Qmul_le_mul
#print axioms Analysis.Qabs_mul_diff
#print axioms Analysis.Qabs_le_add
#print axioms Analysis.Qmul_den_pos
#print axioms Analysis.Qabs_num_nonneg

-- v0.5.0 — ℝ: ≈ is an equivalence; ℝ multiplication with regularity.
#print axioms Analysis.Req_of_seq_Qeq
#print axioms Analysis.Req_trans
#print axioms Analysis.Radd_comm
#print axioms Analysis.Radd_neg
#print axioms Analysis.canon_bound
#print axioms Analysis.Ridx_succ
#print axioms Analysis.Rmul
#print axioms Analysis.Rmul_comm

-- v0.5.0 — operation-congruence over ≈ (well-definedness on the setoid).
#print axioms Analysis.Rneg_congr
#print axioms Analysis.Radd_congr
#print axioms Analysis.Rsub_congr

-- v0.5.0 — ℂ = ℝ×ℝ with all four operations and commutative multiplication.
#print axioms Analysis.Ceq_refl
#print axioms Analysis.Ceq_symm
#print axioms Analysis.Ceq_trans
#print axioms Analysis.Cadd_comm
#print axioms Analysis.Cadd_neg
#print axioms Analysis.Cmul_re
#print axioms Analysis.Cmul_im
#print axioms Analysis.Cmul_comm

-- v0.6.0 — the well-definedness engine (generalized Archimedean lemma + linear-bound criterion).
#print axioms Analysis.Qscale_le
#print axioms Analysis.Qarch_gen
#print axioms Analysis.Ridx_ge
#print axioms Analysis.Qconst_le
#print axioms Analysis.Rgap_le
#print axioms Analysis.Rcross_le
#print axioms Analysis.Req_of_lin_bound
#print axioms Analysis.Rmul_gap
#print axioms Analysis.Qabs_two_diff_gen
#print axioms Analysis.canon_bound_mul
#print axioms Analysis.canon_bound_le

-- v0.6.0 — ℝ as a commutative ring up to ≈ (multiplication well-defined on the setoid).
#print axioms Analysis.Rmul_congr
#print axioms Analysis.Rmul_one
#print axioms Analysis.Radd_assoc
#print axioms Analysis.Rmul_distrib
#print axioms Analysis.Rmul_assoc
#print axioms Analysis.Rmul_zero
#print axioms Analysis.Radd_zero
#print axioms Analysis.Rsub_zero
#print axioms Analysis.Rmul_distrib_right
#print axioms Analysis.Rsub_Radd_Radd
#print axioms Analysis.Radd_swap
#print axioms Analysis.Rmul_neg_left
#print axioms Analysis.Rmul_neg_right
#print axioms Analysis.Rmul_sub_distrib
#print axioms Analysis.Rmul_sub_distrib_right
#print axioms Analysis.Rreassoc_sub
#print axioms Analysis.Rreassoc_add

-- v0.6.0 — ℂ as a commutative ring up to ≈.
#print axioms Analysis.Cadd_assoc
#print axioms Analysis.Cmul_one
#print axioms Analysis.Cmul_distrib
#print axioms Analysis.Cmul_assoc

-- v0.7.0 — Cauchy completeness of ℝ (every regular sequence of reals converges).
#print axioms Analysis.Qfrac_le
#print axioms Analysis.Qcollapse_le
#print axioms Analysis.RlimSeq_regular
#print axioms Analysis.Rlim
#print axioms Analysis.Rlim_seq
#print axioms Analysis.Rlim_tendsTo
#print axioms Analysis.Qabs_Qsub_comm
#print axioms Analysis.RTendsTo_unique

-- Tendsto ⟹ per-index real closeness + its Lipschitz image (new Analysis/RTendsToClose.lean): two general
-- Bishop-real convergence primitives. RTendsTo_imp_close: RTendsTo X L gives |X_k − L| ≤ 2/(k+1) as a real
-- (tendsto bound at doubled index 2n+1, then 2/(2n+2) ≤ 2/(n+1)). Rlip_close: a K-Lipschitz g sends a
-- convergent xs to |g(xs_k) − g(L)| ≤ K·(2/(k+1)) (compose hlip + RTendsTo_imp_close + Rmul_ofQ_ofQ). The
-- non-acceleration half of the Lipschitz limit-preservation the real-scale covariance capstone needs;
-- the reindex half (closeness ⟹ RTendsTo at canonical rate) is unbuilt. No scale continuity, no covariance,
-- no factorization, no positivity, no crux.
#print axioms Analysis.RTendsTo_imp_close
#print axioms Analysis.Rlip_close
#print axioms Analysis.Rlim_congr
#print axioms Analysis.Rlim_neg
#print axioms Analysis.Rinv_congr
#print axioms Analysis.genSum_congr
#print axioms Analysis.CnormSq_CdigammaArg_conj
#print axioms Analysis.CdigammaTerm_re_conj
#print axioms Analysis.CDigammaCore_re_conj
#print axioms Analysis.CDigamma_re_conj
#print axioms Analysis.genSum_neg
#print axioms Analysis.RReg_neg
#print axioms Analysis.CdigammaTerm_im_conj
#print axioms Analysis.CDigammaCore_im_conj
#print axioms Analysis.CDigamma_im_conj
#print axioms Analysis.CDigamma_conj
#print axioms Analysis.Cexp_conj
#print axioms Analysis.CnormSq_conj
#print axioms Analysis.Cinv_conj
#print axioms Analysis.CpiPow_conj
#print axioms Analysis.CxiPoly_conj
#print axioms Analysis.Cxi_conj
#print axioms Analysis.Rlim_zero
#print axioms Analysis.Rlim_add
#print axioms Analysis.Rlim_add_of_approx
#print axioms Analysis.Rlim_ofQ_mul
#print axioms Analysis.Rlim_ofQ_mul_of_approx

-- The real power is base-Lipschitz on a bounded domain (new Analysis/RpowBaseLip.lean): |xᵏ⁺¹ − yᵏ⁺¹| ≤
-- (k+1)·Bᵏ·|x−y| for |x|,|y| ≤ B (rational B≥0). Telescoping induction: abs-bound |xᵏ|≤Bᵏ (Rpow_abs_le,
-- private) + mixed-product identity x·Px−y·Py = x·(Px−Py)+(x−y)·Py (mixed_id, private) give the step
-- |xᵏ⁺²−yᵏ⁺²| ≤ B·((k+1)·Bᵏ·|x−y|) + |x−y|·Bᵏ⁺¹ = (k+2)·Bᵏ⁺¹·|x−y|. The polynomial-factor continuity
-- (cⁿ⁺¹ vs q_kⁿ⁺¹, B=S) the real-scale covariance capstone consumes alongside mellinHat_scale_split.
-- General Bishop-real primitive; no covariance, no positivity, no crux.
#print axioms Analysis.Rpow_base_lip

-- The Archimedean squeeze for Bishop reals (new Analysis/RealNullFamily.lean): if |x−y| ≤ C/(k+1) for
-- EVERY k (as reals), then x ≈ y (Req_of_real_null_family). Fix index n: the family gives
-- |(x−y).seq n| ≤ C/(k+1) + 2/(n+1) ∀k, so Qarch_gen kills the C/(k+1) term to leave ≤ 2/(n+1), and
-- Req_of_lin_bound turns that into x−y ≈ 0. The density-argument closer: a quantity within an
-- arbitrarily small rational gap of a target at every resolution equals it. The real-scale covariance
-- capstone's final step (F continuous + F const on rationals ⟹ F(c) = mellinHat φ). General Bishop-real
-- lemma; no covariance, no positivity, no crux.
#print axioms Analysis.Req_of_real_null_family
-- genSum of embedded rationals collapses to one embedded rational (new Analysis/GenSumOfQ.lean):
-- genSum (fun i => ofQ (g i)) N ≈ ofQ (qGenSum g N), qGenSum the rational partial sum mirroring
-- genSum term-for-term. Exposes the Mellin scale-continuity "head" Σ_{m<N} φ.L·(m+2)·(powWinTest m n).M
-- as a concrete rational H_N, the key that lets a rational index schedule drive the covariance
-- continuity gap to 0 (discharging hbound). Substrate finite-sum identity; no analysis, no crux.
#print axioms Analysis.genSum_ofQ
#print axioms Analysis.qGenSum_den
-- Rate-arithmetic core for the covariance null family (new Analysis/CovRateQ.lean): two elementary
-- rational inequalities. Qmul_recip_le — a nonneg rational a scaled by 1/(idx+1) is ≤ 1/D once
-- idx clears a·D (a.num·D < idx+1 ⟹ a/(idx+1) ≤ 1/D). Qmul_four_le — a nonneg P times the fixed
-- 4/(k+1) weight is ≤ ⌈4P⌉/(k+1). Together they bound the covComb continuity gap by C₀/(k+1) (the
-- null-family shape the Archimedean squeeze needs to discharge hbound). Rational inequalities; no
-- reals, no analysis, no crux.
#print axioms Analysis.Qmul_recip_le
#print axioms Analysis.Qmul_four_le
#print axioms Analysis.genSum_const_zero
#print axioms Analysis.CdigammaTerm_one_eq_zero
#print axioms Analysis.CDigammaCore_one_eq_zero
#print axioms Analysis.CDigamma_one

-- v0.8.0 — the first transcendental: Euler's number e via the exponential series.
#print axioms Analysis.fct_pos
#print axioms Analysis.self_le_fct
#print axioms Analysis.two_mul_fct_le
#print axioms Analysis.eSum_den_pos
#print axioms Analysis.eSum_le
#print axioms Analysis.efac_step
#print axioms Analysis.eU_step
#print axioms Analysis.eU_le
#print axioms Analysis.ediff_bound
#print axioms Analysis.eabs_bound
#print axioms Analysis.efct_reindex
#print axioms Analysis.eSeq_regular
#print axioms Analysis.e
#print axioms Analysis.e_pos

-- v0.9.0 — the general exponential exp(q) on the rational interval [0,1].
#print axioms Analysis.qpow_den_pos
#print axioms Analysis.qpow_nonneg
#print axioms Analysis.qpow_le_one
#print axioms Analysis.expTerm_le
#print axioms Analysis.expSum_den_pos
#print axioms Analysis.expSum_le
#print axioms Analysis.Qsub_add_right
#print axioms Analysis.expdiff_dom
#print axioms Analysis.expdiff_bound
#print axioms Analysis.expabs_bound
#print axioms Analysis.expSeq_regular
#print axioms Analysis.Rexp
#print axioms Analysis.Qeq_trans
#print axioms Analysis.expSum_zero_eq
#print axioms Analysis.Rexp_zero
#print axioms Analysis.Rexp_one_pos
#print axioms Analysis.Qadd_congr
#print axioms Analysis.qpow_one_eq
#print axioms Analysis.expSum_one_eq
#print axioms Analysis.Rexp_one_eq_e

-- Coverage completion: leaf and helper lemmas that are transitively reached by the audited
-- theorems above, audited here EXPLICITLY so `honesty_audit.sh`'s coverage check can mechanically
-- enforce that EVERY non-private proof-layer theorem/lemma is `#print axioms`-checked (no drift).
#print axioms Analysis.RingNF.mul4
#print axioms Analysis.I_im
#print axioms Analysis.ofReal_im
#print axioms Analysis.Qeq_symm
#print axioms Analysis.neg_den_pos
#print axioms Analysis.fct_succ
#print axioms Analysis.eSum_step
#print axioms Analysis.eU_den_pos
#print axioms Analysis.e_seq
#print axioms Analysis.one_seq
#print axioms Analysis.zero_seq
#print axioms Analysis.Ridx_comm
#print axioms Analysis.RmulK_comm
#print axioms Analysis.RmulK_pos
#print axioms Analysis.xBound_pos
#print axioms Analysis.Qabs_le_of_nonneg
#print axioms Analysis.Qsub_le_sub
#print axioms Analysis.Qsub_add_cancel
#print axioms Analysis.Qle_self_add
#print axioms Analysis.Qle_add_self
#print axioms Analysis.qpow_succ
#print axioms Analysis.qpow_zero_succ_num
#print axioms Analysis.expSum_step
#print axioms Analysis.expTerm_den_pos
#print axioms Analysis.expTerm_num_nonneg
#print axioms Analysis.expTerm_one_eq
#print axioms Analysis.expTerm_zero_succ_num
#print axioms Analysis.Qeq_add_zero_num
#print axioms Analysis.Qle_Qabs_Qsub_of_Qeq
#print axioms Analysis.Rexp_seq

-- v0.11.0 — the order ≤ on ℝ (foundation for the transcendentals).
#print axioms Analysis.Qle_self_Qabs
#print axioms Analysis.Qabs_le_of_both
#print axioms Analysis.Qle_add_of_Qabs_sub
#print axioms Analysis.Qsub_le_of_le_add
#print axioms Analysis.Rnonneg_zero
#print axioms Analysis.Rnonneg_one
#print axioms Analysis.Rnonneg_Radd
#print axioms Analysis.Rle_refl
#print axioms Analysis.Rle_of_Req
#print axioms Analysis.Rle_antisymm
#print axioms Analysis.Rle_trans
#print axioms Analysis.Rle_zero_of_Rnonneg

-- v0.12.0 (in progress) — the multiplicative substrate: real powers + the reciprocal.
#print axioms Analysis.Rpow_zero
#print axioms Analysis.Rpow_succ
#print axioms Analysis.Rpow_one
#print axioms Analysis.Rpow_congr
#print axioms Analysis.Qmul_congr
#print axioms Analysis.Qinv_den_pos
#print axioms Analysis.Qinv_num_pos
#print axioms Analysis.Qmul_Qinv
#print axioms Analysis.Qinv_antitone
#print axioms Analysis.Qinv_sub_eq
#print axioms Analysis.Rdelta_num_pos
#print axioms Analysis.Rdelta_den_pos
#print axioms Analysis.RL_num_pos
#print axioms Analysis.RL_den_pos
#print axioms Analysis.Rinv_lb
#print axioms Analysis.Qabs_Qinv
#print axioms Analysis.Rinv_num_pos
#print axioms Analysis.RinvR_ge
#print axioms Analysis.Rinv_perterm
#print axioms Analysis.Qmul_add_right
#print axioms Analysis.Qabs_Qsub_swap
#print axioms Analysis.RinvSeq_regular
#print axioms Analysis.Rinv
#print axioms Analysis.qpow_abs
#print axioms Analysis.qpow_base_mono
#print axioms Analysis.expSumM_den_pos
#print axioms Analysis.expSumM_step
#print axioms Analysis.expSumM_le
#print axioms Analysis.expM_step_le
#print axioms Analysis.expM_U_den_pos
#print axioms Analysis.expM_U_step
#print axioms Analysis.expM_U_le
#print axioms Analysis.expM_diff_bound
#print axioms Analysis.qpow_nat_base
#print axioms Analysis.expTerm_abs_le_M
#print axioms Analysis.expSum_abs_diff_le_M
#print axioms Analysis.expSum_trunc_bound
#print axioms Analysis.qpow_abs_le
#print axioms Analysis.qpow_diff_bound
#print axioms Analysis.expTerm_diff_bound
#print axioms Analysis.LipS_den_pos
#print axioms Analysis.expSum_Lip_le
#print axioms Analysis.Pbound_closed
#print axioms Analysis.expSumM_le_U
#print axioms Analysis.LipS_shift
#print axioms Analysis.LipS_le_U
#print axioms Analysis.two_pow_ge
#print axioms Analysis.fct_ge_geom
#print axioms Analysis.trunc_reindex
#print axioms Analysis.expSumM_num_nonneg
#print axioms Analysis.expM_U_num_nonneg
#print axioms Analysis.Qle_toNat
#print axioms Analysis.RexpReal_diag_le
#print axioms Analysis.RexpReal_regular
#print axioms Analysis.RexpReal
#print axioms Analysis.Qabs_neg
#print axioms Analysis.fct_mono
#print axioms Analysis.qsq_abs_le
#print axioms Analysis.altTerm_den_pos
#print axioms Analysis.altSum_den_pos
#print axioms Analysis.altTerm_abs_le
#print axioms Analysis.altSum_abs_diff_le
#print axioms Analysis.altSum_trunc_bound
#print axioms Analysis.altTerm_diff_bound
#print axioms Analysis.altSum_Lip_le
#print axioms Analysis.qsq_diff_le
#print axioms Analysis.RaltReal_diag_le
#print axioms Analysis.RaltReal_regular
#print axioms Analysis.RaltReal
#print axioms Analysis.Rcos
#print axioms Analysis.Rsin
#print axioms Analysis.geoSum_den_pos
#print axioms Analysis.geoU_eq
#print axioms Analysis.geo_diff_eq
#print axioms Analysis.Qsub_le_self
#print axioms Analysis.geo_diff_bound
#print axioms Analysis.artTerm_den_pos
#print axioms Analysis.artSum_den_pos
#print axioms Analysis.artTerm_abs_le
#print axioms Analysis.artSum_abs_diff_le
#print axioms Analysis.artSum_trunc
#print axioms Analysis.qpow_abs_le_rat
#print axioms Analysis.Pcoef_den_pos
#print axioms Analysis.Pcoef_num_nonneg
#print axioms Analysis.qpow_diff_bound_rat
#print axioms Analysis.geoEvenSum_den_pos
#print axioms Analysis.geoEven_eq
#print axioms Analysis.geoEven_bound
#print axioms Analysis.Pcoef_closed
#print axioms Analysis.artTerm_diff_bound
#print axioms Analysis.artSum_Lip_le
#print axioms Analysis.qpow_half_value
#print axioms Analysis.qpow_half_le
#print axioms Analysis.qpow_geom_bound
#print axioms Analysis.Qmul_le_cancel_right
#print axioms Analysis.Qone_mul
#print axioms Analysis.Qmul_swap_right
#print axioms Analysis.artanh_reindex
#print axioms Analysis.Rartanh_diag_le
#print axioms Analysis.Rartanh_regular
#print axioms Analysis.Rartanh
#print axioms Analysis.Qmul_rearrange4
#print axioms Analysis.Qmul_rearrange4b
#print axioms Analysis.Qmul_sub_right
#print axioms Analysis.Qneg_congr
#print axioms Analysis.Qsub_congr
#print axioms Analysis.Qinv_mul
#print axioms Analysis.tmap_ring
#print axioms Analysis.tmap_diff_cleared
#print axioms Analysis.Qabs_of_nonneg
#print axioms Analysis.tmap_lipschitz
#print axioms Analysis.tmap_cross_le
#print axioms Analysis.tmap_cross_ge
#print axioms Analysis.Qmul_neg_left
#print axioms Analysis.tmap_abs_le
#print axioms Analysis.Rlog_regular
#print axioms Analysis.tmap_M_eq
#print axioms Analysis.Rlog
#print axioms Analysis.Rlog_two_ok
#print axioms Analysis.Qle_add_right_nonneg
#print axioms Analysis.Qle_add_left_nonneg
#print axioms Analysis.Qbound_anti
#print axioms Analysis.reindex_regular
#print axioms Analysis.RlogPosR_tail
#print axioms Analysis.RlogPosR_self
#print axioms Analysis.Rlog_ub
#print axioms Analysis.RlogPos
#print axioms Analysis.qpow_one
#print axioms Analysis.arctanTerm_den_pos
#print axioms Analysis.arctanSum_den_pos
#print axioms Analysis.arctanTerm_abs_le
#print axioms Analysis.arctanSum_abs_diff_le
#print axioms Analysis.arctanSum_trunc
#print axioms Analysis.Rarctan_diag_le
#print axioms Analysis.Rarctan_regular
#print axioms Analysis.Rarctan
-- v0.22.0 Track 1 brick 1: arctan at a general REAL argument (Analysis/RArctan.lean) — the
-- forced-first prerequisite for complex Clog / Γ(s/2), mirroring real-argument Rartanh.
#print axioms Analysis.arctanTerm_diff_bound
#print axioms Analysis.arctanSum_Lip_le
#print axioms Analysis.RarctanR_diag_le
#print axioms Analysis.RarctanR_regular
#print axioms Analysis.arctanTerm_zero_num
#print axioms Analysis.arctanTerm_zero
#print axioms Analysis.arctanSum_zero_num
#print axioms Analysis.arctanSum_zero
#print axioms Analysis.RarctanR_zero
#print axioms Analysis.qpow_succ_num_eq_zero
#print axioms Analysis.arctanTerm_num_eq_zero
#print axioms Analysis.arctanSum_num_eq_zero
#print axioms Analysis.RarctanR_of_num_zero
-- v0.22.0 Track 1: arctan continuity (Analysis/RArctanCongr.lean) — lifts rational identities to real.
#print axioms Analysis.RarctanR_congr
#print axioms Analysis.Req_add_of_exp_values
-- v0.22.0 Track 1: rational artanh addition law (Analysis/ArtanhAdd.lean) — heart of log-multiplicativity.
#print axioms Analysis.Rnonneg_TwoArtanhConst
#print axioms Analysis.Rexp_twoArtanh_general
#print axioms Analysis.TwoArtanh_add_rat
#print axioms Analysis.wval_num
#print axioms Analysis.wval_den
#print axioms Analysis.wval_den_pos
#print axioms Analysis.wval_num_nonneg
#print axioms Analysis.wval_lt
#print axioms Analysis.wval_hg
#print axioms Analysis.TwoArtanh_add_wval
#print axioms Analysis.wval_argdiff1_cleared
#print axioms Analysis.wval_argdiff2_cleared
#print axioms Analysis.wvalR_num
#print axioms Analysis.wvalR_den
#print axioms Analysis.wvalR_den_pos
#print axioms Analysis.wvalR_argdiff1
#print axioms Analysis.wvalR_argdiff2
#print axioms Analysis.wval_halfbound
#print axioms Analysis.wval_csq_le
#print axioms Analysis.wval_lip1
#print axioms Analysis.wvalR_comm
#print axioms Analysis.wval_lip2
#print axioms Analysis.wvalR_rel
#print axioms Analysis.tmap_mul_wvalR
#print axioms Analysis.wval_inner_pos
#print axioms Analysis.tmul_wvalReal_via
#print axioms Analysis.Rexp_twoArtanh_general_rho
#print axioms Analysis.TwoArtanh_add_wval_rho
#print axioms Analysis.artSum_wval_argdiff
#print axioms Analysis.RartanhConst_add_wval_rho
#print axioms Analysis.wval_eq_wvalR
#print axioms Analysis.Rartanh_add_real_via
#print axioms Analysis.Rlog_mul_algebra
#print axioms Analysis.Rlog_mul_via
#print axioms Analysis.wvalR_tmap_bound
#print axioms Analysis.tmap_nonneg_lt_one
#print axioms Analysis.wvalR_tmap_seq_bound
#print axioms Analysis.Rlog_mul
#print axioms Analysis.vval_num
#print axioms Analysis.vval_den
#print axioms Analysis.vval_den_pos
#print axioms Analysis.vval_argdiff1_cleared
#print axioms Analysis.vval_argdiff2_cleared
#print axioms Analysis.vval_lip1_den
#print axioms Analysis.vval_argdiff1
#print axioms Analysis.vval_argdiff2
#print axioms Analysis.vval_halfbound
#print axioms Analysis.vval_csq_le
#print axioms Analysis.vval_comm
#print axioms Analysis.vval_inner_pos
#print axioms Analysis.vval_lip1
#print axioms Analysis.vval_lip2
#print axioms Analysis.vvalReal
-- v0.22.0 Track 1: the formal arctan ODE A′=1/(1+t²) (Analysis/ArctanODE.lean).
#print axioms Analysis.arctanCoeff_den_pos
#print axioms Analysis.geomAlt_den_pos
#print axioms Analysis.arctan_fderiv
#print axioms Analysis.geomAlt_recurrence
#print axioms Analysis.geomAlt_zero
#print axioms Analysis.geomAlt_one
#print axioms Analysis.sinCoeff_den_pos
#print axioms Analysis.cosCoeff_den_pos
#print axioms Analysis.sin_fderiv
#print axioms Analysis.cos_fderiv
#print axioms Analysis.Qadd_neg_distrib
#print axioms Analysis.Fsum_neg
#print axioms Analysis.fmul_neg_left
#print axioms Analysis.fcomp_neg_left
#print axioms Analysis.arctanCoeff_zero
#print axioms Analysis.sinComp_deriv
#print axioms Analysis.cosComp_deriv
#print axioms Analysis.Xident_den_pos
#print axioms Analysis.fmul_Xident_zero
#print axioms Analysis.fmul_Xident
#print axioms Analysis.onePlusSq_den_pos
#print axioms Analysis.sq2_den_pos
#print axioms Analysis.fmul_fone_left
#print axioms Analysis.fmul_sq2
#print axioms Analysis.onePlusSq_decomp
#print axioms Analysis.fmul_onePlusSq
#print axioms Analysis.fmul_onePlusSq_zero
#print axioms Analysis.fmul_onePlusSq_one
#print axioms Analysis.Qmul_pos_strip
#print axioms Analysis.Qmul_const_zero
#print axioms Analysis.Qadd_right_zero_cancel
#print axioms Analysis.fderiv_strip
#print axioms Analysis.ode_unique
#print axioms Analysis.fderiv_sub
#print axioms Analysis.fmul_subR
#print axioms Analysis.Qalg1
#print axioms Analysis.Xident_fderiv
#print axioms Analysis.fmul_neg_right
#print axioms Analysis.X_sq_eq_sq2
#print axioms Analysis.onePlusSq_geomAlt
#print axioms Analysis.absorb_onePlusSq_geomAlt
#print axioms Analysis.Gseq_fderivT
#print axioms Analysis.Gseq_den_pos
#print axioms Analysis.Gseq_zero
#print axioms Analysis.Gseq_ode
#print axioms Analysis.sin_arctan_eq
#print axioms Analysis.peval_sin_arctan_eq
#print axioms Analysis.peval_sinComp_swap
#print axioms Analysis.peval_cosComp_swap
#print axioms Analysis.qpow_neg_one_abs
#print axioms Analysis.arctanCoeff_term_odd
#print axioms Analysis.arctanCoeff_term_even
#print axioms Analysis.peval_arctanCoeff_eq_arctanSum
#print axioms Analysis.DN_sin_eq
#print axioms Analysis.e_le_T_arctan
#print axioms Analysis.DN_sin_abs_le
#print axioms Analysis.fpow_fabs_arctan_bound
#print axioms Analysis.fpow_arctan_term_bound
#print axioms Analysis.peval_arctan_pow_gap
#print axioms Analysis.peval_arctan_pow_cauchy
#print axioms Analysis.Qabs_arctan_C_le
#print axioms Analysis.corner_inner_eq_arctan
#print axioms Analysis.corner_term_le_arctan
#print axioms Analysis.corner_bound_arctan
#print axioms Analysis.corner_sum_bound_arctan
#print axioms Analysis.corner_sum_closed_arctan
#print axioms Analysis.DN_sin_closed
#print axioms Analysis.cosCoeff_term_even
#print axioms Analysis.cosCoeff_term_odd
#print axioms Analysis.peval_cosCoeff_eq_altSum
#print axioms Analysis.Qmul_rearr_sin
#print axioms Analysis.sinCoeff_term_odd
#print axioms Analysis.sinCoeff_term_even
#print axioms Analysis.peval_sinCoeff_eq
#print axioms Analysis.DN_cos_eq
#print axioms Analysis.DN_cos_abs_le
#print axioms Analysis.DN_cos_closed
#print axioms Analysis.Qrearr_AABP
#print axioms Analysis.DN_arctan_decay
#print axioms Analysis.DN_sin_recip
#print axioms Analysis.DN_cos_recip
#print axioms Analysis.peval_fmul_Xident_shift
#print axioms Analysis.peval_sin_arctan_shift
#print axioms Analysis.Rcos_seq_eq_peval
#print axioms Analysis.RsinAux_seq_eq_altSum
#print axioms Analysis.RsinAux_seq_eq_peval
#print axioms Analysis.peval_arg_congr
#print axioms Analysis.peval_arctanCoeff_even
#print axioms Analysis.arctanSum_abs_le_one
#print axioms Analysis.LipS_num_nonneg
#print axioms Analysis.peval_cosCoeff_Lip
#print axioms Analysis.geoSum_mono
#print axioms Analysis.geoSum_diff_recip
#print axioms Analysis.peval_cosCoeff_arctan_argdiff
#print axioms Analysis.peval_cosCoeff_arctan_argdiff_recip
#print axioms Analysis.cos_nested_general
#print axioms Analysis.Rcos_arctan_nested
#print axioms Analysis.altSum_abs_le
#print axioms Analysis.altSum_arctan_abs_le_U
#print axioms Analysis.altSum_argdiff_recip
#print axioms Analysis.Qabs_mul_sub_le
#print axioms Analysis.peval_sinCoeff_arctan_argdiff_recip
#print axioms Analysis.sin_nested_general
#print axioms Analysis.Rsin_arctan_nested
#print axioms Analysis.Rsin_arctan_value_eq
#print axioms Analysis.Rcos_arctan_sq
#print axioms Analysis.Rcos_arctan_inv
#print axioms Analysis.Rtan_arctan_eq
#print axioms Analysis.Rmul_left_comm_loc
#print axioms Analysis.Rone_mul_loc
#print axioms Analysis.Rmul_pair_regroup
#print axioms Analysis.Rsin_add_of_tan
#print axioms Analysis.Rcos_add_of_tan
#print axioms Analysis.vval_rel_poly
#print axioms Analysis.vval_rel
#print axioms Analysis.vval_coeff_eq
#print axioms Analysis.Rsin_cos_add_tan
#print axioms Analysis.altTerm_base_neg
#print axioms Analysis.altSum_base_neg
#print axioms Analysis.xBound_neg
#print axioms Analysis.RaltReal_K_neg
#print axioms Analysis.RaltReal_R_neg
#print axioms Analysis.Rcos_neg
#print axioms Analysis.RsinAux_neg
#print axioms Analysis.Rsin_neg
#print axioms Analysis.Rsin_sub
#print axioms Analysis.Rsin_sub_eq_zero
#print axioms Analysis.Rmul_eq_zero_cancel
#print axioms Analysis.Req_of_Rsub_zero_loc
#print axioms Analysis.Rtan_inj
#print axioms Analysis.Req_add_of_tan_values
#print axioms Analysis.Qneg_le_of_Qabs_le
#print axioms Analysis.altSum_sin_two_ge
#print axioms Analysis.altSum_sin_diag_gt
#print axioms Analysis.Pos_RsinAux_of_small
#print axioms Analysis.Rarctan_add
#print axioms Analysis.geoSum_le_two
#print axioms Analysis.Rarctan_seq_abs_le
#print axioms Analysis.Qmul_two_le_third
#print axioms Analysis.Rarctan_diff_seq_le
#print axioms Analysis.Rarctan_add_of_small
#print axioms Analysis.arctanSum_vval_argdiff
#print axioms Analysis.RarctanConst_add_vval_rho
#print axioms Analysis.RarctanR_add_real_via
#print axioms Analysis.Qabs_sub_mul_right_eq
#print axioms Analysis.Qabs_sub_mul_left_eq
#print axioms Analysis.Qrecip_anti
#print axioms Analysis.RaltReal_R_ge
#print axioms Analysis.Rartanh_R_ge
#print axioms Analysis.sinCoeff_abs_le_one
#print axioms Analysis.cosCoeff_abs_le_one
#print axioms Analysis.arctanSum_abs_le
#print axioms Analysis.arctanCoeff_fabs_le_one
#print axioms Analysis.gcornerB_den
#print axioms Analysis.e_rec_alg2
#print axioms Analysis.gen_per_m_step
#print axioms Analysis.gen_per_m_bound
-- v0.22.0 Track 1: the complex argument on the principal sector (Analysis/ComplexArg.lean).
#print axioms Analysis.Carg_ofReal_pos
-- v0.22.0 Track 1: the complex logarithm Clog on the principal sector (Analysis/ComplexLog.lean).
#print axioms Analysis.Clog_re
#print axioms Analysis.Clog_im
#print axioms Analysis.Clog_ofReal_pos_im
-- v0.22.0 Track 1: tmap closed forms at a rational argument (Analysis/RexpLogRat.lean).
#print axioms Analysis.tmap_rat_num
#print axioms Analysis.tmap_rat_den
#print axioms Analysis.Qle_of_Qsub_le_Qsub_left
#print axioms Analysis.Qle_of_Qsub_le_Qsub_right
#print axioms Analysis.Rlt_Qbound_of_Rle_ofQ
#print axioms Analysis.Pos_of_Rle_ofQ
#print axioms Analysis.Rpi_lower
#print axioms Analysis.Rle_Rneg
#print axioms Analysis.Radd_le_add
#print axioms Analysis.Rsub_le_sub
#print axioms Analysis.arctanSum_diag_ge
#print axioms Analysis.arctanSum_diag_le
#print axioms Analysis.arctanSum_diag_ge_at
#print axioms Analysis.arctanSum_diag_le_at
#print axioms Analysis.Rpi_lower_three
#print axioms Analysis.Rpi_seq_ge_three
#print axioms Analysis.tmap_ge_half
#print axioms Analysis.Rarctan_ge
#print axioms Analysis.Rarctan_le
#print axioms Analysis.Qmul_sub_left
#print axioms Analysis.Qabs_mul_const_sub
#print axioms Analysis.Qneg_le_neg
#print axioms Analysis.Qsub_le_2
#print axioms Analysis.Qabs_Qsub_neg_neg
#print axioms Analysis.Rpi_seq_den_pos
#print axioms Analysis.Rpi_regular
#print axioms Analysis.Rpi_pos
-- the log π LOWER bound (Analysis/LogPiLower.lean), resting on π ≥ 3.
#print axioms Analysis.RpiTmap_ge_half
#print axioms Analysis.Rartanh_RpiTmap_ge_half
#print axioms Analysis.Rlogpi_ge_one

-- v0.14.0 (wip) — γ₀ (Euler–Mascheroni) via the alternating ζ-series.
#print axioms Analysis.AltSum_succ
#print axioms Analysis.Qsub_nonneg_of_le
#print axioms Analysis.Qzero_le
#print axioms Analysis.num_nonneg_of_Qzero_le
#print axioms Analysis.Qsub_zero_eq
#print axioms Analysis.AltSum_den_pos
#print axioms Analysis.altSum_bracket
#print axioms Analysis.altSum_gap
#print axioms Analysis.zetaSum_s_anti_step
#print axioms Analysis.zetaSum_num_nonneg
#print axioms Analysis.zetaSum_le_two
#print axioms Analysis.altSum_diff_le
#print axioms Analysis.bterm_den_pos
#print axioms Analysis.bterm_num_nonneg
#print axioms Analysis.bterm_anti
#print axioms Analysis.bterm_le
#print axioms Analysis.bterm_depth_diff
#print axioms Analysis.gammaSeq_den_pos
#print axioms Analysis.gammaSeq_reg_le
#print axioms Analysis.gammaSeq_regular

-- v0.14.0 (wip) — accelerated γ (harmonic/telescoping): the artanh rational bounds.
#print axioms Analysis.artTerm_num_nonneg
#print axioms Analysis.artSum_step
#print axioms Analysis.artSum_mono
#print axioms Analysis.artSum_zero_eq
#print axioms Analysis.artSum_ge_arg
#print axioms Analysis.artTerm_le_geoTerm
#print axioms Analysis.artSum_le_geoSum
#print axioms Analysis.geoSum_cleared_le
#print axioms Analysis.artSum_le_geo
#print axioms Analysis.two_artSum_ge
#print axioms Analysis.two_artSum_le
#print axioms Analysis.cApprox_den_pos
#print axioms Analysis.cApprox_num_nonneg
#print axioms Analysis.cApprox_ub
#print axioms Analysis.Ssum_den_pos
#print axioms Analysis.Ssum_tail_le
#print axioms Analysis.npow_base_mono
#print axioms Analysis.npow_add
#print axioms Analysis.qpow_one_den
#print axioms Analysis.cApprox_depth_diff
#print axioms Analysis.Ssum_depth_diff
#print axioms Analysis.Ssum_le
#print axioms Analysis.pow_dom
#print axioms Analysis.gammaHseq_den_pos
#print axioms Analysis.gammaHseq_reg_le
#print axioms Analysis.gammaHseq_regular
#print axioms Analysis.Qabs_lower
#print axioms Analysis.clow_le_cApprox
#print axioms Analysis.Ssum_le_of_le
#print axioms Analysis.clow_den_pos
#print axioms Analysis.gammaHseq_ge_clow
#print axioms Analysis.gammaHseq_nonneg
#print axioms Analysis.Rgamma_h_lower
#print axioms Analysis.Qle_add_of_Qsub_le
#print axioms Analysis.artSum_upper_cleared
#print axioms Analysis.Rmul_ofQ_le
#print axioms Analysis.artSum_le_value
#print axioms Analysis.log_tail_eq
#print axioms Analysis.Rlog2c_le
#print axioms Analysis.deltaTail_eq
#print axioms Analysis.artTerm_base_mono
#print axioms Analysis.artSum_base_mono
#print axioms Analysis.Rpi_seq_lb
#print axioms Analysis.arctanSum_deep_le
#print axioms Analysis.arctanSum_deep_ge
#print axioms Analysis.Rpi_seq_ub_tight
#print axioms Analysis.Rpi_seq_ge
#print axioms Analysis.Rpi_seq_num_pos
#print axioms Analysis.tmap_num_nonneg
#print axioms Analysis.RpiTmap_den
#print axioms Analysis.RpiTmap_abs_le
#print axioms Analysis.RpiTmap_nonneg
#print axioms Analysis.tailπ_eq
#print axioms Analysis.Rlogπc_le
#print axioms Analysis.Qmul_half_le
#print axioms Analysis.Qabs_half_le
#print axioms Analysis.Rneg_le
#print axioms Analysis.Rhalf_ge
#print axioms Analysis.Rle_ofQ_add_Radd
#print axioms Analysis.Radd_Rle_ofQ_add
#print axioms Analysis.Rneg_ofQ_le
#print axioms Analysis.Rlambda1_pos

-- v0.15.0 — the complex analytic engine (stage A).
#print axioms Analysis.Cexp_re
#print axioms Analysis.Cexp_im
#print axioms Analysis.qpow_num_zero
#print axioms Analysis.altTerm_cos_zero_num
#print axioms Analysis.altSum_cos_zero
#print axioms Analysis.RexpReal_zero
#print axioms Analysis.Rcos_zero
#print axioms Analysis.Rsin_zero
#print axioms Analysis.Cexp_zero
#print axioms Analysis.choose_zero_right
#print axioms Analysis.choose_zero_succ
#print axioms Analysis.choose_succ_succ
#print axioms Analysis.choose_eq_zero_of_lt
#print axioms Analysis.choose_self
#print axioms Analysis.choose_mul_fct_mul_fct
#print axioms Analysis.Fsum_den_pos
#print axioms Analysis.Fsum_congr
#print axioms Analysis.Qadd_rearrange
#print axioms Analysis.Qmul_add_left
#print axioms Analysis.Fsum_add
#print axioms Analysis.Fsum_mul_left
#print axioms Analysis.Fsum_shift
#print axioms Analysis.Qadd_sub_cancel_left
#print axioms Analysis.Fsum_front
#print axioms Analysis.binTerm_den_pos
#print axioms Analysis.binTerm_top_zero
#print axioms Analysis.binTerm_zero_bot
#print axioms Analysis.Qadd_zero_right
#print axioms Analysis.Qadd_swap_left
#print axioms Analysis.Fsum_congr_le
#print axioms Analysis.Qmul_swap
#print axioms Analysis.binTerm_succ
#print axioms Analysis.binomial
#print axioms Analysis.expTerm_conv_term
#print axioms Analysis.expTerm_conv
#print axioms Analysis.alternating_binomial
#print axioms Analysis.Qadd_assoc3
#print axioms Analysis.Fsum_triangle_reindex
#print axioms Analysis.Fsum_square_decomp
#print axioms Analysis.Fsum_swap
#print axioms Analysis.Fsum_split_add
#print axioms Analysis.Fsum_split_at
#print axioms Analysis.Fsum_mono_len
#print axioms Analysis.Fsum_le_congr
#print axioms Analysis.Fsum_num_nonneg
#print axioms Analysis.Fsum_abs_le
#print axioms Analysis.Fsum_mul_const_right
#print axioms Analysis.Fsum_mul_square
#print axioms Analysis.expSum_eq_Fsum
#print axioms Analysis.Fsum_conv_expSum
#print axioms Analysis.Qmul_sub_distrib
#print axioms Analysis.QnegCongr
#print axioms Analysis.QsubCongr
#print axioms Analysis.Fsum_sq_cauchy
#print axioms Analysis.expSum_mul_eq
#print axioms Analysis.expSum_corner_factored
#print axioms Analysis.Qsub_add_left_cancel
#print axioms Analysis.expSum_mul_le
#print axioms Analysis.expSum_corner_le
-- v0.15.0 — the exponential functional equation on ℝ (the diagonal lift of the Cauchy product).
#print axioms Analysis.Qsub_add_self_left
#print axioms Analysis.Qsub_num_nonneg
#print axioms Analysis.exp_diag_gap
#print axioms Analysis.Rexp_add
-- v0.15.0 — the trigonometric Cauchy product (toward cos² + sin² = 1).
#print axioms Analysis.Qmul_left_comm
#print axioms Analysis.Qmul4_rearrange
#print axioms Analysis.qpow_add
#print axioms Analysis.altTerm_mul
#print axioms Analysis.altConv_factor
#print axioms Analysis.Qadd_perm
#print axioms Analysis.Qadd_perm4
#print axioms Analysis.Fsum_parity_split
#print axioms Analysis.Qadd_same_den_loc
#print axioms Analysis.Fsum_const_den
#print axioms Analysis.qpow_neg_one_even
#print axioms Analysis.qpow_neg_one_odd
#print axioms Analysis.NFsum_neg
#print axioms Analysis.binTerm_even
#print axioms Analysis.binTerm_odd
#print axioms Analysis.binom_even_odd_eq
#print axioms Analysis.cosFct_term
#print axioms Analysis.sinFct_term
#print axioms Analysis.cosFct_eq_sinFct
#print axioms Analysis.Qmul_assoc3
#print axioms Analysis.Qmul_qsq_qpow
#print axioms Analysis.altPyth_conv_vanish
#print axioms Analysis.Qadd_cancel_mid
#print axioms Analysis.altPyth_telescope
#print axioms Analysis.altPyth_partial
#print axioms Analysis.altCorner_factored
#print axioms Analysis.altCorner_abs_le
#print axioms Analysis.qpow_natBase
#print axioms Analysis.expTerm_natBase
#print axioms Analysis.altSum_eq_Fsum
#print axioms Analysis.expSumM_eq_Fsum
#print axioms Analysis.altAbsSum_le_U
#print axioms Analysis.altAbsTail_le
#print axioms Analysis.altTail_deep_le
#print axioms Analysis.Qsub_le_self_loc
#print axioms Analysis.altGap_le_U
#print axioms Analysis.altCorner_mertens
#print axioms Analysis.altTerm_abs_le_exp
#print axioms Analysis.altAntidiag_abs_le
#print axioms Analysis.Qabs_add3_le
#print axioms Analysis.Qabs_qsq_mul_le
#print axioms Analysis.altPyth_dev_eq_err
#print axioms Analysis.altErr_abs_le
#print axioms Analysis.Qsq_diff_le
#print axioms Analysis.Rcos_sq_diag_le
#print axioms Analysis.diagU_le
#print axioms Analysis.n_le_RaltReal_R
#print axioms Analysis.Rsin_sq_diag_le
#print axioms Analysis.Q_den_mono
#print axioms Analysis.Rcos_sq_add_sin_sq
#print axioms Analysis.Rmul4_rearrange
#print axioms Analysis.Rsin_sq_eq
#print axioms Analysis.altSum_reconcile
#print axioms Analysis.RaltReal_trunc_decay
#print axioms Analysis.RaltReal_trunc_le
#print axioms Analysis.npow_fct_decay
#print axioms Analysis.truncCoef_Q
#print axioms Analysis.Q_le_num_toNat
#print axioms Analysis.qpow_Qeq
#print axioms Analysis.expTerm_Qeq
#print axioms Analysis.expTerm_2MM
#print axioms Analysis.truncCoef_QE
#print axioms Analysis.uterm_le
#print axioms Analysis.altErr_bound_decay
#print axioms Analysis.xreg_n_le
#print axioms Analysis.xsq_diff_n_le
#print axioms Analysis.Qprodsq_diff_le
#print axioms Analysis.RaltReal_R_mono
#print axioms Analysis.altSum_abs_le_U
#print axioms Analysis.altSq_reconcile
#print axioms Analysis.deepErr_le
#print axioms Analysis.ratPyth_le

-- v0.10.0 — the λₙ / RH proof boundary (analytic face), locked faithfully.
#print axioms Li.Pos_one
#print axioms Li.template_liPositive
#print axioms Li.template_liNonneg
#print axioms Li.template_liPositiveUpTo
#print axioms Li.liPositive_iff_all_upTo
#print axioms Li.liDecomposition_genuine
#print axioms Li.explicitFormulaTrace_genuine
#print axioms Li.liAgreesWith_genuine

-- v0.10.0 — ExactBoundedReal enclosure interface + ζ(s) as an exact-bounded object.
#print axioms Analysis.enclosure_width
#print axioms Analysis.lowerB_le_upperB
#print axioms Analysis.certificate
#print axioms Analysis.npow_succ
#print axioms Analysis.npow_pos
#print axioms Analysis.npow_two
#print axioms Analysis.npow_one
#print axioms Analysis.npow_mono
#print axioms Analysis.zetaSum_den_pos
#print axioms Analysis.zetaSum_step
#print axioms Analysis.zetaSum_le
#print axioms Analysis.zeta_step_le
#print axioms Analysis.zetaU_den_pos
#print axioms Analysis.zetaU_step
#print axioms Analysis.zetaU_le
#print axioms Analysis.zetadiff_bound
#print axioms Analysis.zetaabs_bound
#print axioms Analysis.zetaSeq_regular
#print axioms Analysis.zeta_seq
#print axioms Analysis.zeta_pos

-- v0.15.0 keystone D corollary — |cos| ≤ 1, |sin| ≤ 1 (cos² ≤ 1, sin² ≤ 1).
#print axioms Analysis.Rnonneg_Rmul_self
#print axioms Analysis.Rle_self_Radd_right
#print axioms Analysis.Rle_self_Radd_left
#print axioms Analysis.Rcos_sq_le_one
#print axioms Analysis.Rsin_sq_le_one

-- v0.15.0 payoff — the Cexp modulus identity |Cexp z|² = (exp Re z)² (from cos²+sin²=1).
#print axioms Analysis.CnormSq
#print axioms Analysis.Cexp_normSq

-- v0.15.0 payoff — nˢ for integer base n ≥ 2 (Cexp(s·log n)) and its modulus.
#print axioms Analysis.RofNat
#print axioms Analysis.RlogNat
#print axioms Analysis.ncpow
#print axioms Analysis.ncpow_normSq

-- v0.15.0 ζ-stack — exp functional equation on all of ℝ (general-argument Cauchy corner).
#print axioms Analysis.expSum_corner_le_gen
#print axioms Analysis.expSum_add_le
#print axioms Analysis.expSum_reconcile
#print axioms Analysis.Qprod_diff_le
#print axioms Analysis.RexpReal_trunc_decay
#print axioms Analysis.RexpReal_trunc_le
#print axioms Analysis.expSum_abs_le_Un
#print axioms Analysis.expSum_add_decay
#print axioms Analysis.expTerm_abs
#print axioms Analysis.Fsum_tail_abs_le
#print axioms Analysis.expSum_corner_le_gen_signed
#print axioms Analysis.expSum_add_le_signed
#print axioms Analysis.expSum_add_decay_signed
#print axioms Analysis.n_le_RexpReal_R
#print axioms Analysis.rexp_factor_reconcile
#print axioms Analysis.rexp_add_gap
#print axioms Analysis.RexpReal_add_aux
#print axioms Analysis.RexpReal_add
-- v0.15.1 (wip) — toward exp∘log = id: exp respects ≈, and the reciprocal law.
#print axioms Analysis.RexpReal_congr
#print axioms Analysis.RexpReal_mul_neg
#print axioms Analysis.gPow_den_pos
#print axioms Analysis.gPow_num_nonneg
#print axioms Analysis.gPow_telescope
#print axioms Analysis.Qzero_add
#print axioms Analysis.fderiv_den_pos
#print axioms Analysis.fmul_den_pos
#print axioms Analysis.fderiv_fmul
#print axioms Analysis.Qadd_comm
#print axioms Analysis.Qmul_comm
#print axioms Analysis.Fsum_reverse
#print axioms Analysis.fmul_comm
#print axioms Analysis.Qmul_assoc
#print axioms Analysis.fmul_assoc
#print axioms Analysis.fone_den_pos
#print axioms Analysis.Fsum_zeros
#print axioms Analysis.fmul_one
#print axioms Analysis.dexpderiv_den
#print axioms Analysis.dgeom_den
#print axioms Analysis.dexpderiv_sum
#print axioms Analysis.dgeom_ode
#print axioms Analysis.peval_den_pos
#print axioms Analysis.peval_dgeom
#print axioms Analysis.expTerm_quad
#print axioms Analysis.Qsq_mul_nonneg
#print axioms Analysis.expSum_quad
#print axioms Analysis.artSum_lin_quad
#print axioms Analysis.Fsum_single
#print axioms Analysis.fmono_den
#print axioms Analysis.fmul_fmono
#print axioms Analysis.peval_conv
#print axioms Analysis.peval_mul
#print axioms Analysis.fmul_fmono_zero
#print axioms Analysis.fmul_add_left
#print axioms Analysis.kdbl_den
#print axioms Analysis.kdbl_shift_cancel
#print axioms Analysis.kdbl_main
#print axioms Analysis.kdbl_rel
#print axioms Analysis.oneplusSq_den
#print axioms Analysis.fderiv_congr
#print axioms Analysis.fmul_congr_left
#print axioms Analysis.twoFone_den
#print axioms Analysis.fderiv_oneplusSq
#print axioms Analysis.fderiv_twoT
#print axioms Analysis.kdbl_deriv_rel
#print axioms Analysis.fpow_den_pos
#print axioms Analysis.fpow_vanish
#print axioms Analysis.fcomp_den_pos
#print axioms Analysis.fcomp_const
#print axioms Analysis.fderiv_fone
#print axioms Analysis.fmul_congr_right
#print axioms Analysis.fsmul_den
#print axioms Analysis.fmul_zero_right
#print axioms Analysis.fmul_smul_right
#print axioms Analysis.fmul_swap_left
#print axioms Analysis.Qcombine_succ
#print axioms Analysis.fpow_deriv
#print axioms Analysis.fderiv_fcomp_sum
#print axioms Analysis.fcomp_chain_pre
#print axioms Analysis.Fsum_extend_zero
#print axioms Analysis.fcomp_chain
#print axioms Analysis.fsmono_den
#print axioms Analysis.fmul_fsmono
#print axioms Analysis.fmul_fsmono_zero
#print axioms Analysis.gcoef_den
#print axioms Analysis.acoef_den
#print axioms Analysis.fderiv_acoef
#print axioms Analysis.oneMinusSq_den
#print axioms Analysis.gcoef_shift_cancel
#print axioms Analysis.artanh_main
#print axioms Analysis.artanh_ode
#print axioms Analysis.fcomp_congr_left
#print axioms Analysis.Fsum_sub
#print axioms Analysis.fmul_sub_left
#print axioms Analysis.Qeq_of_Qsub_zero
#print axioms Analysis.oneMinusSq_eval2
#print axioms Analysis.oneMinusSq_eval0
#print axioms Analysis.oneMinusSq_eval1
#print axioms Analysis.oneMinusSq_zero_cancel
#print axioms Analysis.fmul_oneMinusSq_cancel
#print axioms Analysis.oneplusSq_eval2
#print axioms Analysis.oneplusSq_eval0
#print axioms Analysis.oneplusSq_eval1
#print axioms Analysis.oneplusSq_zero_cancel
#print axioms Analysis.fmul_oneplusSq_cancel
#print axioms Analysis.twoT_den
#print axioms Analysis.ksq_rel
#print axioms Analysis.fmono1_twoT
#print axioms Analysis.tk_rel
#print axioms Analysis.fmul_add_right
#print axioms Analysis.oneplusSq_twoFone
#print axioms Analysis.oneplusSq_kderiv
#print axioms Analysis.kdbl_W
#print axioms Analysis.twoFone_2fone
#print axioms Analysis.twoFone_fsmono
#print axioms Analysis.fmul_twoFone
#print axioms Analysis.twoT_fmono
#print axioms Analysis.twoT_2tk
#print axioms Analysis.oneMinusSq_as_sub
#print axioms Analysis.kdbl_sq_id
#print axioms Analysis.fpow_add
#print axioms Analysis.fcomp_add
#print axioms Analysis.fcomp_fone
#print axioms Analysis.Qsub_telescope3
#print axioms Analysis.geoEvenPow_den
#print axioms Analysis.fpow_sq_bump
#print axioms Analysis.geoEven_telescope
#print axioms Analysis.Fsum_collapse_odd
#print axioms Analysis.kdbl_zero
#print axioms Analysis.fcomp_gcoef_geoEven
#print axioms Analysis.comp_recip
#print axioms Analysis.fderiv_inj
#print axioms Analysis.twoacoef_ode
#print axioms Analysis.fcomp_acoef_ode
#print axioms Analysis.formal_doubling
#print axioms Analysis.acoef_even_zero
#print axioms Analysis.acoef_odd_artTerm
#print axioms Analysis.peval_acoef_artSum
#print axioms Analysis.peval_congr
#print axioms Analysis.peval_smul
#print axioms Analysis.dcomp_artSum
#print axioms Analysis.mul_left_zero
#print axioms Analysis.mul_right_zero
#print axioms Analysis.peval_fcomp_swap
#print axioms Analysis.Fsum_le_Fsum
#print axioms Analysis.peval_abs_bound
#print axioms Analysis.Qeq_sub_of_eq_add
#print axioms Analysis.peval_fpow_succ
#print axioms Analysis.fabs
#print axioms Analysis.fabs_den_pos
#print axioms Analysis.fabs_nonneg
#print axioms Analysis.Qabs_fmul_le
#print axioms Analysis.fmul_mono_right
#print axioms Analysis.fpow_abs_dom
#print axioms Analysis.peval_mono
#print axioms Analysis.peval_abs_le_peval_fabs
#print axioms Analysis.peval_fone
#print axioms Analysis.Qmul_num_nonneg
#print axioms Analysis.fpow_num_nonneg
#print axioms Analysis.peval_num_nonneg
#print axioms Analysis.peval_fpow_le_pow
#print axioms Analysis.peval_fpow_abs_bound
#print axioms Analysis.fabs_kdbl_even
#print axioms Analysis.fabs_kdbl_odd
#print axioms Analysis.peval_fabs_kdbl_geoSum
#print axioms Analysis.geoTerm_tel
#print axioms Analysis.geoSum_telescope
#print axioms Analysis.geoSum_tel_le
#print axioms Analysis.fabs_kdbl_le2
#print axioms Analysis.pow2_sum
#print axioms Analysis.fpow_fabs_kdbl_bound
#print axioms Analysis.qpow_mul
#print axioms Analysis.qpow_two_nat
#print axioms Analysis.fpow_kdbl_term_bound
#print axioms Analysis.Fsum_abs_diff_le
#print axioms Analysis.peval_kdbl_pow_gap
#print axioms Analysis.gPow_eq_Fsum
#print axioms Analysis.Qsub_sub_one
#print axioms Analysis.gPow_gap_le
#print axioms Analysis.Qmul_sub_left_loc
#print axioms Analysis.peval_kdbl_pow_cauchy
#print axioms Analysis.peval_kdbl_pow_abs_le
#print axioms Analysis.corner_inner_eq
#print axioms Analysis.Qle_rho_two_rho
#print axioms Analysis.qpow_conv_le
#print axioms Analysis.mul_rearrange
#print axioms Analysis.Qabs_C_le
#print axioms Analysis.corner_term_le
#print axioms Analysis.Fsum_le_Fsum_le
#print axioms Analysis.corner_bound
#print axioms Analysis.kdbl_period
#print axioms Analysis.add_rearrange
#print axioms Analysis.qpow_mul_sq
#print axioms Analysis.kdbl_innerval
#print axioms Analysis.uval
#print axioms Analysis.uval_den_pos
#print axioms Analysis.uval_rel
#print axioms Analysis.Qabs_kdbl_qpow_le
#print axioms Analysis.q_conv
#print axioms Analysis.uval_abs_le
#print axioms Analysis.Qabs_sub_le_add
#print axioms Analysis.e_rec_alg
#print axioms Analysis.kcorner
#print axioms Analysis.kcorner_den
#print axioms Analysis.per_m_step
#print axioms Analysis.per_m_bound
#print axioms Analysis.DN_eq
#print axioms Analysis.acoef_num_nonneg
#print axioms Analysis.acoef_le_one
#print axioms Analysis.DN_abs_le
#print axioms Analysis.e_le_T
#print axioms Analysis.DN_double_le
#print axioms Analysis.Qadd_num_nonneg_loc
#print axioms Analysis.Qzero_le_loc
#print axioms Analysis.sq_le_four_pow
#print axioms Analysis.corner_sum_bound
#print axioms Analysis.Qadd_const_mul
#print axioms Analysis.Fsum_const_eq
#print axioms Analysis.pow4_sum_le
#print axioms Analysis.Qmul_rearr3
#print axioms Analysis.pow4_2_sum_le
#print axioms Analysis.corner_sum_closed
#print axioms Analysis.Qmul_swap_outer
#print axioms Analysis.mul_div2
#print axioms Analysis.corner_sum_final
#print axioms Analysis.T_le
#print axioms Analysis.DN_geom_le
#print axioms Analysis.qpow_double
#print axioms Analysis.qpow_mono_exp
#print axioms Analysis.qpow_const_nat
#print axioms Analysis.qpow_const_combine
#print axioms Analysis.Qadd_2_2_4
#print axioms Analysis.Qadd_4_4_8
#print axioms Analysis.Qmul_2_2_4
#print axioms Analysis.qpow_Qeq_loc
#print axioms Analysis.T_pow_le
#print axioms Analysis.two_pow_2Nplus2
#print axioms Analysis.Qmul_8rearr
#print axioms Analysis.DN_pow_le
#print axioms Analysis.qpow_le_recip
#print axioms Analysis.Qmul_2_2
#print axioms Analysis.geoSum_num_nonneg
#print axioms Analysis.peval_kdbl_abs_le_one
#print axioms Analysis.DN_recip
#print axioms Analysis.Qadd_self
#print axioms Analysis.RartanhAtQ_seq
#print axioms Analysis.Qadd_same_den
#print axioms Analysis.Rartanh_double_via
#print axioms Analysis.Rartanh_double_rat
#print axioms Analysis.geoEvenSum_num_nonneg
#print axioms Analysis.geoEvenSum_le_two
#print axioms Analysis.Rartanh_congr
#print axioms Analysis.uval_diff_cleared
#print axioms Analysis.uval_lip
#print axioms Analysis.artSum_depth_recip
#print axioms Analysis.Dterm_recip
#print axioms Analysis.artSum_uval_argdiff
#print axioms Analysis.Rartanh_double_real_via
#print axioms Analysis.Qmul_cancel_left
#print axioms Analysis.tmap_uval_core
#print axioms Analysis.tmap_sq_uval
#print axioms Analysis.tmap_lip
#print axioms Analysis.tsq_uvalReal_via
#print axioms Analysis.Rlog_double_algebra
#print axioms Analysis.Rartanh_radius_indep
#print axioms Analysis.Rlog_sq_via
#print axioms Analysis.Rlog_eq_Rmul
#print axioms Analysis.Rlog_tbound
#print axioms Analysis.Rlog_radius_facts
#print axioms Analysis.Rlog_sq
#print axioms Analysis.ecoef_den
#print axioms Analysis.fderiv_ecoef
#print axioms Analysis.fderiv_mul_inj
#print axioms Analysis.fderiv_twoacoef
#print axioms Analysis.formal_exp_geom
#print axioms Analysis.expSum_eq_peval_ecoef
#print axioms Analysis.peval_twoacoef_artSum
#print axioms Analysis.comp_eval_gap_le
#print axioms Analysis.peval_dgeom_mul_cleared
#print axioms Analysis.peval_dgeom_tail_cleared
#print axioms Analysis.truncTo_den
#print axioms Analysis.truncTo_le
#print axioms Analysis.peval_truncTo
#print axioms Analysis.Fsum_ext_zero
#print axioms Analysis.peval_mul_no_corner
#print axioms Analysis.fpow_supp
#print axioms Analysis.peval_fpow_pow_eq
#print axioms Analysis.truncTo_nonneg
#print axioms Analysis.fpow_mono
#print axioms Analysis.qpow_peval_le
#print axioms Analysis.Fsum_le_extend
#print axioms Analysis.exp_corner_le
#print axioms Analysis.dgeom_geom_gap_le
#print axioms Analysis.exp_artanh_rat_cleared
#print axioms Analysis.mul_div_gen
#print axioms Analysis.Fsum_smul
#print axioms Analysis.peval_twoacoef_cauchy
#print axioms Analysis.peval_twoacoef_abs_le_gpow
#print axioms Analysis.exp_artanh_recip
#print axioms Analysis.Rexp_two_artanh_via
#print axioms Analysis.two_gPow_le
#print axioms Analysis.Rexp_two_artanh_ofQ
#print axioms Analysis.tmap_nat_den
#print axioms Analysis.tmap_nat_num
#print axioms Analysis.Rexp_log_nat
#print axioms Analysis.Rexp_log_nat_Rlog

-- v0.15.2 — real powers `nᶜ = exp(c·log n)` (RealPow.lean).
#print axioms Analysis.Rnsmul_zero
#print axioms Analysis.Rnsmul_succ
#print axioms Analysis.RexpReal_nsmul
#print axioms Analysis.RexpReal_nsmul_eq
#print axioms Analysis.Rnonneg_Rmul
#print axioms Analysis.Rnonneg_of_Rle_zero
#print axioms Analysis.Rnonneg_congr
#print axioms Analysis.Rhalf_double
#print axioms Analysis.Rhalf_Radd
#print axioms Analysis.Rhalf_Rneg
#print axioms Analysis.Rhalf_Rsub
#print axioms Analysis.Rhalf_congr
#print axioms Analysis.Rhalf_le_Rhalf
#print axioms Analysis.Rhalf_nonneg
#print axioms Analysis.RexpReal_nonneg
#print axioms Analysis.RexpReal_sub_one_nonneg
#print axioms Analysis.Rnonneg_Rsub_of_Rle
#print axioms Analysis.Rle_of_Rnonneg_Rsub
#print axioms Analysis.Radd_Rsub_self
#print axioms Analysis.RexpReal_le_of_Rle
#print axioms Analysis.Rmul_ofQ_ofQ
#print axioms Analysis.RexpReal_neg_eq_recip
#print axioms Analysis.artSum_nonneg
#print axioms Analysis.Rlog_nonneg
#print axioms Analysis.Rneg_Radd
#print axioms Analysis.Rone_mul
#print axioms Analysis.Rmul_two_eq_add
#print axioms Analysis.Rmul_two_le_Rmul
#print axioms Analysis.RexpReal_neg_two_eq
#print axioms Analysis.RexpReal_neg_sigma_le
#print axioms Analysis.expSum_le_gPow
#print axioms Analysis.expSum_mul_one_sub_le
#print axioms Analysis.Rnonneg_of_Rmul_Pos
#print axioms Analysis.Pos_of_Rle_one
#print axioms Analysis.expSum_ge_one_add
#print axioms Analysis.RexpReal_ge_one_add_nonneg
#print axioms Analysis.gval_den_pos
#print axioms Analysis.gval_rel
#print axioms Analysis.tmap_two_law
#print axioms Analysis.dcoef_den
#print axioms Analysis.dcoef_zero
#print axioms Analysis.nine3w_den
#print axioms Analysis.eightT_den
#print axioms Analysis.nine3w_split
#print axioms Analysis.dcoef_cancel_scalar
#print axioms Analysis.dcoef_shift_cancel
#print axioms Analysis.dcoef_main
#print axioms Analysis.dcoef_rel
#print axioms Analysis.threeFone_den
#print axioms Analysis.eightFone_den
#print axioms Analysis.fderiv_nine3w
#print axioms Analysis.fderiv_eightT
#print axioms Analysis.dcoef_deriv_rel
#print axioms Analysis.mul9_eq_zero
#print axioms Analysis.nine3w_eval0
#print axioms Analysis.nine3w_eval_succ
#print axioms Analysis.nine3w_zero_cancel
#print axioms Analysis.fmul_nine3w_cancel
#print axioms Analysis.threeFone_eq_fsmono
#print axioms Analysis.nine3w_dderiv
#print axioms Analysis.nine3w_dsq
#print axioms Analysis.eightT_eq_fsmono
#print axioms Analysis.eightT_sq_val
#print axioms Analysis.nine3w_sq_val
#print axioms Analysis.nine3w_eightT_val
#print axioms Analysis.g2_final
#print axioms Analysis.fmul_sub_right
#print axioms Analysis.eightFone_eq_fsmul
#print axioms Analysis.eight_n_three_e
#print axioms Analysis.nine3w_8m3d
#print axioms Analysis.nine3w_M2
#print axioms Analysis.nine3w_qcomp1
#print axioms Analysis.nine3w_de
#print axioms Analysis.qcomp_den
#print axioms Analysis.nine3w_qcomp2
#print axioms Analysis.dcoef_ode
#print axioms Analysis.sacDpair_den
#print axioms Analysis.sacD_den
#print axioms Analysis.sacD_succ_succ
#print axioms Analysis.p2_den
#print axioms Analysis.p2_split
#print axioms Analysis.sacD_cancel
#print axioms Analysis.sacD_ode
#print axioms Analysis.sacoef_zero
#print axioms Analysis.sacoef_den
#print axioms Analysis.fderiv_sacoef
#print axioms Analysis.fcomp_shift1
#print axioms Analysis.fmono1_sq
#print axioms Analysis.fcomp_shift2
#print axioms Analysis.fmul_smul_left
#print axioms Analysis.fcomp_smul
#print axioms Analysis.fcomp_sub
#print axioms Analysis.fmul_fsmono_smul
#print axioms Analysis.p2_sacD
#print axioms Analysis.qcomp_add
#print axioms Analysis.composed_ode
#print axioms Analysis.mul9_cancel
#print axioms Analysis.fderiv_fcomp_sacoef
#print axioms Analysis.fcomp_sacoef_eq_acoef
#print axioms Analysis.peval_fcomp_sacoef_artSum
#print axioms Analysis.gcorner_den
#print axioms Analysis.per_m_step_gen
#print axioms Analysis.per_m_bound_gen
#print axioms Analysis.qpow_third_abs_le_one
#print axioms Analysis.dcoef_abs_le_one
#print axioms Analysis.drat_den
#print axioms Analysis.drat_rel
#print axioms Analysis.peval_nine3w
#print axioms Analysis.peval_eightT
#print axioms Analysis.nine3w_peval_dcoef
#print axioms Analysis.nine3w_peval_dcoef_sub
#print axioms Analysis.inner_eval_bound
#print axioms Analysis.dcoef_term_geo
#print axioms Analysis.inner_eval_geo
#print axioms Analysis.fpow_fabs_dcoef_bound
#print axioms Analysis.qpow_two_eq
#print axioms Analysis.qpow_mul_dist
#print axioms Analysis.fpow_fabs_dcoef_term
#print axioms Analysis.peval_dcoef_pow_gap
#print axioms Analysis.peval_dcoef_pow_cauchy
#print axioms Analysis.corner_inner_eq_gen
#print axioms Analysis.Qabs_dcoef_qpow_le
#print axioms Analysis.dcoef_corner_term
#print axioms Analysis.dcoef_gcorner_bound
#print axioms Analysis.Pos_imp_ofQ_le
#print axioms Analysis.Pos_mono
#print axioms Analysis.Rnonneg_of_Pos
#print axioms Analysis.Rnonneg_neg_of_not_Pos
#print axioms Analysis.not_Pos_of_Rnonneg_neg
#print axioms Analysis.Rneg_neg
#print axioms Analysis.Rneg_Rsub
#print axioms Analysis.RexpReal_ge_one
#print axioms Analysis.Pos_RexpReal
#print axioms Analysis.Pos_congr
#print axioms Analysis.exp_sub_exp_eq
#print axioms Analysis.Rsub_Radd_eq
#print axioms Analysis.Rle_exp_sub_one
#print axioms Analysis.Rle_self_Rmul_left
#print axioms Analysis.RexpReal_strictmono
#print axioms Analysis.RexpReal_reflects_le
#print axioms Analysis.RexpReal_inj
#print axioms Analysis.Rexp_logN
#print axioms Analysis.Rnonneg_logN
#print axioms Analysis.logN_mul
#print axioms Analysis.logN_eq_of_eq
#print axioms Analysis.logN_one
#print axioms Analysis.logN_pow_two
#print axioms Analysis.Rle_ofQ_ofQ
#print axioms Analysis.logN_mono
#print axioms Analysis.logN_ge_k_log2
#print axioms Analysis.Rmul_le_Rmul_left
#print axioms Analysis.exp_block_bound
#print axioms Analysis.Rexp_k_log2
#print axioms Analysis.Rexp_half_le
#print axioms Analysis.logN_2_ge_half
#print axioms Analysis.Rnonneg_ofQ
#print axioms Analysis.Rle_recip
#print axioms Analysis.Rexp_neg_le_ratio
#print axioms Analysis.Rmul_le_Rmul_right
#print axioms Analysis.Pos_Rmul
#print axioms Analysis.Rmul_sub_add_self
#print axioms Analysis.Rle_of_Rmul_self_le
#print axioms Analysis.Rneg_sq
#print axioms Analysis.Rcos_le_one
#print axioms Analysis.Rneg_one_le_Rcos
#print axioms Analysis.Rsin_le_one
#print axioms Analysis.Rneg_one_le_Rsin
#print axioms Analysis.Cexp_re_le
#print axioms Analysis.Cexp_re_ge
#print axioms Analysis.Cexp_im_le
#print axioms Analysis.Cexp_im_ge
#print axioms Analysis.czetaTerm_re_le
#print axioms Analysis.czetaTerm_re_ge
#print axioms Analysis.czetaTerm_im_le
#print axioms Analysis.czetaTerm_im_ge
#print axioms Analysis.Rsub_Radd_left
#print axioms Analysis.Rneg_zero
#print axioms Analysis.czeta_re_diff_le_aux
#print axioms Analysis.czeta_re_diff_le
#print axioms Analysis.czeta_re_diff_ge_aux
#print axioms Analysis.czeta_re_diff_ge
#print axioms Analysis.czeta_im_diff_le_aux
#print axioms Analysis.czeta_im_diff_le
#print axioms Analysis.czeta_im_diff_ge_aux
#print axioms Analysis.czeta_im_diff_ge
#print axioms Analysis.czetaExp_block_le
#print axioms Analysis.czetaExp_term_le
#print axioms Analysis.czetaExp_block
#print axioms Analysis.Rnonneg_Rpow
#print axioms Analysis.Rpow_ofQ
#print axioms Analysis.Rpow_mono
#print axioms Analysis.Rmul_Rnsmul
#print axioms Analysis.Rneg_Rnsmul
#print axioms Analysis.Rmul_mul_mul
#print axioms Analysis.Rpow_mul_dist
#print axioms Analysis.Radd_ofQ_ofQ
#print axioms Analysis.ofQ_congr
#print axioms Analysis.Rnsmul_eq_Rmul_ofQ
#print axioms Analysis.czetaExpB_eq_pow
#print axioms Analysis.czetaExp_block_pow
#print axioms Analysis.czeta_theta_arg_eq
#print axioms Analysis.czetaU_2u_eq
#print axioms Analysis.czetaU_2u_le_of_theta
#print axioms Analysis.czeta_theta_ge
#print axioms Analysis.czetaExp_block_geo
#print axioms Analysis.Rsub_telescope
#print axioms Analysis.geoFrom_den_pos
#print axioms Analysis.czetaExp_tail
#print axioms Analysis.geoFrom_telescope
#print axioms Analysis.geoFrom_le
#print axioms Analysis.seq_diff_le
#print axioms Analysis.RReg_of_real_bound
#print axioms Analysis.geom_reindex
#print axioms Analysis.czetaR_facts
#print axioms Analysis.czetaExp_tail_reindex
#print axioms Analysis.czetaMidx_mono
#print axioms Analysis.czetaExp_tail_mono
#print axioms Analysis.czetaRe_tail_le
#print axioms Analysis.czetaRe_tail_ge
#print axioms Analysis.czetaIm_tail_le
#print axioms Analysis.czetaIm_tail_ge
#print axioms Analysis.Czeta_re_tendsTo
#print axioms Analysis.Czeta_im_tendsTo
#print axioms Analysis.czetaRe_RReg
#print axioms Analysis.czetaIm_RReg
#print axioms Analysis.czeta_two_theta
#print axioms Analysis.czetaExp_mono
#print axioms Analysis.czetaExp_tail_full
#print axioms Analysis.czetaRe_tail_full
#print axioms Analysis.czetaRe_tail_full_neg
#print axioms Analysis.czetaIm_tail_full
#print axioms Analysis.czetaIm_tail_full_neg
#print axioms Analysis.czetaRe_cauchy_full
#print axioms Analysis.czetaIm_cauchy_full
#print axioms Analysis.RTendsTo_to_Rle
#print axioms Analysis.RTendsTo_to_Rle_lower
#print axioms Analysis.Req_of_Rle_ofQ_all
#print axioms Analysis.czetaRe_full_tendsTo
#print axioms Analysis.czetaIm_full_tendsTo
#print axioms Analysis.Czeta_re_canonical
#print axioms Analysis.Czeta_im_canonical

-- Mangoldt (the von Mangoldt function Λ and the explicit-formula prime side; v0.15.3).
#print axioms Analysis.spfFrom_ge_one
#print axioms Analysis.one_le_spf
#print axioms Analysis.two_le_of_isPrimePow
#print axioms Analysis.spf_dvd
#print axioms Analysis.spf_two_le
#print axioms Analysis.spf_prime
#print axioms Analysis.vonMangoldt_prime
#print axioms Analysis.vonMangoldt_one
#print axioms Analysis.vonMangoldt_two
#print axioms Analysis.vonMangoldt_three
#print axioms Analysis.vonMangoldt_four
#print axioms Analysis.vonMangoldt_six
#print axioms Analysis.vonMangoldt_eight
#print axioms Analysis.vonMangoldt_nine
#print axioms Analysis.vonMangoldt_nonneg
#print axioms Analysis.primeSide_stable
#print axioms Analysis.primeTerm_zero_of_h

-- GammaOne (the first Stieltjes constant γ₁ substrate: (ln k)/k, S(N), g(N); v0.16.0).
#print axioms Analysis.lnOver_nonneg
#print axioms Analysis.lnSum_step
#print axioms Analysis.lnSum_mono
#print axioms Analysis.logN_four_ge_one
#print axioms Analysis.logN_ge_one
#print axioms Analysis.twoArtanhRecip_le
#print axioms Analysis.Rnonneg_RartanhConst
#print axioms Analysis.Rexp_twoArtanhRecip
#print axioms Analysis.deltaLog_eq_twoArtanh
#print axioms Analysis.deltaLog_upper_tight
#print axioms Analysis.qRoundUp_ge
#print axioms Analysis.qRoundUp_den_pos
#print axioms Analysis.dPlusQ_den_pos
#print axioms Analysis.logBound_den_pos
#print axioms Analysis.logN_le_logBound
#print axioms Analysis.lnSumBound_den_pos
#print axioms Analysis.lnSum_le_lnSumBound
#print axioms Analysis.ofQ_artSum_le_RartanhConst
#print axioms Analysis.deltaLog_lower_tight
#print axioms Analysis.dMinusQ_den_pos
#print axioms Analysis.qRoundDown_le
#print axioms Analysis.qRoundDown_den_pos
#print axioms Analysis.logLowBound_den_pos
#print axioms Analysis.logN_ge_logLowBound
#print axioms Analysis.Rhalf_ofQ
#print axioms Analysis.Rneg_ofQ
#print axioms Analysis.dMinusQ_num_nonneg
#print axioms Analysis.logLowBound_num_nonneg
#print axioms Analysis.gBound_den_pos
#print axioms Analysis.gSeq_le_gBound
#print axioms Analysis.gBound200_le_neg
#print axioms Analysis.Rgamma1_le_neg445
#print axioms Analysis.gBound200_T4_le_neg055
#print axioms Analysis.Rgamma1_le_neg055
#print axioms Analysis.deltaLog_upper
#print axioms Analysis.expDelta_eq
#print axioms Analysis.expRecip_le
#print axioms Analysis.Rexp_recip_le
#print axioms Analysis.deltaLog_lower
#print axioms Analysis.addsub_linear
#print axioms Analysis.sq_diff_identity
#print axioms Analysis.Rsub_le_of_le_add
#print axioms Analysis.half_combine
#print axioms Analysis.dStep_le_half_sq
#print axioms Analysis.dStep_le
#print axioms Analysis.dStep_ge
#print axioms Analysis.Rsub_Rneg_Rneg
#print axioms Analysis.gSeq_step_eq
#print axioms Analysis.Rsub_split
#print axioms Analysis.gSeq_step_le
#print axioms Analysis.gSeq_step_ge
#print axioms Analysis.Usum_den_pos
#print axioms Analysis.Qadd_Qsub_comm
#print axioms Analysis.gSeq_diff_le_U
#print axioms Analysis.Qadd_Qsub_telescope
#print axioms Analysis.Usum_step_ineq
#print axioms Analysis.Usum_tail_le
#print axioms Analysis.gSeq_diff_le
#print axioms Analysis.logN_2_le_one
#print axioms Analysis.logN_le_block
#print axioms Analysis.gSeq_step_ge_block
#print axioms Analysis.Vsum_den_pos
#print axioms Analysis.gSeq_diff_ge_block
#print axioms Analysis.Vsum_step_eq
#print axioms Analysis.Vsum_tail_le
#print axioms Analysis.Qsub_block_le
#print axioms Analysis.gSeq_block_ge
#print axioms Analysis.Wsum_den_pos
#print axioms Analysis.gSeq_diff_ge_outer
#print axioms Analysis.Qadd_Qsub_fwd
#print axioms Analysis.Wsum_tail_le
#print axioms Analysis.lt_two_pow
#print axioms Analysis.lin_le_two_pow
#print axioms Analysis.gamma_domination
#print axioms Analysis.gammaMidx_mono
#print axioms Analysis.Qunit_le
#print axioms Analysis.Qsub_unit_le
#print axioms Analysis.succ_le_two_pow_midx
#print axioms Analysis.gamma_pair_le
#print axioms Analysis.Qsub_le_left
#print axioms Analysis.gamma_T_le
#print axioms Analysis.gamma_pair_ge
#print axioms Analysis.gSeqDyadic_RReg
#print axioms Analysis.Rle_of_Rsub_le_all
#print axioms Analysis.Rle_add_of_Rsub_le
#print axioms Analysis.gSeq_le_anchor
#print axioms Analysis.Rgamma1_le_gSeq

-- ZetaTwo (the ζ(2) ≥ 1.63 lower bracket; v0.16.0, for Pos λ₂).
#print axioms Analysis.zeta_ge_partial
#print axioms Analysis.zetaSum_two_70_ge
#print axioms Analysis.zeta2_lower
#print axioms Analysis.zeta_le_partial
#print axioms Analysis.zetaU_two_70_le
#print axioms Analysis.zeta2_upper
#print axioms Analysis.zetaSum_three_70_ge
#print axioms Analysis.zeta3_lower
#print axioms Analysis.zetaU_three_70_le
#print axioms Analysis.zeta3_upper

-- GammaUpper (the γ ≤ 0.66 upper bracket, companion to Rgamma_h_lower; v0.16.0, for Pos λ₂).
#print axioms Analysis.Qabs_upper
#print axioms Analysis.Qadd_sub_cancel
#print axioms Analysis.chigh_den_pos
#print axioms Analysis.cApprox_le_chigh
#print axioms Analysis.gammaHseq_le_one
#print axioms Analysis.gammaHseq_le_chigh
#print axioms Analysis.chigh_sum_bound
#print axioms Analysis.Rgamma_h_upper

-- Bernoulli (exact rational Bernoulli numbers; v0.16.0 foundation for Euler–Maclaurin).
#print axioms Analysis.bernTable_den_pos
#print axioms Analysis.bernoulli_den_pos
#print axioms Analysis.bernoulli_zero
#print axioms Analysis.bernoulli_one
#print axioms Analysis.bernoulli_two
#print axioms Analysis.bernoulli_three
#print axioms Analysis.bernoulli_four
#print axioms Analysis.bernoulli_five
#print axioms Analysis.bernoulli_six

-- LiOne (the Bombieri–Lagarias n=1 decomposition λ₁ = λ₁^arith + λ₁^∞; v0.15.3).
#print axioms Analysis.Rhalf_two
#print axioms Analysis.Rlambda1_decomposition
#print axioms Analysis.li_decomposition_realized

-- LambdaTwo (Pos λ₂; v0.16.0 stage-B capstone).
#print axioms Analysis.Rneg_Rneg
#print axioms Analysis.parab_gen
#print axioms Analysis.Rlambda2_pos

-- EulerMaclaurin (the deterministic EM correction-term data; v0.16.0 goal B foundation).
#print axioms Analysis.Cpoch_zero
#print axioms Analysis.Cpoch_succ
#print axioms Analysis.emCoeff_den_pos
#print axioms Analysis.emCoeff_one
#print axioms Analysis.emCoeff_two
#print axioms Analysis.emCoeff_three

-- RealDiv (the real inverse law x·(1/x)=1; the Inv.lean gap, prereq for Cinv / goals A,B).
#print axioms Analysis.Qmul_Qinv_sub_one
#print axioms Analysis.Rmul_Rinv_perpoint
#print axioms Analysis.Rmul_Rinv_self

-- The pointwise dilation-covariance of the reciprocal (new Analysis/RinvDilate.lean).
#print axioms Analysis.Rmul_ofQ_Rinv_Rmul

-- The Haar density's dilation-covariance on the window (new Analysis/HaarDensity.lean).
#print axioms Analysis.clampedInv_dilate_on

-- ComplexInv (the complex reciprocal 1/z = z̄/|z|²; prereq for 1/(s−1) and the Γ place).
#print axioms Analysis.Cmul_Cinv
#print axioms Analysis.emCorrSum_zero
#print axioms Analysis.emCorrSum_succ
#print axioms Analysis.czFinSum_zero
#print axioms Analysis.czFinSum_succ

-- BernoulliPoly (Bernoulli polynomials Bₙ(x); prereq for the periodic-Bernoulli EM remainder).
#print axioms Analysis.bernPoly_den_pos
#print axioms Analysis.bernPoly_zero
#print axioms Analysis.bernPoly_one_at_zero
#print axioms Analysis.bernPoly_two_at_zero
#print axioms Analysis.bernPoly_one_at_one
#print axioms Analysis.bernPoly_two_at_one
#print axioms Analysis.bernPoly_two_form
#print axioms Analysis.bernPoly_two_abs_le

-- EtaFunction (η(s) = Σ(−1)^{n−1}n⁻ˢ; the integration-free critical-strip route, ζ = η/(1−2^{1−s})).
#print axioms Analysis.czEtaSum_zero
#print axioms Analysis.czEtaSum_succ
#print axioms Analysis.czEtaTerm_even
#print axioms Analysis.czEtaTerm_odd

-- CosSinAddFormula (the cos/sin angle-addition foundation: antidiagonal identity → diagonal relation).
#print axioms Analysis.pairTerm_den_pos
#print axioms Analysis.binTerm_scaled_eq
#print axioms Analysis.addPow_div_antidiag
#print axioms Analysis.qpow_sq_eq
#print axioms Analysis.qpow_negsq
#print axioms Analysis.negsq_pair
#print axioms Analysis.altPair_eq
#print axioms Analysis.cosPair_eq
#print axioms Analysis.sinTerm_den_pos
#print axioms Analysis.sinPair_eq
#print axioms Analysis.cosConv_den_pos
#print axioms Analysis.sinConv_den_pos
#print axioms Analysis.cosConv_eq
#print axioms Analysis.sinConv_eq
#print axioms Analysis.altTerm_add_eq
#print axioms Analysis.Fsum_mul_Fsum
#print axioms Analysis.fsum_cauchy
#print axioms Analysis.cosCauchy_eq
#print axioms Analysis.sinCauchy_eq
#print axioms Analysis.altCorner_factored2
#print axioms Analysis.altCorner_abs_le2
#print axioms Analysis.cornerMertens2
#print axioms Analysis.sinTerm_abs_le
#print axioms Analysis.sinConv_abs_le
#print axioms Analysis.cosAdd_resid_eq
#print axioms Analysis.cornerSin_factored
#print axioms Analysis.Qabs_mul_le_MM
#print axioms Analysis.cornerSin_le
#print axioms Analysis.cosAdd_decay_le
#print axioms Analysis.cosAdd_decay_5
#print axioms Analysis.cosMul_diag_le
#print axioms Analysis.xprod_drift
#print axioms Analysis.altProd_drift
#print axioms Analysis.sinMul_diag_le
#print axioms Analysis.altSum_add_eq
#print axioms Analysis.altDiag_to_deep
#print axioms Analysis.cosMulDeep_le
#print axioms Analysis.cosAddLHS_le
#print axioms Analysis.Fsum_sinTerm_eq
#print axioms Analysis.altMulDeep_le
#print axioms Analysis.sinMulDeep_le
#print axioms Analysis.Rcos_add
#print axioms Analysis.pairTermD_den_pos
#print axioms Analysis.binTermD_scaled_eq
#print axioms Analysis.addPow_div_diag
#print axioms Analysis.Fsum_parity_split_odd
#print axioms Analysis.altPairMixed_eq
#print axioms Analysis.scPair_eq
#print axioms Analysis.csPair_eq
#print axioms Analysis.csConv_eq
#print axioms Analysis.scConv_eq
#print axioms Analysis.sinTerm_add_eq
#print axioms Analysis.sinAdd_partial_eq
#print axioms Analysis.csCauchy_eq
#print axioms Analysis.scCauchy_eq
#print axioms Analysis.sinAdd_resid_eq
#print axioms Analysis.altCorner_factored2_mixed
#print axioms Analysis.altCorner_abs_le2_mixed
#print axioms Analysis.cornerMertens2_mixed
#print axioms Analysis.cornerCs_factored
#print axioms Analysis.cornerSc_factored
#print axioms Analysis.cornerCs_le
#print axioms Analysis.cornerSc_le
#print axioms Analysis.sinAdd_decay_le
#print axioms Analysis.sinAdd_decay_5
#print axioms Analysis.csConv_den_pos
#print axioms Analysis.scConv_den_pos
#print axioms Analysis.csMul_diag_le
#print axioms Analysis.scMul_diag_le
#print axioms Analysis.RsinSelf_diag_le
#print axioms Analysis.csMulDeep_le
#print axioms Analysis.scMulDeep_le
#print axioms Analysis.sinAddLHS_le
#print axioms Analysis.Rsin_add
#print axioms Analysis.Cexp_add
#print axioms Analysis.RaltReal_congr
#print axioms Analysis.Rcos_congr
#print axioms Analysis.Rsin_congr
#print axioms Analysis.Cexp_congr
#print axioms Analysis.cpowNeg_succ
#print axioms Analysis.Rsub_RnegRneg
#print axioms Analysis.Cadd_congr
#print axioms Analysis.Cneg_congr
#print axioms Analysis.Cmul_congr
#print axioms Analysis.Csub_congr
#print axioms Analysis.Cmul_neg_right
#print axioms Analysis.cpowNeg_diff
#print axioms Analysis.cpowNeg_re_le
#print axioms Analysis.cpowNeg_re_ge
#print axioms Analysis.cpowNeg_im_le
#print axioms Analysis.cpowNeg_im_ge
#print axioms Analysis.RexpReal_neg_le_one
#print axioms Analysis.expSum_ge_one_add_four
#print axioms Analysis.RexpReal_ge_one_add_four
#print axioms Analysis.RexpReal_one_sub_neg_le
#print axioms Analysis.altSum_quad
#print axioms Analysis.RaltReal_upper_le
#print axioms Analysis.RaltReal_lower_ge
#print axioms Analysis.Rcos_one_sub_le_sq
#print axioms Analysis.RsinAux_upper_le
#print axioms Analysis.RsinAux_lower_ge
#print axioms Analysis.Rexp_RlogNat
#print axioms Analysis.Rnonneg_RlogNat
#print axioms Analysis.RlogNat_eq_logN
#print axioms Analysis.Rnonneg_deltaLogNat
#print axioms Analysis.deltaLogNat_le_recip
#print axioms Analysis.Rsub_neg_eq_add
#print axioms Analysis.Rmul_le_mul_of_abs
#print axioms Analysis.Rneg_mul_le_of_abs
#print axioms Analysis.oneSubCexp_re_upper
#print axioms Analysis.oneSubCexp_re_lower
#print axioms Analysis.oneSubCexp_im_upper
#print axioms Analysis.oneSubCexp_im_lower
#print axioms Analysis.Rmul_sub_two_sided
#print axioms Analysis.Rmul_add_two_sided
#print axioms Analysis.cpowNeg_diff_re_bound
#print axioms Analysis.cpowNeg_diff_im_bound
#print axioms Analysis.czEtaSum_two_eq_paired
#print axioms Analysis.czEtaPaired_re_diff_le
#print axioms Analysis.czEtaPaired_re_diff_ge
#print axioms Analysis.czEtaPaired_im_diff_le
#print axioms Analysis.czEtaPaired_im_diff_ge
#print axioms Analysis.cpowNeg_diff_re_tail
#print axioms Analysis.cpowNeg_diff_im_tail
#print axioms Analysis.Vterm_le_A_delta
#print axioms Analysis.etaU_le_ratio
#print axioms Analysis.A_eq_czetaExp
#print axioms Analysis.A_dyadic_le
#print axioms Analysis.Vterm_dyadic_le
#print axioms Analysis.deltaLogNat_sum_telescope
#print axioms Analysis.RsumRange_mono
#print axioms Analysis.RsumRange_smul
#print axioms Analysis.Vconst_den_pos
#print axioms Analysis.Vconst_num_nonneg
#print axioms Analysis.Vterm_block_le
#print axioms Analysis.logBlock_eq
#print axioms Analysis.Vterm_geo_block_le
#print axioms Analysis.etaB_le_geo
#print axioms Analysis.RsumRange_congr
#print axioms Analysis.EtaVSum_diff_eq_RsumRange
#print axioms Analysis.EtaVSum_block_geo_le
#print axioms Analysis.EtaVSum_tail
#print axioms Analysis.EtaVSum_tail_reindex
#print axioms Analysis.Rnonneg_Vterm
#print axioms Analysis.Rnonneg_etaVtermTerm
#print axioms Analysis.EtaVSum_mono
#print axioms Analysis.EtaVSum_tail_full
#print axioms Analysis.RsumRange_odd_le
#print axioms Analysis.etaPaired_sum_le_tail
#print axioms Analysis.czEtaPaired_re_tail
#print axioms Analysis.czEtaPaired_im_tail
#print axioms Analysis.eta_smallness_n
#print axioms Analysis.etaMidx_ge_N0
#print axioms Analysis.etaMidx_mono
#print axioms Analysis.etaMidx_two_pow
#print axioms Analysis.eta_Vconst_bound
#print axioms Analysis.etaLevel_ge_N0
#print axioms Analysis.etaMidx_ge_one
#print axioms Analysis.etaRe_tail_reindexed
#print axioms Analysis.etaIm_tail_reindexed
#print axioms Analysis.etaRe_RReg
#print axioms Analysis.etaIm_RReg
#print axioms Analysis.Ceta
#print axioms Analysis.cpowNeg_normSq
#print axioms Analysis.CnormSq_Cmul_ofReal
#print axioms Analysis.Pos_RlogNat_two
#print axioms Analysis.etaTwoPow_re
#print axioms Analysis.etaDenom_Pos_normSq
#print axioms Analysis.CzetaStrip
#print axioms Analysis.CzetaStrip_functional
#print axioms Analysis.RrpowPos
#print axioms Analysis.Pos_RrpowPos_of_nonneg
#print axioms Analysis.RrpowPos_add
#print axioms Analysis.Rnonneg_Rinv
#print axioms Analysis.Rinv_le_ofQ_Qinv
#print axioms Analysis.ofQ_le_digammaArg
#print axioms Analysis.digammaArg_witness
#print axioms Analysis.digamma_const_shift
#print axioms Analysis.digammaArg_sub_succ_eq
#print axioms Analysis.digamma_succ_mul_pos
#print axioms Analysis.digamma_Rinv_le
#print axioms Analysis.digammaPfac_bound
#print axioms Analysis.digammaTerm_abs_le
#print axioms Analysis.digamma_Rsub_Radd_left
#print axioms Analysis.digammaSum_diff_eq
#print axioms Analysis.digammaTailQ_den_pos
#print axioms Analysis.digammaTail_two_sided
#print axioms Analysis.digammaMidx_ge_one
#print axioms Analysis.digammaMidx_mono
#print axioms Analysis.digammaTailQ_Midx_le
#print axioms Analysis.digammaCore_RReg
#print axioms Analysis.Rinv_ofQ_sub_eq
#print axioms Analysis.Rnonneg_of_ofQ_le
#print axioms Analysis.Rsub_eq_mul_of_inv
#print axioms Analysis.Qsub_nat_den_pos
#print axioms Analysis.spougeSign_den_pos
#print axioms Analysis.ofQ_le_spougeBase
#print axioms Analysis.spougeBase_witness
#print axioms Analysis.etaEps_le
#print axioms Analysis.etaEps_den_pos
#print axioms Analysis.etaEps_num_pos
#print axioms Analysis.etaTau_den_pos
#print axioms Analysis.etaTau_num_pos
#print axioms Analysis.etaTau_add_num_pos
#print axioms Analysis.etaU_le_ratio_data
#print axioms Analysis.etaB_le_geo_data
#print axioms Analysis.EtaVSum_block_geo_data
#print axioms Analysis.CetaW
#print axioms Analysis.CetaW_half_wellTyped
#print axioms Analysis.CetaW_re_tendsTo
#print axioms Analysis.CetaW_im_tendsTo
#print axioms Analysis.RTendsTo_of_Req
#print axioms Analysis.CetaW_czEtaSum_re_tendsTo
#print axioms Analysis.CetaW_czEtaSum_im_tendsTo
#print axioms Analysis.etaRe_paired_tail_anchor
#print axioms Analysis.etaIm_paired_tail_anchor
#print axioms Analysis.CetaW_re_full_tendsTo
#print axioms Analysis.CetaW_im_full_tendsTo
#print axioms Analysis.CetaW_re_canonical
#print axioms Analysis.CetaW_im_canonical
#print axioms Analysis.digammaTerm_eq_factored
#print axioms Analysis.digammaTerm_one_eq_zero
#print axioms Analysis.digammaSum_one_eq_zero
#print axioms Analysis.RTendsTo_zero_of_Req_zero
#print axioms Analysis.digammaCore_one_eq_zero
#print axioms Analysis.Digamma_one_eq_neg_gamma
#print axioms Analysis.Rnonneg_RofNat
#print axioms Analysis.spougeGammaWitness
#print axioms Analysis.Pos_RrpowPos_of_nonneg_log
#print axioms Analysis.CzetaStripW
#print axioms Analysis.CzetaStripW_functional
#print axioms Analysis.etaDenom_cancel
#print axioms Analysis.CzetaStrip_half_nonvacuous
#print axioms Analysis.qpow_neg_den
#print axioms Analysis.qpow_neg_num_odd
#print axioms Analysis.qpow_neg_odd
#print axioms Analysis.Qneg_add
#print axioms Analysis.artTerm_neg
#print axioms Analysis.artSum_neg
#print axioms Analysis.artSum_le_two_arg
#print axioms Analysis.one_sub_sq_ge_half
#print axioms Analysis.artSum_ge_neg_two_arg
#print axioms Analysis.Rartanh_R_ge_two
#print axioms Analysis.Rnonneg_Rartanh_of_nonneg
#print axioms Analysis.tmap_ge_sub
#print axioms Analysis.Rnonneg_Rlog_seq_of_one_le
#print axioms Analysis.Rnonneg_Rlog_of_one_le
#print axioms Analysis.Rnonneg_RlogPos
#print axioms Analysis.Pos_RrpowPos_of_base_ge_one

-- v0.20.0 stage F, brick A1 (Square/Cohomology.lean): the canonical H¹-object.
-- HONEST REPAIR (task 2): H1 = (ℕ,succ,0) reclassified as free Frobenius-orbit SYNTAX/INDEXING, not a
-- Hilbert carrier. H1_phi_not_surjective: succ n ≠ 0 ⇒ succ not surjective ⇒ not invertible ⇒ not
-- unitary. The genuine unitary H¹ carrier is the open operator contract. Crux none.
#print axioms Square.H1_phi_not_surjective

-- HP OPERATOR CONTRACT (task 3, new Square/HilbertPolyaSpec.lean, ζ-free construction layer) +
-- CONDITIONAL BRIDGE (task 8, new Square/HilbertPolyaBridge.lean, the only HP module touching zeros).
-- The contract's predicates are now QUARANTINED under a Nominal prefix (NominalDense/NominalSymmetric/
-- NominalAdjointDomainEq/NominalClosable/NominalClosed/NominalEssSelfAdjoint/NominalSelfAdjoint/
-- NominalHasSelfAdjointGenerator/NominalTraceFormula) — NAMED OBLIGATIONS (defs, no audit line), NOT
-- operator-theoretic notions (vacuous on the axiom-free bundle). PROVED: specMap_orbit (orbit action = free H¹,
-- via H1_universal). BRIDGE (proved conditionals): transformedSpectrum_onLine (½+iμ on Re=½,
-- unconditional); riemannHypothesis_of_zeroInclusion (ZeroInclusion spec → RiemannHypothesisStrip);
-- rh_of_selfadjoint_and_inclusion (the literal on-line + inclusion form). Self-adjointness alone is
-- insufficient; SpectralCompleteness (stronger, spurious-spectrum exclusion) stated but unused. Crux none.
#print axioms Square.specMap_orbit
#print axioms Square.transformedSpectrum_onLine
#print axioms Square.riemannHypothesis_of_zeroInclusion
#print axioms Square.rh_of_selfadjoint_and_inclusion
-- HONESTY REPAIR (names must denote their objects): the HP predicates are VACUOUS on the axiom-free
-- bundle, now QUARANTINED under the Nominal prefix. zeroBundle_NominalSelfAdjoint PROVES inner≡0 (not an
-- inner product) satisfies NominalSelfAdjoint — so the name does NOT denote self-adjointness; a genuine
-- contract needs vector-space/inner-product axioms (the separate programme now begun in FinInnerProduct).
-- zeroInclusion_of_rh PROVES RH→ZeroInclusion, so the bridge's hypothesis is EQUIVALENT to RH. Crux none.
#print axioms Square.zeroBundle_NominalSelfAdjoint
#print axioms Square.zeroInclusion_of_rh
-- HP POSITIVE METRIC (task 4, new Square/HilbertPolyaMetric.lean, ζ-free). posForm c N = Σ_{i<N} c_i²
-- (the Euclidean/Hurwitz diagonal norm). posForm_nonneg (PSD) + posForm_definite (POSITIVE-DEFINITE:
-- ‖c‖²_N=0 ⇒ c_i=0 ∀ i<N, PROVED via sum-of-nonnegs-zero + Bishop square-definiteness). A genuine PD
-- metric — separate from the signed INDEFINITE atlasM observable and the rank-one PSD (not PD) atlasNorm.
-- Composition (|xy|=|x||y|) and completion are further named obligations. Crux none.
#print axioms Square.posForm_nonneg
#print axioms Square.posForm_definite
-- Zeta-free real square-definiteness kernels (new Analysis/RealSquareDefinite.lean, ROrder/Real/QOrder
-- cone only), reused by both posForm and the complex IP space's PD proof.
#print axioms Analysis.Rnonneg_Rmul_self_loc
#print axioms Analysis.Radd_eq_zero_split
#print axioms Analysis.Rmul_self_eq_zero_imp
-- GENUINE FINITE COMPLEX INNER-PRODUCT SPACE (Fin N → ℂ, new Square/FinInnerProduct.lean) — replaces the
-- quarantined nominal contract with an ACTUAL sesquilinear positive-definite Hermitian inner product.
-- cInner x y = Σ conj(xᵢ)yᵢ: sesquilinear (add/smul both slots, conj-linear in 1st), Hermitian (cInner_conj),
-- POSITIVE-DEFINITE (self diagonal real+nonneg, and cInner_self_definite: ⟨x,x⟩=0 ⇒ x=0, via Bishop
-- square-definiteness), coherent embeddings preserving the inner product (cInner_embed). Crux none.
#print axioms Square.cvecSum_congr
#print axioms Square.cvecSum_add
#print axioms Square.cvecSum_smul
#print axioms Square.cvecSum_conj
#print axioms Square.cvecSum_im_zero
#print axioms Square.cvecSum_re_nonneg
#print axioms Square.cInner_add_right
#print axioms Square.cInner_add_left
#print axioms Square.cInner_smul_right
#print axioms Square.cInner_smul_left
#print axioms Square.cInner_conj
#print axioms Square.cInner_self_im_zero
#print axioms Square.cInner_self_re_nonneg
#print axioms Square.cInner_self_definite
#print axioms Square.cInner_embed
-- Setoid CVecEq + complex-module laws + inner-product congruence (the vector-space structure and
-- extensionality the raw finite form lacked): cInner descends to the quotient (cInner_congr).
#print axioms Square.CVecEq_refl
#print axioms Square.CVecEq_symm
#print axioms Square.CVecEq_trans
#print axioms Square.cvAdd_congr
#print axioms Square.cvSmul_congr
#print axioms Square.cvNeg_congr
#print axioms Square.cvAdd_comm
#print axioms Square.cvAdd_assoc
#print axioms Square.cvAdd_zero
#print axioms Square.cvAdd_neg
#print axioms Square.cvSmul_cvAdd
#print axioms Square.cvSmul_Cadd
#print axioms Square.cvSmul_assoc
#print axioms Square.cvSmul_one
#print axioms Square.cInner_congr
-- PACKAGED finite pre-Hilbert object (new Square/FinPreHilbert.lean): Setoid Complex/CVec instances,
-- CommRingoid (complex scalar ring, complexRingoid), the FinPreHilbert record instantiated at cInner
-- (finPreHilbert), zero-action laws, bundled definiteness, and the N≤M linear-isometry directed system
-- (cvInc + congr/add/smul/inner-preservation/identity/composition). Crux none.
#print axioms Square.cvSmul_zero
#print axioms Square.cvZero_smul
#print axioms Square.cInner_self_definite_vec
#print axioms Square.cvecSum_pad
#print axioms Square.cvInc_congr
#print axioms Square.cvInc_add
#print axioms Square.cvInc_smul
#print axioms Square.cvInc_inner
#print axioms Square.cvInc_id
#print axioms Square.cvInc_comp
#print axioms Square.cvInc_neg
-- FINITE-SUPPORT DIRECT LIMIT (new Square/FinDirectLimit.lean) — the FIRST real consumer of
-- finPreHilbert/cvInc: LinIsometry (bundled isometry) + cvIncIso; DLimRaw/DLimEq setoid colimit of the
-- cvInc system; dlimInner with STAGE/REPRESENTATIVE INDEPENDENCE (dlimInner_eval, dlimInner_wd —
-- consuming cvInc_inner); inclusions become identity in the limit (dlimMk_cvInc) so dlimInner extends
-- cInner (dlimInner_mk). Crux none.
#print axioms Square.DLimEq_refl
#print axioms Square.DLimEq_symm
#print axioms Square.DLimEq_trans
#print axioms Square.dlimInner_eval
#print axioms Square.dlimInner_wd
#print axioms Square.dlimMk_cvInc
#print axioms Square.dlimInner_mk
-- The direct limit COMPLETED into a packaged Bishop pre-Hilbert object (dlimPreHilbert : FinPreHilbert):
-- limit ops (dlimAdd/dlimSmul/dlimNeg/dlimZero) well-defined against DLimEq, the complex-module laws, and
-- the sesquilinear/Hermitian/positivity/definiteness inner-product laws (inner laws DERIVED from stagewise
-- finPreHilbert). Crux none.
#print axioms Square.dlimAdd_incl
#print axioms Square.dlimNeg_wd
#print axioms Square.dlimSmul_wd
#print axioms Square.dlimAdd_wd
#print axioms Square.dlimAdd_comm
#print axioms Square.dlimAdd_assoc
#print axioms Square.dlimAdd_zero
#print axioms Square.dlimAdd_neg
#print axioms Square.dlimSmul_dlimAdd
#print axioms Square.dlimSmul_Cadd
#print axioms Square.dlimSmul_assoc
#print axioms Square.dlimSmul_one
#print axioms Square.dlimZero_smul
#print axioms Square.dlimSmul_zero
#print axioms Square.dlimInner_add_right
#print axioms Square.dlimInner_smul_right
#print axioms Square.dlimInner_conj
#print axioms Square.dlimInner_self_im
#print axioms Square.dlimInner_self_nonneg
#print axioms Square.dlimInner_self_definite
-- HP FINITE EVIDENCE (task-7 finite discharge, new Square/HilbertPolyaFinite.lean). finiteHP_symmetric:
-- the finite approximant finiteHP B N satisfies the contract's NominalSymmetric obligation at truncation N
-- (via applyN_self_adjoint) — discharges ONLY the finite symmetry rung; density/closability/closedness/
-- adjoint-domain/self-adjointness/Stone/trace/spectral rungs stay OPEN. Finite evidence (imports the
-- ζ-tainted finite machinery — separate from the ζ-free contract). Crux none.
#print axioms Square.finiteHP_symmetric
#print axioms Square.H1_orbit
#print axioms Square.H1_universal
#print axioms Square.H1_isFree
#print axioms Square.freeFrob_unique_upto_iso
#print axioms Square.orbitShift_succ
#print axioms Square.orbit_realizes_pencil

-- v0.20.0 stage F, bricks A2 + A3 (Square/WeilLattice.lean): trace datum + forced dictionary.
#print axioms Square.zmulR_zero
#print axioms Square.zmulR_one
#print axioms Square.zmulR_negTwo
#print axioms Square.zmulR_congr_coeff
#print axioms Square.RofInt_zero
#print axioms Square.hPair_symm
#print axioms Square.vanCyc_perp_Fh
#print axioms Square.vanCyc_perp_Fv
#print axioms Square.vanCyc_selfpair_gen
#print axioms Square.vanCyc_blind
#print axioms Square.vanCyc_selfpair
#print axioms Square.vanCyc_selfpair_built
#print axioms Square.intrinsicH1_dict
#print axioms Square.genuineSpectralSquare_lam
#print axioms Square.genuineSpectralSquare_dict

-- v0.20.0 stage F, Group B (Square/Forced.lean): the forced signature, the gate reads it.
#print axioms Square.genuine_vanCyc_normal
#print axioms Square.genuine_crux_equivalent
#print axioms Square.genuine_hodgeNeg_iff
#print axioms Square.genuine_evidence_head
#print axioms Square.genuine_crux_frontier
#print axioms Square.genuine_signature_satisfiable
#print axioms Square.genuine_iff_all_upTo
#print axioms Square.genuine_crux_frontier_located

-- v0.20.0 stage F, frontier brick (Analysis/Voros.lean): the Voros growth dichotomy, exclusivity.
#print axioms Analysis.cube_le_pow2
#print axioms Analysis.quad_lt_pow2
#print axioms Analysis.tempered_not_exp
#print axioms Analysis.exp_not_tempered
#print axioms Analysis.voros_at_most_one
#print axioms Analysis.voros_exactly_one

-- v0.20.0 stage F, frontier (Analysis/GammaTwo.lean): the second Stieltjes constant γ₂ — brick 1 (substrate).
#print axioms Analysis.lnSqOver_nonneg
#print axioms Analysis.lnSqSum_step
#print axioms Analysis.lnSqSum_mono
#print axioms Analysis.logCube_nonneg
#print axioms Analysis.Rsub_sub_sub
#print axioms Analysis.g2Seq_step_eq
#print axioms Analysis.cube_diff_identity
#print axioms Analysis.tri_sum_3a2
#print axioms Analysis.Rmul_third_three
#print axioms Analysis.e2_core
#print axioms Analysis.e2_ub_identity
#print axioms Analysis.e2Step_le_quad
#print axioms Analysis.e2_lb_identity
#print axioms Analysis.e2Step_ge_quad
#print axioms Analysis.e2Step_le_num
#print axioms Analysis.e2Step_ge_num

-- v0.20.0 stage F: the Real additive-group normalizer (Analysis/RAddNF.lean) — the UOR κ-form solution.
#print axioms Analysis.RsumL_nil
#print axioms Analysis.RsumL_cons
#print axioms Analysis.RsumL_cons_congr
#print axioms Analysis.RsumL_swap_head
#print axioms Analysis.RsumL_perm
#print axioms Analysis.RsumL_cancel_head
#print axioms Analysis.RsumL_cancel_cons
#print axioms Analysis.RsumL_cancel_anywhere
#print axioms Analysis.RsumL_append
#print axioms Analysis.RsumL_singleton
#print axioms Analysis.Radd_eq_RsumL
#print axioms Analysis.Radd_eq_RsumL3
#print axioms Analysis.RsumL_perm_map
#print axioms Analysis.RsumL_map_Rneg

-- v0.20.0 stage F: γ₂ dyadic-tail regularity → Rgamma2 (Analysis/GammaTwo.lean).
#print axioms Analysis.logSq_le_block
#print axioms Analysis.Qblock_upper
#print axioms Analysis.g2Seq_step_le_block
#print axioms Analysis.g2Seq_step_ge_block
#print axioms Analysis.Csum_step_eq
#print axioms Analysis.Csum_tail_le
#print axioms Analysis.g2Seq_diff_le_block
#print axioms Analysis.g2Seq_diff_ge_block
#print axioms Analysis.g2Seq_block_le
#print axioms Analysis.g2Seq_block_ge
#print axioms Analysis.WUsum_tail_le
#print axioms Analysis.WLsum_tail_le
#print axioms Analysis.g2Seq_diff_le_outer
#print axioms Analysis.g2Seq_diff_ge_outer
#print axioms Analysis.g2_lin2
#print axioms Analysis.g2_quad_lin
#print axioms Analysis.g2_domination
#print axioms Analysis.g2_domination_U
#print axioms Analysis.g2_T_le
#print axioms Analysis.g2_TU_le
#print axioms Analysis.g2_pair_le
#print axioms Analysis.g2_pair_ge
#print axioms Analysis.g2SeqDyadic_RReg
#print axioms Analysis.Rgamma2
#print axioms Analysis.Csum_den_pos
#print axioms Analysis.WUsum_den_pos
#print axioms Analysis.WLsum_den_pos

-- v0.20.0 stage F: Lever 1 — the Li/zero growth geometry (Analysis/ZeroGeometry.lean).
#print axioms Analysis.liRatio_diff_eq
#print axioms Analysis.liRatio_on_line
#print axioms Analysis.liRatio_left_of_line
#print axioms Analysis.liRatio_right_of_line
#print axioms Analysis.Req_of_Rsub_zero
#print axioms Analysis.half_add_half
#print axioms Analysis.allOnLine_ratios_one
#print axioms Analysis.dvp_band_admits_off_line

-- v0.20.0 stage F: λ₃ closed form on the constructive γ₂ (Analysis/LambdaThree.lean).
#print axioms Analysis.Reta2
#print axioms Analysis.nsmulR_congr
#print axioms Analysis.Rlambda3_arith
#print axioms Analysis.Rlambda3
#print axioms Analysis.genuineArith_three
#print axioms Analysis.genuineLam_three
#print axioms Analysis.etaThreeSlice

-- v0.22.0 crux frontier: λ₄ closed form on the constructive γ₃ (Analysis/LambdaFour.lean).
#print axioms Analysis.Reta3
#print axioms Analysis.Rlambda4_arith
#print axioms Analysis.Rlambda4
#print axioms Analysis.genuineArith_four
#print axioms Analysis.genuineLam_four
#print axioms Analysis.genuineArith_five
#print axioms Analysis.genuineLam_five
#print axioms Analysis.etaFourSlice

-- v0.20.0 stage F: the Real multiplicative normalizer (Analysis/RMulNF.lean) — κ-form companion of RAddNF.
#print axioms Analysis.RprodL_nil
#print axioms Analysis.RprodL_cons
#print axioms Analysis.RprodL_cons_congr
#print axioms Analysis.RprodL_swap_head
#print axioms Analysis.RprodL_perm
#print axioms Analysis.RprodL_append
#print axioms Analysis.RprodL_singleton
#print axioms Analysis.Rmul_eq_RprodL
#print axioms Analysis.Rmul_eq_RprodL3
#print axioms Analysis.RprodL_perm_map
#print axioms Analysis.Rmul_pair_eq_RprodL4
#print axioms Analysis.prod_sq_reassoc
#print axioms Analysis.prod_cross_reassoc

-- v0.20.0 stage F: the Li-term modulus growth law (Analysis/LiGrowth.lean) — ring engine end-to-end.
#print axioms Analysis.Radd_pair_eq_RsumL4
#print axioms Analysis.add4_perm1
#print axioms Analysis.add4_perm2
#print axioms Analysis.cancelC
#print axioms Analysis.regroupX
#print axioms Analysis.cnormSq_mul
#print axioms Analysis.cnormSq_one
#print axioms Analysis.cnormSq_npow
#print axioms Analysis.Rnpow_nonneg
#print axioms Analysis.Rnpow_le_Rnpow
#print axioms Analysis.cnormSq_nonneg
#print axioms Analysis.liTerm_dominates

-- the RH witness (Analysis/RHWitness.lean) — the conditional sum-of-nonnegatives form of λₙ.
#print axioms Analysis.Rnpow_congr
#print axioms Analysis.Rnpow_one
#print axioms Analysis.cnormSq_Cnpow_unit
#print axioms Analysis.cnormSq_Cnpow_le_one
#print axioms Analysis.witnessTerm_nonneg
#print axioms Analysis.witnessSum_nonneg
#print axioms Analysis.witnessSum_append
#print axioms Analysis.witnessSum_snoc
#print axioms Analysis.Cnsmul_congr
#print axioms Analysis.Cnsmul_one
#print axioms Analysis.Cnsmul_add
#print axioms Analysis.Cmul_Cnsmul
#print axioms Analysis.Cmul_CsumN
#print axioms Analysis.CsumN_congr_le
#print axioms Analysis.CsumN_shift
#print axioms Analysis.Cnpow_one_add_eq
#print axioms Analysis.Cnpow_one_sub_eq
#print axioms Analysis.Cnpow_one_sub_momentPoly
#print axioms Analysis.witnessTerm_moment
#print axioms Analysis.witnessSum_eq_neg_momentList
#print axioms Analysis.momentListPoly_swap
#print axioms Analysis.witnessSum_moment_order
#print axioms Analysis.momentListPoly_append
#print axioms Analysis.momentListPoly_snoc
#print axioms Analysis.reciprocalMomentPoly_eq_neg_u_cgeomSum
#print axioms Analysis.liRatio_eq_one_sub_inv
#print axioms Analysis.liRatio_npow_moment
#print axioms Analysis.liRatio_witnessTerm_moment
#print axioms Analysis.hadamard_witnessSum_moment
#print axioms Analysis.RarctanExt_value_eq
#print axioms Analysis.RarctanR_add_RarctanExt
#print axioms Analysis.moment_re_eq_arithTail
#print axioms Analysis.witnessSum_eq_genuineArith
#print axioms Analysis.witnessSum_eq_genuineLam
#print axioms Analysis.traceBridge_one
#print axioms Analysis.momentList_eq_binom_powerSum
#print axioms Analysis.witnessSum_eq_binom_powerSum
#print axioms Analysis.onLine_is_unit_modulus
#print axioms Analysis.rh_witness
#print axioms Analysis.rh_witness_onLine

-- the constructive Cayley transform (Analysis/CayleyMap.lean) — discharges the witness's
-- on-line unit-modulus antecedent from the geometry (|1−1/ρ|² = 1 when Re ρ = ½).
#print axioms Analysis.cnormSq_congr
#print axioms Analysis.cnormSq_recip
#print axioms Analysis.cnormSq_sub_one
#print axioms Analysis.cnormSq_liRatio_on_line

-- the per-zero Li linearization (Analysis/LiLinearize.lean) — the geometric factorization
-- 1−wⁿ = (1−w)·Σwᵏ exhibiting the moment 1/ρ; the explicit-formula framework's algebraic core.
#print axioms Analysis.cadd_congr
#print axioms Analysis.cneg_congr
#print axioms Analysis.cmul_congr
#print axioms Analysis.cadd_zero
#print axioms Analysis.czero_cadd
#print axioms Analysis.cmul_czero
#print axioms Analysis.cmul_cneg
#print axioms Analysis.cone_sub_npow_factor
#print axioms Analysis.witnessTerm_eq_linear
#print axioms Analysis.witnessSum_eq_linear

-- the functional-equation reflection at the Li growth-ratio level (Analysis/Reflection.lean).
#print axioms Analysis.cnormSq_Creflect
#print axioms Analysis.csubOneNormSq_Creflect
#print axioms Analysis.mirror_both_in_disk_iff
#print axioms Analysis.onLine_mirror_in_disk
#print axioms Analysis.cnormSq_Cconj
#print axioms Analysis.csubOneNormSq_Cconj
#print axioms Analysis.inClosedDisk_Cconj
#print axioms Analysis.symmetry_orbit_in_disk_iff
#print axioms Analysis.offLine_left_not_inClosedDisk
#print axioms Analysis.inClosedDisk_iff_geom
#print axioms Analysis.double_inj
#print axioms Analysis.onLine_of_ratios_eq
#print axioms Analysis.onLine_iff_ratios_eq
#print axioms Analysis.allInClosedDisk_iff_allOnLine
#print axioms Analysis.Pos_Rnpow
#print axioms Analysis.Pos_of_Pos_Rsub_one
#print axioms Analysis.offLine_term_grows
#print axioms Analysis.witnessTerm_tempered
#print axioms Analysis.voros_term_dichotomy

-- the Bombieri–Lagarias pipeline (Square/BLPipeline.lean) — witness wired to genuine λ, RH-forward.
#print axioms Analysis.Rnonneg_Rlim
#print axioms Square.bl_rh_implies_liNonneg
#print axioms Square.bl_rh_implies_liNonneg_ofZeros
#print axioms Square.liNonneg_implies_onLine
#print axioms Square.li_criterion
#print axioms Square.li_criterion_disk
#print axioms Square.atlas_coupling_analytic_face
#print axioms Square.hodgeIndex_iff_RH
#print axioms Square.hodgeIndex_iff_closedDisk
#print axioms Analysis.riemannHypothesisStrip_iff
#print axioms Square.hodgeIndex_iff_riemannHypothesis

-- the Riemann–Siegel center-slope obstruction (Analysis/RiemannSiegel.lean) — θ′(0) < 0, the
-- non-monotonicity Connes–Consani name as the barrier to semi-local Weil positivity. Obstruction,
-- not a route through it; crux none.
#print axioms Analysis.Rnonneg_RpiTmap
#print axioms Analysis.Rnonneg_Rlogπc
#print axioms Analysis.rsCenterSlope_neg

-- the archimedean kernel Re ψ(1/4+iτ/2) ASSEMBLED at the frontier point τ=10, and the two-sided
-- non-monotonicity of the Riemann–Siegel angle (Analysis/PsiLine.lean). The obstruction completed;
-- crux none.
#print axioms Analysis.corrCore
#print axioms Analysis.corrCore_ge_twelve
#print axioms Analysis.corrP_twelve_lower
#print axioms Analysis.corrCore_lower
#print axioms Analysis.psiLineRe5
#print axioms Analysis.corrT_eq_windowTerm_gain
#print axioms Analysis.psiLineRe5_lower
#print axioms Analysis.rsLineSlope10_pos
#print axioms Analysis.rsAngle_non_monotone
-- the parameterized kernel Re ψ(1/4+iτ/2) over s ∈ [0,25] and the monotone climb (θ convex).
#print axioms Analysis.corrCoreP
#print axioms Analysis.corrCoreP_mono
#print axioms Analysis.psiLineReP
#print axioms Analysis.psiLineReP_mono
#print axioms Analysis.corrCoreP_ge_partial
#print axioms Analysis.psiLineReP_16_lower
#print axioms Analysis.rsLineSlope16_pos
#print axioms Analysis.rsAngle_increasing_on_band
#print axioms Analysis.corrCoreP_zero
#print axioms Analysis.psiLineReP_zero
-- the s=1 kernel upper bound and the kernel-sign indefiniteness h₊(2) < 0 (toward α(2) < 0).
#print axioms Analysis.corrCoreP_one_upper
#print axioms Analysis.psiLineReP_one_upper
#print axioms Analysis.archKernel_at_two_below_logpi

-- v0.21.0 frontier: α(2) < 0 — Burnol's archimedean multiplier is INDEFINITE (Analysis/BurnolAlphaTwo.lean).
-- √2 ≤ 3/2 via the exp∘log inverse (sqrt2² = 2), then |cos|≤1 + h₊(2)<0 give the pointwise sign.
#print axioms Analysis.two_seq_pos
#print axioms Analysis.sqrt2_mul_self
#print axioms Analysis.sqrt2_le_three_halves
#print axioms Analysis.sqrt2_nonneg
#print axioms Analysis.burnolAlphaTwo_neg
-- v0.22.0 Track 2: the indefiniteness capstone — α takes both signs, so pointwise single-place
-- positivity is refuted (the Sonine projection, not pointwise α ≥ 0, is the resolution).
#print axioms Analysis.burnol_multiplier_indefinite
#print axioms Analysis.burnolAlpha_not_pointwise_nonneg
#print axioms Analysis.burnolAlpha_not_pointwise_nonpos

-- v0.20.0 stage F: γ₂≥−0.02 bracket evaluators (Analysis/GammaTwoBracket.lean) — parts (A),(B).
#print axioms Analysis.lnSqSumLo_den_pos
#print axioms Analysis.lnSqSumLo_le
#print axioms Analysis.logBound_ofQ_nonneg
#print axioms Analysis.logNsq_le
#print axioms Analysis.logCube_le
#print axioms Analysis.halfSqOver_le
#print axioms Analysis.half_add_self
#print axioms Analysis.resid_regroup
#print axioms Analysis.hSeq_step_eq
#print axioms Analysis.sStep_stage1
#print axioms Analysis.two_mul_eq
#print axioms Analysis.sq_binom2
#print axioms Analysis.three_mul_eq
#print axioms Analysis.two_plus_one
#print axioms Analysis.inner_merge

-- v0.20.0 stage F: γ₂≥−0.02 bracket (C2) — the s_p decomposition keystone (GammaTwoBracket.lean).
#print axioms Analysis.half_two_cancel
#print axioms Analysis.third_three_cancel
#print axioms Analysis.mul3_pull
#print axioms Analysis.decompForm_eq_RsumL
#print axioms Analysis.sub_add_cancel_real
#print axioms Analysis.partA_eq
#print axioms Analysis.partC_distrib
#print axioms Analysis.partC1
#print axioms Analysis.partC2
#print axioms Analysis.partC3
#print axioms Analysis.partC_eq
#print axioms Analysis.lhsForm_eq_RsumL
#print axioms Analysis.decomp_generic
#print axioms Analysis.sStep_decomp
#print axioms Analysis.dPlusQ_zero_eq_mid
#print axioms Analysis.C2_nonneg
#print axioms Analysis.logN_le_self
#print axioms Analysis.deltaLog_le_mid
#print axioms Analysis.dMinusU1_le
#print axioms Analysis.Rneg_Rsub_swap
#print axioms Analysis.bd_le_one
#print axioms Analysis.bR1_lower
#print axioms Analysis.dsq_self_le
#print axioms Analysis.dcube_self_le
#print axioms Analysis.R0_lower_clean
#print axioms Analysis.sStep_lower_clean
#print axioms Analysis.cube_dom_nat
#print axioms Analysis.hBA_qle
#print axioms Analysis.hAB_qle
#print axioms Analysis.sStep_lower_tele
#print axioms Analysis.hSeq_tele
#print axioms Analysis.Rsub_sub_self
#print axioms Analysis.hSeq_lower_const
#print axioms Analysis.hSeq_le_g2Seq
#print axioms Analysis.Rgamma2_ge_hSeq

-- v0.20.0 stage F: γ₂≥−0.02 bracket — (C4) telescoping tail + (C5) limit + the certified bracket.
#print axioms Analysis.Rsub_ofQ_ofQ
#print axioms Analysis.gBound2_den_pos
#print axioms Analysis.hSeq_ge_gBound2
#print axioms Analysis.gamma2_decide
#print axioms Analysis.Rgamma2_ge_neg002

-- v0.22.0 crux frontier: γ₃ UPPER bracket evaluators (Analysis/GammaThreeBracket.lean) — part (A),(B).
#print axioms Analysis.lnCubeSumUp_den_pos
#print axioms Analysis.lnCubeSum_le
#print axioms Analysis.logLowBound_ofQ_nonneg
#print axioms Analysis.logCube_ge
#print axioms Analysis.logQuartic_ge
#print axioms Analysis.lnCubeOver_ge
#print axioms Analysis.hSeq3_step_eq
#print axioms Analysis.half_three
#print axioms Analysis.quarter_six
#print axioms Analysis.quarter_four
#print axioms Analysis.three_merge
#print axioms Analysis.four_merge
#print axioms Analysis.six_merge
#print axioms Analysis.one_plus_three
#print axioms Analysis.three_plus_one
#print axioms Analysis.three_plus_three
#print axioms Analysis.Rmul_eq_RprodL4L
#print axioms Analysis.Rmul_eq_RprodL5L
#print axioms Analysis.cube_times_pair
#print axioms Analysis.pair_times_triple
#print axioms Analysis.single_times_sqpair
#print axioms Analysis.cube_binom
#print axioms Analysis.partA3_eq
#print axioms Analysis.W_collect
#print axioms Analysis.W_expand
#print axioms Analysis.partC3_eq
#print axioms Analysis.lhsForm3_eq_RsumL
#print axioms Analysis.decomp_generic3
#print axioms Analysis.sStep3_decomp
#print axioms Analysis.decompForm3_eq_RsumL

-- v0.21.0 stage G, brick S (the substrate): the finite-truncation PSD predicate `WeilPSD`,
-- its additive/rank-one structure, the embedding Gram (Gate B free), and the embedding bridge.
#print axioms Square.Rmul_RsumN_left
#print axioms Square.RsumN_mul_RsumN
#print axioms Square.Radd_rearrange4
#print axioms Square.RsumN_add
#print axioms Square.RsumN_zero
#print axioms Square.indic_eq_one
#print axioms Square.indic_eq_zero
#print axioms Square.RsumN_indic_mul
#print axioms Square.WeilPSD_congr
#print axioms Square.WeilPSD_zero
#print axioms Square.weilQuad_add
#print axioms Square.WeilPSD_add
#print axioms Square.rankOne_term_reassoc
#print axioms Square.WeilPSD_rankOne
#print axioms Square.WeilPSD_gramOf
#print axioms Square.WeilPSD_diag
#print axioms Square.embeds_to_hodgeNeg
#print axioms Square.embeds_to_liNonneg
#print axioms Square.realizesDiag_genuine_iff

-- THE FINITE-RANK IMPOSSIBILITY FENCE (Square/AngleEmbeddingBound.lean): a crux-directed LOCALIZATION —
-- converts "no fixed-dimension bounded-entry embedding realizes 2λₙ" into a kernel-checked theorem,
-- explaining WHY every finite atlas Gram is off-object. gramDiag_uniform_bound: entry-squares ≤ ofQ c
-- (uniform in n) ⟹ gramOf ι D n n ≤ RsumN(const c) D (an n-independent bound). realized_seq_uniformly
-- _bounded: hence any sequence such an embedding realizes is bounded uniformly in n — contrapositive: an
-- n-unbounded sequence (2λₙ ~ n log n, Voros) is not the diagonal of any fixed-D bounded-entry embedding.
-- trigEmb (free angle family θ, zero-free by TYPE per §6): the on-object sine-square shape; trigEmb_sq_le
-- (cos²≤1, sin²≤1) + trigGram_uniform_bound instantiate the fence. So the on-object certificate for the
-- unbounded 2λₙ must be INFINITE-rank (the Σ_ρ over zeros cannot be truncated). NON-SMUGGLING: uses only
-- cos,sin ∈ [−1,1]; makes NO claim about the sign of 2λₙ; sharpens the localization, does NOT close or
-- approach the crux. Step 4 = RH; crux fields stay none.
#print axioms Square.gramDiag_uniform_bound
#print axioms Square.realized_seq_uniformly_bounded
#print axioms Square.trigEmb_sq_le
#print axioms Square.trigGram_uniform_bound

-- THE ON-OBJECT SINE-SQUARE BLOCK (Square/SineSquareSOS.lean): the kernel-checked heart of the
-- finite-rank fence. sineSquarePair: (1−cos φ)² + sin²φ = 2 − 2cos φ, for a FREE angle φ (zero-free —
-- no zeros, no λ). On the critical line this is 2·(1−cos nθ), twice the per-zero Li term = the
-- RH-correct sum-of-two-squares block, so the on-object certificate for 2λₙ on the line is gramOf of
-- entries (1−cos nθ_ρ, sin nθ_ρ) ∈ [−2,2]; composed with the fence this pins it as infinite-rank. Pure
-- trig/algebra (Rmul_sub_distrib + Rcos_sq_add_sin_sq); makes NO claim about the sign or growth of 2λₙ.
-- Sharpens the localization; does NOT close the crux. Step 4 = RH; crux fields stay none.
#print axioms Square.sineSquarePair

-- THE ON-OBJECT ANGLE EMBEDDING DIAGONAL (Square/AngleGramDiagonal.lean): completes the on-object SOS
-- structure. angleEmb θ sends coordinate pairs to the sine-square block (1−cos nθ_k, sin nθ_k);
-- angleGram_diag: gramOf (angleEmb θ)(2m) n n = Σ_{k<m}(2 − 2cos nθ_k) exactly (RsumN pair-fold +
-- sineSquarePair). On the line (θ_k=arg(1−1/ρ_k)) this is 2λₙ = Σ_ρ 2(1−cos nθ_ρ), the on-object SOS
-- certificate; composed with the fence (gramDiag_uniform_bound) it is infinite-rank. FREE angle family
-- (zero-free by type §6); NO claim about the sign or growth of 2λₙ. Sharpens the localization; does NOT
-- close the crux. Step 4 = RH; crux fields stay none.
#print axioms Square.angleGram_diag

-- v0.21.0 stage G, brick G0b (the full primitive form): the symmetric form on the Frobenius
-- carrier, the genuine-diagonal forcing, the negative-PSD → Hodge bridge, and the inhabitants.
#print axioms Square.orbit_distinct
#print axioms Square.FullForm.diag_genuine
#print axioms Square.FullForm.negPSD_to_hodgeNeg
#print axioms Square.shiftOffDiag_symm

-- v0.21.0 stage G, brick G0a (the atlas rule + the §6 relocation): the zero-free rule type,
-- Gate B free, the growth pre-filter, and the Cayley relocation made formal at the match level.
#print axioms Square.atlasRule_gateB
#print axioms Square.atlasRule_growth_filter
#print axioms Square.Rdouble_inj
#print axioms Square.cayleyRatio_match_iff_onLine
#print axioms Square.cayley_relocation

-- v0.21.0 stage G, brick G0 (the numerical kill-test, throwaway pre-filter): the decidable
-- finite Gram-diagonal match test, with the growth-kill, the match-admission, and the §6 caveat.
#print axioms Square.killTest_admits_match
#print axioms Square.killTest_kills_wrong_growth
#print axioms Square.killTest_match_not_sufficient

-- v0.21.0 stage G, brick G1 (Gate A, the faithful match): the λ-free atlas pairing, Gate B free,
-- the match-is-RH identity, and the two-sided no-smuggling guards (satisfiable + can-fail).
#print axioms Square.atlasPair_psd
#print axioms Square.gateA_is_liNonneg
#print axioms Square.gateA_satisfiable
#print axioms Square.gateA_can_fail

-- v0.21.0 stage G, brick G2a (the E₈ seed): the ofQ-embedding-Gram reduction, and the E₈ anchor
-- (PSD free, equal to 4× the standard E₈ Cartan matrix, strictly positive diagonal).
#print axioms Square.dotQ_den_pos
#print axioms Square.gramOf_ofQ
#print axioms Square.e8_weilPSD
#print axioms Square.e8_dot_check
#print axioms Square.e8_is_cartan
#print axioms Square.e8_target_diag_pos
#print axioms Square.e8_diag_pos

-- v0.21.0 stage G, bricks G2b.0/G2b.1 (the tower carries a form; infinite definiteness): the
-- negative-diagonal obstruction, the gauge tower (E₈ inhabitant), and the hypothesized Σ indefinite.
#print axioms Square.not_WeilPSD_of_neg_diag
#print axioms Square.limit_indefinite_of_neg_signature
#print axioms Square.sigmaMetric_not_psd

-- v0.21.0 stage G, brick G3 (assembly and adjudication): the missing-object embedding route,
-- located — the §9 Localized terminal state, crux fields stay none.
#print axioms Square.stageG_frontier_located
#print axioms Square.strictRealizes_closes_crux
#print axioms Square.strictRealizes_is_liCrux

-- v0.22.0 Track 2 — the Sonine projection (Square/SonineProjection.lean): the Weil multiplier form,
-- its diagonal collapse, positivity recovered UNCONDITIONALLY on the band complement, and the Burnol
-- instance (bare pairing indefinite; positive on the Sonine complement). The crux = the band coupling.
#print axioms Square.multForm_diag
#print axioms Square.RsumN_sift
#print axioms Square.weilQuad_multForm
#print axioms Square.multForm_psd_iff
#print axioms Square.multForm_psd_on_complement
#print axioms Square.burnol_pairing_indefinite
#print axioms Square.burnol_pairing_psd_on_sonine
#print axioms Square.burnol_sonine_dichotomy
-- Burnol's correction mechanism (the sharpest UNCONDITIONAL Weil-positivity theorem, discretized):
-- a correction making the multiplier pointwise ≥ 0 and vanishing on the window ⟹ window positivity.
#print axioms Square.multForm_psd_via_correction
#print axioms Square.burnol_corrected_nonneg
#print axioms Square.burnol_pairing_psd_via_correction
-- The coupled Weil kernel (Square/CoupledWeilKernel.lean): the OFF-DIAGONAL assembly closing the
-- step 3→4 diagonal-only gap — arch spectral square MINUS the prime Gram (von Mangoldt weights),
-- the quadratic SPLIT, unconditional prime-Gram PSD, and the honest capstone WeilPSD ⟺ dominance = RH.
#print axioms Square.weilQuad_sub
#print axioms Square.Rmul_pull2
#print axioms Square.weilQuad_scale
#print axioms Square.weilQuad_rankOne_eq
#print axioms Square.weilQuad_wRankOne
#print axioms Square.primeGram_sym
#print axioms Square.weilQuad_sumKernel
#print axioms Square.weilQuad_primeGram_split
#print axioms Square.WeilPSD_primeGram
#print axioms Square.WeilPSD_weilPrimeGram
#print axioms Square.weilQuad_coupledWeil_split
#print axioms Square.coupledWeil_psd_iff_dominates
-- Wiring the coupled kernel into the crux faces (Square/CoupledWeilCrux.lean): PSD/dominance ⟹
-- LiNonneg (sufficient half of the crux), and STRICT diagonal dominance ⟺ SpectralCrux.
#print axioms Square.coupledWeil_diag_eq
#print axioms Square.coupledWeil_psd_imp_hodgeNeg
#print axioms Square.coupledWeil_psd_imp_liNonneg
#print axioms Square.archDominatesPrime_imp_liNonneg
#print axioms Square.coupledWeil_diag_strict_iff_crux
-- The coupled form is antitone in the prime band (Square/CoupledWeilMono.lean): per-test dominance
-- atom + prime-energy monotone in M ⟹ coupled form antitone; no finite prime cutoff certifies it.
#print axioms Square.coupledWeil_quad_split
#print axioms Square.coupledWeil_quad_nonneg_iff
#print axioms Square.weilQuad_primeGram_mono
#print axioms Square.coupledWeil_quad_antitone_M
-- The coupled kernel as a self-adjoint operator (Square/CoupledWeilOperator.lean): symmetric,
-- self-adjoint, quadratic form = inner product against its action — the step-4 operator language.
#print axioms Square.coupledWeil_sym
#print axioms Square.coupledWeil_self_adjoint
#print axioms Square.coupledWeil_quad_eq_inner
-- The complement projection does not rescue the coupled kernel (Square/CoupledWeilComplement.lean):
-- on the Sonine complement the coupled form is (arch ≥0) − (prime ≥0), sign undetermined.
#print axioms Square.coupledWeil_complement_signed
#print axioms Square.coupledWeil_complement_lower
#print axioms Square.coupledWeil_complement_psd_iff
-- The coupled kernel welded to the genuine crux (Square/CoupledWeilGenuine.lean): under the
-- explicit-formula diagonal match, strict diagonal dominance ⟺ genuine SpectralCrux ⟺ coupling.
#print axioms Square.coupledWeil_diag_pos_iff_genuine_crux
#print axioms Square.coupledWeil_diag_pos_iff_genuine_coupling
#print axioms Square.genuineLam_eq_arch_sub_prime
-- The Gershgorin PSD certificate (Square/DiagDominant.lean): symmetric + diagonally dominant ⟹
-- WeilPSD, a new unconditional sqrt-free PSD class (AM-GM symmetrized); a sufficient-condition lever.
#print axioms Square.Rabs_mul_self
#print axioms Square.two_Rabs_mul_le
#print axioms Square.cross_term_lower
#print axioms Square.crossMass_eq_offMass
#print axioms Square.weilQuad_offdiag_lower
#print axioms Square.weilQuad_congr
#print axioms Square.offKernel_sym
#print axioms Square.offKernel_absRow
#print axioms Square.weilQuad_nonneg_of_diagDominant
#print axioms Square.WeilPSD_of_diagDominant
#print axioms Square.diagDominant_imp_nonneg_diag
-- The diagonal-dominance lever for the coupled kernel (Square/CoupledWeilDiagDominant.lean): concrete
-- prime-row-sum domination ⟹ DiagDominant ⟹ WeilPSD ⟹ LiNonneg (a bracket-checkable sufficient lever).
#print axioms Square.coupledWeil_offAbs_eq
#print axioms Square.coupledWeil_diagDominant_of_primeRowSum
#print axioms Square.coupledWeil_psd_of_diagDominant
#print axioms Square.coupledWeil_liNonneg_of_primeRowSum
-- The indefinite-arch obstruction (Square/CoupledWeilIndefinite.lean): a negative arch entry ⟹
-- ArchDominatesPrime false over all tests ⟹ coupled kernel not WeilPSD; the '=RH' needs the Sonine restriction.
#print axioms Square.archDominatesPrime_false_of_neg_arch
#print axioms Square.coupledWeil_not_psd_of_neg_arch
-- The Sonine co-support recovers coupled positivity (Square/CoupledWeilSonine.lean): on the co-support
-- subspace (prime energy = 0) intersect the arch complement, the coupled form is arch >= 0.
#print axioms Square.weilQuad_primeGram_prime_null
#print axioms Square.coupledWeil_psd_on_sonine_restriction
#print axioms Square.coupledWeilCorrected_psd_on_primeNull
#print axioms Square.coupledWeilBurnol_psd_on_primeNull
-- The coupled Weil dichotomy (Square/CoupledWeilDichotomy.lean): indefinite arch ⟹ not WeilPSD over
-- all tests, but ≥0 on the Sonine co-support subspace (the honest step-4 structure).
#print axioms Square.coupledWeil_sonine_dichotomy
#print axioms Square.not_Rnonneg_burnolAlphaTwo
#print axioms Square.coupledWeilBurnol_not_psd
#print axioms Square.coupledWeilBurnol_sonine_dichotomy
-- The multiplicative group action on tests (Square/MultShift.lean): dilateTest x↦a·x on L2Test, the
-- first structural prerequisite of the transform bridge the {n,1/n} point-model could not carry.
#print axioms Square.dilateTest_comp
#print axioms Square.dilateTest_one
#print axioms Square.logPull_dilate_shift
#print axioms Square.logPull_dilate_shift_comp
-- Grounding the coupled kernel's v in genuine test place-values (Square/CoupledWeilPlaceValue.lean):
-- placeVal IS the factor of the built weilPrimeTerm (definitional); vFrom feeds real place-values.
#print axioms Square.weilPrimeTerm_eq_placeVal
#print axioms Square.weilPrimePart_eq_placeVal_sum
#print axioms Square.primeGram_vFrom_apply
#print axioms Square.weilPrimeGram_vFrom_psd
#print axioms Square.primeGram_vFrom_sym

-- GROUNDING v=ĝ IN THE TRANSFORM (new Square/CoupledWeilVHat.lean). The coupled kernel intends v m i=ĝ_i(m)
-- (Mellin transform), not the point-value placeVal of vFrom. vHat g m i := mellinMoment (g i) m = ĝ_i(m)=∫₀¹g_i·xᵐ
-- feeds the genuine transform (zero-free): primeGram_vHat_apply gives weilPrimeGram(vHat g) M (i,j)=
-- Σ_m Λ(m+1)·ĝ_i(m)·ĝ_j(m); weilPrimeGram_vHat_psd (unconditional PSD, Λ≥0); primeGram_vHat_sym; and
-- primeGram_vHat_diag (the diagonal = Σ Λ(m+1)·ĝ_i(m)², the transform-domain prime energy the
-- autocorrelation-recovery law ties to weilPrimePart(g_i⋆g_i^τ) via Wall 3's factorization). Object-grounding;
-- does NOT prove weilPrimeGram(vHat)=autocorrelation prime side, NO coupled positivity, NO step-4 dominance
-- (ArchDominatesPrime), which is RH. Crux none.
#print axioms Square.primeGram_vHat_apply
#print axioms Square.weilPrimeGram_vHat_psd
#print axioms Square.primeGram_vHat_sym
#print axioms Square.primeGram_vHat_diag

-- v0.21.0 stage G — the UOR Atlas spectral operator (sourced Σ = {10,2,7,−1}, Atlas §5/§6.6):
-- verified spectrum/trace, the indefiniteness (the sourced make-or-break), and the definite norm.
#print axioms Square.blockEig_spectrum
#print axioms Square.atlasTrace_eq
#print axioms Square.atlasMult
#print axioms Square.atlasM_signature
#print axioms Square.atlasM_not_hodge_signature
#print axioms Square.atlasDim_eq
#print axioms Square.atlasM_neg_entry
#print axioms Square.atlasM_indefinite
#print axioms Square.atlasNorm_psd

-- THE ATLAS POSITIVITY STRUCTURE (new Square/AtlasPositivityStructure.lean) — the crux-closing
-- strategy's "understanding the positivity of the UOR Atlas", as theorems not prose. (1) The conserved
-- positivity BALANCE: atlasPosMass=38 (10·1+7·2+2·7), atlasReflMass=14 (1·14), atlasPositivity_balance:
-- posMass−reflMass = atlasTrace = T·O = 24 (the zero-state positivity invariant, refining the (10,14)
-- signature by eigenvalue-mass). (2) The DIFFERENCE-OF-PSD decomposition: atlasM = multForm posEig −
-- multForm reflEig (atlasM_eq_pos_sub_refl), both parts WeilPSD (atlasPos_psd/atlasRefl_psd via
-- multForm_psd_iff; posEig/reflEig nonneg) — the SAME shape as coupledWeil = multForm arch − primeGram,
-- and by atlasM_indefinite NOT PSD: the finite computable instance of the "difference of PSD need not be
-- PSD" phenomenon whose PSD-ness on genuine data is RH. Does NOT connect the definite parts to 2λₙ (§9
-- gap = RH, NOT made), asserts NO ArchDominatesPrime/WeilPSD of a genuine form. Crux none.
#print axioms Square.atlasPosMass_eq
#print axioms Square.atlasReflMass_eq
#print axioms Square.atlasPositivity_balance
#print axioms Square.atlasPosEig_nonneg
#print axioms Square.atlasReflEig_nonneg
#print axioms Square.atlasPos_psd
#print axioms Square.atlasRefl_psd
#print axioms Square.atlasM_eq_pos_sub_refl
-- The finite kernel witness: two PSD forms (multForm posEig/reflEig) whose DIFFERENCE (= atlasM) is NOT
-- PSD — atlasM_diff_not_psd (neg diagonal at reflection index 10, transported from atlasM_neg_entry) and
-- atlas_diff_of_psd_not_psd (the packaged ∧). The Atlas concretely/decidably realizes the crux's exact
-- phenomenon (coupledWeil = arch − prime, a difference of PSD whose PSD-ness on genuine data is RH). It
-- EXHIBITS why the crux is not automatic; does NOT close it. Crux none.
#print axioms Square.atlasM_diff_not_psd
#print axioms Square.atlas_diff_of_psd_not_psd

-- v0.21.0 stage G — gate sanity: the crux gate discriminates (accepts/rejects/closes-on-witness).
#print axioms Square.crux_gate_faithful

-- v0.21.0 stage G — Atlas characteristics (§1/§5/§10/§11) and the connection to the crux's
-- negative direction. Understanding the Atlas and its links to established mathematics.
#print axioms Square.tower_levels
#print axioms Square.O_eq_two_pow_T
#print axioms Square.self_intersection_tower
#print axioms Square.atlas_balance
#print axioms Square.g2_dim_match
#print axioms Square.twentyFour_eq
#print axioms Square.e8_theta_E4
#print axioms Square.atlas_negative_direction

-- v0.21.0 stage G — Atlas addressing (§2/§5/§8/§10/§12): the scale-invariant tower (inverse
-- system), parametric generation, and the prime skeleton = explicit-formula prime side.
#print axioms Square.atlasModulus_values
-- HONEST REPAIR (task 1): AtlasAddressing relabeled as a FINITE FIXTURE. atlasPrime_finite: the
-- prime table is 4 entries (0 for k≥4); atlasModulus_degenerate: the tower degenerates to 0 from k=5.
-- So no unbounded prime skeleton / no terminal A_∞; the fixture carries Λ for {2,3,5} only, not "in
-- full". The unbounded prime side is open. Crux none.
#print axioms Square.atlasPrime_finite
#print axioms Square.atlasModulus_degenerate
#print axioms Square.atlasModulus_zero_factored
#print axioms Square.atlasModulus_dvd_succ
#print axioms Square.atlasBoundary_zero
#print axioms Square.atlas_parametric_generation
#print axioms Square.primality_of_bounded
#print axioms Square.atlasPrime_five_vonMangoldt
#print axioms Square.atlas_prime_skeleton

-- v0.21.0 stage G — Atlas classes & calculus (§2/§3): the class structure (index, count, stride,
-- belt extent) and the transforms as finite-order class permutations.
#print axioms Square.class_count_stride
#print axioms Square.classIndex_range
#print axioms Square.belt_extent
#print axioms Square.sigma_order_four
#print axioms Square.tau_order_eight
#print axioms Square.mu_order_two

-- v0.21.0 stage G — Atlas conservation (§4/§5): no-loss, round-trip identity, scale-invariance.
#print axioms Square.class_no_loss
#print axioms Square.atlas_roundtrip
#print axioms Square.atlas_scale_consistent

-- v0.21.0 stage G — Atlas forcing: what makes a value NOT a coincidence (parametric identity or
-- over-determination), incl. the discovery that trace = dimension is forced by T = 3.
#print axioms Square.multSum_eq_dim
#print axioms Square.traceParam_formula
#print axioms Square.trace_eq_dim_at_T3
#print axioms Square.twentyFour_overdetermined
#print axioms Square.fourteen_overdetermined
#print axioms Square.twoForty_overdetermined
#print axioms Square.eight_overdetermined

-- v0.21.0 stage G — Atlas → RH connection: addressing↔orbit↔explicit-formula weight, and the
-- three live points where the Atlas feeds the RH program.
#print axioms Square.orbitShift_one
#print axioms Square.atlas_shift_eq_weight
#print axioms Square.atlas_feeds_rh

-- v0.21.0 stage G — Lefschetz coupling: the primitive-part refinement (H²>0, vanCyc primitive) and
-- the crux as the prime–archimedean coupling sign (the ff_hodge_iff_hasse shape over ℤ).
#print axioms Square.vanCyc_perp_H
#print axioms Square.eH_sq
#print axioms Square.eH_sq_pos
#print axioms Square.genuine_crux_arch_coupling
#print axioms Square.crux_is_arithmetic_hodge

-- v0.21.0 stage G — the archimedean place: the arch(n) facet of the coupling, conquered at the
-- head and in the prime-free window (α(0)>0), open outside (the tail bound).
#print axioms Square.coupling_head_positive
#print axioms Square.coupling_window_archimedean
#print axioms Square.archimedean_center_positive
#print axioms Square.archimedean_place_status

-- v0.21.0 stage G — Atlas modular: θ_{E₈^T} = E₄³ = E₆² + 1728Δ (the 24 = dim E₈^T thread to the
-- modular discriminant Δ = η²⁴), proved by power-series convolution over ℤ.
#print axioms Square.eisenstein_coeffs_computed
#print axioms Square.e4sq_is_conv
#print axioms Square.e4cube_eq_e6sq_plus_1728delta
#print axioms Square.delta_coeffs
#print axioms Square.twentyFour_modular

-- v0.21.0 stage G — Atlas exceptional: the magic-square exceptional series (R,C,H,O → F₄,E₆,E₇,E₈),
-- the rank·(h+1) dimension law, and the connections (dim G₂ = (T−1)(O−1), 240 = E₈ roots).
#print axioms Square.exceptional_dims
#print axioms Square.magic_square_octonion_row
#print axioms Square.g2_coxeter_atlas
#print axioms Square.e8_top
#print axioms Square.twoForty_roots

-- v0.21.0 stage G — Atlas Coxeter: E₈ exponents = totatives of the Coxeter number 30; rank = φ(30)
-- = 8 = O; the 30/8/120/240/248 forced web.
#print axioms Square.e8_exponents
#print axioms Square.e8_exponent_count
#print axioms Square.e8_exponent_sum
#print axioms Square.e8_coxeter_web

-- v0.21.0 stage G — Atlas synthesis: the forced web (no coincidences) + the honest open boundary.
#print axioms Square.atlas_forced_web
#print axioms Square.atlas_web_and_open_crux

-- v0.21.0 stage G — Atlas–crux localization: the Atlas insights connected to the crux; closing
-- it reduces to the prime-archimedean coupling sign for n≥3 (the archimedean place).
#print axioms Square.atlas_crux_localization

-- v0.21.0 stage G — crux frontier n=3: the next conquerable coefficient = Pos Rlambda3.
#print axioms Square.coupling_n3_iff_pos_lambda3
#print axioms Square.crux_frontier_n3

-- v0.22.0 crux frontier n=4: the next conquerable coefficient = Pos Rlambda4 (γ₃-bearing).
#print axioms Square.coupling_n4_iff_pos_lambda4
#print axioms Square.crux_frontier_n4
#print axioms Square.coupling_n5_iff_pos_lambda5
#print axioms Square.crux_frontier_n5

-- v0.21.0 stage G — uniform closure: closure is one structural fact, not enumeration (§2 thesis).
#print axioms Square.enumeration_insufficient
#print axioms Square.uniform_fact_closes
#print axioms Square.closure_is_uniform_not_enumeration

-- v0.21.0 stage G — Coxeter candidate: a §7 named uniform-rule candidate, killed by the growth
-- pre-filter (periodic order 30 ⟹ bounded ⟹ cannot match unbounded 2λₙ ~ n log n).
#print axioms Square.coxeter_candidate_killed
#print axioms Square.coxeter_candidate_periodic

-- v0.21.0 stage G — the Single Prime Hypothesis: the Atlas as one Prime object emanating all
-- structure; unity makes crux-closure uniform (one fact, not enumeration).
#print axioms Square.single_prime_binary
#print axioms Square.single_generator_emanates
#print axioms Square.sph_closure_is_uniform

-- v0.21.0 stage G — the atlas generator (candidate): the shift-length-facet uniform-rule
-- candidate; survives the growth filter (unbounded, n log n class) that killed Coxeter.
#print axioms Square.atlasShiftDiag_mono
#print axioms Square.atlasShiftDiag_step_ge_one
#print axioms Square.atlasGenerator_survives_growth
-- ATLAS SMOOTH-FACET n log n GROWTH CLASS (new Square/AtlasGrowth.lean). atlasShiftDiag_double_ge:
-- over a doubling window [n,2n) the atlas candidate grows by ≥ n·log(n+2) (RsumN_split_at window,
-- each term log(n+i+2)≥log(n+2) by logN_mono, RsumN_const+RsumN_le), i.e. SUPER-LINEAR = the n log n
-- class, sharpening the mere step≥1 unboundedness. Zero-free, atlas-intrinsic growth-filter calibration
-- (the 2λₙ~n log n necessary-condition side); does NOT connect to 2λₙ (that identity is RH), asserts no
-- positivity. Crux none.
#print axioms Square.atlasShiftDiag_double_ge

-- v0.21.0 stage G — coherence is the closure condition: the Atlas closes by coherence across all
-- facets (zero-state laws), not a single facet.
#print axioms Square.atlas_coherent
#print axioms Square.coherent_closure_not_single_facet

-- v0.21.0 stage G — Atlas composition algebras: the multiplicative norm at the tower levels (the
-- 2-, 4-, 8-square identities, Hurwitz) — the §6.3/§9 closed positivity.
#print axioms Square.two_square
#print axioms Square.four_square
#print axioms Square.eight_square
#print axioms Square.composition_tower

-- v0.21.0 stage G — Atlas topology: the Betti signature (§6.5, reduced homology rank 1) and
-- Bott/Clifford periodicity (§10); the tower forced four ways.
#print axioms Square.betti_signature
#print axioms Square.bott_periods
#print axioms Square.tower_forced_four_ways

-- v0.21.0 stage G — Atlas calculus: the seven operators, the free-monoid Term, and the
-- catamorphism with its universal property (§3/§4) — form determines function.
#print axioms Square.op_count
#print axioms Square.term_assoc
#print axioms Square.term_unit_left
#print axioms Square.term_unit_right
#print axioms Square.cata_append
#print axioms Square.cata_unique

-- v0.21.0 stage G — the complete UOR Atlas: the roll-up of every facet formalized, crux open.
#print axioms Square.atlas_complete
#print axioms Analysis.Rmul_right_cancel
#print axioms Analysis.Rdiv_mul_cancel
#print axioms Analysis.vvalrel_alg
#print axioms Analysis.vvalReal_rel_via
#print axioms Analysis.ratio_cross_via
#print axioms Analysis.Carg_add
#print axioms Analysis.Clog_add
#print axioms Analysis.RexpReal_eq_one_imp_zero
#print axioms Analysis.RexpReal_inj_gen
#print axioms Analysis.Rexp_log_ratQ
#print axioms Analysis.reindex_Req
#print axioms Analysis.Rlog_congr
#print axioms Analysis.RlogPos_unfold
#print axioms Analysis.RlogPos_eq_Rlog
#print axioms Analysis.RlogPos_mul
#print axioms Analysis.ge1_pos_witness
#print axioms Analysis.RlogPos_congr
#print axioms Analysis.RlogPos_cnormSq_mul
#print axioms Analysis.Clog_add_bounded
#print axioms Analysis.Rartanh_neg
#print axioms Analysis.RartanhConst_neg
#print axioms Analysis.TwoArtanhConst_neg
#print axioms Analysis.Rexp_TwoArtanh_of_neg
#print axioms Analysis.Rexp_TwoArtanh_signed_rho
#print axioms Analysis.Req_add_of_exp_values_gen
#print axioms Analysis.wvalR_hg
#print axioms Analysis.TwoArtanh_add_wvalR_rho
#print axioms Analysis.RartanhConst_add_wvalR_rho
#print axioms Analysis.Rartanh_add_real_via_signed
#print axioms Analysis.tmap_abs_lt_one
#print axioms Analysis.Rlog_mul_via_signed
#print axioms Analysis.wvalR_tmap_seq_bound_signed
#print axioms Analysis.Rlog_mul_signed
#print axioms Analysis.RlogPos_mul_signed
#print axioms Analysis.pos_witness_of_mulM_ge
#print axioms Analysis.RlogPos_cnormSq_mul_signed
#print axioms Analysis.Clog_add_signed
#print axioms Analysis.geoEvenSum_le_gen
#print axioms Analysis.Rartanh_congr_gen
#print axioms Analysis.artSum_depth_recip_gen
#print axioms Analysis.Rartanh_radius_indep_gen
#print axioms Analysis.Rlog_congr_gen
#print axioms Analysis.RlogPos_eq_Rlog_gen
#print axioms Analysis.RlogPos_congr_gen
#print axioms Analysis.wval_csq_le_gen
#print axioms Analysis.wval_halfbound_gen
#print axioms Analysis.wval_inner_pos_gen
#print axioms Analysis.wval_lip1_gen
#print axioms Analysis.wval_lip2_gen
#print axioms Analysis.artSum_wval_argdiff_gen
#print axioms Analysis.Rartanh_add_real_via_gen
#print axioms Analysis.tmul_wvalReal_via_gen
#print axioms Analysis.Rlog_mul_via_gen
#print axioms Analysis.Rlog_mul_gen
#print axioms Analysis.RlogPos_mul_gen
#print axioms Analysis.RlogPos_cnormSq_mul_gen
#print axioms Analysis.Clog_add_gen

-- Argument axis: tan(π/4)=1 and the π/2 values (full-range Carg/Clog anchors).
#print axioms Analysis.sin_eq_cos_pi4
#print axioms Analysis.Rcos_pi_half
#print axioms Analysis.Rsin_pi_half
#print axioms Analysis.Rcos_pi
#print axioms Analysis.Rsin_pi
#print axioms Analysis.Rsin_add_pi
#print axioms Analysis.Rcos_add_pi
#print axioms Analysis.CargLeft_tan
#print axioms Analysis.Cneg_Cmul_left
#print axioms Analysis.CargLeft_add
#print axioms Analysis.CdigammaArg_re
#print axioms Analysis.CdigammaArg_im
#print axioms Analysis.ofQ_le_CnormSq_CdigammaArg
#print axioms Analysis.CdigammaArg_witness
#print axioms Analysis.CdigammaTerm_re
#print axioms Analysis.CdigammaTerm_im
#print axioms Analysis.Cadd_neg_eq_mul_of_inv
#print axioms Analysis.Cmul_natSucc_inv
#print axioms Analysis.CdigammaArg_sub_succ_eq
#print axioms Analysis.CdigammaTerm_factored
#print axioms Analysis.CdigammaPfac_re_eq
#print axioms Analysis.CdigammaPfac_re_bound
#print axioms Analysis.CnormSq_CdigammaArg_ge
#print axioms Analysis.CdigammaPfac_im_eq
#print axioms Analysis.CdigammaPfac_im_bound
#print axioms Analysis.CdigammaTerm_re_bound
#print axioms Analysis.CdigammaTerm_im_bound
#print axioms Analysis.genSum_diff_eq
#print axioms Analysis.genTail_two_sided
#print axioms Analysis.genSum_RReg
#print axioms Analysis.CdigammaReSum_RReg
#print axioms Analysis.CdigammaImSum_RReg
#print axioms Analysis.ofQ_le_cnormSq_CspougeBase
#print axioms Analysis.CspougeBase_cnormSq_witness
#print axioms Analysis.CspougeBase_re_witness
#print axioms Analysis.Rcos_sub
#print axioms Analysis.Rsin_pi_half_sub
#print axioms Analysis.Rcos_pi_half_sub
#print axioms Analysis.Rsin_cos_pi_half_sub_tan
#print axioms Analysis.Rsin_cos_pi_half_sub_tan_real
#print axioms Analysis.tan_pi_half_sub_arctan_eighteen
#print axioms Analysis.Carg_I
#print axioms Analysis.CargUpper_tan
#print axioms Analysis.Rdiv_congr
#print axioms Analysis.Carg_congr
#print axioms Analysis.swapC_re
#print axioms Analysis.swapC_im
#print axioms Analysis.swapC_Cmul_Cconj
#print axioms Analysis.Rsub_radd_neg_regroup
#print axioms Analysis.CargUpper_add
#print axioms Analysis.ClogUpper_add
#print axioms Analysis.CargLower_tan
#print axioms Analysis.Cconj_Cmul
#print axioms Analysis.CargUpper_congr
#print axioms Analysis.CargLower_add
#print axioms Analysis.Cadd_congr_loc
#print axioms Analysis.Cmul_congr_loc
#print axioms Analysis.Cpow_re
#print axioms Analysis.Cpow_add_exp
#print axioms Analysis.Cpow_mul_base
#print axioms Analysis.Rcos_RarctanR_nested
#print axioms Analysis.Rsin_RarctanR_nested
#print axioms Analysis.RarctanR_value_eq
#print axioms Analysis.arctanTerm_neg
#print axioms Analysis.arctanSum_neg
#print axioms Analysis.RarctanR_neg
#print axioms Analysis.ClogUpper_re
#print axioms Analysis.ClogUpper_im
#print axioms Analysis.ClogUpper_I_im
#print axioms Analysis.ClogLower
#print axioms Analysis.ClogLower_re
#print axioms Analysis.ClogLower_im
#print axioms Analysis.ClogLower_eq_conj_ClogUpper
#print axioms Analysis.cnormSq_Cneg
#print axioms Analysis.ClogLeft
#print axioms Analysis.ClogLeft_re
#print axioms Analysis.ClogLeft_im
#print axioms Analysis.ClogLeft_eq_Clog_Cneg_add_pi
#print axioms Analysis.ClogLower_add
#print axioms Analysis.ClogLeft_add
#print axioms Analysis.addsub_linear_b
#print axioms Analysis.sq_diff_identity_b
#print axioms Analysis.add_sub_add_cancel_left
#print axioms Analysis.hSeq1_step_eq
#print axioms Analysis.step_regroup
#print axioms Analysis.WStep_ge_negDsq_gen
#print axioms Analysis.two_delta_le
#print axioms Analysis.WStep_ge_negDsq
#print axioms Analysis.WStep_ge
#print axioms Analysis.sStep1_ge
#print axioms Analysis.hSeq1_step_ge
#print axioms Analysis.hSeq1_diff_ge_U
#print axioms Analysis.hSeq1_diff_ge
#print axioms Analysis.hSeq1_lower_const
#print axioms Analysis.hSeq1_le_gSeq
#print axioms Analysis.Rgamma1_ge_hSeq1
#print axioms Analysis.lnSumLo_den_pos
#print axioms Analysis.lnSum_ge_lnSumLo
#print axioms Analysis.gBound1lo_den_pos
#print axioms Analysis.hSeq1_ge_gBound1lo
#print axioms Analysis.gamma1_lo_decide
#print axioms Analysis.Rgamma1_ge_neg0762
#print axioms Analysis.zetaSum2_perstep_ge
#print axioms Analysis.zetaSum2_tail_ge
#print axioms Analysis.zeta2_ge_partial_tail
#print axioms Analysis.zetaSum_two_70_tail_ge
#print axioms Analysis.zeta2_lower_tight
#print axioms Analysis.cLowQ_den_pos
#print axioms Analysis.cApprox_ge_cLowQ
#print axioms Analysis.gammaLoBound_den_pos
#print axioms Analysis.gammaLoBound_le_Ssum
#print axioms Analysis.Ssum_cLowQ_le_gammaHseq
#print axioms Analysis.dPlusQ_one_eq
#print axioms Analysis.gcf_le
#print axioms Analysis.gcfDen_pos
#print axioms Analysis.dPlusQ_one_le
#print axioms Analysis.Qle_sub_swap
#print axioms Analysis.cLowQ_one_tail_lower
#print axioms Analysis.cApprox_tail_lower
#print axioms Analysis.Ssum_cApprox_tail
#print axioms Analysis.gammaHseq_ge_partial_tail
#print axioms Analysis.Rgamma_h_ge_of_witness
#print axioms Analysis.gammaLo_decide
#print axioms Analysis.Rgamma_h_ge_577
#print axioms Analysis.cApprox_antitone
#print axioms Analysis.cApprox_zero_eq
#print axioms Analysis.cApprox_tail_upper
#print axioms Analysis.gammaHiBound_den_pos
#print axioms Analysis.Ssum_le_gammaHiBound
#print axioms Analysis.Ssum_cApprox_tail_upper
#print axioms Analysis.gammaHseq_le_partial_tail
#print axioms Analysis.Rgamma_h_le_of_witness
#print axioms Analysis.gammaHi_decide
#print axioms Analysis.Rgamma_h_le_578
#print axioms Analysis.Rgamma_sq_le
#print axioms Analysis.Rgamma_sq_ge
#print axioms Analysis.Rgamma_cube_ge
#print axioms Analysis.Rgamma_gamma1_ge
#print axioms Analysis.Rlog4pic_le
#print axioms Analysis.nsmulR3_le_mul3
#print axioms Analysis.archI_ge
#print axioms Analysis.archII_ge
#print axioms Analysis.archTerm2_ge
#print axioms Analysis.archTerm3_ge
#print axioms Analysis.genuineArchSeq3_ge
#print axioms Analysis.reta0_le
#print axioms Analysis.reta1_le
#print axioms Analysis.Rgamma_h_nonneg
#print axioms Analysis.archLoQ_den_pos
#print axioms Analysis.arithLoQ_den_pos
#print axioms Analysis.arithSupQ_den_pos
#print axioms Analysis.gloCubeQ_den_pos
#print axioms Analysis.half_m3xu_den_pos
#print axioms Analysis.iilq_den_pos
#print axioms Analysis.ilq_den_pos
#print axioms Analysis.m3reta1_den_pos
#print axioms Analysis.m3xu_den_pos
#print axioms Analysis.reta1UpQ_den_pos
#print axioms Analysis.reta2UpQ_den_pos
#print axioms Analysis.xuQ_den_pos
#print axioms Analysis.reta2_le
#print axioms Analysis.reta1_le_r
#print axioms Analysis.Rlambda3_arith_ge_r
#print axioms Analysis.archLoR_le
#print axioms Analysis.Rlambda3_pos
#print axioms Square.coupling_n3_positive
#print axioms Analysis.zetaSum_four_70_ge
#print axioms Analysis.zeta4_lower
#print axioms Analysis.zetaU_four_70_le
#print axioms Analysis.zeta4_upper
#print axioms Analysis.zetaSum_five_70_ge
#print axioms Analysis.zeta5_lower
#print axioms Analysis.zetaU_five_70_le
#print axioms Analysis.zeta5_upper
#print axioms Analysis.lnCubeOver_nonneg
#print axioms Analysis.lnCubeSum_step
#print axioms Analysis.lnCubeSum_mono
#print axioms Analysis.logQuartic_nonneg
#print axioms Analysis.g3Seq_step_eq
#print axioms Analysis.Rmul_left_comm3
#print axioms Analysis.quartic_diff_identity
#print axioms Analysis.Rmul_fourth_four
#print axioms Analysis.cube_mono
#print axioms Analysis.W3_ge_4b3
#print axioms Analysis.W3_le_4a3
#print axioms Analysis.quarter_diff_le
#print axioms Analysis.e3Step_ge_num
#print axioms Analysis.quarter_diff_ge
#print axioms Analysis.Rthree_mul
#print axioms Analysis.e3Step_le_num
#print axioms Analysis.logCube_le_block
#print axioms Analysis.g3Seq_step_le_block
#print axioms Analysis.g3Seq_step_ge_block
#print axioms Analysis.g3Seq_diff_le_block
#print axioms Analysis.g3Seq_diff_ge_block
#print axioms Analysis.g3Seq_block_le
#print axioms Analysis.g3Seq_block_ge
#print axioms Analysis.gamma3Midx_mono
#print axioms Analysis.g3_linU
#print axioms Analysis.g3_quad_lin
#print axioms Analysis.g3_domination_U
#print axioms Analysis.g3_TU_le
#print axioms Analysis.g3_linL
#print axioms Analysis.g3_quadincL
#print axioms Analysis.g3_cube_lin
#print axioms Analysis.g3_domination_L
#print axioms Analysis.g3_TL_le
#print axioms Analysis.WUsum3_den_pos
#print axioms Analysis.WLsum3_den_pos
#print axioms Analysis.g3Seq_diff_le_outer
#print axioms Analysis.g3Seq_diff_ge_outer
#print axioms Analysis.WUsum3_tail_le
#print axioms Analysis.WLsum3_tail_le
#print axioms Analysis.g3_pair_le
#print axioms Analysis.g3_pair_ge
#print axioms Analysis.g3SeqDyadic_RReg
#print axioms Analysis.cube_prod_split
#print axioms Analysis.cube_le_cube
#print axioms Analysis.cube_le_27_exp
#print axioms Analysis.logCube_le_self27
#print axioms Analysis.Rsub_le_self
#print axioms Analysis.Rmul_nonpos_left
#print axioms Analysis.Rsub_nonpos_of_le
#print axioms Analysis.Rle_ofQ_num1
#print axioms Analysis.Radd_ofQ_same
#print axioms Analysis.C2_le
#print axioms Analysis.R0_le
#print axioms Analysis.b2R2_le
#print axioms Analysis.bR1_le
#print axioms Analysis.b3C2_le
#print axioms Analysis.sStep3_le
#print axioms Analysis.hSeq3_tele
#print axioms Analysis.hSeq3_upper_const
#print axioms Analysis.Rgamma3_le_dyadic
#print axioms Analysis.g3Seq_eq_hSeq3_add
#print axioms Analysis.logCube_le_cap
#print axioms Analysis.corr_le
#print axioms Analysis.Rgamma3_le_hSeq3
#print axioms Analysis.gBound3_den_pos
#print axioms Analysis.hSeq3_le_gBound3
#print axioms Analysis.corr_weaken50
#print axioms Analysis.gamma3_decide
#print axioms Analysis.Rgamma3_le

-- v0.22.0 crux frontier: γ₃ LOWER bracket (Analysis/GammaThreeLower.lean) — completes −1/20 ≤ γ₃ ≤ 1/8.
#print axioms Analysis.lnCubeSumLo_den_pos
#print axioms Analysis.lnCubeSum_ge
#print axioms Analysis.logQuartic_le
#print axioms Analysis.halfCubeOver_le
#print axioms Analysis.dquart_self_le
#print axioms Analysis.b3C2_ge
#print axioms Analysis.b2R2_ge
#print axioms Analysis.bR1_ge
#print axioms Analysis.R0_ge
#print axioms Analysis.sStep3_lower_clean
#print axioms Analysis.sStep3_lower_tele
#print axioms Analysis.hSeq3_tele_lo
#print axioms Analysis.hSeq3_lower_const
#print axioms Analysis.hSeq3_le_g3Seq
#print axioms Analysis.Rgamma3_ge_hSeq3
#print axioms Analysis.gBound3lo_den_pos
#print axioms Analysis.hSeq3_ge_gBound3lo
#print axioms Analysis.gamma3_lo_decide
#print axioms Analysis.Rgamma3_ge_neg005
-- v0.22.0 crux frontier: γ₄ LOWER bracket (Analysis/GammaFourLower.lean) — `γ₄ ≥ −1/5`
-- (`Rgamma4_ge_neg02`), the LOOSE lower bracket sufficient for `Pos λ₅` (`γ₄` enters λ₅ only via the
--  small favourable `−(5/24)γ₄` term).  The loose `−1/5` target keeps the final big-integer `decide`
--  at `N = 245`, inside the default kernel stack (the tight `−1/20` would need N ≳ 830 + `--tstack`).
#print axioms Analysis.lnQuartSumLo_den_pos
#print axioms Analysis.lnQuartSum_ge
#print axioms Analysis.logQuintic_le
#print axioms Analysis.halfQuartOver_le
#print axioms Analysis.dquint_self_le
#print axioms Analysis.b4C2_ge
#print axioms Analysis.b3R3_ge
#print axioms Analysis.b2R2_ge4
#print axioms Analysis.bR1_ge4
#print axioms Analysis.R0_ge4
#print axioms Analysis.sStep4_lower_clean
#print axioms Analysis.sStep4_lower_tele
#print axioms Analysis.hSeq4_tele_lo
#print axioms Analysis.hSeq4_lower_const
#print axioms Analysis.hSeq4_le_g4Seq
#print axioms Analysis.Rgamma4_ge_hSeq4
#print axioms Analysis.gBound4lo_den_pos
#print axioms Analysis.hSeq4_ge_gBound4lo
#print axioms Analysis.gamma4_lo_decide
#print axioms Analysis.Rgamma4_ge_neg02
-- n=5 constant-precision brackets (Analysis/LambdaFivePrecision.lean) — tightened γ₁/γ₂/γ₃ + ζ(3)
-- for the `Pos λ₅` margin (large-N `decide`, via the lakefile `--tstack`).
#print axioms Analysis.corr_weaken500
#print axioms Analysis.gamma3_40_decide
#print axioms Analysis.Rgamma3_le_1_40
#print axioms Analysis.corr2_weaken400
#print axioms Analysis.gamma2_up_neg0003_decide
#print axioms Analysis.Rgamma2_le_neg0003
#print axioms Analysis.gamma2_ge_neg0014_decide
#print axioms Analysis.Rgamma2_ge_neg0014
#print axioms Analysis.corr1_weaken400
#print axioms Analysis.gamma1_up_neg069_decide
#print axioms Analysis.Rgamma1_le_neg069
#print axioms Analysis.zetaU_three_500_le
#print axioms Analysis.zeta3_le_1205

-- n=5 CLOSURE: Pos Rlambda5 (Analysis/LambdaFivePos.lean) — λ₅^arith_lo + arch(5)_lo → Pos λ₅.
#print axioms Analysis.Rgamma_sq_gamma1_le_t
#print axioms Analysis.Rgamma_gamma2_le_t
#print axioms Analysis.Rgamma_pow5_ge
#print axioms Analysis.Rgamma_cube_gamma1_ge
#print axioms Analysis.Rgamma_gamma1sq_ge
#print axioms Analysis.Rgamma_sq_gamma2_ge
#print axioms Analysis.Rgamma1_gamma2_ge
#print axioms Analysis.Rgamma_gamma3_ge
#print axioms Analysis.reta1_le5
#print axioms Analysis.reta2_le5
#print axioms Analysis.reta3_le5
#print axioms Analysis.reta4_le5
#print axioms Analysis.nsmulR5_le
#print axioms Analysis.nsmulR10_le
#print axioms Analysis.Radd6_ofQ_le
#print axioms Analysis.Rlambda5_S_le
#print axioms Analysis.Rlambda5_arith_ge_r
#print axioms Analysis.m5xu_den_pos
#print axioms Analysis.half_m5xu_den_pos
#print axioms Analysis.ilq5_den_pos
#print axioms Analysis.iilq5_den_pos
#print axioms Analysis.archLoQ5
#print axioms Analysis.archLoQ5_den_pos
#print axioms Analysis.archI5_ge
#print axioms Analysis.archTerm5_2_ge
#print axioms Analysis.archTerm5_3_ge
#print axioms Analysis.archTerm5_4_ge
#print axioms Analysis.archTerm5_5_ge
#print axioms Analysis.archII5_ge
#print axioms Analysis.genuineArchSeq5_ge
#print axioms Analysis.archLoR5_le
#print axioms Analysis.Rlambda5_pos
#print axioms Square.coupling_n5_positive
#print axioms Analysis.WStep_le_Dsq_gen
#print axioms Analysis.delta_ge_2over
#print axioms Analysis.sum_2delta_le
#print axioms Analysis.dsq_ge_4over
#print axioms Analysis.WStep_hkey
#print axioms Analysis.WStep_le_Dsq
#print axioms Analysis.sStep1_le
#print axioms Analysis.hSeq1_step_le
#print axioms Analysis.hSeq1_diff_le_U
#print axioms Analysis.hSeq1_diff_le
#print axioms Analysis.hSeq1_upper_const
#print axioms Analysis.Rgamma1_le_dyadic
#print axioms Analysis.gSeq_eq_hSeq1_add
#print axioms Analysis.logN_le_cap
#print axioms Analysis.corr1_le
#print axioms Analysis.Rgamma1_le_hSeq1_up
#print axioms Analysis.gBound1up_den_pos
#print axioms Analysis.hSeq1_le_gBound1up
#print axioms Analysis.corr1_weaken800
#print axioms Analysis.gamma1_up_decide
#print axioms Analysis.Rgamma1_le_neg0677
#print axioms Analysis.nat_succ_le_two_pow
#print axioms Analysis.Radd_sub_self_cancel
#print axioms Analysis.Rsub_add_swap
#print axioms Analysis.Rle_sub_zero
#print axioms Analysis.sq_le_sq
#print axioms Analysis.sq_le_4_exp
#print axioms Analysis.logSq_le_self4
#print axioms Analysis.b2C2_le
#print axioms Analysis.bR1_le_sq
#print axioms Analysis.R0_le_sq
#print axioms Analysis.sStep_le
#print axioms Analysis.hSeq_tele_up
#print axioms Analysis.hSeq_upper_const
#print axioms Analysis.Rgamma2_le_dyadic
#print axioms Analysis.g2Seq_eq_hSeq_add
#print axioms Analysis.logSq_le_cap
#print axioms Analysis.corr2_le
#print axioms Analysis.Rgamma2_le_hSeq2_up
#print axioms Analysis.lnSqSumUp_den_pos
#print axioms Analysis.lnSqSum_le
#print axioms Analysis.lnSqOver_ge
#print axioms Analysis.gBound2up_den_pos
#print axioms Analysis.hSeq2_le_gBound2up
#print axioms Analysis.corr2_weaken100
#print axioms Analysis.gamma2_up_decide
#print axioms Analysis.Rgamma2_le
#print axioms Analysis.ofQ_nonpos
#print axioms Analysis.Rmul_le_Rmul_right_nonpos
#print axioms Analysis.Rgamma_pow4_le
#print axioms Analysis.Rgamma_sq_gamma1_le
#print axioms Analysis.Rgamma1_sq_le
#print axioms Analysis.Rgamma_gamma2_le
#print axioms Analysis.reta1_le4
#print axioms Analysis.reta3_le
#print axioms Analysis.nsmulR4_le
#print axioms Analysis.nsmulR6_le
#print axioms Analysis.archI4_ge
#print axioms Analysis.archTerm4_2_ge
#print axioms Analysis.archTerm4_3_ge
#print axioms Analysis.archTerm4_4_ge
#print axioms Analysis.archII4_ge
#print axioms Analysis.genuineArchSeq4_ge
#print axioms Analysis.archLoR4_le
#print axioms Analysis.Rlambda4_arith_ge_r
#print axioms Analysis.Rlambda4_pos
#print axioms Analysis.Radd5_ofQ_le
#print axioms Analysis.Rlambda4_S_le
#print axioms Analysis.m4xu_den_pos
#print axioms Analysis.half_m4xu_den_pos
#print axioms Analysis.ilq4_den_pos
#print axioms Analysis.iilq4_den_pos
#print axioms Analysis.archLoQ4_den_pos
#print axioms Analysis.Clim_re
#print axioms Analysis.Clim_im
#print axioms Analysis.Clim_tendsTo
#print axioms Analysis.CTendsTo_unique
#print axioms Analysis.CTendsTo_Clim
#print axioms Analysis.Clim_congr
#print axioms Analysis.Clim_zero
#print axioms Analysis.Clim_add
#print axioms Analysis.Clim_add_of_approx
#print axioms Analysis.Clim_neg
#print axioms Analysis.CsumN_re
#print axioms Analysis.CsumN_im
#print axioms Analysis.CsumN_congr
#print axioms Analysis.CsumN_add
#print axioms Analysis.CsumN_neg
#print axioms Analysis.CprodN_congr
#print axioms Analysis.CprodN_succ_one
#print axioms Analysis.CprodN_mul
#print axioms Analysis.CsumN_re_fun
#print axioms Analysis.CsumN_im_fun
#print axioms Analysis.CsumConv_iff
#print axioms Analysis.Cseries_add
#print axioms Analysis.Clog_conj
#print axioms Analysis.Cpow_conj
#print axioms Analysis.Carg_conj
#print axioms Analysis.Clim_Cconj
#print axioms Analysis.Cconj_congr
#print axioms Analysis.Cconj_Cconj
#print axioms Analysis.Cconj_Cadd
#print axioms Analysis.Cconj_Cneg
#print axioms Analysis.Cconj_ofReal
#print axioms Analysis.Cconj_Czero
#print axioms Analysis.CsumN_Cconj
#print axioms Analysis.Cconj_Cone
#print axioms Analysis.ncpow_conj
#print axioms Analysis.cpowNeg_conj
#print axioms Analysis.etaTwoPow_conj
#print axioms Analysis.etaDenom_conj
#print axioms Analysis.Cinv_congr
#print axioms Analysis.etaDenomInv_conj
#print axioms Analysis.cpowNegDiff_conj
#print axioms Analysis.czEtaPaired_conj
#print axioms Analysis.Ceta_conj
#print axioms Analysis.CzetaStrip_conj
#print axioms Analysis.CspougeBracketWAux_conj
#print axioms Analysis.CspougeBracketW_conj
#print axioms Analysis.CSpougeGammaW_conj
#print axioms Analysis.Cxi_conj_built
#print axioms Analysis.Cneg_Cneg
#print axioms Analysis.cmul_cneg_cneg
#print axioms Analysis.oneSub_eq_neg_sub
#print axioms Analysis.oneSub_sub_one
#print axioms Analysis.CxiPoly_symm
#print axioms Analysis.Cxi_eq_poly_completed
#print axioms Analysis.Cxi_functional_equation
#print axioms Analysis.boundaryTerm
#print axioms Analysis.boundaryTerm_symm
#print axioms Analysis.CompletedZetaFE_of_MellinRep
#print axioms Analysis.oneSub_oneSub
#print axioms Analysis.oneSub_eq_conj_on_critical
#print axioms Analysis.CnegHalf_congr
#print axioms Analysis.CpiPow_congr
#print axioms Analysis.CxiPoly_congr
#print axioms Analysis.Cxi_congr
#print axioms Analysis.Cxi_real_on_critical_line
#print axioms Analysis.hadFactor_one_eq_liRatio
#print axioms Analysis.hadamard_factor_one_is_cayley
#print axioms Analysis.Cxi_zero_reflect
#print axioms Analysis.Cxi_zero_conj
#print axioms Analysis.Cxi_zero_conj_reflect
#print axioms Analysis.Cnpow_congr
#print axioms Analysis.witnessTerm_congr
#print axioms Analysis.witnessSum_mapidx_congr
#print axioms Analysis.witnessSum_hadFactor_eq_liRatio
#print axioms Analysis.hadamard_witnessSum_nonneg_on_line
#print axioms Analysis.hadFactor_zero
#print axioms Analysis.CprodN_const_one
#print axioms Analysis.hadamard_prod_zero
#print axioms Analysis.RexpReal_le_of_le
#print axioms Analysis.one_le_pi_mul
#print axioms Analysis.thetaArg_lower
#print axioms Analysis.thetaTerm_le
#print axioms Analysis.thetaTerm_RReg
#print axioms Analysis.Rnonneg_Rlim_theta
#print axioms Analysis.genSum_nonneg
#print axioms Analysis.thetaFn_nonneg
#print axioms Analysis.Rlim_le_Rlim
#print axioms Analysis.genSum_le
#print axioms Analysis.thetaArg_mono
#print axioms Analysis.thetaTerm_antitone
#print axioms Analysis.thetaFn_antitone
#print axioms Analysis.thetaTerm_congr
#print axioms Analysis.genSumTheta_congr
#print axioms Analysis.thetaFn_congr
#print axioms Analysis.three_le_pi_mul
#print axioms Analysis.thetaTerm_le2
#print axioms Analysis.genSum_boundTele
#print axioms Analysis.Rlim_le_ofQ
#print axioms Analysis.thetaFn_le_one
#print axioms Analysis.riemannSum_congr
#print axioms Analysis.RsumN_const
#print axioms Analysis.riemannSum_const
#print axioms Analysis.RsumN_Radd
#print axioms Analysis.riemannSum_le
#print axioms Analysis.riemannSum_nonneg
#print axioms Analysis.riemannSum_add
#print axioms Analysis.RsumN_Rneg
#print axioms Analysis.riemannSum_neg
#print axioms Analysis.RsumN_Rmul_const
#print axioms Analysis.riemannSum_smul
#print axioms Analysis.RsumN_split2
#print axioms Analysis.RsumN_Rsub
#print axioms Analysis.dyadic_even_point
#print axioms Analysis.Rabs_Radd
#print axioms Analysis.Rabs_zero
#print axioms Analysis.Rabs_ofQ_nonneg
#print axioms Analysis.Rle_of_Rabs_le
#print axioms Analysis.Rabs_Rneg
#print axioms Analysis.Rneg_le_of_Rabs_le
#print axioms Analysis.RsumN_Rabs_le
#print axioms Analysis.dyadic_pair_spacing
#print axioms Analysis.dyadic_pair_lip
#print axioms Analysis.riemannSum_refine
#print axioms Analysis.two_mul_env
#print axioms Analysis.qmul_den_anti
#print axioms Analysis.dyadicTerm_bound
#print axioms Analysis.dyadicSum_RReg
#print axioms Analysis.Radd_Rsub_Rsub
#print axioms Analysis.genSum_telescope
#print axioms Analysis.riemannIntegral_const
#print axioms Analysis.RReg_add_const
#print axioms Analysis.RTendsTo_add_const
#print axioms Analysis.Rlim_add_const
#print axioms Analysis.Rnonneg_Rlim_seq
#print axioms Analysis.Radd_Rsub_cancel
#print axioms Analysis.dyadicR_eq
#print axioms Analysis.riemannIntegral_nonneg
#print axioms Analysis.Rlim_le_seq
#print axioms Analysis.riemannIntegral_le
#print axioms Analysis.riemannIntegral_congr
#print axioms Analysis.genSum_Rneg_of_termwise
#print axioms Analysis.riemannIntegral_neg
#print axioms Analysis.genSum_Rmul_of_termwise
#print axioms Analysis.riemannIntegral_smul
#print axioms Analysis.RReg_Rneg
#print axioms Analysis.genSum_Radd_of_termwise
#print axioms Analysis.riemannIntegral_add
#print axioms Analysis.riemannIntegral_const_gen
#print axioms Analysis.Rabs_Rmul_ofQ_nonneg
#print axioms Analysis.affineMap_congr
#print axioms Analysis.affineMap_diff
#print axioms Analysis.affine_lip
#print axioms Analysis.riemannIntegralI_const
#print axioms Analysis.riemannIntegralI_nonneg
#print axioms Analysis.riemannIntegralI_le
#print axioms Analysis.riemannIntegralI_add
#print axioms Analysis.riemannIntegralI_neg
#print axioms Analysis.riemannIntegralI_smul
#print axioms Analysis.riemannIntegralI_congr
#print axioms Analysis.const_lip0
#print axioms Analysis.Cintegral_const
#print axioms Analysis.Qle_of_not_le
#print axioms Analysis.Qavg_le_right
#print axioms Analysis.Qavg_ge_left
#print axioms Analysis.sqrtBisect_den_pos
#print axioms Analysis.sqrtBisect_width
#print axioms Analysis.sqrtBisect_inv
#print axioms Analysis.sqLo_mono
#print axioms Analysis.sqLo_incr_le
#print axioms Analysis.sqrtK_den_pos
#print axioms Analysis.sqrtK_num_nonneg
#print axioms Analysis.sqrt_env_le
#print axioms Analysis.sqrtTerm_bound
#print axioms Analysis.Qle_of_sq_le
#print axioms Analysis.sqLo_le_sqHi_cross
#print axioms Analysis.genSum_sqrtTerm_eq
#print axioms Analysis.Rsqrt_nonneg
#print axioms Analysis.Rsqrt_le_sqHi
#print axioms Analysis.Rle_of_Rsub_le_eps
#print axioms Analysis.RTendsTo_Rsub_le
#print axioms Analysis.term_le_Rlim
#print axioms Analysis.genSum_mono
#print axioms Analysis.sqLo_mono_le
#print axioms Analysis.Rsqrt_ge_sqLo
#print axioms Analysis.Rsq_mono
#print axioms Analysis.Rsub_le_mono
#print axioms Analysis.sqHi_mono
#print axioms Analysis.sqHi_le_init
#print axioms Analysis.sqrt_sq_width_le
#print axioms Analysis.Rsqrt_sq
#print axioms Analysis.integralTerm
#print axioms Analysis.improperIntegral1
#print axioms Analysis.improperIntegral1_nonneg
#print axioms Analysis.genSum_le_genSum
#print axioms Analysis.improperIntegral1_le
#print axioms Analysis.halfLineIntegral
#print axioms Analysis.halfLineIntegral_nonneg
#print axioms Analysis.halfLineIntegral_le
#print axioms Analysis.improperIntegral1_congr
#print axioms Analysis.halfLineIntegral_congr
#print axioms Analysis.integralTerm_add
#print axioms Analysis.integralTerm_neg
#print axioms Analysis.integralTerm_smul
#print axioms Analysis.improperIntegral1_add
#print axioms Analysis.improperIntegral1_neg
#print axioms Analysis.improperIntegral1_smul
#print axioms Analysis.halfLineIntegral_add
#print axioms Analysis.halfLineIntegral_neg
#print axioms Analysis.halfLineIntegral_smul
#print axioms Analysis.Rle_of_Rsq_le_qpos
#print axioms Analysis.Rle_of_Rsq_le
#print axioms Analysis.Rsqrt_unique
#print axioms Analysis.Rsqrt_mono
#print axioms Analysis.Rsqrt_one
#print axioms Analysis.Rsqrt_ge_one
#print axioms Analysis.Rle_Rabs_self
#print axioms Analysis.Rabs_ofQ
#print axioms Analysis.Rabs_Rmul
#print axioms Analysis.Rsqrt_lipschitz
#print axioms Analysis.rsqrtRealSeq
#print axioms Analysis.rsqrtRealSeq_ge_one
#print axioms Analysis.rsqrtRealSeq_diff_le
#print axioms Analysis.rsqrtRealX_RReg
#print axioms Analysis.RsqrtReal
#print axioms Analysis.RsqrtReal_nonneg
#print axioms Analysis.rsqrtRealSeq_den_pos
#print axioms Analysis.rsqrtRealSeq_ge_zero
#print axioms Analysis.RTendsTo_gen_unique
#print axioms Analysis.rsqrtRealSeq_tendsTo
#print axioms Analysis.RTendsTo_Rabs_rate
#print axioms Analysis.Qle_self_mul_self_of_ge_one
#print axioms Analysis.Rabs_le_of_nonneg_le
#print axioms Analysis.rate_to_gen
#print axioms Analysis.rsqrtRealX_le
#print axioms Analysis.rsqrtRealX_abs_le
#print axioms Analysis.RsqrtReal_abs_le
#print axioms Analysis.RsqrtReal_sq
#print axioms Analysis.RsqrtReal_unique
#print axioms Analysis.Rmul_mul_mul_comm
#print axioms Analysis.RsqrtReal_mul
#print axioms Analysis.ChalfLineIntegral
#print axioms Analysis.ChalfLineIntegral_add
#print axioms Analysis.ChalfLineIntegral_neg
#print axioms Analysis.ChalfLineIntegral_smul
#print axioms Analysis.Cintegral_congr
#print axioms Analysis.ChalfLineIntegral_congr
#print axioms Analysis.RsqrtRealPos
#print axioms Analysis.RsqrtRealPos_nonneg
#print axioms Analysis.RsqrtRealPos_sq
#print axioms Analysis.pi_mul_ge_threeOverD
#print axioms Analysis.thetaArg_lower_pos
#print axioms Analysis.thetaTerm_le_pos
#print axioms Analysis.thetaTerm_RReg_pos
#print axioms Analysis.thetaFnPos
#print axioms Analysis.thetaFnPos_nonneg
#print axioms Analysis.ThetaModular
#print axioms Analysis.Rabs_Rhalf
#print axioms Analysis.Rabs_Rabs_sub_le
#print axioms Analysis.Rhalf_add_self
#print axioms Analysis.RmaxZero_lipschitz
#print axioms Analysis.clampOne
#print axioms Analysis.clampOne_ge_one
#print axioms Analysis.clampOne_eq_of_ge
#print axioms Analysis.clampOne_lipschitz
#print axioms Analysis.clampOne_congr
#print axioms Analysis.riemannIntegral_le_unit
#print axioms Analysis.riemannIntegralI_le_unit
#print axioms Analysis.genSum_Rmul_const
#print axioms Analysis.genSum_geom_eq
#print axioms Analysis.genSum_geom_le
#print axioms Analysis.thetaArg_succ
#print axioms Analysis.thetaTerm_ratio
#print axioms Analysis.Rlim_le_const
#print axioms Analysis.thetaTerm_geom
#print axioms Analysis.thetaFn_decay
#print axioms Analysis.RnatSucc
#print axioms Analysis.one_le_RnatSucc
#print axioms Analysis.Rnonneg_RnatSucc
#print axioms Analysis.Rmul_le_Rmul_both
#print axioms Analysis.thetaTerm0_value_le
#print axioms Analysis.thetaFn_value_decay
#print axioms Analysis.Rle_or_Rle
#print axioms Analysis.RexpReal_one_sub_neg_le_global
#print axioms Analysis.Rmul_self_exp_neg_le_one
#print axioms Analysis.Rle_RmaxZero_self
#print axioms Analysis.RmaxZero_le_Rabs
#print axioms Analysis.RexpReal_one_sub_neg_le_maxZero
#print axioms Analysis.thetaCoeff
#print axioms Analysis.thetaArg_eq_coeff
#print axioms Analysis.thetaCoeff_nonneg
#print axioms Analysis.thetaCoeff_lower
#print axioms Analysis.thetaCoeff_exp_le
#print axioms Analysis.Rabs_le_self_of_nonneg
#print axioms Analysis.Rabs_of_nonneg
#print axioms Analysis.Rabs_le_of_both
#print axioms Analysis.thetaTerm_eq_coeff
#print axioms Analysis.thetaTerm_one_eq
#print axioms Analysis.thetaTerm_diff_le
#print axioms Analysis.thetaTerm_lip
#print axioms Analysis.genSum_Rsub
#print axioms Analysis.genSum_Rmul_const_right
#print axioms Analysis.genSum_thetaMod_le
#print axioms Analysis.genSum_thetaDiff_le
#print axioms Analysis.thetaFn_diff_le
#print axioms Analysis.thetaFn_lip
#print axioms Analysis.thetaClamp
#print axioms Analysis.thetaClamp_congr
#print axioms Analysis.thetaClamp_lip
#print axioms Analysis.thetaClamp_nonneg
#print axioms Analysis.integralTerm_thetaClamp_le
#print axioms Analysis.thetaMellin1
#print axioms Analysis.thetaMellin1_nonneg
#print axioms Analysis.thetaTerm0_value_le2
#print axioms Analysis.thetaFn_value_decay2
#print axioms Analysis.integralTerm_thetaClamp_le2
#print axioms Analysis.thetaMellin1_le
#print axioms Analysis.RartanhAtQ_ge
#print axioms Analysis.RartanhAtQ_le
#print axioms Analysis.Rlog_le_sub_one
#print axioms Analysis.Rlog_ge_two_tmap
#print axioms Analysis.Rle_RexpReal_sub_one
#print axioms Analysis.Qadd_le_self_of_nonpos
#print axioms Analysis.qpow_two_mul_nonneg
#print axioms Analysis.qpow_odd_nonpos
#print axioms Analysis.artTerm_nonpos
#print axioms Analysis.artSum_le_arg_of_nonpos
#print axioms Analysis.two_tmap_le_sub
#print axioms Analysis.two_tmap_le_sub_mul_W
#print axioms Analysis.artSum_tmap_double_le
#print axioms Analysis.Rle_of_lin_bound
#print axioms Analysis.Rlog_le_sub_one_real
#print axioms Analysis.RlogPos_le_sub_one
#print axioms Analysis.RrpowPos_le_exp_sub_one
#print axioms Analysis.RexpReal_sub_le
#print axioms Analysis.RrpowPos_sub_le
#print axioms Analysis.RmaxZero_le_of_le_of_nonneg
#print axioms Analysis.RrpowPos_lip_of_log
#print axioms Analysis.Qdiv_num_pos
#print axioms Analysis.Qinv_le_one
#print axioms Analysis.Qdiv_le_B
#print axioms Analysis.Qinv_mul_ge_one
#print axioms Analysis.Qdiv_ge_invB
#print axioms Analysis.Rdiv_seq_pos
#print axioms Analysis.Rdiv_seq_le_B
#print axioms Analysis.Rdiv_seq_ge_invB
#print axioms Analysis.Rmul_y_Rdiv
#print axioms Analysis.Qone_le_mul
#print axioms Analysis.Qprod_lo
#print axioms Analysis.QB_le_B2
#print axioms Analysis.Rmul_seq_pos
#print axioms Analysis.Rmul_seq_le
#print axioms Analysis.Rle_one_Rdiv
#print axioms Analysis.RlogPos_sub_le_Rdiv
#print axioms Analysis.RrpowPos_lipschitz
#print axioms Analysis.Rmul_lip_const_nonneg
#print axioms Analysis.Rmul_lipschitz
#print axioms Analysis.Rmul_lipschitz_real
#print axioms Analysis.lip_q_of_lip_real
#print axioms Analysis.Rle_one_of_seq_ge1
#print axioms Analysis.Rinv_le_one
#print axioms Analysis.Rdiv_sub_one_le_abs
#print axioms Analysis.Rlog_abs_lipschitz
#print axioms Analysis.RmaxZero_le_abs
#print axioms Analysis.RexpReal_abs_lipschitz
#print axioms Analysis.clampOne_witness
#print axioms Analysis.RrpowPos_le_one_of_nonpos
#print axioms Analysis.RrpowPos_abs_lipschitz
#print axioms Analysis.RlogPos_sub_le_Rdiv_gen
#print axioms Analysis.Rlog_abs_lipschitz_gen
#print axioms Analysis.RrpowPos_abs_lipschitz_gen
#print axioms Analysis.RrpowPos_abs_lipschitz_natB
#print axioms Analysis.Qmax_den_pos
#print axioms Analysis.Qmax_ge_left
#print axioms Analysis.Qmax_ge_right
#print axioms Analysis.Qmax_le
#print axioms Analysis.Qsub_self_le_Qabs
#print axioms Analysis.Qmax_const_lip
#print axioms Analysis.qClampOne_ge1
#print axioms Analysis.qClampOne_pos
#print axioms Analysis.qClampOne_le
#print axioms Analysis.Qmax_eq_right
#print axioms Analysis.Qmax_eq_left
#print axioms Analysis.qClampOne_eq_of_ge
#print axioms Analysis.qClampOne_lipschitz
#print axioms Analysis.gPowClamp_lipschitz
#print axioms Analysis.gPowClamp_congr
#print axioms Analysis.gPowClamp_nonneg
#print axioms Analysis.gPowClamp_le_one
#print axioms Analysis.gPowClamp_abs_le_one
#print axioms Analysis.thetaClamp_abs_le_one
#print axioms Analysis.gPowTheta
#print axioms Analysis.gPowTheta_lip
#print axioms Analysis.gPowTheta_congr
#print axioms Analysis.gPowTheta_nonneg
#print axioms Analysis.gPowTheta_L_le_ofQ
#print axioms Analysis.integralTerm_gPowTheta_le
#print axioms Analysis.thetaMellinPow
#print axioms Analysis.thetaMellinPow_nonneg
#print axioms Analysis.gPowTheta_le_thetaClamp
#print axioms Analysis.thetaClamp_le_succ
#print axioms Analysis.gPowThetaSym
#print axioms Analysis.gPowThetaSym_nonneg
#print axioms Analysis.gPowThetaSym_congr
#print axioms Analysis.gPowThetaSym_swap
#print axioms Analysis.gPowThetaSym_lip
#print axioms Analysis.gPowThetaSym_L_le_ofQ
#print axioms Analysis.integralTerm_gPowThetaSym_le
#print axioms Analysis.thetaMellinPowSym
#print axioms Analysis.thetaMellinPowSym_nonneg
#print axioms Analysis.thetaMellinPowSym_symm
#print axioms Analysis.integralTerm_gPowTheta_le2
#print axioms Analysis.thetaMellinPow_le_two
#print axioms Analysis.Radd_lipschitz_real

-- v0.22.0 crux frontier: γ₄ — the fourth Stieltjes constant as a constructive real (Analysis/GammaFour.lean).
#print axioms Analysis.lnQuartOver_nonneg
#print axioms Analysis.lnQuartSum_step
#print axioms Analysis.lnQuartSum_mono
#print axioms Analysis.logQuintic_nonneg
#print axioms Analysis.g4Seq_step_eq
#print axioms Analysis.Rmul_swap_outer
#print axioms Analysis.Rmul_swap_last
#print axioms Analysis.quintic_diff_identity
#print axioms Analysis.Rmul_fifth_five
#print axioms Analysis.quartic_mono
#print axioms Analysis.W4_ge_5b4
#print axioms Analysis.W4_le_5a4
#print axioms Analysis.quint_diff_le
#print axioms Analysis.e4Step_ge_num
#print axioms Analysis.quint_diff_ge
#print axioms Analysis.Rfour_mul
#print axioms Analysis.e4Step_le_num
#print axioms Analysis.logQuart_le_block
#print axioms Analysis.g4Seq_step_le_block
#print axioms Analysis.g4Seq_step_ge_block
#print axioms Analysis.g4Seq_diff_le_block
#print axioms Analysis.g4Seq_diff_ge_block
#print axioms Analysis.g4Seq_block_le
#print axioms Analysis.g4Seq_block_ge
#print axioms Analysis.gamma4Midx_mono
#print axioms Analysis.g4_linU
#print axioms Analysis.g4_quadincU
#print axioms Analysis.g4_cube_linU
#print axioms Analysis.g4_domination_U
#print axioms Analysis.g4_TU_le
#print axioms Analysis.g4_linL
#print axioms Analysis.g4_quadincL
#print axioms Analysis.g4_cubincL
#print axioms Analysis.g4_quart_linL
#print axioms Analysis.g4_domination_L
#print axioms Analysis.g4_TL_le
#print axioms Analysis.WUsum4_den_pos
#print axioms Analysis.WLsum4_den_pos
#print axioms Analysis.g4Seq_diff_le_outer
#print axioms Analysis.g4Seq_diff_ge_outer
#print axioms Analysis.WUsum4_tail_le
#print axioms Analysis.WLsum4_tail_le
#print axioms Analysis.g4_pair_le
#print axioms Analysis.g4_pair_ge
#print axioms Analysis.g4SeqDyadic_RReg

-- γ₄ bracket foundations (Analysis/GammaFourBracket.lean): quartic cap + accelerated sequence.
#print axioms Analysis.quart_prod_split
#print axioms Analysis.quart_le_256_exp
#print axioms Analysis.logQuart_le_self256
#print axioms Analysis.hSeq4_step_eq
#print axioms Analysis.quartic_binom
#print axioms Analysis.one_plus_four
#print axioms Analysis.four_plus_one
#print axioms Analysis.four_plus_six
#print axioms Analysis.six_plus_four
#print axioms Analysis.Radd_eq_RsumL4
#print axioms Analysis.Radd_eq_RsumL5
#print axioms Analysis.W4_collect
#print axioms Analysis.W4_expand
#print axioms Analysis.half_four
#print axioms Analysis.half_six
#print axioms Analysis.fifth_five
#print axioms Analysis.fifth_ten
#print axioms Analysis.partA4_eq
#print axioms Analysis.partC4_eq
#print axioms Analysis.Rmul_eq_RprodL6L
#print axioms Analysis.quart_times_pair
#print axioms Analysis.cube_times_triple
#print axioms Analysis.pair_times_sqpair
#print axioms Analysis.single_times_cubepair
#print axioms Analysis.decompForm4_eq_RsumL
#print axioms Analysis.lhsForm4_eq_RsumL
#print axioms Analysis.decomp_generic4
#print axioms Analysis.sStep4_decomp

-- The λ₂ − λ₁ gap (Analysis/LambdaGap.lean): the first certified separation of Li coefficients.
#print axioms Analysis.lambda_gap_lower
#print axioms Analysis.lambda_gap_pos
#print axioms Analysis.not_Pos_zero
#print axioms Analysis.Rlambda1_ne_Rlambda2

-- The Gate-A finite-list template + the constant-class prune (Square/GateAFiniteList.lean).
#print axioms Square.SatisfiesRec_congr
#print axioms Square.linRec_unique
#print axioms Square.satisfiesRec_const
#print axioms Square.satisfiesRec_const_step
#print axioms Square.realizesDiag_of_finiteList
#print axioms Square.GateA_of_finiteList
#print axioms Square.finiteList_is_liNonneg
#print axioms Square.finiteList_satisfiable
#print axioms Square.finiteList_can_fail
#print axioms Square.constantClass_lamRec_fails
#print axioms Square.constantClass_pruned

-- The log 4π lower bracket + λ₁ upper (Analysis/LogFourPiLower.lean): first two-sided λ.
#print axioms Analysis.qpow_le_base
#print axioms Analysis.artTerm_le_base
#print axioms Analysis.artSum_le_base
#print axioms Analysis.Rpi_seq_ge_314
#print axioms Analysis.tmap_ge_314
#print axioms Analysis.RpiTmap_ge_107207
#print axioms Analysis.Rartanh_third_ge
#print axioms Analysis.Rlog2c_ge
#print axioms Analysis.Rlog2c_ge_69314
#print axioms Analysis.Rartanh_RpiTmap_ge_deep
#print axioms Analysis.Rlogpic_ge
#print axioms Analysis.Rlogpic_ge_11441
#print axioms Analysis.Rlog4pic_ge
#print axioms Analysis.Rtwolambda1_le
#print axioms Analysis.Rlambda1_le

-- The order clash + doubled-λ₁ gap (Analysis/LambdaGap.lean additions).
#print axioms Analysis.not_Pos_of_Rnonneg_Rneg
#print axioms Analysis.Rlambda1_double_eq
#print axioms Analysis.lambda_gap_pos_double

-- The contraction-class prune (Square/GateAFiniteList.lean additions).
#print axioms Square.satisfiesRec_order1_step
#print axioms Square.contractionClass_lamRec_fails
#print axioms Square.contractionClass_pruned

-- The λ₂ lower + λ₃ upper brackets (LambdaGap.lean addition, new Analysis/LambdaThreeUpper.lean).
#print axioms Analysis.Rlambda2_ge
#print axioms Analysis.Rgamma_cube_le
#print axioms Analysis.Rgamma_gamma1_le
#print axioms Analysis.Rlambda3_arith_le
#print axioms Analysis.genuineArchSeq3_le
#print axioms Analysis.Rlambda3_le

-- The full order-1 class kill (Square/GateAFiniteList.lean additions).
#print axioms Square.not_Rle_ofQ_of_witness
#print axioms Square.order1Class_lamRec_fails
#print axioms Square.order1Class_pruned

-- The λ₂ upper / λ₃ tightened lower (new Analysis/LambdaTwoThreePrecision.lean).
#print axioms Analysis.Rlambda2_le
#print axioms Analysis.Rlambda3_arith_ge_t
#print axioms Analysis.Rlambda3_ge

-- The order-2 contraction-class kill (Square/GateAFiniteList.lean additions).
#print axioms Square.contractionClass2_lamRec_fails
#print axioms Square.contractionClass2_pruned

-- The λ₄ upper bracket (new Analysis/LambdaFourUpper.lean): fourth two-sided λ.
#print axioms Analysis.Rgamma_pow4_ge
#print axioms Analysis.Rgamma_sq_gamma1_ge
#print axioms Analysis.Rgamma1_sq_ge
#print axioms Analysis.Rgamma_gamma2_ge
#print axioms Analysis.Rlambda4_arith_le
#print axioms Analysis.genuineArchSeq4_le
#print axioms Analysis.Rlambda4_le

-- The Li-head strict monotonicity (Analysis/LambdaTwoThreePrecision.lean additions).
#print axioms Analysis.Rlambda1_lt_Rlambda2
#print axioms Analysis.Rlambda2_lt_Rlambda3
#print axioms Analysis.Rlambda_head_increasing

-- The general-order sign prune, the K=0 kill, and the prune ledger (GateAFiniteList.lean).
#print axioms Square.Rmul_nonpos_of_nonpos
#print axioms Square.RsumN_nonpos
#print axioms Square.not_Pos_of_Rle_zero
#print axioms Square.nonPositive_lamRec_fails
#print axioms Square.nonPositiveClass_pruned
#print axioms Square.orderZeroClass_pruned
#print axioms Square.gateA_prune_ledger

-- The convex-combination lever (Square/GateAFiniteList.lean, sixth prune).
#print axioms Square.RsumN_mul_right
#print axioms Square.Rle_Rsub_zero_of_Rle
#print axioms Square.convex_cap
#print axioms Square.convex_lamRec_fails
#print axioms Square.Rsub_double
#print axioms Square.Pos_Rsub_double
#print axioms Square.convexClass12_pruned

-- The λ₄ − λ₃ gap: λ₃ < λ₄ (new Analysis/LambdaFourThreeGap.lean).
#print axioms Analysis.nsmulR6_split
#print axioms Analysis.nsmulR4_split_left
#print axioms Analysis.lambda4_arith_split
#print axioms Analysis.reta3_le_t
#print axioms Analysis.etaGap43_le
#print axioms Analysis.genuineArchSeq4_ge_t
#print axioms Analysis.Radd_rearrange4_an
#print axioms Analysis.Rsub_Radd_cancel_left
#print axioms Analysis.lambda43_gap_lower
#print axioms Analysis.Rlambda3_lt_Rlambda4

-- The order-3 convex prune (Square/GateAFiniteList.lean).
#print axioms Square.convexClass3_pruned
#print axioms Square.convexClass123_pruned

-- The integral evaluation layer (new Analysis/IntegralEval.lean): Rlim_eval + ∫₀¹ x = ½.
#print axioms Analysis.Rlim_eval
#print axioms Analysis.lip_id
#print axioms Analysis.congr_id
#print axioms Analysis.sumIota
#print axioms Analysis.riemannSum_id
#print axioms Analysis.ofQ_zero_num
#print axioms Analysis.genSum_id_eval
#print axioms Analysis.gauss_defect_le
#print axioms Analysis.genSum_id_rate
#print axioms Analysis.riemannIntegral_id

-- The affine evaluation layer + the first evaluated Weil-slot component
-- (IntegralEval.lean addition, new Analysis/AffineIntegral.lean).
#print axioms Analysis.riemannIntegral_id_gen
#print axioms Analysis.lip_const
#print axioms Analysis.congr_const
#print axioms Analysis.lip_scaled
#print axioms Analysis.congr_scaled
#print axioms Analysis.lip_affine
#print axioms Analysis.congr_affine
#print axioms Analysis.riemannIntegral_scaled
#print axioms Analysis.riemannIntegral_affine
#print axioms Analysis.affine_pullback_eq
#print axioms Analysis.lip_id_ge
#print axioms Analysis.tent_piece1
#print axioms Analysis.tent_piece2
#print axioms Analysis.tentPoleA_eq

-- The clamped-reciprocal gadget (new Analysis/ClampedInv.lean): the totalized
-- 1/max(x,a) integrand — uniform witness, (1/a)²-Lipschitz, inert on [a,∞).
#print axioms Analysis.Qlt_of_Qlt_Qle
#print axioms Analysis.Qbound_lt_pos
#print axioms Analysis.qClampQ_ge
#print axioms Analysis.qClampQ_witness
#print axioms Analysis.qClampQ_congr
#print axioms Analysis.qClampQ_lipschitz
#print axioms Analysis.qClampQ_eq_of_ge
#print axioms Analysis.Rle_ofQ_qClampQ
#print axioms Analysis.Rinv_le_ofQ_inv
#print axioms Analysis.Rinv_sub_Rinv
#print axioms Analysis.Rinv_abs_lipschitz

-- The reciprocal / clamped-reciprocal LOWER bound (new Analysis/ClampedInvLower.lean): the mirror of
-- Rinv_le_ofQ_inv. ofQ_inv_le_Rinv: u ≤ B > 0 ⟹ 1/B ≤ 1/u (1/B ≈ ((1/u)·u)·(1/B) ≈ (1/u)·(u·(1/B)) ≤
-- (1/u)·(B·(1/B)) ≈ 1/u). Rle_qClampQ_ofQ: x ≤ B, a ≤ B ⟹ max(x,a) ≤ B (Qmax_le). ofQ_inv_le_clampedInv:
-- x ≤ B, a ≤ B (B>0) ⟹ 1/B ≤ clampedInv a x = 1/max(x,a) — the reciprocal LOWER bound the repo lacked
-- (it carried only upper bounds), what a convolution decay estimate needs to bound f(x·(1/max(t,a))) on
-- a bounded t-window. NO convolution decay, NO half-line assembly, NO factorization, NO positivity, NO crux.
#print axioms Analysis.ofQ_inv_le_Rinv
#print axioms Analysis.Rle_qClampQ_ofQ
#print axioms Analysis.ofQ_inv_le_clampedInv

-- The multiplicative convolution inherits f's window decay (new Analysis/MulConvRDecay.lean).
-- mulConvR_window_decay: if |f(y)| ≤ Cf/(k+1)^{n+2} whenever |y| ≥ k+1, then for x on window [m+1,m+2]
-- and a t-window [lo,lo+w] ⊆ (0,1] (a ≤ 1), |mulConvR f g x| ≤ w·M_g·(1/a)·Cf/(m+1)^{n+2}. On the
-- window the clamped reciprocal 1/max(t,a) ≥ 1 (ofQ_inv_le_clampedInv at B=1), so the argument
-- x·(1/max(t,a)) ≥ x ≥ m+1 clears the INTEGER threshold (no floors); f's decay + the pointwise product
-- bound × M_g × 1/a integrate via riemannIntegralI_abs_le_window. The analytic heart of the half-line
-- assembly (mellinHat(f⋆g) converges only if the convolution's windows decay); f-decay is an explicit
-- hypothesis. NO half-line assembly, NO generalized tail, NO factorization M[f⋆g]=M[f]·M[g], NO
-- positivity, NO crux; the general t-window-past-1 case is separate.
#print axioms Analysis.mulConvR_window_decay

-- The convolution's Mellin tail-term in genSum-ready decay form (new Square/ConvTwTermBound.lean).
-- convTwTerm_bound: for a t-window ⊆ (0,1] (a ≤ 1) and f with order-(n+2) window decay, the m-th twisted
-- tail term of the convolution's Mellin transform at the minimal window-clearing clamp S=m+2 satisfies
-- |twTerm (mulConvRTest f g (m+2)) n m| ≤ (w·Cf·M_g·(1/a)·2ⁿ)/((m+1)·m) — the (C·2ⁿ)/((m+1)m) shape
-- genSum_RReg consumes. Mirrors twTerm_bound's single-window logic: clamp-strip on [m+1,m+2]
-- (qBandQ_eq_of_band + mulConvR_congr) → mulConvR_window_decay → twist ×powWinTest.M ≤ (m+2)ⁿ + collapse
-- (m+2)ⁿ/(m+1)^{n+2} ≤ 2ⁿ/((m+1)m) via riemannIntegralI_abs_le_window (cd_pow_core/cd_collapse reproved
-- inline, MellinHat's are private). So the genuine (clamp-free, twTerm_mulConv_S_indep) per-window value is
-- summable. f-decay is an explicit hypothesis; t-window is (0,1]. NO generalized tail, NO ∫_t
-- reconstruction, NO factorization M[f⋆g]=M[f]·M[g], NO positivity, NO crux.
#print axioms Square.convTwTerm_bound

-- The clamp-free half-line Mellin transform of the convolution EXISTS (new Square/ConvMellinHat.lean).
-- convTwTerm_two_sided: the ∧-form of convTwTerm_bound (Rneg_le_of_Rabs_le/Rle_of_Rabs_le) at modulus
-- K = w·Cf·M_g·(1/a)·2ⁿ, the shape genSum_RReg consumes. Then (defs, no audit) convTwTail = Rlim of the
-- genuine per-window twisted sums (twTerm at minimal clamp m+2, per-m; clamp-free by twTerm_mulConv_S_indep)
-- via genSum_RReg fed by convTwTerm_two_sided — the convergent tail ∫₁^∞(f⋆g)·xⁿ; convMellinHat =
-- mellinMoment(f⋆g) + convTwTail = M[f⋆g](n), the clamp-free half-line transform as a constructed real
-- (mellinHat(mulConvRTest f g S) could NOT converge for fixed S — frozen tail). GOTCHA: explicit T in
-- genSum_RReg (not _) to avoid whnf blowup from higher-order inference over the m-dependent mulConvRTest.
-- NO factorization M[f⋆g]=M[f]·M[g] (the ∫_t reconstruction), NO positivity, NO crux.
#print axioms Square.convTwTerm_two_sided

-- The convolution's Mellin MOMENT factors as the g-weighted dilated moment of f (new
-- Square/MomentMulConvDilated.lean): the [0,1] moment-window analog of twTerm_mulConv_dilated.
-- mom_ptw: the swapped outer test's value at each t equals (g·clampedInv)·mellinMoment(dilateTestR c_t f) n
-- — coupOuterTestSwap_gpull (at powTest n, window [0,1]) composed with dilMellinF_eq_mellinMoment.
-- mellinMoment_mulConv_dilated: mellinMoment(mulConvRTest f g 1) n = ∫_t (g(t)·(1/max(t,a)))·
-- mellinMoment(dilateTestR (1/max(t,a)) f) n dt — a SINGLE ∫_t (no window sum), so the moment piece
-- factors with NO interchange. riemannIntegralI_unit bridge (mellinMoment ↔ [0,1] interval integral) +
-- mellinConv_fubini + riemannIntegralI_congr via mom_ptw. Together with twTerm_mulConv_dilated this gives
-- the per-window factored form for both pieces of convMellinHat=moment+tail. NO tail assembly, NO Σ_m/∫_t
-- interchange, NO covariance application, NO factorization M[f⋆g]=M[f]·M[g], NO positivity, NO crux.
#print axioms Square.mom_ptw
#print axioms Square.mellinMoment_mulConv_dilated

-- General-window integral additivity over L2Test.add (new Square/IntervalAddTest.lean).
-- riemannIntegralI_addTest: ∫_{lo}^{lo+w} (φ+ψ) = ∫ φ + ∫ ψ — the interval-integral analog of
-- innerI_add_left. Three integrands weakened to the common modulus φ.L+ψ.L (lip_weaken) where
-- riemannIntegralI_add fires; certif_irrel returns each summand to its canonical modulus. The two-term
-- additivity the Σ_m/∫_t interchange (the convolution factorization's tail assembly) is built from by
-- induction. NO Σ_m/∫_t interchange, NO tail assembly, NO factorization, NO positivity, NO crux.
#print axioms Square.riemannIntegralI_addTest
-- riemannIntegralI_genSumTest: THE Σ_m/∫_t INTERCHANGE (finite) — Σ_{m<N} ∫_{lo}^{lo+w} (T m) =
-- ∫_{lo}^{lo+w} Σ_{m<N} (T m), for any test family T : Nat → L2Test. Induction on N: base ∫ 0 = 0
-- (riemannIntegralI_const + Rmul_zero, zeroTest matching const's fields defeq), step riemannIntegralI_addTest
-- on genSumTest T (N+1) = (genSumTest T N)+(T N). The m-dependent-modulus obstacle is dissolved: the sum
-- test genSumTest carries the summed modulus intrinsically, so no manual weakening compounding. This is the
-- interchange that turns the convolution's per-window tail-term sum into a single t-integral of the summed
-- dilated tail (defs zeroTest/genSumTest need no audit line). NO tail assembly wired to the convolution yet,
-- NO covariance application, NO factorization M[f⋆g]=M[f]·M[g], NO positivity, NO crux.
#print axioms Square.riemannIntegralI_genSumTest

-- The convolution's partial tail sum is a single ∫_t (new Square/ConvPartialInterchange.lean), wiring the
-- interchange to the convolution. coupFam (def): the swapped-outer-test family coupOut_m =
-- coupOuterTestSwap f g (powWinTest m n) (m+2) … [m+1,m+2]. convPartial_eq_intGenSum: Σ_{m<N} twTerm
-- (mulConvRTest f g (m+2)) n m = ∫_{lo}^{lo+w} (genSumTest coupFam N) — each term is ∫_t coupOut_m
-- (mellinConv_fubini via the twTerm=mellinConv defeq bridge), genSum_congr lands the sum on Σ ∫_t coupOut_m,
-- riemannIntegralI_genSumTest interchanges to the single ∫_t of the summed test. NO N→∞ limit, NO covariance
-- application, NO factorization M[f⋆g]=M[f]·M[g], NO positivity, NO crux.
#print axioms Square.convPartial_eq_intGenSum

-- The summed outer test's integrand is the partial dilated tail (new Square/ConvSummedIntegrand.lean).
-- genSumTest_coupFam_eq: (genSumTest coupFam N).f t = Σ_{m<N} dilTailIntegrand f g n m a t (the g-weighted
-- dilated tail terms) — induction on N: base sumZeroTest.f≡0=genSum 0, step L2Test.add's Radd composed with
-- dilTail_ptw (coupOut_m.f t ≈ dilTailIntegrand_m t, clamp m+2 inert on [m+1,m+2]). So the interchange's
-- ∫_t (genSumTest coupFam N) is the finite ∫_t of the g-weighted partial dilated tail. NO N→∞ limit, NO
-- covariance, NO factorization M[f⋆g]=M[f]·M[g], NO positivity, NO crux.
#print axioms Square.genSumTest_coupFam_eq

-- Scale-uniform tail-decay preservation under real dilation (new Square/DilateTestRDecay.lean).
-- Rabs_le_Rabs_Rmul_of_one_le: for c ≥ 1, |y| ≤ |c·y| (= |c|·|y| with |c| = c ≥ 1) — dilation by
-- c ≥ 1 only enlarges the argument. dilateTestR_hfdec: hence f's clean k-indexed order-(n+2) half-line
-- decay (∀ k, ∀ y, |y| ≥ k+1 → |f(y)| ≤ Cf/(k+1)^{n+2}) transfers to dilateTestR c f with the SAME
-- constant Cf for EVERY c ≥ 1 — the uniform-in-scale decay the ∫_t reconstruction needs (on the t-window
-- ⊆ (0,1] the convolution's inner scale clampedInv(a,t) = 1/max(t,a) ≥ 1). NO tail assembly, NO
-- covariance, NO factorization M[f⋆g]=M[f]·M[g], NO positivity, NO crux.
#print axioms Square.Rabs_le_Rabs_Rmul_of_one_le
#print axioms Square.dilateTestR_hfdec
-- hdec_window_of_hfdec: clean k-indexed decay ⟹ the window-affineMap decay twTerm_bound/twTail/mellinHat
-- consume (the window point affineMap (m+1) 1 x ≥ m+1, so the clean bound at index m fires).
-- dilateTestR_window_hdec: composing the two — the c ≥ 1 dilation's window-format decay with the SAME
-- constant Cf, exactly what twTail (dilateTestR c f) n requires. NO tail assembly, NO factorization, no crux.
#print axioms Square.hdec_window_of_hfdec
#print axioms Square.dilateTestR_window_hdec

-- The dilated-tail integrand is bounded UNIFORMLY in t (new Square/DilTailUniformBound.lean).
-- dilTailIntegrand_window_bound: for a t-window ⊆ (0,1] and f with clean order-(n+2) decay, at EVERY
-- window point t = lo+w·s the m-th dilated-tail integrand g(t)·(1/max(t,a))·twTerm(dilate (1/max(t,a)) f) n m
-- is ≤ (g.M·(1/a)·Cf·2ⁿ)/((m+1)m), with NO t-dependence in the constant. On the window t ≤ 1 (a ≤ 1) the
-- inner scale clampedInv(a,t) ≥ 1 (ofQ_inv_le_clampedInv), so dilateTestR_window_hdec + twTerm_bound give
-- the t-uniform term bound; the g-weight |g(t)·clampedInv| ≤ g.M·(1/a) is t-uniform too. The pointwise-in-t
-- companion of convTwTerm_bound (which bounds the integrated ∫_t value). NO tail assembly, NO
-- limit-inside-integral, NO covariance, NO factorization M[f⋆g]=M[f]·M[g], NO positivity, NO crux.
-- dilTailIntegrand_bound_of_ge1: the per-t core with clampedInv(a,t) ≥ 1 supplied as a hypothesis (the
-- t-uniform term bound that feeds genSum_RReg for the dilated tail at a fixed t); window_bound is its corollary.
-- window_clampedInv_ge_one: on the t-window [lo,lo+w] ⊆ (0,1] (a ≤ 1), the inner scale
-- clampedInv(a, lo+w·s) = 1/max(t,a) ≥ 1 (window point ≤ 1, ofQ_inv_le_clampedInv B=1). The shared hc1
-- the reconstruction feeds to dilTail_partial_close (so hU and the closeness use the SAME term).
#print axioms Square.window_clampedInv_ge_one
#print axioms Square.dilTailIntegrand_bound_of_ge1
#print axioms Square.dilTailIntegrand_window_bound

-- Distance between two interval integrals ≤ window × sup-distance (new Square/IntegralDist.lean).
-- riemannIntegralI_negTest: ∫(neg φ) = -∫φ at the test level (packaging riemannIntegralI_neg).
-- riemannIntegralI_dist_le_of_close: if |φ(x)-ψ(x)| ≤ B on the window [lo,lo+w], then
-- |∫φ - ∫ψ| ≤ w·B — via ∫(φ-ψ)=∫φ-∫ψ (addTest+negTest) and |∫(φ-ψ)|≤w·B (abs_le_window, since
-- (φ-ψ)(x)=φ(x)-ψ(x) definitionally). The reusable heart of the ∫_t reconstruction's commute, to be
-- composed with Rlim_eval_real_rate. NO tail assembly, NO limit-inside-integral, NO factorization, no crux.
#print axioms Square.riemannIntegralI_negTest
#print axioms Square.riemannIntegralI_dist_le_of_close

-- Partial sum at a faster schedule is within 3/(j+1) of the accelerated limit (new Square/GenSumCloseRlim.lean).
-- genSum_close_Rlim: for a decay term T with |T m| ≤ K/((m+1)m) and any schedule R ≥ digammaMidx K,
-- |genSum T (R j) - Rlim(genSum T ∘ digammaMidx K)| ≤ 3/(j+1) — triangle (genSum_close ≤ 1/(j+1) +
-- Rabs_dist_Rlim ≤ 2/(j+1)). The rate depends only on T's decay constant K, so for T = twTerm(dilate c f) n
-- (K = Cf·2ⁿ, scale-independent) it is UNIFORM in the dilation scale c — the ∫_t reconstruction's tail
-- estimate at the convolution's own schedule. NO tail assembly, NO factorization, NO positivity, no crux.
#print axioms Square.genSum_close_Rlim

-- The convolution-schedule partial of the dilated tail is close to K·twTail (new Square/DilTailPartialClose.lean).
-- dilTail_partial_close: for t with clampedInv(a,t) ≥ 1 and any schedule R ≥ digammaMidx(Cf·2ⁿ),
-- |Σ_{m<R j} dilTailIntegrand·t - g(t)·clampedInv·twTail(dilate c_t f) n| ≤ (g.M·(1/a))·3/(j+1), rate uniform
-- in t. Chain: genSum_Rmul_of_termwise pulls K=g(t)·clampedInv out (dilTailIntegrand_m t = K·twTerm(dilate c_t f) n m
-- defeq), Rmul_sub_distrib factors K out of the difference, genSum_close_Rlim bounds |genSum(twTerm) (R j) - twTail|
-- by 3/(j+1) (its Rlim IS twTail by def), |K| ≤ g.M·(1/a) closes the product. NO limit-inside-integral, NO Ttail,
-- NO covariance, NO factorization, NO positivity, no crux.
#print axioms Square.dilTail_partial_close

-- convTwTail is its own limit at any faster schedule (new Square/ConvTwTailSchedule.lean).
-- convTwTail_eq_fast_schedule: for any R with digammaMidx K_conv j ≤ R j (K_conv = w·Cf·M_g·(1/a)·2ⁿ),
-- Rlim(genSum (conv twisted terms) ∘ R) = convTwTail f g n. Via Rlim_approx_eq on the 1/(j+1)
-- schedule-closeness (genSum_close fed by convTwTerm_two_sided) — the analog of improper_schedule_eq for
-- the convolution's clamp-free tail. Lets the ∫_t reconstruction evaluate on a schedule dominating the
-- dilated tail's digammaMidx(Cf·2ⁿ) (K_conv and Cf·2ⁿ not comparable in general). NO factorization, no crux.
#print axioms Square.convTwTail_eq_fast_schedule

-- A common schedule dominating two digammaMidx schedules (new Square/DigammaMidxCommon.lean).
-- digammaMidx_common: for K⋆ = ⟨K.num.toNat + K'.num.toNat, 1⟩, both digammaMidx K j ≤ digammaMidx K⋆ j
-- and digammaMidx K' j ≤ digammaMidx K⋆ j — since digammaMidx B j = (B.num.toNat+1)(j+1) depends on B's
-- numerator only (NOT Qle-monotone). Lets the ∫_t reconstruction evaluate on one schedule dominating both
-- convTwTail's digammaMidx K_conv and the dilated tail's digammaMidx(Cf·2ⁿ). NO factorization, no crux.
#print axioms Square.digammaMidx_common

-- Two schedule-plumbing lemmas for the common evaluation schedule (new Square/TwoSidedWeaken.lean).
-- two_sided_weaken: −B ≤ x ≤ B and Qle B B' ⟹ −B' ≤ x ≤ B' (ofQ mono both sides) — lifts
-- convTwTerm_two_sided from K_conv to K⋆ so genSum_RReg fires at K⋆. Qle_self_toNat_add: a nonneg
-- rational K ≤ ⟨K.num.toNat + c, 1⟩ (c ≥ 0) — the Qle K_conv K⋆ step. NO factorization, no crux.
#print axioms Square.two_sided_weaken
#print axioms Square.Qle_self_toNat_add
-- rate_bound_Qle: the ∫_t reconstruction's per-index rate w·(g.M·(1/a)·3/(j+1)) ≤ C/(j+1) with the fixed
-- Nat C = (w.num·(g.M.num·(1/a).num)·3).toNat — the C Rlim_eval_real_rate consumes. NO factorization, no crux.
#print axioms Square.rate_bound_Qle

-- THE TAIL COMMUTE (new Square/DilTailCommute.lean). convTwTail_eq_intTail: convTwTail f g n = ∫_t U for any
-- test U whose window-values match g(t)·clampedInv(a,t)·twTail(dilateTestR (clampedInv a t) f) n (hypothesis hU,
-- the covariance-connect). Composes the whole Wall-3 stack along the common schedule K⋆: convTwTail_eq_fast_schedule
-- (schedule bump) + genSum_RReg at K⋆ via two_sided_weaken/Qle_self_toNat_add/qmul_le_right_mono/digammaMidx_common,
-- then Rlim_eval_real_rate over convPartial_eq_intGenSum + genSumTest_coupFam_eq + hU + dilTail_partial_close +
-- riemannIntegralI_dist_le_of_close + rate_bound_Qle (C=(w.num·(g.M.num·(1/a).num)·3).toNat). PARAMETRIC in hU
-- (the covariance identification U.f=g·clampedInv·twTail is a hypothesis; grounding v=ĝ still to come). NO
-- factorization asserted, NO positivity, NO crux. Step 4 (band-coupling positivity) is RH; crux fields `none`.
#print axioms Square.convTwTail_eq_intTail

-- The shrinking-dilation ("fine") window decay (new Square/DilateTestFineDecay.lean) — first brick of the
-- c≥1 covariance wall-break. dilateTest_fine_window_decay: for φ with clean order-(n+2) decay (Cf) + bound φ.M
-- and D≥1, the fine dilation dilateTest (1/D) φ (.f y = φ(y/D)) has window decay at the PER-D constant
-- C' = (Cf+φ.M)·(2D)^(n+2). Two regimes (rcases Nat.lt_or_ge (m+1) D): coarse m+1≥D (arg≥1, φ-decay at
-- k=(m+1)/D−1, deflation costs (2D)^(n+2) via m+1≤2D(k+1)); fine m+1<D (arg<1, only φ.M, (m+1)^(n+2)≤(2D)^(n+2)).
-- Per-D constant (NO shared-C blowup) — discharges covariance_at_rational_dilateTestR's hdec_fine at each qk.
-- NO covariance assembly yet, NO factorization, NO positivity, NO crux.
#print axioms Square.dilateTest_fine_window_decay

-- twTail/mellinHat independent of the witnessing decay constant (new Square/MellinHatDecayIndep.lean) — the
-- schedule-bridge for the c≥1 covariance wall-break. twTail_decay_indep: twTail φ n at two valid decay
-- constants C1,C2 = SAME value (both Rlim of genSum(twTerm φ n), reconciled through the common schedule
-- digammaMidx K⋆ = ⟨(C1·2ⁿ).num.toNat+(C2·2ⁿ).num.toNat,1⟩ via genSum_close×2 + digammaMidx_common +
-- Rlim_approx_eq + Rabs triangle). mellinHat_decay_indep = Radd_congr(mellinMoment)(twTail_decay_indep).
-- Reconciles the covariance-at-qk (proved at C=(Cf+φ.M)·(2·qk.den)^(n+2)) to the reconstruction's uniform Cf.
-- NO covariance assembly yet, NO factorization, NO positivity, NO crux.
#print axioms Square.twTail_decay_indep
#print axioms Square.mellinHat_decay_indep

-- Window-decay constant weakening (new Square/HdecWeaken.lean). hdec_window_weaken: ψ's order-(n+2)
-- window decay at C1 ⟹ same at C2 for Qle C1 C2 (ofQ mono in the numerator via qmul_le_right_mono).
-- Generic in ψ — lifts the reconstruction's tight Cf-decay to the larger per-approximant constant
-- covariance_at_rational_dilateTestR shares across hdec_dil/hdec_phi/hdec_fine. NO covariance, no crux.
#print axioms Square.hdec_window_weaken

-- The per-k hcov ingredient of the c≥1 Mellin dilation covariance (new Square/CovarianceAtQk.lean).
-- covariance_at_qk_baseform: for a rational scale q≥1 bounded by S, qⁿ⁺¹·mellinHat(dilateTestR(ofQ q)φ)n
-- = mellinHat φ n, BOTH read at the reconstruction's uniform decay constant Cf. Routes
-- covariance_at_rational_dilateTestR at the enlarged constant Cbig=qⁿ⁺¹·Cf+C'+Cf (carries the fine
-- 1/q.den decay C'=(Cf+φ.M)(2·q.den)ⁿ⁺² and the qⁿ⁺¹-scaled twisted regularity), then bridges every
-- mellinHat back to Cf by mellinHat_decay_indep; scalar (ofQ q)ⁿ⁺¹ normalised by Rpow_ofQ. This is the
-- exact hcov k the base density capstone mellinHat_dilate_covariance_real consumes. NO real-scale
-- covariance (the capstone), no factorization, no v=ĝ grounding, no step-4 positivity. Crux none.
#print axioms Square.covariance_at_qk_baseform

-- The Gate-A Atlas-intrinsic angle family = step-4 implementation target, STATED (new
-- Square/AtlasAngleFamily.lean). angleDiagTarget_nonneg: every partial Σ_{k<m}(2−2cos(nθ_k)) ≥ 0 (each
-- block 2−2cos=(1−cos)+(1−cos)≥0 via Rcos_le_one) — the certificate's semidefinite face is free from the
-- angle structure. atlasAngleFamily_hodgeNeg: the identity Rlim(angleDiagTarget θ n)=2λₙ alone forces
-- SpectralHodgeNeg (Rlim of nonnegs, across genuine_vanCyc_normal −⟨Cₙ,Cₙ⟩=2λₙ) — the semidefinite face,
-- NOT the crux. atlasAngleFamily_closes_crux: the STRICT form — identity + ∀n>0 Pos(Rlim(angleDiagTarget θ n))
-- closes SpectralCrux (Pos(Rlim)=Pos(2λₙ)=Pos(−⟨Cₙ,Cₙ⟩)). The strict hpos is a property of the FREE angle
-- family (angles nonzero), mirroring the repo's accepted strictRealizes_closes_crux discipline (Pos of a free
-- embedding's diagonal + the realization identity) at the infinite rank the fence forces, in the angle-SOS
-- shape. A REDUCTION (hypothesis→crux); NOTHING constructs θ or asserts the identity/strictness for the
-- genuine 2λₙ (= RH); crux fields stay none.
#print axioms Square.angleDiagTarget_nonneg
#print axioms Square.atlasAngleFamily_hodgeNeg
#print axioms Square.atlasAngleFamily_closes_crux

-- The angle certificate's infinite-rank gram diagonal is the angle sum (new Square/AngleGramRlim.lean).
-- angleGram_Rlim: Rlim_m gramOf (angleEmb θ)(2m) n n = Rlim_m (angleDiagTarget θ n) — Rlim_congr over the
-- finite angleGram_diag (both RReg proofs supplied, no RReg-transport). angleEmb_Rlim_closes_crux: the
-- step-4 reduction stated directly on the BUILT embedding's infinite-rank squared-norm diagonal (the gramOf
-- object realizesDiag_genuine_iff asks for, past every fixed dimension the rank fence kills) — hpos(Pos of
-- the gram Rlim) + hid(gram Rlim = 2λₙ) ⟹ SpectralCrux, via angleGram_Rlim + atlasAngleFamily_closes_crux.
-- Constructs no θ; asserts nothing for genuine 2λₙ (= RH); crux fields none.
#print axioms Square.angleGram_Rlim
#print axioms Square.angleEmb_Rlim_closes_crux

-- FRONTIER DISCOVERY — THE RAW ANGLE TARGET'S LIMIT IS BOUNDED (new Square/AngleTargetBound.lean).
-- angleDiagTarget_Rlim_le_two: for EVERY θ with reg, Rlim(angleDiagTarget θ n) ≤ 2 (angleDiagTarget θ n 0
-- = 0 + Rlim_tendsTo at k=0 gives |0−Rlim| ≤ 2/1). This exposes a SATISFIABILITY GAP in the certificate
-- route's closing mechanism: reg forces Rlim ≤ 2 (indep of θ), but hid demands Rlim = 2λₙ ~ n log n → ∞
-- (2λ₇ ≈ 2.2 > 2), so reg ∧ hid are jointly unsatisfiable on the genuine data — the raw-target reduction
-- (angleGram_Rlim / atlasAngleFamily_closes_crux) is valid but cannot be INSTANTIATED to close the crux.
-- The fix is an accelerated angle target (RReg via a rate schedule, unbounded limit). A defect in one
-- mechanism's statement, not an obstruction to RH; asserts no positivity of 2λₙ. Crux none.
#print axioms Square.angleDiagTarget_Rlim_le_two

-- THE FIX — THE ACCELERATED ANGLE TARGET (new Square/AngleTargetAcc.lean). angleDiagTargetAcc θ n sched
-- j := angleDiagTarget θ n (sched j): the raw partials reindexed by a monotone schedule. For sched 0 > 0
-- it starts from a LARGE partial (not 0), so RReg no longer caps the limit — reg' and hid (Rlim=2λₙ) are
-- JOINTLY SATISFIABLE, repairing the satisfiability gap of AngleTargetBound. angleDiagTargetAcc_nonneg
-- (each partial ≥0, semidefinite face free); atlasAngleFamily_hodgeNeg_acc (identity ⟹ SpectralHodgeNeg);
-- atlasAngleFamily_closes_crux_acc (the STRICT reduction ⟹ SpectralCrux) — the proof is target-agnostic
-- (Pos_congr on hid/hpos through genuine_vanCyc_normal), so it transfers verbatim to a target where the
-- hypotheses can actually be met on the unbounded 2λₙ. Constructs no θ/sched; asserts nothing about the
-- genuine 2λₙ (hid = RH); reg' discharge (choosing sched) is separate convergence analysis. Crux none.
#print axioms Square.angleDiagTargetAcc_nonneg
#print axioms Square.atlasAngleFamily_hodgeNeg_acc
#print axioms Square.atlasAngleFamily_closes_crux_acc

-- reg' DISCHARGE (new Square/AngleRegDischarge.lean). Discharges the reg' hypothesis of
-- atlasAngleFamily_closes_crux_acc to a SATISFIABLE convergence-rate condition. angleDiagTarget_mono:
-- the raw partials Σ_{k<m}(2−2cos nθ_k) are monotone (each block 2−2cos≥0). angleDiagTargetAcc_RReg:
-- given a monotone schedule (hmono) + a canonical-rate bound on the ACCELERATED increments (htail:
-- Y k − Y j ≤ 1/(j+1) for j≤k), the accelerated target is RReg (via RReg_of_real_bound, mirroring
-- czetaRe_RReg). FRONTIER FINDING: the hypothesis is stated on the accelerated increments, NOT a linear
-- schedule — the raw tails decay like (log m)²/m (not 1/m), so sched j = B(j+1) is VACUOUS; the
-- accelerated-increment form IS satisfiable (any Cauchy modulus of the raw series is realized by a
-- schedule). Pure convergence analysis on a FREE θ; asserts nothing about the limit being 2λₙ (that is
-- hid = RH); constructs no θ/sched. Crux none.
#print axioms Square.angleDiagTarget_mono
#print axioms Square.angleDiagTargetAcc_RReg
-- angleDiagTargetAcc_RReg_of_modulus: the schedule EXHIBITED as the raw-series convergence modulus
-- (sched := mod). reg' ⟸ mere convergence of the raw angle series (classical zero-density, non-RH),
-- schedule constructed not assumed. hconv asserts nothing about the limit value/sign (2λₙ = hid = RH).
#print axioms Square.angleDiagTargetAcc_RReg_of_modulus
#print axioms Analysis.clampedInv_congr
#print axioms Analysis.Rnonneg_clampedInv
#print axioms Analysis.clampedInv_lipschitz
#print axioms Analysis.clampedInv_eq_of_ge
#print axioms Analysis.Rinv_ofQ
#print axioms Analysis.clampedInv_ofQ
#print axioms Analysis.lip_mono

-- The multiplicative Haar-measure integral over a bounded interval (new Analysis/HaarInterval.lean).
#print axioms Analysis.innerIonI_self_nonneg
#print axioms Analysis.haarDensity_at_rational
#print axioms Analysis.haarIntegral_nonneg

-- The multiplicative inversion of a test (new Analysis/ReflectTest.lean).
#print axioms Analysis.reflectTest_eq_of_ge
#print axioms Analysis.reflectTest_ofQ

-- The pointwise product of two tests as an L2Test (new Analysis/ProductTest.lean).
#print axioms Analysis.productTest_f
#print axioms Analysis.productTest_comm

-- Real-scale dilation of a test (new Analysis/DilateTestR.lean).
#print axioms Analysis.dilateTestR_f
#print axioms Analysis.dilateTestR_ofQ_f

-- The real-parameter multiplicative convolution (new Analysis/MulConvR.lean).
#print axioms Analysis.mulConvR_nonneg

-- The real-bound window estimate (new Analysis/WindowBoundReal.lean).
#print axioms Analysis.riemannIntegralI_abs_le_window_real

-- The real-parameter convolution is uniformly bounded in x (new Analysis/MulConvRBound.lean).
#print axioms Analysis.mulConvR_abs_le

-- The pointwise x-difference bound of the convolution integrand (new Analysis/MulConvRDiff.lean).
#print axioms Analysis.mulConvR_integrand_diff

-- Lipschitz-in-x continuity of the real-parameter convolution (new Square/MulConvRLip.lean).
#print axioms Square.riemannIntegralI_dist_le_window
#print axioms Square.mulConvR_lipschitz

-- Congruence-in-x of the real-parameter convolution (new Analysis/MulConvRCongr.lean).
#print axioms Analysis.mulConvR_congr

-- The convolution as a bounded-Lipschitz test in x (new Square/MulConvRTest.lean).
#print axioms Square.clampS_absle

-- The Mellin pairing of the convolution (new Square/MellinConv.lean).
#print axioms Square.mellinConv_nonneg

-- The parametric interval integral as a test (new Square/ParamIntegral.lean).
#print axioms Square.paramIntegralTest_nonneg

-- The separable product integrand φ(x)·ψ(y) as a parametric test + its inner factorization
-- ∫_y φ(x)ψ(y) ≈ φ(x)·∫ψ (new Square/ProdParamTest.lean). constMul_lip: one-sided product Lipschitz.
#print axioms Square.constMul_lip
#print axioms Square.prodParamTest_f_factor

-- Separable Fubini: ∫_x ∫_y φ(x)·ψ(y) = (∫φ)·(∫ψ) — the iterated integral of a separable (product)
-- integrand factors (new Square/SeparableFubini.lean). The final factorization the Mellin convolution
-- theorem reduces to once the change of variables has decoupled the integrand.
#print axioms Square.separable_fubini
-- The Fubini SWAP for a separable integrand: ∫_x∫_y φ(x)ψ(y) ≈ ∫_y∫_x ψ(y)φ(x) (order swappable;
-- separable case only, via factorization in each order + Rmul commutativity).
#print axioms Square.separable_fubini_swap

-- Finite-rank Fubini: ∫_x∫_y (Σ φ_k(x)ψ_k(y)) = Σ (∫φ_k)(∫ψ_k) — the iterated integral of a finite
-- sum of separable products factors term by term (new Square/FiniteRankFubini.lean). The finite-rank
-- rung of the Bernstein route to the general (coupled) Fubini swap.
#print axioms Square.riemannIntegralI_L2add
#print axioms Square.zeroTest_int
#print axioms Square.finrank_fubini
-- The finite-rank Fubini SWAP: ∫_x∫_y Σ φ_k(x)ψ_k(y) ≈ ∫_y∫_x Σ ψ_k(y)φ_k(x) (the swap B_n(F) obeys).
#print axioms Square.finrank_fubini_swap

-- The 2D Bernstein operator as a finite-rank (i,j)-grid list + its Fubini swap (new
-- Square/Bern2DOperator.lean) — B_n(F) = Σ_{i,j} F(i/n,j/n)·b_i(x)·b_j(y), a separable-sum instance
-- of finrank_fubini_swap. The finite-rank object the 2D-Bernstein route to the general swap builds on.
#print axioms Square.bern2D_fubini_swap

-- The 2D pointwise Bernstein deviation (new Square/Bern2DDeviation.lean): for jointly-Lipschitz F,
-- |Σ_{i,j}F(i/n,j/n)b_i(x)b_j(y) − F(x,y)| ≤ Lx·Σ|i/n−x|b_i(x) + Ly·Σ|j/n−y|b_j(y) on [0,1]² — the
-- analytic core of the general Fubini swap (double partition-of-unity + joint Lipschitz). Crux none.
#print axioms Square.bern2DVal_unfold
#print axioms Square.bern2DVal_deviation

-- The 2D uniform Bernstein convergence bound (new Square/Bern2DUniform.lean): 2δn·|B_n(F)(x,y)−F(x,y)|
-- ≤ (Lx+Ly)·(δ²+n/4) on [0,1]² — the 2D deviation scaled + bernOp_devsum_bound in each variable, giving
-- ‖F−B_n(F)‖∞ → 0 at the schedule δ=k+1, n=(k+1)². The analytic input the general Fubini swap consumes.
#print axioms Square.bern2DVal_devsum_bound

-- The 2D Bernstein list-fold ↔ pointwise-value agreement (new Square/Bern2DValue.lean): the flatMap↔
-- double-RsumN correspondence (via RsumL) + bern2DList_eval_eq (the fold of Σ (φ.f x)(ψ.f y) over
-- bern2DList = bern2DVal(x,y) on [0,1]²), connecting the swap object to the deviation object.
#print axioms Square.RsumL_map_range
#print axioms Square.RsumL_flatMap_range
#print axioms Square.bernBasisTest_f_eq_bernR
#print axioms Square.bern2DList_eval_eq

-- The per-x inner-integral deviation (new Square/Bern2DInnerClose.lean): at fixed x∈[0,1],
-- 2δn·|∫₀¹F(x,y)dy − (sumProdTest (bern2DList …) 0 1).f x| ≤ (Lx+Ly)(δ²+n/4). The key identity
-- sumProdTest_f_eq_gxInt rewrites the finite-rank value as the genuine interval integral ∫₀¹ gxSumTest
-- (whose [0,1] value is bern2DVal), then the 2δn-scaled riemannIntegralI_dist_le_window is fed by the
-- uniform pointwise bern2DVal_devsum_bound. Multiplied form (no reciprocal). No swap, no positivity.
#print axioms Square.gxSumTest_f
#print axioms Square.riemannIntegralI_constTestMul
#print axioms Square.sumProdTest_f_eq_gxInt
#print axioms Square.scaled_lip
#print axioms Square.scaled_fc
#print axioms Square.riemannIntegralI_ofQscale
#print axioms Square.bern2D_inner_close

-- The outer-integration deviation (new Square/Bern2DOuterClose.lean): Move 1 of the general Fubini
-- swap. Integrating the per-x deviation over x, 2δn·|∫_x∫_y F − ∫_x (sumProdTest (bern2DList …) 0 1)|
-- ≤ (Lx+Ly)(δ²+n/4). A structural mirror of bern2D_inner_close one integration level up: paramIntegralTest
-- and sumProdTest(bern2DList) are the two x-integrands, scaled by 2δn (riemannIntegralI_ofQscale), the
-- per-x bound bern2D_inner_close fed as the pointwise hdiff to riemannIntegralI_dist_le_window. NO swap.
#print axioms Square.bern2D_outer_close

-- The finite-rank symmetry (new Square/Bern2DFinrankSymm.lean): Move 2 of the general Fubini swap, a
-- DISCRETE Fubini. The x-outer integral of the finite-rank 2D Bernstein inner test for F equals that
-- for the transpose (fun a b => F b a): finrank_fubini reduces each side to Σᵢⱼ F(i/n,j/n)(∫bᵢ)(∫bⱼ),
-- equal under the discrete grid-index swap RsumN_swap + Rmul commutativity. One integration order only
-- on each side — NOT a continuous Fubini order interchange. No positivity, no limit, no crux.
#print axioms Square.bern2D_finrank_symm

-- The general Fubini swap (new Square/Bern2DGeneralSwap.lean): Move 3 CAPSTONE of the 2D-Bernstein
-- route. For jointly-Lipschitz F on the unit square, the two GENUINE iterated integrals are equal:
-- ∫_x∫_y F = ∫_y∫_x F (LHS = ∫ paramIntegralTest F, RHS = ∫ paramIntegralTest (fun a b => F b a)).
-- Per schedule δ=k+1,n=(k+1)²: bern2D_outer_close at F and at the transpose + bern2D_finrank_symm
-- (Sₙ(F)=Sₙ(Fᵀ)) identify the two Bernstein anchors; anchored triangle scaled by 2δn, divided out by
-- Rle_of_Rmul_ofQ_le, closed by the Archimedean squeeze Req_of_Rle_ofQ_all. The swap is performed
-- HONESTLY via uniform Bernstein approximation — no closeness/limit/swap hypothesis assumed. No crux.
#print axioms Square.bern2D_general_swap

-- The windowed general Fubini swap (new Square/Bern2DWindowSwap.lean): generalizes bern2D_general_swap
-- from the unit square to ARBITRARY rational windows [a,a+w] x [c,c+v] by affine reparametrization —
-- the double integral of F over the box equals the transposed double integral. The pulled-back
-- integrand G p q = F(a+w*p, c+v*q) is jointly-Lipschitz on the unit square (moduli w*Lx, v*Ly);
-- riemannIntegralI_reparam collapses each windowed integral to a width-scaled unit integral;
-- bern2D_general_swap at G supplies the unit-square equality; the shared w*v factor is stripped.
-- Reusable: affineMap_comp, riemannIntegralI_reparam, smul_lip_ofQ, paramIntegralTest_reparam. No crux.
#print axioms Square.affineMap_comp
#print axioms Square.riemannIntegralI_reparam
#print axioms Square.smul_lip_ofQ
#print axioms Square.paramIntegralTest_reparam
#print axioms Square.windowed_reparam_collapse
#print axioms Square.bern2D_general_swap_window

-- The convolution-Mellin coupled integrand (new Square/ConvMellinIntegrand.lean): the joint (x,t)
-- Lipschitz + bound of coupIntegrand F(x,t) = f(x*clampedInv(a,t))*g(t)*clampedInv(a,t)*psi(x), the
-- inner two-variable integrand of mellinConv (P_x(t) times the Mellin weight psi(x)). The t-factor is
-- a genuine product L2Test couTest x, so the t-direction coup_lipY is l2lip of that product times the
-- psi bound (linchpin: couTest .L/.M are x-independent); coup_lipX reuses mulConvR_integrand_diff; the
-- joint coup_lip is the triangle. Regularity precondition for a later Fubini swap. No swap, no crux.
#print axioms Square.couLy_den
#print axioms Square.couLy_num
#print axioms Square.couLx_den
#print axioms Square.couLx_num
#print axioms Square.couB_den
#print axioms Square.couB_num
#print axioms Square.coup_lipY
#print axioms Square.coup_lipX
#print axioms Square.coup_lip
#print axioms Square.coup_bd
#print axioms Square.coup_fcY
#print axioms Square.coup_fcX

-- The Fubini swap of the convolution-Mellin pairing (new Square/MellinConvFubini.lean): applying the
-- windowed 2D-Bernstein swap to mellinConv. mellinConv_eq_paramInt is the structural identity that
-- mellinConv is the x-outer double integral of coupIntegrand (per-x: pull the t-constant psi(x) out by
-- riemannIntegralI_Rsmul, and int_t (couTest x).f = mulConvRTest.f x by certif_irrel same-integrand);
-- mellinConv_fubini feeds the committed coup_* witnesses to bern2D_general_swap_window for the t-outer
-- form. Inner int_x left unevaluated (the later dilation-covariance step). No new estimate, no crux.
#print axioms Square.mellinConv_eq_paramInt
#print axioms Square.mellinConv_fubini

-- The g-pullout of the swapped convolution-Mellin inner integral (new Square/MellinConvGPull.lean):
-- coupOuterTestSwap.f t = int_x coupIntegrand(x,t) dx has an x-constant weight W(t)=g(t)*clampedInv(a,t)
-- buried in the integrand; coupOuterTestSwap_gpull regroups coupIntegrand = W(t)*D(x,t) (gpull_regroup)
-- then pulls W(t) out by riemannIntegralI_Rsmul, isolating dilMellinF = int_x D(x,t) dx (D = the
-- dilated-Mellin-of-f integrand f(clamp x*clampedInv(a,t))*psi(x), dilIntegrand_lipX its x-Lipschitz).
-- mellinConv_gpull composes with mellinConv_fubini. dilMellinF LEFT UNEVALUATED (the later half-line
-- dilation-covariance step). Scalar-linearity regrouping only. No dilation covariance, no crux.
#print axioms Square.dilLx_den
#print axioms Square.dilLx_num
#print axioms Square.dilIntegrand_lipX
#print axioms Square.dilIntegrand_fcX
#print axioms Square.coupOuterTestSwap_gpull
#print axioms Square.mellinConv_gpull
-- The FIRST evaluation of dilMellinF (new Square/DilMellinFEval.lean): dilMellinF_eq_pairing — on any
-- window [xlo,xlo+xw] ⊆ [0,S] the clamp qBandQ 0 S inside dilIntegrand is inert, so
-- dilMellinF f ψ S a t = innerIonI (dilateTestR (clampedInv a t) f) ψ [xlo,xlo+xw], the clean interval
-- L² pairing of the real-scale dilated test against ψ. Strips the clamp and lands dilMellinF on the
-- pairing/dilation-covariance machinery (the next factorization step reads the covariance off this).
-- Content = qBandQ_eq_of_band on the affine window point + Rmul_comm, across two integrand moduli via
-- riemannIntegralI_congr_unit_mod. NO covariance, NO half-line assembly, NO factorization, NO crux.
#print axioms Square.dilMellinF_eq_pairing
-- dilMellinF at the moment window [0,1] with weight powTest n is the moment of the dilated test
-- (Square/DilMellinFEval.lean): dilMellinF_eq_mellinMoment — specialise dilMellinF_eq_pairing to the
-- [0,1] window (needs only S ≥ 1) and collapse the interval pairing to the plain moment via
-- riemannIntegralI_unit, giving dilMellinF f (powTest n) S a t = mellinMoment (dilateTestR (clampedInv a t) f) n.
-- Lands the factorization's inner integral (moment window) on mellinMoment, which carries its own
-- rational-scale dilation covariance (mellinMoment_dilate). NO real-scale covariance, NO factorization, NO crux.
#print axioms Square.dilMellinF_eq_mellinMoment
-- dilMellinF at the tail window [m+1,m+2] is the twisted-tail term of the dilated test
-- (Square/DilMellinFEval.lean): dilMellinF_eq_twTerm — the HALF-LINE analogue of dilMellinF_eq_mellinMoment.
-- On [m+1,m+2] ⊆ [0,S] (m+2 ≤ S) the clamp is inert, so dilMellinF f (powWinTest m n) S a t =
-- innerIonI (dilateTestR c f) (powWinTest m n) [m+1,m+2], which is DEFINITIONALLY twTerm (dilateTestR c f) n m
-- (same riemannIntegralI, proof-irrelevant window args). Pure composition of dilMellinF_eq_pairing. Summing
-- these over m (+ the [0,1] moment) is the half-line decomposition mellinHat = mellinMoment + twTail — the level
-- the prime side reads (tests at prime powers ≥ 1), which the [0,1] moment track alone cannot reach. No
-- half-line assembly yet, NO factorization, NO crux.
#print axioms Square.dilMellinF_eq_twTerm

-- The per-window rational-scale Mellin dilation (new Square/MellinWindowDilate.lean): the FIRST
-- sub-brick of the eventual dilation covariance. For rational s>0 and a window [lo,lo+w],
-- int over [s*lo, s*(lo+w)] of (f*P) = s^(n+1) * int over [lo,lo+w] of (dilateTest s f * P) — ONE
-- linear change of variables (riemannIntegralI_dilate, Jacobian s) plus degree-n homogeneity of the
-- weight (P(s*x)=s^n*P(x), Rpow_dilate_ofQ; s^n pulled out). The homogeneity is an EXPLICIT hHom
-- hypothesis, discharged for the genuine clamped weight powTest n by powTest_dilate_on (clamp-inert on
-- the window). NO half-line, NO exhaustion-independence, NO real-scale dilation, NO factorization, NO crux.
#print axioms Square.Rpow_dilate_ofQ
#print axioms Square.powTest_dilate_on
#print axioms Square.mellinWindowDilate

-- The integer-exponent Mellin transform of the convolution (new Square/MellinConvInt.lean).
#print axioms Square.bandTest_nonneg
#print axioms Square.powWinTest_nonneg
#print axioms Square.mellinConvInt_nonneg

-- The exp bounds + per-step logarithm bracket (new Analysis/ExpBounds.lean).
#print axioms Analysis.RexpReal_R_ge_one
#print axioms Analysis.RexpReal_ofQ_ge_one_add
#print axioms Analysis.qpow_unit
#print axioms Analysis.expTerm_unit_le
#print axioms Analysis.expSum_unit_le_geom
#print axioms Analysis.expSum_unit_le
#print axioms Analysis.RexpReal_unit_le
#print axioms Analysis.logN_step_upper
#print axioms Analysis.logN_step_lower

-- The harmonic-log bridge and ∫₀¹ dx/(1+x) ≈ log 2 (new Analysis/HarmonicLog.lean).
#print axioms Analysis.Rlim_eval_real
#print axioms Analysis.Rneg_involutive
#print axioms Analysis.Rsub_le_of_le_Radd
#print axioms Analysis.Rsub_nonpos_of_Rle
#print axioms Analysis.Radd_le_cancel_right
#print axioms Analysis.Rsub_shift_drop
#print axioms Analysis.hFold_den_pos
#print axioms Analysis.hFoldLo_den_pos
#print axioms Analysis.logN_telescope_upper
#print axioms Analysis.logN_telescope_lower
#print axioms Analysis.hFold_eq_hFoldLo
#print axioms Analysis.log2_le_hFold
#print axioms Analysis.hFold_le_log2_add
#print axioms Analysis.hFold_log2_defect
#print axioms Analysis.gRecip_lip
#print axioms Analysis.gRecip_congr
#print axioms Analysis.gRecip_point
#print axioms Analysis.harmTermFold_den_pos
#print axioms Analysis.RsumN_gRecip
#print axioms Analysis.harmTermFold_scale
#print axioms Analysis.riemannSum_gRecip
#print axioms Analysis.dyadicR_gRecip_zero
#print axioms Analysis.genSum_gRecip_rate
#print axioms Analysis.riemannIntegral_recip_gen
#print axioms Analysis.riemannIntegral_recip

-- The tent f̃(0) component ≈ log 2 (new Analysis/TentLogPiece.lean).
#print axioms Analysis.Rsub_Rneg_pair
#print axioms Analysis.Rsub_const_sub
#print axioms Analysis.Rmul_two_eq
#print axioms Analysis.tentF1_lip
#print axioms Analysis.tentF1_congr
#print axioms Analysis.tentF2_lip
#print axioms Analysis.tentF2_congr
#print axioms Analysis.Rabs_Rsub_swap
#print axioms Analysis.tent_arg1
#print axioms Analysis.tent_pull1
#print axioms Analysis.tent_pull2
#print axioms Analysis.gRecip_lip_at
#print axioms Analysis.s2g_lip
#print axioms Analysis.s2g_congr
#print axioms Analysis.n2g_lip
#print axioms Analysis.n2g_congr
#print axioms Analysis.G1_lip
#print axioms Analysis.G1_congr
#print axioms Analysis.G2_lip
#print axioms Analysis.G2_congr
#print axioms Analysis.tent_pieceB1
#print axioms Analysis.tent_pieceB2
#print axioms Analysis.tentPoleB_eq

-- General log-additivity + ∫₀¹ dx/(2+x) = log 3 − log 2 (new Analysis/HarmonicLog32.lean).
#print axioms Analysis.logN_mul_gen
#print axioms Analysis.Rle_Rsub_of_Radd_le
#print axioms Analysis.log32_le_hFold
#print axioms Analysis.hFold32_le
#print axioms Analysis.hFold32_defect
#print axioms Analysis.gRecip32_lip
#print axioms Analysis.gRecip32_congr
#print axioms Analysis.gRecip32_point
#print axioms Analysis.harmTermFold32_den_pos
#print axioms Analysis.RsumN_gRecip32
#print axioms Analysis.harmTermFold32_scale
#print axioms Analysis.riemannSum_gRecip32
#print axioms Analysis.dyadicR_gRecip32_zero
#print axioms Analysis.genSum_gRecip32_rate
#print axioms Analysis.riemannIntegral_recip32_gen
#print axioms Analysis.riemannIntegral_recip32

-- The arch tail's [1,2] piece (new Analysis/TentArchPiece.lean).
#print axioms Analysis.tentArch1_lip
#print axioms Analysis.tentArch1_congr
#print axioms Analysis.tent_arch_pull
#print axioms Analysis.s4g32_lip
#print axioms Analysis.s4g32_congr
#print axioms Analysis.n4g32_lip
#print axioms Analysis.n4g32_congr
#print axioms Analysis.innerG_lip
#print axioms Analysis.innerG_congr
#print axioms Analysis.XG_lip
#print axioms Analysis.XG_congr
#print axioms Analysis.G3_lip
#print axioms Analysis.G3_congr
#print axioms Analysis.gRecip32_lip_at
#print axioms Analysis.tent_arch12

-- The general-base harmonic bridge ∫₀¹ dx/(c+x) = log(c+1) − log c (new Analysis/HarmonicLogC.lean).
#print axioms Analysis.logC_le_hFold
#print axioms Analysis.hFoldC_le
#print axioms Analysis.hFoldC_defect
#print axioms Analysis.gRecipC_lip
#print axioms Analysis.gRecipC_congr
#print axioms Analysis.gRecipC_lip_at
#print axioms Analysis.gRecipC_point
#print axioms Analysis.harmTermFoldC_den_pos
#print axioms Analysis.RsumN_gRecipC
#print axioms Analysis.harmTermFoldC_scale
#print axioms Analysis.riemannSum_gRecipC
#print axioms Analysis.dyadicR_gRecipC_zero
#print axioms Analysis.genSum_gRecipC_rate
#print axioms Analysis.riemannIntegral_recipC_gen
#print axioms Analysis.riemannIntegral_recipC

-- The improper archimedean tail = log 3 and the assembled tail (new Analysis/TentArchTail.lean).
#print axioms Analysis.tail_step_alg
#print axioms Analysis.hTail_lip
#print axioms Analysis.hTail_congr
#print axioms Analysis.diffC_lip
#print axioms Analysis.diffC_congr
#print axioms Analysis.hTail_pull
#print axioms Analysis.integralTerm_hTail
#print axioms Analysis.genSum_hTail
#print axioms Analysis.tail_decay
#print axioms Analysis.tail_rate
#print axioms Analysis.improperTail_eq
#print axioms Analysis.tentArchTail_eq

-- THE FIRST REALIZED WEIL SLOT + the first realized window-positivity instance
-- (new Square/TentSlot.lean).
#print axioms Square.tentF_supp_high
#print axioms Square.tentF_supp_low
#print axioms Square.tentF_two
#print axioms Square.tentF_half
#print axioms Square.tentF_one
#print axioms Square.tentPrimePart_eq
#print axioms Square.tentArchConst_eq
#print axioms Square.tentWeilValue_eq
#print axioms Square.tentL2q_den
#print axioms Square.tentU32q_den
#print axioms Square.tentL32q_den
#print axioms Square.tent_L2
#print axioms Square.tent_U32
#print axioms Square.tent_L32
#print axioms Square.tent_L3
#print axioms Square.tentSLq_den
#print axioms Square.tentTUq_den
#print axioms Square.tentBUq_den
#print axioms Square.tentPLq_den
#print axioms Square.tent_B_le
#print axioms Square.tent_P_ge
#print axioms Square.tentWeilValue_pos

-- The bump slot: the first realized test whose support MEETS the primes (prime side
-- = log 2), its evaluated integrals, and the first certified NEGATIVE Weil value
-- (new Analysis/BumpPieces.lean + Square/BumpSlot.lean).
#print axioms Analysis.bump_pieceA1
#print axioms Analysis.bump_pieceA2
#print axioms Analysis.bumpPoleA_eq
#print axioms Analysis.bumpB1_lip
#print axioms Analysis.bumpB1_congr
#print axioms Analysis.bumpB2_lip
#print axioms Analysis.bumpB2_congr
#print axioms Analysis.bump_pieceB1
#print axioms Analysis.bump_pieceB2
#print axioms Analysis.bumpPoleB_eq
#print axioms Analysis.bumpT1_lip
#print axioms Analysis.bumpT1_congr
#print axioms Analysis.bumpT2_lip
#print axioms Analysis.bumpT2_congr
#print axioms Analysis.bump_pieceT1
#print axioms Analysis.bump_pieceT2
#print axioms Analysis.bumpArchTail_eq
#print axioms Square.bumpF_supp_high
#print axioms Square.bumpF_supp_low
#print axioms Square.bumpF_one
#print axioms Square.bumpF_half
#print axioms Square.bumpF_third
#print axioms Square.bumpF_two
#print axioms Square.bumpF_three
#print axioms Square.bumpPrimePart_eq
#print axioms Square.bumpArchConst_eq
#print axioms Square.bumpWeilValue_eq
#print axioms Square.bmpL2q_den
#print axioms Square.bmpU32q_den
#print axioms Square.bmpL43q_den
#print axioms Square.bmp_L2
#print axioms Square.bmp_U32
#print axioms Square.bmp_L43
#print axioms Square.bmpPUq_den
#print axioms Square.bmpSLq_den
#print axioms Square.bump_P_le
#print axioms Square.bump_S_ge
#print axioms Square.bumpWeilValue_neg

-- The cone-shaped test: the square-scale log-tent (autocorrelation shape, rational
-- generating box [1/2, 2]), the first cone-shaped datum with a live prime side, and
-- its evaluated finite-place side (new Square/ConeTent.lean).
#print axioms Square.t4F_supp_high
#print axioms Square.t4F_supp_low
#print axioms Square.t4F_one
#print axioms Square.t4F_two
#print axioms Square.t4F_half
#print axioms Square.t4F_three
#print axioms Square.t4F_third
#print axioms Square.t4F_four
#print axioms Square.t4F_quarter
#print axioms Square.t4PrimePart_eq

-- The ∫log layer, part 1: the antiderivative step bracket Gn(i)+log i ≤ Gn(i+1) ≤
-- Gn(i)+log(i+1), its telescopes, and the harmonic gap bound (new Analysis/LogStep.lean).
#print axioms Analysis.Gn_one
#print axioms Analysis.Gn_step_lower
#print axioms Analysis.Gn_step_upper
#print axioms Analysis.Gn_tele_lower
#print axioms Analysis.Gn_tele_upper
#print axioms Analysis.logFold_gap

-- The ∫log layer, part 2a: Qmin + the per-index ceiling qCapQ + the two-sided band
-- clamp qBandQ (new Analysis/BandClamp.lean).
#print axioms Analysis.Qmin_eq_left
#print axioms Analysis.Qmin_eq_right
#print axioms Analysis.Qmin_den_pos
#print axioms Analysis.Qmin_le_left
#print axioms Analysis.Qmin_le_right
#print axioms Analysis.Qle_Qmin
#print axioms Analysis.Qmin_const_lip
#print axioms Analysis.qCapQ_le
#print axioms Analysis.qCapQ_ge
#print axioms Analysis.qCapQ_congr
#print axioms Analysis.qCapQ_lipschitz
#print axioms Analysis.qCapQ_eq_of_le
#print axioms Analysis.qBandQ_ge
#print axioms Analysis.qBandQ_le
#print axioms Analysis.qBandQ_one_num_pos
#print axioms Analysis.qBandQ_witness
#print axioms Analysis.qBandQ_congr
#print axioms Analysis.qBandQ_lipschitz
#print axioms Analysis.qBandQ_eq_of_band

-- The ∫log layer, part 2b: the totalized log integrand gLog c (RlogPos over the band
-- clamp), Lipschitz + congruence, instances c = 1, 2, 3 (new Analysis/LogIntegrand.lean).
#print axioms Analysis.gLogArg_pos
#print axioms Analysis.gLogArg_hi
#print axioms Analysis.gLogArg_ge1
#print axioms Analysis.gLogArg_lo
#print axioms Analysis.gLogArg_witness
#print axioms Analysis.gLog_congr_of
#print axioms Analysis.gLog_lip_of
#print axioms Analysis.gLog1_congr
#print axioms Analysis.gLog1_lip
#print axioms Analysis.gLog2_congr
#print axioms Analysis.gLog2_lip
#print axioms Analysis.gLog3_congr
#print axioms Analysis.gLog3_lip

-- The ∫log layer, part 2c(i): the uniform small-radius certificate for the
-- log-of-rational bridge, general in the sample (new Analysis/LogRatCert.lean).
#print axioms Analysis.radius_half_of_le4
#print axioms Analysis.radius_half_proj
#print axioms Analysis.sample_ge_one

-- The ∫log layer, part 2c(ii): the log-of-rational bridge, RlogPos(a/d) ≈ logN a − logN d
-- via exp-injectivity, general on the band d ≤ a ≤ 4d (new Analysis/LogRatBridge.lean).
#print axioms Analysis.RlogPos_ofQ_eq_logN

-- The ∫log layer, part 2c(iii): the point values, gLog c (j/(N+1)) ≈ logN(c(N+1)+j) −
-- logN(N+1), general in the dyadic sample (new Analysis/LogPointVal.lean).
#print axioms Analysis.gLog_point

-- The ∫log layer, part 2c(iv): the Riemann-sum fold + collapse, the logFold bracket
-- between Gn differences, and the scale identity (new Analysis/LogRiemann.lean).
#print axioms Analysis.RsumN_gLog
#print axioms Analysis.riemannSum_gLog
#print axioms Analysis.logFold_le_Gn
#print axioms Analysis.Gn_le_logFold
#print axioms Analysis.Gn_scale_expand
#print axioms Analysis.Gn_scale_identity

-- The ∫log layer, part 2c(v): the evaluation — ∫₀¹ log(c+t) dt = Gn(c+1) − Gn(c),
-- rate + Rlim_eval_real, headline instances c = 1, 2, 3 (new Analysis/LogIntegralEval.lean).
#print axioms Analysis.hFold_le_ratio
#print axioms Analysis.scaled_hFold_le
#print axioms Analysis.dyadicR_gLog_pow
#print axioms Analysis.dyadicR_gLog_zero
#print axioms Analysis.dyadicR_gLog_defect
#print axioms Analysis.genSum_gLog_rate
#print axioms Analysis.riemannIntegral_logC_gen
#print axioms Analysis.riemannIntegral_logC1
#print axioms Analysis.riemannIntegral_logC2
#print axioms Analysis.riemannIntegral_logC3

-- The t4PoleA pieces: generic const±f integral vehicles + the five constructed interval
-- integrals of the cone tent, evaluated (new Analysis/T4PoleAPieces.lean).
#print axioms Analysis.lip_const_sub
#print axioms Analysis.congr_const_sub
#print axioms Analysis.lip_const_add
#print axioms Analysis.congr_const_add
#print axioms Analysis.lip_neg
#print axioms Analysis.congr_neg
#print axioms Analysis.int_const_add_eval
#print axioms Analysis.int_const_sub_eval
#print axioms Analysis.t4A12_eq
#print axioms Analysis.t4A23_eq
#print axioms Analysis.t4A34_eq
#print axioms Analysis.t4Ah_eq
#print axioms Analysis.t4Aq_eq

-- The t4PoleA assembly, part 1: the first exact piece value (∫₁²(2log2 − logx) = 1)
-- and the Gn 3 telescope (new Analysis/T4PoleAAssembly.lean).
#print axioms Analysis.t4A12_val
#print axioms Analysis.t4A2334_val

-- The t4PoleA assembly, part 2: NF components and the exact value 9/4.
#print axioms Analysis.gn21_nf
#print axioms Analysis.gn42_nf
#print axioms Analysis.a2334_nf
#print axioms Analysis.ah_nf
#print axioms Analysis.aq_nf
#print axioms Analysis.t4PoleA_eq

-- The ∫log/x layer, part 1: the log-squared antiderivative Hn = (log n)^2 and its
-- unit-step bracket via difference of squares (new Analysis/LogSqStep.lean).
#print axioms Analysis.Hn_one
#print axioms Analysis.Hn_step_lower
#print axioms Analysis.Hn_step_upper

-- The ∫log/x layer, part 2: the step-folds and the Hn telescopes.
#print axioms Analysis.Hn_tele_lower
#print axioms Analysis.Hn_tele_upper

-- The ∫log/x layer, part 3: the fold gap (crude log ≤ n + the harmonic telescope).
#print axioms Analysis.gapQ_den_pos
#print axioms Analysis.hsFold_gap

-- The ∫log/x layer, part 4a: the sample fold and its foldHi comparison.
#print axioms Analysis.hsSample_le_foldHi

-- The ∫log/x layer, part 4b: the reverse slack and the two-sided sample bracket.
#print axioms Analysis.hsFoldHi_le_sample
#print axioms Analysis.Hn_sample_upper
#print axioms Analysis.Hn_sample_lower

-- The ∫log/x layer, part 5: the integrand family gLx = 2·gLog·gRecipC with bounds,
-- congruence, and the product-Lipschitz certificate (new Analysis/LogOverX.lean).
#print axioms Analysis.gLog_nonneg
#print axioms Analysis.gLog_le
#print axioms Analysis.twoGLog_abs
#print axioms Analysis.twoF_lip
#print axioms Analysis.gRecipC_abs
#print axioms Analysis.gLx_congr_of
#print axioms Analysis.gLx_lip_of

-- The ∫log/x layer, part 6: the point values and the Riemann fold/collapse
-- (new Analysis/LogOverXSum.lean).
#print axioms Analysis.gLx_point
#print axioms Analysis.RsumN_gLx
#print axioms Analysis.riemannSum_gLx

-- The ∫log/x layer, part 7: the Hn scale identity ((a+b)-squared over logN_mul_gen).
#print axioms Analysis.Hn_scale_expand
#print axioms Analysis.Hn_scale_diff

-- The ∫log/x layer, part 8a: log(2^m) ≤ m and the E-capped fold gap (the log-aware
-- slack that decays like m/M after the harmonic telescope).
#print axioms Analysis.logN_two_le_one
#print axioms Analysis.logN_two_pow_le
#print axioms Analysis.gapQE_den_pos
#print axioms Analysis.hsFold_gap_cap

-- The ∫log/x layer, part 8b-i: the rate ingredients (schedule arithmetic, per-cell
-- log cap, capped sample bracket, rational gap collapse; new Analysis/LogOverXRate.lean).
#print axioms Analysis.lxr_sched
#print axioms Analysis.logN_succ_le_two
#print axioms Analysis.lxr_cap
#print axioms Analysis.Hn_sample_upper_cap
#print axioms Analysis.gapQE_le

-- The ∫log/x layer, part 8b-ii: the dyadic defect |D_m − (Hn(c+1) − Hn(c))| ≤ (5m+5)/2^m
-- (new Analysis/LogOverXEval.lean).
#print axioms Analysis.dyadicR_gLx_pow
#print axioms Analysis.dyadicR_gLx_defect

-- The ∫log/x layer, part 8c: the anchor, the schedule rate, and the EVALUATION —
-- ∫₀¹ 2log(c+t)/(c+t) dt = Hn(c+1) − Hn(c) at c = 1, 2, 3.
#print axioms Analysis.dyadicR_gLx_zero
#print axioms Analysis.genSum_gLx_rate
#print axioms Analysis.riemannIntegral_gLx_gen
#print axioms Analysis.riemannIntegral_gLx1
#print axioms Analysis.riemannIntegral_gLx2
#print axioms Analysis.riemannIntegral_gLx3

-- The real-scalar reciprocal evaluation: ∫₀¹ C·(1/(c+t)) = C·(log(c+1) − log c) for
-- bounded real C (new Analysis/RecipSmulEval.lean) — the poleB pieces' engine.
#print axioms Analysis.riemannIntegral_recipC_smul

-- The t4PoleB pieces, part 1: the smul/add Lipschitz combinators and the cone-height
-- bounds (new Analysis/T4PoleBPieces.lean).
#print axioms Analysis.smul_lip
#print axioms Analysis.smul_congr
#print axioms Analysis.add_lip
#print axioms Analysis.add_congr_fn
#print axioms Analysis.t4H_nonneg
#print axioms Analysis.t4H_abs
#print axioms Analysis.oneL_abs

-- The t4PoleB pieces, part 2: the upper-piece evaluation (t4H·recip − ½·gLx).
#print axioms Analysis.negHalf_abs
#print axioms Analysis.LxQ_den_pos
#print axioms Analysis.LxQ_num_nonneg
#print axioms Analysis.t4B_upper_eval

-- The t4PoleB pieces, part 3: the lower-piece evaluation (C·recip + ½·gLx; the log
-- measure dx/x pulls back with NO outer weight).
#print axioms Analysis.posHalf_abs
#print axioms Analysis.t4B_lower_eval

-- The t4PoleB pieces, part 4: the five constructed pieces and their evaluations.
#print axioms Analysis.t4B12_eq
#print axioms Analysis.t4B23_eq
#print axioms Analysis.t4B34_eq
#print axioms Analysis.t4Bh_eq
#print axioms Analysis.t4Bq_eq

-- The t4PoleB assembly: t4PoleB = t4H·t4H = 4(log2)^2, EXACT.
#print axioms Analysis.t4PoleB_eq

-- The t4 arch tail, part 1: the compact reciprocal half (recipC_smul instances at
-- bases 2, 3, 4, telescoping to t4H·(log5 − log2); new Analysis/T4ArchPieces.lean).
#print axioms Analysis.t4Trecip_eq
#print axioms Analysis.t4Trecip_sum

-- The t4 arch tail, part 2: the improper remainder ∫₁^∞ (1/(w+2) − 1/(w+4)) = log5 −
-- log3 (the shifted TentArchTail mirror; new Analysis/T4TailImproper.lean).
#print axioms Analysis.t4Tail_lip
#print axioms Analysis.t4Tail_congr
#print axioms Analysis.t4Tail_pull
#print axioms Analysis.integralTerm_t4Tail
#print axioms Analysis.genSum_t4Tail
#print axioms Analysis.t4tail_decay
#print axioms Analysis.t4tail_rate
#print axioms Analysis.t4Improper_eq

-- The monotone dyadic bracket: for sample-antitone integrands ONE finite dyadic sum
-- brackets the certified integral (D_M − V/2^M ≤ ∫₀¹f ≤ D_M) — the bracket engine for
-- integrals with no closed form (new Analysis/MonotoneIntegral.lean).
#print axioms Analysis.const_le_Rlim
#print axioms Analysis.RsumN_telescope
#print axioms Analysis.Rneg_Rsub_flip
#print axioms Analysis.Rle_Radd_of_Rsub_le
#print axioms Analysis.riemannIntegral_le_sample
#print axioms Analysis.riemannSum_refine_regroup
#print axioms Analysis.riemannSum_refine_anti
#print axioms Analysis.riemannSum_refine_gap
#print axioms Analysis.dyadicR_anti_step
#print axioms Analysis.dyadicR_gap_step
#print axioms Analysis.dyadicR_level_anti
#print axioms Analysis.dyadicR_level_gap
#print axioms Analysis.riemannIntegral_anti_upper
#print axioms Analysis.riemannIntegral_anti_lower

-- The dilog kernel Φ(u) = ∫₀¹ ds/(1+s·band(u)): the totalized integrand of the t4
-- dilog ∫₁⁴ logx/(x−1)dx with the removable singularity REMOVED BY CONSTRUCTION
-- (new Analysis/DilogPhi.lean).
#print axioms Analysis.bandU_congr
#print axioms Analysis.bandU_lip
#print axioms Analysis.bandU_nonneg
#print axioms Analysis.bandU_le
#print axioms Analysis.bandU_abs
#print axioms Analysis.bandU_ofQ
#print axioms Analysis.Qinv_anti
#print axioms Analysis.one_add_mul_num_pos
#print axioms Analysis.one_le_one_add_mul
#print axioms Analysis.phiInner_congr
#print axioms Analysis.phiInner_lip
#print axioms Analysis.Phi_congr
#print axioms Analysis.Phi_diff_le
#print axioms Analysis.Phi_lip
#print axioms Analysis.phiInner_ofQ
#print axioms Analysis.Phi_ofQ_anti

-- The dilog kernel's rational brackets: phiRat(u,2^M−1) − (3/4)/2^M ≤ Φ(u) ≤ phiRat —
-- the whole sample layer is exact rational arithmetic (new Analysis/DilogPhiVal.lean).
#print axioms Analysis.qFoldPhi_den_pos
#print axioms Analysis.phiRat_den_pos
#print axioms Analysis.RsumN_phi_eq
#print axioms Analysis.riemannSum_phi_eq
#print axioms Analysis.phiInner_sampleAnti
#print axioms Analysis.phiInner_var
#print axioms Analysis.phi_sched
#print axioms Analysis.Phi_ofQ_le
#print axioms Analysis.Phi_ofQ_ge

-- The constructed t4 dilog: three kernel pieces ∫₀¹Φ(c'+t)dt and the outer monotone
-- bracket machinery (new Analysis/DilogPieces.lean).
#print axioms Analysis.dgPiece_congr
#print axioms Analysis.dgPiece_lip
#print axioms Analysis.dgPiece_sampleAnti
#print axioms Analysis.qFoldLo_den_pos
#print axioms Analysis.RsumN_dg_ge
#print axioms Analysis.dyadicR_dg_ge
#print axioms Analysis.dg_var
#print axioms Analysis.dilogPiece_ge

-- The certified dilog lower bound t4Dilog ≥ 1.909 (true ≈ 1.93939): the first fully
-- rational bracket of a log-type integral (new Analysis/DilogValue.lean).
#print axioms Analysis.t4Dilog_ge

-- THE REALIZED CONE SLOT (new Square/ConeSlot.lean): t4Slot (every field a genuine
-- constructed integral), the closed form, and **W(t4) > 0** — the first certified
-- positivity on the autocorrelation cone with a live prime side (margin ≈ +0.0558;
-- M = 512 wedges + the rational dilog bound). One cone element, NOT the cone
-- (uniform positivity on the cone = RH); crux fields stay none.
#print axioms Square.t4U2q_den
#print axioms Square.t4L2q_den
#print axioms Square.t4_U2
#print axioms Square.t4_L2
#print axioms Square.t4U32q_den
#print axioms Square.t4_U32
#print axioms Square.t4L32q_den
#print axioms Square.t4_L32
#print axioms Square.t4U3q_den
#print axioms Square.t4_U3
#print axioms Square.t4L3q_den
#print axioms Square.t4_L3
#print axioms Square.t4H_le
#print axioms Square.t4H_ge
#print axioms Square.t4ArchConst_eq
#print axioms Square.t4ArchTail_eq
#print axioms Square.t4WeilValue_eq
#print axioms Square.t4PLq_den
#print axioms Square.t4Sq_den
#print axioms Square.t4BUq_den
#print axioms Square.t4_P_ge
#print axioms Square.t4_S_ge
#print axioms Square.t4_S_nonneg
#print axioms Square.t4_S_le
#print axioms Square.t4_B_le
#print axioms Square.t4WeilValue_pos

-- THE PRE-HILBERT LAYER, brick 1 (Square/PreHilbert.lean) — the Sonine route's step 3 opened:
-- the truncated inner product with the four inner-product laws, prefix monotonicity, and the
-- sqrt-free Cauchy–Schwarz via the LAGRANGE IDENTITY (the defect as an explicit SOS).
#print axioms Square.RsumN_neg
#print axioms Square.RsumN_sub
#print axioms Square.RsumN_le_prefix
#print axioms Square.innerN_congr
#print axioms Square.innerN_symm
#print axioms Square.innerN_add_left
#print axioms Square.innerN_smul_left
#print axioms Square.innerN_self_nonneg
#print axioms Square.innerN_self_mono
#print axioms Square.lagSOS_nonneg
#print axioms Square.Rsub_sq_expand
#print axioms Square.lagrange_identity
#print axioms Square.cauchy_schwarz

-- THE PRE-HILBERT LAYER, brick 2 (Square/SelfAdjoint.lean) — kernels as operators and finite
-- self-adjointness: weilQuad = ⟨c, B·c⟩, symmetric kernels self-adjoint via the real Fubini
-- exchange, and the Sonine skeleton's multiplier form as the self-adjoint diagonal instance.
#print axioms Square.RsumN_swap
#print axioms Square.RsumN_mul_const
#print axioms Square.weilQuad_eq_inner
#print axioms Square.applyN_self_adjoint
#print axioms Square.gramOf_sym
#print axioms Square.multForm_sym
#print axioms Square.applyN_multForm
#print axioms Square.multForm_self_adjoint
#print axioms Square.burnol_pairing_eq_inner

-- THE PRE-HILBERT LAYER, brick 3 (Square/Projection.lean) — orthogonal projection and Bessel:
-- Fourier coefficients, the finite-rank projection, Bessel's inequality (sqrt-free), the
-- indicator basis, and the Sonine band restriction as a genuine self-adjoint idempotent
-- projection with unconditional pairing-positivity on its range.
#print axioms Square.innerN_neg_left
#print axioms Square.innerN_sub_left
#print axioms Square.inner_proj
#print axioms Square.proj_coeff
#print axioms Square.proj_self_inner
#print axioms Square.bessel
#print axioms Square.indic_ortho
#print axioms Square.bandProj_band
#print axioms Square.bandProj_idem
#print axioms Square.bandProj_self_adjoint
#print axioms Square.bandProj_pairing_nonneg

-- THE PRE-HILBERT LAYER, brick 4 (Square/StableInner.lean) — the N → ∞ passage for the
-- finitely-supported space: truncated inner products and Weil pairings STABILIZE past the
-- support bound (the direct limit is attained); the band projection acts on the space.
#print axioms Square.RsumN_stable
#print axioms Square.innerN_stable
#print axioms Square.innerN_welldef
#print axioms Square.weilQuad_stable
#print axioms Square.weilQuad_welldef
#print axioms Square.FinSupp_bandProj

-- THE PRE-HILBERT LAYER, brick 5 (Analysis/IntegralInner.lean) — the L² pairing over the
-- certified integral: the bounded-Lipschitz test class, innerI = ∫₀¹ φ·ψ with the product
-- certificate, norm positivity, and symmetry up to the certificate.
#print axioms Analysis.l2L_den
#print axioms Analysis.l2L_num
#print axioms Analysis.l2lip
#print axioms Analysis.l2fc
#print axioms Analysis.innerI_self_nonneg
#print axioms Analysis.l2lip_swap
#print axioms Analysis.l2fc_swap
#print axioms Analysis.innerI_symm_certif

-- THE PRE-HILBERT LAYER, brick 6 (Analysis/IntegralCertIrrel.lean) — CERTIFICATE INDEPENDENCE
-- of the certified integral (the value depends only on the integrand): the telescoping Cauchy
-- modulus of the dyadic sums, the two-sided distance-to-limit, the rate-generalized limit
-- evaluation, and the L² pairing's honest symmetry.
#print axioms Analysis.RTendsTo_le_Rsub
#print axioms Analysis.Rabs_dist_Rlim
#print axioms Analysis.Rlim_eval_real_rate
#print axioms Analysis.dyadicTerm_abs_bound
#print axioms Analysis.genSum_gap
#print axioms Analysis.digammaMidx_ge
#print axioms Analysis.riemannIntegral_certif_irrel
#print axioms Analysis.innerI_symm

-- THE PRE-HILBERT LAYER, brick 7 (Analysis/IntegralBilinear.lean) — bilinearity of the L²
-- pairing: the test class closed under addition, certificates weakened to a common modulus,
-- additivity in both slots via certificate independence.
#print axioms Analysis.lip_weaken
#print axioms Analysis.innerI_add_left
#print axioms Analysis.innerI_add_right

-- THE PRE-HILBERT LAYER, brick 8 (Square/IntegralCS.lean) — the per-level Cauchy–Schwarz for
-- Riemann sums (brick 1's discrete CS through the definitional sample-family identification,
-- uniform weight squaring out sqrt-free), the uniform bound on Riemann sums, and the effective
-- dyadic error bound |∫f − D_m| ≤ (⌈L⌉+2)/m. Plus Rabs_Rsub_symm made public (brick 6).
#print axioms Analysis.Rabs_Rsub_symm
#print axioms Square.riemannSum_cauchy_schwarz
#print axioms Square.riemannSum_abs_le
#print axioms Square.riemannIntegral_dyadic_dist

-- THE PRE-HILBERT LAYER, brick 9 (Square/IntegralCSFull.lean) — THE INTEGRAL CAUCHY–SCHWARZ:
-- ⟨φ,ψ⟩² ≤ ⟨φ,φ⟩·⟨ψ,ψ⟩ for the L² pairing, by the ε-collapse over the per-level CS and the
-- effective dyadic error bound; the discrete Lagrange SOS carried through the dyadic limit.
#print axioms Square.Rabs_prod_diff
#print axioms Square.Rabs_le_of_close
#print axioms Square.qmul_eps_le
#print axioms Square.qmul_eps_le_left
#print axioms Square.l2bd
#print axioms Square.innerI_cauchy_schwarz

-- THE PRE-HILBERT LAYER, brick 10 (Square/TestAlgebra.lean) — the test ALGEBRA (closure under
-- multiplication, every certificate an existing lemma), the clamped identity/monomial tests,
-- the integer Mellin moments, and the uniform pairing bound.
#print axioms Square.clamp01_congr
#print axioms Square.clamp01_nonneg
#print axioms Square.clamp01_le_one
#print axioms Square.clamp01_abs
#print axioms Square.clamp01_ofQ
#print axioms Square.innerI_abs_le
#print axioms Square.mellinMoment_cs
#print axioms Square.mellinMoment_zero

-- THE PRE-HILBERT LAYER, brick 11 (Square/Parseval.lean) — Parseval at the full indicator
-- basis: the Fourier coefficients are the coordinates, the projection is the identity on the
-- truncation, and Bessel SATURATES — the finite-complete case of the completeness axis.
#print axioms Square.fourierC_indic
#print axioms Square.proj_indic_eq
#print axioms Square.parseval_indic
#print axioms Square.bessel_saturates_at_indic

-- THE PRE-HILBERT LAYER, brick 12 (Square/Parallelogram.lean) — the parallelogram law (the
-- identity certifying genuine inner-product geometry; cross terms cancel in the RsumL
-- multiset) and the sqrt-free squared-distance geometry with the doubling quasi-triangle.
#print axioms Square.innerN_add_right
#print axioms Square.innerN_sub_right
#print axioms Square.parallelogram
#print axioms Square.dist2_nonneg
#print axioms Square.dist2_self
#print axioms Square.dist2_symm
#print axioms Square.dist2_doubling

-- THE PRE-HILBERT LAYER, brick 13 (Square/PairingLimit.lean) — the completion axis opened:
-- Cauchy–Schwarz continuity of the pairing (squared modulus), the squared-Cauchy-to-RReg
-- conversion (order-reflection of squaring + the completeness bridge), the extended pairing
-- value pairingLim with its effective Bishop rate.
#print axioms Square.inner_sub_sq_le
#print axioms Square.pairing_RReg
#print axioms Square.pairingLim_dist

-- THE PRE-HILBERT LAYER, brick 14 (Square/PairingLimitI.lean) — the L² mirror of the
-- completion axis: negation/subtraction on the test class, the L² squared distance, the L²
-- Cauchy–Schwarz continuity, and the extended L² pairing along squared-Cauchy sequences.
#print axioms Square.innerI_neg_left
#print axioms Square.innerI_sub_left
#print axioms Square.dist2I_nonneg
#print axioms Square.innerI_sub_sq_le
#print axioms Square.pairingI_RReg
#print axioms Square.pairingILim_dist

-- THE PRE-HILBERT LAYER, brick 15 (Square/Completion.lean) — STRONG COMPLETENESS at fixed
-- truncation: the limit member CONSTRUCTED (coordinates = extended pairings against the
-- indicator basis), coordinate rates, and dist2-convergence with effective rate N·(2/(j+1))².
#print axioms Square.sqCauchy_pairing
#print axioms Square.limMember_coord_dist
#print axioms Square.limMember_converges

-- THE PRE-HILBERT LAYER, brick 16 (Square/CompleteComplement.lean) — the Sonine complement is
-- CLOSED under completion: band vanishing passes to limit members, and the skeleton's
-- unconditional complement-positivity survives the limit.
#print axioms Square.limMember_band_zero
#print axioms Square.sonine_complement_complete

-- THE PRE-HILBERT LAYER, brick 17 (Square/UniformCompletion.lean) — the truncation-uniform
-- completion: the limit coordinates are truncation-COHERENT, the diagonal member is one
-- infinite object, and it converges in dist2 at EVERY truncation.
#print axioms Square.limMember_coherent
#print axioms Square.limMemberU_eq
#print axioms Square.limMemberU_converges

-- THE PRE-HILBERT LAYER, brick 18 (Analysis/MellinDecay.lean) — the Mellin front opened: the
-- window bound (pointwise window bound ⟹ |∫ window| ≤ w·B), the decaying test class
-- MellinTest, the derived gateway data, and the certified half-line integral ∫₀^∞ φ.
#print axioms Analysis.riemannIntegralI_abs_le_window
#print axioms Analysis.mellinTerm_bound
#print axioms Analysis.mellinIntegral_nonneg

-- THE PRE-HILBERT LAYER, brick 19 (Square/WindowPower.lean) — the window power substrate of
-- the Mellin twist: the band-clamped identity per half-line window as a test (inert on its
-- window) and its iterated powers through the test algebra.
#print axioms Square.bandTest_inert
#print axioms Square.powWinTest_zero
#print axioms Square.powWinTest_succ_inert
#print axioms Square.qmul_le_right_mono
#print axioms Square.powWinTest_M_le

-- THE PRE-HILBERT LAYER (Square/RationalWindowPower.lean) — the window power substrate on an
-- ARBITRARY rational window [lo,hi]: bandGen (identity clamped to [lo,hi], inert on its window)
-- and its iterated powers powBandGen (= tⁿ on the window, bound ≤ hiⁿ). Generalizes the
-- integer-window powWinTest; the weight object the per-window Mellin dilation covariance consumes
-- (dilating [m+1,m+2] by rational s lands on the rational window [s(m+1),s(m+2)]). No integral,
-- no dilation, no positivity, no crux. (bandGen, powBandGen are defs — no audit line.)
#print axioms Square.bandGen_inert
#print axioms Square.powBandGen_zero
#print axioms Square.powBandGen_succ_inert
#print axioms Square.powBandGen_M_le

-- THE PRE-HILBERT LAYER (Square/RationalWindowDilate.lean) — the degree-n HOMOGENEITY of the
-- rational-window power powBandGen on its band: on a band containing both a point and its s-scaling,
-- powBandGen(s·y) = sⁿ·powBandGen(y) (powBandGen_dilate_on), via the band-inertness
-- powBandGen_eq_Rpow_on (= tⁿ on the band) + Rpow_dilate_ofQ. The hHom discharge mellinWindowDilate
-- consumes, generalized from the [0,1]-clamped powTest_dilate_on to the wide band. No integral,
-- no dilation covariance, no positivity, no crux.
#print axioms Square.powBandGen_eq_Rpow_on
#print axioms Square.powBandGen_dilate_on

-- THE PRE-HILBERT LAYER (Square/WindowDilatePow.lean) — the committed per-window rational-scale
-- Mellin dilation (mellinWindowDilate) INSTANTIATED at the twist weight powBandGen, on the integer
-- window [m+1,m+2], with the weight over a band [lo,hi] covering both the window and its s-scaling
-- [s(m+1),s(m+2)]. The hHom hypothesis is discharged by powBandGen_dilate_on; the four membership
-- facts come from the affine/scaling algebra under the band-containment hyps. Gives
-- ∫_{[s(m+1),s(m+2)]}(φ·powBandGen) = s^(n+1)·∫_{[m+1,m+2]}(dilate_s φ·powBandGen). No weight-swap,
-- no half-line assembly, no positivity, no crux.
#print axioms Square.window_dilate_powBandGen

-- THE PRE-HILBERT LAYER (Square/TwTermPowBand.lean) — the weight-swap connecting the wide-band
-- powBandGen window integral to the mellinHat tail term twTerm (which carries the integer-window
-- powWinTest). riemannIntegralI_congr_unit_mod is a REUSABLE different-L window congruence (weaken
-- both certs to Lf+Lg via lip_weaken, run the same-L congr_unit, move back by certif_irrel).
-- powWinTest_eq_Rpow_on = powWinTest is tⁿ on its window (mirror of powBandGen_eq_Rpow_on).
-- twTerm_eq_window_powBandGen = the (ψ·powBandGen) window integral equals twTerm ψ n m, since both
-- weights reduce to ψ·tⁿ on [m+1,m+2]. No half-line assembly, no reschedule, no positivity, no crux.
#print axioms Square.riemannIntegralI_congr_unit_mod
#print axioms Square.powWinTest_eq_Rpow_on
#print axioms Square.twTerm_eq_window_powBandGen

-- THE PRE-HILBERT LAYER (Square/TwTermDilateWindow.lean) — the per-window twisted dilation
-- covariance, composing window_dilate_powBandGen (per-window dilation at the wide-band weight) with
-- twTerm_eq_window_powBandGen (weight-swap to powWinTest), instantiated at the dilated test:
-- ∫_{[s(m+1),s(m+2)]}(φ·powBandGen) = s^(n+1)·twTerm (dilate_s φ) n m. No half-line assembly, no
-- reschedule (the sum over windows), no positivity, no crux.
#print axioms Square.twTerm_dilate_window

-- THE PRE-HILBERT LAYER (Square/RescheduleFinite.lean) — the finite reschedule: summing the
-- per-window twisted dilation covariance twTerm_dilate_window over m<N (constant-pull
-- Rmul_RsumN_left + RsumN_congr with per-m band containment from the N-covering hyps) and
-- telescoping the s-scaled window tiling (riemannIntegralI_telescope, node c m = s(m+1)) into a
-- single cap integral: s^(n+1)·Σ_{m<N} twTerm (dilate_s φ) n m = ∫_{[s, s(N+1)]}(φ·powBandGen).
-- Band depends on N (tⁿ unbounded). No half-line limit, no boundary, no positivity, no crux.
-- (capNode, capDiff_num are private — no audit line.)
#print axioms Square.reschedule_finite

-- THE PRE-HILBERT LAYER (Square/ScaledTwistedTail.lean) — the s-scaled-window twisted tail, the
-- per-window-band analog of the mellinHat twTail (each window carries its OWN band [0,(s+1)(m+2)]
-- covering both [m+1,m+2] and [s(m+1),s(m+2)], so it is a genuine improper Rlim, not a finite
-- reschedule). scaledTwTerm_eq = twTerm_dilate_window at the concrete band (per-window bridge);
-- genSum_scaled_eq = the partial-sum proportionality (genSum_congr + genSum_Rmul_const);
-- scaledTwTail_eq_dilate = the Rlim capstone: Rlim of the scaled sums = s^(n+1)·twTail(dilate_s φ)
-- (Rlim_ofQ_mul_of_approx; hReg/hdec carried explicitly). No boundary, no compact piece, no full
-- covariance, no positivity, no crux. (scaledTwTerm is a def, sbHi/sbHi_* private — no audit line.)
#print axioms Square.scaledTwTerm_eq
#print axioms Square.genSum_scaled_eq
#print axioms Square.scaledTwTail_eq_dilate

-- THE PRE-HILBERT LAYER (Square/CompactMomentDilate.lean) — the compact [0,1]-window Mellin
-- dilation covariance: the scaled compact integral over [0,s] of φ against powBandGen_{[0,s+1]}
-- equals s^(n+1)·mellinMoment(dilate_s φ) n. The [0,1]-window companion of the tail dilation:
-- STEP A mellinWindowDilate at lo=0,w=1,band=[0,s+1] (hHom via powBandGen_dilate_on); STEP B
-- weight-swap to powTest on [0,1] (riemannIntegralI_congr_unit_mod, both = tⁿ there); STEP C the
-- riemannIntegralI_unit bridge to innerI/mellinMoment. No half-line, no boundary, no split, no
-- positivity, no crux. (band01_le, aff01_base, aff01_top private — no audit line.)
#print axioms Square.mellinMoment_dilate

-- THE PRE-HILBERT LAYER (Square/MellinHatDilateScaled.lean) — assembling the compact and tail
-- dilation halves: s^(n+1)·mellinHat(dilate_s φ) n = int_0^s(φ·powBandGen) + Rlim(scaled twisted
-- sums), by Rmul_distrib over mellinHat = mellinMoment + twTail and the committed mellinMoment_dilate
-- (compact) + scaledTwTail_eq_dilate (tail). The RHS is the improper Mellin integral of φ against
-- tⁿ over the s-uniform tiling; identifying it with mellinHat φ (integer tiling) is the later
-- split-point/tiling-independence step. No split independence, no factorization, no positivity, no
-- crux. (band01_le' private — no audit line.)
#print axioms Square.mellinHat_dilate_scaled

-- THE PRE-HILBERT LAYER (Square/MellinHatCovariance.lean) — the half-line Mellin DILATION
-- COVARIANCE capstone: s^(n+1)·mellinHat(dilate_s φ) n = mellinHat φ n, by Req_trans of the
-- committed mellinHat_dilate_scaled with the explicit tiling-independence hypothesis htile (the
-- s-uniform-tiling improper integral = the standard integer-tiling mellinHat φ). htile is a
-- GENUINE non-RH real-analysis fact (two cofinal exhaustions of [0,inf) against the common
-- integrand φ·tⁿ) carried audit-visibly in the honest-hypothesis pattern (as mellinHat carries
-- hdec, the crux carries hmatch) — NOT a smuggle, NOT RH, NO crux; discharged by a later cap-Rlim
-- / exhaustion-rung brick. No factorization, no positivity, no crux. (band01_le'' private.)
#print axioms Square.mellinHat_dilate_covariance

-- THE PRE-HILBERT LAYER (Square/MellinHatUniform1.lean) — mellinHat(φ) as the 1-uniform-tiling
-- improper Mellin integral: instantiating the committed mellinHat_dilate_scaled at s=1 and
-- collapsing the trivial scale factor (qpow 1 (n+1) ≈ 1; dilate_1 φ ≈ φ lifted through mellinMoment
-- via riemannIntegral_congr_mod and through twTail via riemannIntegralI_congr_unit_mod + genSum_congr
-- + Rlim_congr). This REDUCES the committed dilation-covariance hypothesis htile to a pure WIDTH
-- comparison (s-uniform vs 1-uniform); it does NOT discharge the width comparison. No factorization,
-- no positivity, no crux. (band01_le1, qpow_one_Qeq, ofQ_qpow_one, the *_dilate1_congr helpers are
-- private — no audit line.)
#print axioms Square.mellinHat_eq_uniform1

-- THE PRE-HILBERT LAYER (Square/UniformPartialCap.lean) — the s-uniform-tiling PARTIAL SUM as a
-- single cap integral: the compact [0,s] moment + the finite genSum(scaledTwTerm φ s) up to N equals
-- one interval integral over the scaled cap [0, s(N+1)]. Route: genSum_scaled_eq + reschedule_finite
-- (covering band [0,(s+1)(N+2)]) for the tail, reconciled to the cap band by riemannIntegralI_congr_
-- unit_mod (both uⁿ on the shared window) + riemannIntegralI_congr_Q; then riemannIntegralI_split_at
-- joins [0,s]+[s,s(N+1)]=[0,s(N+1)]. First step of the WIDTH COMPARISON discharging htile; builds NO
-- Cauchy-at-infinity, NO schedule comparison, no positivity, no crux. (all helpers private.)
#print axioms Square.uniform_partial_eq_cap

-- THE PRE-HILBERT LAYER (Square/PartialCommonRefine.lean) — the common-refinement identity: for a
-- rational scale s=<p,q> (p=s.num>0, q=s.den), the s-uniform partial sum equals the (1/q)-uniform
-- partial sum at the shifted index p(N+1)-1, because both collapse (uniform_partial_eq_cap at each
-- scale) to the SAME cap integral over [0, s(N+1)] (cap values s(N+1)=(1/q)·p(N+1) Qeq via ring_uor
-- + (p:Int)=s.num; reconciled by riemannIntegralI_congr_unit_mod (both uⁿ) + riemannIntegralI_congr_Q).
-- The step that lets rung 4b compare the two tilings' widths as fast cofinal schedules of the SAME
-- genSum(scaledTwTerm φ (1/q)). No Rlim, no rung-4b application, no width-comparison completion, no
-- positivity, no crux. (all helpers private.)
#print axioms Square.partial_s_eq_partial_refine

-- THE PRE-HILBERT LAYER (Square/PartialCoarseRefine.lean) — the GENERAL common-refinement: for a
-- fine scale and a positive integer k, the (fine·k)-uniform partial sum equals the fine-uniform
-- partial sum at the shifted index k(N+1)-1, because both collapse (uniform_partial_eq_cap at each
-- scale) to the SAME cap integral over [0, (fine·k)(N+1)] (cap value Qeq: coarse.num=fine.num·k,
-- coarse.den=fine.den; (k(N+1)-1)+1=k(N+1) needs k>0; reconciled by congr_unit_mod + congr_Q).
-- Generalizes partial_s_eq_partial_refine to cover BOTH the s-side (k=p) and the 1-side (k=q) of the
-- width comparison. No Rlim, no rung-4b application, no width-comparison completion, no positivity,
-- no crux. (all helpers private, file-scoped.)
#print axioms Square.partial_coarse_refine

-- THE PRE-HILBERT LAYER (Square/HtileDischarge.lean) — DISCHARGING the tiling-independence
-- hypothesis htile of the committed mellinHat_dilate_covariance, making the half-line Mellin
-- dilation covariance s^(n+1)·mellinHat(dilate_s φ) = mellinHat φ UNCONDITIONAL. scaledTwTerm_bound:
-- the two-sided Ks/((m+1)m) decay of scaledTwTerm (Ks=s^(n+1)·C·2ⁿ), scaling the committed
-- twTerm_bound through scaledTwTerm_eq. scaledTwTerm_schedule_eq: rung-4b schedule-independence for
-- the scaled summand (genSum_close + Rlim_approx_eq, general in T, with the decay bound). htile_holds:
-- the tiling-independence Req PROVED (NON-CIRCULAR — hyps are decay/regularity data, NOT htile) —
-- both s-uniform and 1-uniform improper integrals refine (partial_coarse_refine) to the common
-- 1/q-tiling where the two Rlims coincide. mellinHat_dilate_covariance_uncond: the covariance with
-- htile discharged. htile is a NON-RH real-analysis fact; discharging it introduces NO factorization,
-- NO positivity, NO ArchDominatesPrime, NO crux (step 4 positivity = RH stays the honest wall). (18
-- private helpers — no audit line.)
#print axioms Square.scaledTwTerm_bound
#print axioms Square.scaledTwTerm_schedule_eq
#print axioms Square.htile_holds
#print axioms Square.mellinHat_dilate_covariance_uncond

-- THE PRE-HILBERT LAYER (Square/GeneralWindowDilate.lean) — the GENERAL-WINDOW rational-scale Mellin
-- dilation covariance: for an ARBITRARY rational window [lo,lo+w], int_{[s·lo, s·(lo+w)]}(f·powBandGen)
-- = s^(n+1)·int_{[lo,lo+w]}(dilate_s f·powBandGen), via mellinWindowDilate + powBandGen_dilate_on with
-- the general-window affineMap membership (band [bandLo,bandHi] covers the window hc1/hc2 and its
-- s-scaling hc3/hc4). Generalizes window_dilate_powBandGen (fixed [m+1,m+2]) to the window dilMellinF
-- integrates over — the rational base of the real-scale factorization gate (rung 6). No real-scale
-- extension, no factorization, no half-line, no positivity, no crux.
#print axioms Square.general_window_dilate

-- THE PRE-HILBERT LAYER (Square/MellinMomentScaleLip.lean) — the compact Mellin moment is LIPSCHITZ IN
-- THE REAL DILATION SCALE: |mellinMoment(dilateTestR c φ) n − mellinMoment(dilateTestR c' φ) n| ≤
-- φ.L·|c−c'|. dilateTestR c φ and dilateTestR c' φ share L=φ.L·S and M=φ.M (both scale-independent),
-- so the two moment integrands sit at ONE common modulus l2L(dilateTestR c φ)(powTest n); the pointwise
-- difference |φ(c·x)−φ(c'·x)|·|clamp01(x)ⁿ| ≤ φ.L·|c−c'|·|x|·1 is ≤ φ.L·|c−c'| on the unit window
-- (|x|≤1, powTest_abs_le_one gives |clamp01(x)ⁿ|≤1), delivered by a [0,1]-window distance estimate
-- (riemannIntegral_dist_le_unit, private — the w=1 analog of riemannIntegralI_dist_le_window). The
-- continuity engine of the rung-6 rational→real scale extension of the half-line dilation covariance.
-- No tail continuity, no half-line real-scale covariance, no factorization, no positivity, no crux.
#print axioms Square.powTest_abs_le_one
#print axioms Square.mellinMoment_scale_lipschitz

-- THE PRE-HILBERT LAYER (Square/WindowMomentScaleLip.lean) — GENERAL-WINDOW scale-Lipschitz: the window
-- integral c ↦ ∫_{[lo,lo+w]} φ(c·x)·ψ(x) (real scale c INSIDE φ, weight test ψ, rational window, lo≥0) is
-- Lipschitz in c with constant w·φ.L·(lo+w)·ψ.M. Generalizes mellinMoment_scale_lipschitz off [0,1]; the
-- reusable per-window continuity primitive feeding (i) the twisted-tail terms twTerm(dilate_c φ) n m
-- (ψ=powWinTest, window [m+1,m+2]) and (ii) dilMellinF (window [xlo,xw]). Same shared-modulus algebra
-- (dilateTestR c/c' share L=φ.L·S, M=φ.M) + affine point p=lo+w·x has 0≤p≤lo+w so |φ(cp)−φ(c'p)|·|ψ(p)|
-- ≤ φ.L·|c−c'|·(lo+w)·ψ.M, via riemannIntegralI_dist_le_window (×w width). No tail continuity (needs
-- uniform-in-scale decay across windows, unbuilt), no half-line covariance, no factorization, no crux.
#print axioms Square.window_moment_scale_lipschitz

-- THE PRE-HILBERT LAYER (Square/TwTermScaleLip.lean) — the twisted-tail term is LIPSCHITZ IN THE REAL
-- SCALE: |twTerm(dilateTestR c φ) n m − twTerm(dilateTestR c' φ) n m| ≤ φ.L·(m+2)·(powWinTest m n).M·|c−c'|.
-- A direct instance of window_moment_scale_lipschitz at ψ=powWinTest m n, integer window [m+1,m+2]
-- (lo=m+1, w=1), constant simplified (w=1 drops, (m+1)+1=m+2 via ofQ_congr Qeq). The atomic per-window
-- continuity of the twisted tail; whole-tail continuity needs a UNIFORM-in-scale decay across the ∞
-- windows (per-window const GROWS with m, NOT summable) — unbuilt wall. No half-line covariance, no
-- factorization, no positivity, no crux.
#print axioms Square.twTerm_scale_lipschitz

-- THE PRE-HILBERT LAYER (Square/TailPartialScaleLip.lean) — the twisted-tail FINITE PARTIAL SUM is
-- LIPSCHITZ IN THE REAL SCALE: |genSum(twTerm(dilateTestR c φ) n) N − genSum(twTerm(dilateTestR c' φ) n) N|
-- ≤ (Σ_{m<N} φ.L·(m+2)·(powWinTest m n).M)·|c−c'|. Composes twTerm_scale_lipschitz across the sum:
-- genSum_Rsub (diff of sums = sum of diffs) + genSum_Rabs_le (finite triangle, private, = RsumN_Rabs_le
-- for genSum) + genSum_le_genSum (per-window bound) + genSum_Rmul_const_right (pull |c−c'| out). THE WALL:
-- per-window const GROWS with m ⇒ partial-sum const grows with N ⇒ NOT convergent ⇒ whole tail is NOT
-- Lipschitz; whole-tail CONTINUITY needs a uniform-in-scale decay remainder bound (unbuilt). No half-line
-- covariance, no factorization, no positivity, no crux.
#print axioms Square.genSum_twTerm_scale_lipschitz

-- THE PRE-HILBERT LAYER (Square/DilateTestBridge.lean) — the RATIONAL↔REAL DILATION BRIDGE for the Mellin
-- transform: at a rational scale q, dilateTest q φ and dilateTestR (ofQ q) φ have LITERALLY IDENTICAL .f
-- (both φ.f(Rmul (ofQ q) x)), differing only in the Lipschitz-modulus field (φ.L·q vs φ.L·S), so the
-- certified Mellin objects (certificate-independent) agree: mellinMoment_bridge (one
-- riemannIntegral_certif_irrel on the common defeq integrand), twTail_bridge (Rlim_congr + genSum_congr
-- over per-window twTerm_bridge=riemannIntegralI_certif_irrel; decay hyp transfers verbatim via defeq .f),
-- mellinHat_bridge (Radd_congr of the two halves). Connects the dilateTest-form rational-scale covariance
-- (mellinHat_dilate_covariance_uncond) to the dilateTestR-form continuity foundation for the real-scale
-- capstone. A representation bridge only: no real-scale covariance, no continuity, no factorization, no crux.
#print axioms Square.mellinMoment_bridge
#print axioms Square.twTail_bridge
#print axioms Square.mellinHat_bridge

-- THE PRE-HILBERT LAYER (Square/TwTailScaleCont.lean) — the twisted tail is SCALE-CONTINUOUS (split-at-depth):
-- |twTail(dilateTestR c φ) n − twTail(dilateTestR c' φ) n| ≤ (Σ_{m<N_j} φ.L·(m+2)·(powWinTest m n).M)·|c−c'|
-- + 4/(j+1), N_j = digammaMidx(C·2ⁿ) j, for EVERY depth j. Three-term triangle through the two j-th partial
-- sums: each twTail is within 2/(j+1) of its own partial sum by the UNIFORM Bishop-limit rate
-- (Rabs_dist_Rlim, scale-independent), middle = genSum_twTerm_scale_lipschitz (finite head). NO uniform-in-
-- scale decay hypothesis needed — the tail beyond depth j is controlled by the limit rate, not by summing
-- the growing per-window constants. As j→∞, c'→c the bound →0 = whole-tail continuity. No compact+tail
-- assembly (=mellinHat), no covariance, no factorization, no positivity, no crux.
#print axioms Square.twTail_scale_split

-- THE PRE-HILBERT LAYER (Square/MellinHatScaleCont.lean) — the MELLIN TRANSFORM is SCALE-CONTINUOUS
-- (split-at-depth): |mellinHat(dilateTestR c φ) n − mellinHat(dilateTestR c' φ) n| ≤
-- (φ.L + Σ_{m<N_j} φ.L·(m+2)·(powWinTest m n).M)·|c−c'| + 4/(j+1), N_j = digammaMidx(C·2ⁿ) j, every j.
-- mellinHat = mellinMoment + twTail: moment φ.L-Lipschitz (mellinMoment_scale_lipschitz) + tail split
-- (twTail_scale_split); Rsub_Radd_Radd + Rabs_Radd split the sum, Rmul_distrib_right factors |c−c'|. As
-- j→∞, c'→c the bound →0 = full Mellin scale-continuity. The engine the real-scale covariance capstone
-- passes to the limit. No covariance, no factorization, no positivity, no crux.
#print axioms Square.mellinHat_scale_split

-- THE PRE-HILBERT LAYER (Square/CovarianceAtRational.lean) — the RATIONAL-scale dilation covariance in
-- dilateTestR FORM: qⁿ⁺¹·mellinHat(dilateTestR (ofQ q) φ) n = mellinHat φ n. The unconditional covariance
-- mellinHat_dilate_covariance_uncond (stated with dilateTest q) transported through the representation
-- bridge mellinHat_bridge (Rmul_congr pulls the bridge inside the scalar qⁿ⁺¹). Changes only the
-- REPRESENTATION, not the content — the shape the real-scale limit q_k→c consumes. No real-scale
-- covariance (that is the capstone), no factorization, no positivity, no crux.
#print axioms Square.covariance_at_rational_dilateTestR

-- THE PRE-HILBERT LAYER (Square/MellinHatBound.lean) — the Mellin transform has a FINITE, SCALE-INDEPENDENT
-- MAGNITUDE BOUND: |mellinHat(dilateTestR c φ) n| ≤ φ.M/(n+1) + (Σ_{m<N₀} φ.M·(powWinTest m n).M) + 2,
-- N₀=digammaMidx(C·2ⁿ) 0. Depends only on φ.M,C,n — NOT c (dilateTestR.M=φ.M). CRUDE (no decay, no
-- telescoping): moment via mellinMoment_abs_le, tail via |twTail|≤|0th partial sum|+2 (Rabs_dist_Rlim at
-- j=0) with the finite 0th sum bounded term-by-term by twTerm_crude_bound (riemannIntegralI_abs_le_window,
-- |twTerm m|≤φ.M·(powWinTest m n).M). The |M_c| bound the covariance capstone's F-continuity multiplies
-- against. No covariance, no F-continuity, no positivity, no crux.
#print axioms Square.twTerm_crude_bound
#print axioms Square.twTail_crude_bound
#print axioms Square.mellinHat_abs_le

-- THE PRE-HILBERT LAYER (Square/CovCombScaleCont.lean) — the COVARIANCE COMBINATION is SCALE-CONTINUOUS:
-- F(c) = cⁿ⁺¹·mellinHat(dilateTestR c φ) n obeys, for every depth j, |F(c)−F(c')| ≤ Sⁿ⁺¹·((φ.L+head_j)·|c−c'|
-- + 4/(j+1)) + Bφ·((n+1)·Sⁿ·|c−c'|), head_j=Σ_{m<N_j}φ.L·(m+2)·(powWinTest m n).M, Bφ=mellinHat magnitude
-- bound. →0 as j→∞, c'→c. mixed-product identity F(c)−F(c')=cⁿ⁺¹·(M_c−M_c')+(cⁿ⁺¹−c'ⁿ⁺¹)·M_c'; first term
-- ≤|cⁿ⁺¹|≤Sⁿ⁺¹ × mellinHat_scale_split, second ≤ Rpow_base_lip × mellinHat_abs_le. The last continuity
-- before the real-scale covariance (F continuous + F const on rationals ⟹ F(c)=mellinHat φ). No covariance,
-- no factorization, no positivity, no crux.
#print axioms Square.covComb_scale_split

-- THE PRE-HILBERT LAYER (Square/MellinHatDilateCovarianceReal.lean) — THE REAL-SCALE MELLIN DILATION
-- COVARIANCE (rung-6 goal): cⁿ⁺¹·mellinHat(dilateTestR c φ) n = mellinHat φ n for a REAL scale c. The
-- rational-scale covariance (covariance_at_rational_dilateTestR) holds at every rational q, and F(c)=
-- cⁿ⁺¹·mellinHat(dilateTestR c φ) is scale-continuous (covComb_scale_split); so F is continuous +
-- constant on the rationals ⟹ constant on ℝ, by the Archimedean squeeze Req_of_real_null_family.
-- hcov (rational covariance at the approximants) and hbound (the continuity gap is a null family = the
-- approximants converge fast enough) are the two explicit dischargeable analytic inputs, NEITHER RH-
-- equivalent. OBJECT-GROUNDING substrate (evaluating the inner x-integral at a real scale toward
-- grounding v=ĝ); NOT step-4 band-coupling positivity (ArchDominatesPrime), which is RH. Crux none.
#print axioms Square.mellinHat_dilate_covariance_real

-- THE PRE-HILBERT LAYER (Square/MellinHatDilateCovarianceRealDerived.lean) — the real-scale covariance
-- with hcov DERIVED (not assumed): mellinHat_dilate_covariance_real_derived discharges the
-- rational-scale covariance hcov from the primitive per-approximant decay data (hdec_qk/hdec_fine_qk/
-- hReg_qk) via the unconditional covariance_at_rational_dilateTestR + the Rpow_ofQ scalar bridge
-- (Rpow (ofQ q)(n+1) = ofQ(qpow q (n+1))). Only hbound (the fast-approximation continuity rate) remains
-- an explicit input. Object-grounding; the deferred piece is the diagonal q_k=c.seq(fast(k)) construction.
-- NO factorization, NO grounding of v=ĝ, NO step-4 positivity (RH). Crux none.
#print axioms Square.mellinHat_dilate_covariance_real_derived

-- THE PRE-HILBERT LAYER (Square/CovCombHbound.lean) — the covariance continuity gap is a NULL FAMILY:
-- covComb_hbound_of_fast discharges the last remaining hypothesis (hbound) of the real-scale dilation
-- covariance. Given a rational sequence qk approximating c fast enough (|c−qk| ≤ 1/(covIdx k + 1) —
-- FREE for qk k = c.seq(covIdx k) via Rabs_sub_seq_le), the covComb_scale_split gap is ≤ covC0/(k+1),
-- exactly the hbound shape the Archimedean squeeze consumes. Mechanism: instantiate covComb at c'=qk,
-- j=k; collapse the two genSum heads to rationals (genSum_ofQ); bound |c−qk| (hfast); drive under
-- covC0/(k+1) with the rate inequalities Qmul_recip_le/Qmul_four_le, the index covIdx k chosen from the
-- RATIONAL magnitude of the covComb coefficient. So hbound is no longer a standalone input; the covariance
-- reduces to the per-approximant decay data alone. Object-grounding; NO factorization, NO grounding of
-- v=ĝ, NO step-4 positivity (RH). Crux none.
#print axioms Square.covComb_hbound_of_fast

-- THE PRE-HILBERT LAYER (Square/MellinHatDilateCovarianceRealSeq.lean) — the real-scale covariance with
-- hbound AUTO-DISCHARGED along the fast diagonal: mellinHat_dilate_covariance_real_seq fixes the
-- approximant sequence to c.seq(covIdx k), so the fast-approximation input is free (Rabs_sub_seq_le) and
-- hbound is discharged internally by covComb_hbound_of_fast. No separate hbound hypothesis remains — the
-- covariance rests only on the per-approximant decay/positivity/regularity at the diagonal. The natural
-- capstone of the hbound-discharge arc. Object-grounding; NO factorization, NO grounding of v=ĝ, NO
-- step-4 positivity (RH). Crux none.
#print axioms Square.mellinHat_dilate_covariance_real_seq

-- THE FINE-DECAY WALL REMOVED (new Square/MellinHatDilateCovarianceRealClean.lean).
-- mellinHat_dilate_covariance_real_clean: the real-scale covariance cⁿ⁺¹·mellinHat(dilateTestR c φ)=
-- mellinHat φ along the fast diagonal c.seq(covIdx k), but DROPPING the _seq capstone's per-approximant
-- fine-1/qk.den decay hdec_fine_qk (the c≥1 covariance wall) and regularity hReg_qk — hcov now comes from
-- covariance_at_qk_baseform, which discharges both internally (fine decay from φ's clean decay hfdec via
-- dilateTest_fine_window_decay at Cbig; regularity from scaledTwTerm_bound). Rests only on hdec_c/hdec_phi
-- (window decays), hfdec (φ's clean order-(n+2) decay), and the diagonal hqk_pos/hqk_S/hdec_qk. The
-- wall-break payoff. Object-grounding; NO factorization, NO grounding of v=ĝ, NO step-4 positivity (RH).
-- Crux none.
#print axioms Square.mellinHat_dilate_covariance_real_clean

-- THE c∈[1,S] DISCHARGE (new Square/MellinHatDilateCovarianceRealGe1.lean).
-- mellinHat_dilate_covariance_real_ge1: for a REAL scale c with 1≤c≤S, cⁿ⁺¹·mellinHat(dilateTestR c φ)n=
-- mellinHat φ n, with EVERY per-approximant obligation discharged internally. Runs the base density
-- capstone along the two-sided BAND diagonal qk k=(qBandQ 1 S c).seq(covIdx k) — in [1,S] at every index
-- by construction (qBandQ_ge/le), so hqk_S (≤S), hdec_qk (scale≥1, from hfdec via
-- dilateTestR_window_hdec), and the numerator positivity covariance_at_qk_baseform needs all discharge.
-- hcov from covariance_at_qk_baseform; hbound from covComb_hbound_of_fast with hfast FREE (band inert
-- since c∈[1,S], so c'≈c gives |c−ofQ(qk k)|=|c'−ofQ(c'.seq)|≤1/(N+1) — no clamp-nonexpansiveness lemma).
-- Rests only on hdec_c/hdec_phi window decays and φ's clean decay hfdec. The scale usable directly at
-- c=clampedInv(a,t). Object-grounding; NO factorization, NO grounding of v=ĝ, NO step-4 positivity (RH).
-- Crux none.
#print axioms Square.mellinHat_dilate_covariance_real_ge1

-- THE COVARIANCE HEAD IDENTITY (new Square/CovarianceHead.lean). Rmul_head_of_covariance: the pure
-- real-power rearrangement cⁿ⁺¹·H≈M ∧ t·c≈1 ⟹ c·H≈tⁿ·M (via tⁿ·M=tⁿ·cⁿ⁺¹·H=(t·c)ⁿ·c·H=1ⁿ·c·H=c·H,
-- Rpow_mul_dist + Rpow_one_eq). The head factor g·tⁿ·M[f] of the covConnect's U=Whead−Tmom, obtained by
-- splitting twTail=mellinHat−mellinMoment and applying mellinHat_dilate_covariance_real_ge1 at
-- c=clampedInv(a,t) (t·c=1 on window). Pure Real algebra; NO mellinHat, NO factorization, NO v=ĝ
-- grounding, NO step-4 positivity (RH). Crux none.
#print axioms Square.Rmul_head_of_covariance

-- THE covCONNECT ALGEBRA (new Square/CovConnectPure.lean). covConnect_pure: with mellinHat(dilate c f)
-- abstracted as mom+tw (its def mellinMoment+twTail), the covariance cⁿ⁺¹·(mom+tw)≈M and reciprocal
-- T·c≈1 give the tail integrand as the head/moment difference g·c·tw ≈ (g·Tⁿ·M) − (g·c·mom). Built on
-- Rmul_head_of_covariance (head c·(mom+tw)=Tⁿ·M) + Rmul_distrib/Rmul_sub_distrib/Rmul_assoc. This is the
-- exact split U=Whead−Tmom the tail commute's hU consumes (Whead.f=g·Tⁿ·M[f], Tmom.f=g·c·mellinMoment).
-- Pure Real algebra; supplies NO U, NO factorization, NO v=ĝ grounding, NO step-4 positivity (RH). Crux
-- none.
#print axioms Square.covConnect_pure

-- THE COVARIANCE AT c=clampedInv(a,t) (new Square/CovarianceAtClampedInv.lean).
-- covariance_at_clampedInv: mellinHat_dilate_covariance_real_ge1 instantiated at the genuine window
-- scale c=clampedInv(a, affineMap lo w s)=1/max(t,a)≥1, all hypotheses discharged from the tail commute's
-- own data — c≥1 (window_clampedInv_ge_one), c≤1/a (recipTest.hbd), Qinv a≥1 (Qinv_antitone from a≤1),
-- hdec_c = the exact dilateTestR_window_hdec, mellinHat f at hdec_window_of_hfdec. So the Mellin term
-- matches convTwTail_eq_intTail's hU verbatim, giving clampedInvⁿ⁺¹·mellinHat(dilate clampedInv f)=
-- mellinHat f — the hcov slot of covConnect_pure. Object-grounding; NO U, NO factorization, NO v=ĝ
-- grounding, NO step-4 positivity (RH). Crux none.
#print axioms Square.covariance_at_clampedInv

-- THE covCONNECT AT THE GENUINE SCALE (new Square/CovConnectClampedInv.lean). covConnect_at_clampedInv:
-- covConnect_pure instantiated at c=clampedInv(a,t), T=qClampQ a t=max(t,a), so the tail commute's per-t
-- integrand g·clampedInv·twTail(dilate clampedInv f) EQUALS the head/moment difference
-- g·max(t,a)ⁿ·mellinHat f − g·clampedInv·mellinMoment(dilate clampedInv f). LHS is hU's target verbatim,
-- RHS is Whead−Tmom (M[f] factored out). hcov = covariance_at_clampedInv; the reciprocal T·c=1 is
-- Rmul_Rinv_self (qClampQ_witness…) since clampedInv=Rinv(qClampQ…) by def. Object-grounding; builds NO
-- Whead/Tmom objects yet, NO factorization, NO v=ĝ grounding, NO step-4 positivity (RH). Crux none.
#print axioms Square.covConnect_at_clampedInv

-- THE UNDILATED MELLIN MAGNITUDE BOUND (new Square/MellinHatIdBound.lean) — the rational modulus for the
-- constant M[f]=mellinHat f the head test Whead=g·max(t,a)ⁿ·M[f] carries (constTest needs a rational mB).
-- twTerm_id_crude_bound/twTail_id_crude_bound/mellinHat_id_abs_le mirror the dilated mellinHat_abs_le for
-- the plain f (moment ≤ φ.M/(n+1) by mellinMoment_abs_le, tail by the finite window sum +2; scale-free via
-- φ.hbd); mellinHat_id_abs_le_ofQ collapses the genSum-of-ofQ to a single ofQ (mellinHatIdBnd, genSum_ofQ +
-- Radd_ofQ_ofQ). Object-grounding magnitude bound; NO head test, NO factorization, NO v=ĝ grounding, NO
-- step-4 positivity (RH). Crux none.
#print axioms Square.twTerm_id_crude_bound
#print axioms Square.twTail_id_crude_bound
#print axioms Square.mellinHat_id_abs_le
#print axioms Square.mellinHatIdBnd_den
#print axioms Square.mellinHat_id_abs_le_ofQ

-- THE RECONSTRUCTION'S HEAD TEST Whead (new Square/HeadTest.lean) — one of the two objects the doc named
-- missing (Tmom is the existing coupOuterTestSwap). headTest f g n … = L2Test.mul (L2Test.mul g (powTest n))
-- (constTest M[f] (mellinHatIdBnd f n Cf) …), so .f t = g·clamp01(t)ⁿ·M[f] (headTest_f_eq, via powTest_f_eq);
-- M[f]=mellinHat f at hdec_window_of_hfdec, its rational modulus from mellinHat_id_abs_le_ofQ.
-- mellinHatIdBnd_num: the modulus has nonneg numerator (constTest's hMn). Object-grounding; assembles NO U
-- (=L2Test.sub Whead Tmom) yet, NO factorization, NO v=ĝ grounding, NO step-4 positivity (RH). Crux none.
#print axioms Square.mellinHatIdBnd_num
#print axioms Square.headTest_f_eq

-- THE TAIL COMMUTE DISCHARGED (new Square/ConvTwTailIntU.lean). convTwTail_eq_intU: the parametric
-- convTwTail_eq_intTail instantiated at U = L2Test.sub (headTest) (coupOuterTestSwap) = Whead − Tmom, with
-- hU PROVED — so convTwTail f g n = ∫_t (Whead − Tmom), the tail branch now hypothesis-free. hU from
-- covConnect_at_clampedInv (per-t head/moment split) + the clamps' window inertness (a≤lo makes
-- clamp01(t)=max(t,a)=t on [lo,lo+w]⊆(0,1] via qBandQ_eq_of_band/qClampQ_eq_of_ge, so Rpow(clamp01 t)n≈
-- Rpow(qClampQ a t)n) + headTest_f_eq + mom_ptw (Tmom.f≈momIntegrand). Object-grounding; does NOT yet
-- compose the moment side into the factorization, NO factorization M[f⋆g]=M[f]·M[g], NO v=ĝ grounding, NO
-- step-4 positivity (RH). Crux none.
#print axioms Square.convTwTail_eq_intU

-- THE Tmom-CANCELLATION READOFF: convMellinHat = ∫_t Whead (new Square/ConvMellinHatIntWhead.lean).
-- convMellinHat_eq_intWhead: by def convMellinHat = mellinMoment(mulConv) + convTwTail; the moment side is
-- ∫_t Tmom (riemannIntegralI_unit + mellinConv_fubini, at Tmom's STANDARD certs — stopping before
-- mellinMoment_mulConv_dilated's mom_ptw rewrite so it's syntactically the tail-side integral) and the tail
-- side is ∫_t (Whead − Tmom) (convTwTail_eq_intU), so the Tmom integrals cancel (riemannIntegralI_addTest +
-- negTest) leaving ∫_t Whead. Since Whead.f t=g·max(t,a)ⁿ·M[f], ∫Whead=M[f]·∫(g·tⁿ) — the convolution
-- theorem M[f⋆g]=M[f]·(compact moment of g) on the window (a≤lo), one scalar pullout away. Object-grounding;
-- does NOT yet pull M[f] out of ∫Whead, NO closed factorization, NO v=ĝ grounding, NO step-4 positivity (RH).
-- Crux none.
#print axioms Square.convMellinHat_eq_intWhead

-- THE RIGHT-CONSTANT SCALAR PULLOUT (new Square/ConstMulRight.lean). riemannIntegralI_mulConstTest_right:
-- ∫_t(ψ(t)·c)=c·∫_t ψ(t) — the mirror of riemannIntegralI_constTestMul for the constant on the RIGHT
-- (Whead's outer factor). Reconciles the product modulus to a common Lc (certif_irrel), commutes ψ·c→c·ψ
-- (riemannIntegralI_congr via Rmul_comm), pulls c out (riemannIntegralI_Rsmul), realigns. Object-grounding
-- scalar linearity; no factorization, no v=ĝ grounding, no step-4 positivity (RH). Crux none.
#print axioms Square.riemannIntegralI_mulConstTest_right

-- THE ON-WINDOW CONVOLUTION FACTORIZATION (new Square/ConvMellinHatFactor.lean). convMellinHat_eq_MfMoment:
-- convMellinHat f g n = M[f]·∫_t(g·tⁿ), M[f]=mellinHat f — the readoff M[f⋆g]=M[f]·M[g] on the window
-- (a≤lo), with M[g] the compact ∫_t g·tⁿ. Composes convMellinHat_eq_intWhead (=∫Whead) with
-- riemannIntegralI_mulConstTest_right (M[f], Whead's outer constTest, pulls out). Wall 3 of the transform
-- bridge COMPLETE: grounds v=ĝ at the value level — at prime powers this turns mulConv into
-- weilPrimeGram(vFrom g), the genuine autocorrelation prime side. Does NOT assemble the coupled kernel,
-- NO step-4 band-coupling positivity (ArchDominatesPrime), which is RH. Crux none.
#print axioms Square.convMellinHat_eq_MfMoment

-- THE REFLECTION COVARIANCE IN LOG-COORDINATES (new Square/LogReflect.lean). logPull_reflect_neg:
-- logPull (reflectTest a φ) u ≈ logPull φ (−u) on the inert window (exp u ≥ a) — the multiplicative
-- inversion x↦1/x of reflectTest is the additive negation u↦−u under logPull (sibling of
-- logPull_dilate_shift). The log-coordinate keystone of M[g^τ](s)=M[g](−s), the self-dual arm of the
-- autocorrelation recovery. Proof: clamp drops on the window (clampedInv_eq_of_ge), 1/exp u = exp(−u)
-- by inverse-uniqueness (exp(−u)·exp u=exp 0=1), φ.hfc lifts. NOT the reflected Mellin moment (needs the
-- log-integral rep on top), NOT the autocorrelation identification, NO step-4 positivity (RH). Crux none.
#print axioms Square.logPull_reflect_neg

-- THE REFLECTION GENERATOR'S DILATION LAW (Square/LogReflect.lean). logPull_reflect_dilate:
-- logPull (reflectTest a (dilateTest n φ)) u ≈ logPull φ (log n − u) — reflecting a dilated test is
-- negation + the dilation shift; the honest analog of logPull_dilate_shift_comp for the reflect∘dilate
-- generator, completing MultShift's log-coordinate group laws. Composes logPull_reflect_neg with
-- logPull_dilate_shift at −u. Substrate; NOT the reflected moment, NO step-4 positivity (RH). Crux none.
#print axioms Square.logPull_reflect_dilate

-- THE REFLECTION INVOLUTION (Square/LogReflect.lean). logPull_reflect_involutive: reflectTest applied
-- twice returns the original on the reciprocal-symmetric window a ≤ exp u ≤ 1/a —
-- logPull (reflectTest a (reflectTest a φ)) u ≈ logPull φ u — the order-2 group law (u↦−u↦u) completing
-- the reflection generator's log-coordinate laws (logPull_reflect_neg twice + Rneg_neg). The structural
-- reason g^τ is self-inverse. Substrate; NOT the reflected moment, NO step-4 positivity (RH). Crux none.
#print axioms Square.logPull_reflect_involutive

-- THE SELF-DUAL (MELLIN-EVEN) TEST CLASS (new Square/SelfDualTest.lean). logPull_selfDualTest_self_dual:
-- selfDualTest a φ := φ + reflectTest a φ is invariant under reflectTest on the reciprocal-symmetric
-- window (logPull (reflectTest a (selfDualTest a φ)) u ≈ logPull (selfDualTest a φ) u) — the
-- Connes-Consani test class the autocorrelation self-dual arm needs, the payoff of the reflection
-- involution. reflectTest+logPull distribute over L2Test.add definitionally; involution collapses the
-- reflect²φ summand; Radd_comm reorders. NOT the reflected Mellin MOMENT identity (needs innerI
-- congruence + [0,a) boundary handling), NOT the autocorrelation identification, NO step-4 positivity
-- (RH). Crux none.
#print axioms Square.logPull_selfDualTest_self_dual

-- CONVOLUTION SECOND-ARGUMENT WINDOW-CONGRUENCE (new Square/MulConvCongr.lean). mulConv_congr_right:
-- if g ≈ g' on the integration window [lo,lo+w], then mulConv f g x ≈ mulConv f g' x — g enters only
-- through the integrand's window values. One riemannIntegralI_congr_unit_mod (window-only, different
-- moduli); integrands (f(x/t)·g(t))·(1/max(t,a)) agree from the middle factor (Rmul_congr twice). The
-- reusable tool turning self-duality (reflectTest g ≈ g on window) into autocorr(g)=g⋆g WITHOUT a change
-- of variables. NOT the reflected moment, NOT the autocorrelation identification, NO step-4 positivity
-- (RH). Crux none.
#print axioms Square.mulConv_congr_right

-- THE VALUE-LEVEL REFLECTION INVOLUTION (new Square/ValueInvolution.lean). clampedInv_involutive:
-- clampedInv a (clampedInv a t) ≈ t on the reciprocal-symmetric window a ≤ t ≤ 1/a (t witness) — both
-- clamps inert (clampedInv a t ≈ 1/t via clampedInv_eq_of_ge; 1/t ≥ a via ofQ_inv_le_Rinv +
-- Qinv(Qinv a)=a), outer clamp inert too, Rinv involution 1/(1/t)=t. The value-level (pointwise-in-t)
-- form the convolution consumes. Rests on private Qinv_Qinv + Rinv_involutive. NOT the self-duality yet,
-- NO step-4 positivity (RH). Crux none.
#print axioms Square.clampedInv_involutive

-- POINTWISE SELF-DUALITY OF THE MELLIN-EVEN CLASS (new Square/SelfDualPointwise.lean).
-- reflectTest_involutive_pointwise: (reflectTest a (reflectTest a φ)).f t ≈ φ.f t on a≤t≤1/a (φ.hfc
-- through clampedInv_involutive). selfDualTest_self_dual_pointwise: (reflectTest a (selfDualTest a φ)).f
-- t ≈ (selfDualTest a φ).f t on the window — reflectTest & .f distribute over L2Test.add, pointwise
-- involution collapses the reflect²φ summand, Radd_comm reorders (value-level twin of
-- logPull_selfDualTest_self_dual). The version mulConv_congr_right consumes (agreement AT the integration
-- points t). NOT the autocorrelation identity yet, NO step-4 positivity (RH). Crux none.
#print axioms Square.reflectTest_involutive_pointwise
#print axioms Square.selfDualTest_self_dual_pointwise

-- MILESTONE A: AUTOCORRELATION OF A MELLIN-EVEN TEST = ITS SELF-CONVOLUTION (new
-- Square/SelfDualAutocorr.lean). autocorr_selfDual_eq_conv: autocorr (selfDualTest a φ) x ≈
-- mulConv (selfDualTest a φ) (selfDualTest a φ) x on [lo,lo+w]⊆[a,1/a] (a≤lo, lo+w≤1/a). autocorr g =
-- g⋆g^τ and g^τ ≈ g on the window (selfDualTest_self_dual_pointwise fed to mulConv_congr_right over the
-- affineMap window points a≤t≤1/a), so the reflected factor collapses to g — REACHED BY CONGRUENCE, no
-- nonlinear change-of-variables. This is the object identity M's factorization will act on to reach
-- weilPrimeGram(vHat g) for the Connes-Consani class. NOT the transform identification (milestone B), NOT
-- the full autocorrelation identification, NO step-4 positivity (ArchDominatesPrime), which is RH. Crux none.
#print axioms Square.autocorr_selfDual_eq_conv

-- MILESTONE B, BRICK 1: WINDOW-MOMENT REFLECTION SYMMETRY OF THE SELF-DUAL CLASS (new
-- Square/WindowMomentReflect.lean, workflow-built). windowMoment_reflect_selfDual:
-- ∫_[lo,lo+w] (reflectTest a (selfDualTest a φ))·tᵐ ≈ ∫_[lo,lo+w] (selfDualTest a φ)·tᵐ on
-- [lo,lo+w]⊆[a,1/a] — the moment-integral twin of Milestone A's autocorr_selfDual_eq_conv. One
-- riemannIntegralI_congr_unit_mod (different moduli; reflectTest carries (1/a)²) fed by
-- selfDualTest_self_dual_pointwise over the affineMap window points a≤t≤1/a. NO change of variables, NO
-- case-split. Composed with the [a,1]-support collapse it gives M[reflectTest g]=M[g] (bricks 2-3). The
-- SYMMETRIC transform Gram identification stays blocked by the f-side window wall (mellinHat≠mellinMoment
-- for straddling support). NO step-4 positivity (RH). Crux none.
#print axioms Square.windowMoment_reflect_selfDual

-- MILESTONE B, BRICKS 2a/2/3 — THE REFLECTION MOMENT SYMMETRY M[reflectTest g]=M[g] (new
-- Square/SelfDualMomentSymmetry.lean, workflow-built, congruence route). selfDual_vanish_below_floor:
-- below the floor x≤a, both selfDualTest a φ and reflectTest a (selfDualTest a φ) vanish (φ vanishing at
-- floor+ceiling; clamp sends x→1/a and double-clamp→≤a). windowMoment_eq_mellinMoment: for h vanishing on
-- [0,a], ∫_[a,1] h·tᵐ ≈ mellinMoment h m (split [0,1]=[0,a]∪[a,1] via riemannIntegralI_split_at, [0,a]
-- piece=0, riemannIntegralI_unit). mellinMoment_reflect_selfDual (SUB-GOAL 1): M[reflectTest a g](m) ≈
-- M[g](m) for g=selfDualTest a φ, φ supported in (a,1/a) — chains the [a,1] collapse (both sides) around
-- windowMoment_reflect_selfDual (brick 1). NO change of variables. NOT the convolution factorization, NOT
-- the symmetric transform Gram (f-side window wall), NO step-4 positivity (RH). Crux none.
#print axioms Square.selfDual_vanish_below_floor
#print axioms Square.windowMoment_eq_mellinMoment
#print axioms Square.mellinMoment_reflect_selfDual

-- MILESTONE B, BRICK 4: THE HONEST ASYMMETRIC AUTOCORRELATION FACTORIZATION (new
-- Square/ConvAutocorrFactor.lean). convAutocorr_factor_selfDual: for self-dual g_i,g_j (φ_j vanishing
-- outside (a,1/a)) on window [a,1], convMellinHat g_i (reflectTest a g_j) m ≈ mellinHat(g_i)(m)·
-- mellinMoment(g_j)(m) — i.e. M[g_i⋆g_j^τ](m)=mellinHat(g_i)·mellinMoment(g_j). Composes
-- convMellinHat_eq_MfMoment (factors into mellinHat(g_i)·∫_[a,1](reflectTest g_j)·tᵐ) + brick 1
-- windowMoment_reflect_selfDual (drops reflection) + brick 2 windowMoment_eq_mellinMoment (fed brick 2a
-- vanishing, collapses to mellinMoment g_j). ASYMMETRIC (f-side mellinHat, g-side mellinMoment): this
-- makes THE WINDOW WALL kernel-explicit — the symmetric Gram identification needs mellinHat(g_i)=
-- mellinMoment(g_i), FALSE for support straddling x=1, NOT crossed here. NOT the point-value Weil prime
-- side (different functional). NO step-4 positivity (RH). Crux none.
#print axioms Square.convAutocorr_factor_selfDual

-- THE PRE-HILBERT LAYER, brick 20 (Square/MellinHat.lean) — THE MELLIN TRANSFORM AT INTEGER
-- POINTS: the exponent-generic collapse, the twisted gateway data, and mellinHat = moment +
-- convergent twisted tail — the first constructed value of the f ↦ f̂ direction.
#print axioms Square.qmul_le_left_mono
#print axioms Square.twTerm_bound
#print axioms Square.hdec_of_supp
#print axioms Square.mellinHat_compact

-- THE PRE-HILBERT LAYER, brick 20 (Square/MellinHat.lean) — THE MELLIN TRANSFORM AT INTEGER
-- POINTS: the exponent-generic twisted collapse, the twisted gateway data, the convergent
-- twisted tail, and mellinHat φ n = moment + tail — the first constructed f̂ value.
#print axioms Square.qmul_le_left_mono
#print axioms Square.twTerm_bound

-- THE PRE-HILBERT LAYER, brick 21 (Square/MellinLinear.lean) — THE TRANSFORM IS LINEAR:
-- interval-integral certificate independence and congruence, additivity of the twisted window
-- integrals and tails (shared decay constant/schedule), and mellinHat_add — transform-side
-- vanishing conditions now cut out subspaces. Plus Qle_self_add_l made public (brick 7).
#print axioms Analysis.Qle_self_add_l
#print axioms Square.riemannIntegralI_certif_irrel
#print axioms Square.twTerm_add
#print axioms Square.twTail_add
#print axioms Square.mellinHat_add

-- THE PRE-HILBERT LAYER, brick 22 (Square/HatVanishes.lean) — THE CO-SUPPORT PREDICATE:
-- bundled all-order window decay (weakening + addition), HatVanishes with its downward
-- filtration and SUBSPACE closure (mellinHat_add against 0+0≈0), the compact/moment bridge,
-- and nonvacuity via the constructed zero test with all moments evaluated to 0.
#print axioms Square.windowDecay_weaken
#print axioms Square.allDecay_weaken
#print axioms Square.windowDecay_add
#print axioms Square.allDecay_add
#print axioms Square.allDecay_of_supp
#print axioms Square.hatVanishes_mono
#print axioms Square.hatVanishes_add
#print axioms Square.hatVanishes_of_moments
#print axioms Square.zeroL2_supp
#print axioms Square.mellinMoment_zeroL2
#print axioms Square.hatVanishes_zeroL2

-- THE PRE-HILBERT LAYER, brick 23 (Square/MomentValue.lean + Analysis/IntegralLocal.lean) —
-- THE MOMENT MAP TAKES CERTIFIED NONZERO VALUES: the unit-local congruence (antisymmetry of
-- riemannIntegral_le_unit), the clamp's domain-local inertness, and the exact evaluations
-- mellinMoment oneTest 0 ≈ 1 and mellinMoment clampTest 0 ≈ 1/2 — the moment functionals
-- provably separate tests.
#print axioms Analysis.riemannIntegral_congr_unit

-- The linear change of variables for the interval integral (new Analysis/DilateIntegral.lean).
#print axioms Analysis.dilate_fc
#print axioms Analysis.dilate_lip
#print axioms Analysis.riemannIntegralI_dilate

-- Window-congruence for the interval integral (new Analysis/IntervalCert.lean).
#print axioms Analysis.riemannIntegralI_congr_unit

-- Haar invariance of the multiplicative-measure integral (new Square/HaarInvariant.lean).
#print axioms Square.haarIntegral_dilate

-- The multiplicative convolution, constructed (new Square/MulConv.lean).
#print axioms Square.mulConv_nonneg

-- The autocorrelation g * g^tau, constructed (new Square/Autocorr.lean).
#print axioms Square.autocorr_nonneg

#print axioms Square.clamp01_inert
#print axioms Square.mellinMoment_one_zero
#print axioms Square.mellinMoment_clamp_zero

-- THE PRE-HILBERT LAYER, brick 24 (Square/MomentSquare.lean) — THE FIRST QUADRATIC
-- EVALUATION OF THE GATEWAY: the square fold, the clamped-square Riemann sums and telescoped
-- dyadic evaluation with its rational defect, ∫₀¹ clamp01² ≈ 1/3 general in the Lipschitz
-- datum, and the clamp's second Mellin datum mellinMoment clampTest 1 ≈ 1/3.
#print axioms Square.sumSquaresQ
#print axioms Square.riemannSum_clampSq
#print axioms Square.genSum_clampSq_eval
#print axioms Square.sq_defect_le
#print axioms Square.genSum_clampSq_rate
#print axioms Square.riemannIntegral_clampSq_gen
#print axioms Square.mellinMoment_clamp_one

-- THE PRE-HILBERT LAYER, brick 25 (Square/CoSupportMember.lean) — THE FIRST NONZERO TRANSFORM
-- VALUE: the band clamp's saturation side, the [0,1]-supported unit bump x(1−x) with
-- mellinMoment 1/6, the transform value f̂(0) ≈ 1/6 with Pos, and the properness of the
-- co-support subspace (bumpU is not in HatVanishes · 1).
#print axioms Square.qCapQ_eq_of_ge
#print axioms Square.clamp01_sat
#print axioms Square.affine_window_ge_one
#print axioms Square.bumpU_supp
#print axioms Square.mellinMoment_bumpU
#print axioms Square.mellinHat_bumpU_value
#print axioms Square.mellinHat_bumpU_pos
#print axioms Square.bumpU_not_hatVanishes

-- THE PRE-HILBERT LAYER, brick 26 (Square/MomentCube.lean) — THE CUBIC EVALUATION: the
-- Nicomachus fold, the clamped-cube Riemann sums and telescoped evaluation with rational
-- defect, ∫₀¹ clamp01³ ≈ 1/4 general in the Lipschitz datum, and the clamp's third Mellin
-- datum mellinMoment clampTest 2 ≈ 1/4.
#print axioms Square.sumCubesQ
#print axioms Square.riemannSum_clampCube
#print axioms Square.genSum_clampCube_eval
#print axioms Square.cube_defect_le
#print axioms Square.genSum_clampCube_rate
#print axioms Square.riemannIntegral_clampCube_gen
#print axioms Square.mellinMoment_clamp_two

-- THE PRE-HILBERT LAYER, brick 27 (Square/CubicMember.lean) — THE NONZERO CO-SUPPORT SUBSPACE
-- MEMBER: the cubic bump x(1−x)(1−2x) is [0,1]-supported, its zeroth moment vanishes exactly
-- (the three engine values cancel at one shared modulus), it is IN HatVanishes · 1, and it is
-- apart from zero at x = 1/4 (value 3/32, Pos).
#print axioms Square.cubeBump_supp
#print axioms Square.mellinMoment_cubeBump
#print axioms Square.cubeBump_hatVanishes
#print axioms Square.cubeBump_value_quarter
#print axioms Square.cubeBump_apart

-- THE PRE-HILBERT LAYER, brick 28 (Square/CoSupportWeld.lean) — THE WELD: the f,f̂ pair
-- object (MellinPair), the compact pair's hat = the L² pairing against monomials, the
-- EQUIVALENCE HatVanishes ⟺ orthogonality to the monomial band, span-extension by
-- bilinearity, and the realized nonzero instance (the cubic bump pair).
#print axioms Square.mellinPair_hat_compact
#print axioms Square.hatVanishes_iff_orthogonal
#print axioms Square.orthogonal_band_add
#print axioms Square.cubePair_orthogonal

-- THE PRE-HILBERT LAYER, brick 29 (Square/BandBridge.lean) — THE BAND BRIDGE: the moment map
-- relates the monomial band to the skeleton's indicator band (momSeq_fourier), pushes the
-- co-support condition to the skeleton's band condition, fixes the moment sequence under
-- bandProj, and fires the skeleton's unconditional complement-positivity on genuine f,f̂
-- data (weil_psd_on_cosupport) with its zero-member instance.
#print axioms Square.momSeq_fourier
#print axioms Square.momSeq_band_vanishes
#print axioms Square.momSeq_bandProj_fixed
#print axioms Square.weil_psd_on_cosupport
#print axioms Square.weil_psd_cosupport_instance

-- THE PRE-HILBERT LAYER, brick 30 (Square/MomentQuartic.lean) — THE QUARTIC EVALUATION: the
-- Faulhaber fold, the clamped-quartic Riemann sums and telescoped evaluation (the N⁴ terms
-- cancel in the defect), ∫₀¹ clamp01⁴ ≈ 1/5 general in the Lipschitz datum, and the clamp's
-- fourth Mellin datum mellinMoment clampTest 3 ≈ 1/5.
#print axioms Square.sumQuarticsQ
#print axioms Square.riemannSum_clampQuad
#print axioms Square.genSum_clampQuad_eval
#print axioms Square.quad_defect_le
#print axioms Square.genSum_clampQuad_rate
#print axioms Square.riemannIntegral_clampQuad_gen
#print axioms Square.mellinMoment_clamp_three

-- THE PRE-HILBERT LAYER, brick 31 (Square/MomentQuintic.lean) — THE QUINTIC EVALUATION: the
-- quintic fold Σi⁵ = k²(k−1)²(2k²−2k−1)/12, the clamped-quintic Riemann sums and telescoped
-- evaluation (N⁴ cancels; numerator −(36N³+78N²+48N+12) ≤ 72(N+1)³), ∫₀¹ clamp01⁵ ≈ 1/6
-- general in the Lipschitz datum, and mellinMoment clampTest 4 ≈ 1/6.
#print axioms Square.sumQuinticsQ
#print axioms Square.riemannSum_clampQuint
#print axioms Square.genSum_clampQuint_eval
#print axioms Square.quint_defect_le
#print axioms Square.genSum_clampQuint_rate
#print axioms Square.riemannIntegral_clampQuint_gen
#print axioms Square.mellinMoment_clamp_four

-- THE PRE-HILBERT LAYER, brick 32 (Square/DeepMember.lean) — THE NONZERO K=2 CO-SUPPORT
-- MEMBER: deepBump = x(1−x)(1−5x+5x²) in expanded linear form; both moments vanish by
-- bilinearity against the engine values; unit support from p(1)=0; apartness at 1/10
-- (99/2000); HatVanishes at K=2; and the capstone weil_psd_nonzero_instance — the
-- skeleton's unconditional positivity on genuinely nonzero f,f̂ data.
#print axioms Square.deepBump_moment_zero
#print axioms Square.deepBump_moment_one
#print axioms Square.deepBump_supp
#print axioms Square.deepBump_value_tenth
#print axioms Square.deepBump_apart
#print axioms Square.deepBump_hatVanishes
#print axioms Square.weil_psd_nonzero_instance

-- THE PRE-HILBERT LAYER, brick 33 (Square/MomentLaw.lean) — THE HAUSDORFF MOMENT LAW: the
-- discrete mean-value bracket (pow_succ_lower/upper), the telescoped power-sum bounds, the
-- uniform defect, and mellinMoment clampTest n ≈ 1/(n+2) for EVERY n (subsuming the five
-- per-degree engines).
#print axioms Square.pow_succ_lower
#print axioms Square.pow_succ_upper
#print axioms Square.powSum_lower
#print axioms Square.powSum_upper
#print axioms Square.powTest_sample
#print axioms Square.powSum_fold
#print axioms Square.riemannSum_powTest
#print axioms Square.powSum_defect_le
#print axioms Square.powTest_dyadicR0
#print axioms Square.genSum_powTest_eval
#print axioms Square.genSum_powTest_rate
#print axioms Square.riemannIntegral_powTest_succ
#print axioms Square.mellinMoment_clamp_general

-- THE PRE-HILBERT LAYER, brick 34 (Square/HilbertGram.lean) — THE HILBERT MATRIX IS THE GRAM
-- MATRIX OF THE MONOMIAL BAND: the monomial tests multiply (xⁱ·xʲ = x^{i+j}), ∫₀¹ clampᵐ =
-- 1/(m+1) for EVERY m, ⟨xⁱ,xʲ⟩ = 1/(i+j+1) in closed form, its symmetry, the moment map on
-- the monomials, and brick 33's Hausdorff law recovered as the i = 1 row.
#print axioms Square.powTest_mul
#print axioms Square.riemannIntegral_powTest_all
#print axioms Square.innerI_powTest_hilbert
#print axioms Square.hilbertGram_symm
#print axioms Square.mellinMoment_powTest
#print axioms Square.mellinMoment_clamp_via_hilbert

-- THE PRE-HILBERT LAYER, brick 35 (Square/DeepMemberThree.lean) — THE K=3 CO-SUPPORT MEMBER
-- READ OFF THE HILBERT MATRIX: the reusable integer-scaling helper natScale with its support/
-- pointwise/pairing transfer laws, and deep3 = x − 10x² + 30x³ − 35x⁴ + 14x⁵ with three
-- vanishing moments, membership, apartness, and the skeleton positivity at depth 3.
#print axioms Square.natScale_supp
#print axioms Square.natScale_val
#print axioms Square.innerI_zeroL2
#print axioms Square.innerI_natScale_val
#print axioms Square.powTest_window_one
#print axioms Square.pv_add
#print axioms Square.pv_neg
#print axioms Square.pv_scale
#print axioms Square.fv_add
#print axioms Square.fv_neg
#print axioms Square.fv_scale
#print axioms Square.deep3_supp
#print axioms Square.deep3_moment_zero
#print axioms Square.deep3_moment_one
#print axioms Square.deep3_moment_two
#print axioms Square.deep3_hatVanishes
#print axioms Square.deep3_value_tenth
#print axioms Square.deep3_apart
#print axioms Square.weil_psd_deep3

-- THE PRE-HILBERT LAYER, brick 36 (Square/CoSupportStrict.lean) — THE CO-SUPPORT FILTRATION
-- DOES NOT COLLAPSE: deep3's THIRD moment is −1/2520 ≠ 0 (read off the Hilbert matrix), so
-- deep3 sits in level 3 and not level 4; with brick 25's bumpU at level 0, two witnessed
-- strictness levels.
#print axioms Square.sub_ofQ_val
#print axioms Square.deep3_moment_three
#print axioms Square.deep3_not_hatVanishes_four
#print axioms Square.cosupport_strict_at_three
#print axioms Square.cosupport_strict_at_zero

-- THE PRE-HILBERT LAYER, brick 37 (Square/CoSupportChain.lean) — THE STRICT CHAIN THROUGH
-- DEPTH 4: the depth-1 member x − 3x² + 2x³ and the depth-2 member x − 6x² + 10x³ − 5x⁴,
-- each in P−N linear form with membership, first-non-vanishing moment, support and
-- apartness — filling brick 36's middle so 0 ⊋ 1 ⊋ 2 ⊋ 3 ⊋ 4 is strict throughout.
#print axioms Square.lin1_supp
#print axioms Square.lin1_moment_zero
#print axioms Square.lin1_moment_one
#print axioms Square.lin1_hatVanishes
#print axioms Square.lin1_not_hatVanishes_two
#print axioms Square.lin1_apart
#print axioms Square.lin2_supp
#print axioms Square.lin2_moment_zero
#print axioms Square.lin2_moment_one
#print axioms Square.lin2_moment_two
#print axioms Square.lin2_hatVanishes
#print axioms Square.lin2_not_hatVanishes_three
#print axioms Square.cosupport_chain_strict

-- THE PRE-HILBERT LAYER, brick 38 (Square/MomentDecay.lean) — THE SHARP MOMENT DECAY:
-- monomial nonnegativity, scalar Lipschitz transfer, and |⟨φ,xⁿ⟩| ≤ M_φ/(n+1) by two-sided
-- comparison on the sampling domain (the lower half free from L2Test.neg, which keeps M).
#print axioms Square.powTest_nonneg
#print axioms Square.lip_smul_of
#print axioms Square.mellinMoment_le
#print axioms Square.mellinMoment_abs_le

-- THE PRE-HILBERT LAYER, brick 39 (Square/MomentSummable.lean) — THE ℓ² DATUM: the squared
-- moments are summable with an explicit tail rate, Σ_{i<K} ⟨φ,x^{N+i}⟩² ≤ 2M²/(N+1) uniformly
-- in K, off the EXACT telescoping sum Σ_{i<K} 2/((N+i+1)(N+i+2)) = 2K/((N+1)(N+K+1)).
#print axioms Square.Rsq_le_of_abs_le
#print axioms Square.teleTerm_den
#print axioms Square.teleFrom_den
#print axioms Square.teleFrom_step
#print axioms Square.teleFrom_eq
#print axioms Square.teleFrom_le
#print axioms Square.mellinMoment_sq_le
#print axioms Square.momentSqTail_exact_le
#print axioms Square.momentSqTail_le
#print axioms Square.momentSqSum_le

-- THE PRE-HILBERT LAYER, brick 40 (Square/MomentNorm.lean) — THE ℓ² NORM OF THE MOMENT SEQUENCE
-- AS A CONSTRUCTED REAL: brick 39's tail rate becomes Bishop regularity under the index rescale
-- N = c(j+1), c ≥ 2M², so Σ_n ⟨φ,xⁿ⟩² is an Rlim with 0 ≤ · ≤ 2M² and the canonical rate.
#print axioms Analysis.RsumN_split_at
#print axioms Square.momentSqSum_split
#print axioms Square.momentSqTail_nonneg
#print axioms Square.momentSqSum_mono
#print axioms Square.momentSqSum_diff_le
#print axioms Square.momScale_bound
#print axioms Square.scale_cross
#print axioms Square.momentSqIdx_rate
#print axioms Square.momentSqIdx_mono
#print axioms Square.momentSqIdx_RReg
#print axioms Square.momentL2Sq_nonneg
#print axioms Square.momentL2Sq_le
#print axioms Square.momentL2Sq_approx

-- THE PRE-HILBERT LAYER, brick 41 (Square/DeepMemberFour.lean) — THE K=4 CO-SUPPORT MEMBER:
-- deep4 = x − 15x² + 70x³ − 140x⁴ + 126x⁵ − 42x⁶, read off the Hilbert matrix; first
-- non-vanishing moment ⟨deep4,x⁴⟩ = 1/13860, so the strict chain extends to 0 ⊋ … ⊋ 5.
#print axioms Square.deep4_supp
#print axioms Square.deep4_moment_zero
#print axioms Square.deep4_moment_one
#print axioms Square.deep4_moment_two
#print axioms Square.deep4_moment_three
#print axioms Square.deep4_hatVanishes
#print axioms Square.deep4_moment_four
#print axioms Square.deep4_not_hatVanishes_five
#print axioms Square.cosupport_strict_at_four
#print axioms Square.deep4_value_tenth
#print axioms Square.deep4_apart
#print axioms Square.weil_psd_deep4
#print axioms Square.cosupport_chain_strict_five

-- THE PRE-HILBERT LAYER, brick 42 (Square/CoSupportEnergy.lean) — DEEP CO-SUPPORT MEANS SMALL
-- MOMENT ENERGY: depth K kills the head of the squared-moment sum outright, so every partial
-- sum is a tail and brick 39's rate bounds them all: ‖φ̂‖² ≤ 2M²/(K+1); full co-support ⟹ 0.
#print axioms Square.momentSqSum_zero
#print axioms Square.momentSqSum_le_of_moments
#print axioms Square.momentL2Sq_le_of_moments
#print axioms Square.momentL2Sq_le_of_hatVanishes
#print axioms Square.momentL2Sq_zero_of_moments

-- THE PRE-HILBERT LAYER, brick 43 (Square/MomentCompletion.lean) — THE FIRST GENUINE ℓ²
-- INSTANCE OF THE TRUNCATION-UNIFORM COMPLETION: the moment vector, cut at the QUADRATIC
-- rescale c(j+1)², satisfies SqCauchyU (modulus independent of the truncation N).
#print axioms Square.momTrunc_diff_sq_le
#print axioms Square.RsumN_momTailTerm_le
#print axioms Square.dist2_momTrunc_le
#print axioms Square.momIdx_rate
#print axioms Square.momIdx_sqCauchyU
#print axioms Square.momIdx_completes

-- THE PRE-HILBERT LAYER, brick 44 (Square/MomentMember.lean) — THE COMPLETED MEMBER IS THE
-- MOMENT SEQUENCE: limMemberU (momCovIdx φ) i ≈ ⟨φ,xⁱ⟩ (uniform-rate limit evaluation, powered
-- by brick 38's sharp decay), so the cuts converge strongly to momSeq φ at every truncation.
#print axioms Square.momScale_ge_num
#print axioms Square.cut_index_le
#print axioms Square.limMemberU_momIdx
#print axioms Square.momIdx_converges_to_momSeq

-- THE PRE-HILBERT LAYER, brick 45 (Square/MomentEnergyDetect.lean) — THE ENERGY DETECTS THE
-- MOMENTS: ⟨φ,xⁿ⟩² ≤ momentL2Sq φ for every n (the X k ≤ lim X direction via term_le_Rlim), so
-- any moment apart from zero forces Pos energy; capstone Pos (momentL2Sq deep3) via ⟨deep3,x³⟩².
#print axioms Square.momentSqSum_le_momentL2Sq
#print axioms Square.mellinMoment_sq_le_momentL2Sq
#print axioms Square.momentL2Sq_pos_of_moment
#print axioms Square.deep3_moment_three_sq_pos
#print axioms Square.momentL2Sq_deep3_pos

-- THE PRE-HILBERT LAYER, brick 46 (Square/MomentGram.lean) — UNIFORM CAUCHY–SCHWARZ FOR MOMENT
-- SEQUENCES: (Σ_{n<N} ⟨φ,xⁿ⟩⟨ψ,xⁿ⟩)² ≤ momentL2Sq φ · momentL2Sq ψ at every truncation, from
-- the finite Lagrange-CS on the moment coordinate vectors + brick 45's partial-energy bound.
#print axioms Square.crossMomSum_diag
#print axioms Square.crossMomSum_sq_le

-- THE PRE-HILBERT LAYER, brick 47 (Square/MomentInvariant.lean) — THE MOMENT ENERGY IS A
-- MOMENT-INVARIANT: equal moments ⟹ equal momentL2Sq (the rescale is scaffolding, not content),
-- via brick 45 both ways through Rlim_le_const; second nonzero instance Pos (momentL2Sq bumpU).
#print axioms Square.momentSqSum_congr
#print axioms Square.momentL2Sq_le_of_moments_eq
#print axioms Square.momentL2Sq_congr
#print axioms Square.momentL2Sq_bumpU_pos

-- THE PRE-HILBERT LAYER, brick 48 (Square/CoSupportCompletion.lean) — THE SKELETON'S POSITIVITY
-- ON THE COMPLETED ℓ² MEMBER: the band coordinate of limMemberU (momCovIdx φ) is φ's first moment
-- (brick 44), killed by co-support, so burnol_pairing_psd_on_sonine fires at the completion
-- level on truncation-uniform data of certified nonzero energy (deep3, deep4 instances).
#print axioms Square.limMemberU_momIdx_band_zero
#print axioms Square.weil_psd_on_completed_cosupport
#print axioms Square.weil_psd_completed_deep3
#print axioms Square.weil_psd_completed_deep4
#print axioms Square.completed_cosupport_nonzero
#print axioms Square.deep3_momIdx_converges

-- THE PRE-HILBERT LAYER, brick 49 (Square/MomentPairing.lean) — THE BILINEAR MOMENT PAIRING
-- CONVERGES: ⟪φ,ψ⟫ = Σ_n ⟨φ,xⁿ⟩⟨ψ,xⁿ⟩ as a constructed real, with ⟪φ,φ⟫ ≈ momentL2Sq φ. The
-- window CS bound is the EXACT square of the rational 2MφMψ/(a+1), so Rle_of_Rsq_le is sqrt-free.
#print axioms Square.crossWindow_diag
#print axioms Square.crossBound_den
#print axioms Square.crossBound_num
#print axioms Square.crossWindow_sq_le
#print axioms Square.crossWindow_abs_le
#print axioms Square.crossMomSum_split
#print axioms Square.crossMomSum_diff_abs_le
#print axioms Square.crossScale_bound
#print axioms Square.crossIdx_dist
#print axioms Square.crossIdx_RReg
#print axioms Square.crossMomL2_approx
#print axioms Square.crossIdx_diag_mono
#print axioms Square.crossMomL2_diag

-- THE PRE-HILBERT LAYER, brick 50 (Square/MomentPairingLaws.lean) — THE PAIRING IS SYMMETRIC AND
-- UNIFORMLY BOUNDED: ⟪φ,ψ⟫ ≈ ⟪ψ,φ⟫ (cuts aligned by crossScale_comm, then innerN_symm through
-- Rlim_congr) and |⟪φ,ψ⟫| ≤ 2MφMψ (the window bound from cut 0, inherited from both sides).
#print axioms Square.crossScale_comm
#print axioms Square.crossMomL2_symm
#print axioms Square.crossMomSum_abs_le
#print axioms Square.crossMomL2_abs_le
#print axioms Square.momentL2Sq_le_via_pairing

-- THE PRE-HILBERT LAYER, brick 51 (Square/MomentPairingCS.lean) — CAUCHY–SCHWARZ AT THE LIMIT:
-- ⟪φ,ψ⟫² ≤ momentL2Sq φ · momentL2Sq ψ. The squared bound passes through the Bishop limit by
-- difference-of-squares (small factor × bounded factor) + the Archimedean Rle_of_Rsub_le_eps.
#print axioms Square.crossTwo_den
#print axioms Square.crossTwo_num
#print axioms Square.crossBound_add_self
#print axioms Square.crossMomL2_add_idx_abs_le
#print axioms Square.crossGap_le
#print axioms Square.crossMomL2_sq_le

-- THE PRE-HILBERT LAYER, brick 52 (Square/MomentPairingBilinear.lean) — THE PAIRING IS BILINEAR:
-- ⟪φ+ψ,χ⟫ ≈ ⟪φ,χ⟫+⟪ψ,χ⟫. RReg is not closed under +, and the three limits run along different
-- schedules, so the comparison is made at a COMMON CUT (crossMomSum_dist_limit: the pairing can
-- be read off ANY deep partial sum), where the finite identity is exact.
#print axioms Square.Rabs_sub_triangle
#print axioms Square.crossMomSum_dist_scheduled
#print axioms Square.crossMomSum_dist_limit
#print axioms Square.momSeq_add
#print axioms Square.crossMomSum_add_left
#print axioms Square.crossMomL2_add_left

-- THE PRE-HILBERT LAYER, brick 53 (Square/CoSupportPairing.lean) — DEEP CO-SUPPORT IS NEARLY
-- ORTHOGONAL TO EVERYTHING: |⟪φ,ψ⟫| ≤ 2MφMψ/(K+1) for EVERY ψ when φ ∈ HatVanishes·K (brick 42's
-- diagonal rate made bilinear). Co-support eats the head, so every partial sum is a K-window.
#print axioms Square.crossMomSum_zero_below
#print axioms Square.crossMomSum_eq_window
#print axioms Square.crossMomSum_abs_le_of_moments
#print axioms Square.crossMomL2_abs_le_of_moments
#print axioms Square.crossMomL2_abs_le_of_hatVanishes
#print axioms Square.deep3_crossMomL2_abs_le

-- THE PRE-HILBERT LAYER, brick 54 (Square/DeepMemberFive.lean) — THE K=5 CO-SUPPORT MEMBER:
-- deep5 = x − 21x² + 140x³ − 420x⁴ + 630x⁵ − 462x⁶ + 132x⁷; first non-vanishing moment
-- ⟨deep5,x⁵⟩ = 748873/9009 − 665/8 = −1/72072, so the strict chain reaches 0 ⊋ … ⊋ 6.
#print axioms Square.deep5_supp
#print axioms Square.deep5_moment_zero
#print axioms Square.deep5_moment_one
#print axioms Square.deep5_moment_two
#print axioms Square.deep5_moment_three
#print axioms Square.deep5_moment_four
#print axioms Square.deep5_hatVanishes
#print axioms Square.deep5_moment_five
#print axioms Square.deep5_not_hatVanishes_six
#print axioms Square.cosupport_strict_at_five
#print axioms Square.cosupport_chain_strict_six
#print axioms Square.deep5_value_tenth
#print axioms Square.deep5_apart
#print axioms Square.weil_psd_deep5

-- THE PRE-HILBERT LAYER, brick 55 (Square/CoSupportDimension.lean) — THE CO-SUPPORT LEVELS ARE
-- NOT ONE-DIMENSIONAL: deep3/deep4/deep5 all lie in level 3 and the moment functionals at 3,4,5
-- separate them TRIANGULARLY (nonzero diagonal); the first two coefficients are extracted, via
-- nat_eq_zero_of_ofQ_zero (no ofQ-injectivity in the substrate — collide Pos with not_Pos_zero).
#print axioms Square.nat_eq_zero_of_ofQ_zero
#print axioms Square.nat_eq_zero_of_ofQ_neg_zero
#print axioms Square.deep3_moment_four
#print axioms Square.deep4_moment_five
#print axioms Square.deep3_moment_five
#print axioms Square.cosupport_triangular_table
#print axioms Square.deep345_in_level_three
#print axioms Square.combo345_moment
#print axioms Square.combo345_moment_three
#print axioms Square.combo345_moment_four
#print axioms Square.deep34_independent

-- THE PRE-HILBERT LAYER, brick 56 (Square/MomentPairingNeg.lean) — THE PAIRING IS LINEAR AND
-- CONTINUOUS IN THE TEST: ⟪−φ,ψ⟫ ≈ −⟪φ,ψ⟫ (common-cut again, the schedules differ), hence
-- ⟪φ−ψ,χ⟫ ≈ ⟪φ,χ⟫−⟪ψ,χ⟫ and |⟪φ,χ⟫−⟪ψ,χ⟫| ≤ 2·M_{φ−ψ}·M_χ.
#print axioms Square.momSeq_neg
#print axioms Square.crossMomSum_neg_left
#print axioms Square.crossMomL2_neg_left
#print axioms Square.crossMomL2_sub_left
#print axioms Square.crossMomL2_dist_le

-- THE PRE-HILBERT LAYER, brick 57 (Square/CoSupportSubspace.lean) — THE CO-SUPPORT LEVELS ARE
-- GENUINE LINEAR SUBSPACES: closed under neg/add/sub/natScale on compact support (via the
-- moment route), so EVERY natural-coefficient combination of deep3/deep4/deep5 lies in level 3.
#print axioms Square.unitSupported_neg
#print axioms Square.unitSupported_add
#print axioms Square.unitSupported_sub
#print axioms Square.hatVanishes_neg
#print axioms Square.hatVanishes_add_supp
#print axioms Square.hatVanishes_sub
#print axioms Square.hatVanishes_natScale
#print axioms Square.combo345_supp
#print axioms Square.combo345_in_level_three

-- THE PRE-HILBERT LAYER, brick 58 (Square/CoSupportFamily.lean) — POSITIVITY ON AN INFINITE
-- FAMILY: every combo345 a b c lies in level 3, so the skeleton's positivity fires on all of
-- them (and on their completed ℓ² members); a ≥ 1 gives certified nonzero moment energy.
#print axioms Square.combo345_weil_psd
#print axioms Square.combo345_weil_psd_completed
#print axioms Square.combo345_moment_three_sq
#print axioms Square.combo345_energy_pos

-- THE PRE-HILBERT LAYER, brick 59 (Square/MomentQuadratic.lean) — THE MOMENT ENERGY IS A
-- QUADRATIC FORM: ‖(φ+ψ)^‖² expands by the pairing, and the parallelogram law holds. Derived
-- from the diagonal identity + symmetry + left-additivity; the ±X cancellation runs through the
-- RsumL additive normalizer (two in-place RsumL_cancel_anywhere splits, no permutation needed).
#print axioms Square.crossMomL2_add_right
#print axioms Square.crossMomL2_neg_right
#print axioms Square.momentL2Sq_neg
#print axioms Square.momentL2Sq_add
#print axioms Square.momentL2Sq_sub
#print axioms Square.momentL2Sq_parallelogram

-- THE PRE-HILBERT LAYER, brick 60 (Square/DeepMemberSix.lean) — THE K=6 CO-SUPPORT MEMBER:
-- deep6 = x − 28x² + 252x³ − 1050x⁴ + 2310x⁵ − 2772x⁶ + 1716x⁷ − 429x⁸; first non-vanishing
-- moment ⟨deep6,x⁶⟩ = 95311/280 − 2190451/6435 = 1/360360, so the chain reaches 0 ⊋ … ⊋ 7.
#print axioms Square.deep6_supp
#print axioms Square.deep6_moment_zero
#print axioms Square.deep6_moment_one
#print axioms Square.deep6_moment_two
#print axioms Square.deep6_moment_three
#print axioms Square.deep6_moment_four
#print axioms Square.deep6_moment_five
#print axioms Square.deep6_hatVanishes
#print axioms Square.deep6_moment_six
#print axioms Square.deep6_not_hatVanishes_seven
#print axioms Square.cosupport_strict_at_six
#print axioms Square.cosupport_chain_strict_seven
#print axioms Square.weil_psd_deep6

-- THE PRE-HILBERT LAYER, brick 61 (Square/MomentDefinite.lean) — POLARIZATION AND THE NULL
-- SPACE: 4⟪φ,ψ⟫ ≈ ‖(φ+ψ)^‖² − ‖(φ−ψ)^‖², and ‖φ̂‖² ≈ 0 ⟺ every moment vanishes, with the null
-- space annihilating the whole pairing (Cauchy–Schwarz). The constructive step is square-root
-- free: Rle_of_Rsq_le reflects the order through squaring, so x² ≈ 0 gives x ≈ 0 with no root.
#print axioms Square.Req_zero_of_sq_zero
#print axioms Square.moments_zero_of_momentL2Sq_zero
#print axioms Square.momentL2Sq_zero_iff
#print axioms Square.crossMomL2_zero_of_null
#print axioms Square.crossMomL2_zero_of_moments
#print axioms Square.momentL2Sq_polarization
#print axioms Square.crossMomL2_congr_of_energies
#print axioms Square.deep3_not_null
#print axioms Square.deep3_moment_not_all_zero

-- THE PRE-HILBERT LAYER, brick 62 (Square/L2Complete.lean) — THE UNIFORM L² COMPLETENESS
-- CRITERION: a ψ-FREE squared-Cauchy condition on a sequence of tests (L2CauchyU) yields the
-- extended L² pairing against EVERY test, by rescaling the index along the test's own rational
-- energy bound (selfBnd). Payoff: the co-support levels are closed under L² limits of functions.
#print axioms Square.selfQ_den
#print axioms Square.selfBnd_pos
#print axioms Square.selfQ_le
#print axioms Square.innerI_self_le_selfBnd
#print axioms Square.dist2I_scaled_le
#print axioms Square.pairingIU_RReg
#print axioms Square.pairingIU_dist
#print axioms Square.dist2I_self
#print axioms Square.L2CauchyU_const
#print axioms Square.pairingIU_const
#print axioms Square.pairingIU_zero_of_moments
#print axioms Square.pairingIU_cosupport_closed

-- SCHEDULE-INDEPENDENCE + RIGHT-LINEARITY OF THE EXTENDED PAIRING (Square/PairingIUReschedule.lean):
-- pairingIU reads Φ along the ψ-dependent schedule j↦selfBnd ψ·(j+1). This brick shows ANY coarser
-- schedule j↦B·(j+1) with B≥selfBnd ψ converges to the SAME limit at rate 4/(k+1)
-- (pairingIU_reschedule_rate — a direct dist2I + sqrt-free-CS estimate: the cross-schedule gap squares
-- to ≤(2/(k+1))² via innerI_sub_sq_le + Rle_of_Rsq_le, since B≥S relaxes (1/B)·selfBnd ψ≤1). Linearity
-- (add/neg/sub in the test argument) then follows by picking a common B and summing three reschedule
-- rates through the Archimedean collapse. The linearity the completion-level moment-determinacy
-- argument consumes; NOT positivity, NOT surjectivity. Step 4 = RH; crux fields stay none.
#print axioms Square.pairingIU_reschedule_rate
#print axioms Square.pairingIU_add_right
#print axioms Square.pairingIU_neg_right
#print axioms Square.pairingIU_sub_right

-- SCALAR HOMOGENEITY + [0,1]-CONGRUENCE OF THE EXTENDED PAIRING (Square/PairingIULinear2.lean):
-- pairingIU_natScale (pairingIU Φ (natScale c ψ) h = c·pairingIU Φ ψ h, by induction from
-- pairingIU_add_right with base pairingIU zeroL2 = 0) and pairingIU_unit_congr (the extended pairing
-- sees the test only on [0,1]: reschedule to a common B = selfBnd ψ + selfBnd ψ', where the two reads
-- agree by innerI_right_congr_on_unit). These lift the H₁ Bernstein-basis reduction to a limit member.
#print axioms Square.pairingIU_natScale
#print axioms Square.pairingIU_unit_congr

-- UNIFORM SELF-ENERGY OF AN L²-CAUCHY SEQUENCE (Square/PairingIUEnergy.lean): innerI_self_le_uniform
-- (⟨Φ_j,Φ_j⟩ ≤ 2·selfBnd(Φ 0)+8 for EVERY j) — a Cauchy sequence has uniformly bounded energies, via
-- the parallelogram doubling ⟨x,x⟩ ≤ 2·d²(x,y)+2·⟨y,y⟩ (from ⟨x−2y,x−2y⟩≥0) at y=Φ 0, with
-- d²(Φ_j,Φ 0)≤4. Feeds the pairing-level Cauchy–Schwarz bound in the moment-determinacy tail.
#print axioms Square.innerI_self_le_uniform

-- THE BERNSTEIN BASIS PAIRS TO ZERO AT THE COMPLETION LEVEL (Square/PairingBernBasisZero.lean): the H₁
-- reduction (innerI_clampProd_zero) lifted from a fixed test to a LIMIT MEMBER. pairingIU_clampProd_zero
-- (extended pairing against xᵏ(1−x)ᵐ vanishes when all extended moments do — the identical Pascal
-- recursion with pairingIU_unit_congr carrying the unit step + pairingIU_sub_right the split) and
-- pairingIU_bernBasis_zero (the normalized basis, through pairingIU_natScale).
#print axioms Square.pairingIU_clampProd_zero
#print axioms Square.pairingIU_bernBasis_zero

-- THE BERNSTEIN OPERATOR PAIRS TO ZERO AT THE COMPLETION LEVEL (Square/PairingBernOpZero.lean): mirror of
-- innerI_bernOpCTest_zero at the limit-member level. pairingIU_L2sumN_zero (a finite sum pairs to 0 if
-- each summand does), pairingIU_constMul (real-coeff homogeneity of the extended pairing, via the
-- reschedule rate + innerI_constMul + |c|≤mB), pairingIU_constMul_zero, and pairingIU_bernOpCTest_zero
-- (the operator B_N(χ) pairs to 0 when all extended moments of Φ vanish, for ANY approximated χ).
#print axioms Square.pairingIU_L2sumN_zero
#print axioms Square.pairingIU_constMul
#print axioms Square.pairingIU_constMul_zero
#print axioms Square.pairingIU_bernOpCTest_zero

-- ★ COMPLETION-LEVEL MOMENT DETERMINACY (Square/PairingMomentDeterminacy.lean): the culmination of the
-- extended-pairing arc. pairingIU_moment_zero_imp_zero — an L²-Cauchy limit member Φ whose extended
-- moments pairingIU Φ (xⁱ) h ALL vanish pairs to zero against EVERY test ψ (the moment map is injective
-- on the completion). Proof (sqrt-free): ψ ≈ B_N(ψ)+χ with χ the Bernstein residual; pairingIU Φ B_N(ψ)=0
-- (bernOpCTest_zero), and |pairingIU Φ χ| bounded per-read by integral CS + uniform self-energy (E) +
-- L²-density energy bound, key Qle E≤E², inherited through Rlim, forced to 0 by the 1/(k+1) rate.
-- L2Elt_moment_zero_imp_eq_zero reads it on the L2Elt structure (E.eq (L2Elt.of zeroL2)). NOT positivity,
-- NOT surjectivity onto function space; step 4 = RH; crux fields stay none.
#print axioms Square.pairingIU_moment_zero_imp_zero
#print axioms Square.L2Elt_moment_zero_imp_eq_zero

-- ★ FULL (TWO-MEMBER) INJECTIVITY OF THE MOMENT MAP ON THE COMPLETION (Square/PairingMomentInjective.lean):
-- pairingIU_moment_eq_imp_eq — two L²-Cauchy limit members Φ,Ψ with EQUAL extended moment sequences pair
-- EQUALLY against every test (L2Elt_moment_eq_imp_eq: E.eq F). The definitive injectivity statement, the
-- relative (equality) form of pairingIU_moment_zero_imp_zero. Supporting relative bricks mirror ④/⑤ with
-- equality: pairingIU_clampProd_eq / pairingIU_bernBasis_eq (Pascal induction, base = moment equality) and
-- pairingIU_L2sumN_eq / pairingIU_bernOpCTest_eq; pairingIU_bernResidual_bound extracts the determinacy
-- brick's per-read CS + uniform-energy + bernOp_L2 bound as a public, moment-independent helper serving both
-- members. NOT positivity, NOT surjectivity onto function space; step 4 = RH; crux fields stay none.
#print axioms Square.pairingIU_clampProd_eq
#print axioms Square.pairingIU_bernBasis_eq
#print axioms Square.pairingIU_L2sumN_eq
#print axioms Square.pairingIU_bernOpCTest_eq
#print axioms Square.pairingIU_bernResidual_bound
#print axioms Square.pairingIU_moment_eq_imp_eq
#print axioms Square.L2Elt_moment_eq_imp_eq

-- THE BERNSTEIN–DURRMEYER IMAGE AS A TEST + ITS L² CONVERGENCE (Square/DurrmeyerTest.lean): the foundation
-- for reconstructing an ARBITRARY L² element from its moments. durrTest φ n hn = L2sumN of
-- constTest((n+1)·⟨φ,b_{n,k}⟩)·bernBasisTest — the Durrmeyer image durrOp φ n packaged as an L2Test
-- (durrTest_eq_on_unit: agrees with durrOp φ n on [0,1]), so the L² machinery applies to it.
-- durrTest_L2_converges: ‖φ − durrTest φ ((k+3)²−2)‖²_{L²[0,1]} ≤ (φ.L/(k+3))² (mirror of
-- bernOp_L2_converges: durrOp_converges uniform pointwise bound + innerI_self_le_of_bound). NOT positivity,
-- NOT surjectivity; step 4 = RH; crux fields stay none.
#print axioms Square.durrTest_eq_on_unit
#print axioms Square.durrTest_L2_converges

-- ★ RECONSTRUCTION OF AN ARBITRARY L² ELEMENT (Square/DurrmeyerReconstruct.lean): the completion-bullet's
-- last open. Every completed L² member E is the L²-limit of the Bernstein–Durrmeyer polynomials of its OWN
-- approximants — reconSeq E m = durrTest (E.seq (3(m+1))) (deg m), an L2Elt L2Elt.recon E equal to E
-- (L2Elt_recon_eq: (L2Elt.recon E).eq E). This reconstructs the arbitrary (non-embedded) element, which
-- durrOpMom alone could not (converges only on embedded tests), via a diagonal over approximants. Pieces:
-- pairingIU_reschedule_rate_gen (arbitrary schedule ≥ selfBnd ψ·(m+1) → pairingIU at rate 4/(m+1));
-- dist2I_triangle2/dist2I_symm (sqrt-free L² triangle); reconSeq_cauchy (the schedule 3(m+1),
-- 3(m+1)(L.num.toNat+1) makes reconSeq L²-Cauchy); L2Elt_recon_moment (moments preserved, sqrt-free CS +
-- reschedule_gen); L2Elt_recon_eq (via the FREE completion-level injectivity L2Elt_moment_eq_imp_eq). NOT
-- surjectivity (Hausdorff), NOT positivity; step 4 = RH; crux fields stay none.
#print axioms Square.pairingIU_reschedule_rate_gen
#print axioms Square.dist2I_triangle2
#print axioms Square.dist2I_symm
#print axioms Square.reconSeq_cauchy
#print axioms Square.L2Elt_recon_moment
#print axioms Square.L2Elt_recon_eq

-- THE MOMENT MAP'S RANGE IS CONFINED — MOMENTS DECAY (Square/MomentRangeNecessary.lean): the Hausdorff /
-- surjectivity front, NECESSARY side. L2Elt_moment_decay: |E.moment n| ≤ √(energy/(2n+1)) with
-- energy=2·selfBnd(E.seq 0)+8 — a completed member's moments decay like 1/√n, so a non-decaying sequence
-- is NOT a moment sequence and the transform is NOT surjective onto arbitrary sequences. Read-level
-- integral CS + uniform self-energy + ⟨xⁿ,xⁿ⟩=1/(2n+1), Rsqrt on the rational radicand, inherited via
-- Rabs_Rlim_le. NOT the full Hausdorff characterization (sufficiency needs the Riesz/Hilbert-system build);
-- NOT positivity. Step 4 = RH; crux fields stay none.
#print axioms Square.L2Elt_moment_decay
-- L2Elt_pairing_bounded: the extended pairing is an L²-BOUNDED functional, |E.pairing ψ| ≤ √(energy·selfBnd ψ)
-- — the CHARACTERIZING necessary condition (by Riesz an L²-bounded moment functional ⟺ representable by an L²
-- element), confining the transform's range to bounded functionals. Same read-level CS + uniform energy +
-- ⟨ψ,ψ⟩≤selfBnd ψ + Rsqrt(rational) + Rabs_Rlim_le.
#print axioms Square.L2Elt_pairing_bounded

-- THE RATIONAL HILBERT FORM ↔ innerI BRIDGE (Square/QHilbertForm.lean): the FOUNDATION of the constructive
-- Hausdorff-SUFFICIENCY arc (building an L² element from a valid moment sequence via orthogonal polynomials).
-- qHil c c' d = Σ_{i,j<d} c_i c'_j/(i+j+1) (the rational Hilbert form of two ℚ-coeff-vectors); the bridge
-- innerI_qPolyTest_qPolyTest: ⟨qPolyTest c, qPolyTest c'⟩ = ofQ(qHil c c') (via innerI_L2sumN + innerI_constMul
-- + mellinMoment_qPolyTest). NOT the sufficiency result itself (orthogonalization + Riesz projection +
-- Parseval + convergence remain); NOT positivity. Step 4 = RH; crux fields stay none.
#print axioms Square.qHil_den_pos
#print axioms Square.innerI_qPolyTest_qPolyTest

-- THE RATIONAL HILBERT FORM IS POSITIVE-DEFINITE (Square/QHilbertPos.lean): the SECOND brick of the
-- Hausdorff-SUFFICIENCY arc — the norm-positivity the Gram–Schmidt orthogonalization of the moment
-- construction consumes. innerI_self_pos_of_ratpoint: φ(ofQ r)² > 0 ⟹ ∫₀¹ φ² > 0 for a RATIONAL
-- r ∈ [0,1] (the density strengthening of innerI_self_pos_of_dyadic, via sq_ge_on_piece_near at the
-- ℕ-computed enclosing dyadic index). qHil_self_pos: a nonzero ℚ-coeff vector c gives qHil c c d > 0
-- (apart at 1/M by poly_nonzero_evalP → nonzero rational value → Pos square → ratpoint definiteness →
-- the bridge). NOT the sufficiency result (orthogonalization + Riesz + Parseval remain); NOT positivity
-- beyond the finite form. Step 4 = RH; crux fields stay none.
#print axioms Square.innerI_self_pos_of_ratpoint
#print axioms Square.qHil_self_pos

-- BILINEARITY OF THE RATIONAL HILBERT FORM (Square/QHilbertBilinear.lean): the ALGEBRA of the
-- Gram–Schmidt orthogonalization (brick 3 of the sufficiency arc). qHil is linear in each
-- coefficient-vector argument (add/smul/neg, both sides), pushed through the double qsumL via
-- qsumL_add/qsumL_smul/qsumL_neg + the scalar distributive laws, factored through the inner-sum
-- abbreviation innerHil. NOT symmetry (needs a qsumL Fubini — a separate brick); NOT the
-- orthogonalization itself; NOT positivity. Step 4 = RH; crux fields stay none.
#print axioms Square.innerHil_den
#print axioms Square.qHil_eq_innerHil
#print axioms Square.innerHil_add
#print axioms Square.innerHil_smul
#print axioms Square.innerHil_neg
#print axioms Square.qHil_add_left
#print axioms Square.qHil_smul_left
#print axioms Square.qHil_neg_left
#print axioms Square.qHil_add_right
#print axioms Square.qHil_smul_right
#print axioms Square.qHil_neg_right

-- SYMMETRY OF THE RATIONAL HILBERT FORM (Square/QHilbertSymm.lean): completes the algebraic
-- foundation of brick 3. qHil_comm: qHil c c' d = qHil c' c d (the Hilbert matrix 1/(i+j+1) is
-- symmetric) — with bilinearity, qHil is a symmetric bilinear form, what Parseval + two-sided
-- orthogonality need. Proof: pull the outer coefficient in, exchange the double qsumL via the
-- reusable Fubini qsumL_qsumL_swap, refactor + reindex i+j+1 = j+i+1. NOT the orthogonalization
-- itself; NOT positivity. Step 4 = RH; crux fields stay none.
#print axioms Square.qsumL_qsumL_swap
#print axioms Square.qHil_comm

-- qHil DISTRIBUTES OVER A LINEAR COMBINATION OF VECTORS (Square/QHilbertComb.lean): the last algebra
-- before the Gram–Schmidt recursion. combVec ls cf v = Σ_{i∈ls} cf_i·v_i (pointwise); qHil_combVec_left/
-- _right expand qHil(Σ cf_i v_i, w) = Σ cf_i·qHil(v_i,w) (both arguments), by induction on ls from the
-- atomic add/smul laws with the zero base qHil 0 w = 0 (qHil_zero_left/_right). This is what the
-- orthogonality proof uses to expand the projection Σ cf_i q_i. NOT the recursion itself; NOT
-- positivity. Step 4 = RH; crux fields stay none.
#print axioms Square.qHil_zero_left
#print axioms Square.qHil_zero_right
#print axioms Square.combVec_den
#print axioms Square.qHil_combVec_left
#print axioms Square.qHil_combVec_right

-- THE GRAM–SCHMIDT CONSTRUCTION, FOUNDATIONS (Square/GramSchmidt.lean): the reusable core of the
-- orthogonal-polynomial construction (brick 3 of the sufficiency arc). eVec k = the monomial x^k
-- (1 at k, 0 else); projCoef d m q i = ⟨e_m,q_i⟩/⟨q_i,q_i⟩ with the Qinv-cancellation projCoef_cancel
-- (cf_i·⟨q_i,q_i⟩ = ⟨e_m,q_i⟩); nextVec d m q = e_m − Σ_{i<m} cf_i q_i with its den (nextVec_den),
-- support strictly above m (nextVec_support, given q_i supported on [0,i]) and monic-at-m
-- (nextVec_monic, leading coeff 1). NOT yet the orthogonality induction (next brick); NOT positivity.
-- Step 4 = RH; crux fields stay none.
#print axioms Square.eVec_den
#print axioms Square.eVec_self
#print axioms Square.eVec_ne
#print axioms Square.eVec_self_ne_zero
#print axioms Square.projCoef_den
#print axioms Square.projCoef_cancel
#print axioms Square.nextVec_den
#print axioms Square.nextVec_support
#print axioms Square.nextVec_monic

-- THE GRAM–SCHMIDT ORTHOGONALITY STEP (Square/GramSchmidtOrtho.lean): the mathematical heart of the
-- orthogonal-polynomial construction. nextVec_ortho: given q_0..q_{m-1} mutually orthogonal with
-- positive self-norms, the next vector q_m = e_m − Σ cf_i q_i is orthogonal to each earlier q_j
-- (⟨q_j, nextVec⟩_d = 0). Expand the projection in the 2nd argument (qHil_add_right/neg_right/
-- combVec_right), collapse the sum to its diagonal term (choice-free single-term collapse over
-- range m), cancel with projCoef_cancel, flip with qHil_comm so ⟨q_j,e_m⟩−⟨e_m,q_j⟩=0. NOT yet the
-- existential induction that assembles the full family (next brick); NOT positivity. Step 4 = RH.
#print axioms Square.nextVec_ortho

-- THE GRAM–SCHMIDT FAMILY EXISTS (Square/GramSchmidtFamily.lean): brick 3 of the sufficiency arc
-- COMPLETE. gramSchmidt_exists d: for every m ≤ d there is a coefficient family that is den-valid,
-- supported/monic on [0,m), and MUTUALLY ORTHOGONAL ⟨q_i,q_j⟩_d = 0 (i≠j) in the rational Hilbert
-- form. Induction on m extending by nextVec; orthogonality from nextVec_ortho (+ qHil_comm for the
-- mirror), self-norm positivity from qHil_self_pos on the monic q_i. This is the orthogonal basis
-- the moment-problem construction (bricks 4-6: Riesz projection, Parseval, convergence) runs on. NOT
-- those bricks; NOT the moment-range surjectivity; NOT positivity. Step 4 = RH; crux fields stay none.
#print axioms Square.gramSchmidt_exists

-- THE MOMENT FUNCTIONAL AND ITS LINEARITY (Square/MomentFunctional.lean): first brick of the moment-
-- REALIZATION sub-arc (bricks 4-6 of the sufficiency direction). Lam μ c d = Σ_{i<d} c_i·μ_i pairs a
-- polynomial's coeff vector against the external moment sequence μ; Lam_add/_smul/_neg/_combVec give
-- ℚ-linearity in the coeff argument (line-for-line clones of the qHil bilinearity with 1/(i+j+1)
-- replaced by μ_i). The Riesz projection reads its coefficients off Lam μ (q_k)/‖q_k‖². NOT the Riesz
-- projection / realization / convergence (later bricks); a finite-form object, NOT positivity. Step
-- 4 = RH; crux fields stay none.
#print axioms Square.Lam_den
#print axioms Square.Lam_add
#print axioms Square.Lam_smul
#print axioms Square.Lam_neg
#print axioms Square.Lam_combVec

-- PAIRING AGAINST A MONOMIAL (Square/QHilEVec.lean): the delta-collapse the realization identity runs
-- on. qsumL_range_single (public, choice-free single-term collapse over range m via List.range_succ);
-- qHil_eVec_right (j<d → ⟨c,x^j⟩_d = innerHil c d j, the j-th Hilbert moment) and Lam_eVec (j<d →
-- Λ_μ(x^j)=μ_j) both by the eVec delta-collapse (off-j vanishes by eVec_ne, at j identity by
-- eVec_self). NOT the realization/Parseval/convergence; NOT positivity. Step 4 = RH; crux stay none.
#print axioms Square.qsumL_range_single
#print axioms Square.qHil_eVec_right
#print axioms Square.Lam_eVec

-- THE RIESZ PROJECTION COEFFICIENT AND VECTOR (Square/RieszCoeff.lean): reading μ off the orthogonal
-- basis. aCoef μ d q k = Λ_μ(q_k)/⟨q_k,q_k⟩_d (GUARDED total, verbatim projCoef structure with ⟨e_m,q_k⟩
-- replaced by Λ_μ(q_k)); aCoef_cancel (aCoef_k·⟨q_k,q_k⟩=Λ_μ(q_k) on the range); qHil_self_num_pos
-- (monic q_k, k<d → ⟨q_k,q_k⟩_d>0 for the guard); pVec μ d q N = Σ_{k≤N} aCoef_k·q_k the degree-N
-- Riesz projection. NOT the realization identity / Parseval / convergence; NOT positivity. Step 4 = RH.
#print axioms Square.aCoef_den
#print axioms Square.aCoef_cancel
#print axioms Square.qHil_self_num_pos
#print axioms Square.pVec_den

-- THE RIESZ REALIZATION IDENTITY (Square/RieszRealize.lean): the mathematical core of brick 4.
-- realize_basis (l≤N → ⟨p_N,q_l⟩_d = Λ_μ(q_l)): expand p_N=Σ aCoef_k q_k (qHil_combVec_left), kill
-- off-diagonal by orthogonality (qsumL_range_single), cancel diagonal (aCoef_cancel). vec_self_expand
-- (a vector supported on [0,j] equals Σ_{i≤j} c_i·x^i, its own coeff expansion over the monomial
-- basis) — the change-of-basis the moment identity dissolves. NOT yet realize_moment (⟨p_N,x^j⟩=μ_j,
-- the strong induction) / Parseval / convergence; NOT positivity. Step 4 = RH; crux fields stay none.
#print axioms Square.realize_basis
#print axioms Square.vec_self_expand

-- THE MOMENT REALIZATION (Square/RieszMoment.lean): brick 4 COMPLETE. realize_moment (j≤N →
-- ⟨p_N,x^j⟩_d = μ_j): a strong induction on j that DISSOLVES the change of basis (no Hilbert-matrix
-- inverse). Defect D_i=⟨p_N,x^i⟩−μ_i vanishes for i<j (IH), so Σ_{i≤j}(q_j)_i·D_i collapses to its
-- leading term (q_j)_j·D_j (qsumL_range_single); that same combination = ⟨p_N,q_j⟩−Λ_μ(q_j)
-- (vec_self_expand+qHil_combVec_right+Lam_combVec+Lam_eVec), which vanishes by realize_basis; so
-- (q_j)_j·D_j=0, leading coeff ≉0, no-zero-divisors force D_j=0. NOT Parseval / convergence; NOT
-- positivity. Step 4 = RH; crux fields stay none.
#print axioms Square.realize_moment

-- PARSEVAL FOR THE RIESZ PROJECTION (Square/RieszParseval.lean): brick 5. parseval_norm
-- (⟨p_N,p_N⟩_d = Σ_{k≤N} aCoef_k·(aCoef_k·⟨q_k,q_k⟩_d)): expand outer p_N (qHil_combVec_left), use
-- ⟨q_k,p_N⟩=⟨p_N,q_k⟩ (qHil_comm) = Λ_μ(q_k) (realize_basis) = aCoef_k·⟨q_k,q_k⟩ (aCoef_cancel) — the
-- orthogonality telescoping on the projection. This is what the convergence brick differences into a
-- Bessel tail. NOT the L²-limit/convergence; NOT positivity. Step 4 = RH; crux fields stay none.
#print axioms Square.parseval_norm

-- THE BESSEL-TAIL IDENTITY FOR THE RIESZ PROJECTION (Square/RieszBessel.lean): brick 5.5. pVec_cross:
-- ⟨p_P, p_M⟩_d = Σ_{k≤M} aCoef_k·Λ_μ(q_k) for M ≤ P — expand the low projection (qHil_combVec_right) and
-- read each pairing off the basis (realize_basis); in particular ⟨p_N,p_M⟩ = ‖p_M‖² (increment
-- orthogonal to p_M). pVec_diff_normSq: ‖p_N − p_M‖²_d = ‖p_N‖²_d − ‖p_M‖²_d for M ≤ N — expand the
-- squared increment into the four Gram entries by bilinearity (qHil over pointwise Qsub), substitute the
-- two cross-terms (qHil_comm for the mirror), middle terms cancel. This is the exact quantity the
-- convergence brick bounds (the squared increments are a Bessel tail Σ_{M<k≤N} aCoef_k²‖q_k‖²).
-- Unconditional, finite, fixed dimension d. NOT the L²-limit / convergence (needs the dim-independent
-- family + a supplied Bessel modulus — next brick), NOT positivity. Step 4 = RH; crux fields stay none.
#print axioms Square.pVec_cross
#print axioms Square.pVec_diff_normSq

-- DIMENSION-INVARIANCE OF THE RATIONAL POLYNOMIAL TEST (Square/QPolyDimInv.lean): brick-6 substrate.
-- innerI_qPolyTest_dim_inv: if the coefficient vector c vanishes at every index ≥ D, the polynomial test
-- qPolyTest c d pairs to the SAME value at any dimension d ≥ D. Distribute over the finite sum
-- (innerI_L2sumN); the extra monomials c_i·xⁱ (i ≥ D) pair to zero (innerI_constMul scales by ofQ c_i ≈
-- 0), so the RsumN past D is inert (induction on d−D). The test-level companion of qHil_trunc_eq (brick
-- 3.5a): a fixed support-[0,N] vector (Riesz projection p_N) reads as an L² test at any d ≥ N+1 with the
-- same value — brings two projections of different degree to a common dimension. NOT the convergence /
-- L²-limit (needs a supplied Bessel modulus), NOT positivity. Step 4 = RH; crux fields stay none.
#print axioms Square.innerI_qPolyTest_dim_inv

-- COEFFICIENT-CONGRUENCE OF THE RATIONAL POLYNOMIAL TEST (Square/QPolyCoefCongr.lean): brick-6 substrate.
-- innerI_qPolyTest_coef_congr: coefficient vectors agreeing rationally give the same pairing —
-- (∀ i, c_i ≈ c'_i) ⟹ ⟨ψ, qPolyTest c d⟩ = ⟨ψ, qPolyTest c' d⟩. Distribute over the finite sum
-- (innerI_L2sumN); each monomial pairing is ofQ c_i · ⟨ψ, xⁱ⟩ (innerI_constMul), ofQ respects Qeq, sums
-- agree termwise (RsumN_congr). With innerI_qPolyTest_dim_inv this is the full bridge: p_N (whose
-- dimension-independence pVec_dim_inv is a POINTWISE Qeq) reads as the same L² functional at any
-- dimension and any Qeq-equal presentation. NOT the convergence / L²-limit (needs a supplied Bessel
-- modulus), NOT positivity. Step 4 = RH; crux fields stay none.
#print axioms Square.innerI_qPolyTest_coef_congr

-- THE L²-DISTANCE ↔ RATIONAL HILBERT FORM OF THE DIFFERENCE (Square/QPolyDistBridge.lean): brick-6
-- substrate. qPolyTest_dist2I: at a common dimension D, d²(qPolyTest cN D, qPolyTest cM D) = ofQ(qHil
-- (cN−cM)(cN−cM) D). Expand d² into the four Gram pairings by L²-bilinearity (innerI_sub_left/right),
-- read each off the bridge (innerI_qPolyTest_qPolyTest), combine the embedded rationals (Rsub_ofQ_ofQ),
-- recognise the four-term as qHil of the pointwise difference by qHil-bilinearity. Unconditional (no
-- orthogonality, no M ≤ N). Composed with pVec_diff_normSq (brick 5.5) it reads the squared increment of
-- the Riesz projections as ofQ(‖p_N‖² − ‖p_M‖²) — the quantity the convergence brick bounds. NOT the
-- L²-limit (needs the dim-independent family + dim-invariance + a supplied Bessel modulus), NOT
-- positivity. Step 4 = RH; crux fields stay none.
#print axioms Square.qPolyTest_dist2I

-- DIMENSION-INDEPENDENCE OF THE RIESZ COEFFICIENT ON THE FIXED FAMILY (Square/RieszDimInv.lean): brick
-- 6a. The L²-limit reads Riesz projections of GROWING degree, each naturally at its own dimension; the
-- Bessel-tail identity (pVec_diff_normSq) only applies when two share the SAME dimension/coefficients.
-- Lam_trunc: Λ_μ(c) is independent of the dimension past the support of c (a qsumL truncation).
-- aCoef_dim_inv: on gsFam, aCoef μ d gsFam k is independent of d > k — the guarded Λ_μ(q_k)/⟨q_k,q_k⟩ is
-- a ratio of two truncation-stable rationals (Lam_trunc + qHil_trunc_eq, brick 3.5a) with the
-- positive-numerator denominator preserved by Qinv. pVec_dim_inv: the degree-N projection is independent
-- of the dimension past N (combination congruence). Unconditional ℚ arithmetic. NOT the convergence /
-- L²-limit (needs a supplied Bessel modulus — next brick), NOT positivity. Step 4 = RH; crux fields none.
#print axioms Square.Lam_trunc
#print axioms Square.aCoef_dim_inv
#print axioms Square.pVec_dim_inv

-- THE RIESZ-PROJECTION SEQUENCE AND ITS L²-DISTANCE (Square/BesselSeqDist.lean): brick before the final
-- convergence brick. besselSeq μ m = qPolyTest (p_m)(m+1), the degree-m Riesz projection as an L² test.
-- besselSeq_innerI_bridge: besselSeq μ m pairs like the projection recomputed at any common dimension
-- D > m (dim-invariance past the support, then coefficient-congruence under pVec_dim_inv). dist2I_congr:
-- the squared distance depends only on the innerI-functional of its two arguments (four-term expansion +
-- innerI_swap). besselSeq_dist2I: d²(besselSeq μ j, besselSeq μ k) = ofQ(qHil (p_j − p_k)(p_j − p_k) D)
-- at any common D > j,k — transport to common dimension (dist2I_congr + bridge) then the distance bridge
-- (qPolyTest_dist2I). Composed with pVec_diff_normSq (brick 5.5) this is ofQ(‖p_k‖²−‖p_j‖²), the squared
-- increment the convergence brick bounds. Unconditional. NOT the convergence itself (L2CauchyU needs a
-- supplied Bessel modulus), NOT the limit element / its moments, NOT positivity. Step 4 = RH; crux none.
#print axioms Square.besselSeq_innerI_bridge
#print axioms Square.dist2I_congr
#print axioms Square.besselSeq_dist2I

-- THE MOMENT REALIZATION: THE L²-LIMIT OF THE RIESZ PROJECTIONS (Square/MomentRealize.lean): the final
-- brick of the moment-realization sub-arc (Hausdorff sufficiency). besselSeq_moment: n ≤ m ⟹ ⟨besselSeq
-- μ m, xⁿ⟩ = ofQ(μ n) — the finite realize_moment read through mellinMoment_qPolyTest + qHil_eVec_right,
-- so the projection reproduces μ up to its degree exactly. besselSeq_L2Elt_moment: CONDITIONAL on
-- L2CauchyU (besselSeq μ) (the constructive Riesz–Fischer / Bessel-Cauchy input, an explicit
-- audit-visible hypothesis, never asserted for a particular μ), the completed element E = ⟨besselSeq μ,·⟩
-- realizes μ on the moment map — ⟨E, xⁿ⟩ = ofQ(μ n) for every n; the reads are eventually exactly ofQ(μ
-- n) and the completion's 2/(j+1) rate (L2Elt_converges) pins the limit (Req_of_Rle_ofQ_all, reindex
-- j=k+n). The matching SUFFICIENT direction to MomentRangeNecessary, for sequences carrying the
-- convergence certificate. NOT surjectivity onto arbitrary sequences, NOT positivity. Step 4 = RH; crux
-- fields stay none.
#print axioms Square.besselSeq_moment
#print axioms Square.besselSeq_L2Elt_moment

-- THE CONSTRUCTIVE BESSEL MODULUS (Square/BesselCauchyModulus.lean): coda of the moment-realization
-- sub-arc — makes the Riesz–Fischer input rational/checkable. besselDiffNorm μ j k = qHil (p_j−p_k)²
-- (j+k+1), the rational squared L²-distance of the j,k-th Riesz projections (the ℚ-value besselSeq_dist2I
-- embeds); besselDiffNorm_den its positive denominator. besselSeq_L2CauchyU: a rational modulus
-- besselDiffNorm μ j k ≤ (1/(j+1)+1/(k+1))² produces the real L2CauchyU (besselSeq μ) (Rle_ofQ_ofQ turns
-- the ℚ-bound into the real Cauchy bound via besselSeq_dist2I). besselSeq_realizes_of_modulus: the
-- end-to-end composed statement — a μ with such a rational modulus is realized by a completed L² element,
-- ⟨E,xⁿ⟩=ofQ(μ n) ∀n. Still CONDITIONAL (the modulus is a supplied audit-visible hypothesis, never an
-- axiom, never asserted for a particular μ) — this only makes its shape rational and exhibitable. NOT
-- surjectivity onto arbitrary sequences, NOT positivity. Step 4 = RH; crux fields stay none.
#print axioms Square.besselDiffNorm_den
#print axioms Square.besselSeq_L2CauchyU
#print axioms Square.besselSeq_realizes_of_modulus

-- THE BESSEL PARTIAL NORM AND THE TAIL IDENTITY (Square/BesselPartialNorm.lean): closing brick of the
-- moment-realization sub-arc — exhibits the coda's rational modulus in its classical Bessel/Riesz–Fischer
-- shape. qHil_congr: pointwise Qeq in each coeff vector ⟹ Qeq of the Hilbert forms (double-qsumL congr).
-- pNorm μ N = qHil p_N p_N (N+1) = ‖p_N‖² (rational); pNorm_parseval: ‖p_N‖² = Σ_{k≤N} aCoef_k·(aCoef_k·
-- ⟨q_k,q_k⟩) (the Bessel sum, from parseval_norm on gsFam). pNorm_dim_inv: qHil p_N p_N d = ‖p_N‖² for
-- d>N (qHil_congr via pVec_dim_inv + qHil_trunc_eq). besselDiffNorm_eq_pNorm_sub: j≤k ⟹ besselDiffNorm μ
-- j k = ‖p_k‖² − ‖p_j‖² (orientation via qHil squared-diff symmetry, then pVec_diff_normSq, then pin each
-- norm to its minimal dimension). So the coda's modulus IS the classical statement that the Bessel sums
-- ‖p_N‖²=Σ aCoef_k²‖q_k‖² are ℚ-Cauchy at the framework rate. Unconditional ℚ arithmetic; does NOT remove
-- the realization's conditionality, NOT surjectivity, NOT positivity. Step 4 = RH; crux fields stay none.
#print axioms Square.qHil_congr
#print axioms Square.pNorm_parseval
#print axioms Square.pNorm_dim_inv
#print axioms Square.besselDiffNorm_eq_pNorm_sub

-- THE MOMENT PROBLEM IS WELL-POSED (Square/MomentProblemWellPosed.lean): capstone of the
-- moment-realization sub-arc — packages conditional existence + completion-level uniqueness.
-- besselSeq_realizes_unique: any L² element with the same moments as the realized one equals it
-- (L2Elt_moment_eq_imp_eq applied to besselSeq_realizes_of_modulus). moment_problem_wellposed: existence
-- ∧ uniqueness — μ (with a rational Bessel modulus) is realized by the completed element E, and every
-- completed element with those moments is E (the moment map is a bijection on this class = the
-- constructive Hausdorff moment theorem for the class). Existence is CONDITIONAL on the supplied rational
-- Bessel modulus (audit-visible, never asserted for a particular μ); uniqueness is unconditional. This is
-- classical measure-theoretic well-posedness of the MOMENT MAP, NOT surjectivity onto arbitrary
-- sequences, NOT positivity of any crux form. Step 4 = RH; crux fields stay none.
#print axioms Square.besselSeq_realizes_unique
#print axioms Square.moment_problem_wellposed

-- TRUNCATION-STABILITY OF THE RATIONAL HILBERT FORM (Square/QHilbertTrunc.lean): brick 3.5a. If c,c'
-- both vanish at every index ≥ D then qHil c c' d = qHil c c' D for d ≥ D (qHil_trunc_eq_of_ge), and
-- so agrees at any two dimensions ≥ D (qHil_trunc_eq). Two single-step extensions — innerHil_trunc_step
-- (extra inner term c_d/(d+j+1) ≈ 0) and qHil_trunc_step (that + extra outer term c'_d·… ≈ 0) — chained
-- by induction on the gap d−D, each peeling the top of the range via List.range_succ (choice-free). The
-- tool that pairs a fixed support-[0,N] vector (Riesz projection) at ANY dimension d ≥ N and gets the
-- same rational — prerequisite for the dimension-independent family and the L²-limit. NOT that family,
-- NOT convergence, NOT positivity. Step 4 = RH; crux fields stay none.
#print axioms Square.qHil_trunc_eq_of_ge
#print axioms Square.qHil_trunc_eq

-- THE DIMENSION-INDEPENDENT GRAM–SCHMIDT FAMILY (Square/GramSchmidtConcrete.lean): brick 3.5b. The
-- committed gramSchmidt_exists is a d-dependent existential; the L²-limit needs one FIXED family whose
-- vectors are stable as degree grows and whose orthogonality holds at EVERY dimension. gsBuild m is the
-- concrete family of the first m Gram–Schmidt vectors (structural recursion, extend at index m by
-- nextVec), gsFam k = gsBuild (k+1) k the k-th fixed orthogonal polynomial. gsBuild_lt: k < m ⟹
-- gsBuild m k = gsFam k (stability). gsBuild_props: the four invariants at every depth (den/support/monic
-- + DIMENSION-UNIFORM orthogonality ∀ d>i,j — nextVec_ortho at m+1 carried to all d by qHil_trunc_eq,
-- brick 3.5a). gsFam_den/gsFam_support/gsFam_monic/gsFam_ortho: the fixed family's d-free interface. NOT
-- the Riesz convergence / L²-limit (needs a supplied Bessel modulus — later brick), NOT surjectivity,
-- NOT positivity. Step 4 = RH; crux fields stay none.
#print axioms Square.gsBuild_lt
#print axioms Square.gsBuild_props
#print axioms Square.gsFam_den
#print axioms Square.gsFam_support
#print axioms Square.gsFam_monic
#print axioms Square.gsFam_ortho

-- THE PRE-HILBERT LAYER, brick 63 (Square/L2MomentBridge.lean) — THE MOMENT GEOMETRY IS AN L²
-- INVARIANT: ⟨φ,φ⟩ ≈ 0 ⟹ every moment vanishes ⟹ ‖φ̂‖² ≈ 0, and tests at L² distance zero have
-- the same moments, the same ℓ² energy and the same co-support depth. One-way only: the converse
-- is determinacy, untouched. Capstone: the moment side certifies ∫₀¹ deep3² apart from zero.
#print axioms Square.innerI_zero_of_innerI_self_zero
#print axioms Square.moments_zero_of_innerI_self_zero
#print axioms Square.momentL2Sq_zero_of_innerI_self_zero
#print axioms Square.mellinMoment_congr_of_dist2I
#print axioms Square.momentL2Sq_congr_of_dist2I
#print axioms Square.moments_vanish_congr_of_dist2I
#print axioms Square.innerI_deep3_self_not_zero

-- THE PRE-HILBERT LAYER, brick 64 (Square/PolyDeterminacy.lean) — DETERMINACY ON THE POLYNOMIAL
-- CLASS AND A DEGREE FLOOR: for a d-coefficient integer polynomial test, d vanishing moments
-- force zero L² energy, hence EVERY moment zero (brick 63). Contrapositive: a nonzero member of
-- co-support level K needs more than K coefficients — the growth deep3..deep6 exhibit is forced.
#print axioms Square.innerI_natScale_zero
#print axioms Square.innerI_polyN_zero
#print axioms Square.innerI_polyPN_zero
#print axioms Square.innerI_polyPN_self_zero
#print axioms Square.polyPN_all_moments_zero
#print axioms Square.momentL2Sq_polyPN_zero
#print axioms Square.polyPN_degree_floor
#print axioms Square.polyPN_level_null

-- THE PRE-HILBERT LAYER, brick 65 (Square/PolyMoment.lean) — EVERY POLYNOMIAL TEST'S MOMENT IN
-- CLOSED FORM: ⟨Σ a_i xⁱ, xⁿ⟩ = Σ a_i/(i+n+1), read off the Hilbert matrix. One theorem replacing
-- every per-member hand computation; co-support becomes a finite rational linear system, and with
-- brick 64 the d×d system already kills the whole moment sequence. Cross-checked on lin1 (−1/60).
#print axioms Square.polyMomQ_den
#print axioms Square.mellinMoment_polyN
#print axioms Square.mellinMoment_polyPN
#print axioms Square.polyPN_moments_zero_of_rational
#print axioms Square.polyPN_all_moments_zero_of_rational
#print axioms Square.polyMoment_lin1_zero
#print axioms Square.polyMoment_lin1_one

-- THE PRE-HILBERT LAYER, brick 66 (Square/PolyMember.lean) — THE MEMBER GENERATOR: matching
-- coefficient sums give [0,1] support (the "both parts sum to the same value" condition, now a
-- theorem), and K matching Hilbert contractions give HatVanishes · K. Exercised at once: deep7
-- (K=7, first non-vanishing moment −1/1750320) takes the strict chain to 0 ⊋ … ⊋ 8.
#print axioms Square.coefSumQ_den
#print axioms Square.polyN_window_val
#print axioms Square.polyPN_supp
#print axioms Square.polyPN_hatVanishes
#print axioms Square.deep7_supp
#print axioms Square.deep7_hatVanishes
#print axioms Square.deep7_moment_seven
#print axioms Square.deep7_not_hatVanishes_eight
#print axioms Square.cosupport_strict_at_seven
#print axioms Square.cosupport_chain_strict_eight
#print axioms Square.weil_psd_deep7

-- THE PRE-HILBERT LAYER, brick 67 (Square/CoSupportDimThree.lean) — THE LEVEL IS AT LEAST
-- THREE-DIMENSIONAL: the x⁵ row of the triangular table, where all three members contribute,
-- closing the third coefficient brick 55 left open. Brick 55's recorded blocker (denominators
-- 924·5544·72072 overrunning the elaborator) was WRONG and is retracted: this elaborates at the
-- DEFAULT heartbeat budget, because the assembled identity is linear in the coefficients.
#print axioms Square.combo345_moment_five
#print axioms Square.deep345_independent

-- CERTIFIED INTEGRATION, THE SPLITTING LAW (Square/IntegralSplit.lean) — ∫₀¹ f ≈ ∫₀^{1/2} f +
-- ∫_{1/2}^1 f. The one structural law the integral gateway lacked: every prior law acted on a
-- FIXED interval, so "positive on a piece ⟹ positive overall" had no route. Proof: an EXACT
-- finite identity on the dyadic sums (the two half partitions interleave into the finer one),
-- then three riemannIntegral_dyadic_dist reads at a common depth + the Archimedean criterion.
#print axioms Square.riemannSum_idx
#print axioms Square.RsumN_idx
#print axioms Square.affine_left_point
#print axioms Square.affine_right_point
#print axioms Square.riemannSum_halves
#print axioms Square.dyadicR_halves
#print axioms Square.dyadicR_halves_named
#print axioms Square.riemannIntegral_split_half_gen
#print axioms Square.riemannIntegral_split_half

-- CERTIFIED INTEGRATION, brick 69 (Square/IntegralPiece.lean) — POSITIVE ON A PIECE ⟹ POSITIVE
-- OVERALL: for a non-negative Lipschitz integrand, each half of [0,1] lower-bounds the whole
-- integral, so Pos on a half gives Pos overall. The first use of brick 68's splitting law; before
-- it, a bound established on part of the domain could not be transported to the whole at all.
#print axioms Square.riemannIntegral_ge_left_half
#print axioms Square.riemannIntegral_ge_right_half
#print axioms Square.riemannIntegral_pos_of_left_half
#print axioms Square.riemannIntegral_pos_of_right_half

-- CERTIFIED INTEGRATION, brick 70 (Square/IntervalSplit.lean) — EVERY INTERVAL SPLITS AT ITS
-- MIDPOINT: ∫_a^{a+w} f ≈ ∫_a^{a+w/2} f + ∫_{a+w/2}^{a+w} f. Brick 68 split [0,1]; this is the
-- general law, and iterating it reaches every dyadic sub-interval of every interval. Mechanism:
-- the affine pullbacks COMPOSE (α_{a,w}∘α_{0,1/2} = α_{a,w/2}), so each piece is already the right
-- interval integral once the moduli (L·w)·½ vs L·(w/2) are reconciled by riemannIntegral_congr_mod.
#print axioms Square.halfQ_den
#print axioms Square.halfQ_num
#print axioms Square.riemannIntegral_congr_mod
#print axioms Square.affineMap_half_left
#print axioms Square.affineMap_half_right
#print axioms Square.riemannIntegralI_split_half

-- CERTIFIED INTEGRATION, brick 71 (Square/IntervalPiece.lean) — A HALF OF AN INTERVAL LOWER-BOUNDS
-- IT, and interval integrals see their endpoints only through Qeq. The Qeq congruence is what an
-- induction over dyadic descents needs: a descent computes endpoints (a + 2q·w/2^{m+1} vs
-- a + q·w/2^m) that are equal rationals but not equal terms.
#print axioms Square.riemannIntegralI_congr_Q
#print axioms Square.riemannIntegralI_ge_left_half
#print axioms Square.riemannIntegralI_ge_right_half

-- CERTIFIED INTEGRATION, brick 72 (Square/DyadicDescent.lean) — EVERY DYADIC SUB-INTERVAL
-- LOWER-BOUNDS THE WHOLE: for f ≥ 0 and j < 2^m, ∫ over [a+j·w/2^m, a+(j+1)·w/2^m] ≤ ∫ over
-- [a,a+w]. The induction bricks 70/71 were built for; the piece may be arbitrarily small, which is
-- what a locality argument needs. j sits inside the den-positivity PROOF TERMS, so it is eliminated
-- by subst (from ∃ q, j = 2q ∨ j = 2q+1), never by rw.
#print axioms Square.two_pow_pos
#print axioms Square.dyadW_den
#print axioms Square.dyadW_num
#print axioms Square.dyadA_den
#print axioms Square.riemannIntegralI_ge_dyadic

-- CERTIFIED INTEGRATION, brick 73 (Square/IntervalMinorant.lean) — A POINTWISE LOWER BOUND ON A
-- PIECE IS A NUMERIC LOWER BOUND ON THE INTEGRAL: c ≤ g on [a,a+w] ⟹ w·c ≤ ∫_a^{a+w} g, via the
-- LOCAL comparison riemannIntegralI_le_unit (the bound is needed only on the piece). Composed with
-- brick 72's descent: a positive constant on one dyadic piece forces the whole integral positive.
#print axioms Square.riemannIntegralI_ge_const
#print axioms Square.riemannIntegralI_unit
#print axioms Square.riemannIntegral_pos_of_piece

-- THE PRE-HILBERT LAYER, brick 74 (Square/L2Definite.lean) — THE L² INNER PRODUCT IS DEFINITE AT
-- DYADIC POINTS: φ(j/2^m)² > 0 ⟹ ∫₀¹ φ² > 0, hence ∫₀¹ φ² ≈ 0 ⟹ φ vanishes at every dyadic
-- point. Restricting to DYADIC points removes the constructive location problem entirely — the
-- point IS a dyadic endpoint, so the enclosing piece is computed in ℕ with no real order decided.
-- Upgrades brick 64's determinacy from the moments to the FUNCTION on the polynomial class.
#print axioms Square.sq_nonneg_pt
#print axioms Square.exists_depth
#print axioms Square.affineMap_dist_le
#print axioms Square.sq_ge_on_piece
#print axioms Square.innerI_self_pos_of_dyadic
#print axioms Square.innerI_self_zero_imp_dyadic_zero
#print axioms Square.polyPN_dyadic_zero
-- brick 74b: the piece lemma with the point only NEAR the endpoint — the reusable half of the
-- density extension (a general real has no dyadic endpoint EQUAL to it, only ones within a width).
#print axioms Square.sq_ge_on_piece_near

-- CERTIFIED INTEGRATION, brick 75 (Square/DyadicApprox.lean) — EVERY RATIONAL HAS A DYADIC POINT
-- WITHIN 1/2^m: the constructive floor ⌊q·2^m⌋ as ℕ division, with the division algorithm as its
-- whole correctness proof. This is where the constructivity of the density argument lives: one
-- cannot locate a REAL, but one can locate a RATIONAL, and every real carries rational approximants.
#print axioms Square.dyadJ_bracket
#print axioms Square.dyadJ_lt
#print axioms Square.dyadApprox_gen
#print axioms Square.dyadApprox_spec

-- THE PRE-HILBERT LAYER, brick 76 (Square/L2DefiniteDensity.lean) — THE TRANSPORT HALF OF DENSITY:
-- with brick 74's dyadic zero, the Lipschitz certificate carries |φ(x)| ≤ L·|x−p| to any nearby
-- point, and the Archimedean criterion closes it. STATED UNDER a DyadicApproximable hypothesis
-- which is NOT discharged for general x — so this does not by itself lift brick 74 off the dyadics.
#print axioms Square.abs_le_of_near_dyadic
#print axioms Square.zero_of_dyadic_approximable
#print axioms Square.dyadicApproximable_dyadPt

-- THE REAL-TO-APPROXIMANT BOUND (Analysis/RSeqApprox.lean) — |x − ofQ (x.seq N)| ≤ 1/(N+1): a
-- Bishop real's rational data is an EFFECTIVE approximation with a known rate. This is the missing
-- half of the density argument for L2Definite: one cannot locate a real by comparison, but one can
-- read off a rational within a prescribed distance and then locate THAT (decidable).
#print axioms Analysis.Rabs_sub_seq_le
#print axioms Analysis.Rabs_seq_sub_le

-- THE PRE-HILBERT LAYER, brick 77 (Square/DyadicClamp.lean) — THE CLAMPED DYADIC INDEX: brick 75's
-- floor lands in [0,2^m) only for an in-range rational, but the density argument feeds it the
-- approximants x.seq N of a real in [0,1], which need NOT be in range. dyadJC caps the floor; the
-- range bound is unconditional, and the clamp is inert (so brick 75's estimate survives) in range.
#print axioms Square.dyadJC_lt
#print axioms Square.dyadJC_eq_of_lt
#print axioms Square.dyadJC_approx

-- THE PRE-HILBERT LAYER, brick 78 (Square/DyadicDense.lean) — DEFINITENESS AT EVERY RATIONAL POINT:
-- the rationals of [0,1) are dyadically approximable (brick 75's floor + brick 77's clamp + 2^m
-- outrunning any rational), which discharges brick 76's hypothesis there. So ∫₀¹φ² ≈ 0 kills φ at
-- every rational, and brick 64's polynomial determinacy reaches the FUNCTION on a dense point set.
#print axioms Square.dyadicApproximable_ofQ
#print axioms Square.innerI_self_zero_imp_rational_zero
#print axioms Square.polyPN_rational_zero

-- THE PRE-HILBERT LAYER, brick 79 (Square/DyadicDenseReal.lean) — DEFINITENESS AT EVERY POINT OF
-- [0,1]: every unit-interval real is dyadically approximable (locate x.seq N within 1/(N+1), floor
-- + clamp to a dyadic point, transport the vanishing value by Lipschitz), so ∫₀¹φ² ≈ 0 kills φ at
-- EVERY point. The out-of-range approximant (below 0 / in range / at-or-above 1) is the new work;
-- the polynomial class is thereby the zero FUNCTION on [0,1].
#print axioms Square.dyadicApproximable_of_unit
#print axioms Square.innerI_self_zero_imp_zero
#print axioms Square.polyPN_unit_zero

-- THE PRE-HILBERT LAYER, brick 80 (Square/L2Separation.lean) — THE L² INNER PRODUCT SEPARATES
-- POINTS OF [0,1]: brick 79's point-definiteness applied to the difference test — dist2I φ ψ ≈ 0
-- forces (φ−ψ)(x) ≈ 0 at every point of [0,1], i.e. φ(x) ≈ ψ(x). So the L² class injects into the
-- values on [0,1] (a genuine SEPARATING form). One direction; the converse is the [0,1]-restricted
-- integral-of-a-vanishing-integrand direction, not performed.
#print axioms Square.dist2I_zero_imp_pointwise_eq
#print axioms Square.innerI_sub_self_zero_imp_pointwise_eq
#print axioms Square.polyPN_dist2I_zero_imp_eq

-- THE PRE-HILBERT LAYER, brick 81 (Square/L2DefiniteIff.lean) — ⟨φ,φ⟩ IS A DEFINITE INNER PRODUCT
-- ON [0,1]: the reverse of brick 79. A function vanishing at every point of [0,1] has zero L²
-- energy (riemannIntegral_zero_of_partition_zero: the Riemann sums sample only i/(N+1) ∈ [0,1), so
-- partition-point vanishing kills every sum, hence dyadic sums, hence the telescoping limit). With
-- brick 79 forward this closes the iff (innerI_self_zero_iff_unit_zero) — the L² seminorm is a
-- genuine norm mod pointwise-[0,1] equality.
#print axioms Square.riemannIntegral_zero_of_partition_zero
#print axioms Square.innerI_self_zero_of_unit_zero
#print axioms Square.innerI_self_zero_iff_unit_zero

-- THE PRE-HILBERT LAYER, brick 82 (Square/L2MetricIff.lean) — THE L² DISTANCE IS A GENUINE METRIC
-- ON [0,1]: brick 80 (separation, forward) + brick 81 (reverse definiteness on the difference
-- test) close the two-directional iff — dist2I φ ψ ≈ 0 ⟺ φ, ψ agree at every point of [0,1]. The
-- L² distance-squared vanishes EXACTLY on the pointwise-[0,1]-equality relation.
#print axioms Square.dist2I_zero_iff_pointwise_eq

-- THE PRE-HILBERT LAYER, brick 83 (Square/CoSupportFunction.lean) — THE CO-SUPPORT MEMBERS ARE
-- GENUINELY NONZERO FUNCTIONS ON [0,1]: the .mpr of the definiteness iff (brick 81), contraposed —
-- a test with nonzero L² self-energy cannot vanish identically on [0,1]. Chained against the
-- certified Pos moment-energy, deep3 and the combo345 (a≥1) family are honestly nonzero FUNCTIONS
-- on [0,1], upgrading the filtration's strictness from moments to functions.
#print axioms Square.not_vanishing_of_innerI_self_not_zero
#print axioms Square.deep3_not_vanishing_on_unit
#print axioms Square.combo345_not_vanishing_on_unit

-- THE PRE-HILBERT LAYER, brick 84 (Square/CoSupportDistinct.lean) — DISTINCT CO-SUPPORT LEVELS ARE
-- DISTINCT FUNCTIONS ON [0,1]: the reusable bridge distinct_on_unit_of_moment_ne (a nonzero moment
-- of φ−ψ ⟹ φ,ψ don't agree on [0,1], via the metric iff brick 82 + moment bridge brick 63). deep3
-- (level 3, 3rd moment −1/2520) and deep4 (level 4, 3rd moment 0) are thereby distinct FUNCTIONS on
-- [0,1] — upgrading the moment-table independence to function level.
#print axioms Square.distinct_on_unit_of_moment_ne
#print axioms Square.deep3_deep4_distinct_on_unit

-- THE PRE-HILBERT LAYER, brick 85 (Square/CoSupportPairwise.lean) — THE THREE FLAGSHIP LEVEL-3
-- MEMBERS ARE PAIRWISE-DISTINCT FUNCTIONS ON [0,1]: brick 84's technique across all three pairs
-- (deep3/deep4 & deep3/deep5 differ at moment 3 = −1/2520 vs 0; deep4/deep5 differ at moment 4 =
-- 1/13860 vs 0), upgrading deep345_independent from moments to functions for the realized triple.
#print axioms Square.deep3_deep5_distinct_on_unit
#print axioms Square.deep4_deep5_distinct_on_unit
#print axioms Square.deep345_pairwise_distinct_on_unit

-- THE PRE-HILBERT LAYER, brick 86 (Square/MellinLinearNeg.lean) — THE MELLIN TRANSFORM RESPECTS
-- NEGATION AND SUBTRACTION: (−φ)^(n) ≈ −φ̂(n) (mellinHat_neg: moment by innerI_neg_left, twisted
-- window by riemannIntegralI_neg = twTerm_neg, tail by genSum_Rneg_of_termwise + Rlim_neg =
-- twTail_neg) and (φ−ψ)^(n) ≈ φ̂(n) − ψ̂(n) (mellinHat_sub, composing add+neg). So HatVanishes cuts
-- out genuine linear subspaces, closed under +, −, scalar negation.
#print axioms Square.twTerm_neg
#print axioms Square.twTail_neg
#print axioms Square.mellinHat_neg
#print axioms Square.mellinHat_sub

-- THE PRE-HILBERT LAYER, brick 87 (Square/MellinInjective.lean) — THE MELLIN TRANSFORM IS INJECTIVE
-- ON THE COMPACT POLYNOMIAL CLASS: a compactly supported polynomial test whose transform vanishes
-- below its coefficient count (HatVanishes … d) is the zero FUNCTION on [0,1] — brick 64's
-- polyPN_level_null (co-support ⟹ L²-null) welded to brick 79's definiteness (L²-null ⟹ pointwise
-- zero). The injectivity half of the transform pair, for the polynomial class.
#print axioms Square.polyPN_hatVanishes_zero_function

-- THE PRE-HILBERT LAYER, brick 88 (Square/MellinInjectivePair.lean) — THE MELLIN TRANSFORM SEPARATES
-- POLYNOMIAL TESTS: two compact polynomial tests with transforms (= moments) agreeing below max d d'
-- are the same function on [0,1] (polyPN_moment_eq_imp_function_eq). The difference is decomposed via
-- innerI-bilinearity into polyN pieces (each killed by brick 64's innerI_polyPN_zero) — no natScale
-- coefficient addition needed — so ⟨p−q,p−q⟩≈0, then brick 79 definiteness gives p≈q on [0,1]. The
-- uniqueness direction of the transform pair, on the polynomial class.
#print axioms Square.innerI_polyPN_diff_zero
#print axioms Square.innerI_polyPN_diff_self_zero
#print axioms Square.polyPN_moment_eq_imp_function_eq

-- THE PRE-HILBERT LAYER, brick 89 (Square/PairingUnitZero.lean) — A TEST VANISHING ON [0,1] PAIRS TO
-- ZERO WITH EVERYTHING (innerI_zero_of_left_unit_zero: ∫₀¹ φ·ψ ≈ 0 when φ vanishes on [0,1], via the
-- partition-restricted argument brick 81), and the nullity survives L² completion
-- (pairingIU_zero_of_left_unit_zero via Rlim_zero). With brick 79 the pairing's left null space is
-- EXACTLY the [0,1]-vanishing tests.
#print axioms Square.innerI_zero_of_left_unit_zero
#print axioms Square.pairingIU_zero_of_left_unit_zero

-- THE PRE-HILBERT LAYER, brick 90 (Square/PairingUnitCongr.lean) — THE L² PAIRING FACTORS THROUGH
-- [0,1]-RESTRICTION: tests agreeing on [0,1] pair identically with everything
-- (innerI_left_congr_on_unit, via brick 89 on the difference + innerI_sub_left; right argument by
-- innerI_symm). So ⟨·,·⟩ is a genuine bilinear form on the [0,1]-equivalence classes of tests.
#print axioms Square.innerI_left_congr_on_unit
#print axioms Square.innerI_right_congr_on_unit

-- THE PRE-HILBERT LAYER, brick 91 (Square/PairingUnitDist.lean) — THE L² METRIC FACTORS THROUGH
-- [0,1]-RESTRICTION: dist2I depends only on the [0,1]-restrictions of both tests
-- (dist2I_congr_on_unit, via brick 90's two-argument congruence on φ−ψ). With bricks 82/89/90 the L²
-- inner product and its metric are a well-defined, definite structure on the [0,1]-equivalence classes.
#print axioms Square.dist2I_congr_on_unit

-- THE PRE-HILBERT LAYER, brick 92 (Square/PairingIUCongr.lean) — THE EXTENDED PAIRING IS WELL-DEFINED
-- ON [0,1]-CLASSES AT THE COMPLETION LEVEL: two L²-Cauchy sequences whose members agree on [0,1] have
-- equal extended pairing (pairingIU_congr_on_unit, via brick 90's left congruence through Rlim_congr).
-- Closes the [0,1]-restriction thread (89-92): the pairing/metric structure is stable under completion.
#print axioms Square.pairingIU_congr_on_unit

-- THE PRE-HILBERT LAYER, brick 93 (Square/ContinuousMoment.lean) — THE COMPACT-SIDE CONTINUOUS MELLIN
-- PARAMETER: the transform ∫₀¹ φ(t)·t^s dt at a continuous exponent s ≥ 0, generalizing the integer
-- moments mellinMoment φ n. The power t↦t^s is totalized on [0,1] by the reciprocal clamp
-- gPowClamp(−s)∘clampedInv a (equal to t^s on [a,1], constant a^s below), a total bounded Lipschitz
-- L2Test; compactMoment = innerI φ against it. The compact analog of the theta half-line thetaMellinPow.
#print axioms Square.compactPow
#print axioms Square.compactPow_nonneg
#print axioms Square.compactPow_abs_le_one
#print axioms Square.compactPow_congr
#print axioms Square.compactPowL
#print axioms Square.compactPowL_den
#print axioms Square.compactPowL_num
#print axioms Square.compactPow_lipschitz
#print axioms Square.compactPowTest
#print axioms Square.compactMoment

-- THE PRE-HILBERT LAYER, brick 94 (Square/ContinuousMomentLinear.lean) — THE CONTINUOUS MELLIN
-- TRANSFORM IS LINEAR IN THE TEST AND L²-BOUNDED: compactMoment φ a s = innerI φ against a fixed
-- power, so additivity/negation/subtraction in φ are the first-slot laws of innerI, and the
-- Cauchy–Schwarz bound (compactMoment φ a s)² ≤ ⟨φ,φ⟩·⟨t^s,t^s⟩ is the continuous-exponent analog of
-- mellinMoment_cs — compactMoment · a s is an L²-bounded linear functional at every exponent s ≥ 0.
#print axioms Square.compactMoment_add
#print axioms Square.compactMoment_neg
#print axioms Square.compactMoment_sub
#print axioms Square.compactMoment_cs

-- THE PRE-HILBERT LAYER, brick 95 (Square/ContinuousMomentZero.lean) — THE CONTINUOUS TRANSFORM
-- SPECIALIZES TO THE INTEGER SKELETON AT s=0: compactPow a 0 t ≈ 1 everywhere (t^0 = exp 0 = 1), so
-- the compact power test agrees with oneTest = powTest 0 on [0,1] and innerI (which only sees [0,1])
-- cannot distinguish them — compactMoment φ a 0 ≈ mellinMoment φ 0 = ∫₀¹ φ. First evaluation of the
-- continuous transform; anchors it as a genuine extension of the integer moments.
#print axioms Square.compactPow_zero
#print axioms Square.compactMoment_zero

-- THE PRE-HILBERT LAYER, brick 96 (Square/ContinuousMomentExp.lean) — THE COMPACT POWER IS LIPSCHITZ IN
-- THE EXPONENT: |compactPow a s x − compactPow a s' x| ≤ 4·|s−s'|·L_x, where L_x = log of the clamped
-- reciprocal base (compactBaseLog, ≥ 0). Via the symmetric exp-Lipschitz RexpReal_abs_lipschitz (bound
-- 1, each exponent −s·L_x ≤ 0) + the distributive collapse (−s·L)−(−s'·L) = (s'−s)·L. Pointwise
-- continuity in s — the constant is x-dependent; the uniform (moment-level) version needs L_x ≤ log(1/a).
#print axioms Square.compactBaseLog
#print axioms Square.compactBaseLog_nonneg
#print axioms Square.compactPow_exp_lipschitz

-- THE PRE-HILBERT LAYER, brick 97 (Square/ContinuousMomentFloor.lean) — THE TRANSFORM'S INTEGRAND IS
-- FLOOR-INDEPENDENT AT RATIONAL SAMPLE POINTS: at q ≥ a the clamp is inert (clampedInv a q = 1/q), so
-- compactPow a s q ≈ (1/q)^{−s} drops the floor (compactPow_ofQ), and two floors a,a' ≤ q give the same
-- value (compactPow_floor_indep). The certified integral samples only rationals i/(N+1), so above the
-- floor the transform is floor-free — the structural fact underpinning the a→0 limit.
#print axioms Square.compactPow_ofQ
#print axioms Square.compactPow_floor_indep

-- THE PRE-HILBERT LAYER, brick 98 (Square/ContinuousMomentMono.lean) — THE COMPACT POWER IS ANTITONE IN
-- THE EXPONENT: s ≤ s' ⟹ compactPow a s' t ≤ compactPow a s t. compactPow a σ t = exp(−σ·L_t) with
-- L_t = compactBaseLog ≥ 0, so a larger σ scales −σ·L_t down and exp is monotone (RexpReal_le_of_le).
-- The monotone companion to brick 96's continuity; holds for all t, all s ≤ s' (no sign hypothesis).
#print axioms Square.compactPow_antitone_exp

-- THE PRE-HILBERT LAYER, brick 99 (Square/ContinuousMomentAdd.lean) — THE POWER LAW IN THE EXPONENT:
-- compactPow a (s+s') t ≈ compactPow a s t · compactPow a s' t (t^{s+s'} = t^s·t^{s'}). Via
-- −(s+s') = −s + −s' (Rneg_Radd) + right-distributivity + RexpReal_add: exp(−(s+s')·L) =
-- exp(−s·L)·exp(−s'·L). The totalized power is a homomorphism (ℝ,+)→(ℝ,·) in the exponent — the third
-- exponent-structure law after continuity (96) and monotonicity (98). Holds for all s,s',t.
#print axioms Square.compactPow_exp_add

-- THE PRE-HILBERT LAYER, brick 100 (Square/ContinuousMomentValue.lean) — THE t^s IDENTIFICATION AT
-- RATIONAL POINTS: compactPow a s (q) ≈ exp(−s·(log q_den − log q_num)) = q^s for q ∈ [max(a,1/4),1].
-- The general-real log machinery is blocked (no per-index band bounds), but ofQ constants have constant
-- sequences → trivial bounds; so at the rational partition points the integral samples, gPowClamp_ofQ_eq
-- (RlogPos_congr_gen at B=4) drops the clamp and rrpowPos_ofQ_eq (RlogPos_ofQ_eq_logN) evaluates the log.
-- Also rlogPos_one (log 1 = 0). The first genuine t^s identification on the totalized compact power.
#print axioms Square.rlogPos_one
#print axioms Square.rrpowPos_ofQ_eq
#print axioms Square.gPowClamp_ofQ_eq
#print axioms Square.compactPow_ofQ_pow

-- THE PRE-HILBERT LAYER, brick 101 (Square/ContinuousMomentValueAll.lean) — THE t^s IDENTIFICATION AT
-- ALL RATIONAL POINTS OF (a,1]: compactPow a s (q) ≈ q^s for every rational q ∈ (a,1], no lower cutoff.
-- Brick 100's q ≥ 1/4 cap (the [1,4] radius of RlogPos_ofQ_eq_logN) is lifted by RlogPos_eq_Rlog_gen at
-- K=(A+D)², where the convergence condition 1 ≤ K·(1−ρ²) becomes 1 ≤ 4AD (true ∀ A,D ≥ 1). So
-- RlogPos_ofQ_eq_logN_all evaluates log(A/D)=logN A−logN D for all A≥D≥1, and the whole chain
-- (rrpowPos_ofQ_eq_all → gPowClamp_ofQ_eq_all → compactPow_ofQ_pow_all) drops the A≤4D hypothesis. Now
-- covers every rational partition point i/(N+1) ∈ [a,1] the certified integral samples.
#print axioms Square.RlogPos_ofQ_eq_logN_all
#print axioms Square.rrpowPos_ofQ_eq_all
#print axioms Square.gPowClamp_ofQ_eq_all
#print axioms Square.compactPow_ofQ_pow_all

-- THE PRE-HILBERT LAYER, brick 102 (Square/ContinuousMomentOne.lean) — THE COMPACT POWER AT EXPONENT 1
-- IS THE IDENTITY AT RATIONAL POINTS: compactPow a 1 (q) ≈ q for every rational q ∈ (a,1] (t^1=t). The
-- engine Rexp_logN_sub reads exp(logN A − logN D) ≈ A/D for all A,D ≥ 1 (RexpReal_add + Rexp_logN +
-- RexpReal_neg_eq_recip); at s=1 the brick-101 closed form collapses to log q_num − log q_den = log q.
#print axioms Square.Rexp_logN_sub
#print axioms Square.compactPow_ofQ_one

-- THE PRE-HILBERT LAYER, brick 103 (Square/ContinuousMomentTwo.lean) — THE COMPACT POWER AT EXPONENT 2
-- IS THE SQUARE AT RATIONAL POINTS: compactPow a 2 (q) ≈ q² for every rational q ∈ (a,1], via the power
-- law (brick 99, compactPow a (1+1) = compactPow a 1 · compactPow a 1) and the s=1 value (brick 102).
-- A worked instance of the integer-power reader the moment identification iterates.
#print axioms Square.compactPow_ofQ_two

-- THE PRE-HILBERT LAYER, brick 104 (Square/ContinuousMomentGeneral.lean) — THE COMPACT POWER AT EXPONENT
-- 1 IS THE IDENTITY FOR GENERAL REAL t: compactPow a 1 t ≈ t for every real t ∈ [a,1], lifting the
-- rational value (brick 102) to all reals by density. For any t ∈ [a,1] the clamped rational sample
-- qN = clamp(t.seq N,[a,1]) is within 1/(N+1) of t (band_approx_close, via the 1-Lipschitz band
-- projection qBandQ) and carries the value; step_bound + Archimedean collapse (Rle_of_Rsub_le_eps) close
-- it. No exp∘log inverse — the density route goes through the rational values. Closes the doc's flagged
-- "not for general real t" at s=1.
#print axioms Square.step_bound
#print axioms Square.band_approx_close
#print axioms Square.compactPow_one_general

-- THE PRE-HILBERT LAYER, brick 105 (Square/ContinuousMomentGenTwo.lean) — THE COMPACT POWER AT EXPONENT 2
-- IS THE SQUARE FOR GENERAL REAL t: compactPow a 2 t ≈ t² for every real t ∈ [a,1], composing the
-- general-real s=1 identity (brick 104) with the power law (brick 99). The integer t^n identification
-- now holds for all real t ∈ [a,1] by iterating, not only rationals.
#print axioms Square.compactPow_two_general

-- THE PRE-HILBERT LAYER, brick 106 (Square/ContinuousMomentClamp.lean) — THE COMPACT POWER AT s=1 AGREES
-- WITH THE CLAMPED-IDENTITY TEST ON [a,1]: compactPow a 1 t ≈ clampTest.f t for every real t ∈ [a,1]
-- (brick 104 + clamp01 inertness). The integrands compactPow a 1 and (powTest 1).f coincide off the
-- sub-a region, pinning the floor-dependence of compactMoment φ a 1 vs mellinMoment φ 1 to [0,a) — the
-- O(M·a) tail whose a→0 limit is the last Mellin step.
#print axioms Square.compactPow_one_eq_clamp

-- CERTIFIED INTEGRATION, brick 107 (Square/IntegralTailBound.lean) — THE DYADIC TAIL BOUND: a
-- globally-bounded (|f| ≤ B) Lipschitz integrand that vanishes on the dyadic tail [1/2^m,1] has
-- |∫₀¹ f| ≤ B·(1/2^m). Induction on the depth m via the midpoint split (brick 68): the [1/2,1] half
-- vanishes by hypothesis, the [0,1/2] half rescales to depth m under the affine pullback and the width
-- factor 1/2 supplies the geometric decay. The arbitrary-a subdivision ∫₀¹ = ∫₀^a + ∫_a^1 is NOT in
-- the repo and NOT needed — the floor is ours to choose, so dyadic floors suffice. The private base
-- case (riemannIntegral_abs_le, the global |∫| ≤ B) and affine helper (affine_upper) carry no audit
-- line (private). This is the locality tool for the a→0 Mellin limit.
#print axioms Square.riemannIntegral_dyadic_tail_bound

-- THE PRE-HILBERT LAYER, brick 108 (Square/ContinuousMomentTailBound.lean) — THE FLOOR DEFECT DECAYS
-- LIKE 1/2^m: |compactMoment φ (1/2^m) 1 − mellinMoment φ 1| ≤ 2·M_φ·(1/2^m). The difference of the
-- continuous-floor and integer Mellin moments is innerI φ of the difference test (via innerI_sub_right,
-- the second-slot subtraction derived from innerI_symm + innerI_sub_left); its integrand vanishes on
-- the dyadic tail [1/2^m,1] (brick 106: compactPow 1 ≈ clamp01, and (powTest 1).f = one·clamp01 ≈
-- clamp01) and is bounded by 2·M_φ, so the dyadic tail bound (brick 107) gives the geometric decay.
-- The a→0 Mellin limit made quantitative, with an explicit modulus of convergence.
#print axioms Square.innerI_sub_right
#print axioms Square.compactMomentOne_sub_mellin_bound

-- THE PRE-HILBERT LAYER, brick 109 (Square/ContinuousMomentLimit.lean) — THE a→0 MELLIN LIMIT AS A
-- CONSTRUCTED LIMIT OBJECT: Rlim_{j→∞} compactMoment φ (1/2^{r(j)}) 1 ≈ mellinMoment φ 1
-- (compactMomentOne_limit_eq_mellin). The depth reindex r(j)=(⌈2·M_φ⌉+1)(j+1) absorbs the constant
-- (via n<2^n), so the reindexed sequence lies within 1/(j+1) of the Mellin moment (compactMomentSeq_rate);
-- it is regular (compactMomentSeq_RReg, triangle through the limit) and its Bishop limit IS the Mellin
-- moment (Rlim_eval_real_rate). The continuous parameter proper at the transform boundary s=1: the
-- compact totalization's floor dependence is a removable artifact. momRate/compactMomentSeq are defs.
#print axioms Square.compactMomentSeq_rate
#print axioms Square.compactMomentSeq_RReg
#print axioms Square.compactMomentOne_limit_eq_mellin

-- THE PRE-HILBERT LAYER, brick 110 (Square/ContinuousMomentFloorReal.lean) — REAL-LEVEL FLOOR
-- INDEPENDENCE: compactPow a s x ≈ compactPow a' s x for EVERY real x ≥ both floors
-- (compactPow_floor_indep_real), lifting brick 97's rational-point floor-independence to all reals via
-- clampedInv_eq_of_ge (above the floor the clamped reciprocal IS 1/x). The positivity witness for x is
-- free from x ≥ a > 0 (Pos_mono). The structural fact the general-s a→0 limit rests on.
#print axioms Square.compactPow_floor_indep_real

-- THE PRE-HILBERT LAYER, brick 111 (Square/ContinuousMomentGenTail.lean) — THE COMPACT MELLIN MOMENT AT
-- GENERAL s IS CAUCHY IN THE FLOOR: |compactMoment φ (1/2^p) s − compactMoment φ (1/2^q) s| ≤
-- 2·M_φ·(1/2^p) for p ≤ q (compactMoment_floor_diff_bound). At general real s there is no integer
-- target (unlike s=1, brick 109) — the deliverable is that the floor sequence CONVERGES. The two
-- integrands agree on the overlap [1/2^p,1] (real-level floor-independence, brick 110), so their
-- difference (innerI φ of the difference test, via innerI_sub_right) vanishes on the dyadic tail and is
-- bounded by 2·M_φ; the dyadic tail bound (brick 107) gives the geometric decay. compactPowTestF/
-- compactMomentF are defs (no audit line). Structurally identical to brick 108.
#print axioms Square.compactMoment_floor_diff_bound

-- THE PRE-HILBERT LAYER, brick 112 (Square/ContinuousMomentGenLimit.lean) — THE CONTINUOUS MELLIN
-- MOMENT AT GENERAL REAL s EXISTS: the compact moment at exponent s converges as the floor → 0 to a
-- constructed real (compactMomentGenLim), defined as the Bishop limit of the regular reindexed floor
-- sequence. At general s there is no integer target — the content is that the sequence is CAUCHY
-- (compactMomentGenSeq_RReg): brick 111's floor-difference bound at the two reindexed depths, weakened
-- through the same constant-absorbing reindex as brick 109 (via n<2^n), feeding RReg_of_real_bound; the
-- two orderings by Nat.le_total. compactMomentGenSeq_tendsto = the a→0 convergence (Rlim_tendsTo).
-- compactMomentGenSeq/compactMomentGenLim are defs; gen_reindex_Qle/momRate_mono private (no audit).
#print axioms Square.compactMomentGenSeq_RReg
#print axioms Square.compactMomentGenSeq_tendsto

-- THE PRE-HILBERT LAYER, brick 113 (Square/ContinuousMomentNatExp.lean) — THE COMPACT POWER AT THE
-- INTEGER EXPONENT n IS THE CLAMPED MONOMIAL: compactPow a (natExpR n) t ≈ (powTest n).f t = clamp01ⁿ
-- for real t∈[a,1] (compactPow_natExpR_eq_powTest), generalizing brick 106 (s=1) to all integer
-- exponents. Induction on n: base compactPow_zero, step power law (brick 99) + IH + brick 106.
-- natExpR n = n ones; natExpR_nonneg + natExpR_eq_ofQ (≈ ofQ⟨n,1⟩) are the σ-data. natExpR is a def.
#print axioms Square.natExpR_nonneg
#print axioms Square.natExpR_eq_ofQ
#print axioms Square.compactPow_natExpR_eq_powTest

-- THE PRE-HILBERT LAYER, brick 114 (Square/ContinuousMomentNatTail.lean) — THE FLOOR DEFECT AT THE
-- INTEGER EXPONENT n DECAYS LIKE 1/2^m: |compactMoment φ (1/2^m) n − mellinMoment φ n| ≤ 2·M_φ·(1/2^m)
-- (compactMomentF_natExpR_sub_mellin_bound). Brick 113 makes the compact integrand agree with
-- (powTest n).f on [1/2^m,1], so the difference (innerI φ of the difference test, via innerI_sub_right)
-- vanishes on the dyadic tail and is bounded by 2·M_φ; the dyadic tail bound (brick 107) gives the
-- geometric decay. Brick 108 at general integer exponent. powTest_M ((powTest n).M=⟨1,1⟩) private.
#print axioms Square.compactMomentF_natExpR_sub_mellin_bound

-- THE PRE-HILBERT LAYER, brick 115 (Square/ContinuousMomentNatLimit.lean) — THE CONTINUOUS TRANSFORM AT
-- THE INTEGER EXPONENT IS THE INTEGER MELLIN MOMENT: compactMomentGenLim φ n ≈ mellinMoment φ n for
-- every n (compactMomentGenLim_natExpR_eq_mellin). The floor defect at exponent n (brick 114) is within
-- 1/(j+1) of the integer moment after the same reindex as brick 109 (nat_reindex_Qle private), so
-- Rlim_eval_real_rate identifies the a→0 limit with mellinMoment φ n. Closes integer-moment
-- identification beyond s=1: the continuous transform and the discrete moment sequence agree on integers.
#print axioms Square.compactMomentGenLim_natExpR_eq_mellin

-- THE PRE-HILBERT LAYER, brick 116 (Square/ContinuousMomentClampValue.lean) — THE CONTINUOUS TRANSFORM
-- COMPUTES: compactMomentGenLim clampTest n ≈ 1/(n+2) (compactMomentGenLim_clamp_eq). A concrete
-- closed-form evaluation of the abstract a→0 continuous Mellin transform on the clamped identity: at
-- integer exponent n the continuous transform is the integer moment (brick 115), and the integer moment
-- of clampTest obeys the Hausdorff law mellinMoment clampTest n = 1/(n+2) (brick 33). End-to-end
-- verification that the continuous-transform stack produces the correct number.
#print axioms Square.compactMomentGenLim_clamp_eq

-- THE PRE-HILBERT LAYER, brick 117 (Square/ContinuousMomentGenRate.lean) — THE CONTINUOUS TRANSFORM IS
-- THE a→0 LIMIT AT EVERY FLOOR (schedule-independent): |compactMoment φ (1/2^m) s − compactMomentGenLim
-- φ s| ≤ 2·M_φ·(1/2^m) (compactMomentF_dist_lim). Brick 112 defined the transform along ONE reindex
-- schedule; this proves the value is the honest a→0 limit at EVERY floor, uniformly in the reindex —
-- the schedule-independence the transform-as-a-map (linearity, the pairing) requires. Triangulates
-- through the reindexed sequence at depth j=m+k (brick 111 + Rabs_dist_Rlim), Archimedean collapse
-- removes the residual. abs_sub_tri'/le_momRate private.
#print axioms Square.compactMomentF_dist_lim

-- THE PRE-HILBERT LAYER, brick 118 (Square/ContinuousMomentGenLinear.lean) — THE CONTINUOUS TRANSFORM
-- IS ADDITIVE: compactMomentGenLim (φ+ψ) s ≈ compactMomentGenLim φ s + compactMomentGenLim ψ s
-- (compactMomentGenLim_add), the first structural law of the transform pair. At each floor the compact
-- moment is additive (innerI_add_left); the brick-117 schedule-independent rate on φ+ψ, φ, ψ controls
-- the limit, and the reusable Archimedean collapse Req_of_geom_rate (|a−b| ≤ E/2^m ∀m ⟹ a≈b, constant
-- E absorbed by n<2^n) closes it. geom_reindex_Qle/abs_sub_swap'/abs_sub_tri'' private.
#print axioms Square.Req_of_geom_rate
#print axioms Square.compactMomentGenLim_add

-- THE PRE-HILBERT LAYER, brick 119 (Square/ContinuousMomentGenNeg.lean) — THE CONTINUOUS TRANSFORM IS
-- NEGATION-COMPATIBLE: compactMomentGenLim (−φ) s ≈ −compactMomentGenLim φ s (compactMomentGenLim_neg),
-- the second structural law of the transform pair. Mirrors additivity: at each floor innerI_neg_left
-- flips the sign ((−φ).M = φ.M so brick 117 gives the same rate), Req_of_geom_rate passes to the limit.
-- abs_sub_swap2/abs_sub_tri2/abs_sub_neg2 private.
#print axioms Square.compactMomentGenLim_neg

-- THE PRE-HILBERT LAYER, brick 120 (Square/ContinuousMomentGenSub.lean) — THE CONTINUOUS TRANSFORM
-- RESPECTS SUBTRACTION: compactMomentGenLim (φ−ψ) s ≈ compactMomentGenLim φ s − compactMomentGenLim ψ s
-- (compactMomentGenLim_sub), completing the continuous transform as a LINEAR MAP. Immediate composite of
-- additivity (brick 118) and negation (brick 119), since L2Test.sub φ ψ = L2Test.add φ (−ψ).
#print axioms Square.compactMomentGenLim_sub

-- THE PRE-HILBERT LAYER, brick 121 (Square/ContinuousMomentGenScale.lean) — THE CONTINUOUS TRANSFORM
-- IS ℤ⁺-HOMOGENEOUS: compactMomentGenLim (k·φ) s ≈ k·compactMomentGenLim φ s (compactMomentGenLim_natScale),
-- completing the transform as a ℤ-LINEAR map. Induction on k from additivity (brick 118); the seal on
-- natScale is passed as a propositional equation (natScale_succ), never forced through momRate/.M.
-- compactMomentGenLim_zeroL2 (transform of the zero test = 0) is the induction base, via Rlim_zero.
#print axioms Square.compactMomentGenLim_zeroL2
#print axioms Square.compactMomentGenLim_natScale

-- THE PRE-HILBERT LAYER, brick 122 (Square/ContinuousMomentGenFamily.lean) — THE ℤ-LINEAR TRANSFORM
-- COMPUTES ON THE ℤ⁺-CLAMP FAMILY: compactMomentGenLim (k·clampTest) n ≈ k/(n+2)
-- (compactMomentGenLim_natScale_clamp), the concrete payoff of the linearity arc — homogeneity
-- (brick 121) carries the single-test closed form 1/(n+2) (brick 116) across the whole ℤ⁺-orbit.
#print axioms Square.compactMomentGenLim_natScale_clamp

-- THE PRE-HILBERT LAYER, brick 123 (Square/ContinuousMomentGenInjective.lean) — THE CONTINUOUS
-- TRANSFORM SEPARATES POLYNOMIAL TESTS: two compactly-supported polynomial tests whose continuous
-- transforms agree at every integer exponent below their degree are equal on [0,1]
-- (compactMomentGenLim_poly_eq_imp_function_eq). The injectivity half of the transform pair for the
-- continuous object — brick 115's integer-exponent bridge turns transform equality into moment
-- equality, then brick 88's moment separation closes it. Polynomial class only; NOT general determinacy.
#print axioms Square.compactMomentGenLim_poly_eq_imp_function_eq

-- THE BERNSTEIN ARC, sub-brick A (Analysis/RealBinomial.lean) — THE REAL BINOMIAL THEOREM
-- (a+b)ⁿ ≈ Σ_{i=0}^{n} C(n,i)·aⁱ·bⁿ⁻ⁱ (Rbinomial, over RsumN/Rpow), the foundation of the Bernstein
-- approximation arc for general (bounded-Lipschitz) moment determinacy + Mellin inversion. Reproves
-- Binomial.lean's ℚ theorem over the constructive reals (Bernstein needs a real argument x ∈ [0,1]);
-- the real Bernstein term binTermR + its Pascal step binTermR_succ + boundary laws. Reusable plumbing:
-- RsumN_front (finite-sum front-peel), RofNat_add (ℕ→ℝ additive), Rpow_add (xᵐ⁺ⁿ = xᵐ·xⁿ).
#print axioms Analysis.RsumN_front
#print axioms Analysis.RofNat_add
#print axioms Analysis.Rpow_add
#print axioms Analysis.binTermR_top_zero
#print axioms Analysis.binTermR_zero_bot
#print axioms Analysis.binTermR_succ
#print axioms Analysis.Rbinomial

-- THE BERNSTEIN ARC, sub-brick B (Analysis/Bernstein.lean) — THE BERNSTEIN BASIS + PARTITION OF UNITY
-- bernR x n k = C(n,k)·xᵏ·(1−x)ⁿ⁻ᵏ; Σ_{k=0}^n bernR x n k ≈ 1 (bernR_partition), read off the real
-- binomial theorem at (x, 1−x) since x+(1−x)=1 and 1ⁿ=1. The normalization the Bernstein operator's
-- convergence estimates divide by; mean/variance identities follow.
#print axioms Analysis.bernR_partition

-- THE BERNSTEIN ARC, sub-brick C (Analysis/BernsteinMoments.lean) — THE BERNSTEIN MEAN IDENTITY
-- Σ_{k=0}^n k·b_{n,k}(x) = n·x (bernR_mean). The k=0 term drops; each k=j+1 term reindexes by
-- succ_mul_choose ((k+1)C(n+1,k+1)=(n+1)C(n,k), from choose_mul_fct_mul_fct + ℕ-cancellation) to
-- (n·x)·b_{n-1,j}(x), so the sum is n·x·(partition for n-1) = n·x. Minted RofNat_mul (ℕ→ℝ multiplicative).
#print axioms Analysis.succ_mul_choose
#print axioms Analysis.RofNat_mul
#print axioms Analysis.bernR_mean_term
#print axioms Analysis.bernR_mean

-- THE BERNSTEIN ARC, sub-brick D (Analysis/BernsteinMoments.lean) — THE BERNSTEIN SECOND FACTORIAL
-- MOMENT Σ_{k=0}^n k(k-1)·b_{n,k}(x) = n(n-1)·x² (bernR_sq). The k=0,1 terms drop; each k=j+2 term
-- reindexes by dfact_choose ((j+2)(j+1)C(m+2,j+2)=(m+2)(m+1)C(m,j), two succ_mul_choose) to
-- (n(n-1)x²)·b_{n-2,j}(x), so the sum is n(n-1)x²·(partition for n-2). Second moment for the variance.
#print axioms Analysis.dfact_choose
#print axioms Analysis.bernR_sq_term
#print axioms Analysis.bernR_sq

-- THE BERNSTEIN ARC, sub-brick E (Square/BernsteinVariance.lean) — THE BERNSTEIN VARIANCE IDENTITY
-- Σ_{k=0}^n (k-nx)²·b_{n,k}(x) = nx(1-x) (bernR_variance), the estimate the Bernstein convergence
-- divides by (Chebyshev). Expand (k-nx)² (Rsub_sq_expand), split by RsumN linearity into the second
-- factorial moment + mean (bernR_sq + bernR_mean), the partition (bernR_partition), and the cross term,
-- then collapse the (nx)² terms. Minted RofNat_sub (ℕ→ℝ respects truncated subtraction).
#print axioms Square.RofNat_sub
#print axioms Square.bernR_variance

-- THE BERNSTEIN ARC, sub-brick F (Square/BernsteinConverge.lean) — THE FIRST ABSOLUTE CENTRAL MOMENT
-- 2δ·Σ_{k=0}^n |k-nx|·b_{n,k}(x) ≤ δ² + nx(1-x) (bernR_abs_moment), the sqrt-free/split-free heart of
-- Bernstein convergence: the pointwise AM-GM 2δ|t| ≤ δ²+t² (amgm_2delta, from (δ-|t|)²≥0) summed against
-- the nonneg basis (bernR_nonneg, RsumN_le) and closed by the variance + partition. Dodges both the sqrt
-- (Cauchy-Schwarz) and the undecidable near/far split a real x would force.
#print axioms Square.bernR_nonneg
#print axioms Square.amgm_2delta
#print axioms Square.bernR_abs_moment

-- THE BERNSTEIN ARC, sub-brick G (Square/BernsteinDeviation.lean) — THE BERNSTEIN OPERATOR + POINTWISE
-- DEVIATION: |B_n(φ)(x) - φ(x)| ≤ L·Σ_{k=0}^n |k/n - x|·b_{n,k}(x) (bernOp_deviation) — Bernstein's
-- theorem itself. φ(x)=φ(x)·Σb (partition), so B_n(φ)(x)-φ(x)=Σ(φ(k/n)-φ(x))·b; triangle on the sum
-- (RsumN_Rabs_le, basis ≥ 0) + the Lipschitz modulus (L2Test.hlip). bernOp_unfold seals the operator so
-- the free-variable sample point k/n never whnf-blows-up.
#print axioms Square.bernOp_unfold
#print axioms Square.bernOp_deviation

-- THE BERNSTEIN ARC, sub-brick H₁ (Square/BernsteinBasisZero.lean) — THE BERNSTEIN BASIS PAIRS TO ZERO
-- against a moment-null test: ⟨φ, C(n,k)·xᵏ·(1-x)ⁿ⁻ᵏ⟩ = ∫₀¹ φ·b_{n,k} ≈ 0 when every moment of φ
-- vanishes (innerI_bernBasis_zero). The first integration step of the determinacy arc: the real
-- coefficients φ(k/n) of B_n(φ)=Σφ(k/n)b are only outer factors, so the operator integral collapses
-- once each single-basis integral vanishes. No monomial bookkeeping — the Pascal recursion
-- xᵏ(1-x)ᵐ⁺¹ = xᵏ(1-x)ᵐ - xᵏ⁺¹(1-x)ᵐ (clampProd_step_pt), by induction on m via innerI_sub_right +
-- unit-restriction congruence, reduces every basis pairing to the base moment ⟨φ,xᵏ⟩ (innerI_clampProd_zero).
#print axioms Square.clampProd_step_pt
#print axioms Square.innerI_clampProd_zero
#print axioms Square.innerI_bernBasis_zero

-- THE BERNSTEIN ARC, sub-brick H₂ (Square/BernsteinClampMatch.lean) — THE CLAMPED BERNSTEIN BASIS
-- MATCHES THE HONEST ONE ON [0,1]: bernR x n k ≈ C(n,k)·(clampProdTest k (n-k)).f x for 0≤x≤1
-- (bernR_eq_scaled_clampProd). Welds the clamped tests (which pair through the certified integral) to
-- the honest bernR (built from Rpow, unbounded off [0,1]) that Bernstein's deviation bound is stated
-- over. Clean inductions (powTest_f_eq: (powTest k).f x = clamp01(x)ᵏ; powMinusTest_f_eq) + clamp01
-- inertness on [0,1] (clamp01_eq_self, qBandQ_eq_of_band) collapse both to the honest monomials.
#print axioms Square.clamp01_eq_self
#print axioms Square.powTest_f_eq
#print axioms Square.powMinusTest_f_eq
#print axioms Square.clampProdTest_eq_on_unit
#print axioms Square.bernR_eq_scaled_clampProd

-- REAL-SCALAR LINEARITY OF THE CERTIFIED INTEGRAL (Analysis/IntegralRsmul.lean) — the missing real
-- coefficient case of integral linearity: ∫₀¹ (c·f) = c·∫₀¹ f for c : Real (riemannIntegral_Rsmul),
-- the piece the "full linear-algebra API" lacked beyond the rational riemannIntegral_smul. The new
-- ingredient is that a real scalar commutes with the Bishop limit (Rmul_Rlim_of_approx): the gap
-- |lim(c·X) - c·lim X| telescopes through (c·X)_m to (2 + 2·xBound c)/(m+1) via the convergence rate
-- (Rabs_dist_Rlim) and |c| ≤ xBound c (Rabs_le_ofQ_xBound), and the real squeeze (Req_of_Rle_ofQ_all)
-- closes. The Bernstein determinacy arc needs it to pull the real coefficient φ(k/n) out of ∫φ·(c·b).
#print axioms Analysis.Rabs_le_ofQ_xBound
#print axioms Analysis.Rmul_Rlim_of_approx
#print axioms Analysis.riemannIntegral_Rsmul

-- The interval-integral counterpart: ∫_a^{a+w} (c·f) = c·∫_a^{a+w} f for c : Real
-- (new Analysis/IntervalRsmul.lean), the real-scalar mirror of the rational riemannIntegralI_smul —
-- riemannIntegral_Rsmul on the affine-rescaled integrand, then commute c past the width factor. The
-- tool a separable Fubini step (pull φ(x) out of ∫_y, then ∫ψ out of ∫_x) runs through.
#print axioms Analysis.riemannIntegralI_Rsmul

-- THE BERNSTEIN ARC, sub-brick H₃ (Square/ConstScale.lean) — THE CONSTANT TEST + REAL-SCALAR PAIRING
-- LAW: ⟨φ, (constTest c)·ψ⟩ ≈ c·⟨φ, ψ⟩ (innerI_constMul), so ⟨φ, (constTest c)·ψ⟩ ≈ 0 when ⟨φ,ψ⟩ ≈ 0
-- (innerI_constMul_zero). A real scalar cannot scale an L2Test (rational bound), so B_n(φ)=Σ φ(k/n)·b's
-- real coefficient is carried as a constant test (f≡c, bound |c|≤mB) and multiplied in by the algebra.
-- Mirror of innerI_add_left: common-modulus weakening, riemannIntegral_congr moves φ·(c·ψ) to c·(φ·ψ),
-- riemannIntegral_Rsmul pulls c out.
#print axioms Square.innerI_constMul
#print axioms Square.innerI_constMul_zero

-- THE BERNSTEIN ARC, sub-brick H₄ (Square/BernsteinOperatorTest.lean) — THE BERNSTEIN OPERATOR AS A
-- TEST + ITS MOMENT-INTEGRAL. The clamped operator B_n(φ) is realized as an L2Test
-- (bernOpCTest = Σ_k (constTest φ(k/n)·C(n,k))·(clampProdTest k (n-k))) that (a) pairs to zero against a
-- moment-null φ (innerI_bernOpCTest_zero: ⟨φ, B_nφ⟩ ≈ 0 — each summand is a real coeff times a vanishing
-- single-basis integral, finite-additive via innerI_L2sumN_zero) and (b) agrees with the honest bernOp
-- on [0,1] (bernOpCTest_eq_on_unit, via H₂ + assoc). Together: ∫₀¹ φ·B_nφ = 0 plus the handle on
-- ∫₀¹ φ·(φ − B_nφ) the determinacy step needs. L2sumN_f_eq: finite sum of tests evaluates termwise.
#print axioms Square.L2sumN_f_eq
#print axioms Square.innerI_L2sumN_zero
#print axioms Square.bernCoef_bound
#print axioms Square.innerI_bernOpCTest_zero
#print axioms Square.bernOpCTest_eq_on_unit

-- THE BERNSTEIN ARC, sub-brick H₅ (Square/BernsteinDeviationTransfer.lean) — THE DETERMINACY REDUCTION
-- + DEVIATION TRANSFER. reduction: ⟨φ,φ⟩ ≈ ⟨φ, φ − B_nφ⟩ (innerI_self_eq_sub, since ⟨φ,B_nφ⟩≈0 by H₄),
-- the energy equals the pairing with the Bernstein residual. transfer: on [0,1] the residual is bounded
-- by Bernstein's pointwise deviation |φ(x) − bernOpCTest.f x| ≤ L·Σ|k/n−x|·b (bernOpCTest_pointwise_dev),
-- since the operator test agrees with honest bernOp there (H₄) and bernOp obeys the bound (G). Together
-- these turn the moment-integral into a bound on ⟨φ,φ⟩ (next: the vanishing rational bound).
#print axioms Square.innerI_self_eq_sub
#print axioms Square.bernOpCTest_pointwise_dev

-- THE BERNSTEIN ARC, sub-brick H₇ (Square/BernsteinEnergyBound.lean) — THE MULTIPLIED-FORM ENERGY BOUND
-- 2δn·|⟨φ, φ − B_nφ⟩| ≤ M_φ·L·(δ²+n/4), any δ≥0 (bernOp_energy_bound). The residual integrand is bounded
-- pointwise by M_φ·(deviation) (H₅ + φ.hbd), and 2δn·(deviation sum) ≤ δ²+n/4 (H₆); the scalar 2δn is
-- pulled out at the RAW integral level via riemannIntegral_Rsmul (weakened to a common modulus), and the
-- unit-local absolute integral bound (riemannIntegral_abs_le_unit) closes — NO constTest, so the deeply
-- nested operator test is never whnf-forced. Kept multiplied so the reciprocal is deferred to the squeeze.
#print axioms Square.riemannIntegral_abs_le_unit
#print axioms Square.bernOp_energy_bound
-- (energy_from_pointwise is the general two-slot scalar-pairing bound |c·(φ·ψ)|≤B ⟹ c·|⟨φ,ψ⟩|≤B,
-- exposed for the two-function reconstruction energy bound of the Mellin-inversion arc, I₃.)
#print axioms Square.energy_from_pointwise

-- THE BERNSTEIN ARC, sub-brick H₈ (Square/MomentDeterminacy.lean) — GENERAL MOMENT DETERMINACY, the
-- capstone. A bounded-Lipschitz test whose every integer moment vanishes is the zero function on [0,1]:
-- (∀n, ⟨φ,xⁿ⟩≈0) ⟹ ⟨φ,φ⟩≈0 (moment_determinacy) ⟹ ∀x∈[0,1], φ(x)≈0 (moment_determinacy_unit). Closes
-- the general-determinacy question the polynomial class (brick 64) left open. ⟨φ,φ⟩=⟨φ,φ−B_nφ⟩ (H₅),
-- bounded by 2δn·⟨φ,φ⟩ ≤ M_φL(δ²+n/4) (H₇); the schedule δ=k+1, n=(k+1)² divides down to ⟨φ,φ⟩ ≤
-- 5M_φL/(8(k+1)) ≤ (5·M.num·L.num)/(k+1) → Req_of_Rle_ofQ_all forces ⟨φ,φ⟩≈0 (≥0 by innerI_self_nonneg),
-- and brick 79 lifts to the pointwise statement. A genuine constructive Weierstrass/Bernstein theorem.
#print axioms Square.moment_determinacy
#print axioms Square.moment_determinacy_unit
#print axioms Square.moment_injective_unit
-- (Rle_of_Rmul_ofQ_le is the general "divide a weighted bound by the positive weight" lemma,
-- exposed for the reconstruction convergence of the Mellin-inversion arc, I₃b.)
#print axioms Square.Rle_of_Rmul_ofQ_le

-- THE MELLIN-INVERSION ARC, sub-brick I₁ (Square/MomentFiniteDiff.lean) — THE RECONSTRUCTION COEFFICIENTS
-- ARE FINITE DIFFERENCES OF THE MOMENTS: ⟨φ, xᵏ(1-x)ᵐ⟩ = (Δᵐμ)_k (clampProd_integral_eq_momDiff), where
-- (Δᵐμ)_k is the m-th forward difference of the moment sequence (momDiff). The Hausdorff/Bernstein
-- inversion's coefficients are the clampProd integrals; this shows they are computable from the moments
-- alone. Same Pascal recursion as determinacy (clampProd_step_pt = the finite-difference recursion), by
-- induction on m, base ⟨φ,xᵏ⟩=μ_k. No signed binomial coefficients formed.
#print axioms Square.clampProd_integral_eq_momDiff

-- THE MELLIN-INVERSION ARC, sub-brick I₂ (Square/MomentReconSum.lean) — THE OPERATOR PAIRING IS THE
-- RECONSTRUCTION SUM: ⟨φ, B_n(ψ)⟩ = Σ_{k=0}^n ψ(k/n)·C(n,k)·(Δⁿ⁻ᵏμ)_k (innerI_bernOpCTest_eq_reconSum),
-- the reconstruction sum (bernReconSum), whose RHS reads φ only through the finite differences of its
-- moments. Distribute the pairing over the operator's finite sum (innerI_L2sumN, the general companion of
-- innerI_L2sumN_zero), pull each real coefficient out (innerI_constMul, H₃), and rewrite each single-basis
-- integral as a finite difference of moments (clampProd_integral_eq_momDiff, I₁). Algebraic backbone of the
-- weak (pairing) inversion; the convergence ⟨φ, B_n(ψ)⟩ → ⟨φ,ψ⟩ is the next step.
#print axioms Square.innerI_L2sumN
#print axioms Square.innerI_bernOpCTest_eq_reconSum

-- THE MELLIN-INVERSION ARC, sub-brick I₃a (Square/MomentReconEnergy.lean) — THE TWO-FUNCTION
-- RECONSTRUCTION ENERGY BOUND: 2δn·|⟨φ,ψ⟩ − bernReconSum φ ψ n| ≤ M_φ·L_ψ·(δ²+n/4), any δ≥0
-- (bernOp_recon_energy_bound), the multiplied-form bound on the reconstruction error. The error is the
-- residual pairing ⟨φ, ψ − B_n(ψ)⟩ (innerI_resid_eq, via innerI_sub_right + I₂); its integrand is bounded
-- pointwise by M_φ·L_ψ·(deviation) (energy_pt_gen, the general-L pointwise bound, deviation via
-- bernOpCTest_pointwise_dev for ψ), and 2δn·(deviation sum) ≤ δ²+n/4 (H₆); the exposed general
-- energy_from_pointwise (H₇) pulls 2δn out at the raw-integral level. Two-function generalization of
-- bernOp_energy_bound (the φ=ψ, moment-null determinacy case). The limit is the next step (I₃b).
#print axioms Square.innerI_resid_eq
#print axioms Square.bernOp_recon_energy_bound

-- THE MELLIN-INVERSION ARC, sub-brick I₃b (Square/MomentReconConverge.lean) — THE RECONSTRUCTION SUMS
-- CONVERGE TO THE PAIRING (weak inversion capstone): along the schedule n=(k+1)², δ=k+1,
-- |⟨φ,ψ⟩ − bernReconSum φ ψ ((k+1)²)| ≤ (5·M_φ.num·L_ψ.num)/(k+1) (bernReconSum_converges), so
-- ⟨φ,ψ⟩ = lim_k bernReconSum φ ψ ((k+1)²), the right side computed entirely from φ's moment sequence (I₂):
-- the moment transform's pairing action is invertible — the whole functional ψ ↦ ⟨φ,ψ⟩ is recovered from
-- φ's moments alone. Divide the reconstruction energy bound (I₃a) by 2δn=2(k+1)³ (the determinacy schedule
-- and division helper Rle_of_Rmul_ofQ_le); the residual rational inequality factors as in the determinacy
-- capstone (φ.L→ψ.L). Weak (pairing) inversion; NOT pointwise reconstruction, NOT surjectivity onto
-- function space, NOT positivity.
#print axioms Square.bernReconSum_converges

-- THE MELLIN-INVERSION ARC, sub-brick J₁ (Square/MomentDurrmeyer.lean) — THE BERNSTEIN–DURRMEYER OPERATOR
-- IS COMPUTABLE FROM THE MOMENTS: durrOp φ n x = (n+1)·Σ_k b_{n,k}(x)·⟨φ,b_{n,k}⟩ (the positive summability
-- operator built from the integrals ⟨φ,b_{n,k}⟩, vs. B_n's point values), and each Durrmeyer coefficient
-- is a scaled finite difference of moments ⟨φ,b_{n,k}⟩ = C(n,k)·(Δⁿ⁻ᵏμ)_k (innerI_bernBasis_eq_momDiff, via
-- innerI_natScale_right — the general 2nd-slot ℕ-scaling of the pairing — + I₁), so durrOp reads φ only
-- through its moments (durrOp_eq_momData). The candidate for POINTWISE inversion (durrOp φ n x is a function
-- of x, moment-computable, → φ(x)). NOT the normalization, NOT the second-moment estimate, NOT convergence.
#print axioms Square.innerI_natScale_right
#print axioms Square.innerI_bernBasis_eq_momDiff
#print axioms Square.durrOp_eq_momData

-- THE MELLIN-INVERSION ARC, sub-brick J₂ (Square/DurrmeyerMoments.lean) — THE FINITE DIFFERENCES OF THE
-- HILBERT MOMENT SEQUENCE IN CLOSED FORM: momDiff (powTest j) k m = m!·(k+j)!/(k+j+m+1)! (momDiff_powTest).
-- The moment sequence of xʲ is the Hilbert-matrix row 1/(i+j+1) (mellinMoment_powTest), and its forward
-- finite differences telescope to the factorial value (Δᵐ[1/(k+c)] = m!/((k+c)···(k+c+m))). Induction on m,
-- base the moment 1/(k+j+1); the step is a factorial identity ((k+j+m+2)−(k+j+1)=m+1) via ring_uor on
-- explicit integer atoms. The exact-value input to the Durrmeyer pointwise-inversion estimate (with J₁:
-- ∫₀¹ b_{n,k}·tʲ = C(n,k)·momDiff (powTest j) k (n−k)).
#print axioms Square.momDiff_powTest

-- THE MELLIN-INVERSION ARC, sub-brick J₃ (Square/DurrmeyerWeights.lean) — THE DURRMEYER INTEGRALS OF THE
-- MONOMIALS: ⟨xʲ,b_{n,k}⟩ = C(n,k)·(n−k)!·(k+j)!/(n+j+1)! (durrInt_raw, from J₁+J₂), which the factorial
-- identity C(n,k)·k!·(n−k)!=n! collapses to ⟨1,b_{n,k}⟩=n!/(n+1)! (durrInt_zero), ⟨x,b_{n,k}⟩=(k+1)n!/(n+2)!
-- (durrInt_one), ⟨x²,b_{n,k}⟩=(k+1)(k+2)n!/(n+3)! (durrInt_two). The per-k weights the Durrmeyer moment sums
-- (M_n⁽ʲ⁾ and the second central moment T_n) consume. Factorial denominators ride as opaque atoms; the
-- fct(k+j) numerators expand by fct_succ and the choose_mul_fct identity closes via ring_uor on ℤ atoms.
#print axioms Square.durrInt_raw
#print axioms Square.durrInt_zero
#print axioms Square.durrInt_one
#print axioms Square.durrInt_two

-- THE MELLIN-INVERSION ARC, sub-brick J₄ (Square/DurrmeyerMomentSum.lean) — THE DURRMEYER OPERATOR
-- PRESERVES THE CONSTANT 1 (M_n⁽⁰⁾ = 1): durrOp 1 n x = 1 (durrOp_powTest_zero). Each weight is the
-- constant ⟨1,b_{n,k}⟩ = n!/(n+1)! (J₃); pull it out of the sum (RsumN_mul_const), collapse Σ_k b_{n,k}(x)=1
-- (bernR_partition, partition of unity), and (n+1)·n!/(n+1)!=1. This is the normalization ∫₀¹ K_n(x,t)dt=1 of
-- the Durrmeyer kernel (a genuine averaging operator). Companions M_n⁽¹⁾ = (nx+1)/(n+2)
-- (durrOp_powTest_one) and M_n⁽²⁾ = (n(n−1)x²+4nx+2)/((n+2)(n+3)) (durrOp_powTest_two) collapse the k-sums
-- against the raw Bernstein moments Σ b_{n,k}(k+1)=nx+1 (bernR_shift1) and Σ b_{n,k}(k+1)(k+2)=n(n−1)x²+4nx+2
-- (bernR_shift2, via the Nat identity (k+1)(k+2)=k(k−1)+4k+2 feeding bernR_sq). The three moments give the
-- second central moment T_n = M_n⁽²⁾ − 2x·M_n⁽¹⁾ + x² that drives durrOp φ n x → φ(x). NOT T_n, NOT convergence.
#print axioms Square.bernR_shift1
#print axioms Square.bernR_shift2
#print axioms Square.durrOp_powTest_zero
#print axioms Square.durrOp_powTest_one
#print axioms Square.durrOp_powTest_two

-- THE MELLIN-INVERSION ARC, sub-brick J₅b (Square/DurrmeyerLinear.lean) — LINEARITY OF THE DURRMEYER
-- OPERATOR: durrOp(φ±ψ) n x = durrOp φ n x ± durrOp ψ n x (durrOp_add, durrOp_sub). Termwise first-slot
-- pairing linearity (innerI_add_left/innerI_sub_left) + weight distribution (Rmul_distrib/Rmul_sub_distrib),
-- the finite sum splits (RsumN_Radd/RsumN_Rsub), the (n+1) scalar pulls back through. The algebraic
-- housekeeping the pointwise-convergence capstone needs to split durrOp φ n x − φ(x) test-by-test.
#print axioms Square.durrOp_add
#print axioms Square.durrOp_sub

-- THE MELLIN-INVERSION ARC, sub-brick J₅c (Square/DurrmeyerConst.lean) — THE DURRMEYER OPERATOR REPRODUCES
-- CONSTANTS + THE DEVIATION-AS-IMAGE: durrOp(constTest c) n x = c (durrOp_constTest, the M_n⁽⁰⁾-scaling: the
-- constant rides through ⟨constTest c,b⟩=c·⟨1,b⟩ via innerI_symm/innerI_right_congr_on_unit/innerI_constMul,
-- then c·durrOp(powTest 0)=c·1); hence durrOp φ n x − φ(x) = durrOp(φ − φ(x)·1) n x (durrOp_dev_eq, via
-- durrOp_sub J₅b), so the pointwise deviation is the Durrmeyer image of the residual ψ=φ−φ(x)·1 (Lipschitz-L,
-- ψ(x)=0, |ψ(t)|≤L|t−x|) — the object the convergence estimate consumes.
#print axioms Square.durrOp_constTest
#print axioms Square.durrOp_dev_eq

-- THE MELLIN-INVERSION ARC, sub-brick J₅d-crux (Square/IntegralMono.lean) — POINTWISE-DOMINATION
-- MONOTONICITY OF THE L² PAIRING: |⟨ψ,χ⟩| ≤ ⟨g,χ⟩ when |ψ|≤g and χ≥0 on [0,1] (innerI_abs_le_mono).
-- Both integrands weakened to the common modulus L=l2L ψ χ + l2L g χ (lip_weaken + certif_irrel, the
-- energy_from_pointwise pattern), then riemannIntegral_le_unit on the pointwise dominations ψ·χ≤|ψ|·χ≤g·χ
-- (positive) and −g·χ≤−|ψ|·χ≤ψ·χ (negative, via innerI_neg_left), combined by Rabs_le_of_both. The
-- integral-monotonicity engine the Durrmeyer pointwise-convergence estimate runs the residual bound through.
#print axioms Square.innerI_abs_le_mono

-- THE MELLIN-INVERSION ARC, sub-brick J₅a (Square/DurrmeyerCentral.lean) — THE DURRMEYER SECOND CENTRAL
-- MOMENT BOUND: T_n(x) = durrOp(x²) − 2x·durrOp(x) + x² ≤ 1/(n+2) on [0,1] (durrOp_central2_le, written for
-- n=p+3 to kill Nat subtraction: ≤ 1/(p+5)). The exact identity T_n·(n+2)(n+3) = 2(n−3)x(1−x)+2 (cleared
-- from the moment closed forms M⁽¹⁾,M⁽²⁾ via distribute+regroup+ring_uor), then quarter_bound (x(1−x)≤1/4)
-- gives 2p·x(1−x)+2 ≤ p+6, and Rle_of_Rmul_ofQ_le divides by the positive weight. The vanishing kernel
-- variance ∫(t−x)²K_n(x,t)dt → 0 that drives the Durrmeyer pointwise convergence durrOp φ n x → φ(x).
#print axioms Square.durrOp_central2_le

-- THE MELLIN-INVERSION ARC, sub-brick J₅d-final (Square/DurrmeyerConverge.lean) — STRONG POINTWISE MELLIN
-- INVERSION: the Bernstein–Durrmeyer operator converges to the test pointwise on [0,1]. The multiplied-form
-- deviation bound 2δ·|durrOp φ n x − φ(x)| ≤ φ.L·(δ² + T_n(x)) (durrOp_dev_bound), folding in the T_n bound
-- (J₅a) → 2δ·|durrOp φ (p+3) x − φ(x)| ≤ φ.L·(δ²+1/(p+5)) (durrOp_dev_bound_le), and the LIMIT along the
-- schedule n=(k+3)²−2, δ=1/(k+3): |durrOp φ ((k+3)²−2) x − φ(x)| ≤ φ.L/(k+3) → 0 (durrOp_converges).
-- Assembly: durrOp φ − φ(x) = durrOp(residual ψ=φ−φ(x)·1) (J₅c durrOp_dev_eq); the rational multiple 2δ·ψ is
-- dominated on [0,1] by G=φ.L·(δ²+(·−x)²) via amgm_2delta + φ.hlip; durrOp_abs_le_dom transports domination
-- through innerI_abs_le_mono (J₅d-crux) + bernBasisTest_f_nonneg + bernR_nonneg; durrOp_scalar
-- (durrOp((constTest s)·h)=s·durrOp(h)) + durrOp_add/durrOp_constTest compute durrOp G = φ.L·(δ²+T_n) with
-- the squared deviation matched to the operator monomials pointwise (sqdev_eq_mono); the squeeze divides by
-- 2δ (Rle_of_Rmul_ofQ_le). Weak inversion (I₃b) + this strong inversion close the transform-pair
-- reconstruction question on the general bounded-Lipschitz class. NOT the transform pair's surjectivity onto
-- function space; step 4 (band-coupling positivity) = RH; crux fields stay none.
#print axioms Square.durrOp_scalar
#print axioms Square.bernBasisTest_f_nonneg
#print axioms Square.durrOp_abs_le_dom
#print axioms Square.durrOp_dev_bound
#print axioms Square.durrOp_dev_bound_le
#print axioms Square.durrOp_converges

-- THE MELLIN-INVERSION ARC, sub-brick K1 (Square/DurrmeyerTendsTo.lean) — THE DURRMEYER LIMIT AS A
-- PACKAGED RTendsTo OBJECT: RTendsTo (fun m => durrOp φ (Kₘ²−2) x) (φ.f x) with Kₘ=(φ.L.num.toNat+1)(m+1)+3
-- (durrOp_tendsTo), the reindexed Durrmeyer sequence converging to φ(x) in the codebase's canonical limit
-- predicate (Bishop 2/(k+1)+2/(n+1) modulus). Reindex absorbs φ.L: the explicit rate φ.L/(k+3) at k=Kₘ−3
-- becomes ≤ 1/(m+1) ≤ 2/(m+1) (durrRate, pure-ℤ Int.mul_le_mul chain — omega can't, the bound is nonlinear);
-- push the single real bound to the .seq level both directions via seq_diff_le + Qabs_le_of_both
-- (tendsTo_of_rate, reusable). Upgrades the explicit-rate durrOp_converges (J₅d-final) to a first-class limit
-- object — the strong pointwise Mellin inversion delivered as a genuine RTendsTo limit. NOT surjectivity onto
-- function space; step 4 (band-coupling positivity) = RH; crux fields stay none.
#print axioms Square.durrOp_tendsTo

-- THE MELLIN-INVERSION FRONT (Square/MomentInversionRaw.lean) — RECONSTRUCTION FROM MOMENT DATA ALONE:
-- durrOpMom μ n x = (n+1)Σ_k b_{n,k}(x)·C(n,k)·(Δⁿ⁻ᵏμ)_k, the Bernstein–Durrmeyer reconstruction as an
-- operator on a RAW moment sequence μ:Nat→Real (momDiffRaw = the Pascal recursion on μ directly). It reads
-- only the moments (durrOpMom_eq_durrOp: durrOpMom (mellinMoment φ) = durrOp φ, via durrOp_eq_momData +
-- momDiff_eq_raw) and reconstructs the test from its moment sequence at the certified rate
-- |durrOpMom (mellinMoment φ) ((k+3)²−2) x − φ(x)| ≤ φ.L/(k+3) on [0,1] (durrOpMom_converges, transporting
-- durrOp_converges). So a bounded-Lipschitz test is recovered FROM ITS MOMENTS ALONE — the transform pair's
-- inversion stated purely on the moment data. NOT the Hausdorff characterization of which raw sequences are
-- moment sequences, NOT a completed L² space; step 4 (band-coupling positivity) = RH; crux fields stay none.
-- durrOpMom_tendsTo packages that convergence as a first-class RTendsTo limit object (the moment-side
-- companion of durrOp_tendsTo): the reindex k:=(φ.L.num.toNat+1)(m+1) turns φ.L/(k+3) into ≤1/(m+1).
#print axioms Square.momDiff_eq_raw
#print axioms Square.momDiffRaw_congr
#print axioms Square.durrOpMom_congr
#print axioms Square.durrOpMom_eq_durrOp
#print axioms Square.durrOpMom_converges
#print axioms Square.durrOpMom_tendsTo

-- THE COMPLETION AXIS (Square/L2ElementSpace.lean) — THE COMPLETED L² SPACE, WITH LIMIT MEMBERS: the
-- L²-Cauchy sequence of tests, packaged as a first-class limit member `L2Elt {seq, cauchy}` (L2Complete gave
-- pairing VALUES but "no limit member"). The extended pairing is a method (L2Elt.pairing = pairingIU), the
-- limit moment sequence is L2Elt.moment, every test embeds faithfully (L2Elt.of, constant sequence;
-- L2Elt_of_pairing = innerI φ ψ), the sequence converges weakly to its limit member (L2Elt_converges, rate
-- 2/(j+1)), and members are equal iff they pair identically (L2Elt.eq, a genuine equivalence — refl/symm/trans).
-- For an embedded test the loop closes: durrOpMom (L2Elt.of φ).moment recovers φ (L2Elt_of_reconstruct). A
-- Bishop-style setoid completion, NOT a Quotient (the Real pairing is only Req-well-defined, so Quotient.liftOn
-- cannot carry it). NOT a norm-limit function (L² conv ≠ pointwise), NOT reconstruction of an arbitrary
-- (non-Lipschitz) L² element, NOT positivity. Step 4 (band-coupling positivity) = RH; crux fields stay none.
#print axioms Square.L2Elt_of_pairing
#print axioms Square.L2Elt_of_moment
#print axioms Square.L2Elt_converges
#print axioms Square.L2Elt_of_reconstruct
#print axioms Square.L2Elt_eq_refl
#print axioms Square.L2Elt_eq_symm
#print axioms Square.L2Elt_eq_trans

-- THE BERNSTEIN ARC, sub-brick H₆ (Square/BernsteinDevBound.lean) — THE MULTIPLIED-FORM DEVIATION BOUND
-- 2δn·Σ_k |k/n − x|·b_{n,k}(x) ≤ δ² + n/4 on [0,1] (bernOp_devsum_bound). Bernstein's central-moment bound
-- (F) uses |k−nx|, the operator deviation (G) uses |k/n−x|; they differ by n. devsum_rescale rescales
-- (n·devsum = central-moment sum), bernR_abs_moment applies, and x(1−x)≤1/4 (quarter_bound, from
-- (x−½)²≥0 via Rsub_sq_expand + a structural additive rearrangement — ring_uor blows on the multi-fraction
-- Qeq) clamps. Kept in multiplied form so the reciprocal 1/(2δn) is only formed at the concrete squeeze schedule.
#print axioms Square.quarter_bound
#print axioms Square.devsum_rescale
#print axioms Square.bernOp_devsum_bound

-- THE BERNSTEIN ARC, sub-brick L₁ (Square/BernsteinUniform.lean) — UNIFORM (WEIERSTRASS) CONVERGENCE OF
-- THE OPERATOR-AS-TEST: on [0,1], |φ(x) − (bernOpCTest φ ((k+1)²) …).f x| ≤ 5·φ.L/(8(k+1)), a rate
-- INDEPENDENT of x (bernOp_uniform_converges). Combine the pointwise deviation transfer (H₅,
-- bernOpCTest_pointwise_dev) with the AM-GM deviation-sum bound (H₆, bernOp_devsum_bound) at δ=k+1,
-- n=(k+1)²: the deviation sum is ≤ (5/4)(k+1)²/(2(k+1)³) = 5/(8(k+1)) (divided out by Rle_of_Rmul_ofQ_le),
-- and scaling by φ.L gives the uniform rate. The constructive Weierstrass theorem for the bounded-Lipschitz
-- class; the approximation companion of moment determinacy. NOT L² density (next sub-brick), NOT surjectivity
-- onto function space, NOT positivity; step 4 (band-coupling positivity) = RH; crux fields stay none.
#print axioms Square.bernOp_uniform_converges

-- THE BERNSTEIN ARC, sub-brick L₂ (Square/BernsteinL2Density.lean) — L² DENSITY OF THE BERNSTEIN
-- POLYNOMIALS: the energy of the Bernstein residual vanishes at a rational rate,
-- ‖φ − bernOpCTest φ ((k+1)²) …‖²_{L²[0,1]} = ⟨φ−B_nφ, φ−B_nφ⟩ ≤ (5·φ.L/(8(k+1)))² (bernOp_L2_converges),
-- so the polynomials are dense in L²[0,1] (residual → 0 in energy). The reusable innerI_self_le_of_bound
-- turns a pointwise sup bound |g(x)| ≤ B on [0,1] into ⟨g,g⟩ = ∫₀¹ g² ≤ B² (unit-local monotonicity of the
-- certified integral against the constant B²), applied to the residual g = φ − bernOpCTest with the uniform
-- bound from L₁. The approximation half of the completed function space — complementary to L2Complete (which
-- extends the pairing along L²-Cauchy sequences but builds no approximating family) and to moment determinacy
-- (the injectivity half). NOT a completed L² space of functions (no limit member, no inversion of an arbitrary
-- L² element), NOT surjectivity onto function space, NOT positivity; step 4 (band-coupling positivity) = RH;
-- crux fields stay none.
#print axioms Square.innerI_self_le_of_bound
#print axioms Square.bernOp_L2_converges

-- THE BERNSTEIN ARC, sub-brick L₃ (Square/BernsteinL2Limit.lean) — THE L² DENSITY LIMIT, PACKAGED:
-- RTendsTo (fun m => ⟨φ − bernOpCTest φ ((Kₘ+1)²) …, φ − …⟩) 0 with Kₘ=(φ.L.num.toNat+1)(m+1)
-- (bernOp_L2_tendsTo) — the Bernstein polynomials converge to φ in the L²[0,1] norm as a first-class
-- RTendsTo limit (Bishop 2/(m+1)+2/(n+1) modulus). The reindex Kₘ turns the L₂ rate (5φ.L/(8(Kₘ+1)))²
-- into ≤ 1/(m+1) (energy_reindex_le — the squared denominator has one factor of Kₘ+1 to spare over the
-- linear numerator 25·φ.L.num²; the nonlinear Int chain is explicit Int.mul_le_mul, omega can't); the
-- energy is ≥ 0 so |energy−0| = energy and the one-sided rate suffices; rate_to_seq (the L=0 instance of
-- K1's rate⟹RTendsTo packaging) closes. The L₂ density result delivered as a genuine limit object — the
-- packaged-limit companion of the durrOp strong-inversion limit (K1). NOT a completed L² space of
-- functions, NOT surjectivity onto function space, NOT positivity; step 4 (band-coupling positivity) = RH;
-- crux fields stay none.
#print axioms Square.bernOp_L2_tendsTo

-- THE CO-SUPPORT OBJECT, sub-brick M₁ (Square/CoSupportTrivial.lean) — THE FILTRATION INTERSECTION IS
-- TRIVIAL: (∀ K, φ ∈ HatVanishes·K) ⟹ φ ≈ 0 on [0,1] (hatVanishes_all_imp_zero), i.e. ⋂_K HatVanishes·K
-- = {0} — a unit-supported test orthogonal to EVERY monomial xⁿ is zero on [0,1]. The monomial system is
-- total (the dual of L² density bernOp_L2_converges: polynomials dense ⟺ nothing nonzero orthogonal to all
-- of them). Weld: each level unfolds via hatVanishes_iff_orthogonal to ⟨φ,xⁿ⟩≈0 for n<K; at K=i+1 every
-- moment mellinMoment φ i = innerI φ (powTest i) (defeq) vanishes, and moment_determinacy_unit (the completed
-- Bernstein arc) closes. A determinacy corollary about the co-support filtration; NOT a completed L² space,
-- NOT surjectivity, NOT positivity; step 4 (band-coupling positivity) = RH; crux fields stay none.
#print axioms Square.hatVanishes_all_imp_zero

-- CO-SUPPORT DEPTH-EXISTENCE, sub-brick N₁ (Square/QSumList.lean) — RATIONAL SUMS OVER A VARIABLE LIST:
-- qsumL f vars = Σ_{i ∈ vars} f i (a List-indexed rational sum) with the linear-algebra laws qsumL_add /
-- qsumL_neg / qsumL_smul / qsumL_congr / qsumL_zero and the pivot split qsumL_erase (Σ_vars f ≈ f p +
-- Σ_{vars.erase p} f for p ∈ vars — the row operation Gaussian elimination performs). List indexing (not a
-- Nat range) makes "eliminate variable p" reindexing-free. Substrate for the over-determined-homogeneous-
-- system-has-a-nonzero-solution lemma that gives co-support members at every depth. Pure finite rational
-- arithmetic; no members/co-support/positivity yet. Step 4 (band-coupling positivity) = RH; crux fields none.
#print axioms Square.qsumL_den
#print axioms Square.qsumL_congr
#print axioms Square.qsumL_zero
#print axioms Square.qsumL_add
#print axioms Square.qsumL_neg
#print axioms Square.qsumL_smul
#print axioms Square.qsumL_erase

-- CO-SUPPORT DEPTH-EXISTENCE, sub-brick N₂ (Square/QLinearKernel.lean) — AN OVER-DETERMINED HOMOGENEOUS
-- ℚ-SYSTEM HAS A NONZERO SOLUTION: #equations < #variables ⟹ ∃ nonzero c with every Σ_{i∈vars}(row i)·(c i)≈0
-- (qkernel_exists), by division-free Gaussian elimination (recursion on the equation list; scale row e to
-- e' = (e₀ p)·e − (e p)·e₀ to kill the pivot column, recurse on vars.erase p, lift by scaling off-pivot). This
-- is the "hypergeometric identity the layer cannot reach", reached by row reduction. Helpers: ball_or_exists_not
-- (decidable pivot search), redEqRow (the scaled row op), and the CHOICE-FREE erase_len_succ / not_mem_erase_nodup
-- (List.length_erase_of_mem and List.Nodup.not_mem_erase both pull Classical.choice in core → reproved by
-- induction), plus qsumL_congr_mem/qsumL_zero_mem and the Q helpers Qeq_zero_iff/Qmul_ne_zero/Qmul_zero_left/
-- Qneg_congr/Qeq_of_Qsub_zero. Pure finite rational linear algebra; no members/positivity. Step 4 = RH; crux none.
#print axioms Square.qsumL_congr_mem
#print axioms Square.qsumL_zero_mem
#print axioms Square.Qeq_zero_iff
#print axioms Square.Qmul_ne_zero
#print axioms Square.Qmul_zero_left
#print axioms Square.ball_or_exists_not
#print axioms Square.qkernel_exists

-- CO-SUPPORT DEPTH-EXISTENCE, sub-brick N₃ (Square/QPolyMember.lean) — THE ℚ-COEFFICIENT POLYNOMIAL MEMBER:
-- qPolyTest c hc d = Σ_{i<d} (constTest (ofQ c_i))·(powTest i), a bounded-Lipschitz test whose Mellin moment
-- is the rational Hilbert contraction of c: mellinMoment (qPolyTest c hc d) n = ofQ (Σ_{i∈range d} c_i/(i+n+1))
-- (mellinMoment_qPolyTest, via innerI_symm + innerI_L2sumN + innerI_constMul + innerI_powTest_hilbert), and its
-- unit-support is Σc_i = 0 (qPolyTest_supp). So a rational kernel vector drops straight into hatVanishes_of_moments
-- (qPolyTest_hatVanishes) with NO denominator clearing to Nat coefficients. Bridges: qsumL_append and
-- RsumN_ofQ_qsumL_range (real RsumN over 0..d ↔ rational qsumL over List.range d), innerI_powTest_qMono (the
-- rational-scaled monomial's pairing). Member constructor for the co-support existence theorem; the nonzero
-- coefficient vector comes from the kernel lemma (N₂). Step 4 (band-coupling positivity) = RH; crux fields none.
#print axioms Square.qsumL_append
#print axioms Square.RsumN_ofQ_qsumL_range
#print axioms Square.innerI_powTest_qMono
#print axioms Square.mellinMoment_qPolyTest
#print axioms Square.qPolyTest_supp
#print axioms Square.qPolyTest_hatVanishes

-- CO-SUPPORT DEPTH-EXISTENCE, sub-brick N₄ (Square/QCoSupportExists.lean) — CO-SUPPORT MEMBERS EXIST AT EVERY
-- DEPTH: for every K there is a rational coefficient vector c with a nonzero coordinate whose ℚ-coefficient
-- polynomial test qPolyTest c hc (K+2) is unit-supported and lies in HatVanishes·K (coSupport_member_exists).
-- The Hilbert system (support row Σcᵢ + moment rows Σcᵢ/(i+n+1), n<K) has K+1 equations in K+2 unknowns, so
-- qkernel_exists (N₂) supplies the vector and qPolyTest_hatVanishes (N₃) certifies the member — the general-K
-- inhabitation the layer had only for K=1..7. CHOICE-FREE nodup_range_cf / nodup_map_succ replace the classical
-- List.nodup_range (core pulls Classical.choice). HONEST: the member is nonzero as a VECTOR (∃v, cᵥ≉0); that it
-- is nonzero as a FUNCTION on [0,1] (monomials linearly independent there) is the factor-theorem apartness, a
-- separate brick NOT proved here. NOT positivity. Step 4 (band-coupling positivity) = RH; crux fields stay none.
#print axioms Square.hilbertEqns_den
#print axioms Square.hilbertEqns_length
#print axioms Square.nodup_map_succ
#print axioms Square.nodup_range_cf
#print axioms Square.coSupport_member_exists

-- CO-SUPPORT DEPTH-EXISTENCE, sub-brick N₅ (Square/QPolyApart.lean) — THE FACTOR-THEOREM APARTNESS: the
-- depth-K co-support member is nonzero as a FUNCTION on [0,1], not just as a coefficient vector
-- (coSupport_member_apart: ∀K, ∃ member ∈ HatVanishes·K with ∃ x∈[0,1], member.f x ≉ 0). Route (large-M
-- evaluation, no synthetic division): the member's value at a rational r∈[0,1] is ofQ(qPolyEval c r d)
-- (qPolyTest_eval_ofQ, via powTest_f_ofQ recursion powTest i .f (ofQ r)=ofQ(rⁱ) + clamp01_ofQ + RsumN_ofQ_
-- qsumL_range); a nonzero coefficient vector gives an explicit M≥1 with qPolyEval c (1/M) d ≉ 0
-- (poly_nonzero_evalP: bottom-Horner evalP, |evalP|≤Σ|cᵢ| majorant, c₀-domination at M=|B|.num.toNat·(c 0).den+1);
-- evaluating the member at 1/M∈[0,1] gives the apartness witness (Qeq_of_ofQ_eq_zero via Qarch_gen bridges
-- ofQ q≈0 ⟹ Qeq q ⟨0,1⟩). UPGRADES coSupport_member_exists from a nonzero VECTOR to a nonzero FUNCTION — the
-- co-support object is now inhabited beyond zero at EVERY depth. NOT positivity; step 4 = RH; crux fields none.
#print axioms Square.Qpow_den
#print axioms Square.qPolyEval_den
#print axioms Square.powTest_f_ofQ
#print axioms Square.qMonoTest_f_ofQ
#print axioms Square.qPolyTest_eval_ofQ
#print axioms Square.evalP_den
#print axioms Square.sumAbs_den
#print axioms Square.qsumL_map_succ
#print axioms Square.qPolyEval_eq_evalP
#print axioms Square.evalP_abs_le_sumAbs
#print axioms Square.sumAbs_num_nonneg
#print axioms Square.evalP_abs_c0_le
#print axioms Square.poly_nonzero_evalP
#print axioms Square.Qeq_of_ofQ_eq_zero
#print axioms Square.coSupport_member_apart

-- The analytic foundation for general split-point additivity (new Square/IntervalSplitAt.lean): the
-- Riemann-SUM machinery the arbitrary-rational interval split needs. RsumN_flatten (block flatten);
-- riemannSum_multiple_refine (block refinement bound |R_{cP}-R_P|<=L/P, general integer factor);
-- riemannSum_conv_dist (the general Riemann-sum convergence rate |int - R_N|<=L/(N+1) for EVERY N, not
-- just dyadic 2^m -- the key result exhaustion-independence rests on); riemannSum_split_at_gen (the
-- exact finite split at a general node t0=(a+1)/(a+b+2), generalizing riemannSum_halves). Foundation
-- for the coming riemannIntegralI_split_at. No improper integral, no dilation, no positivity, no crux.
#print axioms Square.RsumN_flatten
#print axioms Square.riemannSum_multiple_refine
#print axioms Square.riemannSum_conv_dist
#print axioms Square.riemannSum_split_at_gen

-- The interval-level general split-point additivity (new Square/IntervalSplitAtCap.lean): the capstone.
-- int over [a,a+w] f = int over [a,a+w1] f + int over [a+w1,a+w] f for arbitrary rational 0<w1<=w.
-- Assembled as the Archimedean limit of the committed riemannSum_split_at_gen closed by
-- riemannSum_conv_dist: the UNIT split (riemannIntegral_split_at_unit) is the Rlim over resolution
-- (k+1)*q of the exact finite split at node t0=p/q (block sizes A=(k+1)p-1, B=(k+1)(q-p)-1), then the
-- interval law follows by affineMap_comp. Foundation for exhaustion-independence. No dilation, no crux.
#print axioms Square.riemannIntegral_split_at_unit
#print axioms Square.riemannIntegralI_split_at

-- The window integral is Lipschitz in its upper limit (new Square/IntervalUpperLip.lean):
-- riemannIntegralI_upper_lip — |∫_0^q φ − ∫_0^{q'} φ| ≤ (q−q')·φ.M for rational q ≥ q' > 0, via
-- riemannIntegralI_split_at (∫_0^q = ∫_0^{q'} + ∫_{q'}^q, difference = the tail) + the window bound
-- riemannIntegralI_abs_le_window. The continuity of the partial integral q ↦ ∫_0^q φ in the upper
-- limit — the primitive that lets the REAL-upper-limit window integral ∫_0^c φ be built as the Rlim of
-- rational partials (the wall-breaker for evaluating mellinMoment(dilateTestR c f) at real scale). No
-- real-window integral yet, no covariance, no factorization, no crux.
#print axioms Square.riemannIntegralI_upper_lip

-- The real-upper-limit window integral (new Square/RealWindowIntegral.lean): riwI φ qk … =
-- Rlim (fun k => ∫_0^{qk k} φ) — the partial integral ∫_0^c φ to a REAL upper limit c, along a supplied
-- positive fast rational sequence qk → c. riwSeq_RReg: the partials are regular, via RReg_of_real_bound
-- fed the upper-limit Lipschitz bound |∫_0^{qk j} − ∫_0^{qk k}| ≤ φ.M·|qk j − qk k| ≤ 1/(j+1)+1/(k+1)
-- (both orderings by an ordering case split; last step = the supplied fast condition hqk_fast, a fast
-- diagonal qk=c.seq(idx k) discharges it as in covComb_hbound_of_fast). The wall-breaker object for
-- evaluating mellinMoment(dilateTestR c f) n = c^{-(n+1)}·∫_0^c (f·xⁿ) at real scale. NO covariance yet,
-- NO factorization, NO crux.
#print axioms Square.riwSeq_RReg

-- The real-window partial evaluates as a scaled moment (new Square/RiwSeqMoment.lean):
-- riwSeq_term_eq_moment — ∫_0^s (f·powBandGen_{[0,B]}) = s^(n+1)·mellinMoment(dilate_s f) n for rational
-- s>0 with s+1≤B (window under the fixed band). Three known-lemma steps onto the built mellinMoment_dilate:
-- riemannIntegralI_congr_Q (bridge window [⟨0,1⟩,s] → [mul s ⟨0,1⟩, mul s ⟨1,1⟩], Qeq windows) then
-- riemannIntegralI_congr_unit_mod (swap fixed band [0,B] → [0,s+1] on [0,s]; both weights = Rpow p n via
-- powBandGen_eq_Rpow_on) then mellinMoment_dilate. Evaluates each riwSeq term at the FIXED-band twist weight;
-- passing the Rlim gives the real-scale moment covariance mellinMoment(dilateTestR c f)=c^{-(n+1)}·riwI. No
-- Rlim interchange yet, no factorization, no crux.
#print axioms Square.riwSeq_term_eq_moment

-- The moment covariance combination is scale-Lipschitz (new Square/MomentCovLip.lean):
-- moment_covComb_scale_lip — H(c)=cⁿ⁺¹·mellinMoment(dilateTestR c f) n is Lipschitz in the real scale c:
-- |H(c)−H(c')| ≤ Sⁿ⁺¹·(f.L·(powTest n).M)·|c−c'| + (f.M/(n+1))·((n+1)Sⁿ)·|c−c'|. The MOMENT analog of
-- covComb_scale_split, but NO tail (clean single Lipschitz). mixed-product split cⁿ⁺¹·(M_c−M_c') +
-- (cⁿ⁺¹−c'ⁿ⁺¹)·M_c': first = Sⁿ⁺¹ × moment scale-continuity (window_moment_scale_lipschitz, bridged
-- [0,1]-interval→mellinMoment by riemannIntegralI_unit), second = moment bound (mellinMoment_abs_le,
-- f.M/(n+1) scale-independent) × Rpow_base_lip. The continuity for the Rlim-interchange capstone
-- (riwI = c^{n+1}·mellinMoment(dilateTestR c f)). No Rlim interchange yet, no factorization, no crux.
#print axioms Square.moment_covComb_scale_lip

-- The real-window integral is the limit of its partials (new Square/RiwILimit.lean): riwI_eq_of_bound —
-- if the rational partials riwSeq φ' qk … (m k) approach a target L fast enough (|riwSeq(m k) − L| ≤
-- C₀/(k+1) along a sub-index m with k ≤ m k), then riwI φ' qk … = L. Pure completeness: riwI = Rlim(riwSeq),
-- so |riwI − riwSeq(m k)| ≤ 2/(m k+1) ≤ 2/(k+1) (Rabs_dist_Rlim + k ≤ m k); triangle with hbound gives
-- |riwI − L| ≤ (2+C₀)/(k+1), a null family, closed by Req_of_real_null_family. The Rlim-interchange capstone:
-- for L = c^{n+1}·mellinMoment(dilateTestR c f) n, hbound discharges from riwSeq_term_eq_moment +
-- mellinMoment_bridge/Rpow_ofQ + moment_covComb_scale_lip along a fast diagonal, giving the real-scale moment
-- covariance. hbound is an explicit dischargeable input (as in mellinHat_dilate_covariance_real). No
-- factorization, no crux.
#print axioms Square.riwI_eq_of_bound

-- The real-scale moment covariance (new Square/RiwIMomentCovariance.lean): riwI_moment_covariance —
-- riwI (f·powBandGen_{[0,B]}) qk … = cⁿ⁺¹·mellinMoment(dilateTestR c f) n along a fast positive rational
-- diagonal qk → c. Discharges the hbound input of riwI_eq_of_bound, mirroring covComb_hbound_of_fast: per
-- approximant qk(m k), riwSeq(m k) = (qk m k)ⁿ⁺¹·mellinMoment(dilate_{qk m k} f) (riwSeq_term_eq_moment) ≈
-- H(ofQ qk m k) (Rpow_ofQ + mellinMoment_bridge, dilateTest→dilateTestR), and |H(qk m k)−H(c)| ≤ Lip·|qk m k −c|
-- (moment_covComb_scale_lip) driven under 2/(k+1) by Qmul_recip_le with the momCovIdx rational schedule. The one
-- rate input hconv is FREE for qk(m k)=c.seq(momCovIdx…) via Rabs_sub_seq_le at positive c; hqk_B/hqk_mS are band/ball
-- slack. Pure Req — NO positivity, NO factorization, NO half-line assembly, NO step-4 positivity (RH). Crux none.
#print axioms Square.riwI_moment_covariance

-- The inner integral evaluated: cⁿ⁺¹·dilMellinF = riwI (new Square/DilMellinFRiwI.lean):
-- dilMellinF_pow_eq_riwI — cⁿ⁺¹·dilMellinF f (powTest n) S a t [0,1] = riwI (f·powBandGen_{[0,B]}) qk … with
-- c = clampedInv(a,t), i.e. dilMellinF = c^{-(n+1)}·∫_0^c (f·xⁿ). A one-line composition of
-- dilMellinF_eq_mellinMoment (dilMellinF = mellinMoment(dilateTestR c f)) and riwI_moment_covariance
-- (riwI = cⁿ⁺¹·mellinMoment(dilateTestR c f)). The change-of-variables that turns the convolution–Mellin
-- inner integral into a genuine window integral of f — the substitution the ∫_t assembly consumes. NO
-- ∫_t assembly, NO factorization, NO positivity, NO crux.
#print axioms Square.dilMellinF_pow_eq_riwI

-- Clamp-independence of the convolution's Mellin tail-term on inert windows (new
-- Square/MulConvClampIndep.lean). mulConvR_S_indep: the convolution value mulConvR f g x S is
-- independent of the clamp bound S (for |x| ≤ S, |x| ≤ S') — the two Haar integrals integrate the
-- SAME S-free function f(x·(1/max(t,a)))·g(t)·(1/max(t,a)) at different Lipschitz moduli, bridged by
-- riemannIntegralI_certif_irrel. twTerm_mulConv_S_indep: consequently, for m+2 ≤ S and m+2 ≤ S', the
-- m-th twisted tail term twTerm (mulConvRTest f g S) n m is the SAME for both clamps (both clamps inert
-- on [m+1,m+2] by qBandQ_eq_of_band; congr_unit_mod across the two moduli). The eventually-constant-in-S
-- fact that makes the clamp-free (S→∞) half-line transform of the convolution well-defined per window —
-- mellinHat(mulConvRTest f g S) does NOT converge for fixed S (frozen tail). NO S→∞ limit object, NO
-- half-line assembly, NO factorization M[f⋆g]=M[f]·M[g], NO positivity, NO crux.
#print axioms Square.mulConvR_S_indep
#print axioms Square.twTerm_mulConv_S_indep

-- The convolution's Mellin tail-term factored onto the dilated-tail form (new
-- Square/TwTermMulConvDilated.lean). dilTail_ptw: the swapped outer test's value at each t equals the
-- dilated-tail integrand (g·clampedInv)·twTerm(dilateTestR (clampedInv a t) f) n m — coupOuterTestSwap_gpull
-- (g-pullout) composed with dilMellinF_eq_twTerm (the inert-clamped inner x-integral on [m+1,m+2]⊆[0,S]).
-- twTerm_mulConv_dilated: for m+2 ≤ S, twTerm (mulConvRTest f g S) n m = ∫_t (g(t)·(1/max(t,a)))·
-- twTerm(dilateTestR (1/max(t,a)) f) n m dt — the per-window bridge from the convolution side onto the
-- dilation-covariance side (mellinConv_fubini + riemannIntegralI_congr via dilTail_ptw). NO ∫_t
-- reconstruction of M[g], NO half-line assembly, NO covariance application, NO factorization
-- M[f⋆g]=M[f]·M[g], NO positivity, NO crux.
#print axioms Square.dilTail_ptw
#print axioms Square.twTerm_mulConv_dilated

-- The finite telescoping of adjacent-window interval integrals (new Square/IntervalTelescope.lean):
-- exhaustion rung 3. For an increasing rational endpoint sequence c, Σ_{m<N} ∫_{[c m, c(m+1)]} f =
-- ∫_{[c 0, c N]} f, a pure finite-additivity induction driven by riemannIntegralI_split_at (splitting
-- the whole window at the last node c N). The finite exhaustion-independence both the integer and the
-- s-scaled tilings satisfy. No improper integral, no limit, no dilation, no positivity, no crux.
#print axioms Square.riemannIntegralI_telescope

-- The exhaustion characterization of the half-line integral (new Square/HalfLineExhaustion.lean):
-- exhaustion rung 4. halfLineIntegral f = Rlim_j of the INTERVAL integral over the cap [0, 1+digammaMidx K j],
-- re-expressing the window-genSum improper integral as a limit of interval integrals: STEP A telescope
-- (genSum integralTerm = int_1^{N+1}), STEP B split_at at width 1 (join the [0,1] gateway), STEP C
-- Rlim_add_const + Rlim_congr (same digammaMidx sampling, no new limit minted). No dilation, no crux.
#print axioms Square.halfLineIntegral_eq_Rlim

-- Exhaustion-independence of the improper half-line integral (new Square/ImproperScheduleIndep.lean):
-- exhaustion rung 4b. ANY integer schedule R growing at least as fast as digammaMidx K yields the SAME
-- Rlim as improperIntegral1, so the improper Mellin integral is schedule-independent. seq_gap_bound:
-- a real gap |P-V| <= C/(N+1) gives the raw-approximant gap |P.seq N - V.seq N| <= (C+2)/(N+1)
-- (Qarch_gen via the read-index 2m+1). Rlim_approx_eq: per-index closeness of two regular sequences
-- implies equal Rlim (diagonal 4n+3 -> Req_of_lin_bound). genSum_close: the two schedules agree within
-- 1/(j+1) (genSum_diff_eq + genTail_two_sided + digammaTailQ_Midx_le). improper_schedule_eq: the capstone.
-- hgrow is load-bearing (the canonical RTendsTo modulus needs the accelerated schedule). No dilation,
-- no factorization, no positivity, no determinacy, no crux.
#print axioms Square.seq_gap_bound
#print axioms Square.Rlim_approx_eq
#print axioms Square.genSum_close
#print axioms Square.improper_schedule_eq

-- Generic diagonal-operator theory (new Square/DiagonalOperatorCore.lean): weight-agnostic machinery
-- factored out of FinAtlasOperator/BlockLadderCandidate so the reusable operator theory does NOT depend
-- on any concrete diagonal (Atlas seed, block-ladder, or otherwise). diagOp w N: real-diagonal operator
-- on CVec N; diagOp_congr/_add/_smul: setoid-respecting + ℂ-linear; diagOp_herm: SYMMETRIC for a real
-- weight (⟨Ax,y⟩=⟨x,Ay⟩ — symmetry, NOT self-adjointness); diagOp_cvInc: tower compatibility A_M∘ι≈ι∘A_N.
-- dlimDiagW + dlimDiagW_wd/_add/_smul/_herm: generic descent of any real diagonal to the colimit
-- dlimPreHilbert. dlimBasis_normalized: normalized coordinate basis ⟨e_i,e_i⟩≈1; dlimDiagW_eigen: the
-- EIGENPAIR A e_i ≈ w_i·e_i (each weight is an eigenvalue on the normalized point spectrum). No spectrum,
-- no Atlas, no crux; crux none.
#print axioms Square.diagOp_congr
#print axioms Square.diagOp_add
#print axioms Square.diagOp_smul
#print axioms Square.diagOp_herm
#print axioms Square.diagOp_cvInc
#print axioms Square.dlimDiagW_wd
#print axioms Square.dlimDiagW_add
#print axioms Square.dlimDiagW_smul
#print axioms Square.dlimDiagW_herm
#print axioms Square.dlimBasis_normalized
#print axioms Square.dlimDiagW_eigen
#print axioms Square.dlimDiagW_eigen_normSq
#print axioms Square.dlimBasis_self_re

-- The Atlas seed operator (Square/FinAtlasOperator.lean): the sourced spectral operator M (§5/§6.6,
-- atlasEig/atlasM) realized as a DIAGONAL OBSERVABLE via the generic diagOp/dlimDiagW, SYMMETRIC w.r.t.
-- the POSITIVE metric cInner (not the metric). atlasObsEig = atlasEig on i<24, 0 beyond
-- (atlasObsEig_sourced/_seam): the −1 tail is NOT an unbounded spectrum; the unbounded scale-lift is the
-- EXPOSED open seam. atlasObsEig_signature: indefinite Atlas signature (10,14) on the sourced carrier.
-- atlasObsEig_carrier_and_seam: −1 eigenspace within [0,24), tail zeroed. atlasWeight_eq_atlasM_diag:
-- provenance — the weight IS atlasM's diagonal on i<24. dlimAtlas_wd/_add/_smul/_herm: the seed descends
-- to dlimPreHilbert as a symmetric operator (thin wrappers over dlimDiagW_*). Finite seed M₂₄⊕0,
-- bounded; crux none.
#print axioms Square.atlasObsEig_sourced
#print axioms Square.atlasObsEig_seam
#print axioms Square.atlasObsEig_signature
#print axioms Square.atlasObsEig_carrier_and_seam
#print axioms Square.atlasWeight_eq_atlasM_diag
#print axioms Square.atlasWeight_seam
#print axioms Square.atlasObs_vanishes_off_carrier
-- Fin-24-typed finite seed M₂₄ (reviewer item 1: source boundary enforced by the type Fin 24, tail
-- unrepresentable) + base restriction to M₂₄ + bounded spectrum. atlasEig_range (AtlasSpectralCore):
-- every eigenvalue ∈ [−1,10] at every index → the sourced diagonal is BOUNDED (op-norm ≤ 10), the
-- reason the seed is not the (unbounded) HP operator. atlasSeedWeight_eq_atlasWeight/atlasSeedOp_eq:
-- the Fin-24 seed agrees with the ℕ-indexed tower operator on the carrier (inherits symmetry).
-- atlasSeedWeight_eq_atlasM: base restriction — the seed weight IS atlasM's diagonal. atlasSeedOp_herm:
-- the seed is symmetric on cInner 24 (symmetry, not self-adjointness). atlasSeedEig_bounded: seed
-- spectrum ⊆ [−1,10]. NO unbounded operator, NO refinement lift, NO completion; crux none.
#print axioms Square.atlasEig_range
#print axioms Square.atlasSeedWeight_eq_atlasWeight
#print axioms Square.atlasSeedOp_eq
#print axioms Square.atlasSeedWeight_eq_atlasM
#print axioms Square.atlasSeedOp_herm
#print axioms Square.atlasSeedEig_bounded
#print axioms Square.dlimAtlas_wd
#print axioms Square.dlimAtlas_add
#print axioms Square.dlimAtlas_smul
#print axioms Square.dlimAtlas_herm

-- The block-ladder candidate (new Square/BlockLadderCandidate.lean): ONE locally-invented unbounded
-- diagonal, built with a WEIGHT-RANGE asymmetry diagnostic (NOT a formal HP rejection). blockLadderEval on the typed carrier
-- BlockLadderAddr=(scale ℓ, block∈Fin 24): (M₂₄ eigenvalue at block) + ℓ·log5, where ℓ·log5 =
-- orbitShift 5 ℓ (Frobenius-orbit length, chain prime p=5=atlasPrime0); the M₂₄+ℓ·log5 LAW is invented,
-- NOT a warranted Atlas refinement. log5_ge_one: log5≥1 zero-free (logN_ge_k_log2 + logN_2_ge_half in
-- the ComplexZeta-free RealPow). blockLadderWeight_val/_mul24: raw-index form. blockLadderWeight_base +
-- blockLadderOp_base_action: base-ACTION agreement with atlasSeedOp on CVec 24. blockLadderEval_scale_succ
-- + blockLadder_scale_gap: each level adds exactly log5 (a CONSTANT scale gap). blockLadder_scale_step +
-- blockLadderWeight_scale_ge + blockLadder_unbounded: weight unboundedness (∀B ∃i, B≤weight i).
-- dlimBlockLadder_eigen: the OPERATOR-level eigenpair dlimBlockLadder e_i ≈ w_i·e_i (ties each weight to
-- the operator via the core's normalized basis). Crux none.
#print axioms Square.log5_ge_one
#print axioms Square.blockLadderWeight_val
#print axioms Square.blockLadderWeight_mul24
#print axioms Square.blockLadderWeight_base
#print axioms Square.blockLadderOp_base_action
#print axioms Square.blockLadderEval_scale_succ
#print axioms Square.blockLadder_scale_gap
#print axioms Square.blockLadder_scale_step
#print axioms Square.blockLadderWeight_scale_ge
#print axioms Square.blockLadder_unbounded
#print axioms Square.dlimBlockLadder_eigen

-- The WEIGHT-RANGE asymmetry DIAGNOSTIC (Square/BlockLadderCandidate.lean) — NOT a formal operator rejection.
-- blockLadderWeight_ge_neg_one: every weight ≥ −1 (block eigenvalue ≥ −1 via atlasEig_range + scale
-- shift ≥ 0). blockLadderWeight_zero_eq_ten: w₀ = 10 (a weight > 2). blockLadder_gt_neg_ten: w_i + 10 > 0
-- strictly (Pos) for every i — so −10 is strictly below the whole diagonal while 10 is a weight.
-- blockLadderSpec_not_neg_closed: the weight spectrum blockLadderWeightSpec (weights ⊆ point spectrum, by
-- dlimBlockLadder_eigen, weights ⊆ point spectrum ONLY) is NOT closed under μ↦−μ (NegClosed). HONEST
-- LIMITATION: a non-closed subset can sit inside a negation-closed superset, so this is a weight-range
-- DIAGNOSTIC, NOT a formal operator/HP rejection (the converse point-spectrum⊆weights is unformalized);
-- crux none.
#print axioms Square.blockLadderWeight_ge_neg_one
#print axioms Square.blockLadderWeight_zero_eq_ten
#print axioms Square.blockLadder_gt_neg_ten
#print axioms Square.blockLadderSpec_not_neg_closed
-- Operator-theoretic unboundedness — the HP UNBOUNDEDNESS PREREQUISITE, passed (Square/
-- BlockLadderCandidate.lean). dlimDiagW_eigen_normSq (core): ⟨A e_i, A e_i⟩.re = w_i² (from the
-- eigenpair + normalization); dlimBasis_self_re (core): ⟨e_i,e_i⟩.re = 1. dlimBlockLadder_not_normBounded:
-- ∀ nat B, dlimBlockLadder is NOT norm-bounded by RofNat B (on e_j with w_j ≥ RofNat(B+1), ⟨A e_j,A e_j⟩
-- = w_j² > (RofNat B)², violating OpNormBounded). dlimBlockLadder_not_normBounded_real: upgraded to ALL
-- real bounds via Archimedean domination (exists_nat_ge: x ≤ RofNat B) + bound monotonicity. This is a
-- NECESSARY HP feature (unbounded operator) — a PASSED prerequisite, not a rejection. (The weight-range
-- asymmetry blockLadderSpec_not_neg_closed is a diagnostic, not a formal operator rejection.) Crux none.
#print axioms Square.dlimBlockLadder_not_normBounded
#print axioms Square.dlimBlockLadder_not_normBounded_real

-- The ℓ² completion of the finite-support direct limit: the ANALYTIC SUBSTRATE (new
-- Square/DlimHilbertCompletion.lean, phase 1; imports ONLY FinDirectLimit — candidate-independent, no
-- block-ladder/Atlas/nominal/zero modules). Squared norm dlimNormSq:=⟨a,a⟩.re, squared distance
-- dlimDist2:=‖a−b‖² (kept SQUARED, no Rsqrt). dlimNormSq_wd/dlimSub_wd/dlimDist2_wd: representative
-- independence over the colimit setoid DLimEq. dlimNormSq_nonneg/dlimDist2_nonneg: nonnegativity (from
-- dlimInner_self_nonneg). dlimNormSq_zero/dlimDist2_self: ‖0‖²≈0 and ‖a−a‖²≈0. dlimEq_of_sub_zero:
-- colimit group cancellation a−b≈0⟹a≈b. dlimDist2_zero_iff: THE NORM-NULL EQUIVALENCE ‖a−b‖²≈0 ↔ a≈b
-- (the completion's squared-distance gauge definiteness — NOT a metric — via dlimInner_self_definite). DLimCauchyU (def): the squared
-- Cauchy relation. THE NEGATION FOUNDATION (gate item 1): dlimInner_neg_right/dlimInner_neg_left
-- (⟨a,−b⟩≈⟨−a,b⟩≈−⟨a,b⟩, from dlimInner_smul_right through dlimNeg≈(−1)·, a termwise (−1)·z≈−z proved
-- from the ℝ product laws — NO out-of-cone Cneg_Cmul_left/Cconj_Cneg), dlimNormSq_neg (‖−a‖²≈‖a‖²),
-- dlimDist2_symm (DISTANCE SYMMETRY ‖a−b‖²≈‖b−a‖² via b−a≈−(a−b)). NO completion limit, NO inner product
-- on the completion, NO operator yet; the quasi-triangle, setoid, group laws and squared-norm scaling are
-- proved in later blocks; still open = full scalar action + the completed inner product; crux none.
#print axioms Square.dlimNormSq_wd
#print axioms Square.dlimSub_wd
#print axioms Square.dlimDist2_wd
#print axioms Square.dlimNormSq_nonneg
#print axioms Square.dlimDist2_nonneg
#print axioms Square.dlimNormSq_zero
#print axioms Square.dlimDist2_self
#print axioms Square.dlimEq_of_sub_zero
#print axioms Square.dlimDist2_zero_iff
#print axioms Square.dlimInner_neg_right
#print axioms Square.dlimInner_neg_left
#print axioms Square.dlimNormSq_neg
#print axioms Square.dlimDist2_symm
-- THE PARALLELOGRAM + SQUARED QUASI-TRIANGLE (gate item 1, second half): dlimInner_add_left
-- (⟨a+b,c⟩≈⟨a,c⟩+⟨b,c⟩, left-additivity from right-additivity + Hermitian symmetry), dlimNormSq_add
-- (the parallelogram expansion ‖x+y‖²≈‖x‖²+(⟨y,x⟩.re+⟨x,y⟩.re)+‖y‖²), dlimDist2_quasitriangle
-- (d²(a,c) ≤ 2·d²(a,b)+2·d²(b,c) — the sqrt-free replacement for the ordinary triangle law, via the
-- cross-term cancellation quasi_arith and ‖u−v‖²≥0; Radd_le_add ported LOCAL to hold the import fence).
#print axioms Square.dlimInner_add_left
#print axioms Square.dlimNormSq_add
#print axioms Square.dlimDist2_quasitriangle
-- THE CAUCHY-PREDICATE STRUCTURAL LEMMAS (gate item 2): DLimCauchyU_const (the constant sequence is
-- Cauchy, ‖a−a‖²≈0 ≤ M(j,k)) and DLimCauchyU_congr (pointwise DLimEq congruence: x≈y pointwise ⟹
-- x Cauchy → y Cauchy). Supported by the private modulus facts symmetry/nonnegativity/decay
-- (M(n,n) ≤ 4/(n+1), the canonical null domination) — all import-only-FinDirectLimit.
#print axioms Square.DLimCauchyU_const
#print axioms Square.DLimCauchyU_congr
-- THE COMPLETION SETOID (gate items 4–7): DLimCompletionRaw (Cauchy seq + regularity proof, item 4);
-- DLimCompletionEq = norm-null sequence equivalence (∀k ∃N ∀n≥N ‖Xn−Yn‖² ≤ 1/(k+1); the ∀k absorbs
-- the quasi-triangle factor so it is a genuine transitive equivalence in the sqrt-free squared setting).
-- DLimCompletionEq_refl/_symm/_trans (item 5, trans via dlimDist2_quasitriangle at auxiliary level 4k+3),
-- packaged as the proof-bearing instance dlimCompletionSetoid (item 6); DLimCompletionRaw.of = the
-- constant-sequence MAP + DLimCompletionEq_of (respects DLimEq, item 7). Rescheduled add/neg operations
-- and the group laws are proved below; still open = full scalar action + the completed inner product.
#print axioms Square.DLimCompletionEq_refl
#print axioms Square.DLimCompletionEq_symm
#print axioms Square.DLimCompletionEq_trans
#print axioms Square.dlimCompletionSetoid
#print axioms Square.DLimCompletionEq_of
-- EMBEDDING REFLECTION / INJECTIVITY (reviewer gate 1): DLimCompletionEq_of_iff (of a ≈ of b ↔ a ≈ b) —
-- the constant map `of` is injective mod the two setoids (forward via the Archimedean squeeze
-- Req_zero_of_nonneg_of_small + the norm-null equivalence dlimDist2_zero_iff). Isometry/density remain
-- separate & OPEN; `of` is downgraded in-source from "isometric dense embedding" to injective map.
#print axioms Square.DLimCompletionEq_of_iff
-- RESCHEDULED OPERATIONS (gate item 8, first two): dlimCompletionNeg/_congr (negation preserves the
-- modulus outright) and dlimCompletionAdd/_congr (RESCHEDULED n↦2n+1 so the quasi-triangle's factor-4 is
-- cancelled by dlimCauchyMod_halve : 4·M(2j+1,2k+1) ≈ M(j,k)); both preserve regularity AND equivalence.
-- Still open: scalar multiplication (the |c|²-dependent reschedule) and the completed inner product.
#print axioms Square.dlimCompletionNeg_congr
#print axioms Square.dlimCompletionAdd_congr
-- COFINAL-RESCHEDULING INVARIANCE (reviewer gate 2): dlimReschedOdd_eq (X ≈ its odd subsequence
-- n↦X_{2n+1}), via the reusable modulus monotonicity dlimCauchyMod_mono (M(p',q')≤M(p,q) for p≤p',q≤q')
-- + the diagonal decay: ‖X_n−X_{2n+1}‖² ≤ M(n,2n+1) ≤ M(n,n) ≤ 4/(n+1) ≤ 1/(k+1) for n≥4k+3.
#print axioms Square.dlimReschedOdd_eq
-- AFFINE COFINAL INVARIANCE (reviewer gate 2, generalized): dlimResched (the σ_q(n)=q(n+1)−1 affine
-- reschedule member, q≥1, generalizing the q=2 odd reschedule — scalar mult will use a scalar-dependent q)
-- + dlimResched_eq (X ≈ X_{σ_q(n)}; threshold n≥4k+3 independent of q, via mono + diagonal decay).
#print axioms Square.dlimResched
#print axioms Square.dlimResched_eq
-- RAW SQUARED-NORM / SQUARED-DISTANCE SCALING (reviewer gate 3, on the clean cNormSq core):
-- dlimNormSq_smul (‖c·v‖² ≈ |c|²·‖v‖², via ⟨c·v,c·v⟩ ≈ (c·conj c)·⟨v,v⟩ then the real part) and
-- dlimDist2_smul (‖c·a−c·b‖² ≈ |c|²·‖a−b‖², via c·a−c·b ≈ c·(a−b)). Both EQUALITIES (no Rmul-monotonicity);
-- the |c|²·M(σ_q j,σ_q k) ≤ M(j,k) attenuation INEQUALITY and the scalar action are the next commit.
#print axioms Square.dlimNormSq_smul
#print axioms Square.dlimDist2_smul
-- THE q⁻² AFFINE-MODULUS ATTENUATION (reviewer gate 4): dlimCauchyMod_atten — for x ≤ q (q≥1),
-- x·M(σ_q j,σ_q k) ≤ M(j,k) with σ_q(n)=q(n+1)−1. Since M(σ_q)=M/q², x≤q leaves x·M(σ_q)≤q·M/q²=M/q≤M.
-- Needs Real-mult MONOTONICITY, absent in-cone — reproduced as private `_loc` ports of RealPow's
-- Rmul_le_Rmul_left/right (whose module reaches Zeta), verbatim from the in-cone Q/Real primitives
-- (mul_lo_core, Rnonneg_Rmul, the order⇄Bishop bridges, Rmul_ofQ_ofQ, Qneg_le_neg). This is the
-- scalar-multiplication regularity bridge the scalar action (next) consumes.
#print axioms Square.dlimCauchyMod_atten
-- SCALAR MULTIPLICATION (reviewer gate 5): scalarSchedule c := xBound|c|² (choice-free Nat, not the
-- ∃-witness of cNormSq_nat_bound — it can index a sequence); one_le_scalarSchedule (≥1);
-- cNormSq_le_scalarSchedule (|c|² ≤ scalarSchedule c, the ∃-free bound). dlimCompletionSmul (the proof-
-- bearing scalar action, reg via dlimDist2_smul + Rmul_le_Rmul_left_loc + dlimCauchyMod_atten — DIRECTLY
-- axiom-audited per step 7). sched_comp (σ_r(σ_q(n))=σ_{rq}(n), the common-refinement tool).
-- dlimCompletionSmul_congr_vec (X≈Y ⟹ c·X≈c·Y). dlimCompletionSmul_congr_scalar (c≈c' ⟹ c·X≈c'·X —
-- the reschedule/common-refinement route: reschedule c·X by scalarSchedule c' and c'·X by scalarSchedule c,
-- align both at σ_{qr} via sched_comp + Nat.mul_comm, close stagewise with dlimSmul_wd hc; NO scalar-diff
-- estimate). Together vec+scalar congruence = dlimCompletionSmul is a WELL-DEFINED complex-scalar-setoid
-- action. dlimCompletionSmul_congr (combined two-argument congruence c≈c' ∧ X≈Y ⟹ c·X≈c'·Y).
-- COMPLEX-MODULE LAWS (reviewer gate 6, all via the common-refinement combinator + the raw colimit scalar
-- laws applied stagewise): dlimCompletionSmul_one (1·X≈X), dlimCompletionZero_smul (0·X≈0),
-- dlimCompletionSmul_zero (c·0≈0), DLimCompletionEq_of_smul (of-homomorphism c·of a ≈ of(c·a)),
-- dlimCompletionSmul_add (c·(X+Y)≈c·X+c·Y), dlimCompletionSmul_Cadd ((c+d)·X≈c·X+d·X),
-- dlimCompletionSmul_assoc (c·(d·X)≈(cd)·X). With these seven laws closed, the completion carrier is a
-- complex-module modulo the completion setoid. Still downstream: the completed inner product / completeness.
#print axioms Square.scalarSchedule
#print axioms Square.one_le_scalarSchedule
#print axioms Square.cNormSq_le_scalarSchedule
#print axioms Square.dlimCompletionSmul
#print axioms Square.sched_comp
#print axioms Square.dlimCompletionSmul_congr_vec
#print axioms Square.dlimCompletionSmul_congr_scalar
#print axioms Square.dlimCompletionSmul_congr
#print axioms Square.dlimCompletionSmul_one
#print axioms Square.dlimCompletionZero_smul
#print axioms Square.dlimCompletionSmul_zero
#print axioms Square.DLimCompletionEq_of_smul
#print axioms Square.dlimCompletionSmul_add
#print axioms Square.dlimCompletionSmul_Cadd
#print axioms Square.dlimCompletionSmul_assoc
-- CLEAN COMPLEX-ONLY SQUARED-MODULUS CORE (reviewer gate item 3; new Analysis/ComplexNormSqCore.lean,
-- Zeta-free cone = ComplexCore + RealSquareDefinite only — NOT the ζ-tainted ZeroGeometry.cnormSq, NOT the
-- heavy ComplexMod): cNormSq z := re²+im², cNormSq_nonneg (sum of squares ≥ 0), and z·conj z = the real
-- scalar |z|²: Cmul_Cconj_re (Re = |z|²) + Cmul_Cconj_im (Im = 0). Feeds the scalar-mult ‖c·v‖²≈|c|²‖v‖².
#print axioms Analysis.cNormSq
#print axioms Analysis.cNormSq_nonneg
#print axioms Analysis.Cmul_Cconj_re
#print axioms Analysis.Cmul_Cconj_im
-- cNormSq now CANONICAL: ZeroGeometry.cnormSq and ComplexMod.CnormSq are redefined as := cNormSq z
-- (defeq aliases). cNormSq_congr (|·|² respects Ceq); exists_nat_ge_loc (constructive Archimedean
-- upper bound ∃B:Nat, x ≤ B/1, port of the block-ladder lemma) + cNormSq_nat_bound (|c|² ≤ B) — the
-- scalar-magnitude bound scalar multiplication's reschedule will consume.
#print axioms Analysis.cNormSq_congr
#print axioms Analysis.exists_nat_ge_loc
#print axioms Analysis.cNormSq_nat_bound
-- SHARED ζ-FREE REAL MULTIPLICATION/ORDER CORE (reviewer debt: new Analysis/RealOrderCore.lean). The
-- ~190 lines of generic Bishop-real mul/order theory previously copied PRIVATELY into DlimHilbertCompletion
-- are now ONE reusable public module (Zeta-free cone = RealSquareDefinite), so the completed-inner-product
-- work imports them instead of re-duplicating. `_loc` suffix = globally-unique leaf names (distinct from
-- RealPow's Zeta-reaching Rnonneg_Rmul / Rmul_le_Rmul_left / …), required by the coverage gate.
#print axioms Analysis.Rnonneg_ofQ_loc
#print axioms Analysis.Rle_ofQ_of_Qle_loc
#print axioms Analysis.Radd_ofQ_loc
#print axioms Analysis.Rmul_ofQ_ofQ_loc
#print axioms Analysis.Radd_le_add_loc
#print axioms Analysis.Qneg_le_neg_loc
#print axioms Analysis.mul_lo_core_loc
#print axioms Analysis.Rnonneg_Rmul_loc
#print axioms Analysis.Rnonneg_of_Rle_zero_loc
#print axioms Analysis.Rnonneg_congr_loc
#print axioms Analysis.Rnonneg_Rsub_of_Rle_loc
#print axioms Analysis.Rle_of_Rnonneg_Rsub_loc
#print axioms Analysis.Rmul_le_Rmul_left_loc
#print axioms Analysis.Rmul_le_Rmul_right_loc
-- COORDINATEWISE COMPLEX-LIMIT CORE (reviewer's named prerequisite for the completed inner product; new
-- Analysis/ComplexLimitCore.lean, Zeta-free cone = Complete + Complex). Lifts the real completeness engine
-- (RReg/Rlim/Rlim_tendsTo/RTendsTo_unique) to ℂ coordinatewise. `…Core` suffix keeps leaf names UNIQUE vs
-- the existing Zeta-tainted Analysis.ComplexLimit (Clim/CReg/…, imports RlimProps→…→Zeta). CRegCore (both
-- coords regular), ClimCore (pair of real limits), ClimCore_re/ClimCore_im (coordinate projections = rfl),
-- CTendsToCore, ClimCore_tendsTo (completeness of ℂ), CTendsToCore_unique (limit unique up to Ceq). The
-- completed inner product ⟨X,Y⟩ := lim ⟨X_n,Y_n⟩ will stand on this.
#print axioms Analysis.CRegCore
#print axioms Analysis.ClimCore
#print axioms Analysis.ClimCore_re
#print axioms Analysis.ClimCore_im
#print axioms Analysis.CTendsToCore
#print axioms Analysis.ClimCore_tendsTo
#print axioms Analysis.CTendsToCore_unique
-- RReg BRIDGE (ζ-free ports of ComplexZeta.seq_diff_le / RReg_of_real_bound, renamed `_core` for
-- leaf-uniqueness): from a real pairwise-difference bound `X_j − X_k ≤ c_jk ≤ 1/(j+1)+1/(k+1)` conclude the
-- coordinate sequence is RReg — the exact glue feeding each inner-product coordinate into CRegCore.
#print axioms Analysis.seq_diff_le_core
#print axioms Analysis.RReg_of_real_bound_core
-- NULL-DIFFERENCE LIMIT THEOREM (the completedInner_congr foundation the reviewer named): two regular
-- sequences eventually within 1/(k+1) of each other have EQUAL Bishop limits (Rlim_eq_of_close), lifted
-- coordinatewise to ℂ (ClimCore_eq_of_close). Built by the Qarch_gen constant-tolerating technique.
#print axioms Analysis.Rlim_eq_of_close
#print axioms Analysis.ClimCore_eq_of_close
-- CLEAN LIMIT LAWS (consumed by the completed-inner-product Hermitian/positivity laws), named _core for
-- leaf-uniqueness vs RlimProps/ComplexDigammaConj:
#print axioms Analysis.Rlim_congr_core
#print axioms Analysis.Rlim_const_core
#print axioms Analysis.Rlim_zero_core
#print axioms Analysis.RReg_neg_core
#print axioms Analysis.RTendsTo_neg_core
#print axioms Analysis.Rlim_nonneg_core
#print axioms Analysis.Rlim_neg_core
-- TOWARD THE COMPLETED INNER PRODUCT (in DlimHilbertCompletion): the four analytic foundations —
-- dlimInner_sub_left/right (subtraction bilinearity for the difference split), dlimInner_re_amgm (the
-- sqrt-free AM-GM/polarization complex Cauchy–Schwarz seed 2λ·Re⟨u,v⟩ ≤ ‖u‖²+λ²‖v‖²), Rmul_le_cancel_ofQ
-- (positive-rational left-cancellation — divide the AM-GM by 2λ, no Pos-chain/sqrt), Rle_ofQ_xBound +
-- normBound_spec + dlimNormSq_uniform_bound (choice-free uniform squared-norm bound). Then the reusable
-- single-term bound dlimInner_re_termBound (Re⟨u,v⟩ ≤ e·(1+B)/2) and the Im-coordinate reduction
-- dlimInner_im_eq_re / dlimNormSq_smul_negI (the −i twist, so the same bound covers the imaginary part).
#print axioms Square.dlimInner_sub_left
#print axioms Square.dlimInner_sub_right
#print axioms Square.dlimInner_re_amgm
#print axioms Square.Rmul_le_cancel_ofQ
#print axioms Square.Rle_ofQ_xBound
#print axioms Square.normBound_spec
#print axioms Square.dlimNormSq_uniform_bound
#print axioms Square.dlimDist2_zero_eq
#print axioms Square.dlimInner_re_termBound
#print axioms Square.dlimInner_im_eq_re
#print axioms Square.dlimNormSq_smul_negI
-- THE COMPLETED INNER PRODUCT (DlimCompletedInner.lean — consumes BOTH DlimHilbertCompletion and
-- ComplexLimitCore): modulus_bound (the reschedule inequality, reduces to 2+BX+BY ≤ 2F);
-- innerSeq_re_split/im_split (the difference split ⟨aj,bj⟩−⟨ak,bk⟩ = ⟨aj−ak,bj⟩+⟨ak,bj−bk⟩);
-- one_le_Fsched (reschedule factor ≥ 1); innerSeq_re_bound/im_bound (each coordinate's pairwise difference
-- ≤ 1/(j+1)+1/(k+1)); innerSeq_CRegCore (REGULARITY of n ↦ ⟨X_{σn},Y_{σn}⟩, reviewer gate step 3);
-- completedInner (the def ⟨X,Y⟩ := ClimCore, reviewer gate step-5 definition). Pre-Hilbert laws + rep
-- independence are the NEXT gate — not claimed here.
#print axioms Square.modulus_bound
#print axioms Square.innerSeq_re_split
#print axioms Square.innerSeq_im_split
#print axioms Square.one_le_Fsched
#print axioms Square.innerSeq_re_bound
#print axioms Square.innerSeq_im_bound
#print axioms Square.innerSeq_CRegCore
#print axioms Square.completedInner
-- REPRESENTATIVE INDEPENDENCE (reviewer's non-negotiable gate): completedInner_congr — X≈X' ∧ Y≈Y' ⟹
-- ⟨X,Y⟩≈⟨X',Y'⟩, so the completed inner product descends to the completion setoid. Supporting: the general
-- single-difference bounds dlimInner_re_diff_le/im_diff_le (Re⟨a,b⟩−Re⟨a',b'⟩ ≤ eₐ(1+Bb)/2+e_b(1+Ba)/2);
-- the unified schedule/tolerance constant congrM + congrM_pos/congrM_halfBound; dlimCauchyMod_le_inv_sq
-- (M(i,j)≤1/m² for indices ≥2m, the Term-B Cauchy bound). Aligns the two representative-dependent Fsched
-- schedules by a mid-point triangle, unified e=1/m, fed into ClimCore_eq_of_close.
#print axioms Square.dlimInner_re_diff_le
#print axioms Square.dlimInner_im_diff_le
#print axioms Square.congrM_pos
#print axioms Square.congrM_halfBound
#print axioms Square.dlimCauchyMod_le_inv_sq
#print axioms Square.completedInner_congr
-- INNER SELF/HERMITIAN LAWS (3 of 6 FinPreHilbert inner laws): self_nonneg, self_im, conj.
#print axioms Square.completedInner_self_nonneg
#print axioms Square.completedInner_self_im
#print axioms Square.completedInner_conj
-- DEFINITENESS (the load-bearing FinPreHilbert inner law): completedInner_self_definite —
-- <X,X> ~ 0 implies X ~ 0 in the completion setoid (quasi-triangle through a rescheduled
-- representative whose squared norm -> 0 via the eventually-small extraction from Rlim ~ 0).
#print axioms Square.completedInner_self_definite
-- ADDITIVE STRUCTURE ON THE COMPLETION (reviewer gate 3): DLimCompletionEq_of_pointwise (pointwise
-- DLimEq ⟹ completion eq — the workhorse), dlimCompletionZero (constant 0), and the group laws mod
-- completion equivalence: dlimCompletionAdd_comm, dlimCompletionAdd_zero (right unit, via the cofinal
-- invariance dlimReschedOdd_eq), dlimCompletionAdd_neg (inverse). The `of`-homomorphism laws
-- DLimCompletionEq_of_add (of(a+b) ≈ of a + of b) and DLimCompletionEq_of_neg (of(−a) ≈ −of a), both
-- stagewise reflexivity. ASSOCIATIVITY (dlimCompletionAdd_assoc, below) completes the group, proved via
-- assoc_dist_bound over abstract points (avoiding the whnf blow-up of the nested members).
#print axioms Square.DLimCompletionEq_of_pointwise
#print axioms Square.dlimCompletionAdd_comm
#print axioms Square.dlimCompletionAdd_zero
#print axioms Square.dlimCompletionAdd_neg
#print axioms Square.DLimCompletionEq_of_add
#print axioms Square.DLimCompletionEq_of_neg
-- ASSOCIATIVITY (the last group law, now proved — the completion addition is an abelian group mod ≈):
-- dlimCompletionAdd_assoc, via assoc_dist_bound over ABSTRACT points (no completion nesting → no whnf
-- blow-up; the nesting is touched once at the boundary), reducing d²((X+Y)+Z,X+(Y+Z)) to 2d²(X₄,X₂)+
-- 2d²(Z₂,Z₄) and collapsing 4·(1/(4(k+1)))=1/(k+1) for n≥8k+7.
#print axioms Square.dlimCompletionAdd_assoc
-- PROOF-BEARING DEFINITIONS (their `.reg`/regularity fields carry inline proofs not otherwise audited;
-- audited directly so no sorry can hide in a definition's proof component): the constant map, zero, and
-- the three completion members (negation, rescheduled addition, odd reschedule).
#print axioms Square.DLimCompletionRaw.of
#print axioms Square.dlimCompletionZero
#print axioms Square.dlimCompletionNeg
#print axioms Square.dlimCompletionAdd
#print axioms Square.dlimReschedOdd

-- ===========================================================================
-- FINPREHILBERT COMPLETION PACKAGE (this phase): the completed inner product's two remaining
-- sesquilinearity laws (add_right / smul_right), the reusable dominating-schedule refinement infra
-- (genInner regularity + alignInner master alignment), the limit-linearity workhorses (RReg of a
-- pointwise sum/scale is FALSE at the canonical modulus, so these take combined-seq regularity as a
-- hypothesis), and the packaged instance dlimCompletionPreHilbert : FinPreHilbert. All choice-free.
-- ===========================================================================
#print axioms Analysis.Rlim_add_of_approx_core
#print axioms Analysis.Rlim_add_core
#print axioms Analysis.Rlim_smul_ofQ_of_approx
#print axioms Analysis.Rlim_smul_ofQ
#print axioms Square.cauchyMod_le_rhoMod_ar
#print axioms Square.genInner_re_bound_ar
#print axioms Square.genInner_im_bound_ar
#print axioms Square.genInner_CRegCore_ar
#print axioms Square.alignInner_ar
#print axioms Square.completedInner_add_right
#print axioms Square.Rmul_diag_gap_sr
#print axioms Square.Rlim_lincomb2_add_sr
#print axioms Square.ClimCore_Cmul_approx_sr
#print axioms Square.completedInner_smul_right
#print axioms Square.dlimCompletionPreHilbert

-- ===========================================================================
-- COMPLETION: isometric embedding + density + completeness (this phase). The completion
-- (DLimCompletionRaw/DLimCompletionEq, completedInner) is a genuine metric completion of the
-- finite-support direct limit: ofHom (linear isometry), completion_dense (density with modulus),
-- completionLim + completion_complete (Cauchy sequences converge). All choice-free.
-- ===========================================================================
#print axioms Analysis.Rle_Rlim_ofQ_eventual_core
#print axioms Square.completedInner_of
#print axioms Square.FinPreHilbertHom
#print axioms Square.ofHom
#print axioms Square.completedNormSq
#print axioms Square.dlimCompletionSub
#print axioms Square.completedDist2
#print axioms Square.completedNormSq_nonneg
#print axioms Square.completedDist2_nonneg
#print axioms Square.Rle_Rlim_ofQ_eventual_dns
#print axioms Square.completedDist2_reduce_dns
#print axioms Square.completion_dense
#print axioms Square.le_of_eq_cpl
#print axioms Square.Rneg_Rneg_cpl
#print axioms Square.Cadd_zero_cpl
#print axioms Square.Cneg_Cneg_cpl
#print axioms Square.Cneg_congr_cpl
#print axioms Square.Cconj_Cneg_cpl
#print axioms Square.Ceq_zero_of_eq_add_self_cpl
#print axioms Square.Ceq_neg_of_add_eq_zero_cpl
#print axioms Square.completedInner_add_left_cpl
#print axioms Square.completedInner_zero_right_cpl
#print axioms Square.completedInner_neg_right_cpl
#print axioms Square.completedInner_neg_left_cpl
#print axioms Square.completedNormSq_congr_cpl
#print axioms Square.completedNormSq_neg_cpl
#print axioms Square.completedNormSq_add_expand_cpl
#print axioms Square.zeroAdd_cpl
#print axioms Square.negAddSelf_cpl
#print axioms Square.telescope_cpl
#print axioms Square.completedDist2_of_cpl
#print axioms Square.dist2_polar_cpl
#print axioms Square.completedDist2_symm_cpl
#print axioms Square.completedDist2_quasitriangle_cpl
#print axioms Square.completion_dense_at_cpl
#print axioms Square.sumbound_key_cpl
#print axioms Square.tree_collapse_cpl
#print axioms Square.CompletionCauchyU
#print axioms Square.hcauchy_cpl
#print axioms Square.tree_collapse2_cpl
#print axioms Square.completionLim
#print axioms Square.completion_complete

-- PACKAGED Bishop-complete pre-Hilbert space (reviewer step 1): the squared-distance metric laws
-- (congruence/definiteness/self via completedInner_* black boxes) + the bundled record + instance.
-- SQUARED distance, factor-2 quasi-triangle — honestly NOT a Hilbert space.
#print axioms Square.dlimCompletionEq_of_sub_zero
#print axioms Square.completedDist2_congr
#print axioms Square.completedDist2_self
#print axioms Square.completedDist2_definite
#print axioms Square.dlimCompletionSpace

-- CONTRACT REPAIR (reviewer): tie dist2↔inner (dist2_eq_inner) + cauchy↔dist2 (canonical bishopCauchy);
-- + the completion RELATIONSHIP bundle (source/embed/reflect/dense/complete-target).
#print axioms Square.bishopCauchy
#print axioms Square.CompletionOf
#print axioms Square.dlimIsCompletion

-- COORDINATE READS (reviewer items 4-5): coord i X := <of e_i, X> + congr/add/smul/recovery-on-of
-- + coord_re_continuity (real coord 1-Lipschitz in d2) via completion AM-GM + normalized-vector CS.
#print axioms Square.coord
#print axioms Square.coord_congr
#print axioms Square.coord_add
#print axioms Square.coord_smul
#print axioms Square.coord_of
#print axioms Square.completedNormSq_smul_real
#print axioms Square.completedInner_re_amgm
#print axioms Square.completedInner_re_cs_unit
#print axioms Square.coord_re_continuity

-- BASIS ORTHONORMALITY + coefficient recovery (item 2) + FULL COMPLEX coordinate continuity (item 3).
#print axioms Square.dlimBasis_coord_bo
#print axioms Square.dlimBasis_ortho_bo
#print axioms Square.completedNormSq_smul_negI
#print axioms Square.coord_im_continuity
#print axioms Square.coord_modulus_continuity

-- FINITE COORDINATE PROJECTIONS + residual Pythagoras/contraction + P_N X -> X via density (reviewer items 4-5).
#print axioms Square.finProj
#print axioms Square.coord_finProj_ge_pj
#print axioms Square.coord_finProj_lt_pj
#print axioms Square.finProj_ortho_residual
#print axioms Square.finProj_contraction_pj
#print axioms Square.finProj_best_approx_pj
#print axioms Square.rawProj
#print axioms Square.rawProj_stage_le
#print axioms Square.finProj_of_eq_rawProj
#print axioms Square.dlim_ext_coords
#print axioms Square.rawProj_eq
#print axioms Square.finProj_of_eq_pj
#print axioms Square.finProj_converges_pj

-- PROJECTION HARDENING + GENERAL division-free Cauchy-Schwarz (resolves zeta-fence deferral) + fixed-vector continuity.
#print axioms Square.finProj_pythagoras_hd
#print axioms Square.finProj_congr_hd
#print axioms Square.finProj_add_hd
#print axioms Square.finProj_smul_hd
#print axioms Square.finProj_idem_hd
#print axioms Square.coord_separation_hd
#print axioms Square.finProj_converges_pkg_hd
#print axioms Square.completedInner_re_cs_gen
#print axioms Square.inner_fixed_continuity_cs

-- REAL-WEIGHT MULTIPLIER as a constructive GRAPH/DOMAIN (reviewer gate items 2-3): MulGraph/MulDom (no
-- choice-based output) + setoid congruence, output uniqueness, graph linearity, finite-support domain density.
#print axioms Square.MulGraph
#print axioms Square.MulDom
#print axioms Square.MulGraph_congr_mp
#print axioms Square.MulGraph_unique_mp
#print axioms Square.MulGraph_add_mp
#print axioms Square.MulGraph_smul_mp
#print axioms Square.MulDom_of_mp
#print axioms Square.MulDom_dense_mp
#print axioms Square.MulDom_add_mp
#print axioms Square.MulDom_smul_mp

-- SHARP (uncancelled) Cauchy-Schwarz + GENUINE full-complex fixed-vector LIMIT continuity (supersedes the
-- raw inner_fixed_continuity_cs) + graph CLOSEDNESS + MulDom congruence (reviewer refined gate items 2,3,4).
#print axioms Square.completedInner_re_cs_sharp
#print axioms Square.inner_re_diff_sq_le_scs
#print axioms Square.inner_im_diff_sq_le_scs
#print axioms Square.CompletionTendsTo
#print axioms Square.ComplexTendsTo
#print axioms Square.tendsto_of_le_dist2_scs
#print axioms Square.inner_fixed_tendsto_scs
#print axioms Square.MulGraph_closed_cl
#print axioms Square.MulDom_congr_mcl

-- PARSEVAL (inner = limit of finite coordinate sums) + genuine inner-product SYMMETRY of the real-weight
-- multiplier on its maximal domain (reviewer gate item 5).
#print axioms Square.finCoordSum
#print axioms Square.completedInner_finrank_sy
#print axioms Square.completedInner_finProj_tendsto_sy
#print axioms Square.completedInner_parseval_sy
#print axioms Square.finCoordSum_symm_weight_sy
#print axioms Square.mult_symm_sy

-- GENUINE ADJOINT (inner-product universal property) + both domain inclusions + Dom(A*)=Dom(A) + actual
-- graph-level SELF-ADJOINTNESS of the real-weight multiplier (reviewer gate items 6-7 - the culmination).
#print axioms Square.AdjGraph
#print axioms Square.AdjDom
#print axioms Square.adj_of_dom_adj
#print axioms Square.AdjDom_of_dom_adj
#print axioms Square.dom_of_adj_adj
#print axioms Square.dom_of_adj_dom_adj
#print axioms Square.dom_eq_adj
#print axioms Square.selfadjoint_adj

-- Adjoint congruence + adjoint-witness UNIQUENESS + PACKAGED self-adjointness (density+closed-graph+graph-eq+dom-eq).
#print axioms Square.AdjGraph_congr_adj
#print axioms Square.adj_unique_adj
#print axioms Square.MultiplierSelfAdjoint
#print axioms Square.multiplier_selfAdjoint

-- WeilPrimeShift SPINE: the finite-place Weil prime side as a fold of genuine multiplicative
-- dilation/shift local terms, proved = weilPrimePart (POINT-VALUE, not the Mellin-Gram shortcut).
#print axioms Square.dilateShift_realize_pos
#print axioms Square.dilateShift_realize
#print axioms Square.weilPrimeShiftTerm_eq
#print axioms Square.weilPrimeShiftFold
#print axioms Square.weilPrimeShift_stable
#print axioms Square.dilateShift_comm

-- WeilPrimeShift/Recip: window-aware reciprocal covariance (log-line reflection ↦ reciprocal place value).
#print axioms Square.logPull_reflect_at_logN_eq_recip
#print axioms Square.logPull_reflect_dilate_origin_eq_direct
-- WeilPrimeShift/Norm: the q^{-1/2} normalization bridge (unsymmetrized CC ↔ symmetric Burnol).
#print axioms Square.ofQn_wit
#print axioms Square.qInvSqrt_scale
#print axioms Square.qInvSqrt_sq
#print axioms Square.qInvSqrt_nonneg
#print axioms Square.n_mul_qInvSqrt
#print axioms Square.F_reflect
#print axioms Square.F_normalization
-- WeilPrimeShift/Autocorr: support-stabilization + autocorrWeilTest + weilPrimeShiftFold_autocorr (first consumer).
#print axioms Square.riemannIntegral_le_pts
#print axioms Square.riemannIntegral_pts_zero
#print axioms Square.riemannIntegralI_pts_zero
#print axioms Square.haarIntegral_window_vanish
#print axioms Square.qnum_pos_of_le
#print axioms Square.qinv_scale_le
#print axioms Square.qlow_engine
#print axioms Square.qBandQ_ge_ofQ
#print axioms Square.autocorrL2_f_haar
#print axioms Square.mulConvR_ofQ_vanish
#print axioms Square.autocorrL2_high_vanish
#print axioms Square.autocorrL2_low_vanish
#print axioms Square.autocorrWeilTest_apply
#print axioms Square.weilPrimeShiftFold_autocorr
-- WeilPrimeShift/Bridge: canonical autocorr = in-band autocorrL2 (connects the clamped consumer object to the canonical cone).
#print axioms Square.autocorr_eq_autocorrL2
-- WeilPrimeShift/RecipAutocorr: the pivotal autocorr reciprocal self-duality h(n)≈h(1/n) via the honest Haar CoV.
#print axioms Square.haarIntegral_congr_Q
#print axioms Square.haarIntegral_split_at
#print axioms Square.haarIntegral_congr_window
#print axioms Square.Ps_ofQ
#print axioms Square.mul_n_Qinv_mul_n
#print axioms Square.dilDN_pt_zero
#print axioms Square.P1n_pt_zero
#print axioms Square.left_DN_window_vanish
#print axioms Square.right_I1n_window_vanish
#print axioms Square.Qsub_num_pos_of_lt
#print axioms Square.Qsub_num_nonneg_of_le
#print axioms Square.n_mul_inv_n
#print axioms Square.inv_n_mul_le
#print axioms Square.w1_num_pos
#print axioms Square.CoreStrict
#print axioms Square.core_integrand_agree
#print axioms Square.autocorr_recip_core
#print axioms Square.autocorr_recip
-- WeilPrimeShift/Sonine: the CC √-normalization on the real autocorr (proven hsym), analytic content.
#print axioms Square.acPt_pos
#print axioms Square.acPt_congr
#print axioms Square.autocorr_recip_all
#print axioms Square.ac_CC_normalization
#print axioms Square.acPlaceSym_collapse
#print axioms Square.oneLeSucc
#print axioms Square.acNormFold_collapse
-- WeilPrimeShift/Crux: the GENUINE connection — normalized-autocorr WeilTest, weilPrimePart = acNormFold
-- (non-Gram, no vFrom), and the arch-MINUS-prime weilValue at that slot; positivity = RH left open.
#print axioms Square.acbase_eq_acPt
#print axioms Square.Rsqrt_congr
#print axioms Square.Qinv_congr
#print axioms Square.qinv_num_nonneg
#print axioms Square.normWeight_pos_eq
#print axioms Square.normWeight_congr
#print axioms Square.normWeight_hi
#print axioms Square.normWeight_lo
#print axioms Square.normAutocorr_f_hi
#print axioms Square.normAutocorr_f_lo
#print axioms Square.acT_congr
#print axioms Square.normAutocorrTest_congr
#print axioms Square.recip_bridge
#print axioms Square.placeVal_eq_acPlaceSym
#print axioms Square.weilPrimePart_normAutocorr
#print axioms Square.normCtx_hnS
#print axioms Square.weilPrimePart_normAutocorr_collapsed
#print axioms Square.weilValue_normAutocorr
#print axioms Square.normAutocorr_nonzero
#print axioms Square.normAutocorr_weil_psd_iff_hodge
-- WeilPrimeShift/RH: the HONEST RH reduction — positivity of the constructed functional ⟺ RH GIVEN the
-- classical explicit-formula identity W ≈ genuineLamSeq (explicit hypothesis; positivity & identity open).
#print axioms Square.normAutocorr_positivity_iff_RH
-- WeilPrimeShift/Operator: the direct point-value operator route — N(q) Haar-core normalized dilation,
-- the correctly-weighted adjoint law N(1/n)=n·N(n) (proved on the actual autocorr), and primePlaceOp
-- whose finite quadratic readback = weilPrimePart_normAutocorr_collapsed. No primeGram/vFrom/vHat, no PSD.
#print axioms Square.Nop_hi
#print axioms Square.Nop_lo
#print axioms Square.Nop_adjoint
#print axioms Square.Nop_adjoint_ac
#print axioms Square.primePlaceOp_eq_weilPrimeTerm
#print axioms Square.primePlaceOp_readback
#print axioms Square.primePlaceOp_readback_collapsed
-- WeilPrimeShift/HaarForm: the GENUINE two-test finite-prime Haar bilinear form. H_q(f,g)=∫f(q/t)g(1/t)d×t,
-- H_q(g,g)=autocorr; the two-test reciprocal/adjoint law H_q(f,g)=H_{1/q}(g,f) (generalizing autocorr_recip
-- to two tests); B_q(f,g)=q^{-1}B_{1/q}(g,f); P_m(f,g)=P_m(g,f) two-input symmetry; diagonal = primePlaceOp;
-- fold = primePlaceOp_readback_collapsed. No primeGram/vFrom/vHat, no PSD.
#print axioms Square.Ps_ofQ2
#print axioms Square.dilDN_pt_zero2
#print axioms Square.P1n_pt_zero2
#print axioms Square.left_DN_window_vanish2
#print axioms Square.right_I1n_window_vanish2
#print axioms Square.core_integrand_agree2
#print axioms Square.HForm_diag
#print axioms Square.HForm_recip_core
#print axioms Square.HForm_recip
#print axioms Square.Pn_pt_zero_degen
#print axioms Square.Pn_window_vanish_degen
#print axioms Square.HForm_recip_all
#print axioms Square.ofQ_recip_one
#print axioms Square.normWeight_recip_lo
#print axioms Square.normWeight_recip_hi
#print axioms Square.BForm_adjoint_all
#print axioms Square.BForm_adjoint_swap_all
#print axioms Square.PForm_symm_all
#print axioms Square.PrimeForm_symm
#print axioms Square.HForm_diag_acPtC
#print axioms Square.PForm_diag
#print axioms Square.PrimeForm_diag_weilPrimePart
#print axioms Square.PrimeForm_diag_collapsed
-- WeilPrimeShift/HaarForm biadditivity + fixed geometry: haarIntegral additive over L2Test.add,
-- HForm/BForm/PForm/PrimeForm biadditive in both arguments; PrimeFormG over a fixed HaarGeom.
#print axioms Square.haarIntegral_L2add
#print axioms Square.HForm_add_left
#print axioms Square.HForm_add_right
#print axioms Square.Radd_add_add_comm
#print axioms Square.BForm_add_left
#print axioms Square.BForm_add_right
#print axioms Square.PForm_add_left
#print axioms Square.PForm_add_right
#print axioms Square.PrimeForm_add_left
#print axioms Square.PrimeForm_add_right
#print axioms Square.PrimeFormG_symm
#print axioms Square.PrimeFormG_add_left
#print axioms Square.PrimeFormG_add_right
-- WeilPrimeShift/HaarForm: n=1 reciprocity + the CONSTRUCTED two-input Archimedean CONSTANT term
-- (constructed from Rlog4pic/Rgamma_h, symmetric + biadditive, diagonal = weilArchConst).
#print axioms Square.HForm_recip_one
#print axioms Square.ArchConstForm_symm
#print axioms Square.ArchConstForm_add_left
#print axioms Square.ArchConstForm_add_right
#print axioms Square.ArchConstForm_diag
-- WeilInvSqrt: the certified x^{-1/2} weight test (RsqrtRealPos unique root, radicand bounds,
-- N/2-Lipschitz via difference-of-squares, rational readback to normWeight).
#print axioms Square.RsqrtRealPos_unique
#print axioms Square.isqRad_congr
#print axioms Square.qnum_pos_of_one_le
#print axioms Square.isqU_seq_le
#print axioms Square.isqU_le_B
#print axioms Square.isqRad_le_one
#print axioms Square.isqRad_ge_invB
#print axioms Square.one_le_N_invB
#print axioms Square.one_le_N_isqRad
#print axioms Square.isqRad_scale
#print axioms Square.invSqrtF_sq
#print axioms Square.invSqrtF_nonneg
#print axioms Square.invSqrtF_le_one
#print axioms Square.invSqrtF_ge_invN
#print axioms Square.invSqrtF_congr
#print axioms Square.invSqrtF_lipschitz
#print axioms Square.invSqrtF_ofQ
#print axioms Square.invSqrtF_one
-- WeilCrossF: the continuous normalized cross-correlation F_{f,g}=x^{-1/2}H_{f,g} — bridge to HForm,
-- readback to BForm, value-at-1 symmetry, real-x compact support, biadditive values.
#print axioms Square.HcrossTest_diag
#print axioms Square.HForm_eq_HcrossTest
#print axioms Square.FTest_ofQ
#print axioms Square.FTest_one_symm
#print axioms Square.qBandQ_ge_real
#print axioms Square.crossIntegrand_pt_zero
#print axioms Square.HcrossTest_high_vanish
#print axioms Square.FTest_high_vanish
#print axioms Square.HcrossTest_add_left
#print axioms Square.HcrossTest_add_right
#print axioms Square.FTest_add_left
#print axioms Square.FTest_add_right
-- WeilPoleForm: ClosedGeom/CoreTest typed domain + the CONSTRUCTED improper PoleForm with proved
-- block decay (vanishing past the support bound, width·sup before it).
#print axioms Square.coreTest_add
#print axioms Square.closedGeom_Bd0
#print axioms Square.FTestG_high_vanish
#print axioms Square.poleIntegrand_high_vanish
#print axioms Square.poleK_den
#print axioms Square.poleK_num
#print axioms Square.poleK_early
#print axioms Square.poleDecay
-- WeilPoleForm pre-seal wrappers over the fixed geometry.
#print axioms Square.FTestG_one_symm
#print axioms Square.FTestG_ofQ
#print axioms Square.FTestG_add_left
#print axioms Square.FTestG_add_right
-- WeilArchNum: the archimedean-tail numerator N = F+F♯−2F(1)/x (endpoint vanishing + rate,
-- retained-tail form past the support bound) and the split kernels.
#print axioms Square.sub_shift_iso
#print axioms Square.add_shift_iso
#print axioms Square.Rle_self_qClampQ
#print axioms Square.clampedInv_le_ofQ_inv_of_ge
#print axioms Square.twoFone_bound
#print axioms Square.archNum_f
#print axioms Square.archNum_one_zero
#print axioms Square.archNum_abs_le_dist_one
#print axioms Square.archNum_past
-- WeilArchTailFar: the regular/far improper parts with PROVED decay (early width·sup, late
-- retained-tail product bound under the computed K = M·Bd² + 2M_F).
#print axioms Square.K_early_general
#print axioms Square.archKl_den
#print axioms Square.archKl_num
#print axioms Square.archK_den
#print axioms Square.archK_num
#print axioms Square.archK_early
#print axioms Square.archK_late
#print axioms Square.blockPoint_ge
#print axioms Square.blockPoint_succ_ge
#print axioms Square.archNum_late_bound
#print axioms Square.archRegDecay
#print axioms Square.archFarDecay
-- WeilArchNear: the x=1 lower-end improper limit — strip identity, quotient cap N.L, geometric
-- telescope, Bishop regularity, ArchNearPart = Rlim of the honest truncations.
#print axioms Square.dyQ_den
#print axioms Square.dyQ_num
#print axioms Square.nearLo_den
#print axioms Square.nearW_den
#print axioms Square.nearW_num
#print axioms Square.nearIntegrand_cap
#print axioms Square.sub_one_ge_of_ge_add
#print axioms Square.affine_ge_lo
#print axioms Square.dyQ_succ_le
#print axioms Square.dyQ_le_nearW
#print axioms Square.nearW_sub_num
#print axioms Square.nearLo_step_eq
#print axioms Square.nearW_step_eq
#print axioms Square.nearIntegrand_step_agree
#print axioms Square.nearRest_eq
#print axioms Square.Radd_sub_cancel_right
#print axioms Square.nearJ_split
#print axioms Square.nearJ_succ_diff
#print axioms Square.nearCN_ge
#print axioms Square.nearJ_succ_bound
#print axioms Square.Rabs_sub_le_tri
#print axioms Square.dy_halve
#print axioms Square.nearJ_tel
#print axioms Square.nearJ_diff_le
#print axioms Square.nearC_den
#print axioms Square.nearC_addend_le
#print axioms Square.nearC_le
#print axioms Square.nearX_bound
#print axioms Square.nearX_RReg
-- ClosedWeilBilin: the COMPLETE closed Weil form (ArchTailForm assembly, ClosedNormCtx, the
-- constructed slot with NO free poles/archTail) and THE ACCEPTANCE THEOREM closedWeilBilin_diag.
#print axioms Square.normCtx_core
#print axioms Square.closedWeilBilin_diag
-- WeilCrossF pre-seal equation lemmas.
#print axioms Square.FTest_f
#print axioms Square.HcrossTest_f
-- WeilInvSqrtTwo: the TWO-SIDED x^{-1/2} weight on [c,B] (floor c, not 1) — radicand bounds, scale,
-- (N/2)(1/c)^2-Lipschitz, unique-root congruence, two-sided rational readback to normWeight.
#print axioms Square.twoRad_congr
#print axioms Square.twoU_seq_le
#print axioms Square.twoU_le_B
#print axioms Square.twoRad_le_invc
#print axioms Square.twoRad_ge_invB
#print axioms Square.one_le_N_twoRad
#print axioms Square.twoRad_scale
#print axioms Square.invSqrtTwoF_sq
#print axioms Square.invSqrtTwoF_nonneg
#print axioms Square.invSqrtTwoF_le
#print axioms Square.invSqrtTwoF_ge_invN
#print axioms Square.invSqrtTwoF_congr
#print axioms Square.invSqrtTwoF_lipschitz
#print axioms Square.invSqrtTwoF_ofQ
-- WeilCrossFTwo: the two-sided normalized correlation F⁺ = x^{-1/2}H on [c,B]: two-sided readback
-- to BForm, agreement with the high-side FTest on [1,B], low-side compact support (x ≤ b·a), and the
-- integer-scale reciprocal transpose (1/n)F⁺_{f,g}(1/n) = F⁺_{g,f}(n).
#print axioms Square.FTwo_ofQ
#print axioms Square.twoRad_eq_isqRad_high
#print axioms Square.invSqrtTwoF_eq_high
#print axioms Square.FTwo_eq_FTest_high
#print axioms Square.crossIntegrand_low_pt_zero
#print axioms Square.HcrossTest_low_vanish
#print axioms Square.FTwo_low_vanish
#print axioms Square.FTwo_recip_int
-- WeilDensity: |x − ofQ (x.seq n)| ≤ 1/(n+1); real-level linear bound ⟹ Req; THE DENSITY PRINCIPLE
-- (rational-Lipschitz functions agreeing on the rationals of a band agree on the band).
#print axioms Square.Rabs_sub_ofQ_seq_le
#print axioms Square.Qneg_Qsub_eq
#print axioms Square.Req_of_Rabs_le_lin
#print axioms Square.Rabs_sub_tri
#print axioms Square.Qle_num_cap
#print axioms Square.Req_of_lipschitz_dense
-- WeilRecipQ: two-test reciprocity H_q(f,g) = H_{1/q}(g,f) at EVERY RATIONAL scale q ≥ 1 (no overlap
-- hypothesis): rational-scale helpers, pointwise/window vanishing, the Route-D core, scale congruence.
#print axioms Square.Qmul_Qinv_mul_gen
#print axioms Square.q_mul_inv_q
#print axioms Square.inv_q_mul_le
#print axioms Square.qnum_gt_den_of_one_lt
#print axioms Square.w1_num_pos_gen
#print axioms Square.CoreStrict_gen
#print axioms Square.qlow_engine_gen
#print axioms Square.Qle_of_one_lt
#print axioms Square.dilDN_pt_zero_Q
#print axioms Square.P1n_pt_zero_Q
#print axioms Square.Pn_pt_zero_degen_Q
#print axioms Square.left_DN_window_vanish_Q
#print axioms Square.right_I1n_window_vanish_Q
#print axioms Square.Pn_window_vanish_degen_Q
#print axioms Square.core_integrand_agree_Q
#print axioms Square.HForm_recip_core_Q
#print axioms Square.HForm_congr_scale
#print axioms Square.HForm_recip_all_Q
-- WeilRecipReal: the REAL-scale cross-correlation law H_{f,g}(x) ≈ H_{g,f}(1/x) by density, the real
-- radicand/weight identities at 1/x, and the real reciprocal transpose x⁻¹·F⁺_{f,g}(1/x) ≈ F⁺_{g,f}(x).
#print axioms Square.Hcross_recip_lip
#print axioms Square.Hcross_recip_real
#print axioms Square.twoRad_recip
#print axioms Square.invSqrtTwoF_recip
#print axioms Square.FTwo_recip_real
-- WeilRecipCanon: the rational layer (normWeight(q⁻¹)=q·normWeight(q) INDEPENDENTLY proved; B_{1/q}(f,g)
-- = q·B_q(g,f) and q⁻¹·F⁺_{f,g}(q⁻¹)=F⁺_{g,f}(q) at EVERY rational q ≥ 1) and the CANONICAL band from
-- NormCtx alone (B = X+1, c = 1/B with c·B = 1 exactly, c ≤ b·a from hband_lo): FCanon_recip_real.
#print axioms Square.qinv_qinv
#print axioms Square.qinv_le_one
#print axioms Square.qsq_mul_qinv
#print axioms Square.normWeight_recip_Q
#print axioms Square.BForm_adjoint_swap_all_Q
#print axioms Square.FTwo_recip_Q
#print axioms Square.canonB_den
#print axioms Square.canonB_num
#print axioms Square.canonB_one
#print axioms Square.canonC_num
#print axioms Square.canonC_den
#print axioms Square.canonC_mul_B
#print axioms Square.canonC_mul_B_le
#print axioms Square.canonC_le_one
#print axioms Square.canonC_le_B
#print axioms Square.canonB_le_N
#print axioms Square.canonB_le_S
#print axioms Square.canonC_le_ba
#print axioms Square.FCanon_recip_Q
#print axioms Square.FCanon_recip_real
-- IntegralCell: the LEFT-endpoint Lipschitz cell estimate |∫_{[a,a+w]}φ − w·φ(a)| ≤ w·(L·w) and the
-- iterated split of the certified integral along ANY rational partition (increasing and decreasing).
#print axioms Square.Rsub_add_cancel_left
#print axioms Square.affineMap_sub_lo
#print axioms Square.unit_abs_le_one
#print axioms Square.diffTest_f
#print axioms Square.diffTest_integral
#print axioms Square.cell_est_left
#print axioms Square.Qle_of_Qlt_loc
#print axioms Square.Qadd_Qsub_cancel
#print axioms Square.Qsub_Qsub_Qsub
#print axioms Square.partition_split
#print axioms Square.partition_split_dec
#print axioms Square.genSum_Rsub_cells
#print axioms Square.genSum_Rabs_le
#print axioms Square.genSum_const_eq
#print axioms Square.genSum_le_const
#print axioms Square.Qinv_lt_of_lt
-- IntegralInversionGeom: the uniform partition y_i = 1 + i·h of [1,B] (h = (B−1)/(N+1)), its inverse
-- image x_i = 1/y_i, and the KEY identity x_i − x_{i+1} = h·x_i·x_{i+1}.
#print axioms Square.Qlt_of_Qsub_num_pos
#print axioms Square.Qlt_self_add_pos
#print axioms Square.Qsub_add_self_eq
#print axioms Square.invH_den
#print axioms Square.invH_num
#print axioms Square.invY_den
#print axioms Square.invY_ge_one
#print axioms Square.invY_num
#print axioms Square.invY_step_lt
#print axioms Square.invY_step_sub
#print axioms Square.invY_zero_lt_step
#print axioms Square.invY_zero_lt
#print axioms Square.invY_eq_zero_id
#print axioms Square.invY_eq_step_id
#print axioms Square.invY_eq
#print axioms Square.invY_top
#print axioms Square.invX_den
#print axioms Square.invX_num
#print axioms Square.invX_nonneg
#print axioms Square.invX_le_one
#print axioms Square.invX_zero_eq
#print axioms Square.invX_step_lt
#print axioms Square.invX_zero_lt
#print axioms Square.invX_sub_eq
#print axioms Square.invX_sub_nonneg
#print axioms Square.invX_prod_le_one
#print axioms Square.invX_sub_le_h
-- IntegralInversion: INVERSION UNDER THE CERTIFIED INTEGRAL ∫_{1/B}^{1} φ = ∫_1^B φ(1/y)·y⁻² dy
-- (riemannIntegralI_inversion) — both sides compared with the same rational non-uniform sum, cell by cell.
#print axioms Square.invPullTest_f
#print axioms Square.invPullTest_ofQ
#print axioms Square.hxx_sub_id
#print axioms Square.invC_eq
#print axioms Square.invV_den
#print axioms Square.invV_nonneg
#print axioms Square.invV_le_h
#print axioms Square.invC_den
#print axioms Square.invC_rep_nonneg
#print axioms Square.invC_rep_le
#print axioms Square.hR_nonneg
#print axioms Square.xR_nonneg
#print axioms Square.xR_le_one
#print axioms Square.vR_nonneg
#print axioms Square.vR_le_hR
#print axioms Square.xR_sub
#print axioms Square.cell_T1
#print axioms Square.cell_T3
#print axioms Square.pR_nonneg
#print axioms Square.pR_le_hR
#print axioms Square.hpsi_eq
#print axioms Square.pR_sub_vR
#print axioms Square.pR_sub_vR_abs_le
#print axioms Square.cell_T2
#print axioms Square.invE_den
#print axioms Square.invE_num
#print axioms Square.cellBoundQ_eq
#print axioms Square.cellBound_real
#print axioms Square.cell_total
#print axioms Square.psi_window_split
#print axioms Square.phi_window_split
#print axioms Square.sum_diff_le
#print axioms Square.invG_den
#print axioms Square.invG_num
#print axioms Square.tail_eq
#print axioms Square.tail_le
#print axioms Square.B_num_pos
#print axioms Square.psi_window_congr
#print axioms Square.phi_window_congr
#print axioms Square.riemannIntegralI_inversion
-- ImproperFinite: the improper integral of an integrand vanishing past M is the finite window [1, M+1]
-- (partial sums stabilize; Bishop limit of an eventually constant sequence; integer-partition split).
#print axioms Square.genSum_stable
#print axioms Square.riemannIntegralI_window_zero
#print axioms Square.integralTerm_vanish
#print axioms Square.intPt_den
#print axioms Square.intPt_zero_lt
#print axioms Square.intPt_step_le
#print axioms Square.intPt_step_sub
#print axioms Square.intPt_top_sub
#print axioms Square.intPt_zero_eq
#print axioms Square.intPt_cell_eq
#print axioms Square.intPt_window_eq
#print axioms Square.window_eq_genSum_terms
#print axioms Square.RReg_const_fin
#print axioms Square.improperIntegral1_eq_finite
-- WeilMellinPole: THE INDEPENDENTLY DEFINED MELLIN POLE TERM ∫₀^∞ F⁺(x)(1+1/x)dx = low [1/B,1] + high [1,B]
-- windows, THE FOLDING THEOREM MellinPole_eq_PoleForm (inversion + real transpose + finite collapse),
-- the SUBSTANTIVE PoleForm_diag, and the slot with the independent pole field (closedWeilBilin_diag_mellin).
#print axioms Square.canonB_gt_one
#print axioms Square.lowInt_f
#print axioms Square.highInt_f
#print axioms Square.poleDens_f
#print axioms Square.FCanon_low_vanish
#print axioms Square.FCanon_high_vanish
#print axioms Square.Rinv_ge_ofQ_inv
#print axioms Square.Rinv_Rinv_eq
#print axioms Square.clampedInv_recip_eq
#print axioms Square.Rmul_clampedInv_one
#print axioms Square.fold_pointwise
#print axioms Square.affine_one_lo
#print axioms Square.affine_one_hi
#print axioms Square.MellinLow_fold
#print axioms Square.poleIntegrand_f
#print axioms Square.FTestG_geom_f
#print axioms Square.MellinHigh_sum
#print axioms Square.poleIntegrand_term_vanish
#print axioms Square.PoleForm_eq_finite
#print axioms Square.pole_window_congr
#print axioms Square.MellinPole_eq_PoleForm
#print axioms Square.PoleForm_diag
#print axioms Square.closedWeilBilin_diag_mellin
-- WeilArchKern: the UNSPLIT kernel 1/max(x − x⁻¹, c) as an L2Test, inertness/caps, and THE PARTIAL-FRACTION
-- IDENTITY 1/(x − x⁻¹) = ½(1/(x−1) + 1/(x+1)) proved directly on x − 1 ≥ c.
#print axioms Square.innerXm_congr
#print axioms Square.innerXm_lip
#print axioms Square.archKernFull_f
#print axioms Square.sub_one_le_innerXm
#print axioms Square.innerXm_ge_c
#print axioms Square.archKernFull_cap
#print axioms Square.archKernFull_le_inv
#print axioms Square.innerXm_mul
#print axioms Square.inv_sum_mul_two
#print axioms Square.inv_eq_half_of
#print axioms Square.archKernFull_partial
-- WeilArchNumC: the numerator N⁺ from the two-sided F⁺ and its agreement with archNum on ALL x ≥ 1.
#print axioms Square.Rle_ofQ_qBandQ
#print axioms Square.twoRad_eq_isqRad_ge_one
#print axioms Square.invSqrtTwoF_eq_ge_one
#print axioms Square.FCanon_eq_FTestG_ge_one
#print axioms Square.twoFoneC_bound
#print axioms Square.archNumC_f
#print axioms Square.archNumC_eq_archNum
#print axioms Square.archNumC_one_zero
#print axioms Square.archNumC_abs_le_dist_one
#print axioms Square.archNumC_late_bound
-- WeilShiftTest: translation of tests and THE WINDOW TRANSLATION ∫_{[a,w]} φ(·+δ) = ∫_{[a+δ,w]} φ.
#print axioms Square.add_shift_iso_gen
#print axioms Square.shiftTest_f
#print axioms Square.affineMap_add_shift
#print axioms Square.shift_window
#print axioms Square.shiftTest_comp
#print axioms Square.shiftTest_congr_shift
#print axioms Square.integralTerm_shift_one
-- WeilArchTrunc: the shifted full-kernel family, its UNIFORM block decay (constant independent of k and δ),
-- and the honest truncation archTrunc k = ∫_{1+2⁻ᵏ}^{∞} N⁺/(x − x⁻¹) (improper).
#print axioms Square.fullInt_f
#print axioms Square.truncInt_f
#print axioms Square.archKC_den
#print axioms Square.archKC_num
#print axioms Square.archKC_early
#print axioms Square.archKC_late
#print axioms Square.qinv_nat_le_one
#print axioms Square.late_product_eq
#print axioms Square.truncDecay
-- WeilArchLimit: certificate irrelevance, THE SAME-CONSTANT IMPROPER SPLIT, the far-window rate, the step
-- identity, the Cauchy rate CNC/2ᵏ, and THE INDEPENDENT UNSPLIT ArchIntegral (lower-end Bishop limit).
#print axioms Square.improperIntegral1_certif_irrel
#print axioms Square.archKernFull_inert_pair
#print axioms Square.genSum_terms_eq_window
#print axioms Square.q_one_add_nat
#print axioms Square.q_addsub_left
#print axioms Square.q_addsub_right
#print axioms Square.split_partial_identity
#print axioms Square.rate_le_of_ge
#print axioms Square.improper_split_shift
#print axioms Square.improperIntegral1_congr_terms
#print axioms Square.integralTerm_congr_ge
#print axioms Square.fullInt_cap
#print axioms Square.le_Bd_num_of_lt
#print axioms Square.archCF_ge_Kl
#print axioms Square.archCF_ge_MB
#print axioms Square.qinv_block_le
#print axioms Square.qCF_mul_inv
#print axioms Square.truncFar
#print axioms Square.dyQ_add_le
#print axioms Square.dyQ_le_one
#print axioms Square.dyQ_sub_num_pos
#print axioms Square.dyQ_sub_le
#print axioms Square.shifted_pt_facts
#print axioms Square.archTrunc_step
#print axioms Square.archCNC_ge
#print axioms Square.archTrunc_diff_le
#print axioms Square.archC_den
#print axioms Square.archC_addend_le
#print axioms Square.archC_le
#print axioms Square.archX_bound
#print axioms Square.archX_RReg
-- WeilArchReconcile: decay monotone in K / block-wise congruent / integer shift, SCHEDULE INDEPENDENCE of the
-- improper integral (telescoped tail), the half-scaling certificate.
#print axioms Square.decay_mono
#print axioms Square.decay_of_terms_congr
#print axioms Square.q_block_shift_le
#print axioms Square.decay_shift_one
#print axioms Square.digammaTailQ_le_inv
#print axioms Square.genSum_sched_close
#print axioms Square.Radd_Rsub_cancel_arch
#print axioms Square.Rlim_sched_indep
#print axioms Square.improperIntegral1_sched
#print axioms Square.half_lip
#print axioms Square.half_fc
-- WeilArchRegSplit: the regular-kernel family, uniform decay, far rate, and the split of ∫₁^∞ N⁺/(x+1) at 2.
#print axioms Square.regInt_f
#print axioms Square.archKernReg_le_inv
#print axioms Square.archKernReg_le_one
#print axioms Square.archKernReg_nonneg
#print axioms Square.regDecay
#print axioms Square.regFar
#print axioms Square.reg_split_two
-- WeilArchIdent: THE IDENTIFICATION ArchIntegral = ArchTailForm — per-k identity (strip partial fractions,
-- far translation, regular chain, assembly) and the k → ∞ passage against the nearCN schedule.
#print axioms Square.archKR_den
#print axioms Square.archKR_num
#print axioms Square.archKF_den
#print axioms Square.archKF_num
#print axioms Square.archKB_den
#print axioms Square.archKB_num
#print axioms Square.archKC_le_KB
#print axioms Square.archKR_le_KB
#print axioms Square.archKF_le_KB
#print axioms Square.arch_assemble
#print axioms Square.arch_limit_diff
#print axioms Square.halfTest_f
#print axioms Square.integralTerm_half
#print axioms Square.integralTerm_addTest
#print axioms Square.q_double_mul
#print axioms Square.q_half_double
#print axioms Square.decay_add
#print axioms Square.decay_half
#print axioms Square.nearIntC_f
#print axioms Square.farTranslate_eq
#print axioms Square.farTranslate_terms
#print axioms Square.regZero_eq
#print axioms Square.regZero_terms
#print axioms Square.decay_farTranslate
#print axioms Square.decay_farIntegrand
#print axioms Square.decay_B
#print axioms Square.decay_regIntegrand_KB
#print axioms Square.decay_regIntegrand_KC
#print axioms Square.archK2_den
#print axioms Square.archK2_num
#print axioms Square.archKB_le_K2
#print axioms Square.archKC_le_K2
#print axioms Square.decay_weaken_L
#print axioms Square.strip_width_pos
#print axioms Square.strip_width_le_one
#print axioms Square.strip_width_eq_nearW
#print axioms Square.fullInt_partial_pt
#print axioms Square.strip_partial
#print axioms Square.near_readback
#print axioms Square.trunc_split_two
#print axioms Square.strip_readback
#print axioms Square.far_partial_pt
#print axioms Square.decay_farA_KB
#print axioms Square.decay_farB_KB
#print axioms Square.farA_terms
#print axioms Square.farB_f
#print axioms Square.decay_farB_KC
#print axioms Square.decay_farA_K2
#print axioms Square.decay_farB_K2
#print axioms Square.decay_farAB_K2
#print axioms Square.decay_farH_K2
#print axioms Square.far_half_sum
#print axioms Square.farA_eq_Far
#print axioms Square.far_window
#print axioms Square.reg_window_split
#print axioms Square.regZero_pt
#print axioms Square.reg_chain
#print axioms Square.archTrunc_ident
#print axioms Square.archE_bound
#print axioms Square.nearJ_limit_rate
#print axioms Square.half_le_self
#print axioms Square.dy_mul_le_cap
#print axioms Square.q_add_same_den
#print axioms Square.q_den_mono
#print axioms Square.succ_le_two_pow_of_le
#print axioms Square.ArchIntegral_eq_ArchTailForm
-- WeilArchSemantic: the SUBSTANTIVE ArchTailForm_diag, the semantic slot (both hard fields independent),
-- and closedWeilBilin_diag_semantic with NO component-level reflexivity for either hard field.
#print axioms Square.ArchTailForm_diag
#print axioms Square.closedWeilBilin_diag_semantic
-- WeilFormLaws: the improper bricks improper_congr_sched / improper_add_sched (block-wise congruent/additive
-- integrands at DIFFERENT sealed constants and moduli) and PoleForm_symm / add_left / add_right.
#print axioms Square.improper_congr_sched
#print axioms Square.improper_add_sched
#print axioms Square.poleIntegrand_symm_pt
#print axioms Square.poleIntegrand_add_left_pt
#print axioms Square.poleIntegrand_add_right_pt
#print axioms Square.poleDecayAt
#print axioms Square.integralTerm_congr_all
#print axioms Square.PoleForm_symm
#print axioms Square.PoleForm_add_left
#print axioms Square.PoleForm_add_right
-- WeilArchTailLaws: archNum pointwise symmetry/biadditivity, Reg/Far laws (improper bricks), Near laws through the
-- CN/2ᵏ rates (different nearCN schedules reconciled), ArchTailForm_symm / add_left / add_right.
#print axioms Square.archNum_symm_pt
#print axioms Square.archNum_add_alg
#print axioms Square.archNum_add_left_pt
#print axioms Square.archNum_add_right_pt
#print axioms Square.archRegIntegrand_f
#print axioms Square.archFarIntegrand_f
#print axioms Square.archRegDecayAt
#print axioms Square.archFarDecayAt
#print axioms Square.ArchRegPart_symm
#print axioms Square.ArchFarPart_symm
#print axioms Square.ArchRegPart_add_left
#print axioms Square.ArchRegPart_add_right
#print axioms Square.ArchFarPart_add_left
#print axioms Square.ArchFarPart_add_right
#print axioms Square.nearIntegrand_f
#print axioms Square.nearJ_symm
#print axioms Square.nearJ_add_left
#print axioms Square.nearJ_add_right
#print axioms Square.rate_two_pow_to_lin
#print axioms Square.ArchNearPart_symm
#print axioms Square.near_add_tri
#print axioms Square.ArchNearPart_add_left
#print axioms Square.ArchNearPart_add_right
#print axioms Square.tail_add_alg
#print axioms Square.ArchTailForm_symm
#print axioms Square.ArchTailForm_add_left
#print axioms Square.ArchTailForm_add_right
-- WeilCoupledForm (AC-09–AC-13): ArchForm = PoleForm − (ArchConstForm + ArchTailForm), CoupledForm = ArchForm − PrimeForm,
-- their symmetry/biadditivity, THE EXACT IDENTITY CoupledForm = closedWeilBilin, the diagonal semantic readback.
#print axioms Square.ArchForm_symm
#print axioms Square.arch_add_alg
#print axioms Square.ArchForm_add_left
#print axioms Square.ArchForm_add_right
#print axioms Square.CoupledForm_symm
#print axioms Square.coupled_add_alg
#print axioms Square.CoupledForm_add_left
#print axioms Square.CoupledForm_add_right
#print axioms Square.coupled_ident_alg
#print axioms Square.CoupledForm_eq_closedWeilBilin
#print axioms Square.CoupledForm_diag_semantic
#print axioms Square.CoupledForm_diag_components
-- WeilDominance: the fixed core ClosedCore C, the DEFINED (not proved) predicate CurrentArchDominatesPrime, and
-- the algebraic sign equivalences PrimeForm ≤ ArchForm ⟺ 0 ≤ CoupledForm ⟺ 0 ≤ closedWeilBilin (no PSD claim).
#print axioms Square.dominance_iff_coupled_nonneg
#print axioms Square.CurrentArchDominatesPrime_iff
#print axioms Square.CurrentArchDominatesPrime_iff_closed
-- AtlasIncidence: the physical Atlas operator M = −I + J₃⊗I₈ + I₃⊗J₈ on the 3×8 fiber PROVED equal to the sourced
-- block formula (O+2)I − T·Π_T − O·Π_O and to BᵀB − I for the genuine K_{3,8} incidence; cycle space = −1
-- eigenspace; cut action; the square-root-free compression Q_M(a⊕b) = 56Σa² + 6Σb² + 3(Σb)² ≥ 0 (Σa = 0).
#print axioms Square.RsumN_smul_ai
#print axioms Square.RsumN_smul_right_ai
#print axioms Square.RsumN_indicator_ai
#print axioms Square.RsumN_add_block_ai
#print axioms Square.RsumN_block38_ai
#print axioms Square.RsumN_swap_ai
#print axioms Square.Rsub_Rsub_eq
#print axioms Square.three_piT
#print axioms Square.eight_piO
#print axioms Square.ten_sub_three_sub_eight
#print axioms Square.atlasOp_sourced
#print axioms Square.incBv_left
#print axioms Square.incBv_right
#print axioms Square.incBt_eq
#print axioms Square.atlasOp_eq_BtB
#print axioms Square.atlasOp_cycle
#print axioms Square.rowSum_cut
#print axioms Square.colSum_cut
#print axioms Square.Radd_regroup
#print axioms Square.eight_sub_one
#print axioms Square.three_sub_one
#print axioms Square.RofNat_eq
#print axioms Square.cut_regroup
#print axioms Square.atlasOp_cut
#print axioms Square.x_mul_lin
#print axioms Square.y_mul_lin
#print axioms Square.two_add_seven
#print axioms Square.cut_term_expand
#print axioms Square.cut_inner_sum
#print axioms Square.cut_outer_sum
#print axioms Square.Qform_cut
#print axioms Square.Qform_cut_nonneg
-- WeilStageFalsify: the explicit tent core test, the explicit context C₀ (a=1/2, b=2/3, X=2), and the certified
-- lower bound H₂(tent,tent) ≥ 1/176 on C₀ (window split + constant minorant on [12/11, 4/3]).
#print axioms Square.qClampQ_eq_of_le
#print axioms Square.tentRaw_le_one
#print axioms Square.tentRaw_lip
#print axioms Square.tentRaw_congr
#print axioms Square.tentTest43_f
#print axioms Square.tent_vanish_of_far
#print axioms Square.tent_vanish_high
#print axioms Square.tent_vanish_low
#print axioms Square.tent_core
#print axioms Square.tent_ge_of_close
#print axioms Square.tent_ge_eighth
#print axioms Square.tent_ge_quarter
#print axioms Square.tent_nonneg
#print axioms Square.HForm_tent_unfold
#print axioms Square.tent_integrand_f
#print axioms Square.tentG_nonneg
#print axioms Square.tentG_ge
#print axioms Square.tentInt_f
#print axioms Square.HForm_tent_ge
-- WeilStageReport: THE EXACT UNCANCELLED TERM — PrimeForm C₀.X tent tent > 0 (certified), hence no cut-space
-- stage (Σa = 0) of a path-independent Atlas coefficient map can read back −PrimeForm on (C₀, tent).
#print axioms Square.Pos_logN_two
#print axioms Square.Pos_normWeight_two
#print axioms Square.Pos_H2_tent
#print axioms Square.Pos_B2_tent
#print axioms Square.reflect_tent_nonneg
#print axioms Square.Bhalf_tent_nonneg
#print axioms Square.PForm_one_tent_pos
#print axioms Square.prime_component_positive
#print axioms Square.no_cut_stage_reads_prime
-- AtlasBundle: the canonical cut/cycle decomposition a_v = row/8 − total/24, b_v = col/3, P_cut, R_cyc (∈ ker B),
-- orthogonality, additivity of M, the bilinear cut formula, and THE BUNDLED ALL-PAIRS READBACK
-- ⟨v, Mw⟩ = 56Σa_v a_w + 6Σb_v b_w + 3(Σb_v)(Σb_w) − ⟨R_cyc v, R_cyc w⟩ (atlas_bilinear_readback).
#print axioms Square.pairF_congr
#print axioms Square.pairF_comm
#print axioms Square.pairF_add_right
#print axioms Square.pairF_neg_right
#print axioms Square.totalF_cols
#print axioms Square.aOf_sum_zero
#print axioms Square.bOf_sum
#print axioms Square.decomp_pt
#print axioms Square.eight_aOf
#print axioms Square.three_bOf
#print axioms Square.Rcyc_row_zero
#print axioms Square.Rcyc_col_zero
#print axioms Square.Rcyc_isCycle
#print axioms Square.pairF_cut_cycle
#print axioms Square.rowSum_add
#print axioms Square.colSum_add
#print axioms Square.atlasOp_add
#print axioms Square.rowSum_congr
#print axioms Square.colSum_congr
#print axioms Square.atlasOp_congr
#print axioms Square.x_mul_lin2
#print axioms Square.cut_term_expand2
#print axioms Square.cut_inner_sum2
#print axioms Square.cut_outer_sum2
#print axioms Square.pairF_cut_Mcut
#print axioms Square.atlasOp_cut_is_cut
#print axioms Square.atlas_bilinear_readback
-- WeilRecipReal: the REAL-scale law by density — H_{f,g}(x) ≈ H_{g,f}(1/x), the weight identity
-- x⁻¹·w(1/x) = w(x) (unique root), and x⁻¹·F⁺_{f,g}(1/x) ≈ F⁺_{g,f}(x) on real 1 ≤ x ≤ hi (item 2).
#print axioms Square.Hcross_recip_lip
#print axioms Square.Hcross_recip_real
#print axioms Square.twoRad_recip
#print axioms Square.invSqrtTwoF_recip
#print axioms Square.FTwo_recip_real
-- AtlasChannels: rank-one fiber vectors s⊗t, the M-pairing formula ⟨s⊗t, M(s'⊗t')⟩ (pairF_tens_M), and the
-- address-indexed cut/cycle channels p_ℓ(x) = x·(𝟙⊗(2/3)e_ℓ), q_{d,ℓ}(x) = x·((e_d−e_{d+1})⊗(e_ℓ−e_{ℓ+1})) with
-- [p,p]_M = 4xy, [q,q]_M = −4xy, [p,q]_M = [q,p]_M = 0 at EVERY valid address (address-independent readback).
#print axioms Square.Rzero_mul_ch
#print axioms Square.mul4_swap_ch
#print axioms Square.mul4_swap2_ch
#print axioms Square.rowSum_tens
#print axioms Square.colSum_tens
#print axioms Square.atlasOp_tens
#print axioms Square.tens_pt_expand
#print axioms Square.pairF_tens_M
#print axioms Square.RsumN_indic
#print axioms Square.RsumN_smul_indic
#print axioms Square.smul_indic_sq_pt
#print axioms Square.dotN_smul_indic
#print axioms Square.RsumN_sg
#print axioms Square.sg_sq_pt
#print axioms Square.dotN_sg
#print axioms Square.RsumN_smul_sg
#print axioms Square.dotN_smul_sg
#print axioms Square.dotN_const_smul_sg
#print axioms Square.dotN_smul_sg_const
#print axioms Square.succ_mod3
#print axioms Square.succ_mod8
#print axioms Square.pp_const_collapse
#print axioms Square.qq_const_collapse
#print axioms Square.pCh_pCh
#print axioms Square.qCh_qCh
#print axioms Square.pCh_qCh
#print axioms Square.qCh_pCh
#print axioms Square.pCh_smul_pt
#print axioms Square.qCh_smul_pt
#print axioms Square.pCh_add
#print axioms Square.qCh_add
#print axioms Square.pCh_scale
#print axioms Square.qCh_scale
-- AtlasGammaAtom: the atom Γ_c(u,v) = p((cu−v)/4) + q((cu+v)/4) and THE ATOMIC IDENTITY
-- [Γ_c(u_f,v_f), Γ_c(u_g,v_g)]_M = −(c/2)(u_f v_g + v_f u_g) by polarization (cut + / cycle −); additivity in (u,v).
#print axioms Square.cTwo_mul
#print axioms Square.sub_mul_sub_ga
#print axioms Square.add_mul_add_ga
#print axioms Square.neg_sub_self_ga
#print axioms Square.polar_core_ga
#print axioms Square.quarter_collapse_ga
#print axioms Square.quarter_neg_two_ga
#print axioms Square.pairF_add_left
#print axioms Square.gamma_bilinear
#print axioms Square.gammaAtom_readback
#print axioms Square.aCoef_add
#print axioms Square.bCoef_add
#print axioms Square.gammaAtom_add
#print axioms Square.aCoef_neg
#print axioms Square.bCoef_neg
#print axioms Square.gammaAtom_neg
#print axioms Square.gammaAtom_zero
-- IntegralFiniteLin: QsumN moduli, Lipschitz closure under finite sums and real scalars (|c| ≤ xBound c),
-- finite linearity of riemannSum / riemannIntegral (riemannIntegral_RsumN_fl, riemannIntegral_smul_real_fl), RReg transport.
#print axioms Square.RsumN_zero_fl
#print axioms Square.RsumN_succ_fl
#print axioms Square.QsumN_den_pos
#print axioms Square.QsumN_num_nonneg
#print axioms Square.QsumN_le_succ
#print axioms Square.QsumN_mono
#print axioms Square.Qle_term_QsumN
#print axioms Square.lip_weaken_fl
#print axioms Square.lip_add_fl
#print axioms Square.lip_zero_fl
#print axioms Square.lip_RsumN_fl
#print axioms Square.fc_RsumN_fl
#print axioms Square.xBQ_num_nonneg
#print axioms Square.lip_smul_fl
#print axioms Square.fc_smul_fl
#print axioms Square.riemannSum_zero_fn_fl
#print axioms Square.riemannSum_RsumN_fl
#print axioms Square.riemannIntegral_RsumN_fl
#print axioms Square.xBQ1_num_nonneg
#print axioms Square.Qle_L_xBQ1_mul
#print axioms Square.Qle_xBQ_xBQ1_mul
#print axioms Square.riemannIntegral_smul_real_fl
#print axioms Square.RReg_congr_fl
-- AtlasPrimeDyadicReadback: THE FIXED Γ FAMILY (atlasCoeff) from the raw reflectTest/dilateTest Haar evaluations at the
-- dyadic points with sourced weights Λ(m+1)·q^{-1/2}·w (fine +κ / coarse −κ telescoping atoms); THE EXACT ALL-PAIRS
-- PARTIAL-SUM READBACK gammaPartial_readback (= symmetrized dyadic approximation −½Σκ(D_S F_fg + D_S F_gf));
-- gammaPartial_eq_dyadicR (= D_S of ONE combined integrand G); the RReg of the partial sums along the certified
-- schedule (gammaSeq_RReg); THE BISHOP LIMIT gammaLimit_eq = −½(PrimeForm(f,g)+PrimeForm(g,f)) for ALL tests, and
-- gammaLimit_eq_neg_PrimeForm = −PrimeForm(f,g) on ClosedCore C.  Indefinite readback only — NO positivity claim.
#print axioms Square.hIntL_den
#print axioms Square.hIntL_num
#print axioms Square.hInt_lip
#print axioms Square.hInt_fc
#print axioms Square.HForm_unfold
#print axioms Square.atom_pt_alg
#print axioms Square.hInt_pt
#print axioms Square.level_readback
#print axioms Square.primeAddr_valid
#print axioms Square.atomOf_zero
#print axioms Square.atomOf_succ
#print axioms Square.uEv_add
#print axioms Square.vEv_add
#print axioms Square.uEv_neg
#print axioms Square.vEv_neg
#print axioms Square.atomGamma_add
#print axioms Square.atomGamma_neg
#print axioms Square.atlasCoeff_add
#print axioms Square.atlasCoeff_neg
#print axioms Square.blockPair_zero
#print axioms Square.omegaW_neg
#print axioms Square.blockPair_succ
#print axioms Square.stageSum_zero
#print axioms Square.tele_step_alg
#print axioms Square.gammaPartial_readback
#print axioms Square.pairL_den
#print axioms Square.pairL_num
#print axioms Square.pair_lip
#print axioms Square.pair_fc
#print axioms Square.termL_den
#print axioms Square.termL_num
#print axioms Square.term_lip
#print axioms Square.term_fc
#print axioms Square.innerL_den
#print axioms Square.innerL_num
#print axioms Square.inner_lip
#print axioms Square.inner_fc
#print axioms Square.KG_den
#print axioms Square.KG_num
#print axioms Square.G_lip
#print axioms Square.G_fc
#print axioms Square.dyadicR_G
#print axioms Square.gammaPartial_eq_dyadicR
#print axioms Square.add_sub_cancel_pd
#print axioms Square.gammaSeq_eq
#print axioms Square.tailReg
#print axioms Square.gammaSeq_RReg
#print axioms Square.gammaLimit_eq_integral
#print axioms Square.integral_pair
#print axioms Square.integral_G
#print axioms Square.RsumN_two_pd
#print axioms Square.w_pull_pd
#print axioms Square.place_regroup_pd
#print axioms Square.placeData_zero_q
#print axioms Square.placeData_one_q
#print axioms Square.PForm_unfold
#print axioms Square.place_readback
#print axioms Square.gammaLimit_eq
#print axioms Square.half_double_pd
#print axioms Square.gammaLimit_eq_neg_PrimeForm
#print axioms Square.gammaLimit_diag
-- AtlasPrimeDirect: the positive-measure direct-integral realization of the prime form with ONE weight-free field
-- Φ_f(t) = negFiber(u(f)(t), v(f)(t)) (κ and the Haar density OUTSIDE Γ as the nonnegative measure κ·dt/max(t,a)):
-- placeKappa_nonneg, primeMeasure_nonneg, atlasPrimeDirect_split (= cut − cycle), atlasPrimeCut_nonneg, atlasPrimeCycle_nonneg,
-- primeCutDyadic_RReg / primeCycleDyadic_RReg (stages of the one field), atlasPrimeDirect_eq = −½(PF(f,g)+PF(g,f)),
-- atlasPrimeDirect_eq_neg_PrimeForm = −PrimeForm on ClosedCore.  NO positivity / range / contraction claim.
#print axioms Square.negFiber_readback
#print axioms Square.posFiber_readback
#print axioms Square.negFiber_split
#print axioms Square.placeData_kappa
#print axioms Square.normWeight_nonneg_pd
#print axioms Square.placeKappa_nonneg
#print axioms Square.primeMeasure_nonneg
#print axioms Square.primePairInt_split
#print axioms Square.pair_pt_alg_pd
#print axioms Square.primePairInt_eq_gTerm
#print axioms Square.lip_of_congr_pd
#print axioms Square.fc_of_congr_pd
#print axioms Square.primePairInt_lip
#print axioms Square.primePairInt_fc
#print axioms Square.prodIntL_den
#print axioms Square.prodIntL_num
#print axioms Square.prodInt_lip
#print axioms Square.prodInt_fc
#print axioms Square.cut_pt_alg_pd
#print axioms Square.cyc_pt_alg_pd
#print axioms Square.cutInt_eq
#print axioms Square.cycInt_eq
#print axioms Square.cutL_den
#print axioms Square.cutL_num
#print axioms Square.cutInt_lip
#print axioms Square.cutInt_fc
#print axioms Square.cycL_den
#print axioms Square.cycL_num
#print axioms Square.cycInt_lip
#print axioms Square.cycInt_fc
#print axioms Square.primeCutDyadic_field
#print axioms Square.primeCutDyadic_RReg
#print axioms Square.primeCycleDyadic_RReg
#print axioms Square.primeCut_limit
#print axioms Square.lip_neg_pd
#print axioms Square.primeDirect_split
#print axioms Square.atlasPrimeDirect_split
#print axioms Square.atlasPrimeCut_nonneg
#print axioms Square.atlasPrimeCycle_nonneg
#print axioms Square.primeDirect_eq
#print axioms Square.atlasPrimeDirect_eq
#print axioms Square.atlasPrimeDirect_eq_neg_PrimeForm
#print axioms Square.atlasPrime_diag
-- AtlasArchCoords: the raw single-test archimedean coordinates U_x(f,t) = x^{-1/2} f(x/max(t,a)), V(f,t) = f(1/max(t,a)),
-- D_x = U_x − (1/max(x,1))·V exactly as FCanon realizes F⁺; THE RAW ENDPOINT-DEFECT IDENTITY (endpoint_defect_pt /
-- endpoint_defect_coords) and its lift to the numerator: archNumC_endpoint_defect N⁺(x) = w·∫[D_x(f)V(g)+V(f)D_x(g)]/max(t,a)
-- for every real x (FCanon_f_eq definitional, FCanon_one_eq via FTwo_ofQ at q=1).  No fiber, measure or form is built.
#print axioms Square.Rsub_mul_ac
#print axioms Square.endpoint_defect_core
#print axioms Square.endpoint_defect_pt
#print axioms Square.endpoint_defect_coords
#print axioms Square.crossL_den
#print axioms Square.crossL_num
#print axioms Square.crossInt_lip
#print axioms Square.crossInt_fc
#print axioms Square.FCanon_f_eq
#print axioms Square.vvL_den
#print axioms Square.vvL_num
#print axioms Square.vvInt_lip
#print axioms Square.vvInt_fc
#print axioms Square.hInt_one_eq_vv
#print axioms Square.FCanon_one_eq
#print axioms Square.asmInt_eq_defInt
#print axioms Square.asmL_den
#print axioms Square.asmL_num
#print axioms Square.p1_lip
#print axioms Square.p3_lip
#print axioms Square.asmInt_lip
#print axioms Square.asmInt_fc
#print axioms Square.defInt_lip
#print axioms Square.defInt_fc
#print axioms Square.integral_asm
#print axioms Square.swap_w_ac
#print axioms Square.two_w_ac
#print axioms Square.archNumC_endpoint_defect
-- AtlasArchCoords (AC-19): the raw endpoint/tail estimates Uc_one_eq_Vc, Dc_one_zero, Dc_abs_le_dist_one (uniform in the
-- Haar variable, modulus DcL sourced from the certified x^{-1/2} and the test's own certificates), Uc_high_zero, Dc_high_eq_neg_rOne_Vc.
#print axioms Square.invSq_one
#print axioms Square.xBand_one
#print axioms Square.rOne_one
#print axioms Square.Uc_congr_x
#print axioms Square.Uc_one_eq_Vc
#print axioms Square.Dc_one_zero
#print axioms Square.invSqL_den
#print axioms Square.invSqL_num
#print axioms Square.invSq_lip
#print axioms Square.invSq_bd
#print axioms Square.dilL_den
#print axioms Square.dilL_num
#print axioms Square.dil_lip
#print axioms Square.dil_bd
#print axioms Square.UcL_den
#print axioms Square.Uc_lip_x
#print axioms Square.rVL_den
#print axioms Square.rV_lip_x
#print axioms Square.DcL_den
#print axioms Square.Dc_lip_x
#print axioms Square.Dc_abs_le_dist_one
#print axioms Square.inv_a_le_B_inv_aw
#print axioms Square.Uc_high_zero
#print axioms Square.Dc_high_eq_neg_rOne_Vc
-- AtlasFibers: the pole fiber posFiber(U_x,V) with density 2(1+1/max(x,1))·w·r, the constant fiber negFiber(V,V) with density
-- (log4π+γ)·w·r, and the tail fiber negFiber(Z_x,W_x), Z_x = x·K(x)·D_x, W_x = (1/max(x,1))·V, density 2·w·r (mandatory factor 2);
-- POINTWISE readbacks density·⟨Φ_f,MΦ_g⟩ = the respective scalar integrand; all densities nonnegative.  No limit, no form value.
#print axioms Square.archAddr_valid
#print axioms Square.poleDensity_nonneg
#print axioms Square.two_half_pd
#print axioms Square.poleFiber_readback
#print axioms Square.archConst_nonneg
#print axioms Square.constDensity_nonneg
#print axioms Square.constFiber_readback
#print axioms Square.tailDensity_nonneg
#print axioms Square.Zc_mul_Wc
#print axioms Square.Wc_mul_Zc
#print axioms Square.tailFiber_readback
-- AtlasCarrier: finite weighted carriers with DISJOINT tags (prime/pole/cst/tail × quadrature sites), nonnegative site weights,
-- cut/cycle coordinates, stagePair_split; THE TRANSFER GATE: the explicit atlasTransferStage (cycle = cut + the x=1 pole column),
-- mixedCycleStage_factor for EVERY test (via cut_pole_zero: A(pole 0 i) = V/2 from U_1 = V), the necessary kernel condition
-- atlasTransfer_kernel, linearity; and the HONEST contraction test atlasTransferStage_not_contract: on the full cut carrier the
-- x=1 pole pulse has cutMass ≤ cycleMass (K pulse) — the transfer is not contractive off the range of cutStage.  No dominance claim.
#print axioms Square.canonBm1_den
#print axioms Square.canonBm1_num
#print axioms Square.xPt_zero
#print axioms Square.cellT_nonneg
#print axioms Square.cellX_nonneg
#print axioms Square.siteWeight_nonneg
#print axioms Square.siteAddr_valid
#print axioms Square.siteFiber_prime
#print axioms Square.siteFiber_pole
#print axioms Square.siteFiber_cst
#print axioms Square.siteFiber_tail
#print axioms Square.siteFiber_split
#print axioms Square.siteSum_congr
#print axioms Square.siteSum_sub
#print axioms Square.siteSum_nonneg
#print axioms Square.stagePair_split
#print axioms Square.cutPair_diag_eq_mass
#print axioms Square.cyclePair_diag_eq_mass
#print axioms Square.cutMass_nonneg
#print axioms Square.cycleMass_nonneg
#print axioms Square.b_eq_a_add_half
#print axioms Square.b_eq_a_sub_half
#print axioms Square.cut_pole_zero
#print axioms Square.mixedCycleStage_factor
#print axioms Square.atlasTransferStage_zero
#print axioms Square.atlasTransfer_kernel
#print axioms Square.atlasTransferStage_add
#print axioms Square.polePulse_prime
#print axioms Square.polePulse_cst
#print axioms Square.polePulse_tail
#print axioms Square.polePulse_pole_succ
#print axioms Square.polePulse_pole_zero
#print axioms Square.mass_zero_term
#print axioms Square.RsumN_zero_terms
#print axioms Square.indicator_term
#print axioms Square.indicator_mass
#print axioms Square.cutMass_polePulse
#print axioms Square.Rle_add_nonneg_left
#print axioms Square.Rle_add_nonneg_right
#print axioms Square.cycleMass_transfer_pulse_ge
#print axioms Square.pole_w_rearr
#print axioms Square.poleWeight_le_cstWeight
#print axioms Square.atlasTransferStage_not_contract
-- AtlasFibers (AC-20): the anchor identity (K(x + x·x⁻¹) + x⁻¹)·(V/2) = 2(xK·A_pole − A_tail) (raw and x ≥ 1 forms), posFiber V V is
-- pure cut, and the omitted x ≥ B tail reads as posFiber V V against the nonnegative density 2·w·r·K/x (closed form not claimed).
#print axioms Square.sub_regroup_af
#print axioms Square.anchor_from_pole_tail
#print axioms Square.anchor_from_pole_tail_ge_one
#print axioms Square.posFiber_VV_cycle_zero
#print axioms Square.posFiber_VV_cut
#print axioms Square.posFiber_VV_readback
#print axioms Square.tail_high_alg
#print axioms Square.tailFiber_high_pure_cut
-- AtlasCarrier (AC-20): source-exact tail floor dyQ k; the weak reverse bound reworded; THE GENERIC SHEAR NO-GO shear_no_go —
-- any transfer (Tc)_p = c_p + L(c) at a positive-weight prime site with L prime-blind and injecting an anchor is not contractive
-- on the full carrier (witness c_M = Mβ·e_p + a: cutMass c_M + 4w_pβ² ≤ cycleMass(T c_M)); shear_no_go_transfer instantiates it.
#print axioms Square.Rle_term_RsumN
#print axioms Square.Rle_prime_term_siteSum
#print axioms Square.primeUnit_self
#print axioms Square.primeUnit_pole
#print axioms Square.primeUnit_cst
#print axioms Square.primeUnit_tail
#print axioms Square.ind3_sum
#print axioms Square.siteSum_eq_parts
#print axioms Square.sq_succ_expand
#print axioms Square.primePart_mass_witness
#print axioms Square.primePart_mass_anchor
#print axioms Square.restPart_mass_witness
#print axioms Square.shear_no_go
#print axioms Square.shear_no_go_transfer
-- AtlasArchCoords (AC-21): THE COMMON-SCALE BRIDGE Uc_ofQ_eq_normWeight_uEv / Uc_placeData — every active prime evaluation is the
-- rational-scale restriction of the one normalized field U (invSqrtTwoF_ofQ + inert band clamp + rational dilation); prime_coherent.
#print axioms Square.Uc_ofQ_eq_normWeight_uEv
#print axioms Square.placeData_in_band
#print axioms Square.Uc_placeData
#print axioms Square.placeKappa_eq_lamW
#print axioms Square.prime_coherent
-- AtlasTailSplit: the EXACT split archTrunc k = compactTail k − farTailGram k (k ≥ 1, core tests): compact domain [1+2^{-k}, B]
-- (improper_split_shift at the exact rational gap), far part identified termwise beyond B (F⁺ vanishes, the retained −2F⁺(1)/x
-- survives), farCoef = ∫_B^∞ K_k(x)/x dx certified (decay 1/((m+1)m)) and ≥ 0, farTailGram = 2·farCoef·w·∫VV/max(t,a) ≥ 0 on the
-- diagonal = 2·farCoef·F⁺(1); improper_Rsmul_terms (real scalar through an improper integral, schedules reconciled).
#print axioms Square.tailGap_den
#print axioms Square.two_le_two_pow
#print axioms Square.tailGap_num_pos
#print axioms Square.tailGap_num_nonneg
#print axioms Square.kerRec_f
#print axioms Square.farShift_den
#print axioms Square.farShift_num_nonneg
#print axioms Square.one_add_farShift
#print axioms Square.one_le_farShift
#print axioms Square.farKer_f
#print axioms Square.farKer_nonneg
#print axioms Square.rOne_le_inv
#print axioms Square.affineMap_ge_a
#print axioms Square.inv_m_inv_succ
#print axioms Square.farKer_decay
#print axioms Square.farCoef_nonneg
#print axioms Square.farTailGram_diag_nonneg
#print axioms Square.farTailGram_eq_F1
#print axioms Square.decay_weaken
#print axioms Square.improper_Rsmul_terms
#print axioms Square.integralTerm_smul_real
#print axioms Square.far_term_eq
#print axioms Square.far_window_bound
#print axioms Square.archTrunc_split
-- AtlasParamIntegral (AC-22): |∫₀¹h| ≤ b (real b), THE PARAMETRIC LIPSCHITZ LEMMA x ↦ ∫₀¹F(x,·) (param_integral_lip), and its congruence
#print axioms Square.lip_neg_pi
#print axioms Square.riemannIntegral_abs_le_unit_real
#print axioms Square.param_integral_lip
#print axioms Square.param_integral_congr
-- AtlasDefectGram (AC-22 follow-up): the source identities a positive stage would consume — pole cut = prime cycle, pole cycle = prime cut (at every scale, hence at the upper scale n), the constant channel is pure cycle
#print axioms Square.pole_cut_eq_prime_cycle
#print axioms Square.pole_cycle_eq_prime_cut
#print axioms Square.poleFiber_cut_at_upR
#print axioms Square.negFiber_VV_cut_zero
#print axioms Square.negFiber_VV_cycle
-- AtlasSourceLaws (AC-23 prerequisites, target-free): the orbit law x'·t = x·t' ⟹ x'^{-1/2}U_x(f,t) = x^{-1/2}U_{x'}(f,t'), the λ-orbit form, the weight law (invSq(λx))²·λ = (invSq x)², THE SOURCE-COHERENCE LAW U_x(f,t) = x^{-1/2}V(f,t/x) on t ≥ ax, and the support-forced zero rows U_q(f,t) = 0 for t ≤ aq (prime rows with a+w ≤ na vanish on the window); no measure coupling, no positivity
#print axioms Square.dilRef_f
#print axioms Square.xBand_inert
#print axioms Square.Rnonneg_of_ge_a
#print axioms Square.inv_cross_alg
#print axioms Square.dilRef_orbit
#print axioms Square.Uc_orbit
#print axioms Square.Uc_orbit_scale
#print axioms Square.invSq_sq_mul_self
#print axioms Square.invSq_scale_sq
#print axioms Square.Rle_a_of_ax
#print axioms Square.Uc_eq_invSq_Vc_shift
#print axioms Square.q_mul_inv_aq
#print axioms Square.Uc_zero_row
#print axioms Square.Uc_zero_row_upR
-- AtlasPrimeFold (AC-22 item 2): THE FOLD P_m = Λ(n)(B_n(f,g)+B_n(g,f)) on the core, B_n(f,g) = w∫U_n(f)V(g)r, the folded negFiber(U_n,V) field with density 2Λ(n)wr, primeFoldDirect_m = −Λ(n)(B_n+B_n), primeFoldGram = −PrimeForm on the core
#print axioms Square.PForm_fold
#print axioms Square.primeFoldDensity_nonneg
#print axioms Square.primeFoldFiber_readback
#print axioms Square.foldL_den
#print axioms Square.foldL_num
#print axioms Square.foldInt_lip
#print axioms Square.foldInt_fc
#print axioms Square.pull_af
#print axioms Square.foldInt_eq_UV
#print axioms Square.foldInt_eq_hInt
#print axioms Square.integral_foldInt
#print axioms Square.BForm_eq_w_foldInt
#print axioms Square.fold_pt_alg
#print axioms Square.primeFoldInt_eq_exp
#print axioms Square.foldPairL_den
#print axioms Square.foldPairL_num
#print axioms Square.foldPair_lip
#print axioms Square.foldPair_fc
#print axioms Square.foldExpL_den
#print axioms Square.foldExpL_num
#print axioms Square.foldExpPos_lip
#print axioms Square.foldExpPos_fc
#print axioms Square.foldExp_lip
#print axioms Square.foldExp_fc
#print axioms Square.primeFoldInt_lip
#print axioms Square.primeFoldInt_fc
#print axioms Square.primeFoldDirect_eq
#print axioms Square.primeFoldDirect_eq_BForm
#print axioms Square.primeFoldGram_eq_neg_PrimeForm
-- AtlasArchGram (AC-22 item 3): the constant Gram (= −archConst·w∫VV r, ArchConstForm_eq_vv), the POLE GRAM ∫_{[1,B]}∫₀¹ (inner value (1+1/x)w(x^{-1/2}∫cross_fg + x^{-1/2}∫cross_gf), scale-Lipschitz via param_integral_lip), the COMPACT TAIL GRAM ∫_{[1+2^{-k},B]}∫₀¹ at the [1,B]-clamped scale (inner value −wK(x̄)·defectIntegral(x̄)); tailGap moved here
#print axioms Square.lip_mul_const_right
#print axioms Square.lip_const_mul_left
#print axioms Square.abs_mul_bd
#print axioms Square.abs_add_bd
#print axioms Square.Vc_bd
#print axioms Square.Uc_bd
#print axioms Square.rOne_bd
#print axioms Square.one_add_rOne_bd
#print axioms Square.one_add_rOne_lip
#print axioms Square.wr_bd
#print axioms Square.UcL_num
#print axioms Square.const_pt_alg
#print axioms Square.constInt_eq_exp
#print axioms Square.constExpL_den
#print axioms Square.constExpL_num
#print axioms Square.constExpPos_lip
#print axioms Square.constExpPos_fc
#print axioms Square.constExp_lip
#print axioms Square.constExp_fc
#print axioms Square.constInt_lip
#print axioms Square.constInt_fc
#print axioms Square.constGram_eq
#print axioms Square.ArchConstForm_eq_vv
#print axioms Square.symL_den
#print axioms Square.symL_num
#print axioms Square.symInt_lip
#print axioms Square.symInt_fc
#print axioms Square.symInt_eq_UV
#print axioms Square.poleInt_eq_exp
#print axioms Square.poleExpL_den
#print axioms Square.poleExpL_num
#print axioms Square.poleExp_lip
#print axioms Square.poleExp_fc
#print axioms Square.poleInt_lip
#print axioms Square.poleInt_fc
#print axioms Square.poleInner_eq
#print axioms Square.poleL1_den
#print axioms Square.poleM1_den
#print axioms Square.wa_num
#print axioms Square.poleL1_num
#print axioms Square.poleM1_num
#print axioms Square.poleF1_lip
#print axioms Square.poleF1_bd
#print axioms Square.poleL2_den
#print axioms Square.poleL2_num
#print axioms Square.poleM2_den
#print axioms Square.poleM2_num
#print axioms Square.poleF2_lip
#print axioms Square.poleF2_bd
#print axioms Square.poleXL_den
#print axioms Square.poleXL_num
#print axioms Square.poleRB_lip_x
#print axioms Square.poleRB_congr_x
#print axioms Square.poleInt_lip_x
#print axioms Square.poleInt_congr_x
#print axioms Square.poleInner_lip
#print axioms Square.poleInner_fc
#print axioms Square.xcl_ge_one
#print axioms Square.xcl_le_B
#print axioms Square.xcl_lip
#print axioms Square.xcl_congr
#print axioms Square.xcl_eq_of_band
#print axioms Square.lip_comp_xcl
#print axioms Square.kerL_den
#print axioms Square.kerL_num
#print axioms Square.kerM_den
#print axioms Square.kerM_num
#print axioms Square.Kx_lip
#print axioms Square.Kx_bd
#print axioms Square.Kx_congr
#print axioms Square.tailInt_eq_RB
#print axioms Square.tail_pt_alg
#print axioms Square.tailRB_eq_exp
#print axioms Square.tailInt_eq_exp
#print axioms Square.tailExpL_den
#print axioms Square.tailExpL_num
#print axioms Square.tailExpPos_lip
#print axioms Square.tailExpPos_fc
#print axioms Square.tailExp_lip
#print axioms Square.tailExp_fc
#print axioms Square.tailInt_lip
#print axioms Square.tailInt_fc
#print axioms Square.tailInner_eq
#print axioms Square.rVL_num
#print axioms Square.DcL_num
#print axioms Square.DcM_den
#print axioms Square.DcM_num
#print axioms Square.Dc_bd
#print axioms Square.Dc_congr_x
#print axioms Square.Dcl_lip
#print axioms Square.tailL2_den
#print axioms Square.tailL2_num
#print axioms Square.tailM2_den
#print axioms Square.tailM2_num
#print axioms Square.tailS_lip
#print axioms Square.tailS_bd
#print axioms Square.tailKS_den
#print axioms Square.tailKS_num
#print axioms Square.tailKS_lip
#print axioms Square.tailXL_den
#print axioms Square.tailXL_num
#print axioms Square.tailRB_lip_x
#print axioms Square.tailRB_congr_x
#print axioms Square.tailInt_lip_x
#print axioms Square.tailInt_congr_x
#print axioms Square.tailInner_lip
#print axioms Square.tailInner_fc
-- AtlasDefectReadback (AC-22 items 3-5): poleGram = PoleForm, constGram = −ArchConstForm, tailGram_k = −compactTail_k, THE ALL-PAIRS COMPACT GRAM IDENTITY atlasCompactCoupled_k = atlasDefectGram_k on the core, coupled_trunc_split, CoupledForm = lim(atlasDefectGram_k + farTailGram_k), and the CONDITIONAL atlasDefect_nonneg_imp_dominance (hypothesis NOT proved, NOT asserted = the crux)
#print axioms Square.poleInner_eq_poleIntegrand
#print axioms Square.poleGram_eq_PoleForm
#print axioms Square.constGram_eq_neg_ArchConstForm
#print axioms Square.defectIntegral_congr_x
#print axioms Square.tailInner_eq_neg_fullInt
#print axioms Square.affineMap_le_top
#print axioms Square.tail_window_top
#print axioms Square.tailGram_eq_neg_compactTail
#print axioms Square.atlasDefect_readback
#print axioms Square.sub_sub_comm_dr
#print axioms Square.sub_add_dr
#print axioms Square.sub_add_cancel_dr
#print axioms Square.add_sub_swap_dr
#print axioms Square.sub_sub_sub_dr
#print axioms Square.coupled_alg_dr
#print axioms Square.coupled_trunc_split
#print axioms Square.archCNC_pos
#print axioms Square.cmpSeq_RReg
#print axioms Square.defectSeq_RReg
#print axioms Square.CoupledForm_eq_lim_defect
#print axioms Square.defectSeq_nonneg_imp_dominance
#print axioms Square.atlasDefect_nonneg_imp_dominance
