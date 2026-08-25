/-
F1 square — **passage through the improper limits** (`WeilArchLimit.lean`):

  • `improperIntegral1_certif_irrel` — the improper integral does not depend on the Lipschitz
    certificate (same decay constant, hence the same schedule);
  • `archKernFull_inert_pair` — two full kernels with floors below `x − 1` agree;
  • **THE SAME-CONSTANT IMPROPER SPLIT** (`improper_split_shift`):
        `∫_{1+δ}^{∞} φ = ∫_{1+δ}^{1+δ+Δ} φ + ∫_{1+δ+Δ}^{∞} φ`
    for the shifted tests, both improper integrals certified at the SAME decay constant (so their
    partial sums run on the SAME schedule); the partial-sum discrepancy is the far window
    `∫_{[M_j+1, M_j+1+Δ]}`, bounded by the explicit hypothesis `hfar` with rate `C/(j+1)` — the
    Bishop limits then agree (`Rlim_eq_of_close`).
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.WeilArchTrunc

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- (1) Certificate irrelevance and kernel inertness.
-- ===========================================================================

/-- The improper integral does not depend on the Lipschitz certificate (same `K`). -/
theorem improperIntegral1_certif_irrel {f : Real → Real} {L L' K : Q}
    (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfc : ∀ x y, Req x y → Req (f x) (f y))
    (hL'd : 0 < L'.den) (hL'n : 0 ≤ L'.num)
    (hlip' : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L' hL'd) (Rabs (Rsub x y))))
    (hfc' : ∀ x y, Req x y → Req (f x) (f y)) (hKd : 0 < K.den) (hK0 : 0 ≤ K.num)
    (hb : ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
          (integralTerm hLd hLn hlip hfc m)
      ∧ Rle (integralTerm hLd hLn hlip hfc m)
          (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
    (hb' : ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
          (integralTerm hL'd hL'n hlip' hfc' m)
      ∧ Rle (integralTerm hL'd hL'n hlip' hfc' m)
          (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm)))) :
    Req (improperIntegral1 hLd hLn hlip hfc hKd hK0 hb)
        (improperIntegral1 hL'd hL'n hlip' hfc' hKd hK0 hb') := by
  show Req (Rlim (fun j => genSum (integralTerm hLd hLn hlip hfc) (digammaMidx K j)) _)
    (Rlim (fun j => genSum (integralTerm hL'd hL'n hlip' hfc') (digammaMidx K j)) _)
  refine Rlim_congr _ _ _ _ (fun j => genSum_congr _ _ (fun m => ?_) _)
  exact riemannIntegralI_certif_irrel hLd hLn hlip hfc hL'd hL'n hlip' hfc' _ _ _ _ _

/-- Two full kernels with floors `c, c' ≤ x − 1` agree at `x` (both are `1/(x − x⁻¹)`). -/
theorem archKernFull_inert_pair (c c' : Q) (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hc'n : 0 < c'.num) (hc'd : 0 < c'.den) (x : Real) (hx1 : Rle one x)
    (hxc : Rle (ofQ c hcd) (Rsub x one)) (hxc' : Rle (ofQ c' hc'd) (Rsub x one)) :
    Req ((archKernFull c hcn hcd).f x) ((archKernFull c' hc'n hc'd).f x) := by
  rw [archKernFull_f, archKernFull_f]
  have hge := innerXm_ge_c c hcd x hx1 hxc
  have hge' := innerXm_ge_c c' hc'd x hx1 hxc'
  obtain ⟨ki, hki⟩ := Pos_of_Rle_ofQ hcn hcd hge
  exact Req_trans (clampedInv_eq_of_ge (a := c) (han := hcn) (had := hcd) hki hge)
    (Req_symm (clampedInv_eq_of_ge (a := c') (han := hc'n) (had := hc'd) hki hge'))

-- ===========================================================================
-- (2) The partial sums of a shifted improper integral are finite windows.
-- ===========================================================================

/-- `Σ_{m < M} ∫_{[m+1,m+2]} f = ∫_{[1, M+1]} f` for `M ≥ 1`. -/
theorem genSum_terms_eq_window {f : Real → Real} {L : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfc : ∀ x y, Req x y → Req (f x) (f y)) (M : Nat) (hM : 1 ≤ M) :
    Req (genSum (integralTerm hLd hLn hlip hfc) M)
        (riemannIntegralI hLd hLn hlip hfc (⟨1, 1⟩ : Q) (⟨(M : Int), 1⟩ : Q)
          Nat.one_pos Nat.one_pos (Int.ofNat_nonneg _)) := by
  obtain ⟨M', hM'⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  subst hM'
  exact Req_symm (window_eq_genSum_terms hLd hLn hlip hfc M')

/-- `(1 + M) = ⟨M+1, 1⟩` and `(Δ + M) − M = Δ`, `(Δ + M) − Δ = M` (rational bookkeeping). -/
theorem q_one_add_nat (M : Nat) : Qeq (add (⟨1, 1⟩ : Q) (⟨(M : Int), 1⟩ : Q)) (⟨(M : Int) + 1, 1⟩ : Q) := by
  simp only [Qeq, add]; push_cast; omega

theorem q_addsub_left (Δ : Q) (M : Nat) : Qeq (Qsub (add Δ (⟨(M : Int), 1⟩ : Q)) Δ) (⟨(M : Int), 1⟩ : Q) :=
  Qsub_add_self_eq Δ _

theorem q_addsub_right (Δ : Q) (M : Nat) : Qeq (Qsub (add Δ (⟨(M : Int), 1⟩ : Q)) (⟨(M : Int), 1⟩ : Q)) Δ := by
  simp only [Qeq, add, Qsub, neg]
  push_cast
  generalize Δ.num = dn
  generalize ((Δ.den : Nat) : Int) = dd
  generalize ((M : Nat) : Int) = Mi
  ring_uor

-- ===========================================================================
-- (3) THE SAME-CONSTANT IMPROPER SPLIT.
-- ===========================================================================

/-- The decay predicate of a test at constant `K` (abbreviation for readability). -/
def DecayAt (ψ : L2Test) (K : Q) (hKd : 0 < K.den) : Prop :=
  ∀ m, ∀ hm : 1 ≤ m,
    Rle (Rneg (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
        (integralTerm ψ.hLd ψ.hLn ψ.hlip ψ.hfc m)
    ∧ Rle (integralTerm ψ.hLd ψ.hLn ψ.hlip ψ.hfc m)
        (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm)))

/-- The per-`j` identity: `c + Y_j = X_j + tail_j`, where `X_j, Y_j` are the `j`-th partial sums of the
    two improper integrals (same schedule `M_j`), `c = ∫_{[1,1+Δ]} g`, `tail_j = ∫_{[M_j+1, M_j+1+Δ]} g`. -/
theorem split_partial_identity (φ : L2Test) (δ Δ : Q) (hδd : 0 < δ.den) (hΔd : 0 < Δ.den)
    (hΔn : 0 < Δ.num) (M : Nat) (hM : 1 ≤ M) :
    Req (Radd (riemannIntegralI (shiftTest δ hδd φ).hLd (shiftTest δ hδd φ).hLn (shiftTest δ hδd φ).hlip
            (shiftTest δ hδd φ).hfc (⟨1, 1⟩ : Q) Δ Nat.one_pos hΔd (Int.le_of_lt hΔn))
          (genSum (integralTerm (shiftTest (add δ Δ) (add_den_pos hδd hΔd) φ).hLd
            (shiftTest (add δ Δ) (add_den_pos hδd hΔd) φ).hLn
            (shiftTest (add δ Δ) (add_den_pos hδd hΔd) φ).hlip
            (shiftTest (add δ Δ) (add_den_pos hδd hΔd) φ).hfc) M))
        (Radd (genSum (integralTerm (shiftTest δ hδd φ).hLd (shiftTest δ hδd φ).hLn
            (shiftTest δ hδd φ).hlip (shiftTest δ hδd φ).hfc) M)
          (riemannIntegralI (shiftTest δ hδd φ).hLd (shiftTest δ hδd φ).hLn (shiftTest δ hδd φ).hlip
            (shiftTest δ hδd φ).hfc (⟨(M : Int) + 1, 1⟩ : Q) Δ Nat.one_pos hΔd (Int.le_of_lt hΔn))) := by
  have hMn : (0 : Int) < (M : Int) := by omega
  -- Y = ∫_{[1,M]} g' = ∫_{[1,M]} (shift Δ g) = ∫_{[1+Δ, M]} g
  have hY : Req (genSum (integralTerm (shiftTest (add δ Δ) (add_den_pos hδd hΔd) φ).hLd
        (shiftTest (add δ Δ) (add_den_pos hδd hΔd) φ).hLn
        (shiftTest (add δ Δ) (add_den_pos hδd hΔd) φ).hlip
        (shiftTest (add δ Δ) (add_den_pos hδd hΔd) φ).hfc) M)
      (riemannIntegralI (shiftTest δ hδd φ).hLd (shiftTest δ hδd φ).hLn (shiftTest δ hδd φ).hlip
        (shiftTest δ hδd φ).hfc (add (⟨1, 1⟩ : Q) Δ) (⟨(M : Int), 1⟩ : Q) (add_den_pos Nat.one_pos hΔd)
        Nat.one_pos (Int.ofNat_nonneg _)) := by
    refine Req_trans (genSum_terms_eq_window _ _ _ _ M hM) ?_
    refine Req_trans (riemannIntegralI_congr_unit_mod
      (shiftTest (add δ Δ) (add_den_pos hδd hΔd) φ).hLd (shiftTest (add δ Δ) (add_den_pos hδd hΔd) φ).hLn
      (shiftTest (add δ Δ) (add_den_pos hδd hΔd) φ).hlip (shiftTest (add δ Δ) (add_den_pos hδd hΔd) φ).hfc
      (shiftTest Δ hΔd (shiftTest δ hδd φ)).hLd (shiftTest Δ hΔd (shiftTest δ hδd φ)).hLn
      (shiftTest Δ hΔd (shiftTest δ hδd φ)).hlip (shiftTest Δ hΔd (shiftTest δ hδd φ)).hfc
      (⟨1, 1⟩ : Q) (⟨(M : Int), 1⟩ : Q) Nat.one_pos Nat.one_pos (Int.ofNat_nonneg _)
      (fun t _ _ => Req_symm (shiftTest_comp δ Δ hδd hΔd φ _))) ?_
    exact shift_window Δ hΔd (shiftTest δ hδd φ) (⟨1, 1⟩ : Q) (⟨(M : Int), 1⟩ : Q) Nat.one_pos Nat.one_pos
      (Int.ofNat_nonneg _)
  -- c + ∫_{[1+Δ, M]} g = ∫_{[1, Δ+M]} g
  have hsplit1 := riemannIntegralI_split_at (shiftTest δ hδd φ).hLd (shiftTest δ hδd φ).hLn
    (shiftTest δ hδd φ).hlip (shiftTest δ hδd φ).hfc (⟨1, 1⟩ : Q) (add Δ (⟨(M : Int), 1⟩ : Q)) Δ
    Nat.one_pos (add_den_pos hΔd Nat.one_pos) (Qadd_num_nonneg_loc (Int.le_of_lt hΔn) (Int.ofNat_nonneg _))
    hΔd hΔn (Qle_self_add (Int.ofNat_nonneg _))
    (Qsub_num_nonneg (Qle_self_add (Int.ofNat_nonneg _)))
  -- ∫_{[1, Δ+M]} g = ∫_{[1, M]} g + ∫_{[1+M, Δ]} g
  have hsplit2 := riemannIntegralI_split_at (shiftTest δ hδd φ).hLd (shiftTest δ hδd φ).hLn
    (shiftTest δ hδd φ).hlip (shiftTest δ hδd φ).hfc (⟨1, 1⟩ : Q) (add Δ (⟨(M : Int), 1⟩ : Q))
    (⟨(M : Int), 1⟩ : Q) Nat.one_pos (add_den_pos hΔd Nat.one_pos)
    (Qadd_num_nonneg_loc (Int.le_of_lt hΔn) (Int.ofNat_nonneg _))
    Nat.one_pos hMn (Qle_self_add_l (Int.le_of_lt hΔn)) (Qsub_num_nonneg (Qle_self_add_l (Int.le_of_lt hΔn)))
  refine Req_trans (Radd_congr (Req_refl _) hY) ?_
  refine Req_trans (Radd_congr (Req_refl _) (Req_symm (riemannIntegralI_congr_Q
    (shiftTest δ hδd φ).hLd (shiftTest δ hδd φ).hLn (shiftTest δ hδd φ).hlip (shiftTest δ hδd φ).hfc
    (add (⟨1, 1⟩ : Q) Δ) (Qsub (add Δ (⟨(M : Int), 1⟩ : Q)) Δ) (add (⟨1, 1⟩ : Q) Δ) (⟨(M : Int), 1⟩ : Q)
    (add_den_pos Nat.one_pos hΔd) (Qsub_den_pos (add_den_pos hΔd Nat.one_pos) hΔd)
    (Qsub_num_nonneg (Qle_self_add (Int.ofNat_nonneg _)))
    (add_den_pos Nat.one_pos hΔd) Nat.one_pos (Int.ofNat_nonneg _)
    (Qeq_refl _) (q_addsub_left Δ M)))) ?_
  refine Req_trans (Req_symm hsplit1) ?_
  refine Req_trans hsplit2 ?_
  refine Radd_congr (Req_symm (genSum_terms_eq_window _ _ _ _ M hM)) ?_
  exact riemannIntegralI_congr_Q
    (shiftTest δ hδd φ).hLd (shiftTest δ hδd φ).hLn (shiftTest δ hδd φ).hlip (shiftTest δ hδd φ).hfc
    (add (⟨1, 1⟩ : Q) (⟨(M : Int), 1⟩ : Q)) (Qsub (add Δ (⟨(M : Int), 1⟩ : Q)) (⟨(M : Int), 1⟩ : Q))
    (⟨(M : Int) + 1, 1⟩ : Q) Δ
    (add_den_pos Nat.one_pos Nat.one_pos) (Qsub_den_pos (add_den_pos hΔd Nat.one_pos) Nat.one_pos)
    (Qsub_num_nonneg (Qle_self_add_l (Int.le_of_lt hΔn)))
    Nat.one_pos hΔd (Int.le_of_lt hΔn)
    (q_one_add_nat M) (q_addsub_right Δ M)

/-- `CF/(n+1) ≤ 1/(k+1)` once `n ≥ CF·(k+1)`. -/
theorem rate_le_of_ge (CF k n : Nat) (hn : CF * (k + 1) ≤ n) :
    Qle (⟨(CF : Int), n + 1⟩ : Q) (⟨1, k + 1⟩ : Q) := by
  show (CF : Int) * ((k + 1 : Nat) : Int) ≤ 1 * ((n + 1 : Nat) : Int)
  have h : ((CF * (k + 1) : Nat) : Int) ≤ ((n : Nat) : Int) := Int.ofNat_le.mpr hn
  push_cast at h ⊢
  omega

/-- **THE SAME-CONSTANT IMPROPER SPLIT**
    `∫_{1+δ}^{∞} φ = ∫_{[1+δ, 1+δ+Δ]} φ + ∫_{1+δ+Δ}^{∞} φ` (both improper integrals at the same
    decay constant `K`), given the far-window rate `|∫_{[M_j+1, M_j+1+Δ]} (shift δ φ)| ≤ CF/(j+1)`. -/
theorem improper_split_shift (φ : L2Test) (δ Δ : Q) (hδd : 0 < δ.den) (hΔd : 0 < Δ.den)
    (hΔn : 0 < Δ.num) {K : Q} (hKd : 0 < K.den) (hK0 : 0 ≤ K.num)
    (hb0 : DecayAt (shiftTest δ hδd φ) K hKd)
    (hb1 : DecayAt (shiftTest (add δ Δ) (add_den_pos hδd hΔd) φ) K hKd)
    (CF : Nat)
    (hfar : ∀ j, Rle (Rabs (riemannIntegralI (shiftTest δ hδd φ).hLd (shiftTest δ hδd φ).hLn
        (shiftTest δ hδd φ).hlip (shiftTest δ hδd φ).hfc
        (⟨((digammaMidx K j : Nat) : Int) + 1, 1⟩ : Q) Δ Nat.one_pos hΔd (Int.le_of_lt hΔn)))
      (ofQ (⟨(CF : Int), j + 1⟩ : Q) (Nat.succ_pos j))) :
    Req (improperIntegral1 (shiftTest δ hδd φ).hLd (shiftTest δ hδd φ).hLn (shiftTest δ hδd φ).hlip
          (shiftTest δ hδd φ).hfc hKd hK0 hb0)
        (Radd (riemannIntegralI (shiftTest δ hδd φ).hLd (shiftTest δ hδd φ).hLn (shiftTest δ hδd φ).hlip
            (shiftTest δ hδd φ).hfc (⟨1, 1⟩ : Q) Δ Nat.one_pos hΔd (Int.le_of_lt hΔn))
          (improperIntegral1 (shiftTest (add δ Δ) (add_den_pos hδd hΔd) φ).hLd
            (shiftTest (add δ Δ) (add_den_pos hδd hΔd) φ).hLn
            (shiftTest (add δ Δ) (add_den_pos hδd hΔd) φ).hlip
            (shiftTest (add δ Δ) (add_den_pos hδd hΔd) φ).hfc hKd hK0 hb1)) := by
  -- the two partial-sum sequences (same schedule) and the constant
  show Req (Rlim (fun j => genSum (integralTerm (shiftTest δ hδd φ).hLd (shiftTest δ hδd φ).hLn
      (shiftTest δ hδd φ).hlip (shiftTest δ hδd φ).hfc) (digammaMidx K j)) _)
    (Radd _ (Rlim (fun j => genSum (integralTerm (shiftTest (add δ Δ) (add_den_pos hδd hΔd) φ).hLd
      (shiftTest (add δ Δ) (add_den_pos hδd hΔd) φ).hLn
      (shiftTest (add δ Δ) (add_den_pos hδd hΔd) φ).hlip
      (shiftTest (add δ Δ) (add_den_pos hδd hΔd) φ).hfc) (digammaMidx K j)) _))
  have hid : ∀ j, Req (Radd (riemannIntegralI (shiftTest δ hδd φ).hLd (shiftTest δ hδd φ).hLn
        (shiftTest δ hδd φ).hlip (shiftTest δ hδd φ).hfc (⟨1, 1⟩ : Q) Δ Nat.one_pos hΔd (Int.le_of_lt hΔn))
        (genSum (integralTerm (shiftTest (add δ Δ) (add_den_pos hδd hΔd) φ).hLd
          (shiftTest (add δ Δ) (add_den_pos hδd hΔd) φ).hLn
          (shiftTest (add δ Δ) (add_den_pos hδd hΔd) φ).hlip
          (shiftTest (add δ Δ) (add_den_pos hδd hΔd) φ).hfc) (digammaMidx K j)))
      (Radd (genSum (integralTerm (shiftTest δ hδd φ).hLd (shiftTest δ hδd φ).hLn
          (shiftTest δ hδd φ).hlip (shiftTest δ hδd φ).hfc) (digammaMidx K j))
        (riemannIntegralI (shiftTest δ hδd φ).hLd (shiftTest δ hδd φ).hLn (shiftTest δ hδd φ).hlip
          (shiftTest δ hδd φ).hfc (⟨((digammaMidx K j : Nat) : Int) + 1, 1⟩ : Q) Δ Nat.one_pos hΔd
          (Int.le_of_lt hΔn))) :=
    fun j => split_partial_identity φ δ Δ hδd hΔd hΔn (digammaMidx K j) (digammaMidx_ge_one K j)
  refine Req_trans (Rlim_eq_of_close (genSum_RReg _ hKd hK0 hb0)
    (RReg_add_const (riemannIntegralI (shiftTest δ hδd φ).hLd (shiftTest δ hδd φ).hLn
        (shiftTest δ hδd φ).hlip (shiftTest δ hδd φ).hfc (⟨1, 1⟩ : Q) Δ Nat.one_pos hΔd (Int.le_of_lt hΔn))
      (fun j => genSum (integralTerm (shiftTest (add δ Δ) (add_den_pos hδd hΔd) φ).hLd
        (shiftTest (add δ Δ) (add_den_pos hδd hΔd) φ).hLn
        (shiftTest (add δ Δ) (add_den_pos hδd hΔd) φ).hlip
        (shiftTest (add δ Δ) (add_den_pos hδd hΔd) φ).hfc) (digammaMidx K j))
      (genSum_RReg _ hKd hK0 hb1)) ?_ ?_) ?_
  · -- X_n ≤ (c + Y_n) + 1/(k+1) eventually
    intro k
    refine ⟨CF * (k + 1), fun n hn => ?_⟩
    have hr := Rle_ofQ_ofQ (Nat.succ_pos n) (Nat.succ_pos k) (rate_le_of_ge CF k n hn)
    -- X = (X + tail) − tail = (c + Y) − tail ≤ (c + Y) + |tail|
    refine Rle_trans (Rle_of_Req (Req_symm (Radd_sub_cancel_right
      (genSum (integralTerm (shiftTest δ hδd φ).hLd (shiftTest δ hδd φ).hLn
          (shiftTest δ hδd φ).hlip (shiftTest δ hδd φ).hfc) (digammaMidx K n))
      (riemannIntegralI (shiftTest δ hδd φ).hLd (shiftTest δ hδd φ).hLn (shiftTest δ hδd φ).hlip
          (shiftTest δ hδd φ).hfc (⟨((digammaMidx K n : Nat) : Int) + 1, 1⟩ : Q) Δ Nat.one_pos hΔd
          (Int.le_of_lt hΔn))))) ?_
    refine Rle_trans (Rle_of_Req (Rsub_congr (Req_symm (hid n)) (Req_refl _))) ?_
    exact Radd_le_add (Rle_refl _) (Rle_trans (Rle_Rabs_self _)
      (Rle_trans (Rle_of_Req (Rabs_Rneg _)) (Rle_trans (hfar n) hr)))
  · -- (c + Y_n) ≤ X_n + 1/(k+1) eventually
    intro k
    refine ⟨CF * (k + 1), fun n hn => ?_⟩
    have hr := Rle_ofQ_ofQ (Nat.succ_pos n) (Nat.succ_pos k) (rate_le_of_ge CF k n hn)
    refine Rle_trans (Rle_of_Req (hid n)) ?_
    exact Radd_le_add (Rle_refl _) (Rle_trans (Rle_Rabs_self _) (Rle_trans (hfar n) hr))
  · exact Rlim_add_const _ _ _ _


-- ===========================================================================
-- (4) Block-wise congruence of improper integrals, the strip cap, the far-window rate.
-- ===========================================================================

/-- Improper integrals with block-wise equal unit terms (same `K`) agree. -/
theorem improperIntegral1_congr_terms {f g : Real → Real} {L L' K : Q}
    (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlipf : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfcf : ∀ x y, Req x y → Req (f x) (f y))
    (hL'd : 0 < L'.den) (hL'n : 0 ≤ L'.num)
    (hlipg : ∀ x y, Rle (Rabs (Rsub (g x) (g y))) (Rmul (ofQ L' hL'd) (Rabs (Rsub x y))))
    (hfcg : ∀ x y, Req x y → Req (g x) (g y)) (hKd : 0 < K.den) (hK0 : 0 ≤ K.num)
    (hbf : ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
          (integralTerm hLd hLn hlipf hfcf m)
      ∧ Rle (integralTerm hLd hLn hlipf hfcf m)
          (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
    (hbg : ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
          (integralTerm hL'd hL'n hlipg hfcg m)
      ∧ Rle (integralTerm hL'd hL'n hlipg hfcg m)
          (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
    (hterm : ∀ m, Req (integralTerm hLd hLn hlipf hfcf m) (integralTerm hL'd hL'n hlipg hfcg m)) :
    Req (improperIntegral1 hLd hLn hlipf hfcf hKd hK0 hbf)
        (improperIntegral1 hL'd hL'n hlipg hfcg hKd hK0 hbg) := by
  show Req (Rlim (fun j => genSum (integralTerm hLd hLn hlipf hfcf) (digammaMidx K j)) _)
    (Rlim (fun j => genSum (integralTerm hL'd hL'n hlipg hfcg) (digammaMidx K j)) _)
  exact Rlim_congr _ _ _ _ (fun j => genSum_congr _ _ hterm _)

/-- A unit term is determined by the integrand on window points `≥ m+1`. -/
theorem integralTerm_congr_ge {f g : Real → Real} {L L' : Q}
    (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlipf : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfcf : ∀ x y, Req x y → Req (f x) (f y))
    (hL'd : 0 < L'.den) (hL'n : 0 ≤ L'.num)
    (hlipg : ∀ x y, Rle (Rabs (Rsub (g x) (g y))) (Rmul (ofQ L' hL'd) (Rabs (Rsub x y))))
    (hfcg : ∀ x y, Req x y → Req (g x) (g y)) (m : Nat)
    (hfg : ∀ x, Rle (ofQ (⟨(m : Int) + 1, 1⟩ : Q) Nat.one_pos) x → Req (f x) (g x)) :
    Req (integralTerm hLd hLn hlipf hfcf m) (integralTerm hL'd hL'n hlipg hfcg m) :=
  riemannIntegralI_congr_unit_mod hLd hLn hlipf hfcf hL'd hL'n hlipg hfcg _ _ Nat.one_pos (by decide)
    (by decide) (fun t ht0 _ => hfg _ (blockPoint_ge m t ht0))

/-- **THE STRIP CAP** `|N⁺(x)·K(x)| ≤ L_{N⁺}` on `x − 1 ≥ 2⁻ᵏ` (the vanishing rate absorbs the pole). -/
theorem fullInt_cap (C : NormCtx) (f g : L2Test) (k : Nat) (x : Real) (hx1 : Rle one x)
    (hxc : Rle (ofQ (dyQ k) (dyQ_den k)) (Rsub x one)) :
    Rle (Rabs ((fullInt C f g k).f x)) (ofQ (archNumC C f g).L (archNumC C f g).hLd) := by
  rw [fullInt_f]
  have hKnn : Rnonneg ((archKernFull (dyQ k) (dyQ_num k) (dyQ_den k)).f x) := by
    rw [archKernFull_f]; exact Rnonneg_clampedInv _ _ _ _
  have hx1' : Rnonneg (Rsub x one) := Rnonneg_of_Rle_zero (Rle_trans (Rle_of_Req (Req_symm (Radd_neg one)))
    (Rsub_le_mono hx1 (Rle_refl one)))
  refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
  refine Rle_trans (Rle_of_Req (Rmul_congr (Req_refl _) (Rabs_of_nonneg hKnn))) ?_
  refine Rle_trans (Rmul_le_Rmul_right hKnn (archNumC_abs_le_dist_one C f g x)) ?_
  refine Rle_trans (Rle_of_Req (Rmul_assoc _ _ _)) ?_
  refine Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ _ (archNumC C f g).hLn)
    (Rle_trans (Rle_of_Req (Rmul_congr (Rabs_of_nonneg hx1') (Req_refl _)))
      (archKernFull_cap (dyQ k) (dyQ_num k) (dyQ_den k) x hx1 hxc))) ?_
  exact Rle_of_Req (Rmul_one _)

/-- `m+1 ≤ Bd.num` from `⟨m+1,1⟩ < Bd`. -/
theorem le_Bd_num_of_lt (G : ClosedGeom) (m : Nat) (hlt : Qlt (⟨(m : Int) + 1, 1⟩ : Q) G.Bd) :
    (m : Int) + 1 ≤ G.Bd.num := by
  have h := hlt
  simp only [Qlt] at h
  push_cast at h
  have hd : (1 : Int) ≤ (G.Bd.den : Int) := by have := G.hBdd; omega
  have h2 : ((m : Int) + 1) * 1 ≤ ((m : Int) + 1) * (G.Bd.den : Int) :=
    Int.mul_le_mul_of_nonneg_left hd (by omega)
  omega

/-- The far constant `CF = ⌈K_l + M·Bd.num⌉ + 1`. -/
def archCF (C : NormCtx) (f g : L2Test) : Nat :=
  (add (archKl C.geom f g) (mul (archNumC C f g).M (⟨C.geom.Bd.num, 1⟩ : Q))).num.toNat + 1

theorem archCF_ge_Kl (C : NormCtx) (f g : L2Test) :
    Qle (archKl C.geom f g) (⟨((archCF C f g : Nat) : Int), 1⟩ : Q) := by
  have hBdn : 0 < C.geom.Bd.num := qnum_pos_of_one_le C.geom.hBdd C.geom.hBd1
  have hMB : 0 ≤ (mul (archNumC C f g).M (⟨C.geom.Bd.num, 1⟩ : Q)).num :=
    Int.mul_nonneg (archNumC C f g).hMn (Int.le_of_lt hBdn)
  refine Qle_trans (add_den_pos (archKl_den C.geom f g) (Qmul_den_pos (archNumC C f g).hMd Nat.one_pos))
    (Qle_self_add hMB) ?_
  exact Qle_num_cap _ (add_den_pos (archKl_den C.geom f g) (Qmul_den_pos (archNumC C f g).hMd Nat.one_pos))
    (Qadd_num_nonneg_loc (archKl_num C.geom f g) hMB)

theorem archCF_ge_MB (C : NormCtx) (f g : L2Test) :
    Qle (mul (archNumC C f g).M (⟨C.geom.Bd.num, 1⟩ : Q)) (⟨((archCF C f g : Nat) : Int), 1⟩ : Q) := by
  have hBdn : 0 < C.geom.Bd.num := qnum_pos_of_one_le C.geom.hBdd C.geom.hBd1
  have hMB : 0 ≤ (mul (archNumC C f g).M (⟨C.geom.Bd.num, 1⟩ : Q)).num :=
    Int.mul_nonneg (archNumC C f g).hMn (Int.le_of_lt hBdn)
  refine Qle_trans (add_den_pos (archKl_den C.geom f g) (Qmul_den_pos (archNumC C f g).hMd Nat.one_pos))
    (Qle_self_add_l (archKl_num C.geom f g)) ?_
  exact Qle_num_cap _ (add_den_pos (archKl_den C.geom f g) (Qmul_den_pos (archNumC C f g).hMd Nat.one_pos))
    (Qadd_num_nonneg_loc (archKl_num C.geom f g) hMB)

/-- `1/((M+1)M) ≤ 1/(j+1)` for `j+1 ≤ M`. -/
theorem qinv_block_le (M j : Nat) (hM : j + 1 ≤ M) :
    Qle (⟨1, (M + 1) * M⟩ : Q) (⟨1, j + 1⟩ : Q) := by
  show (1 : Int) * ((j + 1 : Nat) : Int) ≤ 1 * (((M + 1) * M : Nat) : Int)
  have h : j + 1 ≤ (M + 1) * M := Nat.le_trans hM (Nat.le_mul_of_pos_left M (by omega))
  have h' := Int.ofNat_le.mpr h
  push_cast at h' ⊢
  omega

/-- `⟨CF,1⟩·⟨1,j+1⟩ = ⟨CF, j+1⟩`. -/
theorem qCF_mul_inv (CF j : Nat) :
    Qeq (mul (⟨(CF : Int), 1⟩ : Q) (⟨1, j + 1⟩ : Q)) (⟨(CF : Int), j + 1⟩ : Q) := by
  simp only [Qeq, mul]; push_cast; ring_uor


-- ===========================================================================
-- (5) THE FAR-WINDOW RATE for the truncation family.
-- ===========================================================================

/-- `|∫_{[M_j+1, M_j+1+Δ]} g_{k,δ}| ≤ CF/(j+1)` (`δ ≥ 0`, `0 < Δ ≤ 1`), `M_j = digammaMidx archKC j`. -/
theorem truncFar (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g)
    (k : Nat) (δ : Q) (hδd : 0 < δ.den) (hδn : 0 ≤ δ.num) (Δ : Q) (hΔd : 0 < Δ.den) (hΔn : 0 < Δ.num)
    (hΔ1 : Qle Δ (⟨1, 1⟩ : Q)) (j : Nat) :
    Rle (Rabs (riemannIntegralI (truncInt C f g k δ hδd).hLd (truncInt C f g k δ hδd).hLn
        (truncInt C f g k δ hδd).hlip (truncInt C f g k δ hδd).hfc
        (⟨((digammaMidx (archKC C f g) j : Nat) : Int) + 1, 1⟩ : Q) Δ Nat.one_pos hΔd (Int.le_of_lt hΔn)))
      (ofQ (⟨((archCF C f g : Nat) : Int), j + 1⟩ : Q) (Nat.succ_pos j)) := by
  have hMj : j + 1 ≤ digammaMidx (archKC C f g) j := digammaMidx_ge _ j
  have hM1 : 1 ≤ digammaMidx (archKC C f g) j := digammaMidx_ge_one _ j
  have hm1n : (0 : Int) < ((digammaMidx (archKC C f g) j : Nat) : Int) + 1 := by omega
  have hm0n : (0 : Int) < ((digammaMidx (archKC C f g) j : Nat) : Int) := by omega
  have hpt : ∀ t : Real, Rle zero t →
      Rle (ofQ (⟨((digammaMidx (archKC C f g) j : Nat) : Int) + 1, 1⟩ : Q) Nat.one_pos)
        (Radd (affineMap (⟨((digammaMidx (archKC C f g) j : Nat) : Int) + 1, 1⟩ : Q) Δ Nat.one_pos hΔd t)
          (ofQ δ hδd)) :=
    fun t ht0 => Rle_trans (affine_ge_lo _ _ Nat.one_pos hΔd (Int.le_of_lt hΔn) t ht0)
      (Rle_self_Radd_right (Rnonneg_ofQ hδd hδn))
  have hKnn : ∀ x, Rnonneg ((archKernFull (dyQ k) (dyQ_num k) (dyQ_den k)).f x) := fun x => by
    rw [archKernFull_f]; exact Rnonneg_clampedInv (dyQ k) (dyQ_num k) (dyQ_den k) (innerXm x)
  rcases Qle_or_Qlt C.geom.Bd (⟨((digammaMidx (archKC C f g) j : Nat) : Int) + 1, 1⟩ : Q) with hpast | hearly
  · -- LATE
    have hBLd : 0 < (mul (mul (archKl C.geom f g)
        (Qinv (⟨((digammaMidx (archKC C f g) j : Nat) : Int) + 1, 1⟩ : Q)))
        (Qinv (⟨((digammaMidx (archKC C f g) j : Nat) : Int), 1⟩ : Q))).den :=
      Qmul_den_pos (Qmul_den_pos (archKl_den C.geom f g) (Qinv_den_pos hm1n)) (Qinv_den_pos hm0n)
    have hBLn : 0 ≤ (mul (mul (archKl C.geom f g)
        (Qinv (⟨((digammaMidx (archKC C f g) j : Nat) : Int) + 1, 1⟩ : Q)))
        (Qinv (⟨((digammaMidx (archKC C f g) j : Nat) : Int), 1⟩ : Q))).num :=
      Int.mul_nonneg (Int.mul_nonneg (archKl_num C.geom f g) (Int.le_of_lt (Qinv_num_pos Nat.one_pos)))
        (Int.le_of_lt (Qinv_num_pos Nat.one_pos))
    refine Rle_trans (riemannIntegralI_abs_le_window (truncInt C f g k δ hδd).hLd
      (truncInt C f g k δ hδd).hLn (truncInt C f g k δ hδd).hlip (truncInt C f g k δ hδd).hfc
      _ Δ _ Nat.one_pos hΔd (Int.le_of_lt hΔn) hBLd ?_) ?_
    · intro t ht0 _
      have hx := hpt t ht0
      rw [truncInt_f]
      have hNb := archNumC_late_bound C f g hf hg _ hm1n Nat.one_pos _ hx hpast
      have hkb := archKernFull_le_inv (dyQ k) (dyQ_num k) (dyQ_den k) _ hM1 _ hx
      refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
      refine Rle_trans (Rmul_le_Rmul_both (Rnonneg_Rabs _)
        (Rnonneg_ofQ (Qinv_den_pos hm0n) (Int.le_of_lt (Qinv_num_pos Nat.one_pos)))
        hNb (Rle_trans (Rle_of_Req (Rabs_of_nonneg (hKnn _))) hkb)) ?_
      refine Rle_of_Req (Req_trans (Rmul_congr
        (Rmul_ofQ_ofQ (archKl_den C.geom f g) (Qinv_den_pos hm1n)) (Req_refl _)) ?_)
      exact Rmul_ofQ_ofQ (Qmul_den_pos (archKl_den C.geom f g) (Qinv_den_pos hm1n)) (Qinv_den_pos hm0n)
    · refine Rle_ofQ_ofQ (Qmul_den_pos hΔd hBLd) (Nat.succ_pos j) ?_
      -- Δ·B ≤ 1·B = B = K_l/((M+1)M) ≤ K_l/(j+1) ≤ CF/(j+1)
      refine Qle_trans (Qmul_den_pos Nat.one_pos hBLd) (Qmul_le_mul_right hBLn hΔ1) ?_
      refine Qle_trans hBLd (Qeq_le (Qone_mul _)) ?_
      refine Qle_trans (Qmul_den_pos (archKl_den C.geom f g) (digamma_succ_mul_pos hM1))
        (Qeq_le (late_product_eq (archKl C.geom f g) _ hM1)) ?_
      refine Qle_trans (Qmul_den_pos (archKl_den C.geom f g) (Nat.succ_pos j))
        (Qmul_le_mul_left (archKl_num C.geom f g) (qinv_block_le _ j hMj)) ?_
      refine Qle_trans (Qmul_den_pos Nat.one_pos (Nat.succ_pos j))
        (Qmul_le_mul_right (show (0 : Int) ≤ 1 by decide) (archCF_ge_Kl C f g)) ?_
      exact Qeq_le (qCF_mul_inv _ j)
  · -- EARLY
    refine Rle_trans (riemannIntegralI_abs_le_window (truncInt C f g k δ hδd).hLd
      (truncInt C f g k δ hδd).hLn (truncInt C f g k δ hδd).hlip (truncInt C f g k δ hδd).hfc
      _ Δ (archNumC C f g).M Nat.one_pos hΔd (Int.le_of_lt hΔn) (archNumC C f g).hMd ?_) ?_
    · intro t ht0 _
      have hx := hpt t ht0
      rw [truncInt_f]
      have hkb := archKernFull_le_inv (dyQ k) (dyQ_num k) (dyQ_den k) _ hM1 _ hx
      have hk1 : Rle ((archKernFull (dyQ k) (dyQ_num k) (dyQ_den k)).f _) one :=
        Rle_trans hkb (Rle_ofQ_ofQ _ (by decide) (qinv_nat_le_one _ hM1))
      refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
      refine Rle_trans (Rmul_le_Rmul_both (Rnonneg_Rabs _) (Rnonneg_ofQ (by decide) (by decide))
        ((archNumC C f g).hbd _) (Rle_trans (Rle_of_Req (Rabs_of_nonneg (hKnn _))) hk1)) ?_
      exact Rle_of_Req (Rmul_one _)
    · refine Rle_ofQ_ofQ (Qmul_den_pos hΔd (archNumC C f g).hMd) (Nat.succ_pos j) ?_
      refine Qle_trans (Qmul_den_pos Nat.one_pos (archNumC C f g).hMd)
        (Qmul_le_mul_right (archNumC C f g).hMn hΔ1) ?_
      refine Qle_trans (archNumC C f g).hMd (Qeq_le (Qone_mul _)) ?_
      -- M ≤ CF/(j+1):  M.num·(j+1) ≤ M.num·Bd.num ≤ CF·M.den
      have hjB : ((j : Nat) : Int) + 1 ≤ C.geom.Bd.num := by
        have h1 := le_Bd_num_of_lt C.geom (digammaMidx (archKC C f g) j) hearly
        have h2 : ((j : Nat) : Int) + 1 ≤ ((digammaMidx (archKC C f g) j : Nat) : Int) + 1 := by
          have := Int.ofNat_le.mpr hMj; push_cast at this; omega
        omega
      have hMB := archCF_ge_MB C f g
      simp only [Qle, mul] at hMB
      push_cast at hMB
      show (archNumC C f g).M.num * ((j + 1 : Nat) : Int)
        ≤ ((archCF C f g : Nat) : Int) * ((archNumC C f g).M.den : Int)
      push_cast
      have h3 : (archNumC C f g).M.num * ((j : Int) + 1) ≤ (archNumC C f g).M.num * C.geom.Bd.num :=
        Int.mul_le_mul_of_nonneg_left hjB (archNumC C f g).hMn
      have e1 : (archNumC C f g).M.num * C.geom.Bd.num * 1 = (archNumC C f g).M.num * C.geom.Bd.num := by
        ring_uor
      have e2 : ((archCF C f g : Nat) : Int) * ((archNumC C f g).M.den * 1 : Int)
          = ((archCF C f g : Nat) : Int) * ((archNumC C f g).M.den : Int) := by ring_uor
      omega

-- ===========================================================================
-- (6) Dyadic bookkeeping.
-- ===========================================================================

theorem dyQ_add_le (k : Nat) : ∀ d, Qle (dyQ (k + d)) (dyQ k)
  | 0 => Qle_refl _
  | (d + 1) => Qle_trans (dyQ_den _) (dyQ_succ_le (k + d)) (dyQ_add_le k d)

theorem dyQ_le_one (k : Nat) : Qle (dyQ k) (⟨1, 1⟩ : Q) := by
  show (1 : Int) * ((1 : Nat) : Int) ≤ 1 * ((2 ^ k : Nat) : Int)
  have h : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have h' := Int.ofNat_le.mpr h
  push_cast at h' ⊢
  omega

/-- `0 < 2⁻ᵏ − 2⁻ᵏ⁻ᵈ` for `d ≥ 1`. -/
theorem dyQ_sub_num_pos (k d : Nat) (hd : 1 ≤ d) : 0 < (Qsub (dyQ k) (dyQ (k + d))).num := by
  refine Qsub_num_pos_of_lt ?_
  show (1 : Int) * ((2 ^ k : Nat) : Int) < 1 * ((2 ^ (k + d) : Nat) : Int)
  have h2d : 2 ^ 1 ≤ 2 ^ d := Nat.pow_le_pow_right (by decide) hd
  have hmul : 2 ^ k * 2 ≤ 2 ^ (k + d) := by
    rw [Nat.pow_add]; exact Nat.mul_le_mul_left (2 ^ k) (by simpa using h2d)
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have h : 2 ^ k < 2 ^ (k + d) := by omega
  have h' := Int.ofNat_lt.mpr h
  omega

/-- `2⁻ᵏ − 2⁻ᵏ⁻ᵈ ≤ 2⁻ᵏ`. -/
theorem dyQ_sub_le (k d : Nat) : Qle (Qsub (dyQ k) (dyQ (k + d))) (dyQ k) := by
  have h : Qle (Qsub (dyQ k) (dyQ (k + d))) (Qsub (dyQ k) (⟨0, 1⟩ : Q)) :=
    Qsub_le_sub_right_of (Int.le_of_lt (dyQ_num (k + d)))
  exact Qle_trans (Qsub_den_pos (dyQ_den k) Nat.one_pos) h (Qeq_le (by
    simp only [Qeq, Qsub, add, neg]; push_cast; ring_uor))
  where
    Qsub_le_sub_right_of {a b : Q} (hb : 0 ≤ b.num) : Qle (Qsub a b) (Qsub a (⟨0, 1⟩ : Q)) := by
      simp only [Qle, Qsub, add, neg]
      push_cast
      have hd : (0 : Int) ≤ (a.den : Int) := Int.ofNat_nonneg _
      have hbd : (0 : Int) ≤ (b.den : Int) := Int.ofNat_nonneg _
      have h1 : 0 ≤ b.num * (a.den : Int) := Int.mul_nonneg hb hd
      have e : (a.num * (b.den : Int) + -b.num * (a.den : Int)) * ((a.den : Int) * 1)
          = (a.num * 1 + -0 * (a.den : Int)) * ((a.den : Int) * (b.den : Int))
            - (b.num * (a.den : Int)) * (a.den : Int) := by ring_uor
      have h2 : 0 ≤ (b.num * (a.den : Int)) * (a.den : Int) := Int.mul_nonneg h1 hd
      omega


-- ===========================================================================
-- (7) THE STEP IDENTITY: `T(k+d) = ∫_{[1+2⁻ᵏ⁻ᵈ, 1+2⁻ᵏ]} + T(k)`.
-- ===========================================================================

/-- Window points `u ≥ 1` shifted by `δ ≥ 0` satisfy `x ≥ 1` and `x − 1 ≥ δ`. -/
theorem shifted_pt_facts (δ : Q) (hδd : 0 < δ.den) (hδn : 0 ≤ δ.num) (u : Real) (hu : Rle one u) :
    Rle one (Radd u (ofQ δ hδd)) ∧ Rle (ofQ δ hδd) (Rsub (Radd u (ofQ δ hδd)) one) := by
  have h1 : Rle (ofQ (add (⟨1, 1⟩ : Q) δ) (add_den_pos (by decide) hδd)) (Radd u (ofQ δ hδd)) :=
    Rle_trans (Rle_of_Req (Req_symm (Radd_ofQ_ofQ (by decide) hδd))) (Radd_le_add hu (Rle_refl _))
  exact ⟨Rle_trans hu (Rle_self_Radd_right (Rnonneg_ofQ hδd hδn)), sub_one_ge_of_ge_add hδd h1⟩

/-- **THE STEP IDENTITY** (`d ≥ 1`): the truncation at `1+2⁻ᵏ⁻ᵈ` is the strip `[1+2⁻ᵏ⁻ᵈ, 1+2⁻ᵏ]` plus
    the truncation at `1+2⁻ᵏ` — the improper split at the same constant, the shift congruence, and
    the block-wise kernel-floor congruence (both floors are below `x − 1` on `[1+2⁻ᵏ, ∞)`). -/
theorem archTrunc_step (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g)
    (k d : Nat) (hd : 1 ≤ d) :
    Req (archTrunc C f g hf hg (k + d))
        (Radd (riemannIntegralI (truncInt C f g (k + d) (dyQ (k + d)) (dyQ_den (k + d))).hLd
            (truncInt C f g (k + d) (dyQ (k + d)) (dyQ_den (k + d))).hLn
            (truncInt C f g (k + d) (dyQ (k + d)) (dyQ_den (k + d))).hlip
            (truncInt C f g (k + d) (dyQ (k + d)) (dyQ_den (k + d))).hfc
            (⟨1, 1⟩ : Q) (Qsub (dyQ k) (dyQ (k + d))) Nat.one_pos
            (Qsub_den_pos (dyQ_den k) (dyQ_den (k + d))) (Int.le_of_lt (dyQ_sub_num_pos k d hd)))
          (archTrunc C f g hf hg k)) := by
  have hΔd : 0 < (Qsub (dyQ k) (dyQ (k + d))).den := Qsub_den_pos (dyQ_den k) (dyQ_den (k + d))
  have hΔn := dyQ_sub_num_pos k d hd
  have hΔ1 : Qle (Qsub (dyQ k) (dyQ (k + d))) (⟨1, 1⟩ : Q) :=
    Qle_trans (dyQ_den k) (dyQ_sub_le k d) (dyQ_le_one k)
  have hsumn : 0 ≤ (add (dyQ (k + d)) (Qsub (dyQ k) (dyQ (k + d)))).num :=
    Qadd_num_nonneg_loc (Int.le_of_lt (dyQ_num (k + d))) (Int.le_of_lt hΔn)
  -- the split
  have hsplit := improper_split_shift (fullInt C f g (k + d)) (dyQ (k + d)) (Qsub (dyQ k) (dyQ (k + d)))
    (dyQ_den (k + d)) hΔd hΔn (archKC_den C f g) (archKC_num C f g)
    (truncDecay C f g hf hg (k + d) (dyQ (k + d)) (dyQ_den (k + d)) (Int.le_of_lt (dyQ_num (k + d))))
    (truncDecay C f g hf hg (k + d) (add (dyQ (k + d)) (Qsub (dyQ k) (dyQ (k + d))))
      (add_den_pos (dyQ_den (k + d)) hΔd) hsumn)
    (archCF C f g)
    (truncFar C f g hf hg (k + d) (dyQ (k + d)) (dyQ_den (k + d)) (Int.le_of_lt (dyQ_num (k + d)))
      (Qsub (dyQ k) (dyQ (k + d))) hΔd hΔn hΔ1)
  refine Req_trans hsplit (Radd_congr (Req_refl _) ?_)
  -- shift congruence: δ_{k+d} + Δ = δ_k
  refine Req_trans (improperIntegral1_congr _ _ _ _ _ _ (archKC_den C f g) (archKC_num C f g)
    (truncDecay C f g hf hg (k + d) (add (dyQ (k + d)) (Qsub (dyQ k) (dyQ (k + d))))
      (add_den_pos (dyQ_den (k + d)) hΔd) hsumn)
    (truncDecay C f g hf hg (k + d) (dyQ k) (dyQ_den k) (Int.le_of_lt (dyQ_num k)))
    (fun u => shiftTest_congr_shift _ _ _ _ (Qadd_Qsub_cancel (dyQ (k + d)) (dyQ k)) (fullInt C f g (k + d)) u)) ?_
  -- kernel-floor congruence, block-wise
  show Req (improperIntegral1 (truncInt C f g (k + d) (dyQ k) (dyQ_den k)).hLd
      (truncInt C f g (k + d) (dyQ k) (dyQ_den k)).hLn (truncInt C f g (k + d) (dyQ k) (dyQ_den k)).hlip
      (truncInt C f g (k + d) (dyQ k) (dyQ_den k)).hfc (archKC_den C f g) (archKC_num C f g) _)
    (improperIntegral1 (truncInt C f g k (dyQ k) (dyQ_den k)).hLd
      (truncInt C f g k (dyQ k) (dyQ_den k)).hLn (truncInt C f g k (dyQ k) (dyQ_den k)).hlip
      (truncInt C f g k (dyQ k) (dyQ_den k)).hfc (archKC_den C f g) (archKC_num C f g) _)
  refine improperIntegral1_congr_terms _ _ _ _ _ _ _ _ (archKC_den C f g) (archKC_num C f g) _ _
    (fun m => integralTerm_congr_ge _ _ _ _ _ _ _ _ m (fun u hu => ?_))
  rw [truncInt_f, truncInt_f]
  have hu1 : Rle one u := Rle_trans (Rle_ofQ_ofQ (by decide) Nat.one_pos (by
    show (1 : Int) * ((1 : Nat) : Int) ≤ ((m : Int) + 1) * ((1 : Nat) : Int); push_cast; omega)) hu
  obtain ⟨hx1, hxc⟩ := shifted_pt_facts (dyQ k) (dyQ_den k) (Int.le_of_lt (dyQ_num k)) u hu1
  refine Rmul_congr (Req_refl _) ?_
  exact archKernFull_inert_pair (dyQ (k + d)) (dyQ k) (dyQ_num _) (dyQ_den _) (dyQ_num k) (dyQ_den k)
    _ hx1 (Rle_trans (Rle_ofQ_ofQ (dyQ_den _) (dyQ_den k) (dyQ_add_le k d)) hxc) hxc

-- ===========================================================================
-- (8) THE CAUCHY RATE and THE LOWER-END LIMIT.
-- ===========================================================================

/-- The integer cap `CNC = ⌈L_{N⁺}⌉ + 1` of the numerator's Lipschitz modulus. -/
def archCNC (C : NormCtx) (f g : L2Test) : Nat := (archNumC C f g).L.num.toNat + 1

theorem archCNC_ge (C : NormCtx) (f g : L2Test) :
    Qle (archNumC C f g).L (⟨(archCNC C f g : Int), 1⟩ : Q) :=
  Qle_num_cap _ (archNumC C f g).hLd (archNumC C f g).hLn

/-- **THE STRIP BOUND** `|T(k+d) − T(k)| ≤ CNC·2⁻ᵏ` — the strip has width `≤ 2⁻ᵏ` and the integrand
    is capped by `L_{N⁺}` there (the numerator-vanishing rate). -/
theorem archTrunc_diff_le (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g)
    (k d : Nat) :
    Rle (Rabs (Rsub (archTrunc C f g hf hg (k + d)) (archTrunc C f g hf hg k)))
        (ofQ (⟨(archCNC C f g : Int), 2 ^ k⟩ : Q) (Nat.two_pow_pos k)) := by
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · subst hd0
    refine Rle_trans (Rle_of_Req (Req_trans (Rabs_congr (Radd_neg _)) Rabs_zero)) ?_
    exact Rle_zero_of_Rnonneg (Rnonneg_ofQ _ (by show (0 : Int) ≤ (archCNC C f g : Int); omega))
  · have hstep := archTrunc_step C f g hf hg k d hd
    refine Rle_trans (Rle_of_Req (Rabs_congr (Req_trans (Rsub_congr hstep (Req_refl _))
      (Radd_sub_cancel_right _ _)))) ?_
    have hΔd : 0 < (Qsub (dyQ k) (dyQ (k + d))).den := Qsub_den_pos (dyQ_den k) (dyQ_den (k + d))
    refine Rle_trans (riemannIntegralI_abs_le_window_real _ _ _ _ (⟨1, 1⟩ : Q) _
      (ofQ (archNumC C f g).L (archNumC C f g).hLd) Nat.one_pos hΔd (Int.le_of_lt (dyQ_sub_num_pos k d hd))
      (fun t ht0 _ => ?_)) ?_
    · rw [truncInt_f]
      have hu1 : Rle one (affineMap (⟨1, 1⟩ : Q) (Qsub (dyQ k) (dyQ (k + d))) Nat.one_pos hΔd t) :=
        affine_ge_lo _ _ Nat.one_pos hΔd (Int.le_of_lt (dyQ_sub_num_pos k d hd)) t ht0
      obtain ⟨hx1, hxc⟩ := shifted_pt_facts (dyQ (k + d)) (dyQ_den (k + d)) (Int.le_of_lt (dyQ_num (k + d))) _ hu1
      exact fullInt_cap C f g (k + d) _ hx1 hxc
    · refine Rle_trans (Rle_of_Req (Rmul_ofQ_ofQ hΔd (archNumC C f g).hLd)) ?_
      refine Rle_ofQ_ofQ _ (Nat.two_pow_pos k) ?_
      -- Δ·L ≤ 2⁻ᵏ·CNC = ⟨CNC, 2^k⟩
      refine Qle_trans (Qmul_den_pos (dyQ_den k) (archNumC C f g).hLd)
        (Qmul_le_mul_right (archNumC C f g).hLn (dyQ_sub_le k d)) ?_
      refine Qle_trans (Qmul_den_pos (dyQ_den k) Nat.one_pos)
        (Qmul_le_mul_left (Int.le_of_lt (dyQ_num k)) (archCNC_ge C f g)) ?_
      exact Qeq_le (by simp only [Qeq, mul, dyQ]; push_cast; ring_uor)

/-- The pairwise regularity bound of the reindexed truncations. -/
def archC (C : NormCtx) (f g : L2Test) (j k : Nat) : Q :=
  add (⟨(archCNC C f g : Int), 2 ^ (j + archCNC C f g)⟩ : Q)
      (⟨(archCNC C f g : Int), 2 ^ (k + archCNC C f g)⟩ : Q)

theorem archC_den (C : NormCtx) (f g : L2Test) (j k : Nat) : 0 < (archC C f g j k).den :=
  add_den_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)

theorem archC_addend_le (C : NormCtx) (f g : L2Test) (j : Nat) :
    Qle (⟨(archCNC C f g : Int), 2 ^ (j + archCNC C f g)⟩ : Q) (⟨1, j + 1⟩ : Q) := by
  show ((archCNC C f g : Nat) : Int) * ((j + 1 : Nat) : Int)
    ≤ 1 * ((2 ^ (j + archCNC C f g) : Nat) : Int)
  have hNat : archCNC C f g * (j + 1) ≤ 2 ^ (j + archCNC C f g) := by
    have h1 : archCNC C f g ≤ 2 ^ archCNC C f g := Nat.le_of_lt (Nat.lt_two_pow_self)
    have h2 : j + 1 ≤ 2 ^ j := Nat.lt_two_pow_self
    calc archCNC C f g * (j + 1) ≤ 2 ^ archCNC C f g * 2 ^ j := Nat.mul_le_mul h1 h2
      _ = 2 ^ (j + archCNC C f g) := by rw [← Nat.pow_add, Nat.add_comm]
  calc ((archCNC C f g : Nat) : Int) * ((j + 1 : Nat) : Int)
      = ((archCNC C f g * (j + 1) : Nat) : Int) := by push_cast; ring_uor
    _ ≤ ((2 ^ (j + archCNC C f g) : Nat) : Int) := Int.ofNat_le.mpr hNat
    _ = 1 * ((2 ^ (j + archCNC C f g) : Nat) : Int) := by ring_uor

theorem archC_le (C : NormCtx) (f g : L2Test) (j k : Nat) :
    Qle (archC C f g j k) (add (⟨1, j + 1⟩ : Q) (⟨1, k + 1⟩ : Q)) :=
  Qadd_le_add (archC_addend_le C f g j) (archC_addend_le C f g k)

theorem archX_bound (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g)
    (j k : Nat) :
    Rle (Rsub (archTrunc C f g hf hg (j + archCNC C f g)) (archTrunc C f g hf hg (k + archCNC C f g)))
        (ofQ (archC C f g j k) (archC_den C f g j k)) := by
  rcases Nat.le_total k j with hkj | hjk
  · have he : j + archCNC C f g = (k + archCNC C f g) + (j - k) := by omega
    have hd := archTrunc_diff_le C f g hf hg (k + archCNC C f g) (j - k)
    rw [← he] at hd
    refine Rle_trans (Rle_of_Rabs_le hd) ?_
    refine Rle_ofQ_ofQ (Nat.two_pow_pos _) (archC_den C f g j k) ?_
    exact Qle_self_add_l (by show (0 : Int) ≤ (archCNC C f g : Int); omega)
  · have he : k + archCNC C f g = (j + archCNC C f g) + (k - j) := by omega
    have hd := archTrunc_diff_le C f g hf hg (j + archCNC C f g) (k - j)
    rw [← he] at hd
    have hflip : Req (Rabs (Rsub (archTrunc C f g hf hg (k + archCNC C f g))
          (archTrunc C f g hf hg (j + archCNC C f g))))
        (Rabs (Rsub (archTrunc C f g hf hg (j + archCNC C f g))
          (archTrunc C f g hf hg (k + archCNC C f g)))) :=
      Req_trans (Req_symm (Rabs_Rneg _)) (Rabs_congr (Rneg_Rsub _ _))
    have hd' := Rle_trans (Rle_of_Req (Req_symm hflip)) hd
    refine Rle_trans (Rle_of_Rabs_le hd') ?_
    refine Rle_ofQ_ofQ (Nat.two_pow_pos _) (archC_den C f g j k) ?_
    exact Qle_self_add (by show (0 : Int) ≤ (archCNC C f g : Int); omega)

/-- **The reindexed truncations are Bishop-regular.** -/
theorem archX_RReg (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g) :
    RReg (fun j => archTrunc C f g hf hg (j + archCNC C f g)) :=
  RReg_of_real_bound _ (archC C f g) (archC_den C f g) (archC_le C f g) (archX_bound C f g hf hg)

/-- **★ THE INDEPENDENT, UNSPLIT ARCHIMEDEAN INTEGRAL**
    `ArchIntegral = lim_{k→∞} ∫_{1+2⁻ᵏ}^{∞} (F⁺_{f,g}+F⁺_{g,f}−2F⁺_{f,g}(1)/x)/(x − x⁻¹) dx`
    — the Bishop limit (lower end) of the improper integrals (upper end) of the UNSPLIT integrand,
    with the PROVED geometric regularity from the numerator-vanishing rate.  Defined without reference
    to `ArchTailForm` or its `Reg + Near + Far` decomposition; no endpoint value is invented. -/
def ArchIntegral (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g) : Real :=
  Rlim (fun j => archTrunc C f g hf hg (j + archCNC C f g)) (archX_RReg C f g hf hg)


end UOR.Bridge.F1Square.Square
