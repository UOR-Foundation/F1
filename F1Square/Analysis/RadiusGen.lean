import F1Square.Analysis.RlogMulSigned

/-!
# General-radius (`ρ < 1`) artanh continuity — toward fully general `Rlog`/`Clog`

The bounded/symmetric-band discharges (`RlogMulPos`, `RlogMulSigned`) are gated by the small-radius
constraint `ρ² ≤ 1/2` in the artanh continuity lemmas (`Rartanh_congr`, `Rartanh_radius_indep`),
inherited from `geoEvenSum_le_two` (the even geometric sum `Σρ^{2k} ≤ 2`). For large moduli the
radius `ρ_B = (B−1)/(B+1)` approaches 1, so `ρ² ≤ 1/2` fails.

Key observation: `geoEvenSum ρ N ≤ 1/(1−ρ²) ≤ d²/(2d−1) ~ d/2` (`d = ρ.den`), while the artanh
reindex factor is `ρ.den²+4ρ.den ~ d²`. So the **existing reindex already absorbs** the general
`1/(1−ρ²)` bound — `ρ²≤1/2` is needed only for the clean constant `2`, not for convergence. This file
generalizes the continuity lemmas to any `ρ < 1` with an explicit absorbable bound `K`.
-/

namespace UOR.Bridge.F1Square.Analysis

/-- **General even-geometric-sum bound** `Σ_{k≤N} ρ^{2k} ≤ K` for any `K ≥ 1/(1−ρ²)` (`K·(1−ρ²) ≥ 1`).
    Generalizes `geoEvenSum_le_two` (`K = 2`, `ρ² ≤ 1/2`) to arbitrary `ρ < 1` via `mul_div_gen`. -/
theorem geoEvenSum_le_gen {ρ K : Q} (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (hKd : 0 < K.den) (hK0 : 0 ≤ K.num)
    (hKF : Qle (⟨1, 1⟩ : Q) (mul K (Qsub ⟨1, 1⟩ (mul ρ ρ)))) (N : Nat) :
    Qle (geoEvenSum ρ N) K := by
  have hsd : 0 < (Qsub (⟨1, 1⟩ : Q) (mul ρ ρ)).den := Qsub_den_pos Nat.one_pos (Qmul_den_pos hρd hρd)
  have hab : Qle (mul (geoEvenSum ρ N) (Qsub ⟨1, 1⟩ (mul ρ ρ))) ⟨1, 1⟩ :=
    Qle_trans (add_den_pos (Qmul_den_pos (geoEvenSum_den_pos hρd N) hsd) (qpow_den_pos hρd _))
      (Qle_self_add (qpow_nonneg hρ0 (2 * N + 2)))
      (Qeq_le (geoEven_eq hρd N))
  exact Qle_trans (Qmul_den_pos hKd Nat.one_pos)
    (mul_div_gen (geoEvenSum_num_nonneg hρ0 N) (geoEvenSum_den_pos hρd N) hsd hKd hK0 hKF hab)
    (Qeq_le (mul_one K))

set_option maxHeartbeats 800000 in
/-- **General-radius `Rartanh` argument-congruence**: `Req t t' ⟹ Req (Rartanh t) (Rartanh t')` for any
    `ρ < 1` (no `ρ² ≤ 1/2`). The even-sum bound `geoEvenSum ≤ K` (`K·(1−ρ²) ≥ 1`, `K` a Nat) is absorbed
    by the artanh reindex provided `K ≤ 2(ρ.den²+4ρ.den)` (`hKr`) — which holds for every `ρ < 1`. The
    generalization of `Rartanh_congr` past the small-radius cap. -/
theorem Rartanh_congr_gen (t t' : Real) (ρ : Q) (K : Nat) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (hlt : ρ.num.toNat < ρ.den)
    (hKF : Qle (⟨1, 1⟩ : Q) (mul (⟨(K : Int), 1⟩ : Q) (Qsub ⟨1, 1⟩ (mul ρ ρ))))
    (hKr : K ≤ 2 * (ρ.den * ρ.den + 4 * ρ.den))
    (hbt : ∀ n, Qle (Qabs (t.seq n)) ρ) (hbt' : ∀ n, Qle (Qabs (t'.seq n)) ρ) (heq : Req t t') :
    Req (Rartanh t ρ hρ0 hρd hlt hbt) (Rartanh t' ρ hρ0 hρd hlt hbt') := by
  refine Req_of_lin_bound (C := 4) ?_
  intro n
  show Qle (Qabs (Qsub (artSum (t.seq (Rartanh_R ρ n)) (Rartanh_R ρ n))
      (artSum (t'.seq (Rartanh_R ρ n)) (Rartanh_R ρ n)))) (⟨(4 : Int), n + 1⟩ : Q)
  have hdiffd : 0 < (Qsub (t.seq (Rartanh_R ρ n)) (t'.seq (Rartanh_R ρ n))).den :=
    Qsub_den_pos (t.den_pos _) (t'.den_pos _)
  refine Qle_trans (Qmul_den_pos (geoEvenSum_den_pos hρd _) (Qabs_den_pos hdiffd))
    (artSum_Lip_le (t.den_pos _) (t'.den_pos _) hρd (hbt _) (hbt' _) (Rartanh_R ρ n)) ?_
  refine Qle_trans (Qmul_den_pos Nat.one_pos (Qabs_den_pos hdiffd))
    (Qmul_le_mul_right (Qabs_num_nonneg _)
      (geoEvenSum_le_gen hρ0 hρd Nat.one_pos (by exact Int.ofNat_nonneg K) hKF (Rartanh_R ρ n))) ?_
  refine Qle_trans (Qmul_den_pos Nat.one_pos (Nat.succ_pos _))
    (Qmul_le_mul_left (Int.ofNat_nonneg K) (heq (Rartanh_R ρ n))) ?_
  show ((K : Int) * 2) * ((n + 1 : Nat) : Int) ≤ (4 : Int) * ((1 * (Rartanh_R ρ n + 1) : Nat) : Int)
  unfold Rartanh_R
  push_cast
  have hk2 : (K : Int) * 2 ≤ 4 * ((ρ.den : Int) * ρ.den + 4 * ρ.den) := by
    have h := hKr; push_cast at h; omega
  have hmnn : (0 : Int) ≤ (n : Int) + 1 := by omega
  have hprod := Int.mul_le_mul_of_nonneg_right hk2 hmnn
  have e1 : (4 * ((ρ.den : Int) * ρ.den + 4 * ρ.den)) * ((n : Int) + 1)
      = 4 * (((ρ.den : Int) * ρ.den + 4 * ρ.den) * ((n : Int) + 1)) := by
    generalize ((ρ.den : Int) * ρ.den + 4 * ρ.den) = A; generalize ((n : Int) + 1) = m; ring_uor
  have e2 : (4 : Int) * (1 * (((ρ.den : Int) * ρ.den + 4 * ρ.den) * ((n : Int) + 1) + 1))
      = 4 * (((ρ.den : Int) * ρ.den + 4 * ρ.den) * ((n : Int) + 1)) + 4 := by
    generalize ((ρ.den : Int) * ρ.den + 4 * ρ.den) * ((n : Int) + 1) = P; ring_uor
  rw [e1] at hprod; rw [e2]; omega

/-- **General-radius depth-Cauchy bound** for `artSum`: `|artSum u b − artSum u a| ≤ K·σ.den/(n+1)` for
    `a ≤ b`, `n+1 ≤ 2a+3`, any `σ < 1` with the even-sum bound `K` (`K·(1−σ²) ≥ 1`). Generalizes
    `artSum_depth_recip` (`K = 2`, `σ²≤1/2`) by swapping `mul_div2 → mul_div_gen`. -/
theorem artSum_depth_recip_gen (u σ : Q) (K : Nat) (hud : 0 < u.den) (hσ0 : 0 ≤ σ.num) (hσd : 0 < σ.den)
    (hu : Qle (Qabs u) σ) (hKF : Qle (⟨1, 1⟩ : Q) (mul (⟨(K : Int), 1⟩ : Q) (Qsub ⟨1, 1⟩ (mul σ σ))))
    (hσlt : σ.num.toNat < σ.den) {a b n : Nat} (hab : a ≤ b) (hn : n + 1 ≤ 2 * a + 3) :
    Qle (Qabs (Qsub (artSum u b) (artSum u a))) (⟨(K : Int) * (σ.den : Int), n + 1⟩ : Q) := by
  have hWd : 0 < (Qsub (⟨1, 1⟩ : Q) (mul σ σ)).den := Qsub_den_pos Nat.one_pos (Qmul_den_pos hσd hσd)
  have hW : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul σ σ)).num := by
    rcases Int.le_total 0 (Qsub (⟨1, 1⟩ : Q) (mul σ σ)).num with h | h
    · exact h
    · exfalso
      have hKnn : (0 : Int) ≤ (K : Int) := Int.ofNat_nonneg K
      have hkey : ((Qsub (⟨1, 1⟩ : Q) (mul σ σ)).den : Int)
          ≤ (K : Int) * (Qsub (⟨1, 1⟩ : Q) (mul σ σ)).num := by
        have hh := hKF; simp only [Qle, mul] at hh ⊢; push_cast at hh ⊢; omega
      have hmn : (K : Int) * (Qsub (⟨1, 1⟩ : Q) (mul σ σ)).num ≤ (K : Int) * 0 :=
        Int.mul_le_mul_of_nonneg_left h hKnn
      have hd1 : (1 : Int) ≤ ((Qsub (⟨1, 1⟩ : Q) (mul σ σ)).den : Int) := by exact_mod_cast hWd
      simp only [Int.mul_zero] at hmn; omega
  have htrunc := artSum_trunc hud hσ0 hσd hu hW hab
  have hd2 := mul_div_gen (Qabs_num_nonneg _)
    (Qabs_den_pos (Qsub_den_pos (artSum_den_pos hud b) (artSum_den_pos hud a)))
    (Qsub_den_pos Nat.one_pos (Qmul_den_pos hσd hσd)) Nat.one_pos (Int.ofNat_nonneg K) hKF htrunc
  refine Qle_trans (Qmul_den_pos Nat.one_pos (qpow_den_pos hσd _)) hd2 ?_
  refine Qle_trans (Qmul_den_pos Nat.one_pos (Nat.succ_pos n))
    (Qmul_le_mul_left (Int.ofNat_nonneg K) (qpow_le_recip hσ0 hσd hσlt hn)) ?_
  apply Qeq_le; simp only [Qeq, mul]; push_cast; ring_uor

set_option maxHeartbeats 1200000 in
/-- **General-radius `Rartanh` radius-independence**: `Rartanh t ρ ≈ Rartanh t ρ'` for any two radii
    `ρ, ρ'`, with `t` bounded by `τ < 1` carrying the even-sum bound `K` (`K·(1−τ²) ≥ 1`). The
    generalization of `Rartanh_radius_indep` past `τ²≤1/2`, via `artSum_depth_recip_gen` (`K·τ.den`
    legs) + `geoEvenSum_le_gen` (`2K` Lipschitz leg). Conclusion `Req` is `C`-agnostic. -/
theorem Rartanh_radius_indep_gen (t X X' : Real) (ρ ρ' τ : Q) (K : Nat) (hρd : 0 < ρ.den)
    (hρ'd : 0 < ρ'.den) (hτ0 : 0 ≤ τ.num) (hτd : 0 < τ.den) (hτlt : τ.num.toNat < τ.den)
    (hKF : Qle (⟨1, 1⟩ : Q) (mul (⟨(K : Int), 1⟩ : Q) (Qsub ⟨1, 1⟩ (mul τ τ))))
    (hbt : ∀ m, Qle (Qabs (t.seq m)) τ)
    (hXseq : ∀ j, X.seq j = artSum (t.seq (Rartanh_R ρ j)) (Rartanh_R ρ j))
    (hX'seq : ∀ j, X'.seq j = artSum (t.seq (Rartanh_R ρ' j)) (Rartanh_R ρ' j)) :
    Req X X' := by
  have htd : ∀ m, 0 < (t.seq m).den := fun m => t.den_pos m
  have hRge : ∀ (r : Q), 0 < r.den → ∀ j, j + 1 ≤ Rartanh_R r j := by
    intro r hrd j; unfold Rartanh_R
    have hk : 1 ≤ r.den * r.den + 4 * r.den := Nat.le_trans (by omega : 1 ≤ 4 * r.den) (Nat.le_add_left _ _)
    calc j + 1 = 1 * (j + 1) := by omega
      _ ≤ (r.den * r.den + 4 * r.den) * (j + 1) := Nat.mul_le_mul_right _ hk
  refine Req_of_lin_bound (C := 2 * K * τ.den + 2 * K) ?_
  intro n
  rw [hXseq, hX'seq]
  have hage := hRge ρ hρd n
  have hbge := hRge ρ' hρ'd n
  have haM : Rartanh_R ρ n ≤ max (Rartanh_R ρ n) (Rartanh_R ρ' n) := Nat.le_max_left _ _
  have hbM : Rartanh_R ρ' n ≤ max (Rartanh_R ρ n) (Rartanh_R ρ' n) := Nat.le_max_right _ _
  have hna : n + 1 ≤ 2 * Rartanh_R ρ n + 3 := by omega
  have hnb : n + 1 ≤ 2 * Rartanh_R ρ' n + 3 := by omega
  have hT1 : Qle (Qabs (Qsub (artSum (t.seq (Rartanh_R ρ n)) (Rartanh_R ρ n))
        (artSum (t.seq (Rartanh_R ρ n)) (max (Rartanh_R ρ n) (Rartanh_R ρ' n)))))
      (⟨(K : Int) * (τ.den : Int), n + 1⟩ : Q) := by
    rw [Qabs_Qsub_comm]
    exact artSum_depth_recip_gen (t.seq (Rartanh_R ρ n)) τ K (htd _) hτ0 hτd (hbt _) hKF hτlt haM hna
  have hT3 : Qle (Qabs (Qsub (artSum (t.seq (Rartanh_R ρ' n)) (max (Rartanh_R ρ n) (Rartanh_R ρ' n)))
        (artSum (t.seq (Rartanh_R ρ' n)) (Rartanh_R ρ' n)))) (⟨(K : Int) * (τ.den : Int), n + 1⟩ : Q) :=
    artSum_depth_recip_gen (t.seq (Rartanh_R ρ' n)) τ K (htd _) hτ0 hτd (hbt _) hKF hτlt hbM hnb
  have hT2 : Qle (Qabs (Qsub (artSum (t.seq (Rartanh_R ρ n)) (max (Rartanh_R ρ n) (Rartanh_R ρ' n)))
        (artSum (t.seq (Rartanh_R ρ' n)) (max (Rartanh_R ρ n) (Rartanh_R ρ' n)))))
      (⟨2 * (K : Int), n + 1⟩ : Q) := by
    refine Qle_trans (Qmul_den_pos (geoEvenSum_den_pos hτd _)
        (Qabs_den_pos (Qsub_den_pos (htd _) (htd _))))
      (artSum_Lip_le (htd _) (htd _) hτd (hbt _) (hbt _) _) ?_
    refine Qle_trans (Qmul_den_pos Nat.one_pos (Qabs_den_pos (Qsub_den_pos (htd _) (htd _))))
      (Qmul_le_mul_right (Qabs_num_nonneg _)
        (geoEvenSum_le_gen hτ0 hτd Nat.one_pos (Int.ofNat_nonneg K) hKF _)) ?_
    refine Qle_trans (Qmul_den_pos Nat.one_pos (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _)))
      (Qmul_le_mul_left (Int.ofNat_nonneg K) (t.reg (Rartanh_R ρ n) (Rartanh_R ρ' n))) ?_
    have hRa : Qle (Qbound (Rartanh_R ρ n)) (Qbound n) := by
      show (1 : Int) * ((n + 1 : Nat) : Int) ≤ 1 * ((Rartanh_R ρ n + 1 : Nat) : Int)
      rw [Int.one_mul, Int.one_mul]; exact_mod_cast (show n + 1 ≤ Rartanh_R ρ n + 1 by omega)
    have hRb : Qle (Qbound (Rartanh_R ρ' n)) (Qbound n) := by
      show (1 : Int) * ((n + 1 : Nat) : Int) ≤ 1 * ((Rartanh_R ρ' n + 1 : Nat) : Int)
      rw [Int.one_mul, Int.one_mul]; exact_mod_cast (show n + 1 ≤ Rartanh_R ρ' n + 1 by omega)
    refine Qle_trans (Qmul_den_pos Nat.one_pos (add_den_pos (Qbound_den_pos n) (Qbound_den_pos n)))
      (Qmul_le_mul_left (Int.ofNat_nonneg K) (Qadd_le_add hRa hRb)) ?_
    apply Qeq_le
    show Qeq (mul (⟨(K : Int), 1⟩ : Q) (add (Qbound n) (Qbound n))) (⟨2 * (K : Int), n + 1⟩ : Q)
    simp only [Qeq, mul, add, Qbound]; push_cast; ring_uor
  have hP0d : 0 < (artSum (t.seq (Rartanh_R ρ n)) (Rartanh_R ρ n)).den := artSum_den_pos (htd _) _
  have hP1d : 0 < (artSum (t.seq (Rartanh_R ρ n)) (max (Rartanh_R ρ n) (Rartanh_R ρ' n))).den :=
    artSum_den_pos (htd _) _
  have hP2d : 0 < (artSum (t.seq (Rartanh_R ρ' n)) (max (Rartanh_R ρ n) (Rartanh_R ρ' n))).den :=
    artSum_den_pos (htd _) _
  have hP3d : 0 < (artSum (t.seq (Rartanh_R ρ' n)) (Rartanh_R ρ' n)).den := artSum_den_pos (htd _) _
  have hpc : Qle (Qabs (Qsub (artSum (t.seq (Rartanh_R ρ n)) (max (Rartanh_R ρ n) (Rartanh_R ρ' n)))
        (artSum (t.seq (Rartanh_R ρ' n)) (Rartanh_R ρ' n))))
      (add (⟨2 * (K : Int), n + 1⟩ : Q) (⟨(K : Int) * (τ.den : Int), n + 1⟩ : Q)) :=
    Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos hP1d hP2d))
        (Qabs_den_pos (Qsub_den_pos hP2d hP3d)))
      (Qabs_sub_triangle hP1d hP2d hP3d) (Qadd_le_add hT2 hT3)
  refine Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos hP0d hP1d))
      (Qabs_den_pos (Qsub_den_pos hP1d hP3d)))
    (Qabs_sub_triangle hP0d hP1d hP3d) ?_
  refine Qle_trans (add_den_pos (Nat.succ_pos n) (add_den_pos (Nat.succ_pos n) (Nat.succ_pos n)))
    (Qadd_le_add hT1 hpc) ?_
  refine Qle_trans (add_den_pos (Nat.succ_pos n) (Nat.succ_pos n))
    (Qadd_le_add (Qle_refl _) (Qeq_le (Qadd_same_den_loc (2 * (K : Int)) ((K : Int) * (τ.den : Int)) (n + 1)))) ?_
  refine Qle_trans (Nat.succ_pos n)
    (Qeq_le (Qadd_same_den_loc ((K : Int) * (τ.den : Int)) (2 * (K : Int) + (K : Int) * (τ.den : Int)) (n + 1))) ?_
  apply Qeq_le; simp only [Qeq]; push_cast; ring_uor

set_option maxHeartbeats 1600000 in
/-- **General-radius `Rlog` congruence**: `x ≈ y` (both presented at modulus `M`) ⟹ `Rlog x M ≈ Rlog y M`
    for **any** `M ≥ 1` (no small-radius cap), with `K` the even-sum bound for `ρ_M` (`K = ρ_M.den`
    works). Generalizes `Rlog_congr` via `Rartanh_congr_gen`. -/
theorem Rlog_congr_gen (x y : Real) (M : Q) (K : Nat) (hMd : 0 < M.den) (hMge : Qle (⟨1, 1⟩ : Q) M)
    (hxpos : ∀ n, 0 < (x.seq n).num) (hxhi : ∀ n, Qle (x.seq n) M)
    (hxlo : ∀ n, Qle (⟨1, 1⟩ : Q) (mul (x.seq n) M))
    (hypos : ∀ n, 0 < (y.seq n).num) (hyhi : ∀ n, Qle (y.seq n) M)
    (hylo : ∀ n, Qle (⟨1, 1⟩ : Q) (mul (y.seq n) M))
    (hKF : Qle (⟨1, 1⟩ : Q) (mul (⟨(K : Int), 1⟩ : Q)
      (Qsub ⟨1, 1⟩ (mul ⟨M.num - (M.den : Int), M.num.toNat + M.den⟩
        ⟨M.num - (M.den : Int), M.num.toNat + M.den⟩))))
    (hKr : K ≤ 2 * ((M.num.toNat + M.den) * (M.num.toNat + M.den) + 4 * (M.num.toNat + M.den)))
    (heq : Req x y) :
    Req (Rlog x M hMd hMge hxpos hxhi hxlo) (Rlog y M hMd hMge hypos hyhi hylo) := by
  obtain ⟨hMn, hM1, hρ0, hρd, hρlt, hρ1⟩ := Rlog_radius_facts M hMd hMge
  have hden_x : ∀ n, 0 < (Rlog_seq x n).den := fun n => Qmul_den_pos
    (Qsub_den_pos (x.den_pos _) Nat.one_pos) (Qinv_den_pos (by
      have := hxpos (Rlog_R n); have h := Int.ofNat_nonneg (x.seq (Rlog_R n)).den
      show 0 < (x.seq (Rlog_R n)).num * 1 + 1 * ((x.seq (Rlog_R n)).den : Int); omega))
  have hden_y : ∀ n, 0 < (Rlog_seq y n).den := fun n => Qmul_den_pos
    (Qsub_den_pos (y.den_pos _) Nat.one_pos) (Qinv_den_pos (by
      have := hypos (Rlog_R n); have h := Int.ofNat_nonneg (y.seq (Rlog_R n)).den
      show 0 < (y.seq (Rlog_R n)).num * 1 + 1 * ((y.seq (Rlog_R n)).den : Int); omega))
  have hbtρx := Rlog_tbound x M hMd hMn hM1 hxhi hxlo hxpos
  have hbtρy := Rlog_tbound y M hMd hMn hM1 hyhi hylo hypos
  rw [Rlog_eq_Rmul x M hMd hMge hxpos hxhi hxlo hden_x hρ0 hρd hρlt (fun n => hbtρx (Rlog_R n)),
    Rlog_eq_Rmul y M hMd hMge hypos hyhi hylo hden_y hρ0 hρd hρlt (fun n => hbtρy (Rlog_R n))]
  refine Rmul_congr (Req_refl _) ?_
  have hWeq : Req (⟨Rlog_seq x, Rlog_regular x hxpos, hden_x⟩ : Real)
      ⟨Rlog_seq y, Rlog_regular y hypos, hden_y⟩ := by
    refine Req_of_lin_bound (C := 4) ?_
    intro n
    show Qle (Qabs (Qsub (tmap (x.seq (Rlog_R n))) (tmap (y.seq (Rlog_R n))))) (⟨(4 : Int), n + 1⟩ : Q)
    have ha1 : 0 < (add (x.seq (Rlog_R n)) ⟨1, 1⟩).num := by
      have := hxpos (Rlog_R n); have h := Int.ofNat_nonneg (x.seq (Rlog_R n)).den
      show 0 < (x.seq (Rlog_R n)).num * 1 + 1 * ((x.seq (Rlog_R n)).den : Int); omega
    have hb1 : 0 < (add (y.seq (Rlog_R n)) ⟨1, 1⟩).num := by
      have := hypos (Rlog_R n); have h := Int.ofNat_nonneg (y.seq (Rlog_R n)).den
      show 0 < (y.seq (Rlog_R n)).num * 1 + 1 * ((y.seq (Rlog_R n)).den : Int); omega
    have hage : Qle (⟨1, 1⟩ : Q) (add (x.seq (Rlog_R n)) ⟨1, 1⟩) := by
      have := hxpos (Rlog_R n); have h := Int.ofNat_nonneg (x.seq (Rlog_R n)).den
      simp only [Qle, add]; push_cast; omega
    have hbge : Qle (⟨1, 1⟩ : Q) (add (y.seq (Rlog_R n)) ⟨1, 1⟩) := by
      have := hypos (Rlog_R n); have h := Int.ofNat_nonneg (y.seq (Rlog_R n)).den
      simp only [Qle, add]; push_cast; omega
    refine Qle_trans (Qmul_den_pos (by decide) (Qabs_den_pos (Qsub_den_pos (x.den_pos _) (y.den_pos _))))
      (tmap_lip (x.seq (Rlog_R n)) (y.seq (Rlog_R n)) (x.den_pos _) (y.den_pos _) ha1 hb1 hage hbge) ?_
    refine Qle_trans (Qmul_den_pos (by decide) (Nat.succ_pos _))
      (Qmul_le_mul_left (by decide) (heq (Rlog_R n))) ?_
    show Qle (mul (⟨2, 1⟩ : Q) ⟨2, Rlog_R n + 1⟩) (⟨(4 : Int), n + 1⟩ : Q)
    simp only [Qle, mul, Rlog_R]; push_cast; omega
  exact Rartanh_congr_gen _ _ _ K hρ0 hρd hρlt hKF hKr
    (fun n => hbtρx (Rlog_R n)) (fun n => hbtρy (Rlog_R n)) hWeq

set_option maxHeartbeats 1600000 in
/-- **General-radius `RlogPos → Rlog` bridge**: `RlogPos x k = Rlog x B` for `x ∈ [1/B, B]` at **any**
    `B ≥ 1` (no small-radius cap), with `K` the even-sum bound for `ρ_B` (`K = ρ_B.den` works).
    Generalizes `RlogPos_eq_Rlog` via `Rartanh_radius_indep_gen` (`Mx→B`) + `Rlog_congr_gen`
    (`reindex x ≈ x`). -/
theorem RlogPos_eq_Rlog_gen (x : Real) (k : Nat) (hk : Qlt (Qbound k) (x.seq k))
    (B : Q) (K : Nat) (hBd : 0 < B.den) (hBge : Qle (⟨1, 1⟩ : Q) B)
    (hxposB : ∀ n, 0 < (x.seq n).num) (hxhiB : ∀ n, Qle (x.seq n) B)
    (hxloB : ∀ n, Qle (⟨1, 1⟩ : Q) (mul (x.seq n) B))
    (hKF : Qle (⟨1, 1⟩ : Q) (mul (⟨(K : Int), 1⟩ : Q)
      (Qsub ⟨1, 1⟩ (mul ⟨B.num - (B.den : Int), B.num.toNat + B.den⟩
        ⟨B.num - (B.den : Int), B.num.toNat + B.den⟩))))
    (hKr : K ≤ 2 * ((B.num.toNat + B.den) * (B.num.toNat + B.den) + 4 * (B.num.toNat + B.den))) :
    Req (RlogPos x k hk) (Rlog x B hBd hBge hxposB hxhiB hxloB) := by
  have hLn := RL_num_pos hk
  have hLd := @RL_den_pos x k
  have hLinvn := Qinv_num_pos hLd
  have hLinvd := Qinv_den_pos hLn
  have hAd : 0 < (add (Qabs (x.seq 0)) ⟨2, 1⟩).den :=
    add_den_pos (Qabs_den_pos (x.den_pos 0)) Nat.one_pos
  have hAn : 0 ≤ (add (Qabs (x.seq 0)) ⟨2, 1⟩).num := by
    simp only [add, Qabs]
    have h1 := Int.ofNat_nonneg (x.seq 0).num.natAbs
    have h2 := Int.ofNat_nonneg (x.seq 0).den; push_cast; omega
  have h1A : Qle (⟨1, 1⟩ : Q) (add (Qabs (x.seq 0)) ⟨2, 1⟩) := by
    simp only [Qle, add, Qabs]
    have h1 := Int.ofNat_nonneg (x.seq 0).num.natAbs
    have h2 := Int.ofNat_nonneg (x.seq 0).den; push_cast; omega
  have hMxd : 0 < (add (add (Qabs (x.seq 0)) ⟨2, 1⟩) (Qinv (RL x k))).den := add_den_pos hAd hLinvd
  have hMxge : Qle (⟨1, 1⟩ : Q) (add (add (Qabs (x.seq 0)) ⟨2, 1⟩) (Qinv (RL x k))) :=
    Qle_trans hAd h1A (Qle_add_right_nonneg (Int.le_of_lt hLinvn))
  have hposrix : ∀ n, 0 < ((⟨fun n => x.seq (RlogPosR x k n),
      reindex_regular x (RlogPosR x k) (RlogPosR_self x k), fun _ => x.den_pos _⟩ : Real).seq n).num :=
    fun n => Rinv_num_pos hk (RlogPosR_tail x k n)
  have hhirix : ∀ n, Qle ((⟨fun n => x.seq (RlogPosR x k n),
      reindex_regular x (RlogPosR x k) (RlogPosR_self x k), fun _ => x.den_pos _⟩ : Real).seq n)
      (add (add (Qabs (x.seq 0)) ⟨2, 1⟩) (Qinv (RL x k))) := by
    intro n
    exact Qle_trans (add_den_pos (x.den_pos 0) Nat.one_pos)
      (Rlog_ub x (RlogPosR x k n))
      (Qle_trans hAd (Qadd_le_add (Qle_self_Qabs (x.seq 0)) (Qle_refl _))
        (Qle_add_right_nonneg (Int.le_of_lt hLinvn)))
  have hlorix : ∀ n, Qle (⟨1, 1⟩ : Q) (mul ((⟨fun n => x.seq (RlogPosR x k n),
      reindex_regular x (RlogPosR x k) (RlogPosR_self x k), fun _ => x.den_pos _⟩ : Real).seq n)
      (add (add (Qabs (x.seq 0)) ⟨2, 1⟩) (Qinv (RL x k)))) := by
    intro n
    have hqn : 0 < (x.seq (RlogPosR x k n)).num := Rinv_num_pos hk (RlogPosR_tail x k n)
    have hqd : 0 < (x.seq (RlogPosR x k n)).den := x.den_pos _
    have hqL : Qle (RL x k) (x.seq (RlogPosR x k n)) := Rinv_lb hk (RlogPosR_tail x k n)
    exact Qle_trans (Qmul_den_pos hLd hLinvd)
      (Qeq_le (Qeq_symm (Qmul_Qinv hLn)))
      (Qle_trans (Qmul_den_pos hqd hLinvd)
        (Qmul_le_mul hLd hqd hLinvd (Int.le_of_lt hLn) (Int.le_of_lt hLinvn) hqL (Qle_refl _))
        (Qmul_le_mul_left (Int.le_of_lt hqn) (Qle_add_left_nonneg hAn)))
  rw [RlogPos_unfold x k hk hMxd hMxge hposrix hhirix hlorix]
  have hhirixB : ∀ n, Qle ((⟨fun n => x.seq (RlogPosR x k n),
      reindex_regular x (RlogPosR x k) (RlogPosR_self x k), fun _ => x.den_pos _⟩ : Real).seq n) B :=
    fun n => hxhiB (RlogPosR x k n)
  have hlorixB : ∀ n, Qle (⟨1, 1⟩ : Q) (mul ((⟨fun n => x.seq (RlogPosR x k n),
      reindex_regular x (RlogPosR x k) (RlogPosR_self x k), fun _ => x.den_pos _⟩ : Real).seq n) B) :=
    fun n => hxloB (RlogPosR x k n)
  refine Req_trans ?_
    (Rlog_congr_gen _ x B K hBd hBge hposrix hhirixB hlorixB hxposB hxhiB hxloB hKF hKr
      (reindex_Req x (RlogPosR x k) (RlogPosR_self x k)))
  obtain ⟨hMxn, hMx1, hρMx0, hρMxd, hρMxlt, hρMx1⟩ :=
    Rlog_radius_facts (add (add (Qabs (x.seq 0)) ⟨2, 1⟩) (Qinv (RL x k))) hMxd hMxge
  obtain ⟨hBn, hB1, hρB0, hρBd, hρBlt, hρB1⟩ := Rlog_radius_facts B hBd hBge
  have hden_rix : ∀ n, 0 < (Rlog_seq ⟨fun n => x.seq (RlogPosR x k n),
      reindex_regular x (RlogPosR x k) (RlogPosR_self x k), fun _ => x.den_pos _⟩ n).den := fun n =>
    Qmul_den_pos (Qsub_den_pos (x.den_pos _) Nat.one_pos) (Qinv_den_pos (by
      have hpp : 0 < (x.seq (RlogPosR x k (Rlog_R n))).num := hposrix (Rlog_R n)
      have h := Int.ofNat_nonneg (x.seq (RlogPosR x k (Rlog_R n))).den
      show 0 < (x.seq (RlogPosR x k (Rlog_R n))).num * 1 + 1 * ((x.seq (RlogPosR x k (Rlog_R n))).den : Int)
      omega))
  have hbtMx := Rlog_tbound _ (add (add (Qabs (x.seq 0)) ⟨2, 1⟩) (Qinv (RL x k))) hMxd hMxn hMx1
    hhirix hlorix hposrix
  have hbtB := Rlog_tbound _ B hBd hBn hB1 hhirixB hlorixB hposrix
  rw [Rlog_eq_Rmul _ (add (add (Qabs (x.seq 0)) ⟨2, 1⟩) (Qinv (RL x k))) hMxd hMxge hposrix hhirix hlorix
        hden_rix hρMx0 hρMxd hρMxlt (fun n => hbtMx (Rlog_R n)),
    Rlog_eq_Rmul _ B hBd hBge hposrix hhirixB hlorixB hden_rix hρB0 hρBd hρBlt (fun n => hbtB (Rlog_R n))]
  refine Rmul_congr (Req_refl _) ?_
  exact Rartanh_radius_indep_gen ⟨Rlog_seq ⟨fun n => x.seq (RlogPosR x k n),
      reindex_regular x (RlogPosR x k) (RlogPosR_self x k), fun _ => x.den_pos _⟩,
      Rlog_regular _ hposrix, hden_rix⟩ _ _
    ⟨(add (add (Qabs (x.seq 0)) ⟨2, 1⟩) (Qinv (RL x k))).num
        - ((add (add (Qabs (x.seq 0)) ⟨2, 1⟩) (Qinv (RL x k))).den : Int),
      (add (add (Qabs (x.seq 0)) ⟨2, 1⟩) (Qinv (RL x k))).num.toNat
        + (add (add (Qabs (x.seq 0)) ⟨2, 1⟩) (Qinv (RL x k))).den⟩
    ⟨B.num - (B.den : Int), B.num.toNat + B.den⟩
    ⟨B.num - (B.den : Int), B.num.toNat + B.den⟩ K
    hρMxd hρBd hρB0 hρBd hρBlt hKF (fun n => hbtB (Rlog_R n)) (fun _ => rfl) (fun _ => rfl)

/-- **General-radius `RlogPos` congruence**: `x ≈ y` (both in `[1/B,B]`) ⟹ `RlogPos x ≈ RlogPos y` at
    any `B ≥ 1`. Generalizes `RlogPos_congr` via the general-radius bridge + `Rlog_congr_gen`. -/
theorem RlogPos_congr_gen (x y : Real) (kx : Nat) (hx : Qlt (Qbound kx) (x.seq kx))
    (ky : Nat) (hy : Qlt (Qbound ky) (y.seq ky))
    (B : Q) (K : Nat) (hBd : 0 < B.den) (hBge : Qle (⟨1, 1⟩ : Q) B)
    (hxposB : ∀ n, 0 < (x.seq n).num) (hxhiB : ∀ n, Qle (x.seq n) B)
    (hxloB : ∀ n, Qle (⟨1, 1⟩ : Q) (mul (x.seq n) B))
    (hyposB : ∀ n, 0 < (y.seq n).num) (hyhiB : ∀ n, Qle (y.seq n) B)
    (hyloB : ∀ n, Qle (⟨1, 1⟩ : Q) (mul (y.seq n) B))
    (hKF : Qle (⟨1, 1⟩ : Q) (mul (⟨(K : Int), 1⟩ : Q)
      (Qsub ⟨1, 1⟩ (mul ⟨B.num - (B.den : Int), B.num.toNat + B.den⟩
        ⟨B.num - (B.den : Int), B.num.toNat + B.den⟩))))
    (hKr : K ≤ 2 * ((B.num.toNat + B.den) * (B.num.toNat + B.den) + 4 * (B.num.toNat + B.den)))
    (heq : Req x y) :
    Req (RlogPos x kx hx) (RlogPos y ky hy) :=
  Req_trans (RlogPos_eq_Rlog_gen x kx hx B K hBd hBge hxposB hxhiB hxloB hKF hKr)
    (Req_trans (Rlog_congr_gen x y B K hBd hBge hxposB hxhiB hxloB hyposB hyhiB hyloB hKF hKr heq)
      (Req_symm (RlogPos_eq_Rlog_gen y ky hy B K hBd hBge hyposB hyhiB hyloB hKF hKr)))

end UOR.Bridge.F1Square.Analysis
