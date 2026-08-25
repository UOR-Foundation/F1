/-
F1 square — **reconciling certificates and schedules** (`WeilArchReconcile.lean`):

  • `decay_mono` — a block decay certificate at `K` is one at every `K' ≥ K`;
  • `decay_of_terms_congr` — block-wise equal unit terms share decay certificates;
  • `decay_shift_one` — the integer shift `u ↦ u+1` keeps decay (`K/((m+2)(m+1)) ≤ K/((m+1)m)`);
  • **SCHEDULE INDEPENDENCE** (`improperIntegral1_sched`) — the improper integral does not depend on
    the decay constant used to schedule its partial sums: two schedules differ by a telescoped tail
    `Σ_{m ≥ N} K/((m+1)m) ≤ K/N ≤ K/(j+1)` (`genTail_two_sided`);
  • `half_lip` — the half-scaled function keeps the Lipschitz certificate.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.WeilArchLimit

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- (1) Decay certificates: monotone in `K`, block-wise congruent, integer shift.
-- ===========================================================================

theorem decay_mono (ψ : L2Test) {K K' : Q} (hKd : 0 < K.den) (hK'd : 0 < K'.den) (hKK : Qle K K')
    (hb : DecayAt ψ K hKd) : DecayAt ψ K' hK'd := by
  intro m hm
  have hle : Qle (mul K (⟨1, (m + 1) * m⟩ : Q)) (mul K' (⟨1, (m + 1) * m⟩ : Q)) :=
    Qmul_le_mul_right (show (0 : Int) ≤ 1 by decide) hKK
  have hr := Rle_ofQ_ofQ (Qmul_den_pos hKd (digamma_succ_mul_pos hm))
    (Qmul_den_pos hK'd (digamma_succ_mul_pos hm)) hle
  exact ⟨Rle_trans (Rle_Rneg hr) (hb m hm).1, Rle_trans (hb m hm).2 hr⟩

theorem decay_of_terms_congr (ψ ψ' : L2Test) {K : Q} (hKd : 0 < K.den)
    (hterm : ∀ m, Req (integralTerm ψ.hLd ψ.hLn ψ.hlip ψ.hfc m) (integralTerm ψ'.hLd ψ'.hLn ψ'.hlip ψ'.hfc m))
    (hb : DecayAt ψ K hKd) : DecayAt ψ' K hKd := fun m hm =>
  ⟨Rle_trans (hb m hm).1 (Rle_of_Req (hterm m)), Rle_trans (Rle_of_Req (Req_symm (hterm m))) (hb m hm).2⟩

/-- `K/((m+2)(m+1)) ≤ K/((m+1)m)`. -/
theorem q_block_shift_le (K : Q) (hK0 : 0 ≤ K.num) (m : Nat) :
    Qle (mul K (⟨1, (m + 2) * (m + 1)⟩ : Q)) (mul K (⟨1, (m + 1) * m⟩ : Q)) := by
  refine Qmul_le_mul_left hK0 ?_
  show (1 : Int) * (((m + 1) * m : Nat) : Int) ≤ 1 * (((m + 2) * (m + 1) : Nat) : Int)
  have h : (m + 1) * m ≤ (m + 2) * (m + 1) := Nat.mul_le_mul (by omega) (by omega)
  have h' := Int.ofNat_le.mpr h
  omega

theorem decay_shift_one (ψ : L2Test) {K : Q} (hKd : 0 < K.den) (hK0 : 0 ≤ K.num)
    (hb : DecayAt ψ K hKd) : DecayAt (shiftTest (⟨1, 1⟩ : Q) Nat.one_pos ψ) K hKd := by
  intro m hm
  have hm1 : 1 ≤ m + 1 := by omega
  have hb1 := hb (m + 1) hm1
  have heq := integralTerm_shift_one ψ m
  have hle := Rle_ofQ_ofQ (Qmul_den_pos hKd (digamma_succ_mul_pos hm1))
    (Qmul_den_pos hKd (digamma_succ_mul_pos hm)) (q_block_shift_le K hK0 m)
  exact ⟨Rle_trans (Rle_Rneg hle) (Rle_trans hb1.1 (Rle_of_Req (Req_symm heq))),
    Rle_trans (Rle_of_Req heq) (Rle_trans hb1.2 hle)⟩

-- ===========================================================================
-- (2) SCHEDULE INDEPENDENCE.
-- ===========================================================================

/-- `K·(1/N − 1/(N+d)) ≤ K/N`. -/
theorem digammaTailQ_le_inv (K : Q) (hK0 : 0 ≤ K.num) (N d : Nat) (hN : 1 ≤ N) :
    Qle (digammaTailQ K N d hN) (mul K (⟨1, N⟩ : Q)) := by
  refine Qmul_le_mul_left hK0 ?_
  show ((1 : Int) * ((N + d : Nat) : Int) + -1 * (N : Int)) * (N : Int) ≤ 1 * ((N * (N + d) : Nat) : Int)
  push_cast
  have hNd : (0 : Int) ≤ (N : Int) * (d : Int) := Int.mul_nonneg (Int.ofNat_nonneg _) (Int.ofNat_nonneg _)
  have e1 : ((1 : Int) * ((N : Int) + (d : Int)) + -1 * (N : Int)) * (N : Int) = (N : Int) * (d : Int) := by
    ring_uor
  have e2 : (1 : Int) * ((N : Int) * ((N : Int) + (d : Int))) = (N : Int) * (N : Int) + (N : Int) * (d : Int) := by
    ring_uor
  have hNN : (0 : Int) ≤ (N : Int) * (N : Int) := Int.mul_nonneg (Int.ofNat_nonneg _) (Int.ofNat_nonneg _)
  omega

/-- The partial sums along two schedules are within `K/(j+1)` of each other. -/
theorem genSum_sched_close (T : Nat → Real) {K : Q} (hKd : 0 < K.den) (hK0 : 0 ≤ K.num)
    (hb : ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm)))) (T m)
      ∧ Rle (T m) (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
    (N d j : Nat) (hN : 1 ≤ N) (hjN : j + 1 ≤ N) :
    Rle (Rabs (Rsub (genSum T (N + d)) (genSum T N)))
        (ofQ (mul K (⟨1, j + 1⟩ : Q)) (Qmul_den_pos hKd (Nat.succ_pos j))) := by
  have htail := genTail_two_sided T hKd hb hN d
  have hle1 := Rle_ofQ_ofQ (digammaTailQ_den_pos K N d hN hKd) (Qmul_den_pos hKd (show 0 < N by omega))
    (digammaTailQ_le_inv K hK0 N d hN)
  have hle2 : Qle (mul K (⟨1, N⟩ : Q)) (mul K (⟨1, j + 1⟩ : Q)) := by
    refine Qmul_le_mul_left hK0 ?_
    show (1 : Int) * ((j + 1 : Nat) : Int) ≤ 1 * ((N : Nat) : Int)
    have h := Int.ofNat_le.mpr hjN
    push_cast at h ⊢; omega
  have hle := Rle_trans hle1 (Rle_ofQ_ofQ (Qmul_den_pos hKd (show 0 < N by omega))
    (Qmul_den_pos hKd (Nat.succ_pos j)) hle2)
  refine Rle_trans (Rle_of_Req (Rabs_congr (genSum_diff_eq T N d))) ?_
  refine Rabs_le_of_both (Rle_trans htail.2 hle) ?_
  exact Rle_trans (Rle_Rneg htail.1) (Rle_trans (Rle_of_Req (Rneg_neg _)) hle)

/-- `b + (a − b) = a`. -/
theorem Radd_Rsub_cancel_arch (a b : Real) : Req (Radd b (Rsub a b)) a :=
  Req_trans (Req_symm (Radd_assoc b a (Rneg b)))
    (Req_trans (Radd_congr (Radd_comm b a) (Req_refl _))
      (Req_trans (Radd_assoc a b (Rneg b)) (Req_trans (Radd_congr (Req_refl a) (Radd_neg b)) (Radd_zero a))))

/-- **SCHEDULE INDEPENDENCE**: the same decaying terms summed along the schedules of `K` and `K'`
    (both valid decay constants) have the same Bishop limit. -/
theorem Rlim_sched_indep (T : Nat → Real) {K K' : Q} (hKd : 0 < K.den) (hK0 : 0 ≤ K.num)
    (hK'd : 0 < K'.den) (hK'0 : 0 ≤ K'.num)
    (hb : ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm)))) (T m)
      ∧ Rle (T m) (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
    (hb' : ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul K' (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hK'd (digamma_succ_mul_pos hm)))) (T m)
      ∧ Rle (T m) (ofQ (mul K' (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hK'd (digamma_succ_mul_pos hm)))) :
    Req (Rlim (fun j => genSum T (digammaMidx K j)) (genSum_RReg T hKd hK0 hb))
        (Rlim (fun j => genSum T (digammaMidx K' j)) (genSum_RReg T hK'd hK'0 hb')) := by
  -- both partial sums are within K/(j+1) of each other (the tail from min(M_j, M'_j) ≥ j+1)
  have hclose : ∀ j, Rle (Rabs (Rsub (genSum T (digammaMidx K j)) (genSum T (digammaMidx K' j))))
      (ofQ (mul K (⟨1, j + 1⟩ : Q)) (Qmul_den_pos hKd (Nat.succ_pos j))) := by
    intro j
    rcases Nat.le_total (digammaMidx K' j) (digammaMidx K j) with h | h
    · have he : digammaMidx K j = digammaMidx K' j + (digammaMidx K j - digammaMidx K' j) := by omega
      rw [he]
      exact genSum_sched_close T hKd hK0 hb _ _ j (digammaMidx_ge_one K' j) (digammaMidx_ge K' j)
    · have he : digammaMidx K' j = digammaMidx K j + (digammaMidx K' j - digammaMidx K j) := by omega
      rw [he]
      refine Rle_trans (Rle_of_Req (Req_trans (Req_symm (Rabs_Rneg _)) (Rabs_congr (Rneg_Rsub _ _)))) ?_
      exact genSum_sched_close T hKd hK0 hb _ _ j (digammaMidx_ge_one K j) (digammaMidx_ge K j)
  have hC : Nat := K.num.toNat + 1
  refine Rlim_eq_of_close _ _ ?_ ?_
  · intro k
    refine ⟨(K.num.toNat + 1) * (k + 1), fun n hn => ?_⟩
    have hr : Qle (mul K (⟨1, n + 1⟩ : Q)) (⟨1, k + 1⟩ : Q) := by
      refine Qle_trans (Qmul_den_pos Nat.one_pos (Nat.succ_pos n))
        (Qmul_le_mul_right (show (0 : Int) ≤ 1 by decide) (Qle_num_cap K hKd hK0)) ?_
      refine Qle_trans (Nat.succ_pos n) (Qeq_le (qCF_mul_inv (K.num.toNat + 1) n)) ?_
      exact rate_le_of_ge (K.num.toNat + 1) k n hn
    have hr' := Rle_ofQ_ofQ (Qmul_den_pos hKd (Nat.succ_pos n)) (Nat.succ_pos k) hr
    -- A = B + (A − B) ≤ B + |A − B|
    refine Rle_trans (Rle_of_Req (Req_symm (Radd_Rsub_cancel_arch (genSum T (digammaMidx K n))
      (genSum T (digammaMidx K' n))))) ?_
    exact Radd_le_add (Rle_refl _) (Rle_trans (Rle_Rabs_self _) (Rle_trans (hclose n) hr'))
  · intro k
    refine ⟨(K.num.toNat + 1) * (k + 1), fun n hn => ?_⟩
    have hr : Qle (mul K (⟨1, n + 1⟩ : Q)) (⟨1, k + 1⟩ : Q) := by
      refine Qle_trans (Qmul_den_pos Nat.one_pos (Nat.succ_pos n))
        (Qmul_le_mul_right (show (0 : Int) ≤ 1 by decide) (Qle_num_cap K hKd hK0)) ?_
      refine Qle_trans (Nat.succ_pos n) (Qeq_le (qCF_mul_inv (K.num.toNat + 1) n)) ?_
      exact rate_le_of_ge (K.num.toNat + 1) k n hn
    have hr' := Rle_ofQ_ofQ (Qmul_den_pos hKd (Nat.succ_pos n)) (Nat.succ_pos k) hr
    -- B = A + (B − A) ≤ A + |B − A| = A + |A − B|
    refine Rle_trans (Rle_of_Req (Req_symm (Radd_Rsub_cancel_arch (genSum T (digammaMidx K' n))
      (genSum T (digammaMidx K n))))) ?_
    refine Radd_le_add (Rle_refl _) ?_
    refine Rle_trans (Rle_Rabs_self _) (Rle_trans (Rle_of_Req (Req_trans (Req_symm (Rabs_Rneg _))
      (Rabs_congr (Rneg_Rsub _ _)))) (Rle_trans (hclose n) hr'))

/-- **The improper integral is schedule-independent** (same integrand, two decay constants). -/
theorem improperIntegral1_sched {f : Real → Real} {L K K' : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfc : ∀ x y, Req x y → Req (f x) (f y))
    (hKd : 0 < K.den) (hK0 : 0 ≤ K.num) (hK'd : 0 < K'.den) (hK'0 : 0 ≤ K'.num)
    (hb : ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
          (integralTerm hLd hLn hlip hfc m)
      ∧ Rle (integralTerm hLd hLn hlip hfc m)
          (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
    (hb' : ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul K' (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hK'd (digamma_succ_mul_pos hm))))
          (integralTerm hLd hLn hlip hfc m)
      ∧ Rle (integralTerm hLd hLn hlip hfc m)
          (ofQ (mul K' (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hK'd (digamma_succ_mul_pos hm)))) :
    Req (improperIntegral1 hLd hLn hlip hfc hKd hK0 hb) (improperIntegral1 hLd hLn hlip hfc hK'd hK'0 hb') :=
  Rlim_sched_indep _ hKd hK0 hK'd hK'0 hb hb'

-- ===========================================================================
-- (3) The half-scaling certificate.
-- ===========================================================================

/-- `x ↦ ½·ψ(x)` keeps ψ's Lipschitz certificate. -/
theorem half_lip (ψ : L2Test) : ∀ x y,
    Rle (Rabs (Rsub (Rmul (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1)) (ψ.f x))
                    (Rmul (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1)) (ψ.f y))))
        (Rmul (ofQ ψ.L ψ.hLd) (Rabs (Rsub x y))) := by
  intro x y
  refine Rle_trans (Rle_of_Req (Rabs_congr (Req_symm (Rmul_sub_distrib _ _ _)))) ?_
  refine Rle_trans (Rle_of_Req (Rabs_Rmul_ofQ_nonneg (Nat.succ_pos 1) (by decide) _)) ?_
  refine Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ (Nat.succ_pos 1) (by decide)) (ψ.hlip x y)) ?_
  refine Rle_trans (Rle_of_Req (Req_symm (Rmul_assoc _ _ _))) ?_
  refine Rmul_le_Rmul_right (Rnonneg_Rabs _) ?_
  refine Rle_trans (Rle_of_Req (Rmul_ofQ_ofQ _ _)) (Rle_ofQ_ofQ _ ψ.hLd ?_)
  -- ½·L ≤ L
  show (mul (⟨1, 2⟩ : Q) ψ.L).num * (ψ.L.den : Int) ≤ ψ.L.num * ((mul (⟨1, 2⟩ : Q) ψ.L).den : Int)
  simp only [mul]
  push_cast
  have := ψ.hLn
  have hd : (0 : Int) ≤ (ψ.L.den : Int) := Int.ofNat_nonneg _
  have h1 : 0 ≤ ψ.L.num * (ψ.L.den : Int) := Int.mul_nonneg this hd
  have e1 : 1 * ψ.L.num * (ψ.L.den : Int) = ψ.L.num * (ψ.L.den : Int) := by ring_uor
  have e2 : ψ.L.num * (2 * (ψ.L.den : Int)) = 2 * (ψ.L.num * (ψ.L.den : Int)) := by ring_uor
  omega

theorem half_fc (ψ : L2Test) : ∀ x y, Req x y →
    Req (Rmul (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1)) (ψ.f x)) (Rmul (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1)) (ψ.f y)) :=
  fun x y h => Rmul_congr (Req_refl _) (ψ.hfc x y h)

end UOR.Bridge.F1Square.Square
