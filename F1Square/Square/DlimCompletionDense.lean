/-
# Density of the finite-support direct limit in its completion

`completion_dense`: every completion member `X` is the completion-metric limit of `of (X.seq N)`, with
an explicit squared-norm approximation modulus (`N := 2(k+1)` for tolerance `1/(k+1)`).

The `_dns`-suffixed lemmas are ζ-free in-file replicas of `ComplexLimitCore`'s one-sided limit engine
(`Rle_lim_of_close_one_side` and dependencies are `private`, so not reusable across the import boundary);
they also PRIME the (very expensive) `whnf` reduction of `completedDist2` so that the stagewise reduction
`completedDist2_reduce_dns` and `completion_dense` elaborate within the default heartbeat budget.
-/
import F1Square.Square.DlimCompletionComplete

open UOR.Bridge.F1Square
open UOR.Bridge.F1Square.Analysis

namespace UOR.Bridge.F1Square.Square

-- ===========================================================================
-- ζ-free-cone copies (leaf names end in `_dns`) of the one-sided limit-comparison
-- engine of `ComplexLimitCore` (its `Rle_lim_of_close_one_side` and dependencies are
-- `private`, so they cannot be reused across the import boundary; re-proved verbatim
-- here under globally-unique `_dns` names). Everything they cite is public in the
-- transitive import cone of `DlimCompletionComplete`.
-- ===========================================================================

/-- Real-≤ to same-index-ℚ-≤ bridge across `Radd`+`ofQ` (copy of the private
    `seq_le_of_Rle_Radd_ofQ`). -/
private theorem seq_le_of_Rle_Radd_ofQ_dns (a b : Real) (c : Q) (hcd : 0 < c.den)
    (h : Rle a (Radd b (ofQ c hcd))) (i : Nat) :
    Qle (a.seq i) (add (b.seq i) (add c ⟨2, i + 1⟩)) := by
  apply Qarch_gen (C := 4) (a.den_pos i)
    (add_den_pos (b.den_pos i) (add_den_pos hcd (Nat.succ_pos _)))
  intro m
  have hm : Qle (a.seq m) (add (add (b.seq (2 * m + 1)) c) ⟨2, m + 1⟩) := h m
  have s1 : Qle (a.seq i) (add (a.seq m) (add (Qbound i) (Qbound m))) :=
    Qle_add_of_Qabs_sub (a.den_pos i) (a.den_pos m)
      (add_den_pos (Qbound_den_pos i) (Qbound_den_pos m)) (a.reg i m)
  have hbnd : Qle (Qbound (2 * m + 1)) (Qbound m) := by simp only [Qle, Qbound]; push_cast; omega
  have s3 : Qle (b.seq (2 * m + 1)) (add (b.seq i) (add (Qbound (2 * m + 1)) (Qbound i))) :=
    Qle_add_of_Qabs_sub (b.den_pos (2 * m + 1)) (b.den_pos i)
      (add_den_pos (Qbound_den_pos _) (Qbound_den_pos i)) (b.reg (2 * m + 1) i)
  have s3' : Qle (b.seq (2 * m + 1)) (add (b.seq i) (add (Qbound m) (Qbound i))) :=
    Qle_trans (add_den_pos (b.den_pos i) (add_den_pos (Qbound_den_pos _) (Qbound_den_pos i)))
      s3 (Qadd_le_add (Qle_refl (b.seq i)) (Qadd_le_add hbnd (Qle_refl (Qbound i))))
  have c1 : Qle (a.seq i)
      (add (add (add (b.seq (2 * m + 1)) c) ⟨2, m + 1⟩) (add (Qbound i) (Qbound m))) :=
    Qle_trans (add_den_pos (a.den_pos m) (add_den_pos (Qbound_den_pos i) (Qbound_den_pos m)))
      s1 (Qadd_le_add hm (Qle_refl _))
  have c2 : Qle (a.seq i)
      (add (add (add (add (b.seq i) (add (Qbound m) (Qbound i))) c) ⟨2, m + 1⟩)
        (add (Qbound i) (Qbound m))) :=
    Qle_trans
      (add_den_pos (add_den_pos (add_den_pos (b.den_pos _) hcd) (Nat.succ_pos _))
        (add_den_pos (Qbound_den_pos i) (Qbound_den_pos m)))
      c1
      (Qadd_le_add (Qadd_le_add (Qadd_le_add s3' (Qle_refl c)) (Qle_refl _)) (Qle_refl _))
  refine Qle_trans ?_ c2 (Qeq_le ?_)
  · exact add_den_pos (add_den_pos (add_den_pos
      (add_den_pos (b.den_pos i) (add_den_pos (Qbound_den_pos m) (Qbound_den_pos i))) hcd)
      (Nat.succ_pos _)) (add_den_pos (Qbound_den_pos i) (Qbound_den_pos m))
  · simp only [Qeq, add, Qbound]; push_cast; ring_uor

set_option maxHeartbeats 4000000 in
/-- The per-`m` Archimedean slice of the one-sided limit comparison (copy of `Rle_lim_step`). -/
private theorem Rle_lim_step_dns (A B : Nat → Real) (hA : RReg A) (hB : RReg B) (n m j : Nat)
    (hjm : m ≤ j)
    (hclose : Rle (A j) (Radd (B j) (ofQ (⟨1, m + 1⟩ : Q) (Nat.succ_pos m)))) :
    Qle ((Rlim A hA).seq n)
        (add (add ((Rlim B hB).seq n) (⟨2, n + 1⟩ : Q)) (⟨13, m + 1⟩ : Q)) := by
  have hAt := Rlim_tendsTo A hA
  have hBt := Rlim_tendsTo B hB
  have hbj : Qle (Qbound j) (Qbound m) := by simp only [Qle, Qbound]; push_cast; omega
  have h2j : Qle (⟨2, j + 1⟩ : Q) (⟨2, m + 1⟩ : Q) := by simp only [Qle]; push_cast; omega
  have s1 : Qle ((Rlim A hA).seq n) (add ((Rlim A hA).seq j) (add (Qbound n) (Qbound j))) :=
    Qle_add_of_Qabs_sub ((Rlim A hA).den_pos n) ((Rlim A hA).den_pos j)
      (add_den_pos (Qbound_den_pos n) (Qbound_den_pos j)) ((Rlim A hA).reg n j)
  have s1' : Qle ((Rlim A hA).seq n) (add ((Rlim A hA).seq j) (add (Qbound n) (Qbound m))) :=
    Qle_trans (add_den_pos ((Rlim A hA).den_pos j) (add_den_pos (Qbound_den_pos n) (Qbound_den_pos j)))
      s1 (Qadd_le_add (Qle_refl ((Rlim A hA).seq j)) (Qadd_le_add (Qle_refl (Qbound n)) hbj))
  have s2raw : Qle ((Rlim A hA).seq j) (add ((A j).seq j) (add (⟨2, j + 1⟩ : Q) (⟨2, j + 1⟩ : Q))) := by
    have hcomm : Qle (Qabs (Qsub ((Rlim A hA).seq j) ((A j).seq j))) (add (⟨2, j + 1⟩ : Q) (⟨2, j + 1⟩ : Q)) := by
      rw [Qabs_Qsub_comm]; exact hAt j j
    exact Qle_add_of_Qabs_sub ((Rlim A hA).den_pos j) ((A j).den_pos j)
      (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)) hcomm
  have s2' : Qle ((Rlim A hA).seq j) (add ((A j).seq j) (add (⟨2, m + 1⟩ : Q) (⟨2, m + 1⟩ : Q))) :=
    Qle_trans (add_den_pos ((A j).den_pos j) (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)))
      s2raw (Qadd_le_add (Qle_refl ((A j).seq j)) (Qadd_le_add h2j h2j))
  have s3raw : Qle ((A j).seq j) (add ((B j).seq j) (add (⟨1, m + 1⟩ : Q) (⟨2, j + 1⟩ : Q))) :=
    seq_le_of_Rle_Radd_ofQ_dns (A j) (B j) (⟨1, m + 1⟩ : Q) (Nat.succ_pos m) hclose j
  have s3' : Qle ((A j).seq j) (add ((B j).seq j) (add (⟨1, m + 1⟩ : Q) (⟨2, m + 1⟩ : Q))) :=
    Qle_trans (add_den_pos ((B j).den_pos j) (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)))
      s3raw (Qadd_le_add (Qle_refl ((B j).seq j)) (Qadd_le_add (Qle_refl (⟨1, m + 1⟩ : Q)) h2j))
  have s4raw : Qle ((B j).seq j) (add ((Rlim B hB).seq j) (add (⟨2, j + 1⟩ : Q) (⟨2, j + 1⟩ : Q))) :=
    Qle_add_of_Qabs_sub ((B j).den_pos j) ((Rlim B hB).den_pos j)
      (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)) (hBt j j)
  have s4' : Qle ((B j).seq j) (add ((Rlim B hB).seq j) (add (⟨2, m + 1⟩ : Q) (⟨2, m + 1⟩ : Q))) :=
    Qle_trans (add_den_pos ((Rlim B hB).den_pos j) (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)))
      s4raw (Qadd_le_add (Qle_refl ((Rlim B hB).seq j)) (Qadd_le_add h2j h2j))
  have s5 : Qle ((Rlim B hB).seq j) (add ((Rlim B hB).seq n) (add (Qbound j) (Qbound n))) :=
    Qle_add_of_Qabs_sub ((Rlim B hB).den_pos j) ((Rlim B hB).den_pos n)
      (add_den_pos (Qbound_den_pos j) (Qbound_den_pos n)) ((Rlim B hB).reg j n)
  have s5' : Qle ((Rlim B hB).seq j) (add ((Rlim B hB).seq n) (add (Qbound m) (Qbound n))) :=
    Qle_trans (add_den_pos ((Rlim B hB).den_pos n) (add_den_pos (Qbound_den_pos j) (Qbound_den_pos n)))
      s5 (Qadd_le_add (Qle_refl ((Rlim B hB).seq n)) (Qadd_le_add hbj (Qle_refl (Qbound n))))
  have c1 : Qle ((Rlim A hA).seq n)
      (add (add ((A j).seq j) (add (⟨2, m + 1⟩ : Q) (⟨2, m + 1⟩ : Q))) (add (Qbound n) (Qbound m))) :=
    Qle_trans (add_den_pos ((Rlim A hA).den_pos j) (add_den_pos (Qbound_den_pos n) (Qbound_den_pos m)))
      s1' (Qadd_le_add s2' (Qle_refl _))
  have c2 : Qle ((Rlim A hA).seq n)
      (add (add (add ((B j).seq j) (add (⟨1, m + 1⟩ : Q) (⟨2, m + 1⟩ : Q)))
        (add (⟨2, m + 1⟩ : Q) (⟨2, m + 1⟩ : Q))) (add (Qbound n) (Qbound m))) :=
    Qle_trans (add_den_pos (add_den_pos ((A j).den_pos j)
        (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _))) (add_den_pos (Qbound_den_pos n) (Qbound_den_pos m)))
      c1 (Qadd_le_add (Qadd_le_add s3' (Qle_refl _)) (Qle_refl _))
  have c3 : Qle ((Rlim A hA).seq n)
      (add (add (add (add ((Rlim B hB).seq j) (add (⟨2, m + 1⟩ : Q) (⟨2, m + 1⟩ : Q)))
        (add (⟨1, m + 1⟩ : Q) (⟨2, m + 1⟩ : Q))) (add (⟨2, m + 1⟩ : Q) (⟨2, m + 1⟩ : Q)))
        (add (Qbound n) (Qbound m))) :=
    Qle_trans (add_den_pos (add_den_pos (add_den_pos ((B j).den_pos j)
        (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _))) (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)))
        (add_den_pos (Qbound_den_pos n) (Qbound_den_pos m)))
      c2 (Qadd_le_add (Qadd_le_add (Qadd_le_add s4' (Qle_refl _)) (Qle_refl _)) (Qle_refl _))
  have c4 : Qle ((Rlim A hA).seq n)
      (add (add (add (add (add ((Rlim B hB).seq n) (add (Qbound m) (Qbound n)))
        (add (⟨2, m + 1⟩ : Q) (⟨2, m + 1⟩ : Q))) (add (⟨1, m + 1⟩ : Q) (⟨2, m + 1⟩ : Q)))
        (add (⟨2, m + 1⟩ : Q) (⟨2, m + 1⟩ : Q))) (add (Qbound n) (Qbound m))) :=
    Qle_trans (add_den_pos (add_den_pos (add_den_pos (add_den_pos ((Rlim B hB).den_pos j)
        (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _))) (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)))
        (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _))) (add_den_pos (Qbound_den_pos n) (Qbound_den_pos m)))
      c3 (Qadd_le_add (Qadd_le_add (Qadd_le_add (Qadd_le_add s5' (Qle_refl _)) (Qle_refl _)) (Qle_refl _))
        (Qle_refl _))
  refine Qle_trans ?_ c4 (Qeq_le ?_)
  · exact add_den_pos (add_den_pos (add_den_pos (add_den_pos
      (add_den_pos ((Rlim B hB).den_pos n) (add_den_pos (Qbound_den_pos m) (Qbound_den_pos n)))
      (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)))
      (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)))
      (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)))
      (add_den_pos (Qbound_den_pos n) (Qbound_den_pos m))
  · simp only [Qeq, add, Qbound]; push_cast; ring_uor

/-- One-sided limit comparison (copy of `Rle_lim_of_close_one_side`). -/
private theorem Rle_lim_of_close_one_side_dns {A B : Nat → Real} (hA : RReg A) (hB : RReg B)
    (hAB : ∀ k : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n →
            Rle (A n) (Radd (B n) (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k)))) :
    Rle (Rlim A hA) (Rlim B hB) := by
  intro n
  apply Qarch_gen (C := 13) ((Rlim A hA).den_pos n)
    (add_den_pos ((Rlim B hB).den_pos n) (Nat.succ_pos _))
  intro m
  obtain ⟨N, hN⟩ := hAB m
  exact Rle_lim_step_dns A B hA hB n m (N + m) (Nat.le_add_left m N) (hN (N + m) (Nat.le_add_right N m))

/-- The constant sequence of reals is `RReg` (copy of the private `RReg_const`). -/
private theorem RReg_const_dns (c : Real) : RReg (fun _ => c) := by
  intro j k n
  show Qle (Qabs (Qsub (c.seq n) (c.seq n))) (add (add (⟨1, j + 1⟩ : Q) ⟨1, k + 1⟩) ⟨2, n + 1⟩)
  unfold Qle Qabs
  rw [Qsub_self_num]
  simp only [Int.natAbs_zero, Int.ofNat_zero, Int.zero_mul]
  have hden : (0 : Int) ≤ ((Qsub (c.seq n) (c.seq n)).den : Int) := Int.ofNat_nonneg _
  have hnum : (0 : Int) ≤ (add (add (⟨1, j + 1⟩ : Q) ⟨1, k + 1⟩) ⟨2, n + 1⟩).num := by
    simp only [add]
    exact Int.add_nonneg (Int.mul_nonneg (by omega) (by omega))
      (Int.mul_nonneg (by omega) (by omega))
  exact Int.mul_nonneg hnum hden

-- ===========================================================================
-- THE KEY HELPER — one-sided eventual `Rlim` bound against a rational constant.
-- ===========================================================================

/-- **One-sided eventual `Rlim` bound**: if a regular real sequence is eventually (for every tolerance
    `1/(t+1)`) below `c + 1/(t+1)`, then its Bishop limit is `≤ ofQ c`. The one-sided analogue of
    `Rlim_eq_of_close`, obtained by comparing against the constant sequence `ofQ c` via the
    `Rle_lim_of_close_one_side_dns` engine and `Rlim_const_core`. -/
theorem Rle_Rlim_ofQ_eventual_dns (Xseq : Nat → Real) (hX : RReg Xseq) (c : Q) (hc : 0 < c.den)
    (hev : ∀ t : Nat, ∃ M : Nat, ∀ n : Nat, M ≤ n →
             Rle (Xseq n) (ofQ (add c (⟨1, t + 1⟩ : Q)) (add_den_pos hc (Nat.succ_pos t)))) :
    Rle (Rlim Xseq hX) (ofQ c hc) := by
  have hB : RReg (fun _ => ofQ c hc) := RReg_const_dns (ofQ c hc)
  have step : Rle (Rlim Xseq hX) (Rlim (fun _ => ofQ c hc) hB) :=
    Rle_lim_of_close_one_side_dns hX hB (fun t => by
      obtain ⟨M, hM⟩ := hev t
      exact ⟨M, fun n hn => Rle_trans (hM n hn)
        (Rle_of_Req (Req_symm (Radd_ofQ_loc hc (Nat.succ_pos t))))⟩)
  exact Rle_trans step (Rle_of_Req (Rlim_const_core (ofQ c hc) hB))

-- ===========================================================================
-- REDUCTION: `completedDist2 X (of a)` IS the Bishop limit of the stagewise squared
-- distances `dlimDist2 (X.seq (σ n)) a` at the completion schedule, with `σ` cofinal
-- (`σ n ≥ 2n+1`). Pure definitional unfolding (`rfl`) once `S.seq m = dlimSub (X.seq (2m+1)) a`.
-- ===========================================================================

/-- **The completed squared distance to `of a` is a Bishop limit of stagewise squared distances.**
    `σ n = 2·(ρ·(n+1)−1)+1` with `ρ = Fsched (X⊖of a) (X⊖of a) ≥ 1`, so `σ n ≥ 2n+1` (cofinal). -/
theorem completedDist2_reduce_dns (X : DLimCompletionRaw) (a : DLimRaw) :
    ∃ (σ : Nat → Nat) (hg : RReg (fun n => dlimDist2 (X.seq (σ n)) a)),
      (∀ n, 2 * (n + 1) ≤ σ n + 1) ∧
      completedDist2 X (DLimCompletionRaw.of a)
        = Rlim (fun n => dlimDist2 (X.seq (σ n)) a) hg := by
  refine ⟨fun n => 2 * (Fsched (dlimCompletionSub X (DLimCompletionRaw.of a))
                          (dlimCompletionSub X (DLimCompletionRaw.of a)) * (n + 1) - 1) + 1,
    (innerSeq_CRegCore (dlimCompletionSub X (DLimCompletionRaw.of a))
                       (dlimCompletionSub X (DLimCompletionRaw.of a))).1, ?_, ?_⟩
  · intro n
    show 2 * (n + 1) ≤ 2 * (Fsched (dlimCompletionSub X (DLimCompletionRaw.of a))
                          (dlimCompletionSub X (DLimCompletionRaw.of a)) * (n + 1) - 1) + 1 + 1
    have hle : n + 1 ≤ Fsched (dlimCompletionSub X (DLimCompletionRaw.of a))
                              (dlimCompletionSub X (DLimCompletionRaw.of a)) * (n + 1) :=
      Nat.le_mul_of_pos_left (n + 1)
        (one_le_Fsched (dlimCompletionSub X (DLimCompletionRaw.of a))
                       (dlimCompletionSub X (DLimCompletionRaw.of a)))
    omega
  · rfl

-- ===========================================================================
-- THE TARGET — density of the finite-support direct limit in its completion.
-- ===========================================================================

/-- **Density**: for every tolerance `1/(k+1)`, the image `of (X.seq N)` (with `N := 2(k+1)`) of a
    finite-support representative lies within completed squared distance `1/(k+1)` of `X`. Since the
    stagewise squared distances `dlimDist2 (X.seq (σ n)) (X.seq N)` are Cauchy-bounded by
    `M(σ n, N) ≤ (1/(k+1))² ≤ 1/(k+1)` for `σ n` cofinal, the completion-level limit is `≤ 1/(k+1)`. -/
theorem completion_dense (X : DLimCompletionRaw) (k : Nat) :
    ∃ N : Nat, Rle (completedDist2 X (DLimCompletionRaw.of (X.seq N)))
      (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k)) := by
  refine ⟨2 * (k + 1), ?_⟩
  obtain ⟨σ, hg, hσ, heq⟩ := completedDist2_reduce_dns X (X.seq (2 * (k + 1)))
  rw [heq]
  refine Rle_Rlim_ofQ_eventual_dns _ hg (⟨1, k + 1⟩ : Q) (Nat.succ_pos k) (fun t => ?_)
  refine ⟨k, fun n hn => ?_⟩
  have hi : 2 * (k + 1) ≤ σ n + 1 := by have := hσ n; omega
  have hj : 2 * (k + 1) ≤ 2 * (k + 1) + 1 := by omega
  have hmpos : 0 < k + 1 := Nat.succ_pos k
  have hA : Qle (mul (⟨1, k + 1⟩ : Q) (⟨1, k + 1⟩ : Q)) (⟨1, k + 1⟩ : Q) := by
    have hkk : ((k + 1 : Nat) : Int) ≤ (((k + 1) * (k + 1) : Nat) : Int) := by
      exact_mod_cast Nat.le_mul_of_pos_left (k + 1) (Nat.succ_pos k)
    simp only [Qle, mul]; omega
  have hBle : Qle (⟨1, k + 1⟩ : Q) (add (⟨1, k + 1⟩ : Q) (⟨1, t + 1⟩ : Q)) :=
    Qle_self_add (by show (0 : Int) ≤ 1; omega)
  have hQ : Qle (mul (⟨1, k + 1⟩ : Q) (⟨1, k + 1⟩ : Q)) (add (⟨1, k + 1⟩ : Q) (⟨1, t + 1⟩ : Q)) :=
    Qle_trans (Nat.succ_pos k) hA hBle
  exact Rle_trans (X.reg (σ n) (2 * (k + 1)))
    (Rle_trans (dlimCauchyMod_le_inv_sq (σ n) (2 * (k + 1)) (k + 1) hmpos hi hj)
      (Rle_ofQ_of_Qle_loc _ _ hQ))

end UOR.Bridge.F1Square.Square

