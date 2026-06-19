import F1Square.Analysis.ArtanhAdd

/-!
# `RlogPos` multiplicativity (bounded modulus) — discharging the `Clog_add` modulus seam

`Clog_add` (`ComplexArgAdd.lean`) isolates one explicit hypothesis `hmod`, the `RlogPos`-multiplicativity
`log|zw|² = log|z|² + log|w|²`. This file discharges `hmod` in the **bounded-modulus** regime by
relating `RlogPos` (auto-derived radius) to the presented-radius `Rlog` and reusing `Rlog_mul`.

The two reusable bricks here:
* `reindex_Req` — a sequence reindexed past its tail presents the same real;
* `Rlog_congr` — `Rlog` is a congruence in its argument at small radius.

Both feed the `RlogPos → Rlog` bridge (`RlogPos_eq_Rlog`) and ultimately `RlogPos_mul`.
-/

namespace UOR.Bridge.F1Square.Analysis

/-- Reindexing a regular sequence by any `g` with `n ≤ g n` presents the **same real**. The drift
    `|x_{g n} − x_n| ≤ 1/(g n+1) + 1/(n+1) ≤ 2/(n+1)` (regularity + `g n ≥ n`). -/
theorem reindex_Req (x : Real) (g : Nat → Nat) (hg : ∀ n, n ≤ g n) :
    Req (⟨fun n => x.seq (g n), reindex_regular x g hg, fun _ => x.den_pos _⟩ : Real) x := by
  refine Req_of_lin_bound (C := 2) ?_
  intro n
  show Qle (Qabs (Qsub (x.seq (g n)) (x.seq n))) (⟨(2 : Int), n + 1⟩ : Q)
  refine Qle_trans (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _)) (x.reg (g n) n) ?_
  refine Qle_trans (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _))
    (Qadd_le_add (Qbound_anti (hg n)) (Qle_refl _)) ?_
  apply Qeq_le; show Qeq (add (Qbound n) (Qbound n)) (⟨(2 : Int), n + 1⟩ : Q)
  simp only [Qeq, add, Qbound]; push_cast; ring_uor

set_option maxHeartbeats 1600000 in
/-- **`Rlog` congruence in its argument** (small radius): if `x ≈ y` and both present a `log` at a
    common modulus `M` (with the small-radius `ρ_M² ≤ 1/2`), then `Rlog x M ≈ Rlog y M`. The `t`-map
    arguments `tmap(x.seq ·) ≈ tmap(y.seq ·)` (`tmap_lip` + `x ≈ y`), lifted through `Rartanh_congr`. -/
theorem Rlog_congr (x y : Real) (M : Q) (hMd : 0 < M.den) (hMge : Qle (⟨1, 1⟩ : Q) M)
    (hxpos : ∀ n, 0 < (x.seq n).num) (hxhi : ∀ n, Qle (x.seq n) M)
    (hxlo : ∀ n, Qle (⟨1, 1⟩ : Q) (mul (x.seq n) M))
    (hypos : ∀ n, 0 < (y.seq n).num) (hyhi : ∀ n, Qle (y.seq n) M)
    (hylo : ∀ n, Qle (⟨1, 1⟩ : Q) (mul (y.seq n) M))
    (hρ2 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ⟨M.num - (M.den : Int), M.num.toNat + M.den⟩
              ⟨M.num - (M.den : Int), M.num.toNat + M.den⟩)))
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
  exact Rartanh_congr _ _ _ hρ0 hρd hρlt hρ2 (fun n => hbtρx (Rlog_R n)) (fun n => hbtρy (Rlog_R n)) hWeq

end UOR.Bridge.F1Square.Analysis
