/-
F1 square — **the `t4PoleB` pieces, part 1: the combinators** (`T4PoleBPieces.lean`).
The poleB piece integrands are sums `C·gRecipC + q·gLx` (real constant `C`, rational
`q`); this file supplies the generic Lipschitz combinators they need —

    `smul_lip`  : `|C| ≤ B`, `f` `L_f`-Lipschitz ⟹ `C·f` is `(B·L_f)`-Lipschitz,
    `add_lip`   : `f` `L_f`-, `g` `L_g`-Lipschitz ⟹ `f + g` is `(L_f + L_g)`-Lipschitz

— and the cone-height bounds `0 ≤ t4H = 2·log 2 ≤ 2` (`|t4H| ≤ 2`), feeding
`riemannIntegral_recipC_smul` at `B = 2`.

HONEST SCOPE. Certificate combinators and a constant bound; no integral, no
positivity. The crux fields stay `none`.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.RecipSmulEval
import F1Square.Analysis.T4PoleAPieces

namespace UOR.Bridge.F1Square.Analysis

/-- `a·z + b·z ≈ (a+b)·z` (private copy). -/
private theorem tb_smul_add {a b : Q} (ha : 0 < a.den) (hb : 0 < b.den) (z : Real) :
    Req (Radd (Rmul (ofQ a ha) z) (Rmul (ofQ b hb) z))
      (Rmul (ofQ (add a b) (add_den_pos ha hb)) z) := by
  refine Req_trans (Radd_congr (Rmul_comm _ z) (Rmul_comm _ z)) ?_
  refine Req_trans (Req_symm (Rmul_distrib z (ofQ a ha) (ofQ b hb))) ?_
  refine Req_trans (Rmul_comm z _) ?_
  exact Rmul_congr (Radd_ofQ_ofQ ha hb) (Req_refl z)

/-- **The real-scalar Lipschitz combinator**: `|C| ≤ B` and `f` `L_f`-Lipschitz give
    `C·f` `(B·L_f)`-Lipschitz. -/
theorem smul_lip {C : Real} {Bq : Q} (hBd : 0 < Bq.den) (hCb : Rle (Rabs C) (ofQ Bq hBd))
    {f : Real → Real} {Lf : Q} (hLfd : 0 < Lf.den) (hLfn : 0 ≤ Lf.num)
    (hf : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ Lf hLfd) (Rabs (Rsub x y)))) :
    ∀ x y, Rle (Rabs (Rsub (Rmul C (f x)) (Rmul C (f y))))
      (Rmul (ofQ (mul Bq Lf) (Qmul_den_pos hBd hLfd)) (Rabs (Rsub x y))) := by
  intro x y
  refine Rle_trans (Rle_of_Req (Rabs_congr
    (Req_symm (Rmul_sub_distrib C (f x) (f y))))) ?_
  refine Rle_trans (Rle_of_Req (Rabs_Rmul C _)) ?_
  refine Rle_trans (Rmul_le_Rmul_both (Rnonneg_Rabs _)
    (Rnonneg_Rmul (Rnonneg_ofQ hLfd hLfn) (Rnonneg_Rabs _)) hCb (hf x y)) ?_
  exact Rle_of_Req (Req_trans (Req_symm (Rmul_assoc _ _ _))
    (Rmul_congr (Rmul_ofQ_ofQ hBd hLfd) (Req_refl _)))

/-- `C·f` respects `≈`, given `f`'s congruence. -/
theorem smul_congr (C : Real) {f : Real → Real}
    (hfc : ∀ x y : Real, Req x y → Req (f x) (f y)) :
    ∀ x y : Real, Req x y → Req (Rmul C (f x)) (Rmul C (f y)) :=
  fun _ _ h => Rmul_congr (Req_refl C) (hfc _ _ h)

/-- **The sum Lipschitz combinator**: `f` `L_f`-, `g` `L_g`-Lipschitz give `f + g`
    `(L_f + L_g)`-Lipschitz. -/
theorem add_lip {f g : Real → Real} {Lf Lg : Q}
    (hLfd : 0 < Lf.den) (hLgd : 0 < Lg.den)
    (hf : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ Lf hLfd) (Rabs (Rsub x y))))
    (hg : ∀ x y, Rle (Rabs (Rsub (g x) (g y))) (Rmul (ofQ Lg hLgd) (Rabs (Rsub x y)))) :
    ∀ x y, Rle (Rabs (Rsub (Radd (f x) (g x)) (Radd (f y) (g y))))
      (Rmul (ofQ (add Lf Lg) (add_den_pos hLfd hLgd)) (Rabs (Rsub x y))) := by
  intro x y
  refine Rle_trans (Rle_of_Req (Rabs_congr
    (Rsub_Radd_Radd (f x) (g x) (f y) (g y)))) ?_
  refine Rle_trans (Rabs_Radd _ _) ?_
  refine Rle_trans (Radd_le_add (hf x y) (hg x y)) ?_
  exact Rle_of_Req (tb_smul_add hLfd hLgd (Rabs (Rsub x y)))

/-- `f + g` respects `≈`. -/
theorem add_congr_fn {f g : Real → Real}
    (hfc : ∀ x y : Real, Req x y → Req (f x) (f y))
    (hgc : ∀ x y : Real, Req x y → Req (g x) (g y)) :
    ∀ x y : Real, Req x y → Req (Radd (f x) (g x)) (Radd (f y) (g y)) :=
  fun _ _ h => Radd_congr (hfc _ _ h) (hgc _ _ h)

/-- `t4H = 2·log 2 ≥ 0`. -/
theorem t4H_nonneg : Rnonneg t4H :=
  Rnonneg_Rmul (Rnonneg_ofQ Nat.one_pos (Int.ofNat_nonneg 2)) (Rnonneg_logN 2 (by omega))

/-- **`|t4H| ≤ 2`** — the cone height under the `recipC_smul` bound. -/
theorem t4H_abs : Rle (Rabs t4H) (ofQ (⟨2, 1⟩ : Q) (by decide)) := by
  refine Rle_trans (Rle_of_Req (Rabs_of_nonneg t4H_nonneg)) ?_
  refine Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ Nat.one_pos (Int.ofNat_nonneg 2))
    logN_two_le_one) ?_
  refine Rle_of_Req (Req_trans (Rmul_ofQ_ofQ Nat.one_pos Nat.one_pos) ?_)
  exact ofQ_congr (Qmul_den_pos Nat.one_pos Nat.one_pos) (by decide) (by decide)

/-- `|log 2| ≤ 1` — the half-height bound (for the `[1/2, 1]` piece). -/
theorem oneL_abs : Rle (Rabs (logN 2 (by omega))) (ofQ (⟨1, 1⟩ : Q) (by decide)) :=
  Rle_trans (Rle_of_Req (Rabs_of_nonneg (Rnonneg_logN 2 (by omega)))) logN_two_le_one


-- ===========================================================================
-- Part 2: the upper pieces `[c, c+1]` — `(2log2 − log x)/x` as `t4H·recip − ½·gLx`.
-- ===========================================================================

/-- `|−1/2| ≤ 1/2`. -/
theorem negHalf_abs :
    Rle (Rabs (ofQ (⟨-1, 2⟩ : Q) (by decide))) (ofQ (⟨1, 2⟩ : Q) (by decide)) :=
  Rle_trans (Rle_of_Req (Rabs_ofQ (by decide)))
    (Rle_of_Req (ofQ_congr (by decide) (by decide) (by decide)))

/-- The `gLx` natural Lipschitz constant (`2c + 2`). -/
def LxQ (c : Nat) : Q :=
  add (mul (⟨((2 * c : Nat) : Int), 1⟩ : Q) (⟨1, 1⟩ : Q))
    (mul (⟨1, 1⟩ : Q) (⟨2, 1⟩ : Q))

theorem LxQ_den_pos (c : Nat) : 0 < (LxQ c).den :=
  add_den_pos (Qmul_den_pos Nat.one_pos Nat.one_pos) (Qmul_den_pos Nat.one_pos Nat.one_pos)

theorem LxQ_num_nonneg (c : Nat) : 0 ≤ (LxQ c).num :=
  Int.add_nonneg
    (Int.mul_nonneg (Int.mul_nonneg (Int.ofNat_nonneg _) (by decide)) (Int.ofNat_nonneg _))
    (Int.mul_nonneg (by decide) (Int.ofNat_nonneg _))

set_option maxHeartbeats 1600000 in
/-- **The upper-piece evaluation, general in the base and the weakening certificates**:
    `∫₀¹ (t4H·(1/(c+t)) + (−1/2)·gLx c) dt ≈ t4H·(log(c+1) − log c) − (1/2)·(Hn(c+1) −
    Hn(c))` — the pulled-back `∫_c^{c+1} (2log2 − log x)/x dx`. -/
theorem t4B_upper_eval (c : Nat) (hc1 : 1 ≤ c) (hc3 : c ≤ 3)
    (hgl : ∀ x y : Real, Rle (Rabs (Rsub (gLog c x) (gLog c y)))
      (Rmul (ofQ (⟨1, 1⟩ : Q) (by decide)) (Rabs (Rsub x y))))
    (hgc : ∀ x y : Real, Req x y → Req (gLog c x) (gLog c y))
    {L : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hq1 : Qle (mul (⟨2, 1⟩ : Q) (⟨1, 1⟩ : Q)) L)
    (hqx : Qle (LxQ c) L)
    (hq2 : Qle (mul (⟨1, 2⟩ : Q) (LxQ c)) L)
    (hqS : Qle (add (mul (⟨2, 1⟩ : Q) (⟨1, 1⟩ : Q)) (mul (⟨1, 2⟩ : Q) (LxQ c))) L)
    (hsch : ∀ j, 5 * (j + 1) ≤ digammaMidx L j) :
    Req (riemannIntegral
        (f := fun t => Radd (Rmul t4H (gRecipC c t))
          (Rmul (ofQ (⟨-1, 2⟩ : Q) (by decide)) (gLx c t)))
        hLd hLn
        (fun x y => lip_mono
          (add_den_pos (Qmul_den_pos Nat.one_pos Nat.one_pos)
            (Qmul_den_pos (by decide) (LxQ_den_pos c))) hLd hqS (Rnonneg_Rabs _)
          (add_lip (Qmul_den_pos Nat.one_pos Nat.one_pos)
            (Qmul_den_pos (by decide) (LxQ_den_pos c))
            (smul_lip Nat.one_pos t4H_abs Nat.one_pos (by decide) (gRecipC_lip c))
            (smul_lip (by decide) negHalf_abs (LxQ_den_pos c) (LxQ_num_nonneg c)
              (gLx_lip_of c hc3 hgl)) x y))
        (add_congr_fn (smul_congr t4H (gRecipC_congr c))
          (smul_congr (ofQ (⟨-1, 2⟩ : Q) (by decide)) (gLx_congr_of c hgc))))
      (Radd (Rmul t4H (Rsub (logN (c + 1) (by omega)) (logN c hc1)))
        (Rmul (ofQ (⟨-1, 2⟩ : Q) (by decide))
          (Rsub (Hn (c + 1) (by omega)) (Hn c hc1)))) := by
  refine Req_trans (riemannIntegral_add (f := fun t => Rmul t4H (gRecipC c t))
    (g := fun t => Rmul (ofQ (⟨-1, 2⟩ : Q) (by decide)) (gLx c t)) hLd hLn
    (fun x y => lip_mono (Qmul_den_pos Nat.one_pos Nat.one_pos) hLd hq1
      (Rnonneg_Rabs _) (smul_lip Nat.one_pos t4H_abs Nat.one_pos (by decide)
        (gRecipC_lip c) x y))
    (smul_congr t4H (gRecipC_congr c))
    (fun x y => lip_mono (Qmul_den_pos (by decide) (LxQ_den_pos c)) hLd hq2
      (Rnonneg_Rabs _) (smul_lip (by decide) negHalf_abs (LxQ_den_pos c)
        (LxQ_num_nonneg c) (gLx_lip_of c hc3 hgl) x y))
    (smul_congr (ofQ (⟨-1, 2⟩ : Q) (by decide)) (gLx_congr_of c hgc))
    _ _) ?_
  refine Radd_congr ?_ ?_
  · exact riemannIntegral_recipC_smul c hc1 t4H (B := (⟨2, 1⟩ : Q)) (by decide)
      (by decide) t4H_abs hLd hLn _ _ hsch
  · refine Req_trans (riemannIntegral_smul (⟨-1, 2⟩ : Q) (by decide) hLd hLn
      (fun x y => lip_mono (LxQ_den_pos c) hLd hqx (Rnonneg_Rabs _)
        (gLx_lip_of c hc3 hgl x y))
      (gLx_congr_of c hgc) _ _) ?_
    exact Rmul_congr (Req_refl _)
      (riemannIntegral_gLx_gen c hc1 hc3 hLd hLn
        (fun x y => lip_mono (LxQ_den_pos c) hLd hqx (Rnonneg_Rabs _)
          (gLx_lip_of c hc3 hgl x y))
        (gLx_congr_of c hgc) hsch)

end UOR.Bridge.F1Square.Analysis
