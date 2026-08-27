/-
F1 square — **THE DEGENERATE WINDOW `w = 0`** (`AtlasWindowZero.lean`, target side).

Every channel density of the five-channel carrier carries the factor `w` of the Haar window.  When `w = 0` the
five channel Grams vanish identically (`inner5_w_zero`), hence so does the level-`k` defect on every pair of
core tests (`defect_w_zero` through `source5_split_fixed`), and the scheduled limit is `0`:
`CurrentArchDominatesPrime` holds outright for every context with a degenerate window
(`currentArchDominatesPrime_of_w_zero`).  This is the direct treatment of the case excluded by the
hypothesis `0 < w.num` of the fiber kernel; it asserts nothing for `w > 0`.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasFiveSplit

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis
open CField

/-- A rational with numerator `0` is `0`. -/
theorem ofQ_num_zero_eq_zero {q : Q} (hqd : 0 < q.den) (h : q.num = 0) : Req (ofQ q hqd) zero :=
  Req_of_seq_Qeq (fun _ => by show q.num * ((1 : Nat) : Int) = 0 * (q.den : Int); rw [h]; simp)

/-- `w = 0` ⟹ the Haar weight `w·r(t)` vanishes. -/
theorem wrF_zero (C : NormCtx) (hw : C.w.num = 0) (x t : Real) : Req ((wrF C).F x t) zero := by
  rw [wrF_F]
  exact Req_trans (Rmul_congr (ofQ_num_zero_eq_zero C.hw hw) (Req_refl _)) (Req_trans (Rmul_comm _ _) (Rmul_zero _))

theorem poleDens5_zero (C : NormCtx) (hw : C.w.num = 0) (x t : Real) : Req ((poleDens5 C).F x t) zero := by
  show Req (Rmul _ (Rmul _ (Rmul _ ((wrF C).F x t)))) zero
  exact Req_trans (Rmul_congr (Req_refl _) (Req_trans (Rmul_congr (Req_refl _) (Req_trans (Rmul_congr (Req_refl _) (wrF_zero C hw x t)) (Rmul_zero _))) (Rmul_zero _))) (Rmul_zero _)
theorem primeDens5_zero (C : NormCtx) (hw : C.w.num = 0) (m : Nat) (x t : Real) : Req ((primeDens5 C m).F x t) zero := by
  show Req (Rmul _ (Rmul _ (Rmul _ ((wrF C).F x t)))) zero
  exact Req_trans (Rmul_congr (Req_refl _) (Req_trans (Rmul_congr (Req_refl _) (Req_trans (Rmul_congr (Req_refl _) (wrF_zero C hw x t)) (Rmul_zero _))) (Rmul_zero _))) (Rmul_zero _)
theorem constDens5_zero (C : NormCtx) (hw : C.w.num = 0) (x t : Real) : Req ((constDens5 C).F x t) zero := by
  show Req (Rmul _ (Rmul _ ((wrF C).F x t))) zero
  exact Req_trans (Rmul_congr (Req_refl _) (Req_trans (Rmul_congr (Req_refl _) (wrF_zero C hw x t)) (Rmul_zero _))) (Rmul_zero _)
theorem tailDens5_zero (C : NormCtx) (hw : C.w.num = 0) (x t : Real) : Req ((tailDens5 C).F x t) zero := by
  show Req (Rmul _ (Rmul _ ((wrF C).F x t))) zero
  exact Req_trans (Rmul_congr (Req_refl _) (Req_trans (Rmul_congr (Req_refl _) (wrF_zero C hw x t)) (Rmul_zero _))) (Rmul_zero _)
theorem farDens5_zero (C : NormCtx) (hw : C.w.num = 0) (fc : Real) (x t : Real) : Req ((farDens5 C fc).F x t) zero := by
  show Req (Rmul _ (Rmul _ ((wrF C).F x t))) zero
  exact Req_trans (Rmul_congr (Req_refl _) (Req_trans (Rmul_congr (Req_refl _) (wrF_zero C hw x t)) (Rmul_zero _))) (Rmul_zero _)

/-- A Gram integrand with vanishing density vanishes. -/
theorem gram_int_zero (d u v : CField) (x t : Real) (hd : Req (d.F x t) zero) : Req ((mulF (mulF d u) v).F x t) zero :=
  Req_trans (Rmul_congr (Req_trans (Rmul_congr hd (Req_refl _)) (Req_trans (Rmul_comm _ _) (Rmul_zero _))) (Req_refl _))
    (Req_trans (Rmul_comm _ _) (Rmul_zero _))

/-- The window integral of a pointwise-zero field vanishes. -/
theorem intX_zero_pt (C : NormCtx) (z : CField) (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (h : ∀ x t, Req (z.F x t) zero) : Req (intX C z lo w hlo hw hwn) zero := by
  unfold intX
  refine Req_trans (intI_congr_free _ _ _ _ (by decide) (by decide) (const_lip0 zero) (fun _ _ _ => Req_refl zero)
    (fun x => intT_zero_pt C z x (h x)) lo w hlo hw hwn) ?_
  exact Req_trans (riemannIntegralI_const zero lo w hlo hw hwn) (Rmul_zero _)

theorem RsumN_zero_of (F : Nat → Real) : ∀ N, (∀ i, i < N → Req (F i) zero) → Req (RsumN F N) zero
  | 0, _ => by rw [RsumN_zero_fl]; exact Req_refl _
  | (n + 1), h => by
      rw [RsumN_succ_fl]
      exact Req_trans (Radd_congr (RsumN_zero_of F n (fun i hi => h i (Nat.lt_succ_of_lt hi))) (h n (Nat.lt_succ_self n))) (Radd_zero _)

/-- **★ `w = 0` ⟹ the five-channel form vanishes identically.** -/
theorem inner5_w_zero (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (fc : Real) (hw : C.w.num = 0) (z₁ z₂ : Carrier5) :
    Req (inner5 C k hk fc z₁ z₂) zero := by
  unfold inner5 inner4 poleG primeG constG tailG farG gramX gramT
  refine Req_trans (Radd_congr (Radd_congr (Radd_congr (Radd_congr ?_ ?_) ?_) ?_) ?_)
    (Req_trans (Radd_zero _) (Req_trans (Radd_zero _) (Req_trans (Radd_zero _) (Radd_zero _))))
  · exact intX_zero_pt C _ _ _ _ _ _ (fun x t => gram_int_zero _ _ _ x t (poleDens5_zero C hw x t))
  · exact RsumN_zero_of _ C.X (fun m _ => intT_zero_pt C _ one (fun t => gram_int_zero _ _ _ one t (primeDens5_zero C hw m one t)))
  · exact intT_zero_pt C _ one (fun t => gram_int_zero _ _ _ one t (constDens5_zero C hw one t))
  · exact intX_zero_pt C _ _ _ _ _ _ (fun x t => gram_int_zero _ _ _ x t (tailDens5_zero C hw x t))
  · exact intT_zero_pt C _ one (fun t => gram_int_zero _ _ _ one t (farDens5_zero C hw fc one t))

/-- `w = 0` ⟹ the level-`k` defect vanishes on every pair of tests. -/
theorem defect_w_zero (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (hw : C.w.num = 0) (f g : L2Test) :
    Req (Radd (atlasDefectGram C k hk f g) (farTailGram C f g k)) zero := by
  refine Req_trans (source5_split_fixed C k hk f g) ?_
  refine Req_trans (Rsub_congr (inner5_w_zero C k hk _ hw _ _) (inner5_w_zero C k hk _ hw _ _)) ?_
  exact Radd_neg zero

/-- **★ DOMINANCE FOR A DEGENERATE WINDOW**: `w = 0` ⟹ `CurrentArchDominatesPrime C`. -/
theorem currentArchDominatesPrime_of_w_zero (C : NormCtx) (hw : C.w.num = 0) : CurrentArchDominatesPrime C :=
  defectSeq_nonneg_imp_dominance C (fun f j => Rnonneg_congr (Req_symm (defect_w_zero C _ (archCNC_pos C f.1 f.1 j) hw f.1 f.1))
    (Rnonneg_ofQ (by decide) (by decide)))

end UOR.Bridge.F1Square.Square
