/-
F1 square — **component laws of the closed Weil form, II: the archimedean tail**
(`WeilArchTailLaws.lean`): `ArchTailForm_symm/add_left/add_right`.  The numerator
`N(x) = F_{f,g}+F_{g,f}−2F_{f,g}(1)/x` is pointwise symmetric (`F_{g,f}(1) = F_{f,g}(1)`) and
biadditive; the regular and far parts follow by the improper bricks (`improper_congr_sched`,
`improper_add_sched` — the sealed constants `archK` and the moduli differ syntactically and are
reconciled there); the near part `Near = lim_k J_k` by the PROVED rates `|J_k − Near| ≤ CN/2ᵏ`
(the two sides run on different `nearCN` schedules — reconciled through the common truncations).
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.WeilFormLaws

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- (1) The numerator: pointwise symmetry and biadditivity.
-- ===========================================================================

theorem archNum_symm_pt (G : ClosedGeom) (f g : L2Test) (x : Real) :
    Req ((archNum G f g).f x) ((archNum G g f).f x) := by
  rw [archNum_f, archNum_f]
  exact Radd_congr (Radd_comm _ _)
    (Rneg_congr (Rmul_congr (Rmul_congr (Req_refl _) (FTestG_one_symm G f g)) (Req_refl _)))

/-- Abstract: `((A₁+A₂)+(B₁+B₂)) − (T₁+T₂) = ((A₁+B₁) − T₁) + ((A₂+B₂) − T₂)`. -/
theorem archNum_add_alg (A₁ A₂ B₁ B₂ T₁ T₂ : Real) :
    Req (Radd (Radd (Radd A₁ A₂) (Radd B₁ B₂)) (Rneg (Radd T₁ T₂)))
        (Radd (Radd (Radd A₁ B₁) (Rneg T₁)) (Radd (Radd A₂ B₂) (Rneg T₂))) := by
  refine Req_trans (Radd_congr (Radd_add_add_comm _ _ _ _) (Rneg_Radd _ _)) ?_
  exact Radd_add_add_comm _ _ _ _

theorem archNum_add_left_pt (G : ClosedGeom) (f₁ f₂ g : L2Test) (x : Real) :
    Req ((archNum G (L2Test.add f₁ f₂) g).f x) (Radd ((archNum G f₁ g).f x) ((archNum G f₂ g).f x)) := by
  rw [archNum_f, archNum_f, archNum_f]
  have hT : Req (Rmul (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) ((FTestG G (L2Test.add f₁ f₂) g).f one))
      (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x))
      (Radd (Rmul (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) ((FTestG G f₁ g).f one))
          (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x))
        (Rmul (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) ((FTestG G f₂ g).f one))
          (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x))) := by
    refine Req_trans (Rmul_congr (Rmul_congr (Req_refl _) (FTestG_add_left G f₁ f₂ g one)) (Req_refl _)) ?_
    refine Req_trans (Rmul_congr (Rmul_distrib _ _ _) (Req_refl _)) ?_
    exact Rmul_distrib_right _ _ _
  refine Req_trans (Radd_congr (Radd_congr (FTestG_add_left G f₁ f₂ g x) (FTestG_add_right G g f₁ f₂ x))
    (Rneg_congr hT)) ?_
  exact archNum_add_alg _ _ _ _ _ _

theorem archNum_add_right_pt (G : ClosedGeom) (f g₁ g₂ : L2Test) (x : Real) :
    Req ((archNum G f (L2Test.add g₁ g₂)).f x) (Radd ((archNum G f g₁).f x) ((archNum G f g₂).f x)) := by
  rw [archNum_f, archNum_f, archNum_f]
  have hT : Req (Rmul (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) ((FTestG G f (L2Test.add g₁ g₂)).f one))
      (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x))
      (Radd (Rmul (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) ((FTestG G f g₁).f one))
          (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x))
        (Rmul (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) ((FTestG G f g₂).f one))
          (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x))) := by
    refine Req_trans (Rmul_congr (Rmul_congr (Req_refl _) (FTestG_add_right G f g₁ g₂ one)) (Req_refl _)) ?_
    refine Req_trans (Rmul_congr (Rmul_distrib _ _ _) (Req_refl _)) ?_
    exact Rmul_distrib_right _ _ _
  refine Req_trans (Radd_congr (Radd_congr (FTestG_add_right G f g₁ g₂ x) (FTestG_add_left G g₁ g₂ f x))
    (Rneg_congr hT)) ?_
  exact archNum_add_alg _ _ _ _ _ _

-- ===========================================================================
-- (2) The regular and far parts.
-- ===========================================================================

theorem archRegIntegrand_f (G : ClosedGeom) (f g : L2Test) (x : Real) :
    (archRegIntegrand G f g).f x = Rmul ((archNum G f g).f x) (archKernReg.f x) := by
  unfold archRegIntegrand; rfl

theorem archFarIntegrand_f (G : ClosedGeom) (f g : L2Test) (u : Real) :
    (archFarIntegrand G f g).f u
      = Rmul ((archNum G f g).f (Radd u one)) (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) u) := by
  unfold archFarIntegrand; rfl

theorem archRegDecayAt (G : ClosedGeom) (f g : L2Test) (hf : CoreTest G f) (hg : CoreTest G g) :
    DecayAt (archRegIntegrand G f g) (archK G f g (archRegIntegrand G f g).M)
      (archK_den G f g _ (archRegIntegrand G f g).hMd) := archRegDecay G f g hf hg

theorem archFarDecayAt (G : ClosedGeom) (f g : L2Test) (hf : CoreTest G f) (hg : CoreTest G g) :
    DecayAt (archFarIntegrand G f g) (archK G f g (archFarIntegrand G f g).M)
      (archK_den G f g _ (archFarIntegrand G f g).hMd) := archFarDecay G f g hf hg

theorem ArchRegPart_symm (G : ClosedGeom) (f g : L2Test) (hf : CoreTest G f) (hg : CoreTest G g) :
    Req (ArchRegPart G f g hf hg) (ArchRegPart G g f hg hf) := by
  unfold ArchRegPart
  exact improper_congr_sched _ _ _ _ _ _ (archRegDecayAt G f g hf hg) (archRegDecayAt G g f hg hf)
    (integralTerm_congr_all _ _ (fun x => by
      rw [archRegIntegrand_f, archRegIntegrand_f]; exact Rmul_congr (archNum_symm_pt G f g x) (Req_refl _)))

theorem ArchFarPart_symm (G : ClosedGeom) (f g : L2Test) (hf : CoreTest G f) (hg : CoreTest G g) :
    Req (ArchFarPart G f g hf hg) (ArchFarPart G g f hg hf) := by
  unfold ArchFarPart
  exact improper_congr_sched _ _ _ _ _ _ (archFarDecayAt G f g hf hg) (archFarDecayAt G g f hg hf)
    (integralTerm_congr_all _ _ (fun u => by
      rw [archFarIntegrand_f, archFarIntegrand_f]; exact Rmul_congr (archNum_symm_pt G f g _) (Req_refl _)))

theorem ArchRegPart_add_left (G : ClosedGeom) (f₁ f₂ g : L2Test) (h₁ : CoreTest G f₁) (h₂ : CoreTest G f₂)
    (hg : CoreTest G g) :
    Req (ArchRegPart G (L2Test.add f₁ f₂) g (coreTest_add h₁ h₂) hg)
        (Radd (ArchRegPart G f₁ g h₁ hg) (ArchRegPart G f₂ g h₂ hg)) := by
  unfold ArchRegPart
  exact improper_add_sched _ _ _ _ _ _ _ _ _ (archRegDecayAt G f₁ g h₁ hg) (archRegDecayAt G f₂ g h₂ hg)
    (archRegDecayAt G _ g (coreTest_add h₁ h₂) hg)
    (fun m => Req_trans (integralTerm_congr_all _ (L2Test.add (archRegIntegrand G f₁ g) (archRegIntegrand G f₂ g))
      (fun x => by
        rw [archRegIntegrand_f]
        show Req _ (Radd ((archRegIntegrand G f₁ g).f x) ((archRegIntegrand G f₂ g).f x))
        rw [archRegIntegrand_f, archRegIntegrand_f]
        exact Req_trans (Rmul_congr (archNum_add_left_pt G f₁ f₂ g x) (Req_refl _)) (Rmul_distrib_right _ _ _)) m)
      (integralTerm_addTest _ _ m))

theorem ArchRegPart_add_right (G : ClosedGeom) (f g₁ g₂ : L2Test) (hf : CoreTest G f) (h₁ : CoreTest G g₁)
    (h₂ : CoreTest G g₂) :
    Req (ArchRegPart G f (L2Test.add g₁ g₂) hf (coreTest_add h₁ h₂))
        (Radd (ArchRegPart G f g₁ hf h₁) (ArchRegPart G f g₂ hf h₂)) := by
  unfold ArchRegPart
  exact improper_add_sched _ _ _ _ _ _ _ _ _ (archRegDecayAt G f g₁ hf h₁) (archRegDecayAt G f g₂ hf h₂)
    (archRegDecayAt G f _ hf (coreTest_add h₁ h₂))
    (fun m => Req_trans (integralTerm_congr_all _ (L2Test.add (archRegIntegrand G f g₁) (archRegIntegrand G f g₂))
      (fun x => by
        rw [archRegIntegrand_f]
        show Req _ (Radd ((archRegIntegrand G f g₁).f x) ((archRegIntegrand G f g₂).f x))
        rw [archRegIntegrand_f, archRegIntegrand_f]
        exact Req_trans (Rmul_congr (archNum_add_right_pt G f g₁ g₂ x) (Req_refl _)) (Rmul_distrib_right _ _ _)) m)
      (integralTerm_addTest _ _ m))

theorem ArchFarPart_add_left (G : ClosedGeom) (f₁ f₂ g : L2Test) (h₁ : CoreTest G f₁) (h₂ : CoreTest G f₂)
    (hg : CoreTest G g) :
    Req (ArchFarPart G (L2Test.add f₁ f₂) g (coreTest_add h₁ h₂) hg)
        (Radd (ArchFarPart G f₁ g h₁ hg) (ArchFarPart G f₂ g h₂ hg)) := by
  unfold ArchFarPart
  exact improper_add_sched _ _ _ _ _ _ _ _ _ (archFarDecayAt G f₁ g h₁ hg) (archFarDecayAt G f₂ g h₂ hg)
    (archFarDecayAt G _ g (coreTest_add h₁ h₂) hg)
    (fun m => Req_trans (integralTerm_congr_all _ (L2Test.add (archFarIntegrand G f₁ g) (archFarIntegrand G f₂ g))
      (fun u => by
        rw [archFarIntegrand_f]
        show Req _ (Radd ((archFarIntegrand G f₁ g).f u) ((archFarIntegrand G f₂ g).f u))
        rw [archFarIntegrand_f, archFarIntegrand_f]
        exact Req_trans (Rmul_congr (archNum_add_left_pt G f₁ f₂ g _) (Req_refl _)) (Rmul_distrib_right _ _ _)) m)
      (integralTerm_addTest _ _ m))

theorem ArchFarPart_add_right (G : ClosedGeom) (f g₁ g₂ : L2Test) (hf : CoreTest G f) (h₁ : CoreTest G g₁)
    (h₂ : CoreTest G g₂) :
    Req (ArchFarPart G f (L2Test.add g₁ g₂) hf (coreTest_add h₁ h₂))
        (Radd (ArchFarPart G f g₁ hf h₁) (ArchFarPart G f g₂ hf h₂)) := by
  unfold ArchFarPart
  exact improper_add_sched _ _ _ _ _ _ _ _ _ (archFarDecayAt G f g₁ hf h₁) (archFarDecayAt G f g₂ hf h₂)
    (archFarDecayAt G f _ hf (coreTest_add h₁ h₂))
    (fun m => Req_trans (integralTerm_congr_all _ (L2Test.add (archFarIntegrand G f g₁) (archFarIntegrand G f g₂))
      (fun u => by
        rw [archFarIntegrand_f]
        show Req _ (Radd ((archFarIntegrand G f g₁).f u) ((archFarIntegrand G f g₂).f u))
        rw [archFarIntegrand_f, archFarIntegrand_f]
        exact Req_trans (Rmul_congr (archNum_add_right_pt G f g₁ g₂ _) (Req_refl _)) (Rmul_distrib_right _ _ _)) m)
      (integralTerm_addTest _ _ m))

-- ===========================================================================
-- (3) The near part: window laws of `nearJ`, then the limit through the rates.
-- ===========================================================================

theorem nearIntegrand_f (G : ClosedGeom) (f g : L2Test) (k : Nat) (x : Real) :
    (nearIntegrand G f g k).f x
      = Rmul ((archNum G f g).f x) (clampedInv (dyQ k) (dyQ_num k) (dyQ_den k) (Rsub x one)) := by
  unfold nearIntegrand; rfl

theorem nearJ_symm (G : ClosedGeom) (f g : L2Test) (k : Nat) :
    Req (nearJ G f g k) (nearJ G g f k) := by
  unfold nearJ
  exact riemannIntegralI_congr_unit_mod _ _ _ _ _ _ _ _ _ _ _ _ _ (fun t _ _ => by
    rw [nearIntegrand_f, nearIntegrand_f]; exact Rmul_congr (archNum_symm_pt G f g _) (Req_refl _))

theorem nearJ_add_left (G : ClosedGeom) (f₁ f₂ g : L2Test) (k : Nat) :
    Req (nearJ G (L2Test.add f₁ f₂) g k) (Radd (nearJ G f₁ g k) (nearJ G f₂ g k)) := by
  unfold nearJ
  refine Req_trans (riemannIntegralI_congr_unit_mod _ _ _ _
    (L2Test.add (nearIntegrand G f₁ g k) (nearIntegrand G f₂ g k)).hLd
    (L2Test.add (nearIntegrand G f₁ g k) (nearIntegrand G f₂ g k)).hLn
    (L2Test.add (nearIntegrand G f₁ g k) (nearIntegrand G f₂ g k)).hlip
    (L2Test.add (nearIntegrand G f₁ g k) (nearIntegrand G f₂ g k)).hfc
    (nearLo k) (nearW k) (nearLo_den k) (nearW_den k) (nearW_num k) (fun t _ _ => by
      rw [nearIntegrand_f]
      show Req _ (Radd ((nearIntegrand G f₁ g k).f _) ((nearIntegrand G f₂ g k).f _))
      rw [nearIntegrand_f, nearIntegrand_f]
      exact Req_trans (Rmul_congr (archNum_add_left_pt G f₁ f₂ g _) (Req_refl _)) (Rmul_distrib_right _ _ _))) ?_
  exact riemannIntegralI_addTest _ _ _ _ _ _ _

theorem nearJ_add_right (G : ClosedGeom) (f g₁ g₂ : L2Test) (k : Nat) :
    Req (nearJ G f (L2Test.add g₁ g₂) k) (Radd (nearJ G f g₁ k) (nearJ G f g₂ k)) := by
  unfold nearJ
  refine Req_trans (riemannIntegralI_congr_unit_mod _ _ _ _
    (L2Test.add (nearIntegrand G f g₁ k) (nearIntegrand G f g₂ k)).hLd
    (L2Test.add (nearIntegrand G f g₁ k) (nearIntegrand G f g₂ k)).hLn
    (L2Test.add (nearIntegrand G f g₁ k) (nearIntegrand G f g₂ k)).hlip
    (L2Test.add (nearIntegrand G f g₁ k) (nearIntegrand G f g₂ k)).hfc
    (nearLo k) (nearW k) (nearLo_den k) (nearW_den k) (nearW_num k) (fun t _ _ => by
      rw [nearIntegrand_f]
      show Req _ (Radd ((nearIntegrand G f g₁ k).f _) ((nearIntegrand G f g₂ k).f _))
      rw [nearIntegrand_f, nearIntegrand_f]
      exact Req_trans (Rmul_congr (archNum_add_right_pt G f g₁ g₂ _) (Req_refl _)) (Rmul_distrib_right _ _ _))) ?_
  exact riemannIntegralI_addTest _ _ _ _ _ _ _

/-- `⟨a, 2ⁿ⟩ ≤ ⟨a, n+1⟩` (rate conversion). -/
theorem rate_two_pow_to_lin (a n : Nat) :
    Qle (⟨(a : Int), 2 ^ n⟩ : Q) (⟨(a : Int), n + 1⟩ : Q) :=
  q_den_mono a n n (succ_le_two_pow_of_le n n (Nat.le_refl n))

/-- **`ArchNearPart_symm`** — through the common truncations and the two rates. -/
theorem ArchNearPart_symm (G : ClosedGeom) (f g : L2Test) :
    Req (ArchNearPart G f g) (ArchNearPart G g f) := by
  refine Req_of_Rabs_le_lin (nearCN G f g + nearCN G g f) (fun n => ?_)
  refine Rle_trans (Rabs_sub_tri _ (nearJ G f g n) _) ?_
  refine Rle_trans (Radd_le_add (Rle_trans (Rle_of_Req (Rabs_Rsub_symm _ _)) (nearJ_limit_rate G f g n))
    (Rle_trans (Rle_of_Req (Rabs_congr (Rsub_congr (nearJ_symm G f g n) (Req_refl _))))
      (nearJ_limit_rate G g f n))) ?_
  refine Rle_trans (Rle_of_Req (Radd_ofQ_ofQ _ _)) ?_
  refine Rle_ofQ_ofQ _ (Nat.succ_pos n) ?_
  exact Qle_trans (Nat.two_pow_pos n) (Qeq_le (q_add_same_den _ _ n)) (rate_two_pow_to_lin _ n)

/-- Abstract: `|X − (Y₁ + Y₂)| ≤ |X − J| + |J₁ − Y₁| + |J₂ − Y₂|` when `J = J₁ + J₂`. -/
theorem near_add_tri (X Y₁ Y₂ J J₁ J₂ : Real) (hJ : Req J (Radd J₁ J₂)) :
    Rle (Rabs (Rsub X (Radd Y₁ Y₂)))
        (Radd (Rabs (Rsub X J)) (Radd (Rabs (Rsub J₁ Y₁)) (Rabs (Rsub J₂ Y₂)))) := by
  refine Rle_trans (Rabs_sub_tri _ J _) ?_
  refine Radd_le_add (Rle_refl _) ?_
  refine Rle_trans (Rle_of_Req (Rabs_congr (Rsub_congr hJ (Req_refl _)))) ?_
  -- (J₁ + J₂) − (Y₁ + Y₂) = (J₁ − Y₁) + (J₂ − Y₂)
  refine Rle_trans (Rle_of_Req (Rabs_congr (Req_trans (Radd_congr (Req_refl _) (Rneg_Radd _ _))
    (Radd_add_add_comm _ _ _ _)))) ?_
  exact Rabs_Radd _ _

theorem ArchNearPart_add_left (G : ClosedGeom) (f₁ f₂ g : L2Test) :
    Req (ArchNearPart G (L2Test.add f₁ f₂) g) (Radd (ArchNearPart G f₁ g) (ArchNearPart G f₂ g)) := by
  refine Req_of_Rabs_le_lin (nearCN G (L2Test.add f₁ f₂) g + (nearCN G f₁ g + nearCN G f₂ g)) (fun n => ?_)
  refine Rle_trans (near_add_tri _ _ _ _ _ _ (nearJ_add_left G f₁ f₂ g n)) ?_
  refine Rle_trans (Radd_le_add (Rle_trans (Rle_of_Req (Rabs_Rsub_symm _ _)) (nearJ_limit_rate G _ g n))
    (Radd_le_add (nearJ_limit_rate G f₁ g n) (nearJ_limit_rate G f₂ g n))) ?_
  refine Rle_trans (Rle_of_Req (Radd_congr (Req_refl _) (Radd_ofQ_ofQ _ _))) ?_
  refine Rle_trans (Rle_of_Req (Radd_congr (Req_refl _) (ofQ_congr (add_den_pos (Nat.two_pow_pos n) (Nat.two_pow_pos n))
    (Nat.two_pow_pos n) (q_add_same_den _ _ n)))) ?_
  refine Rle_trans (Rle_of_Req (Radd_ofQ_ofQ _ _)) ?_
  refine Rle_ofQ_ofQ _ (Nat.succ_pos n) ?_
  exact Qle_trans (Nat.two_pow_pos n) (Qeq_le (q_add_same_den _ _ n)) (rate_two_pow_to_lin _ n)

theorem ArchNearPart_add_right (G : ClosedGeom) (f g₁ g₂ : L2Test) :
    Req (ArchNearPart G f (L2Test.add g₁ g₂)) (Radd (ArchNearPart G f g₁) (ArchNearPart G f g₂)) := by
  refine Req_of_Rabs_le_lin (nearCN G f (L2Test.add g₁ g₂) + (nearCN G f g₁ + nearCN G f g₂)) (fun n => ?_)
  refine Rle_trans (near_add_tri _ _ _ _ _ _ (nearJ_add_right G f g₁ g₂ n)) ?_
  refine Rle_trans (Radd_le_add (Rle_trans (Rle_of_Req (Rabs_Rsub_symm _ _)) (nearJ_limit_rate G f _ n))
    (Radd_le_add (nearJ_limit_rate G f g₁ n) (nearJ_limit_rate G f g₂ n))) ?_
  refine Rle_trans (Rle_of_Req (Radd_congr (Req_refl _) (Radd_ofQ_ofQ _ _))) ?_
  refine Rle_trans (Rle_of_Req (Radd_congr (Req_refl _) (ofQ_congr (add_den_pos (Nat.two_pow_pos n) (Nat.two_pow_pos n))
    (Nat.two_pow_pos n) (q_add_same_den _ _ n)))) ?_
  refine Rle_trans (Rle_of_Req (Radd_ofQ_ofQ _ _)) ?_
  refine Rle_ofQ_ofQ _ (Nat.succ_pos n) ?_
  exact Qle_trans (Nat.two_pow_pos n) (Qeq_le (q_add_same_den _ _ n)) (rate_two_pow_to_lin _ n)

-- ===========================================================================
-- (4) THE ARCHIMEDEAN-TAIL LAWS.
-- ===========================================================================

/-- Abstract: `½((R₁+R₂) + ((N₁+N₂) + (F₁+F₂))) = ½(R₁ + (N₁+F₁)) + ½(R₂ + (N₂+F₂))`. -/
theorem tail_add_alg (R₁ R₂ N₁ N₂ F₁ F₂ : Real) :
    Req (Rmul (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1)) (Radd (Radd R₁ R₂) (Radd (Radd N₁ N₂) (Radd F₁ F₂))))
        (Radd (Rmul (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1)) (Radd R₁ (Radd N₁ F₁)))
              (Rmul (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1)) (Radd R₂ (Radd N₂ F₂)))) := by
  refine Req_trans ?_ (Rmul_distrib _ _ _)
  refine Rmul_congr (Req_refl _) ?_
  refine Req_trans (Radd_congr (Req_refl _) (Radd_add_add_comm _ _ _ _)) ?_
  exact Radd_add_add_comm _ _ _ _

theorem ArchTailForm_symm (G : ClosedGeom) (f g : L2Test) (hf : CoreTest G f) (hg : CoreTest G g) :
    Req (ArchTailForm G f g hf hg) (ArchTailForm G g f hg hf) :=
  Rmul_congr (Req_refl _) (Radd_congr (ArchRegPart_symm G f g hf hg)
    (Radd_congr (ArchNearPart_symm G f g) (ArchFarPart_symm G f g hf hg)))

theorem ArchTailForm_add_left (G : ClosedGeom) (f₁ f₂ g : L2Test) (h₁ : CoreTest G f₁) (h₂ : CoreTest G f₂)
    (hg : CoreTest G g) :
    Req (ArchTailForm G (L2Test.add f₁ f₂) g (coreTest_add h₁ h₂) hg)
        (Radd (ArchTailForm G f₁ g h₁ hg) (ArchTailForm G f₂ g h₂ hg)) :=
  Req_trans (Rmul_congr (Req_refl _) (Radd_congr (ArchRegPart_add_left G f₁ f₂ g h₁ h₂ hg)
    (Radd_congr (ArchNearPart_add_left G f₁ f₂ g) (ArchFarPart_add_left G f₁ f₂ g h₁ h₂ hg))))
    (tail_add_alg _ _ _ _ _ _)

theorem ArchTailForm_add_right (G : ClosedGeom) (f g₁ g₂ : L2Test) (hf : CoreTest G f) (h₁ : CoreTest G g₁)
    (h₂ : CoreTest G g₂) :
    Req (ArchTailForm G f (L2Test.add g₁ g₂) hf (coreTest_add h₁ h₂))
        (Radd (ArchTailForm G f g₁ hf h₁) (ArchTailForm G f g₂ hf h₂)) :=
  Req_trans (Rmul_congr (Req_refl _) (Radd_congr (ArchRegPart_add_right G f g₁ g₂ hf h₁ h₂)
    (Radd_congr (ArchNearPart_add_right G f g₁ g₂) (ArchFarPart_add_right G f g₁ g₂ hf h₁ h₂))))
    (tail_add_alg _ _ _ _ _ _)

end UOR.Bridge.F1Square.Square
