/-
F1 square — **THE MEASURED SOURCE-COHERENT CARRIER** (`AtlasCoherent5.lean`, target-free).

`SourceCoherent5 C k z` is the conjunction of the two laws of the CUT carrier that the signed five-channel matrix
consumes, stated as PROPOSITIONS about an arbitrary carrier element `z` (no field of any structure asserts them):

 * ANCHOR AGREEMENT on the band: the anchor `V` recovered from the pole and compact-tail cut fields
   (`recVF`, the AC-26 inversion) agrees with the far copy `2·A_far` (`recVFarF`) at every `(x,t)` with
   `1 ≤ x ≤ B`, `t ∈ [a, a+w]`;
 * THE ORBIT LAW of the cut-only reading: for every place `n = m+1 ≤ X` and `t ∈ [a, a+w]`, the reading integrand
   `readF(x,t)` of the prime channel, divided by the Haar weight `1/max(x̄,1)`, does not depend on the scale
   `x ≥ n` — in the cross-multiplied form `r(x̄')·readF(x,t) = r(x̄)·readF(x',t)`.

THEOREMS.  `cutAnalysis5_coherent`: the cut analysis of EVERY test is coherent (from `recVF_source`,
`recVFarF_source`, `readF_source`).  `readAt` is the reading at one window scale, `readAt_source` says it is
`U_n(f,t)` on every analysis, and `readHaar_eq_of_coherent`: on a coherent carrier element the normalized Haar
average `readHaar` EQUALS the reading `readAt` at every window scale — the Haar transport weight is not
semantic data of a coherent element.  `coherent_bound_imp_defect`: a contraction bound of the matrix on the
coherent carrier forces the defect sign of every test (via the range).  No sign is asserted.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasColligation5

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis
open CField

-- ===========================================================================
-- (1) The two laws, as propositions about a carrier element.
-- ===========================================================================

/-- **The measured source-coherent carrier**: anchor agreement on the band and the orbit law of the reading. -/
structure SourceCoherent5 (C : NormCtx) (k : Nat) (z : Carrier5) : Prop where
  anchor : ∀ x t, Rle one x → Rle x (ofQ (canonB C) (canonB_den C)) → InWin C t →
    Req ((recVF C k z).F x t) ((recVFarF z).F x t)
  orbit : ∀ m, m < C.X → ∀ t, InWin C t → ∀ x x', Rle (upR m) (xcl C x) → Rle (upR m) (xcl C x') →
    Req (Rmul (rOne (xcl C x')) ((readF C k m z).F x t)) (Rmul (rOne (xcl C x)) ((readF C k m z).F x' t))

/-- **★ THE CUT ANALYSIS OF EVERY TEST IS COHERENT.** -/
theorem cutAnalysis5_coherent (C : NormCtx) (k : Nat) (f : L2Test) : SourceCoherent5 C k (cutAnalysis5 C k f) where
  anchor := fun x t _ _ _ => Req_trans (recVF_source C k f x t) (Req_symm (recVFarF_source C k f x t))
  orbit := by
    intro m hm t ht x x' hx hx'
    have h1 := readF_source C k m hm f x t hx ht.1 ht.2
    have h2 := readF_source C k m hm f x' t hx' ht.1 ht.2
    refine Req_trans (Rmul_congr (Req_refl _) h1) (Req_trans (swap_w_ac _ _ _) (Rmul_congr (Req_refl _) (Req_symm h2)))

-- ===========================================================================
-- (2) The reading at one window scale, and the Haar average of a coherent element.
-- ===========================================================================

theorem rOneClF_F (C : NormCtx) (x t : Real) : (rOneClF C).F x t = rOne (xcl C x) := rfl

/-- **The reading at the window scale `x`**: `x̄·readF(x,t)` (the integrand divided by its Haar weight `1/x̄`). -/
def readAt (C : NormCtx) (k m : Nat) (z : Carrier5) (x t : Real) : Real := Rmul (xcl C x) ((readF C k m z).F x t)

/-- `x̄·(1/max(x̄,1)) = 1`. -/
theorem xcl_mul_rOne (C : NormCtx) (x : Real) : Req (Rmul (xcl C x) (rOne (xcl C x))) one :=
  Rmul_clampedInv_one (xcl C x) (xcl_ge_one C x)

/-- **On every analysis the reading at any window scale is `U_n(f,t)`.** -/
theorem readAt_source (C : NormCtx) (k m : Nat) (hm : m < C.X) (f : L2Test) (x t : Real)
    (hxn : Rle (upR m) (xcl C x)) (ht : InWin C t) :
    Req (readAt C k m (cutAnalysis5 C k f) x t) (Uc C (upR m) f t) := by
  unfold readAt
  refine Req_trans (Rmul_congr (Req_refl _) (readF_source C k m hm f x t hxn ht.1 ht.2)) ?_
  exact Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Rmul_congr (xcl_mul_rOne C x) (Req_refl _)) (Rone_mul _))

/-- On a coherent element the integrand at a window scale `x'` is `readAt(x)·r(x̄')` for every `x` with `x̄ ≥ n`. -/
theorem readF_of_coherent (C : NormCtx) (k : Nat) {z : Carrier5} (hz : SourceCoherent5 C k z) (m : Nat) (hm : m < C.X)
    {t : Real} (ht : InWin C t) {x x' : Real} (hx : Rle (upR m) (xcl C x)) (hx' : Rle (upR m) (xcl C x')) :
    Req ((readF C k m z).F x' t) (Rmul (readAt C k m z x t) (rOne (xcl C x'))) := by
  have horb := hz.orbit m hm t ht x x' hx hx'
  unfold readAt
  -- F(x') ≈ (x̄·r(x̄))·F(x') ≈ x̄·(r(x̄)·F(x')) ≈ x̄·(r(x̄')·F(x)) ≈ x̄·(F(x)·r(x̄')) ≈ (x̄·F(x))·r(x̄')
  refine Req_trans (Req_symm (Rone_mul _)) (Req_trans (Rmul_congr (Req_symm (xcl_mul_rOne C x)) (Req_refl _)) ?_)
  refine Req_trans (Rmul_assoc _ _ _) (Req_trans (Rmul_congr (Req_refl _) (Req_symm horb)) ?_)
  exact Req_trans (Rmul_congr (Req_refl _) (Rmul_comm _ _)) (Req_symm (Rmul_assoc _ _ _))

/-- **★ THE HAAR AVERAGE OF A COHERENT ELEMENT IS THE READING AT ANY WINDOW SCALE**: for `SourceCoherent5 z`,
    `readHaar(z)(t) = readAt(z)(x,t)` whenever `x̄ ≥ n` and `t ∈ [a, a+w]` — the transport weight `dx/max(x̄,1)`
    over `[n,B]` is not semantic data of a coherent element. -/
theorem readHaar_eq_of_coherent (C : NormCtx) (k : Nat) {z : Carrier5} (hz : SourceCoherent5 C k z) (m : Nat) (hm : m < C.X)
    {t : Real} (ht : InWin C t) {x : Real} (hx : Rle (upR m) (xcl C x)) (x₀ : Real) :
    Req ((readHaar C k m hm z).F x₀ t) (readAt C k m z x t) := by
  rw [readHaar_F]
  have hpt : ∀ s, Rle zero s → Rle s one →
      Req ((readF C k m z).F (affineMap (upQ m) (wnQ C m) Nat.one_pos Nat.one_pos s) t)
          (Rmul (readAt C k m z x t) ((rOneClF C).F (affineMap (upQ m) (wnQ C m) Nat.one_pos Nat.one_pos s) one)) :=
    fun s hs0 hs1 => by
      rw [rOneClF_F]
      exact readF_of_coherent C k hz m hm ht hx (win_xcl_ge_n C m hm s hs0 hs1)
  have hI := xInt_congr_smul (readF C k m z) (rOneClF C) (upQ m) (wnQ C m) Nat.one_pos Nat.one_pos (wnQ_num C m)
    (readAt C k m z x t) t one hpt
  have hmul := hMassInv_mul C m hm
  unfold hMass at hmul hI
  refine Req_trans (Rmul_congr (Req_refl _) hI) ?_
  generalize readAt C k m z x t = R at *
  generalize xInt (rOneClF C) (upQ m) (wnQ C m) Nat.one_pos Nat.one_pos (wnQ_num C m) one = M at *
  generalize hMassInv C m hm = I at *
  -- I·(R·M) ≈ (I·R)·M ≈ (R·I)·M ≈ R·(I·M) ≈ R·(M·I) ≈ R·1 ≈ R
  refine Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Rmul_congr (Rmul_comm _ _) (Req_refl _)) (Req_trans (Rmul_assoc _ _ _) ?_))
  exact Req_trans (Rmul_congr (Req_refl _) (Req_trans (Rmul_comm _ _) hmul)) (Rmul_one _)

-- ===========================================================================
-- (3) A bound on the coherent carrier is at least the defect sign of every test.
-- ===========================================================================

/-- **The range is inside the coherent carrier**, so a contraction bound of the matrix on `SourceCoherent5`
    forces `energy5(A_k f) − energy5(B_k f) ≥ 0` for every test `f` — the bound on the coherent carrier is at
    least the crux (`defect_k(f,f) + far_k(f,f) ≥ 0`), never weaker. -/
theorem coherent_bound_imp_defect (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (fc : Real)
    (hbd : ∀ z, SourceCoherent5 C k z → Rle (energy5 C k hk fc (atlasMatrix C k z)) (energy5 C k hk fc z)) (f : L2Test) :
    Rnonneg (Rsub (energy5 C k hk fc (cutAnalysis5 C k f)) (energy5 C k hk fc (cycleAnalysis5 C k f))) :=
  (atlasMatrix_range_bound_iff C k hk fc f).1 (hbd _ (cutAnalysis5_coherent C k f))

end UOR.Bridge.F1Square.Square
