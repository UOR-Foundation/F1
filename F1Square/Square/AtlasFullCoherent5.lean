/-
F1 square — **THE FULL SOURCE-COHERENT CARRIER** (`AtlasFullCoherent5.lean`, target-free).

`FullSourceCoherent5 C k z` is the conjunction, as PROPOSITIONS about a five-channel cut carrier element `z`,
of every source and channel law the signed matrix consumes — stated on the recovered fields
`U^{rec} = recUF z`, `V^{rec} = recVF z` (pole/tail ports), `V^{far} = recVFarF z` (far port), and the orbit
reading `readHaar`:

  1. pole/tail RESYNTHESIS from the recovered source on the measured supports;
  2. prime-cut consistency with the recovered `U_n` (orbit reading) and `V`;
  3. constant cut `= 0`;
  4. the far-coordinate law: the far port is constant in the scale (the far `x`-port collapses isometrically);
  5. anchor agreement `V^{rec} = V^{far}` on the band;
  6. multiplicative-orbit covariance of `U^{rec}`;
  7. the piecewise law `U^{rec}_x(t) = x^{-1/2}·V^{far}(t/x)` on its active support `t ≥ a·x`;
  8. support-forced zero rows `U^{rec}_q(t) = 0` at rational scales `1 ≤ q ≤ B`, `t ≤ a·q`.

It is NOT defined as the range of `cutAnalysis5`; `cutAnalysis5_fullCoherent` proves that every core analysis
inhabits it (laws 1–7 for every test, law 8 from the core support).  No bound, no sign.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasColligation5
import F1Square.Square.AtlasSourceLaws

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis
open CField

/-- **★ THE FULL SOURCE-COHERENT CARRIER.** -/
structure FullSourceCoherent5 (C : NormCtx) (k : Nat) (z : Carrier5) : Prop where
  /-- (1a) pole resynthesis `A_pole = (U^{rec} + V^{far})/4` on `[1,B] × [a,a+w]`. -/
  pole_syn : ∀ x t, Rle one x → Rle x (ofQ (canonB C) (canonB_den C)) → InWin C t →
    Req (z.pole.F x t) (aCoefGa one ((recUF C k z).F x t) (Rneg ((recVFarF z).F x t)))
  /-- (1b) tail resynthesis `A_tail = (Z^{rec} − W^{rec})/4` on `[1+2^{-k},B] × [a,a+w]`. -/
  tail_syn : ∀ x t, Rle (ofQ (tailLo k) (tailLo_den k)) x → Rle x (ofQ (canonB C) (canonB_den C)) → InWin C t →
    Req (z.tail.F x t) (aCoefGa one ((ZrecF C k z).F x t) ((WrecF C k z).F x t))
  /-- (2) prime-cut consistency `A_prime,m = (U_n − V)/4` with the orbit reading, at the active places. -/
  prime_syn : ∀ m (hm : m < C.X) x t, InWin C t →
    Req ((z.prime m).F x t) (aCoefGa one ((readHaar C k m hm z).F x t) ((recVFarF z).F x t))
  /-- (3) the constant cut coordinate vanishes. -/
  const_zero : ∀ x t, InWin C t → Req (z.const.F x t) zero
  /-- (4) the far port is constant in the scale (the far `x`-port collapse). -/
  far_const : ∀ x x' t, Req (z.far.F x t) (z.far.F x' t)
  /-- (5) anchor agreement on the band. -/
  anchor : ∀ x t, Rle one x → Rle x (ofQ (canonB C) (canonB_den C)) → InWin C t →
    Req ((recVF C k z).F x t) ((recVFarF z).F x t)
  /-- (6) multiplicative-orbit covariance of the recovered `U`: `x'·s = x·t ⟹ invSq(x')·U_x(s) = invSq(x)·U_{x'}(t)`. -/
  orbit : ∀ x x' s t, Rle one x → Rle x (ofQ (canonB C) (canonB_den C)) → Rle one x' → Rle x' (ofQ (canonB C) (canonB_den C)) →
    Rle (ofQ C.a C.had) s → Rle (ofQ C.a C.had) t → Req (Rmul x' s) (Rmul x t) →
    Req (Rmul (invSq C x') ((recUF C k z).F x s)) (Rmul (invSq C x) ((recUF C k z).F x' t))
  /-- (7) the piecewise law `U_x(t) = x^{-1/2}·V(t/x)` on the active support `t ≥ a·x`. -/
  shift : ∀ x t, Rle one x → Rle x (ofQ (canonB C) (canonB_den C)) → ∀ (kx : Nat) (hkx : Qlt (Qbound kx) (x.seq kx)),
    Rle (Rmul (ofQ C.a C.had) x) t →
    Req ((recUF C k z).F x t) (Rmul (invSq C x) ((recVFarF z).F one (Rmul t (Rinv x kx hkx))))
  /-- (8) support-forced zero rows at rational scales. -/
  zero_row : ∀ (q : Q) (hqd : 0 < q.den), Qle (⟨1, 1⟩ : Q) q → Qle q (canonB C) → ∀ t,
    Rle t (ofQ (mul C.a q) (Qmul_den_pos C.had hqd)) → Req ((recUF C k z).F (ofQ q hqd) t) zero

theorem xcl_inert_band (C : NormCtx) {x : Real} (h1 : Rle one x) (hB : Rle x (ofQ (canonB C) (canonB_den C))) :
    Req (xcl C x) x := xcl_eq_of_band C h1 hB

/-- `U^{rec}(A_k f)(x,t) = U_x(f,t)` on the band. -/
theorem recUF_source_band (C : NormCtx) (k : Nat) (f : L2Test) {x : Real} (h1 : Rle one x)
    (hB : Rle x (ofQ (canonB C) (canonB_den C))) (t : Real) :
    Req ((recUF C k (cutAnalysis5 C k f)).F x t) (Uc C x f t) :=
  Req_trans (recUF_source C k f x t) (Uc_congr_x C (xcl_inert_band C h1 hB) f t)

theorem B_le_S_R (C : NormCtx) : Rle (ofQ (canonB C) (canonB_den C)) (ofQ C.S C.hSd) := Rle_ofQ_ofQ _ _ (canonB_le_S C)
theorem zero_le_of_one_le_R {x : Real} (h : Rle one x) : Rle zero x := Rle_trans (Rle_zero_of_Rnonneg Rnonneg_one) h

/-- **★ EVERY CORE ANALYSIS IS FULLY SOURCE-COHERENT.** -/
theorem cutAnalysis5_fullCoherent (C : NormCtx) (k : Nat) (f : L2Test) (hf : CoreTest C.geom f) :
    FullSourceCoherent5 C k (cutAnalysis5 C k f) where
  pole_syn := fun x t h1 hB _ => by
    rw [cutAnalysis5_pole]
    exact aCoefGa_congr (Req_symm (recUF_source_band C k f h1 hB t)) (Rneg_congr (Req_symm (recVFarF_source C k f x t)))
  tail_syn := fun x t _ _ _ => by
    rw [cutAnalysis5_tail, ZrecF_F, WrecF_F]
    refine aCoefGa_congr ?_ ?_
    · exact Rmul_congr (Req_refl _) (Rsub_congr (Req_symm (recUF_source C k f x t))
        (Rmul_congr (Req_refl _) (Req_symm (recVF_source C k f x t))))
    · exact Rmul_congr (Req_refl _) (Req_symm (recVF_source C k f x t))
  prime_syn := fun m hm x t ht => by
    rw [cutAnalysis5_prime]
    exact aCoefGa_congr (Req_symm (readHaar_source C k m hm f x t ht.1 ht.2)) (Req_symm (recVFarF_source C k f x t))
  const_zero := fun x t _ => by rw [cutAnalysis5_const]; exact negFiber_VV_cut_zero _
  far_const := fun _ _ _ => Req_refl _
  anchor := fun x t _ _ _ => Req_trans (recVF_source C k f x t) (Req_symm (recVFarF_source C k f x t))
  orbit := fun x x' s t h1 hB h1' hB' hs ht horb => by
    refine Req_trans (Rmul_congr (Req_refl _) (recUF_source_band C k f h1 hB s)) ?_
    refine Req_trans ?_ (Rmul_congr (Req_refl _) (Req_symm (recUF_source_band C k f h1' hB' t)))
    exact Uc_orbit C f (zero_le_of_one_le_R h1) (Rle_trans hB (B_le_S_R C)) (zero_le_of_one_le_R h1') (Rle_trans hB' (B_le_S_R C))
      hs ht horb
  shift := fun x t h1 hB kx hkx hax => by
    refine Req_trans (recUF_source_band C k f h1 hB t) ?_
    refine Req_trans (Uc_eq_invSq_Vc_shift C f h1 (Rle_trans hB (B_le_S_R C)) hkx hax) ?_
    exact Rmul_congr (Req_refl _) (Req_symm (recVFarF_source C k f one _))
  zero_row := fun q hqd hq1 hqB t ht => by
    have h1 : Rle one (ofQ q hqd) := Rle_ofQ_ofQ (by decide) hqd hq1
    have hB : Rle (ofQ q hqd) (ofQ (canonB C) (canonB_den C)) := Rle_ofQ_ofQ hqd (canonB_den C) hqB
    refine Req_trans (recUF_source_band C k f h1 hB t) ?_
    exact Uc_zero_row C f hf q hqd hq1 (Qle_trans (canonB_den C) hqB (canonB_le_S C)) ht

/-- **The far `x`-port collapse**: for a fully coherent element every routed use of the far anchor at any scale
    equals its value at the scale `1` — the collapsed far Gram `farG` (evaluated at `x = 1`) loses nothing. -/
theorem far_port_collapse (C : NormCtx) (k : Nat) {z : Carrier5} (hz : FullSourceCoherent5 C k z) (x t : Real) :
    Req ((recVFarF z).F x t) ((recVFarF z).F one t) :=
  Rmul_congr (Req_refl _) (hz.far_const x one t)

/-- Full coherence contains the AC-27 coherence (anchor agreement and orbit invariance of the reading). -/
theorem fullCoherent_anchor (C : NormCtx) (k : Nat) {z : Carrier5} (hz : FullSourceCoherent5 C k z) :
    ∀ x t, Rle one x → Rle x (ofQ (canonB C) (canonB_den C)) → InWin C t → Req ((recVF C k z).F x t) ((recVFarF z).F x t) :=
  hz.anchor

end UOR.Bridge.F1Square.Square
