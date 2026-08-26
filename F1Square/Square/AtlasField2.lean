/-
F1 square — **certified two-variable fields and their channel integrals** (`AtlasField2.lean`, target-free).

A `CField` is a function `(x,t) ↦ F x t` of the scale `x` and the Haar coordinate `t` with GLOBAL rational
certificates: a Lipschitz modulus in `x` uniform in `t`, a Lipschitz modulus in `t` uniform in `x`, a bound,
and the two congruences.  Products, sums, negations, scalar multiples, and compositions with certified maps
are again `CField`s (the constants are the sourced ones of `Rmul_lipschitz`, `lip_add_fl`,
`lip_const_mul_left`).  The two integrals every channel of the five-channel carrier uses are

    `intT z x  = ∫₀¹ z(x, a + w·y) dy`          (the Haar integral at scale `x`, certified in `x` by
                                                 `param_integral_lip` from the uniform `x`-modulus),
    `intX z lo w = ∫_{[lo, lo+w]} intT z x dx`  (the scale integral of the Haar integral).

The plumbing lemmas at the end (`intU_*`, `intI_*`) let pointwise identities of integrands pass through the
integrals with INDEPENDENT certificates (each integral keeps its own sourced modulus): congruence,
difference, real scalar, zero, and agreement on the window only.  Nothing here is a sign claim.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasArchGram

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- (0) Finite sums (local, no target import).
-- ===========================================================================

theorem RsumN_add_f2 (F G : Nat → Real) : ∀ N,
    Req (RsumN (fun i => Radd (F i) (G i)) N) (Radd (RsumN F N) (RsumN G N))
  | 0 => by rw [RsumN_zero_fl, RsumN_zero_fl, RsumN_zero_fl]; exact Req_symm (Radd_zero zero)
  | (n + 1) => by
      rw [RsumN_succ_fl, RsumN_succ_fl, RsumN_succ_fl]
      refine Req_trans (Radd_congr (RsumN_add_f2 F G n) (Req_refl _)) ?_
      -- (A + B) + (a + b) ≈ (A + a) + (B + b)
      refine Req_trans (Radd_assoc _ _ _) (Req_trans (Radd_congr (Req_refl _) ?_) (Req_symm (Radd_assoc _ _ _)))
      refine Req_trans (Req_symm (Radd_assoc _ _ _)) (Req_trans (Radd_congr (Radd_comm _ _) (Req_refl _)) (Radd_assoc _ _ _))

theorem RsumN_neg_f2 (F : Nat → Real) : ∀ N, Req (RsumN (fun i => Rneg (F i)) N) (Rneg (RsumN F N))
  | 0 => by
      rw [RsumN_zero_fl, RsumN_zero_fl]
      exact Req_symm (Req_trans (Req_symm (Radd_zero (Rneg zero))) (Req_trans (Radd_comm _ _) (Radd_neg zero)))
  | (n + 1) => by
      rw [RsumN_succ_fl, RsumN_succ_fl]
      exact Req_trans (Radd_congr (RsumN_neg_f2 F n) (Req_refl _)) (Req_symm (Rneg_Radd _ _))

theorem RsumN_sub_f2 (F G : Nat → Real) (N : Nat) :
    Req (RsumN (fun i => Rsub (F i) (G i)) N) (Rsub (RsumN F N) (RsumN G N)) :=
  Req_trans (RsumN_add_f2 F (fun i => Rneg (G i)) N) (Radd_congr (Req_refl _) (RsumN_neg_f2 G N))

-- ===========================================================================
-- (1) Certified two-variable fields.
-- ===========================================================================

/-- **A certified field** `(x,t) ↦ F x t`: uniform Lipschitz moduli in each variable, a bound, congruences. -/
structure CField where
  F : Real → Real → Real
  Lx : Q
  Lt : Q
  M : Q
  hLxd : 0 < Lx.den
  hLxn : 0 ≤ Lx.num
  hLtd : 0 < Lt.den
  hLtn : 0 ≤ Lt.num
  hMd : 0 < M.den
  hMn : 0 ≤ M.num
  hlipx : ∀ t x x', Rle (Rabs (Rsub (F x t) (F x' t))) (Rmul (ofQ Lx hLxd) (Rabs (Rsub x x')))
  hlipt : ∀ x t t', Rle (Rabs (Rsub (F x t) (F x t'))) (Rmul (ofQ Lt hLtd) (Rabs (Rsub t t')))
  hbd : ∀ x t, Rle (Rabs (F x t)) (ofQ M hMd)
  hfcx : ∀ {x x' : Real} (t : Real), Req x x' → Req (F x t) (F x' t)
  hfct : ∀ (x : Real) {t t' : Real}, Req t t' → Req (F x t) (F x t')

/-- The joint congruence of a certified field. -/
theorem cfield_fc (z : CField) {x x' t t' : Real} (hx : Req x x') (ht : Req t t') : Req (z.F x t) (z.F x' t') :=
  Req_trans (z.hfcx t hx) (z.hfct x' ht)

/-- A rational scalar `q ≥ 0` as a certified bound of itself. -/
theorem abs_ofQ_le {q : Q} (hqd : 0 < q.den) (hqn : 0 ≤ q.num) : Rle (Rabs (ofQ q hqd)) (ofQ q hqd) :=
  Rle_of_Req (Rabs_ofQ_nonneg hqd hqn)

namespace CField

/-- The product field. -/
def mulF (u v : CField) : CField where
  F := fun x t => Rmul (u.F x t) (v.F x t)
  Lx := add (mul u.M v.Lx) (mul v.M u.Lx)
  Lt := add (mul u.M v.Lt) (mul v.M u.Lt)
  M := mul u.M v.M
  hLxd := add_den_pos (Qmul_den_pos u.hMd v.hLxd) (Qmul_den_pos v.hMd u.hLxd)
  hLxn := Qadd_num_nonneg_loc (Qmul_num_nonneg u.hMn v.hLxn) (Qmul_num_nonneg v.hMn u.hLxn)
  hLtd := add_den_pos (Qmul_den_pos u.hMd v.hLtd) (Qmul_den_pos v.hMd u.hLtd)
  hLtn := Qadd_num_nonneg_loc (Qmul_num_nonneg u.hMn v.hLtn) (Qmul_num_nonneg v.hMn u.hLtn)
  hMd := Qmul_den_pos u.hMd v.hMd
  hMn := Qmul_num_nonneg u.hMn v.hMn
  hlipx := fun t x x' => Rmul_lipschitz (f := fun x => u.F x t) (g := fun x => v.F x t)
    u.hLxd v.hLxd u.hMd v.hMd u.hLxn v.hLxn u.hMn v.hMn (u.hlipx t) (v.hlipx t) (fun x => u.hbd x t) (fun x => v.hbd x t) x x'
  hlipt := fun x t t' => Rmul_lipschitz (f := fun t => u.F x t) (g := fun t => v.F x t)
    u.hLtd v.hLtd u.hMd v.hMd u.hLtn v.hLtn u.hMn v.hMn (u.hlipt x) (v.hlipt x) (u.hbd x) (v.hbd x) t t'
  hbd := fun x t => abs_mul_bd u.hMd v.hMd v.hMn (u.hbd x t) (v.hbd x t)
  hfcx := @fun _ _ t h => Rmul_congr (u.hfcx t h) (v.hfcx t h)
  hfct := @fun x _ _ h => Rmul_congr (u.hfct x h) (v.hfct x h)

/-- The sum field. -/
def addF (u v : CField) : CField where
  F := fun x t => Radd (u.F x t) (v.F x t)
  Lx := add u.Lx v.Lx
  Lt := add u.Lt v.Lt
  M := add u.M v.M
  hLxd := add_den_pos u.hLxd v.hLxd
  hLxn := Qadd_num_nonneg_loc u.hLxn v.hLxn
  hLtd := add_den_pos u.hLtd v.hLtd
  hLtn := Qadd_num_nonneg_loc u.hLtn v.hLtn
  hMd := add_den_pos u.hMd v.hMd
  hMn := Qadd_num_nonneg_loc u.hMn v.hMn
  hlipx := fun t x x' => lip_add_fl (f := fun x => u.F x t) (g := fun x => v.F x t) u.hLxd v.hLxd (u.hlipx t) (v.hlipx t) x x'
  hlipt := fun x t t' => lip_add_fl (f := fun t => u.F x t) (g := fun t => v.F x t) u.hLtd v.hLtd (u.hlipt x) (v.hlipt x) t t'
  hbd := fun x t => abs_add_bd u.hMd v.hMd (u.hbd x t) (v.hbd x t)
  hfcx := @fun _ _ t h => Radd_congr (u.hfcx t h) (v.hfcx t h)
  hfct := @fun x _ _ h => Radd_congr (u.hfct x h) (v.hfct x h)

/-- The negated field. -/
def negF (u : CField) : CField where
  F := fun x t => Rneg (u.F x t)
  Lx := u.Lx
  Lt := u.Lt
  M := u.M
  hLxd := u.hLxd
  hLxn := u.hLxn
  hLtd := u.hLtd
  hLtn := u.hLtn
  hMd := u.hMd
  hMn := u.hMn
  hlipx := fun t x x' => lip_neg_pi (F := fun x => u.F x t) u.hLxd (u.hlipx t) x x'
  hlipt := fun x t t' => lip_neg_pi (F := fun t => u.F x t) u.hLtd (u.hlipt x) t t'
  hbd := fun x t => Rle_trans (Rle_of_Req (Rabs_Rneg _)) (u.hbd x t)
  hfcx := @fun _ _ t h => Rneg_congr (u.hfcx t h)
  hfct := @fun x _ _ h => Rneg_congr (u.hfct x h)

/-- The difference field `u − v`. -/
def subF (u v : CField) : CField := addF u (negF v)

/-- A real scalar multiple `c·u` with a certified bound `|c| ≤ Mc`. -/
def smulF (c : Real) {Mc : Q} (hMcd : 0 < Mc.den) (hMcn : 0 ≤ Mc.num) (hc : Rle (Rabs c) (ofQ Mc hMcd)) (u : CField) : CField where
  F := fun x t => Rmul c (u.F x t)
  Lx := mul Mc u.Lx
  Lt := mul Mc u.Lt
  M := mul Mc u.M
  hLxd := Qmul_den_pos hMcd u.hLxd
  hLxn := Qmul_num_nonneg hMcn u.hLxn
  hLtd := Qmul_den_pos hMcd u.hLtd
  hLtn := Qmul_num_nonneg hMcn u.hLtn
  hMd := Qmul_den_pos hMcd u.hMd
  hMn := Qmul_num_nonneg hMcn u.hMn
  hlipx := fun t x x' => lip_const_mul_left (F := fun x => u.F x t) u.hLxd u.hLxn (u.hlipx t) c hMcd hc x x'
  hlipt := fun x t t' => lip_const_mul_left (F := fun t => u.F x t) u.hLtd u.hLtn (u.hlipt x) c hMcd hc t t'
  hbd := fun x t => abs_mul_bd hMcd u.hMd u.hMn hc (u.hbd x t)
  hfcx := @fun _ _ t h => Rmul_congr (Req_refl c) (u.hfcx t h)
  hfct := @fun x _ _ h => Rmul_congr (Req_refl c) (u.hfct x h)

/-- The rational scalar multiple `q·u` (`q ≥ 0`). -/
def smulQF (q : Q) (hqd : 0 < q.den) (hqn : 0 ≤ q.num) (u : CField) : CField :=
  smulF (ofQ q hqd) hqd hqn (abs_ofQ_le hqd hqn) u

/-- A certified function of the scale alone. -/
def ofX (φ : Real → Real) {L M : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num) (hMd : 0 < M.den) (hMn : 0 ≤ M.num)
    (hlip : ∀ x x', Rle (Rabs (Rsub (φ x) (φ x'))) (Rmul (ofQ L hLd) (Rabs (Rsub x x'))))
    (hbd : ∀ x, Rle (Rabs (φ x)) (ofQ M hMd)) (hfc : ∀ x x', Req x x' → Req (φ x) (φ x')) : CField where
  F := fun x _ => φ x
  Lx := L
  Lt := (⟨0, 1⟩ : Q)
  M := M
  hLxd := hLd
  hLxn := hLn
  hLtd := by decide
  hLtn := by decide
  hMd := hMd
  hMn := hMn
  hlipx := fun _ x x' => hlip x x'
  hlipt := fun x t t' => const_lip0 (φ x) t t'
  hbd := fun x _ => hbd x
  hfcx := @fun _ _ _ h => hfc _ _ h
  hfct := @fun _ _ _ _ => Req_refl _

/-- A certified function of the Haar coordinate alone. -/
def ofT (ψ : Real → Real) {L M : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num) (hMd : 0 < M.den) (hMn : 0 ≤ M.num)
    (hlip : ∀ t t', Rle (Rabs (Rsub (ψ t) (ψ t'))) (Rmul (ofQ L hLd) (Rabs (Rsub t t'))))
    (hbd : ∀ t, Rle (Rabs (ψ t)) (ofQ M hMd)) (hfc : ∀ t t', Req t t' → Req (ψ t) (ψ t')) : CField where
  F := fun _ t => ψ t
  Lx := (⟨0, 1⟩ : Q)
  Lt := L
  M := M
  hLxd := by decide
  hLxn := by decide
  hLtd := hLd
  hLtn := hLn
  hMd := hMd
  hMn := hMn
  hlipx := fun t x x' => const_lip0 (ψ t) x x'
  hlipt := fun _ t t' => hlip t t'
  hbd := fun _ t => hbd t
  hfcx := @fun _ _ _ _ => Req_refl _
  hfct := @fun _ _ _ h => hfc _ _ h

/-- A certified constant. -/
def constF (c : Real) {Mc : Q} (hMcd : 0 < Mc.den) (hMcn : 0 ≤ Mc.num) (hc : Rle (Rabs c) (ofQ Mc hMcd)) : CField :=
  ofX (fun _ => c) (L := (⟨0, 1⟩ : Q)) (by decide) (by decide) hMcd hMcn (const_lip0 c) (fun _ => hc) (fun _ _ _ => Req_refl c)

/-- Composition with a certified map of the scale: `(x,t) ↦ u(φ x, t)`. -/
def compX (u : CField) (φ : Real → Real) {Lφ : Q} (hLφd : 0 < Lφ.den) (hLφn : 0 ≤ Lφ.num)
    (hφ : ∀ x x', Rle (Rabs (Rsub (φ x) (φ x'))) (Rmul (ofQ Lφ hLφd) (Rabs (Rsub x x'))))
    (hφc : ∀ x x', Req x x' → Req (φ x) (φ x')) : CField where
  F := fun x t => u.F (φ x) t
  Lx := mul u.Lx Lφ
  Lt := u.Lt
  M := u.M
  hLxd := Qmul_den_pos u.hLxd hLφd
  hLxn := Qmul_num_nonneg u.hLxn hLφn
  hLtd := u.hLtd
  hLtn := u.hLtn
  hMd := u.hMd
  hMn := u.hMn
  hlipx := fun t x x' => Rle_trans (u.hlipx t (φ x) (φ x'))
    (Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ u.hLxd u.hLxn) (hφ x x'))
      (Rle_of_Req (Req_trans (Req_symm (Rmul_assoc _ _ _)) (Rmul_congr (Rmul_ofQ_ofQ u.hLxd hLφd) (Req_refl _)))))
  hlipt := fun x t t' => u.hlipt (φ x) t t'
  hbd := fun x t => u.hbd (φ x) t
  hfcx := @fun _ _ t h => u.hfcx t (hφc _ _ h)
  hfct := @fun x _ _ h => u.hfct (φ x) h

end CField

/-- `|a − c| ≤ |a − b| + |b − c|`. -/
theorem abs_sub_tri (a b c : Real) : Rle (Rabs (Rsub a c)) (Radd (Rabs (Rsub a b)) (Rabs (Rsub b c))) :=
  Rle_trans (Rle_of_Req (Rabs_congr (Req_symm (Rsub_split a b c)))) (Rabs_Radd _ _)

/-- `L₁·d + L₂·d ≈ (L₁ + L₂)·d`. -/
theorem two_mod_combine {L1 L2 : Q} (h1 : 0 < L1.den) (h2 : 0 < L2.den) (d : Real) :
    Req (Radd (Rmul (ofQ L1 h1) d) (Rmul (ofQ L2 h2) d)) (Rmul (ofQ (add L1 L2) (add_den_pos h1 h2)) d) :=
  Req_trans (Req_symm (Rmul_distrib_right _ _ _)) (Rmul_congr (Radd_ofQ_ofQ h1 h2) (Req_refl d))

/-- The two-step Lipschitz estimate through a joint reparametrization `(x,t) ↦ (α x t, β x t)`. -/
theorem comp2_step (u : CField) {α β α' β' : Real} {Lα Lβ : Q} (hLαd : 0 < Lα.den) (hLβd : 0 < Lβ.den) (d : Real)
    (hα : Rle (Rabs (Rsub α α')) (Rmul (ofQ Lα hLαd) d)) (hβ : Rle (Rabs (Rsub β β')) (Rmul (ofQ Lβ hLβd) d)) :
    Rle (Rabs (Rsub (u.F α β) (u.F α' β')))
        (Rmul (ofQ (add (mul u.Lx Lα) (mul u.Lt Lβ)) (add_den_pos (Qmul_den_pos u.hLxd hLαd) (Qmul_den_pos u.hLtd hLβd))) d) := by
  refine Rle_trans (abs_sub_tri (u.F α β) (u.F α' β) (u.F α' β')) ?_
  have h1 : Rle (Rabs (Rsub (u.F α β) (u.F α' β))) (Rmul (ofQ (mul u.Lx Lα) (Qmul_den_pos u.hLxd hLαd)) d) :=
    Rle_trans (u.hlipx β α α') (Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ u.hLxd u.hLxn) hα)
      (Rle_of_Req (Req_trans (Req_symm (Rmul_assoc _ _ _)) (Rmul_congr (Rmul_ofQ_ofQ u.hLxd hLαd) (Req_refl _)))))
  have h2 : Rle (Rabs (Rsub (u.F α' β) (u.F α' β'))) (Rmul (ofQ (mul u.Lt Lβ) (Qmul_den_pos u.hLtd hLβd)) d) :=
    Rle_trans (u.hlipt α' β β') (Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ u.hLtd u.hLtn) hβ)
      (Rle_of_Req (Req_trans (Req_symm (Rmul_assoc _ _ _)) (Rmul_congr (Rmul_ofQ_ofQ u.hLtd hLβd) (Req_refl _)))))
  exact Rle_trans (Radd_le_add h1 h2) (Rle_of_Req (two_mod_combine _ _ d))

namespace CField

/-- Composition with a certified joint reparametrization `(x,t) ↦ u(α x t, β x t)`. -/
def comp2 (u : CField) (α β : Real → Real → Real) {Lαx Lαt Lβx Lβt : Q}
    (hαxd : 0 < Lαx.den) (hαxn : 0 ≤ Lαx.num) (hαtd : 0 < Lαt.den) (hαtn : 0 ≤ Lαt.num)
    (hβxd : 0 < Lβx.den) (hβxn : 0 ≤ Lβx.num) (hβtd : 0 < Lβt.den) (hβtn : 0 ≤ Lβt.num)
    (hαx : ∀ t x x', Rle (Rabs (Rsub (α x t) (α x' t))) (Rmul (ofQ Lαx hαxd) (Rabs (Rsub x x'))))
    (hαt : ∀ x t t', Rle (Rabs (Rsub (α x t) (α x t'))) (Rmul (ofQ Lαt hαtd) (Rabs (Rsub t t'))))
    (hβx : ∀ t x x', Rle (Rabs (Rsub (β x t) (β x' t))) (Rmul (ofQ Lβx hβxd) (Rabs (Rsub x x'))))
    (hβt : ∀ x t t', Rle (Rabs (Rsub (β x t) (β x t'))) (Rmul (ofQ Lβt hβtd) (Rabs (Rsub t t'))))
    (hαc : ∀ {x x' t t' : Real}, Req x x' → Req t t' → Req (α x t) (α x' t'))
    (hβc : ∀ {x x' t t' : Real}, Req x x' → Req t t' → Req (β x t) (β x' t')) : CField where
  F := fun x t => u.F (α x t) (β x t)
  Lx := add (mul u.Lx Lαx) (mul u.Lt Lβx)
  Lt := add (mul u.Lx Lαt) (mul u.Lt Lβt)
  M := u.M
  hLxd := add_den_pos (Qmul_den_pos u.hLxd hαxd) (Qmul_den_pos u.hLtd hβxd)
  hLxn := Qadd_num_nonneg_loc (Qmul_num_nonneg u.hLxn hαxn) (Qmul_num_nonneg u.hLtn hβxn)
  hLtd := add_den_pos (Qmul_den_pos u.hLxd hαtd) (Qmul_den_pos u.hLtd hβtd)
  hLtn := Qadd_num_nonneg_loc (Qmul_num_nonneg u.hLxn hαtn) (Qmul_num_nonneg u.hLtn hβtn)
  hMd := u.hMd
  hMn := u.hMn
  hlipx := fun t x x' => comp2_step u hαxd hβxd (Rabs (Rsub x x')) (hαx t x x') (hβx t x x')
  hlipt := fun x t t' => comp2_step u hαtd hβtd (Rabs (Rsub t t')) (hαt x t t') (hβt x t t')
  hbd := fun _ _ => u.hbd _ _
  hfcx := @fun _ _ t h => cfield_fc u (hαc h (Req_refl t)) (hβc h (Req_refl t))
  hfct := @fun x _ _ h => cfield_fc u (hαc (Req_refl x) h) (hβc (Req_refl x) h)

-- ===========================================================================
-- (2) The Haar integral at a scale and the scale integral.
-- ===========================================================================

/-- **The Haar integral at scale `x`**: `∫₀¹ z(x, a + w·y) dy`. -/
def intT (C : NormCtx) (z : CField) (x : Real) : Real :=
  riemannIntegral (f := fun y => z.F x (affineMap C.a C.w C.had C.hw y)) (L := mul z.Lt C.w)
    (Qmul_den_pos z.hLtd C.hw) (Int.mul_nonneg z.hLtn C.hwn)
    (affine_lip z.hLtd z.hLtn (z.hlipt x) C.a C.w C.had C.hw C.hwn)
    (fun _ _ h => z.hfct x (affineMap_congr C.a C.w C.had C.hw h))

end CField

open CField

/-- The Haar integral is `Lx`-Lipschitz in the scale. -/
theorem intT_lip (C : NormCtx) (z : CField) : ∀ x x',
    Rle (Rabs (Rsub (intT C z x) (intT C z x'))) (Rmul (ofQ z.Lx z.hLxd) (Rabs (Rsub x x'))) :=
  fun x x' => param_integral_lip (F := fun x y => z.F x (affineMap C.a C.w C.had C.hw y)) (L := fun _ => mul z.Lt C.w)
    (fun _ => Qmul_den_pos z.hLtd C.hw) (fun _ => Int.mul_nonneg z.hLtn C.hwn)
    (fun x => affine_lip z.hLtd z.hLtn (z.hlipt x) C.a C.w C.had C.hw C.hwn)
    (fun x _ _ h => z.hfct x (affineMap_congr C.a C.w C.had C.hw h))
    z.hLxd (fun y _ _ x x' => z.hlipx (affineMap C.a C.w C.had C.hw y) x x') x x'

theorem intT_fc (C : NormCtx) (z : CField) : ∀ x x', Req x x' → Req (intT C z x) (intT C z x') :=
  fun x x' h => param_integral_congr (F := fun x y => z.F x (affineMap C.a C.w C.had C.hw y)) (L := fun _ => mul z.Lt C.w)
    (fun _ => Qmul_den_pos z.hLtd C.hw) (fun _ => Int.mul_nonneg z.hLtn C.hwn)
    (fun x => affine_lip z.hLtd z.hLtn (z.hlipt x) C.a C.w C.had C.hw C.hwn)
    (fun x _ _ h => z.hfct x (affineMap_congr C.a C.w C.had C.hw h))
    x x' (fun y => z.hfcx _ h)

namespace CField

/-- **The scale integral of the Haar integral** over `[lo, lo + w]`. -/
def intX (C : NormCtx) (z : CField) (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) : Real :=
  riemannIntegralI (f := fun x => intT C z x) z.hLxd z.hLxn (intT_lip C z) (intT_fc C z) lo w hlo hw hwn

end CField

-- ===========================================================================
-- (3) Plumbing: pointwise identities through integrals with independent certificates.
-- ===========================================================================

section Plumbing

variable {f g h : Real → Real} {Lf Lg Lh : Q}

/-- `f ≈ g` pointwise ⟹ `∫₀¹ f ≈ ∫₀¹ g` (each side with its own certificate). -/
theorem intU_congr_free (hfd : 0 < Lf.den) (hfn : 0 ≤ Lf.num)
    (hflip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ Lf hfd) (Rabs (Rsub x y))))
    (hffc : ∀ x y, Req x y → Req (f x) (f y))
    (hgd : 0 < Lg.den) (hgn : 0 ≤ Lg.num)
    (hglip : ∀ x y, Rle (Rabs (Rsub (g x) (g y))) (Rmul (ofQ Lg hgd) (Rabs (Rsub x y))))
    (hgfc : ∀ x y, Req x y → Req (g x) (g y)) (hfg : ∀ y, Req (f y) (g y)) :
    Req (riemannIntegral hfd hfn hflip hffc) (riemannIntegral hgd hgn hglip hgfc) := by
  have hg' : ∀ x y, Rle (Rabs (Rsub (g x) (g y))) (Rmul (ofQ Lf hfd) (Rabs (Rsub x y))) :=
    lip_of_congr_pd hfd (fun y => Req_symm (hfg y)) hflip
  exact Req_trans (riemannIntegral_congr hfd hfn hflip hffc hg' hgfc hfg)
    (riemannIntegral_certif_irrel _ _ hg' hgfc hgd hgn hglip hgfc)

/-- `f ≈ g` on `[0,1]` ⟹ `∫₀¹ f ≈ ∫₀¹ g` (independent certificates). -/
theorem intU_congr_unit_free (hfd : 0 < Lf.den) (hfn : 0 ≤ Lf.num)
    (hflip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ Lf hfd) (Rabs (Rsub x y))))
    (hffc : ∀ x y, Req x y → Req (f x) (f y))
    (hgd : 0 < Lg.den) (hgn : 0 ≤ Lg.num)
    (hglip : ∀ x y, Rle (Rabs (Rsub (g x) (g y))) (Rmul (ofQ Lg hgd) (Rabs (Rsub x y))))
    (hgfc : ∀ x y, Req x y → Req (g x) (g y)) (hfg : ∀ y, Rle zero y → Rle y one → Req (f y) (g y)) :
    Req (riemannIntegral hfd hfn hflip hffc) (riemannIntegral hgd hgn hglip hgfc) := by
  have hSd : 0 < (add Lf Lg).den := add_den_pos hfd hgd
  have hSn : 0 ≤ (add Lf Lg).num := Qadd_num_nonneg_loc hfn hgn
  have hf' := lip_weaken_fl hfd hSd (Qle_add_right_nonneg hgn) hflip
  have hg' := lip_weaken_fl hgd hSd (Qle_add_left_nonneg hfn) hglip
  refine Req_trans (riemannIntegral_certif_irrel _ _ hflip hffc hSd hSn hf' hffc) ?_
  refine Req_trans (riemannIntegral_congr_unit hSd hSn hf' hffc hg' hgfc hfg) ?_
  exact riemannIntegral_certif_irrel _ _ hg' hgfc hgd hgn hglip hgfc

/-- `h ≈ f − g` pointwise ⟹ `∫₀¹ h ≈ ∫₀¹ f − ∫₀¹ g`. -/
theorem intU_sub_free (hfd : 0 < Lf.den) (hfn : 0 ≤ Lf.num)
    (hflip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ Lf hfd) (Rabs (Rsub x y))))
    (hffc : ∀ x y, Req x y → Req (f x) (f y))
    (hgd : 0 < Lg.den) (hgn : 0 ≤ Lg.num)
    (hglip : ∀ x y, Rle (Rabs (Rsub (g x) (g y))) (Rmul (ofQ Lg hgd) (Rabs (Rsub x y))))
    (hgfc : ∀ x y, Req x y → Req (g x) (g y))
    (hhd : 0 < Lh.den) (hhn : 0 ≤ Lh.num)
    (hhlip : ∀ x y, Rle (Rabs (Rsub (h x) (h y))) (Rmul (ofQ Lh hhd) (Rabs (Rsub x y))))
    (hhfc : ∀ x y, Req x y → Req (h x) (h y)) (hh : ∀ y, Req (h y) (Rsub (f y) (g y))) :
    Req (riemannIntegral hhd hhn hhlip hhfc) (Rsub (riemannIntegral hfd hfn hflip hffc) (riemannIntegral hgd hgn hglip hgfc)) := by
  have hng := lip_neg_pi hgd hglip
  have hngfc : ∀ x y, Req x y → Req (Rneg (g x)) (Rneg (g y)) := fun x y e => Rneg_congr (hgfc x y e)
  have hsum := lip_add_fl hfd hgd hflip hng
  have hsumfc : ∀ x y, Req x y → Req (Radd (f x) (Rneg (g x))) (Radd (f y) (Rneg (g y))) :=
    fun x y e => Radd_congr (hffc x y e) (hngfc x y e)
  have hSd : 0 < (add Lf Lg).den := add_den_pos hfd hgd
  have hSn : 0 ≤ (add Lf Lg).num := Qadd_num_nonneg_loc hfn hgn
  have hf' := lip_weaken_fl hfd hSd (Qle_add_right_nonneg hgn) hflip
  have hng' := lip_weaken_fl hgd hSd (Qle_add_left_nonneg hfn) hng
  refine Req_trans (intU_congr_free hhd hhn hhlip hhfc hSd hSn hsum hsumfc hh) ?_
  refine Req_trans (riemannIntegral_add hSd hSn hf' hffc hng' hngfc hsum hsumfc) ?_
  refine Radd_congr (riemannIntegral_certif_irrel _ _ hf' hffc hfd hfn hflip hffc) ?_
  refine Req_trans (riemannIntegral_certif_irrel _ _ hng' hngfc hgd hgn hng hngfc) ?_
  exact riemannIntegral_neg hgd hgn hglip hgfc hng hngfc

/-- `h ≈ c·f` pointwise (real `c`) ⟹ `∫₀¹ h ≈ c·∫₀¹ f`. -/
theorem intU_smul_free (c : Real) (hfd : 0 < Lf.den) (hfn : 0 ≤ Lf.num)
    (hflip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ Lf hfd) (Rabs (Rsub x y))))
    (hffc : ∀ x y, Req x y → Req (f x) (f y))
    (hhd : 0 < Lh.den) (hhn : 0 ≤ Lh.num)
    (hhlip : ∀ x y, Rle (Rabs (Rsub (h x) (h y))) (Rmul (ofQ Lh hhd) (Rabs (Rsub x y))))
    (hhfc : ∀ x y, Req x y → Req (h x) (h y)) (hh : ∀ y, Req (h y) (Rmul c (f y))) :
    Req (riemannIntegral hhd hhn hhlip hhfc) (Rmul c (riemannIntegral hfd hfn hflip hffc)) :=
  Req_trans (intU_congr_free hhd hhn hhlip hhfc (Qmul_den_pos Nat.one_pos hfd) (Qmul_num_nonneg (xBQ_num_nonneg c) hfn)
      (lip_smul_fl c hfd hfn hflip) (fc_smul_fl c hffc) hh)
    (riemannIntegral_smul_real_fl c hfd hfn hflip hffc)

/-- `h ≈ 0` pointwise ⟹ `∫₀¹ h ≈ 0`. -/
theorem intU_zero_free (hhd : 0 < Lh.den) (hhn : 0 ≤ Lh.num)
    (hhlip : ∀ x y, Rle (Rabs (Rsub (h x) (h y))) (Rmul (ofQ Lh hhd) (Rabs (Rsub x y))))
    (hhfc : ∀ x y, Req x y → Req (h x) (h y)) (hh : ∀ y, Req (h y) zero) :
    Req (riemannIntegral hhd hhn hhlip hhfc) zero :=
  Req_trans (intU_congr_free hhd hhn hhlip hhfc (by decide) (by decide) (const_lip0 zero) (fun _ _ _ => Req_refl zero) hh)
    (riemannIntegral_const_gen zero _ _ _ _)

/-- Window version: `f ≈ g` pointwise ⟹ `∫_{[lo,lo+w]} f ≈ ∫_{[lo,lo+w]} g`. -/
theorem intI_congr_free (hfd : 0 < Lf.den) (hfn : 0 ≤ Lf.num)
    (hflip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ Lf hfd) (Rabs (Rsub x y))))
    (hffc : ∀ x y, Req x y → Req (f x) (f y))
    (hgd : 0 < Lg.den) (hgn : 0 ≤ Lg.num)
    (hglip : ∀ x y, Rle (Rabs (Rsub (g x) (g y))) (Rmul (ofQ Lg hgd) (Rabs (Rsub x y))))
    (hgfc : ∀ x y, Req x y → Req (g x) (g y)) (hfg : ∀ y, Req (f y) (g y))
    (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) :
    Req (riemannIntegralI hfd hfn hflip hffc lo w hlo hw hwn) (riemannIntegralI hgd hgn hglip hgfc lo w hlo hw hwn) := by
  have hg' : ∀ x y, Rle (Rabs (Rsub (g x) (g y))) (Rmul (ofQ Lf hfd) (Rabs (Rsub x y))) :=
    lip_of_congr_pd hfd (fun y => Req_symm (hfg y)) hflip
  exact Req_trans (riemannIntegralI_congr hfd hfn hflip hffc hg' hgfc lo w hlo hw hwn hfg)
    (riemannIntegralI_certif_irrel _ _ hg' hgfc hgd hgn hglip hgfc lo w hlo hw hwn)

/-- Window version with agreement on the window only. -/
theorem intI_congr_unit_free (hfd : 0 < Lf.den) (hfn : 0 ≤ Lf.num)
    (hflip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ Lf hfd) (Rabs (Rsub x y))))
    (hffc : ∀ x y, Req x y → Req (f x) (f y))
    (hgd : 0 < Lg.den) (hgn : 0 ≤ Lg.num)
    (hglip : ∀ x y, Rle (Rabs (Rsub (g x) (g y))) (Rmul (ofQ Lg hgd) (Rabs (Rsub x y))))
    (hgfc : ∀ x y, Req x y → Req (g x) (g y))
    (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (hfg : ∀ y, Rle zero y → Rle y one → Req (f (affineMap lo w hlo hw y)) (g (affineMap lo w hlo hw y))) :
    Req (riemannIntegralI hfd hfn hflip hffc lo w hlo hw hwn) (riemannIntegralI hgd hgn hglip hgfc lo w hlo hw hwn) := by
  have hSd : 0 < (add Lf Lg).den := add_den_pos hfd hgd
  have hSn : 0 ≤ (add Lf Lg).num := Qadd_num_nonneg_loc hfn hgn
  have hf' := lip_weaken_fl hfd hSd (Qle_add_right_nonneg hgn) hflip
  have hg' := lip_weaken_fl hgd hSd (Qle_add_left_nonneg hfn) hglip
  refine Req_trans (riemannIntegralI_certif_irrel _ _ hflip hffc hSd hSn hf' hffc lo w hlo hw hwn) ?_
  refine Req_trans (riemannIntegralI_congr_unit hSd hSn hf' hffc hg' hgfc lo w hlo hw hwn hfg) ?_
  exact riemannIntegralI_certif_irrel _ _ hg' hgfc hgd hgn hglip hgfc lo w hlo hw hwn

/-- Window version: `h ≈ f − g` pointwise ⟹ `∫ h ≈ ∫ f − ∫ g`. -/
theorem intI_sub_free (hfd : 0 < Lf.den) (hfn : 0 ≤ Lf.num)
    (hflip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ Lf hfd) (Rabs (Rsub x y))))
    (hffc : ∀ x y, Req x y → Req (f x) (f y))
    (hgd : 0 < Lg.den) (hgn : 0 ≤ Lg.num)
    (hglip : ∀ x y, Rle (Rabs (Rsub (g x) (g y))) (Rmul (ofQ Lg hgd) (Rabs (Rsub x y))))
    (hgfc : ∀ x y, Req x y → Req (g x) (g y))
    (hhd : 0 < Lh.den) (hhn : 0 ≤ Lh.num)
    (hhlip : ∀ x y, Rle (Rabs (Rsub (h x) (h y))) (Rmul (ofQ Lh hhd) (Rabs (Rsub x y))))
    (hhfc : ∀ x y, Req x y → Req (h x) (h y)) (hh : ∀ y, Req (h y) (Rsub (f y) (g y)))
    (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) :
    Req (riemannIntegralI hhd hhn hhlip hhfc lo w hlo hw hwn)
        (Rsub (riemannIntegralI hfd hfn hflip hffc lo w hlo hw hwn) (riemannIntegralI hgd hgn hglip hgfc lo w hlo hw hwn)) := by
  have hng := lip_neg_pi hgd hglip
  have hngfc : ∀ x y, Req x y → Req (Rneg (g x)) (Rneg (g y)) := fun x y e => Rneg_congr (hgfc x y e)
  have hsum := lip_add_fl hfd hgd hflip hng
  have hsumfc : ∀ x y, Req x y → Req (Radd (f x) (Rneg (g x))) (Radd (f y) (Rneg (g y))) :=
    fun x y e => Radd_congr (hffc x y e) (hngfc x y e)
  have hSd : 0 < (add Lf Lg).den := add_den_pos hfd hgd
  have hSn : 0 ≤ (add Lf Lg).num := Qadd_num_nonneg_loc hfn hgn
  have hf' := lip_weaken_fl hfd hSd (Qle_add_right_nonneg hgn) hflip
  have hng' := lip_weaken_fl hgd hSd (Qle_add_left_nonneg hfn) hng
  refine Req_trans (intI_congr_free hhd hhn hhlip hhfc hSd hSn hsum hsumfc hh lo w hlo hw hwn) ?_
  refine Req_trans (riemannIntegralI_add hSd hSn hf' hffc hng' hngfc hsum hsumfc lo w hlo hw hwn) ?_
  refine Radd_congr (riemannIntegralI_certif_irrel _ _ hf' hffc hfd hfn hflip hffc lo w hlo hw hwn) ?_
  refine Req_trans (riemannIntegralI_certif_irrel _ _ hng' hngfc hgd hgn hng hngfc lo w hlo hw hwn) ?_
  exact riemannIntegralI_neg hgd hgn hglip hgfc hng hngfc lo w hlo hw hwn

end Plumbing

-- ===========================================================================
-- (4) The field integrals inherit the plumbing.
-- ===========================================================================

theorem intT_congr_pt (C : NormCtx) (u v : CField) (x : Real) (h : ∀ t, Req (u.F x t) (v.F x t)) :
    Req (intT C u x) (intT C v x) :=
  intU_congr_free _ _ _ _ _ _ _ _ (fun _ => h _)

/-- Agreement on the Haar window `t ∈ [a, a+w]` (as `t = a + w·y`, `y ∈ [0,1]`) suffices. -/
theorem intT_congr_win (C : NormCtx) (u v : CField) (x : Real)
    (h : ∀ y, Rle zero y → Rle y one → Req (u.F x (affineMap C.a C.w C.had C.hw y)) (v.F x (affineMap C.a C.w C.had C.hw y))) :
    Req (intT C u x) (intT C v x) :=
  intU_congr_unit_free _ _ _ _ _ _ _ _ h

theorem intT_sub_pt (C : NormCtx) (u v z : CField) (x : Real) (h : ∀ t, Req (z.F x t) (Rsub (u.F x t) (v.F x t))) :
    Req (intT C z x) (Rsub (intT C u x) (intT C v x)) :=
  intU_sub_free _ _ _ _ _ _ _ _ _ _ _ _ (fun _ => h _)

theorem intT_zero_pt (C : NormCtx) (z : CField) (x : Real) (h : ∀ t, Req (z.F x t) zero) : Req (intT C z x) zero :=
  intU_zero_free _ _ _ _ (fun _ => h _)

theorem intX_congr_pt (C : NormCtx) (u v : CField) (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (h : ∀ x t, Req (u.F x t) (v.F x t)) :
    Req (intX C u lo w hlo hw hwn) (intX C v lo w hlo hw hwn) :=
  intI_congr_free _ _ _ _ _ _ _ _ (fun x => intT_congr_pt C u v x (h x)) lo w hlo hw hwn

/-- Agreement on the scale window and the Haar window suffices. -/
theorem intX_congr_win (C : NormCtx) (u v : CField) (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (h : ∀ s, Rle zero s → Rle s one → ∀ y, Rle zero y → Rle y one →
      Req (u.F (affineMap lo w hlo hw s) (affineMap C.a C.w C.had C.hw y)) (v.F (affineMap lo w hlo hw s) (affineMap C.a C.w C.had C.hw y))) :
    Req (intX C u lo w hlo hw hwn) (intX C v lo w hlo hw hwn) :=
  intI_congr_unit_free _ _ _ _ _ _ _ _ lo w hlo hw hwn (fun s h0 h1 => intT_congr_win C u v _ (h s h0 h1))

theorem intX_sub_pt (C : NormCtx) (u v z : CField) (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (h : ∀ x t, Req (z.F x t) (Rsub (u.F x t) (v.F x t))) :
    Req (intX C z lo w hlo hw hwn) (Rsub (intX C u lo w hlo hw hwn) (intX C v lo w hlo hw hwn)) :=
  intI_sub_free _ _ _ _ _ _ _ _ _ _ _ _ (fun x => intT_sub_pt C u v z x (h x)) lo w hlo hw hwn

end UOR.Bridge.F1Square.Square
