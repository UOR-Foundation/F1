/-
F1 square — **THE SOURCE-COHERENT CARRIER AND THE ORBIT READING** (`AtlasSourceCoherent.lean`, target-free).

A source field is a pair `(U, V)`: a scale-indexed Haar field `U x t` and an anchor field `V t`.  It is
SOURCE-COHERENT for a context (`SourceCoherent C z`) when it satisfies, as PROPOSITIONS ABOUT `z` (not as
`∃ f`), the laws proved for the decoded scale field in AC-23:

  * the orbit law: `x'·t = x·t'`, both scales in `[0,S]`, both Haar coordinates `≥ a` ⟹
    `invSq(x')·U x t = invSq(x)·U x' t'`;
  * the shift law: `1 ≤ x ≤ S`, `t ≥ a·x` ⟹ `U x t = invSq(x)·V(t·x⁻¹)`;
  * the zero rows: at a rational scale `1 ≤ q ≤ S` and `t ≤ a·q`, `U q t = 0`.

`decodeField C f = (Uc C · f ·, Vc C f)` is source-coherent for every core test (`decodeField_coherent`).

THE ORBIT READING.  On a coupling address `c` (finite site `(n,t)`, Archimedean site `(x,s)`, `n·s = x·t`)
the cross-multiplied reading of the prime-scale value from the continuous leg is
`orbitRead C c z = invSq(n)·U x s`.  **`orbitRead_independent`**: for a coherent `z`, two coupling addresses
with the SAME finite leg give the same reading up to the exact weights,
`invSq(x₂)·orbitRead c₁ z = invSq(x₁)·orbitRead c₂ z` — the choice of Archimedean leg on the orbit is not
semantic data of the coherent field; every admissible reading is the same source-restricted functional.

THE ADMISSIBLE INTERVAL.  `Admissible C k p x`: `x ∈ [1+2^{-k}, B]` with `x·t/n ∈ [a, a+w]` — the scales
whose orbit-mate of the active row `(n,t)` stays inside the Haar window.  `admissible_self`: `x = n` is
admissible for every active row `(n,t)` with `n ≤ B` (`x·t/n = t`).  No density, measure, operator, bound,
or sign is defined or claimed here.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasOrbitDecode
import F1Square.Square.AtlasArchGram

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

/-- A source field: a scale-indexed Haar field and an anchor field. -/
structure SourceField where
  U : Real → Real → Real
  V : Real → Real

/-- **Source coherence** — the AC-23 laws as propositions about the field. -/
structure SourceCoherent (C : NormCtx) (z : SourceField) : Prop where
  orbit : ∀ {x x' t t' : Real}, Rle zero x → Rle x (ofQ C.S C.hSd) → Rle zero x' → Rle x' (ofQ C.S C.hSd) →
    Rle (ofQ C.a C.had) t → Rle (ofQ C.a C.had) t' → Req (Rmul x' t) (Rmul x t') →
    Req (Rmul (invSq C x') (z.U x t)) (Rmul (invSq C x) (z.U x' t'))
  shift : ∀ {x t : Real}, Rle one x → Rle x (ofQ C.S C.hSd) → ∀ {kx : Nat} (hkx : Qlt (Qbound kx) (x.seq kx)),
    Rle (Rmul (ofQ C.a C.had) x) t → Req (z.U x t) (Rmul (invSq C x) (z.V (Rmul t (Rinv x kx hkx))))
  zeroRow : ∀ (q : Q) (hqd : 0 < q.den), Qle (⟨1, 1⟩ : Q) q → Qle q C.S → ∀ {t : Real},
    Rle t (ofQ (mul C.a q) (Qmul_den_pos C.had hqd)) → Req (z.U (ofQ q hqd) t) zero

/-- The decoded scale field of a test. -/
def decodeField (C : NormCtx) (f : L2Test) : SourceField := ⟨fun x t => Uc C x f t, fun t => Vc C f t⟩

/-- **Every core test decodes to a source-coherent field** (AC-23). -/
theorem decodeField_coherent (C : NormCtx) (f : L2Test) (hf : CoreTest C.geom f) : SourceCoherent C (decodeField C f) where
  orbit := fun h0 hS h0' hS' ht ht' horb => Uc_orbit C f h0 hS h0' hS' ht ht' horb
  shift := @fun x t hx1 hS kx hkx hax => Uc_eq_invSq_Vc_shift C f hx1 hS hkx hax
  zeroRow := @fun q hqd hq1 hqS _t ht => Uc_zero_row C f hf q hqd hq1 hqS ht

-- ===========================================================================
-- (1) The orbit reading and its independence of the Archimedean leg.
-- ===========================================================================

/-- **The orbit reading** of the prime-scale value from the continuous leg, cross-multiplied by `invSq(n)`. -/
def orbitRead (C : NormCtx) (c : CouplingAddr) (z : SourceField) : Real :=
  Rmul (invSq C c.fin.n.r) (z.U c.arch.xr c.arch.sr)

/-- The band/window hypotheses of a coupling address. -/
structure AddrAdmissible (C : NormCtx) (c : CouplingAddr) : Prop where
  hnS : Rle c.fin.n.r (ofQ C.S C.hSd)
  hxS : Rle c.arch.xr (ofQ C.S C.hSd)
  ht : Rle (ofQ C.a C.had) c.fin.tr
  hs : Rle (ofQ C.a C.had) c.arch.sr

theorem finN_nonneg (p : FiniteLocalAddr) : Rle zero p.n.r :=
  Rle_ofQ_ofQ (by decide) _ (by
    show (0 : Int) * (p.n.q.den : Int) ≤ p.n.q.num * ((1 : Nat) : Int)
    have := (primePowerAddr_q_num p.n); push_cast; omega)
theorem archX_nonneg (q : ArchLocalAddr) : Rle zero q.xr :=
  Rle_ofQ_ofQ (by decide) _ (by
    show (0 : Int) * (q.x.den : Int) ≤ q.x.num * ((1 : Nat) : Int)
    have := q.hxn; push_cast; omega)

/-- On a coupling address, the coherent field's orbit law reads: `invSq(x)·U n t = invSq(n)·U x s`. -/
theorem coherent_orbit_addr (C : NormCtx) {z : SourceField} (hz : SourceCoherent C z) (c : CouplingAddr)
    (hc : AddrAdmissible C c) :
    Req (Rmul (invSq C c.arch.xr) (z.U c.fin.n.r c.fin.tr)) (orbitRead C c z) :=
  hz.orbit (finN_nonneg c.fin) hc.hnS (archX_nonneg c.arch) hc.hxS hc.ht hc.hs (onOrbit_real (couplingAddr_onOrbit c))

/-- **★ THE ORBIT READING IS INDEPENDENT OF THE ARCHIMEDEAN LEG** (cross-multiplied form): for a coherent field
    and two admissible coupling addresses with the same finite leg,
    `invSq(x₂)·orbitRead c₁ z = invSq(x₁)·orbitRead c₂ z`. -/
theorem orbitRead_independent (C : NormCtx) {z : SourceField} (hz : SourceCoherent C z)
    (c₁ c₂ : CouplingAddr) (h : c₁.fin = c₂.fin) (h₁ : AddrAdmissible C c₁) (h₂ : AddrAdmissible C c₂) :
    Req (Rmul (invSq C c₂.arch.xr) (orbitRead C c₁ z)) (Rmul (invSq C c₁.arch.xr) (orbitRead C c₂ z)) := by
  have e₁ := coherent_orbit_addr C hz c₁ h₁
  have e₂ := coherent_orbit_addr C hz c₂ h₂
  rw [h] at e₁
  -- invSq x₂ · R₁ ≈ invSq x₂ · (invSq x₁ · U n t) ≈ invSq x₁ · (invSq x₂ · U n t) ≈ invSq x₁ · R₂
  refine Req_trans (Rmul_congr (Req_refl _) (Req_symm e₁)) ?_
  refine Req_trans (swap_w_ac _ _ _) ?_
  exact Rmul_congr (Req_refl _) e₂

-- ===========================================================================
-- (2) The admissible interval `J_{k,n,t}` and the self-scale.
-- ===========================================================================

/-- The orbit-mate Haar coordinate `x·t/n` of the row `(n,t)` at scale `x`. -/
def mateS (p : FiniteLocalAddr) (x : Q) : Q := mul (mul x p.t) (Qinv p.n.q)

/-- **Admissibility of a scale for an active row**: `x ∈ [1+2^{-k}, B]` and the orbit-mate stays in the window. -/
structure Admissible (C : NormCtx) (k : Nat) (p : FiniteLocalAddr) (x : Q) : Prop where
  hlo : Qle (tailFloor k) x
  hhi : Qle x (canonB C)
  hwin_lo : Qle C.a (mateS p x)
  hwin_hi : Qle (mateS p x) (add C.a C.w)

theorem mateS_self (p : FiniteLocalAddr) : Qeq (mateS p p.n.q) p.t := by
  unfold mateS
  have hn' : ((p.n.q.num.toNat : Nat) : Int) = p.n.q.num := Int.toNat_of_nonneg (Int.le_of_lt (primePowerAddr_q_num p.n))
  simp only [Qeq, mul, Qinv]
  push_cast [hn']
  simp only [Int.toNat_ofNat, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm, Int.one_mul, Int.mul_one]

/-- `1 + 2^{-k} ≤ 2` for every `k`. -/
theorem tailFloor_le_two (k : Nat) : Qle (tailFloor k) (⟨2, 1⟩ : Q) := by
  unfold tailFloor
  show (1 * ((2 ^ k : Nat) : Int) + 1 * ((1 : Nat) : Int)) * ((1 : Nat) : Int) ≤ 2 * ((1 * 2 ^ k : Nat) : Int)
  have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hp' : (1 : Int) ≤ (2 : Int) ^ k := by exact_mod_cast hp
  push_cast; omega

/-- **★ The self-scale is admissible**: for an active row `(n,t)` (`t ∈ [a, a+w]`, `n ≤ B`), `x = n ∈ J_{k,n,t}`. -/
theorem admissible_self (C : NormCtx) (k : Nat) (p : FiniteLocalAddr) (hnB : Qle p.n.q (canonB C))
    (hta : Qle C.a p.t) (htw : Qle p.t (add C.a C.w)) : Admissible C k p p.n.q where
  hlo := Qle_trans (by decide) (tailFloor_le_two k) (by
    show (2 : Int) * ((1 : Nat) : Int) ≤ ((p.n.1 : Nat) : Int) * ((1 : Nat) : Int)
    have := primePowerAddr_two_le p.n; push_cast; omega)
  hhi := hnB
  hwin_lo := Qle_trans p.htd hta (Qeq_le (Qeq_symm (mateS_self p)))
  hwin_hi := Qle_trans p.htd (Qeq_le (mateS_self p)) htw

-- ===========================================================================
-- (3) THE DIVISION-FREE READING AND ITS FINITE AFFINE COMBINATIONS: every admissible reading IS `U(n,t)`.
-- ===========================================================================

/-- The band hypotheses of a coupling address for the weight law: both scales in `[c, B]`. -/
structure AddrBand (C : NormCtx) (c : CouplingAddr) : Prop where
  hnc : Rle (ofQ (canonC C) (canonC_den C)) c.fin.n.r
  hnB : Rle c.fin.n.r (ofQ (canonB C) (canonB_den C))
  hxc : Rle (ofQ (canonC C) (canonC_den C)) c.arch.xr
  hxB : Rle c.arch.xr (ofQ (canonB C) (canonB_den C))

/-- **The division-free reading** of the prime-scale value from the Archimedean leg:
    `readW c z = invSq(n)·(invSq(x)·(x·U x s))` — the `1/invSq(x)` of the orbit law realized as `invSq(x)·x`. -/
def readW (C : NormCtx) (c : CouplingAddr) (z : SourceField) : Real :=
  Rmul (invSq C c.fin.n.r) (Rmul (invSq C c.arch.xr) (Rmul c.arch.xr (z.U c.arch.xr c.arch.sr)))

/-- `a·(b·(x·u)) ≈ b·(x·(a·u))`. -/
theorem perm4_sc (a b x u : Real) : Req (Rmul a (Rmul b (Rmul x u))) (Rmul b (Rmul x (Rmul a u))) :=
  Req_trans (Req_symm (Rmul_assoc a b (Rmul x u)))
    (Req_trans (Rmul_congr (Rmul_comm a b) (Req_refl (Rmul x u)))
      (Req_trans (Rmul_assoc b a (Rmul x u))
        (Rmul_congr (Req_refl b)
          (Req_trans (Req_symm (Rmul_assoc a x u))
            (Req_trans (Rmul_congr (Rmul_comm a x) (Req_refl u)) (Rmul_assoc x a u))))))

/-- `b·(x·(b'·u)) ≈ ((b·b')·x)·u`. -/
theorem perm4b_sc (b x b' u : Real) : Req (Rmul b (Rmul x (Rmul b' u))) (Rmul (Rmul (Rmul b b') x) u) :=
  Req_trans (Rmul_congr (Req_refl b) (Req_symm (Rmul_assoc x b' u)))
    (Req_trans (Req_symm (Rmul_assoc b (Rmul x b') u))
      (Rmul_congr
        (Req_trans (Req_symm (Rmul_assoc b x b'))
          (Req_trans (Rmul_congr (Rmul_comm b x) (Req_refl b'))
            (Req_trans (Rmul_assoc x b b') (Rmul_comm x (Rmul b b')))))
        (Req_refl u)))

/-- **★ EVERY ADMISSIBLE READING IS THE VALUE ITSELF**: for a coherent field, `readW c z = U n t` on every
    admissible coupling address in the band (orbit law + weight law `(invSq x)²·x = 1`). -/
theorem readW_eq (C : NormCtx) {z : SourceField} (hz : SourceCoherent C z) (c : CouplingAddr)
    (hc : AddrAdmissible C c) (hb : AddrBand C c) :
    Req (readW C c z) (z.U c.fin.n.r c.fin.tr) := by
  obtain ⟨kx, hkx⟩ := Pos_of_Rle_ofQ (canonC_num C) (canonC_den C) hb.hxc
  have horb : Req (Rmul (invSq C c.arch.xr) (z.U c.fin.n.r c.fin.tr)) (Rmul (invSq C c.fin.n.r) (z.U c.arch.xr c.arch.sr)) :=
    coherent_orbit_addr C hz c hc
  have hw : Req (Rmul (Rmul (invSq C c.arch.xr) (invSq C c.arch.xr)) c.arch.xr) one := invSq_sq_mul_self C hb.hxc hb.hxB hkx
  have h1 := perm4_sc (invSq C c.fin.n.r) (invSq C c.arch.xr) c.arch.xr (z.U c.arch.xr c.arch.sr)
  have h2 := perm4b_sc (invSq C c.arch.xr) c.arch.xr (invSq C c.arch.xr) (z.U c.fin.n.r c.fin.tr)
  unfold readW
  refine Req_trans h1 ?_
  refine Req_trans (Rmul_congr (Req_refl (invSq C c.arch.xr)) (Rmul_congr (Req_refl c.arch.xr) (Req_symm horb))) ?_
  refine Req_trans h2 ?_
  exact Req_trans (Rmul_congr hw (Req_refl _)) (Rone_mul _)

/-- A FINITE AFFINE ORBIT READING: `N` point evaluations at coupling addresses `c i` with the same finite leg, with
    weights `θ i` summing to `1` (no cells, no `dx/x` integration, no positivity, no norm — not a step density). -/
def finiteAffineRead (C : NormCtx) (N : Nat) (c : Nat → CouplingAddr) (θ : Nat → Real) (z : SourceField) : Real :=
  RsumN (fun i => Rmul (θ i) (readW C (c i) z)) N

/-- **★ Every finite affine combination of admissible readings reproduces `U n t`** on a coherent field. -/
theorem finiteAffineRead_reproduces (C : NormCtx) {z : SourceField} (hz : SourceCoherent C z) (N : Nat)
    (c : Nat → CouplingAddr) (θ : Nat → Real) (p : FiniteLocalAddr)
    (hfin : ∀ i, i < N → (c i).fin = p) (hadm : ∀ i, i < N → AddrAdmissible C (c i)) (hband : ∀ i, i < N → AddrBand C (c i))
    (hθ : Req (RsumN θ N) one) :
    Req (finiteAffineRead C N c θ z) (z.U p.n.r p.tr) := by
  unfold finiteAffineRead
  have h : ∀ i, i < N → Req (Rmul (θ i) (readW C (c i) z)) (Rmul (θ i) (z.U p.n.r p.tr)) := by
    intro i hi
    have e := readW_eq C hz (c i) (hadm i hi) (hband i hi)
    rw [hfin i hi] at e
    exact Rmul_congr (Req_refl _) e
  refine Req_trans (RsumN_congr N h) ?_
  refine Req_trans (RsumN_smul_right_ai _ _ N) ?_
  exact Req_trans (Rmul_congr hθ (Req_refl _)) (Rone_mul _)

end UOR.Bridge.F1Square.Square
