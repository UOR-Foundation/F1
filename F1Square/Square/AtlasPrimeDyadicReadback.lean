/-
F1 square — **THE DYADIC ATLAS READBACK OF THE PRIME FORM** (`AtlasPrimeDyadicReadback.lean`).

THE COMPLETE-STAGE BLOCK-GROUPED SCALAR READBACK.  For a context `C` (window `[a, a+w]`, cutoff `X`),
every place `m < X`, both scale sides (`q = m+1` and `q = 1/(m+1)`), and every dyadic point of the
certified Haar integral, one ATOM is sourced from the raw `reflectTest`/`dilateTest` Haar evaluations

    `u(f) = (reflect_a (dilate_q f))(y) = f(q / max(y,a))`,   `v(g) = (reflect_a g)(y) = g(1 / max(y,a))`,

at the dyadic point `y = a + w·i/2^k`, with the quadrature coefficient placed INSIDE the atom,
`c = κ · 2^{-k} · (1/max(y,a))` (`κ = Λ(m+1)·q^{-1/2}·w`, resp. `Λ(m+1)·(m+1)^{-1}·q^{-1/2}·w`):

    `Γ_{s,m,side,t}(f) = p(A_f) + q(B_f)`   (`atomOf`, `atlasCoeff`),   `A_f = (c·u(f) − v(f))/4`,  `B_f = (c·u(f) + v(f))/4`.

The atoms are grouped by STAGE `s`: stage `0` is the anchor (one atom per place/side at the
partition `2^0`), stage `s+1` carries the signed fine/coarse atoms of the telescoping increment
`dyadicR(·, s+1) − dyadicR(·, s)` (fine atoms with `+κ`, coarse atoms with `−κ`).  The partial sums
below are taken at COMPLETE-STAGE endpoints only: this is a prescribed block telescoping of scalar
values, NOT convergence of an atom-by-atom series, and NOT a completed Atlas vector (the cut and
cycle masses of the individual atoms are not summable — e.g. at `Λ(1) = 0` the coefficient is `c = 0`,
so `A = −v/4`, `B = v/4`, and each atom has cut mass `4A² = v²/4` and cycle mass `4B² = v²/4` with zero net
energy).  The positive-measure direct-integral realization
of the prime form with a single weight-free field is `AtlasPrimeDirect.lean`.
THE RESULTS.
 * `gammaPartial_readback` — THE EXACT ALL-PAIRS PARTIAL-SUM READBACK: for every pair of tests
   (no core hypothesis) the partial sum through stage `S` of `⟨Γf, MΓg⟩` equals the symmetrized
   dyadic approximation `−½·Σ_{m,side} κ·(D_S(F_{fg}) + D_S(F_{gf}))`, `D_S = dyadicR(·, S)` of the
   pulled-back Haar integrands.
 * `gammaPartial_eq_dyadicR` — that value is the dyadic Riemann sum of ONE combined integrand `G`.
 * `gammaLimit_eq` — THE BISHOP LIMIT: along the certified schedule the partial sums converge, and
   the limit is `−½·(PrimeForm_X(f,g) + PrimeForm_X(g,f))` for ALL tests.
 * `gammaLimit_eq_neg_PrimeForm` — on the fixed core `ClosedCore C` (where `PrimeForm` is symmetric)
   the block-grouped limit is exactly `−PrimeForm_X(f,g)` (a scalar identification only).

The negative prime contribution arises from the `−I` (cycle) term inside the ONE mixed expression
`⟨BΓf, BΓg⟩ − ⟨Γf, Γg⟩ = ⟨Γf, MΓg⟩` (the atomic identity `gammaAtom_readback`), not as a separate stage.
HONEST SCOPE: an indefinite readback of the prime component.  Nothing here is a positivity statement,
a contraction, a range law, or a bound on `CoupledForm`; `CurrentArchDominatesPrime` is untouched.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasGammaAtom
import F1Square.Square.IntegralFiniteLin
import F1Square.Square.WeilGeom
import F1Square.Square.AtlasConservation

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

attribute [local irreducible] RsumN

-- ===========================================================================
-- (1) The raw Haar evaluations and the pulled-back integrand of `H_q(f,g)`.
-- ===========================================================================

/-- One place/side datum: the scale `q` with its positivity certificates and the sourced weight `κ`. -/
structure PlaceDatum where
  q : Q
  hqn : 0 < q.num
  hqd : 0 < q.den
  κ : Real

/-- `u(f)(y) = (reflect_a (dilate_q f))(y)` — the raw dilation/reflection Haar evaluation. -/
def uEv (C : NormCtx) (pd : PlaceDatum) (f : L2Test) (y : Real) : Real :=
  (reflectTest C.a C.han C.had (dilateTest pd.q pd.hqn pd.hqd f)).f y

/-- `v(g)(y) = (reflect_a g)(y)` — the raw reflection Haar evaluation. -/
def vEv (C : NormCtx) (g : L2Test) (y : Real) : Real := (reflectTest C.a C.han C.had g).f y

/-- The Haar density `1/max(y, a)` at `y`. -/
def rEv (C : NormCtx) (y : Real) : Real := (recipTest C.a C.han C.had).f y

/-- The Haar-form product test `φ = (reflect_a (dilate_q f)) · (reflect_a g)`. -/
def haarProd (C : NormCtx) (pd : PlaceDatum) (f g : L2Test) : L2Test :=
  productTest (reflectTest C.a C.han C.had (dilateTest pd.q pd.hqn pd.hqd f)) (reflectTest C.a C.han C.had g)

/-- The pulled-back integrand of `H_q(f,g)` on `[0,1]`: `x ↦ u(f)(y)·v(g)(y)·(1/max(y,a))`, `y = a + w·x`. -/
def hInt (C : NormCtx) (pd : PlaceDatum) (f g : L2Test) (x : Real) : Real :=
  Rmul (Rmul (uEv C pd f (affineMap C.a C.w C.had C.hw x)) (vEv C g (affineMap C.a C.w C.had C.hw x)))
       (rEv C (affineMap C.a C.w C.had C.hw x))

/-- The modulus of the pulled-back integrand (the certified integral's own). -/
def hIntL (C : NormCtx) (pd : PlaceDatum) (f g : L2Test) : Q :=
  mul (l2L (haarProd C pd f g) (recipTest C.a C.han C.had)) C.w

theorem hIntL_den (C : NormCtx) (pd : PlaceDatum) (f g : L2Test) : 0 < (hIntL C pd f g).den :=
  Qmul_den_pos (l2L_den _ _) C.hw

theorem hIntL_num (C : NormCtx) (pd : PlaceDatum) (f g : L2Test) : 0 ≤ (hIntL C pd f g).num :=
  Int.mul_nonneg (l2L_num _ _) C.hwn

theorem hInt_lip (C : NormCtx) (pd : PlaceDatum) (f g : L2Test) : ∀ x y,
    Rle (Rabs (Rsub (hInt C pd f g x) (hInt C pd f g y)))
        (Rmul (ofQ (hIntL C pd f g) (hIntL_den C pd f g)) (Rabs (Rsub x y))) :=
  affine_lip (l2L_den (haarProd C pd f g) (recipTest C.a C.han C.had))
    (l2L_num (haarProd C pd f g) (recipTest C.a C.han C.had))
    (l2lip (haarProd C pd f g) (recipTest C.a C.han C.had)) C.a C.w C.had C.hw C.hwn

theorem hInt_fc (C : NormCtx) (pd : PlaceDatum) (f g : L2Test) : ∀ x y, Req x y →
    Req (hInt C pd f g x) (hInt C pd f g y) :=
  fun x y h => l2fc (haarProd C pd f g) (recipTest C.a C.han C.had) _ _ (affineMap_congr C.a C.w C.had C.hw h)

/-- **`H_q(f,g) = w · ∫₀¹ hInt`** — the Haar form IS the certified integral of the pulled-back
    integrand (definitional: `HForm → mulConv → haarIntegral → innerIonI → riemannIntegralI`). -/
theorem HForm_unfold (C : NormCtx) (pd : PlaceDatum) (f g : L2Test) :
    HForm f g pd.q pd.hqn pd.hqd C.a C.han C.had C.w C.hw C.hwn
      = Rmul (ofQ C.w C.hw)
          (riemannIntegral (hIntL_den C pd f g) (hIntL_num C pd f g) (hInt_lip C pd f g) (hInt_fc C pd f g)) := rfl

-- ===========================================================================
-- (2) Dyadic points, atoms, and the per-level readback.
-- ===========================================================================

/-- The `i`-th point of the `(N+1)`-point partition, pulled to the window: `a + w·(i/(N+1))`. -/
def ptN (C : NormCtx) (N i : Nat) : Real :=
  affineMap C.a C.w C.had C.hw (ofQ (⟨(i : Int), N + 1⟩ : Q) (Nat.succ_pos N))

/-- The sourced atom coefficient `c = κ · (1/(N+1)) · (1/max(y_i, a))`. -/
def atomC (C : NormCtx) (κ : Real) (N i : Nat) : Real :=
  Rmul (Rmul κ (ofQ (⟨1, N + 1⟩ : Q) (Nat.succ_pos N))) (rEv C (ptN C N i))

/-- **The atom at (level `N`, point `i`, address `(d,ℓ)`, weight `κ`)**: `Γ(f) = p(A_f) + q(B_f)` from
    the raw evaluations `u(f), v(f)` at `y_i`. -/
def atomGamma (C : NormCtx) (pd : PlaceDatum) (d ℓ : Nat) (κ : Real) (N i : Nat) (f : L2Test) :
    Nat → Nat → Real :=
  gammaAtom d ℓ (atomC C κ N i) (uEv C pd f (ptN C N i)) (vEv C f (ptN C N i))

/-- `(½·((κh)r))·(A + B') ≈ (½κ)·(h·(A·r) + h·(B·r))` with `B' = v u'`, `B = u' v`. -/
theorem atom_pt_alg (κ h r uf vf ug vg : Real) :
    Req (Rmul (Rmul cH (Rmul (Rmul κ h) r)) (Radd (Rmul uf vg) (Rmul vf ug)))
        (Rmul (Rmul cH κ) (Radd (Rmul h (Rmul (Rmul uf vg) r)) (Rmul h (Rmul (Rmul ug vf) r)))) := by
  have hc : Req (Rmul cH (Rmul (Rmul κ h) r)) (Rmul (Rmul (Rmul cH κ) h) r) :=
    Req_trans (Req_symm (Rmul_assoc cH (Rmul κ h) r))
      (Rmul_congr (Req_symm (Rmul_assoc cH κ h)) (Req_refl r))
  have hterm : ∀ A : Real, Req (Rmul (Rmul (Rmul (Rmul cH κ) h) r) A) (Rmul (Rmul cH κ) (Rmul h (Rmul A r))) := by
    intro A
    refine Req_trans (Rmul_assoc _ r A) ?_
    refine Req_trans (Rmul_congr (Req_refl _) (Rmul_comm r A)) ?_
    exact Rmul_assoc _ h (Rmul A r)
  refine Req_trans (Rmul_congr hc (Req_refl _)) ?_
  refine Req_trans (Rmul_distrib _ _ _) ?_
  refine Req_trans (Radd_congr (hterm (Rmul uf vg)) (Req_trans (hterm (Rmul vf ug))
    (Rmul_congr (Req_refl _) (Rmul_congr (Req_refl h) (Rmul_congr (Rmul_comm vf ug) (Req_refl r)))))) ?_
  exact Req_symm (Rmul_distrib _ _ _)

/-- `hInt` at the `i`-th partition point is the product of the raw evaluations at `y_i`. -/
theorem hInt_pt (C : NormCtx) (pd : PlaceDatum) (f g : L2Test) (N i : Nat) :
    hInt C pd f g (ofQ (⟨(i : Int), N + 1⟩ : Q) (Nat.succ_pos N))
      = Rmul (Rmul (uEv C pd f (ptN C N i)) (vEv C g (ptN C N i))) (rEv C (ptN C N i)) := rfl

/-- **THE PER-LEVEL READBACK**: summing the atomic identity over the `(N+1)` partition points,
    `Σ_i ⟨Γ_i f, M Γ_i g⟩ = (−½κ)·(riemannSum (hInt f g) N + riemannSum (hInt g f) N)`. -/
theorem level_readback (C : NormCtx) (pd : PlaceDatum) (d ℓ : Nat) (hd : d < 3) (hℓ : ℓ < 8)
    (κ : Real) (N : Nat) (f g : L2Test) :
    Req (RsumN (fun i => pairF (atomGamma C pd d ℓ κ N i f) (atlasOp (atomGamma C pd d ℓ κ N i g))) (N + 1))
        (Rmul (Rneg (Rmul cH κ)) (Radd (riemannSum (hInt C pd f g) N) (riemannSum (hInt C pd g f) N))) := by
  -- pointwise: the atomic identity, then the algebra
  have hpt : ∀ i, Req (pairF (atomGamma C pd d ℓ κ N i f) (atlasOp (atomGamma C pd d ℓ κ N i g)))
      (Rneg (Rmul (Rmul cH κ) (Radd
        (Rmul (ofQ (⟨1, N + 1⟩ : Q) (Nat.succ_pos N))
          (Rmul (Rmul (uEv C pd f (ptN C N i)) (vEv C g (ptN C N i))) (rEv C (ptN C N i))))
        (Rmul (ofQ (⟨1, N + 1⟩ : Q) (Nat.succ_pos N))
          (Rmul (Rmul (uEv C pd g (ptN C N i)) (vEv C f (ptN C N i))) (rEv C (ptN C N i))))))) := by
    intro i
    refine Req_trans (gammaAtom_readback d ℓ hd hℓ (atomC C κ N i) _ _ _ _) ?_
    exact Rneg_congr (atom_pt_alg κ _ _ _ _ _ _)
  refine Req_trans (RsumN_congr (N + 1) (fun i _ => hpt i)) ?_
  refine Req_trans (RsumN_Rneg _ (N + 1)) ?_
  refine Req_trans (Rneg_congr (RsumN_smul_ai (Rmul cH κ) _ (N + 1))) ?_
  refine Req_trans (Rneg_congr (Rmul_congr (Req_refl _) (RsumN_Radd _ _ (N + 1)))) ?_
  refine Req_trans (Rneg_congr (Rmul_congr (Req_refl _)
    (Radd_congr (RsumN_smul_ai _ _ (N + 1)) (RsumN_smul_ai _ _ (N + 1))))) ?_
  refine Req_trans (Req_symm (Rmul_neg_left _ _)) ?_
  refine Rmul_congr (Req_refl _) (Radd_congr ?_ ?_)
  · exact Rmul_congr (Req_refl _) (RsumN_congr (N + 1) (fun i _ => by rw [hInt_pt]; exact Req_refl _))
  · exact Rmul_congr (Req_refl _) (RsumN_congr (N + 1) (fun i _ => by rw [hInt_pt]; exact Req_refl _))

-- ===========================================================================
-- (3) The place data, the address gauge, and THE FIXED Γ FAMILY.
-- ===========================================================================

/-- The two scale sides of place `m`: `side 0`: `q = m+1`, `κ = Λ(m+1)·(m+1)^{-1/2}·w`;
    `side 1`: `q = 1/(m+1)`, `κ = Λ(m+1)·(m+1)^{-1}·(1/(m+1))^{-1/2}·w`.  All weights sourced
    (`vonMangoldt`, `normWeight`, the window width); no target scalar. -/
def placeData (C : NormCtx) (m : Nat) : Nat → PlaceDatum
  | 0 => ⟨(⟨((m + 1 : Nat) : Int), 1⟩ : Q), Int.ofNat_pos.mpr (Nat.succ_pos m), Nat.one_pos,
          Rmul (Rmul (vonMangoldt (m + 1)) (normWeight (⟨((m + 1 : Nat) : Int), 1⟩ : Q))) (ofQ C.w C.hw)⟩
  | _ => ⟨(⟨1, m + 1⟩ : Q), (show (0 : Int) < 1 by decide), Nat.succ_pos m,
          Rmul (Rmul (Rmul (vonMangoldt (m + 1)) (ofQ (⟨1, m + 1⟩ : Q) (Nat.succ_pos m)))
            (normWeight (⟨1, m + 1⟩ : Q))) (ofQ C.w C.hw)⟩

/-- **The address GAUGE**: the `(d, ℓ)` part of the Atlas class address of the integer `m+1`
    (`classDecode`).  A deterministic choice only — the readback is address-independent
    (`gammaAtom_readback` holds at every valid address); no semantic scale-to-class map is claimed. -/
def primeAddr (m : Nat) : Nat × Nat := ((classDecode (m + 1)).2.1, (classDecode (m + 1)).2.2)

theorem primeAddr_valid (m : Nat) : (primeAddr m).1 < 3 ∧ (primeAddr m).2 < 8 := by
  show ((m + 1) % 24) / 8 < 3 ∧ (m + 1) % 8 < 8
  have h24 : ∀ x : Nat, x < 24 → x / 8 < 3 := by decide
  exact ⟨h24 _ (Nat.mod_lt _ (by decide)), Nat.mod_lt _ (by decide)⟩

/-- The anchor atom (stage `0`): partition `2^0`, point `t`, weight `+κ`. -/
def atomAnchor (C : NormCtx) (m side t : Nat) (f : L2Test) : Nat → Nat → Real :=
  atomGamma C (placeData C m side) (primeAddr m).1 (primeAddr m).2 (placeData C m side).κ 0 t f

/-- The fine atom of stage `s+1`: partition `2^{s+1}`, point `t`, weight `+κ`. -/
def atomFine (C : NormCtx) (s m side t : Nat) (f : L2Test) : Nat → Nat → Real :=
  atomGamma C (placeData C m side) (primeAddr m).1 (primeAddr m).2 (placeData C m side).κ (2 ^ (s + 1) - 1) t f

/-- The coarse atom of stage `s+1`: partition `2^s`, point `j`, weight `−κ`. -/
def atomCoarse (C : NormCtx) (s m side j : Nat) (f : L2Test) : Nat → Nat → Real :=
  atomGamma C (placeData C m side) (primeAddr m).1 (primeAddr m).2 (Rneg (placeData C m side).κ) (2 ^ s - 1) j f

/-- The number of atoms of a stage (per place and side): `1`, then `2^{s+1} + 2^s`. -/
def blockLen : Nat → Nat
  | 0 => 0 + 1
  | (s + 1) => (2 ^ (s + 1) - 1 + 1) + (2 ^ s - 1 + 1)

/-- **The block-grouped atom family** `atomOf C s m side t f` — the atom at stage `s`, place `m`, side `side`,
    offset `t < blockLen s`, evaluated on the raw test `f`.  Stage `0` is the anchor; stage `s+1`
    lists the fine atoms (`t < 2^{s+1}`) then the coarse atoms (signed copies, not a completed vector). -/
def atomOf (C : NormCtx) : Nat → Nat → Nat → Nat → L2Test → Nat → Nat → Real
  | 0, m, side, t, f => atomAnchor C m side t f
  | (s + 1), m, side, t, f =>
      if t < 2 ^ (s + 1) - 1 + 1 then atomFine C s m side t f
      else atomCoarse C s m side (t - (2 ^ (s + 1) - 1 + 1)) f

theorem atomOf_zero (C : NormCtx) (m side t : Nat) (f : L2Test) :
    atomOf C 0 m side t f = atomAnchor C m side t f := rfl

theorem atomOf_succ (C : NormCtx) (s m side t : Nat) (f : L2Test) :
    atomOf C (s + 1) m side t f =
      (if t < 2 ^ (s + 1) - 1 + 1 then atomFine C s m side t f
       else atomCoarse C s m side (t - (2 ^ (s + 1) - 1 + 1)) f) := rfl

/-- **`atlasCoeff`** — the single-test-linear mixed coefficient map of the Atlas fiber (`3 × 8`),
    the raw Γ of the directive: `atlasCoeff C (s, m, side, t) f : Nat → Nat → Real` (indices `i < 3`,
    `j < 8`).  Built from the dilation/reflection Haar evaluations at dyadic scale/address data only;
    for a core test `f : ClosedCore C` use `atlasCoeff C s m side t f.1`. -/
def atlasCoeff (C : NormCtx) (s m side t : Nat) (f : L2Test) : Nat → Nat → Real := atomOf C s m side t f

-- ---------------------------------------------------------------------------
-- Single-test linearity of the family.
-- ---------------------------------------------------------------------------

theorem uEv_add (C : NormCtx) (pd : PlaceDatum) (f g : L2Test) (y : Real) :
    uEv C pd (L2Test.add f g) y = Radd (uEv C pd f y) (uEv C pd g y) := rfl
theorem vEv_add (C : NormCtx) (f g : L2Test) (y : Real) :
    vEv C (L2Test.add f g) y = Radd (vEv C f y) (vEv C g y) := rfl
theorem uEv_neg (C : NormCtx) (pd : PlaceDatum) (f : L2Test) (y : Real) :
    uEv C pd (L2Test.neg f) y = Rneg (uEv C pd f y) := rfl
theorem vEv_neg (C : NormCtx) (f : L2Test) (y : Real) :
    vEv C (L2Test.neg f) y = Rneg (vEv C f y) := rfl

theorem atomGamma_add (C : NormCtx) (pd : PlaceDatum) (d ℓ : Nat) (κ : Real) (N i : Nat) (f g : L2Test)
    (a b : Nat) :
    Req (atomGamma C pd d ℓ κ N i (L2Test.add f g) a b)
        (Radd (atomGamma C pd d ℓ κ N i f a b) (atomGamma C pd d ℓ κ N i g a b)) := by
  unfold atomGamma
  rw [uEv_add, vEv_add]
  exact gammaAtom_add d ℓ _ _ _ _ _ a b

theorem atomGamma_neg (C : NormCtx) (pd : PlaceDatum) (d ℓ : Nat) (κ : Real) (N i : Nat) (f : L2Test)
    (a b : Nat) :
    Req (atomGamma C pd d ℓ κ N i (L2Test.neg f) a b) (Rneg (atomGamma C pd d ℓ κ N i f a b)) := by
  unfold atomGamma
  rw [uEv_neg, vEv_neg]
  exact gammaAtom_neg d ℓ _ _ _ a b

/-- **Additivity of Γ in the test** (`Γ(f + g) = Γ(f) + Γ(g)` entrywise). -/
theorem atlasCoeff_add (C : NormCtx) (s m side t : Nat) (f g : L2Test) (a b : Nat) :
    Req (atlasCoeff C s m side t (L2Test.add f g) a b)
        (Radd (atlasCoeff C s m side t f a b) (atlasCoeff C s m side t g a b)) := by
  unfold atlasCoeff
  cases s with
  | zero => exact atomGamma_add C _ _ _ _ _ _ f g a b
  | succ s =>
      rw [atomOf_succ, atomOf_succ, atomOf_succ]
      by_cases ht : t < 2 ^ (s + 1) - 1 + 1
      · rw [if_pos ht, if_pos ht, if_pos ht]; exact atomGamma_add C _ _ _ _ _ _ f g a b
      · rw [if_neg ht, if_neg ht, if_neg ht]; exact atomGamma_add C _ _ _ _ _ _ f g a b

/-- **Negation of Γ in the test**. -/
theorem atlasCoeff_neg (C : NormCtx) (s m side t : Nat) (f : L2Test) (a b : Nat) :
    Req (atlasCoeff C s m side t (L2Test.neg f) a b) (Rneg (atlasCoeff C s m side t f a b)) := by
  unfold atlasCoeff
  cases s with
  | zero => exact atomGamma_neg C _ _ _ _ _ _ f a b
  | succ s =>
      rw [atomOf_succ, atomOf_succ]
      by_cases ht : t < 2 ^ (s + 1) - 1 + 1
      · rw [if_pos ht, if_pos ht]; exact atomGamma_neg C _ _ _ _ _ _ f a b
      · rw [if_neg ht, if_neg ht]; exact atomGamma_neg C _ _ _ _ _ _ f a b

-- ===========================================================================
-- (4) Stage sums and THE EXACT PARTIAL-SUM READBACK.
-- ===========================================================================

/-- The signed half-weight `ω = −½·κ` of a place/side. -/
def omegaW (C : NormCtx) (m side : Nat) : Real := Rneg (Rmul cH (placeData C m side).κ)

/-- The pairing sum over one stage block (fixed place and side). -/
def blockPair (C : NormCtx) (f g : L2Test) (s m side : Nat) : Real :=
  RsumN (fun t => pairF (atomOf C s m side t f) (atlasOp (atomOf C s m side t g))) (blockLen s)

/-- The pairing sum over a whole stage. -/
def stageSum (C : NormCtx) (f g : L2Test) (s : Nat) : Real :=
  RsumN (fun m => RsumN (fun side => blockPair C f g s m side) 2) C.X

/-- **The partial sums of the Γ readback** over the stages `< S`:
    `Σ_{s<S} Σ_{m<X} Σ_{side<2} Σ_{t<blockLen s} ⟨Γ_{s,m,side,t} f, M Γ_{s,m,side,t} g⟩`. -/
def gammaPartial (C : NormCtx) (f g : L2Test) (S : Nat) : Real := RsumN (fun s => stageSum C f g s) S

/-- The symmetrized dyadic approximation at level `S`:
    `Σ_{m,side} ω_{m,side}·(D_S(hInt f g) + D_S(hInt g f))`. -/
def symDyad (C : NormCtx) (f g : L2Test) (S : Nat) : Real :=
  RsumN (fun m => RsumN (fun side => Rmul (omegaW C m side)
    (Radd (dyadicR (hInt C (placeData C m side) f g) S) (dyadicR (hInt C (placeData C m side) g f) S))) 2) C.X

/-- The anchor block reads back the level-`0` sums. -/
theorem blockPair_zero (C : NormCtx) (f g : L2Test) (m side : Nat) :
    Req (blockPair C f g 0 m side)
        (Rmul (omegaW C m side)
          (Radd (dyadicR (hInt C (placeData C m side) f g) 0) (dyadicR (hInt C (placeData C m side) g f) 0))) := by
  obtain ⟨hd, hℓ⟩ := primeAddr_valid m
  exact level_readback C (placeData C m side) (primeAddr m).1 (primeAddr m).2 hd hℓ (placeData C m side).κ 0 f g

/-- `−½(−κ) = −ω`. -/
theorem omegaW_neg (C : NormCtx) (m side : Nat) :
    Req (Rneg (Rmul cH (Rneg (placeData C m side).κ))) (Rneg (omegaW C m side)) :=
  Rneg_congr (Rmul_neg_right cH _)

/-- The stage-`(s+1)` block reads back the telescoping increment:
    `ω·(dyadicTerm (hInt f g) s + dyadicTerm (hInt g f) s)`. -/
theorem blockPair_succ (C : NormCtx) (f g : L2Test) (s m side : Nat) :
    Req (blockPair C f g (s + 1) m side)
        (Rmul (omegaW C m side)
          (Radd (dyadicTerm (hInt C (placeData C m side) f g) s) (dyadicTerm (hInt C (placeData C m side) g f) s))) := by
  obtain ⟨hd, hℓ⟩ := primeAddr_valid m
  unfold blockPair
  show Req (RsumN (fun t => pairF (atomOf C (s + 1) m side t f) (atlasOp (atomOf C (s + 1) m side t g)))
      ((2 ^ (s + 1) - 1 + 1) + (2 ^ s - 1 + 1))) _
  refine Req_trans (RsumN_add_block_ai _ (2 ^ (s + 1) - 1 + 1) (2 ^ s - 1 + 1)) ?_
  -- fine block
  have hfine : Req (RsumN (fun t => pairF (atomOf C (s + 1) m side t f) (atlasOp (atomOf C (s + 1) m side t g)))
      (2 ^ (s + 1) - 1 + 1))
      (Rmul (Rneg (Rmul cH (placeData C m side).κ))
        (Radd (riemannSum (hInt C (placeData C m side) f g) (2 ^ (s + 1) - 1))
              (riemannSum (hInt C (placeData C m side) g f) (2 ^ (s + 1) - 1)))) := by
    refine Req_trans (RsumN_congr (G := fun t => pairF (atomFine C s m side t f) (atlasOp (atomFine C s m side t g)))
      (2 ^ (s + 1) - 1 + 1) (fun t ht => ?_)) ?_
    · rw [atomOf_succ, atomOf_succ, if_pos ht, if_pos ht]; exact Req_refl _
    · exact level_readback C (placeData C m side) (primeAddr m).1 (primeAddr m).2 hd hℓ
        (placeData C m side).κ (2 ^ (s + 1) - 1) f g
  -- coarse block
  have hcoarse : Req (RsumN (fun j => pairF (atomOf C (s + 1) m side ((2 ^ (s + 1) - 1 + 1) + j) f)
        (atlasOp (atomOf C (s + 1) m side ((2 ^ (s + 1) - 1 + 1) + j) g))) (2 ^ s - 1 + 1))
      (Rmul (Rneg (Rmul cH (Rneg (placeData C m side).κ)))
        (Radd (riemannSum (hInt C (placeData C m side) f g) (2 ^ s - 1))
              (riemannSum (hInt C (placeData C m side) g f) (2 ^ s - 1)))) := by
    refine Req_trans (RsumN_congr (G := fun j => pairF (atomCoarse C s m side j f) (atlasOp (atomCoarse C s m side j g)))
      (2 ^ s - 1 + 1) (fun j _ => ?_)) ?_
    · have hnl : ¬ ((2 ^ (s + 1) - 1 + 1) + j < 2 ^ (s + 1) - 1 + 1) := by omega
      rw [atomOf_succ, atomOf_succ, if_neg hnl, if_neg hnl, Nat.add_sub_cancel_left]; exact Req_refl _
    · exact level_readback C (placeData C m side) (primeAddr m).1 (primeAddr m).2 hd hℓ
        (Rneg (placeData C m side).κ) (2 ^ s - 1) f g
  refine Req_trans (Radd_congr hfine hcoarse) ?_
  refine Req_trans (Radd_congr (Req_refl _) (Rmul_congr (omegaW_neg C m side) (Req_refl _))) ?_
  refine Req_trans (Radd_congr (Req_refl _) (Rmul_neg_left _ _)) ?_
  -- ω·(D₁ + D₁') − ω·(D₀ + D₀') = ω·((D₁ − D₀) + (D₁' − D₀'))
  refine Req_trans (Req_symm (Rmul_sub_distrib (omegaW C m side) _ _)) ?_
  exact Rmul_congr (Req_refl _) (Rsub_Radd_Radd _ _ _ _)

theorem stageSum_zero (C : NormCtx) (f g : L2Test) : Req (stageSum C f g 0) (symDyad C f g 0) :=
  RsumN_congr C.X (fun m _ => RsumN_congr 2 (fun side _ => blockPair_zero C f g m side))

/-- `(D + D') + ((D₁ − D) + (D₁' − D')) ≈ D₁ + D₁'`. -/
theorem tele_step_alg (D D' D₁ D₁' : Real) :
    Req (Radd (Radd D D') (Radd (Rsub D₁ D) (Rsub D₁' D'))) (Radd D₁ D₁') := by
  refine Req_trans (Radd_swap _ _ _ _) (Radd_congr ?_ ?_)
  · exact Req_trans (Radd_comm _ _) (Req_trans (Radd_assoc D₁ (Rneg D) D)
      (Req_trans (Radd_congr (Req_refl D₁) (Req_trans (Radd_comm _ _) (Radd_neg D))) (Radd_zero D₁)))
  · exact Req_trans (Radd_comm _ _) (Req_trans (Radd_assoc D₁' (Rneg D') D')
      (Req_trans (Radd_congr (Req_refl D₁') (Req_trans (Radd_comm _ _) (Radd_neg D'))) (Radd_zero D₁')))

/-- **★ THE EXACT ALL-PAIRS PARTIAL-SUM READBACK**: for ALL tests `f, g` and every stage `S`, the
    partial sum of the Γ pairings through stage `S` is the symmetrized dyadic approximation
    `Σ_{m,side} (−½κ)·(D_S(hInt f g) + D_S(hInt g f))`. -/
theorem gammaPartial_readback (C : NormCtx) (f g : L2Test) :
    ∀ S, Req (gammaPartial C f g (S + 1)) (symDyad C f g S)
  | 0 => by
      show Req (RsumN (fun s => stageSum C f g s) (0 + 1)) _
      rw [RsumN_succ_fl, RsumN_zero_fl]
      exact Req_trans (Req_trans (Radd_comm _ _) (Radd_zero _)) (stageSum_zero C f g)
  | (S + 1) => by
      show Req (RsumN (fun s => stageSum C f g s) (S + 1 + 1)) _
      rw [RsumN_succ_fl]
      refine Req_trans (Radd_congr (gammaPartial_readback C f g S)
        (RsumN_congr (G := fun m => RsumN (fun side => Rmul (omegaW C m side)
          (Radd (dyadicTerm (hInt C (placeData C m side) f g) S)
                (dyadicTerm (hInt C (placeData C m side) g f) S))) 2) C.X
          (fun m _ => RsumN_congr 2 (fun side _ => blockPair_succ C f g S m side)))) ?_
      unfold symDyad
      refine Req_trans (Req_symm (RsumN_Radd _ _ C.X)) (RsumN_congr C.X (fun m _ => ?_))
      refine Req_trans (Req_symm (RsumN_Radd _ _ 2)) (RsumN_congr 2 (fun side _ => ?_))
      refine Req_trans (Req_symm (Rmul_distrib _ _ _)) (Rmul_congr (Req_refl _) ?_)
      exact tele_step_alg _ _ _ _

-- ===========================================================================
-- (5) The combined integrand `G` and its certificates.
-- ===========================================================================

/-- The place/side term of the combined integrand: `ω·(hInt f g + hInt g f)`. -/
def gTerm (C : NormCtx) (f g : L2Test) (m side : Nat) (x : Real) : Real :=
  Rmul (omegaW C m side) (Radd (hInt C (placeData C m side) f g x) (hInt C (placeData C m side) g f x))

/-- **The combined integrand** `G = Σ_{m<X} Σ_{side<2} ω_{m,side}·(hInt f g + hInt g f)`. -/
def Gint (C : NormCtx) (f g : L2Test) (x : Real) : Real :=
  RsumN (fun m => RsumN (fun side => gTerm C f g m side x) 2) C.X

def pairL (C : NormCtx) (f g : L2Test) (m side : Nat) : Q :=
  add (hIntL C (placeData C m side) f g) (hIntL C (placeData C m side) g f)
theorem pairL_den (C : NormCtx) (f g : L2Test) (m side : Nat) : 0 < (pairL C f g m side).den :=
  add_den_pos (hIntL_den _ _ _ _) (hIntL_den _ _ _ _)
theorem pairL_num (C : NormCtx) (f g : L2Test) (m side : Nat) : 0 ≤ (pairL C f g m side).num :=
  Qadd_num_nonneg_loc (hIntL_num _ _ _ _) (hIntL_num _ _ _ _)

theorem pair_lip (C : NormCtx) (f g : L2Test) (m side : Nat) : ∀ x y,
    Rle (Rabs (Rsub (Radd (hInt C (placeData C m side) f g x) (hInt C (placeData C m side) g f x))
                    (Radd (hInt C (placeData C m side) f g y) (hInt C (placeData C m side) g f y))))
        (Rmul (ofQ (pairL C f g m side) (pairL_den C f g m side)) (Rabs (Rsub x y))) :=
  lip_add_fl (hIntL_den _ _ _ _) (hIntL_den _ _ _ _) (hInt_lip _ _ _ _) (hInt_lip _ _ _ _)
theorem pair_fc (C : NormCtx) (f g : L2Test) (m side : Nat) : ∀ x y, Req x y →
    Req (Radd (hInt C (placeData C m side) f g x) (hInt C (placeData C m side) g f x))
        (Radd (hInt C (placeData C m side) f g y) (hInt C (placeData C m side) g f y)) :=
  fun x y h => Radd_congr (hInt_fc _ _ _ _ x y h) (hInt_fc _ _ _ _ x y h)

def termL (C : NormCtx) (f g : L2Test) (m side : Nat) : Q := mul (xBQ (omegaW C m side)) (pairL C f g m side)
theorem termL_den (C : NormCtx) (f g : L2Test) (m side : Nat) : 0 < (termL C f g m side).den :=
  Qmul_den_pos Nat.one_pos (pairL_den C f g m side)
theorem termL_num (C : NormCtx) (f g : L2Test) (m side : Nat) : 0 ≤ (termL C f g m side).num :=
  Qmul_num_nonneg (xBQ_num_nonneg _) (pairL_num C f g m side)

theorem term_lip (C : NormCtx) (f g : L2Test) (m side : Nat) : ∀ x y,
    Rle (Rabs (Rsub (gTerm C f g m side x) (gTerm C f g m side y)))
        (Rmul (ofQ (termL C f g m side) (termL_den C f g m side)) (Rabs (Rsub x y))) :=
  lip_smul_fl (omegaW C m side) (pairL_den C f g m side) (pairL_num C f g m side) (pair_lip C f g m side)
theorem term_fc (C : NormCtx) (f g : L2Test) (m side : Nat) : ∀ x y, Req x y →
    Req (gTerm C f g m side x) (gTerm C f g m side y) :=
  fc_smul_fl (omegaW C m side) (pair_fc C f g m side)

def innerL (C : NormCtx) (f g : L2Test) (m : Nat) : Q := QsumN (termL C f g m) 2
theorem innerL_den (C : NormCtx) (f g : L2Test) (m : Nat) : 0 < (innerL C f g m).den :=
  QsumN_den_pos _ (termL_den C f g m) 2
theorem innerL_num (C : NormCtx) (f g : L2Test) (m : Nat) : 0 ≤ (innerL C f g m).num :=
  QsumN_num_nonneg _ (termL_num C f g m) 2

theorem inner_lip (C : NormCtx) (f g : L2Test) (m : Nat) : ∀ x y,
    Rle (Rabs (Rsub (RsumN (fun side => gTerm C f g m side x) 2) (RsumN (fun side => gTerm C f g m side y) 2)))
        (Rmul (ofQ (innerL C f g m) (innerL_den C f g m)) (Rabs (Rsub x y))) :=
  lip_RsumN_fl (fun side x => gTerm C f g m side x) (termL C f g m) (termL_den C f g m) (term_lip C f g m) 2
theorem inner_fc (C : NormCtx) (f g : L2Test) (m : Nat) : ∀ x y, Req x y →
    Req (RsumN (fun side => gTerm C f g m side x) 2) (RsumN (fun side => gTerm C f g m side y) 2) :=
  fc_RsumN_fl (fun side x => gTerm C f g m side x) (term_fc C f g m) 2

/-- **The sourced decay constant of the whole family**: `K = Σ_{m<X} Σ_{side<2} xBound(ω)·(L_{fg} + L_{gf})`. -/
def KG (C : NormCtx) (f g : L2Test) : Q := QsumN (fun m => innerL C f g m) C.X
theorem KG_den (C : NormCtx) (f g : L2Test) : 0 < (KG C f g).den :=
  QsumN_den_pos _ (innerL_den C f g) C.X
theorem KG_num (C : NormCtx) (f g : L2Test) : 0 ≤ (KG C f g).num :=
  QsumN_num_nonneg _ (innerL_num C f g) C.X

theorem G_lip (C : NormCtx) (f g : L2Test) : ∀ x y,
    Rle (Rabs (Rsub (Gint C f g x) (Gint C f g y))) (Rmul (ofQ (KG C f g) (KG_den C f g)) (Rabs (Rsub x y))) :=
  lip_RsumN_fl (fun m x => RsumN (fun side => gTerm C f g m side x) 2) (fun m => innerL C f g m)
    (innerL_den C f g) (inner_lip C f g) C.X
theorem G_fc (C : NormCtx) (f g : L2Test) : ∀ x y, Req x y → Req (Gint C f g x) (Gint C f g y) :=
  fc_RsumN_fl (fun m x => RsumN (fun side => gTerm C f g m side x) 2) (inner_fc C f g) C.X

/-- **The symmetrized dyadic approximation IS the dyadic Riemann sum of `G`**. -/
theorem dyadicR_G (C : NormCtx) (f g : L2Test) (S : Nat) :
    Req (dyadicR (Gint C f g) S) (symDyad C f g S) := by
  show Req (riemannSum (Gint C f g) (2 ^ S - 1)) _
  refine Req_trans (riemannSum_RsumN_fl (fun m x => RsumN (fun side => gTerm C f g m side x) 2) (2 ^ S - 1) C.X) ?_
  refine RsumN_congr C.X (fun m _ => ?_)
  refine Req_trans (riemannSum_RsumN_fl (fun side x => gTerm C f g m side x) (2 ^ S - 1) 2) ?_
  refine RsumN_congr 2 (fun side _ => ?_)
  refine Req_trans (riemannSum_smul (omegaW C m side)
    (fun x => Radd (hInt C (placeData C m side) f g x) (hInt C (placeData C m side) g f x)) (2 ^ S - 1)) ?_
  exact Rmul_congr (Req_refl _) (riemannSum_add _ _ (2 ^ S - 1))

/-- **`gammaPartial_eq_dyadicR`**: the partial sum through stage `S` is `D_S(G)`. -/
theorem gammaPartial_eq_dyadicR (C : NormCtx) (f g : L2Test) (S : Nat) :
    Req (gammaPartial C f g (S + 1)) (dyadicR (Gint C f g) S) :=
  Req_trans (gammaPartial_readback C f g S) (Req_symm (dyadicR_G C f g S))

-- ===========================================================================
-- (6) THE BISHOP LIMIT.
-- ===========================================================================

/-- The certified schedule of the family (the `digammaMidx` schedule of its decay constant `K`). -/
def gammaSched (C : NormCtx) (f g : L2Test) (j : Nat) : Nat := digammaMidx (KG C f g) j

/-- The partial sums along the schedule. -/
def gammaSeq (C : NormCtx) (f g : L2Test) (j : Nat) : Real := gammaPartial C f g (gammaSched C f g j + 1)

theorem add_sub_cancel_pd (D₀ D : Real) : Req (Radd D₀ (Rsub D D₀)) D := by
  refine Req_trans (Radd_comm _ _) (Req_trans (Radd_assoc D (Rneg D₀) D₀) ?_)
  exact Req_trans (Radd_congr (Req_refl D) (Req_trans (Radd_comm _ _) (Radd_neg D₀))) (Radd_zero D)

theorem gammaSeq_eq (C : NormCtx) (f g : L2Test) (j : Nat) :
    Req (gammaSeq C f g j)
        (Radd (dyadicR (Gint C f g) 0) (genSum (dyadicTerm (Gint C f g)) (gammaSched C f g j))) := by
  refine Req_trans (gammaPartial_eq_dyadicR C f g (gammaSched C f g j)) ?_
  refine Req_symm (Req_trans (Radd_congr (Req_refl _) (genSum_telescope (Gint C f g) (gammaSched C f g j))) ?_)
  exact add_sub_cancel_pd _ _

theorem tailReg (C : NormCtx) (f g : L2Test) :
    RReg (fun j => genSum (dyadicTerm (Gint C f g)) (gammaSched C f g j)) :=
  dyadicSum_RReg (KG_den C f g) (KG_num C f g) (G_lip C f g) (G_fc C f g)

/-- **The partial sums along the schedule form a regular (Bishop-convergent) sequence.** -/
theorem gammaSeq_RReg (C : NormCtx) (f g : L2Test) : RReg (gammaSeq C f g) :=
  RReg_congr_fl (gammaSeq_eq C f g) (RReg_add_const _ _ (tailReg C f g))

/-- **The block-grouped Γ limit** `lim_S Σ_{stages<S} Σ ⟨Γf, MΓg⟩` along complete-stage endpoints — a
    genuine constructive real (a scalar; no completed Atlas vector is asserted). -/
def gammaLimit (C : NormCtx) (f g : L2Test) : Real := Rlim (gammaSeq C f g) (gammaSeq_RReg C f g)

/-- The Γ limit is the certified integral of the combined integrand. -/
theorem gammaLimit_eq_integral (C : NormCtx) (f g : L2Test) :
    Req (gammaLimit C f g) (riemannIntegral (KG_den C f g) (KG_num C f g) (G_lip C f g) (G_fc C f g)) :=
  Req_trans (Rlim_congr _ _ (gammaSeq_RReg C f g) (RReg_add_const _ _ (tailReg C f g)) (gammaSeq_eq C f g))
    (Rlim_add_const _ _ (tailReg C f g) (RReg_add_const _ _ (tailReg C f g)))

/-- `∫₀¹ hInt f g + hInt g f = ∫ hInt f g + ∫ hInt g f`. -/
theorem integral_pair (C : NormCtx) (f g : L2Test) (m side : Nat) :
    Req (riemannIntegral (pairL_den C f g m side) (pairL_num C f g m side) (pair_lip C f g m side) (pair_fc C f g m side))
        (Radd (riemannIntegral (hIntL_den C (placeData C m side) f g) (hIntL_num _ _ _ _) (hInt_lip _ _ _ _) (hInt_fc _ _ _ _))
              (riemannIntegral (hIntL_den C (placeData C m side) g f) (hIntL_num _ _ _ _) (hInt_lip _ _ _ _) (hInt_fc _ _ _ _))) := by
  have hf := lip_weaken_fl (hIntL_den C (placeData C m side) f g) (pairL_den C f g m side)
    (Qle_add_right_nonneg (hIntL_num C (placeData C m side) g f)) (hInt_lip C (placeData C m side) f g)
  have hg := lip_weaken_fl (hIntL_den C (placeData C m side) g f) (pairL_den C f g m side)
    (Qle_add_left_nonneg (hIntL_num C (placeData C m side) f g)) (hInt_lip C (placeData C m side) g f)
  refine Req_trans (riemannIntegral_add (pairL_den C f g m side) (pairL_num C f g m side)
    hf (hInt_fc _ _ _ _) hg (hInt_fc _ _ _ _) (pair_lip C f g m side) (pair_fc C f g m side)) ?_
  exact Radd_congr
    (riemannIntegral_certif_irrel _ _ hf _ (hIntL_den _ _ _ _) (hIntL_num _ _ _ _) (hInt_lip _ _ _ _) (hInt_fc _ _ _ _))
    (riemannIntegral_certif_irrel _ _ hg _ (hIntL_den _ _ _ _) (hIntL_num _ _ _ _) (hInt_lip _ _ _ _) (hInt_fc _ _ _ _))

/-- The integral of `G` is the weighted sum of the Haar integrals. -/
theorem integral_G (C : NormCtx) (f g : L2Test) :
    Req (riemannIntegral (KG_den C f g) (KG_num C f g) (G_lip C f g) (G_fc C f g))
        (RsumN (fun m => RsumN (fun side => Rmul (omegaW C m side)
          (Radd (riemannIntegral (hIntL_den C (placeData C m side) f g) (hIntL_num _ _ _ _) (hInt_lip _ _ _ _) (hInt_fc _ _ _ _))
                (riemannIntegral (hIntL_den C (placeData C m side) g f) (hIntL_num _ _ _ _) (hInt_lip _ _ _ _) (hInt_fc _ _ _ _)))) 2) C.X) := by
  refine Req_trans (riemannIntegral_RsumN_fl (fun m x => RsumN (fun side => gTerm C f g m side x) 2)
    (fun m => innerL C f g m) (innerL_den C f g) (innerL_num C f g) (inner_lip C f g) (inner_fc C f g) C.X) ?_
  refine RsumN_congr C.X (fun m _ => ?_)
  refine Req_trans (riemannIntegral_RsumN_fl (fun side x => gTerm C f g m side x) (termL C f g m)
    (termL_den C f g m) (termL_num C f g m) (term_lip C f g m) (term_fc C f g m) 2) ?_
  refine RsumN_congr 2 (fun side _ => ?_)
  refine Req_trans (riemannIntegral_smul_real_fl (omegaW C m side) (pairL_den C f g m side) (pairL_num C f g m side)
    (pair_lip C f g m side) (pair_fc C f g m side)) ?_
  exact Rmul_congr (Req_refl _) (integral_pair C f g m side)

-- ===========================================================================
-- (7) Readback of the places: `Σ_side ω·(∫ + ∫) = −½·(P_m(f,g) + P_m(g,f))`.
-- ===========================================================================

theorem RsumN_two_pd (F : Nat → Real) : Req (RsumN F 2) (Radd (F 0) (F 1)) := by
  rw [RsumN_succ_fl, RsumN_succ_fl, RsumN_zero_fl]
  exact Radd_congr (Req_trans (Radd_comm _ _) (Radd_zero _)) (Req_refl _)

/-- `((K·W)·(I + I')) ≈ K·(W·I + W·I')`. -/
theorem w_pull_pd (K W I I' : Real) :
    Req (Rmul (Rmul K W) (Radd I I')) (Rmul K (Radd (Rmul W I) (Rmul W I'))) :=
  Req_trans (Rmul_assoc K W _) (Rmul_congr (Req_refl K) (Rmul_distrib W I I'))

/-- `(Λn₀)(H₀+H₀') + ((Λe)n₁)(H₁+H₁') ≈ Λ(n₀H₀ + e(n₁H₁)) + Λ(n₀H₀' + e(n₁H₁'))`. -/
theorem place_regroup_pd (Λ n₀ n₁ e H₀ H₀' H₁ H₁' : Real) :
    Req (Radd (Rmul (Rmul Λ n₀) (Radd H₀ H₀')) (Rmul (Rmul (Rmul Λ e) n₁) (Radd H₁ H₁')))
        (Radd (Rmul Λ (Radd (Rmul n₀ H₀) (Rmul e (Rmul n₁ H₁))))
              (Rmul Λ (Radd (Rmul n₀ H₀') (Rmul e (Rmul n₁ H₁'))))) := by
  have h0 : Req (Rmul (Rmul Λ n₀) (Radd H₀ H₀')) (Radd (Rmul Λ (Rmul n₀ H₀)) (Rmul Λ (Rmul n₀ H₀'))) :=
    Req_trans (Rmul_assoc Λ n₀ _)
      (Req_trans (Rmul_congr (Req_refl Λ) (Rmul_distrib n₀ H₀ H₀')) (Rmul_distrib Λ _ _))
  have h1 : Req (Rmul (Rmul (Rmul Λ e) n₁) (Radd H₁ H₁'))
      (Radd (Rmul Λ (Rmul e (Rmul n₁ H₁))) (Rmul Λ (Rmul e (Rmul n₁ H₁')))) := by
    refine Req_trans (Rmul_assoc (Rmul Λ e) n₁ _) ?_
    refine Req_trans (Rmul_congr (Req_refl _) (Rmul_distrib n₁ H₁ H₁')) ?_
    refine Req_trans (Rmul_assoc Λ e _) ?_
    refine Req_trans (Rmul_congr (Req_refl Λ) (Rmul_distrib e _ _)) ?_
    exact Rmul_distrib Λ _ _
  refine Req_trans (Radd_congr h0 h1) ?_
  refine Req_trans (Radd_swap _ _ _ _) ?_
  exact Radd_congr (Req_symm (Rmul_distrib Λ _ _)) (Req_symm (Rmul_distrib Λ _ _))

theorem placeData_zero_q (C : NormCtx) (m : Nat) : (placeData C m 0).q = (⟨((m + 1 : Nat) : Int), 1⟩ : Q) := rfl
theorem placeData_one_q (C : NormCtx) (m : Nat) : (placeData C m 1).q = (⟨1, m + 1⟩ : Q) := rfl

/-- `P_m(f,g)` in terms of the certified integrals of the pulled-back integrands (definitional). -/
theorem PForm_unfold (C : NormCtx) (m : Nat) (f g : L2Test) :
    PForm m f g C.a C.han C.had C.w C.hw C.hwn
      = Rmul (vonMangoldt (m + 1))
          (Radd (Rmul (normWeight (⟨((m + 1 : Nat) : Int), 1⟩ : Q))
                  (Rmul (ofQ C.w C.hw) (riemannIntegral (hIntL_den C (placeData C m 0) f g) (hIntL_num _ _ _ _)
                    (hInt_lip _ _ _ _) (hInt_fc _ _ _ _))))
                (Rmul (ofQ (⟨1, m + 1⟩ : Q) (Nat.succ_pos m))
                  (Rmul (normWeight (⟨1, m + 1⟩ : Q))
                    (Rmul (ofQ C.w C.hw) (riemannIntegral (hIntL_den C (placeData C m 1) f g) (hIntL_num _ _ _ _)
                      (hInt_lip _ _ _ _) (hInt_fc _ _ _ _)))))) := rfl

/-- **The two sides of a place read back `−½·(P_m(f,g) + P_m(g,f))`.** -/
theorem place_readback (C : NormCtx) (f g : L2Test) (m : Nat) :
    Req (RsumN (fun side => Rmul (omegaW C m side)
          (Radd (riemannIntegral (hIntL_den C (placeData C m side) f g) (hIntL_num _ _ _ _) (hInt_lip _ _ _ _) (hInt_fc _ _ _ _))
                (riemannIntegral (hIntL_den C (placeData C m side) g f) (hIntL_num _ _ _ _) (hInt_lip _ _ _ _) (hInt_fc _ _ _ _)))) 2)
        (Rneg (Rmul cH (Radd (PForm m f g C.a C.han C.had C.w C.hw C.hwn) (PForm m g f C.a C.han C.had C.w C.hw C.hwn)))) := by
  refine Req_trans (RsumN_two_pd _) ?_
  rw [PForm_unfold, PForm_unfold]
  unfold omegaW
  -- (−(½κ₀))·X₀ + (−(½κ₁))·X₁ ≈ −(½·(κ₀X₀ + κ₁X₁))
  refine Req_trans (Radd_congr (Rmul_neg_left _ _) (Rmul_neg_left _ _)) ?_
  refine Req_trans (Req_symm (Rneg_Radd _ _)) (Rneg_congr ?_)
  refine Req_trans (Radd_congr (Rmul_assoc cH _ _) (Rmul_assoc cH _ _)) ?_
  refine Req_trans (Req_symm (Rmul_distrib cH _ _)) (Rmul_congr (Req_refl cH) ?_)
  -- κ₀·(I₀ + I₀') + κ₁·(I₁ + I₁') with κ₀ = (Λ n₀)·W, κ₁ = ((Λ e) n₁)·W
  show Req (Radd (Rmul (Rmul (Rmul (vonMangoldt (m + 1)) (normWeight (⟨((m + 1 : Nat) : Int), 1⟩ : Q))) (ofQ C.w C.hw)) _)
                 (Rmul (Rmul (Rmul (Rmul (vonMangoldt (m + 1)) (ofQ (⟨1, m + 1⟩ : Q) (Nat.succ_pos m)))
                   (normWeight (⟨1, m + 1⟩ : Q))) (ofQ C.w C.hw)) _)) _
  refine Req_trans (Radd_congr (w_pull_pd _ _ _ _) (w_pull_pd _ _ _ _)) ?_
  exact place_regroup_pd _ _ _ _ _ _ _ _

-- ===========================================================================
-- (8) ★ THE IDENTIFICATION WITH THE PRIME FORM.
-- ===========================================================================

/-- **★ THE BISHOP-LIMIT THEOREM (all tests)**: the limit of the Γ partial sums is
    `−½·(PrimeForm_X(f,g) + PrimeForm_X(g,f))`. -/
theorem gammaLimit_eq (C : NormCtx) (f g : L2Test) :
    Req (gammaLimit C f g)
        (Rneg (Rmul cH (Radd (PrimeForm C.X f g C.a C.han C.had C.w C.hw C.hwn)
                             (PrimeForm C.X g f C.a C.han C.had C.w C.hw C.hwn)))) := by
  refine Req_trans (gammaLimit_eq_integral C f g) ?_
  refine Req_trans (integral_G C f g) ?_
  refine Req_trans (RsumN_congr C.X (fun m _ => place_readback C f g m)) ?_
  refine Req_trans (RsumN_Rneg _ C.X) (Rneg_congr ?_)
  refine Req_trans (RsumN_smul_ai cH _ C.X) (Rmul_congr (Req_refl cH) ?_)
  exact RsumN_Radd _ _ C.X

/-- `½·(x + x) ≈ x`. -/
theorem half_double_pd (x : Real) : Req (Rmul cH (Radd x x)) x := by
  refine Req_trans (Rmul_congr (Req_refl cH) (Req_symm (cTwo_mul x))) ?_
  refine Req_trans (Req_symm (Rmul_assoc cH cTwo x)) ?_
  refine Req_trans (Rmul_congr (Req_trans (Rmul_ofQ_ofQ (by decide) Nat.one_pos)
    (ofQ_congr _ (by decide) (by decide : Qeq (mul (⟨1, 2⟩ : Q) (⟨2, 1⟩ : Q)) (⟨1, 1⟩ : Q)))) (Req_refl x)) ?_
  exact Rone_mul x

/-- **★ The block-grouped limit IS `−PrimeForm` ON THE CORE** (scalar identification): for `f, g : ClosedCore C`,
    `lim Σ ⟨Γf, MΓg⟩ = −PrimeForm_X(f,g)` (the prime form is symmetric on the core, `PrimeForm_symm`). -/
theorem gammaLimit_eq_neg_PrimeForm (C : NormCtx) (f g : ClosedCore C) :
    Req (gammaLimit C f.1 g.1) (Rneg (PrimeForm C.X f.1 g.1 C.a C.han C.had C.w C.hw C.hwn)) := by
  refine Req_trans (gammaLimit_eq C f.1 g.1) (Rneg_congr ?_)
  have hsym : Req (PrimeForm C.X g.1 f.1 C.a C.han C.had C.w C.hw C.hwn)
      (PrimeForm C.X f.1 g.1 C.a C.han C.had C.w C.hw C.hwn) :=
    PrimeForm_symm C.X g.1 f.1 C.a C.han C.had C.w C.hw C.hwn C.b C.hbd C.hbnpos
      g.2.hgh g.2.hgl f.2.hgh f.2.hgl C.hfit
  refine Req_trans (Rmul_congr (Req_refl cH) (Radd_congr (Req_refl _) hsym)) ?_
  exact half_double_pd _

/-- The diagonal, for every raw test: `lim Σ ⟨Γf, MΓf⟩ = −PrimeForm_X(f,f)` (no core hypothesis). -/
theorem gammaLimit_diag (C : NormCtx) (f : L2Test) :
    Req (gammaLimit C f f) (Rneg (PrimeForm C.X f f C.a C.han C.had C.w C.hw C.hwn)) :=
  Req_trans (gammaLimit_eq C f f) (Rneg_congr (half_double_pd _))

end UOR.Bridge.F1Square.Square
