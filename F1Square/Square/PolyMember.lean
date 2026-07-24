/-
F1 square — **the pre-Hilbert layer, brick 66** (`PolyMember.lean`): **THE MEMBER GENERATOR** —
brick 65 turned a polynomial test's moments into an explicit rational; this turns that into a
*constructor*, and then builds the `K = 7` member in fifteen lines instead of a two-hundred-line
file.

    coefficient sums agree  ⟹  `[0,1]`-supported                (`polyPN_supp`)
    `K` rational equations   ⟹  `HatVanishes (polyPN a b d) K`   (`polyPN_hatVanishes`)

Those are the only two conditions. The support one is the "both parts sum to the same value"
identity every constructed member has quietly satisfied (`deep6`'s two parts both sum to `4279`) —
here it is the *theorem* that this is exactly what `[0,1]` support means for a polynomial test,
because `clamp01` is `1` past `1`, so the value on every half-line window is the coefficient sum.
The moment one is brick 65's closed form. Together: **solve the `ℚ`-linear Hilbert system, get a
certified co-support member**, with no per-degree integration and no hand-built `pv_`/`fv_` chains.

The generator is exercised at once. `deep7 = x − 36x² + 420x³ − 2310x⁴ + 6930x⁵ − 12012x⁶ +
12012x⁷ − 6435x⁸ + 1430x⁹` (both parts summing to `20793`) is the depth-7 nullspace of the Hilbert
system; its first non-vanishing moment is `⟨deep7, x⁷⟩ = −1/1750320`, so the strict filtration
chain extends to `0 ⊋ 1 ⊋ ⋯ ⊋ 8` (`cosupport_chain_strict_eight`) and the skeleton's unconditional
positivity fires on it (`weil_psd_deep7`). Every one of those facts is a `decide` on rational
arithmetic that the generator reduced it to.

HONEST SCOPE. A constructor, not an existence theorem: it says a *given* solution of the rational
system yields a member, not that solutions exist at every depth (that is still the hypergeometric
identity the layer cannot reach — each `deepK` is found by a `ℚ`-linear solve outside the kernel
and then certified inside it). One more member and one more strict level; the positivity is still
the skeleton's diagonal multiplier form on moment data, not the Weil functional on the test space.
Step 4 is RH. The crux fields stay `none`.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Square.PolyMoment
import F1Square.Square.DeepMemberSix

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

set_option maxRecDepth 40000

/-- `zero` read as a rational constant (local: the earlier copies are private). -/
private theorem zeroQv : Req zero (ofQ (⟨0, 1⟩ : Q) (by decide)) :=
  Req_of_seq_Qeq (fun _ => Qeq_refl _)

/-- `A = B` as rationals gives `A − B = 0` (local copy). -/
private theorem Qdiff_zero {A B : Q} (h : Qeq A B) : Qeq (add A (neg B)) (⟨0, 1⟩ : Q) := by
  simp only [Qeq, add, neg] at h ⊢
  have e : (-B.num) * (A.den : Int) = -(B.num * (A.den : Int)) := by ring_uor
  rw [e]
  omega

-- ===========================================================================
-- The support law.
-- ===========================================================================

/-- **The coefficient sum** `Σ_{i<d} a_i` — the value of `Σ_{i<d} a_i xⁱ` at every point past
    `1`, since `clamp01` is `1` there. -/
def coefSumQ (a : Nat → Nat) : Nat → Q
  | 0 => (⟨0, 1⟩ : Q)
  | d + 1 => add (coefSumQ a d) (mul (⟨((a d : Nat) : Int), 1⟩ : Q) (⟨1, 1⟩ : Q))

theorem coefSumQ_den (a : Nat → Nat) : ∀ d : Nat, 0 < (coefSumQ a d).den
  | 0 => Nat.one_pos
  | d + 1 => add_den_pos (coefSumQ_den a d) (Qmul_den_pos Nat.one_pos Nat.one_pos)

/-- **The window value of a polynomial test is its coefficient sum.** -/
theorem polyN_window_val (a : Nat → Nat) (m : Nat) {x : Real} (h0 : Rle zero x) : ∀ d : Nat,
    Req ((polyN a d).f (affineMap (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q)
        Nat.one_pos (by decide) x))
      (ofQ (coefSumQ a d) (coefSumQ_den a d))
  | 0 => zeroQv
  | d + 1 =>
      fv_add (coefSumQ_den a d) (Qmul_den_pos Nat.one_pos Nat.one_pos)
        (coefSumQ_den a (d + 1))
        (polyN_window_val a m h0 d)
        (fv_scale (a d) (by decide) (Qmul_den_pos Nat.one_pos Nat.one_pos)
          (powTest_window_one m h0 d) (Qeq_refl _))
        (Qeq_refl _)

/-- **THE SUPPORT LAW**: a `ℤ`-coefficient polynomial test is `[0,1]`-supported exactly when its
    two coefficient sums agree — the "both parts sum to the same value" condition every
    constructed member satisfies, now a theorem. -/
theorem polyPN_supp (a b : Nat → Nat) (d : Nat) (h : Qeq (coefSumQ a d) (coefSumQ b d)) :
    UnitSupported (polyPN a b d) := by
  intro m x h0 _
  show Req (Rsub ((polyN a d).f (affineMap (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q)
      Nat.one_pos (by decide) x))
    ((polyN b d).f (affineMap (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q)
      Nat.one_pos (by decide) x))) zero
  refine Req_trans (Rsub_congr (polyN_window_val a m h0 d) (polyN_window_val b m h0 d)) ?_
  exact Req_trans (sub_ofQ_val (coefSumQ_den a d) (coefSumQ_den b d) (by decide)
    (Qdiff_zero h)) (Req_symm zeroQv)

-- ===========================================================================
-- The generator.
-- ===========================================================================

/-- **THE MEMBER GENERATOR**: matching coefficient sums plus `K` matching Hilbert contractions
    produce a certified depth-`K` co-support member. No integration, no per-degree engine. -/
theorem polyPN_hatVanishes (a b : Nat → Nat) (d K : Nat)
    (hsum : Qeq (coefSumQ a d) (coefSumQ b d))
    (hmom : ∀ n : Nat, n < K → Qeq (polyMomQ a n d) (polyMomQ b n d)) :
    HatVanishes (polyPN a b d) K (C := (⟨0, 1⟩ : Q)) (by decide)
      (by show (0 : Int) ≤ 0; decide)
      (allDecay_of_supp (polyPN a b d) (polyPN_supp a b d hsum)) :=
  hatVanishes_of_moments (polyPN a b d) K (polyPN_supp a b d hsum)
    (polyPN_moments_zero_of_rational a b d K hmom)

-- ===========================================================================
-- The generator exercised: the `K = 7` member.
-- ===========================================================================

/-- The positive part of `deep7`: `x + 420x³ + 6930x⁵ + 12012x⁷ + 1430x⁹` (sum `20793`). -/
def deep7CoefP : Nat → Nat
  | 1 => 1
  | 3 => 420
  | 5 => 6930
  | 7 => 12012
  | 9 => 1430
  | _ => 0

/-- The negative part of `deep7`: `36x² + 2310x⁴ + 12012x⁶ + 6435x⁸` (sum `20793`). -/
def deep7CoefN : Nat → Nat
  | 2 => 36
  | 4 => 2310
  | 6 => 12012
  | 8 => 6435
  | _ => 0

/-- **THE `K = 7` MEMBER**, `x − 36x² + 420x³ − 2310x⁴ + 6930x⁵ − 12012x⁶ + 12012x⁷ − 6435x⁸ +
    1430x⁹`, produced by the generator from its coefficient data alone. -/
def deep7 : L2Test := polyPN deep7CoefP deep7CoefN 10

theorem deep7_supp : UnitSupported deep7 :=
  polyPN_supp deep7CoefP deep7CoefN 10 (by decide)

theorem deep7_hatVanishes :
    HatVanishes deep7 7 (C := (⟨0, 1⟩ : Q)) (by decide) (by show (0 : Int) ≤ 0; decide)
      (allDecay_of_supp deep7 deep7_supp) :=
  polyPN_hatVanishes deep7CoefP deep7CoefN 10 7 (by decide) (fun n hn => by
    match n, hn with
    | 0, _ => decide
    | 1, _ => decide
    | 2, _ => decide
    | 3, _ => decide
    | 4, _ => decide
    | 5, _ => decide
    | 6, _ => decide)

/-- **The first non-vanishing moment**: `⟨deep7, x⁷⟩ = −1/1750320`. -/
theorem deep7_moment_seven :
    Req (mellinMoment deep7 7) (ofQ (⟨-1, 1750320⟩ : Q) (by decide)) :=
  mellinMoment_polyPN deep7CoefP deep7CoefN 7 10 (by decide) (by decide)

theorem deep7_not_hatVanishes_eight :
    ¬ HatVanishes deep7 8 (C := (⟨0, 1⟩ : Q)) (by decide) (by show (0 : Int) ≤ 0; decide)
      (allDecay_of_supp deep7 deep7_supp) := by
  intro h
  have hz : Req (mellinMoment deep7 7) zero :=
    (hatVanishes_iff_orthogonal deep7 8 deep7_supp).mp h 7 (by omega)
  have hv : Req (ofQ (⟨-1, 1750320⟩ : Q) (by decide)) zero :=
    Req_trans (Req_symm deep7_moment_seven) hz
  have hpos : Pos (Rneg (ofQ (⟨-1, 1750320⟩ : Q) (by decide))) := ⟨3500640, by decide⟩
  obtain ⟨n, hn⟩ := Pos_congr (Rneg_congr hv) hpos
  have hlt : (1 : Int) * ((1 : Nat) : Int) < (-0 : Int) * ((n + 1 : Nat) : Int) := hn
  push_cast at hlt
  omega

theorem cosupport_strict_at_seven :
    HatVanishes deep7 7 (C := (⟨0, 1⟩ : Q)) (by decide) (by show (0 : Int) ≤ 0; decide)
        (allDecay_of_supp deep7 deep7_supp)
    ∧ ¬ HatVanishes deep7 8 (C := (⟨0, 1⟩ : Q)) (by decide) (by show (0 : Int) ≤ 0; decide)
        (allDecay_of_supp deep7 deep7_supp) :=
  ⟨deep7_hatVanishes, deep7_not_hatVanishes_eight⟩

/-- **THE STRICT CHAIN THROUGH DEPTH 8** — one level deeper than brick 60, and this level's
    witness came out of the generator rather than a hand-built file. -/
theorem cosupport_chain_strict_eight :
    (¬ HatVanishes bumpU 1 (C := (⟨0, 1⟩ : Q)) (by decide)
        (by show (0 : Int) ≤ 0; decide) (allDecay_of_supp bumpU bumpU_supp))
    ∧ (¬ HatVanishes lin1 2 (C := (⟨0, 1⟩ : Q)) (by decide)
        (by show (0 : Int) ≤ 0; decide) (allDecay_of_supp lin1 lin1_supp))
    ∧ (¬ HatVanishes lin2 3 (C := (⟨0, 1⟩ : Q)) (by decide)
        (by show (0 : Int) ≤ 0; decide) (allDecay_of_supp lin2 lin2_supp))
    ∧ (¬ HatVanishes deep3 4 (C := (⟨0, 1⟩ : Q)) (by decide)
        (by show (0 : Int) ≤ 0; decide) (allDecay_of_supp deep3 deep3_supp))
    ∧ (¬ HatVanishes deep4 5 (C := (⟨0, 1⟩ : Q)) (by decide)
        (by show (0 : Int) ≤ 0; decide) (allDecay_of_supp deep4 deep4_supp))
    ∧ (¬ HatVanishes deep5 6 (C := (⟨0, 1⟩ : Q)) (by decide)
        (by show (0 : Int) ≤ 0; decide) (allDecay_of_supp deep5 deep5_supp))
    ∧ (¬ HatVanishes deep6 7 (C := (⟨0, 1⟩ : Q)) (by decide)
        (by show (0 : Int) ≤ 0; decide) (allDecay_of_supp deep6 deep6_supp))
    ∧ (¬ HatVanishes deep7 8 (C := (⟨0, 1⟩ : Q)) (by decide)
        (by show (0 : Int) ≤ 0; decide) (allDecay_of_supp deep7 deep7_supp)) :=
  ⟨cosupport_chain_strict_seven.1, cosupport_chain_strict_seven.2.1,
   cosupport_chain_strict_seven.2.2.1, cosupport_chain_strict_seven.2.2.2.1,
   cosupport_chain_strict_seven.2.2.2.2.1, cosupport_chain_strict_seven.2.2.2.2.2.1,
   cosupport_chain_strict_seven.2.2.2.2.2.2, deep7_not_hatVanishes_eight⟩

/-- **The capstone**: the skeleton's unconditional positivity, fired on the generated member. -/
theorem weil_psd_deep7 (N : Nat) :
    Rnonneg (weilQuad (multForm burnolMult) (momSeq deep7) N) :=
  weil_psd_on_cosupport deep7 deep7_supp
    (hatVanishes_mono (by decide) deep7_hatVanishes) N

end UOR.Bridge.F1Square.Square
