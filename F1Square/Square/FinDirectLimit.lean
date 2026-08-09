/-
F1 square — **the finite-support direct limit** of the `cvInc` isometry system, the FIRST REAL
CONSUMER of `finPreHilbert` and `cvInc`. This bundles the inclusions into a typed linear-isometry
object (`LinIsometry`), forms the colimit of `(CVec N, cvInc)` as a genuine setoid `DLimRaw`/`DLimEq`,
and — the load-bearing result — proves the colimit inner product `dlimInner` is INDEPENDENT of the
representative and the stage at which it is evaluated (`dlimInner_wd`, `dlimInner_stage`), consuming
the isometry property `cvInc_inner`. It also shows the colimit receives each finite stage
(`dlimMk`) and that the `cvInc` maps become the identity in the limit (`dlimMk_cvInc`), so `cInner`
is genuinely extended (`dlimInner_mk`).

This is the finite-support ℓ²-precursor: a colimit element is a finitely-supported vector, presented
at some finite stage; the metric completion (next brick) will complete it under the `dlimInner` norm.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; fully zeta-free. Crux `none`.
-/

import F1Square.Square.FinPreHilbert

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- The typed linear-isometry object bundling the inclusion `cvInc`.
-- ===========================================================================

/-- A **bundled linear isometry** `CVec N → CVec M`: a setoid-respecting `ℂ`-linear map that
    preserves the inner product. The typed object the raw `cvInc` lemmas assemble into. -/
structure LinIsometry (N M : Nat) where
  toFun : CVec N → CVec M
  isom_congr : ∀ {x y}, CVecEq x y → CVecEq (toFun x) (toFun y)
  isom_add : ∀ x y, CVecEq (toFun (cvAdd x y)) (cvAdd (toFun x) (toFun y))
  isom_smul : ∀ c x, CVecEq (toFun (cvSmul c x)) (cvSmul c (toFun x))
  isom_inner : ∀ x y, Ceq (cInner M (toFun x) (toFun y)) (cInner N x y)

/-- The inclusion `cvInc` packaged as a `LinIsometry`. -/
def cvIncIso {N M : Nat} (h : N ≤ M) : LinIsometry N M where
  toFun := cvInc h
  isom_congr := fun hxy => cvInc_congr h hxy
  isom_add := cvInc_add h
  isom_smul := cvInc_smul h
  isom_inner := cvInc_inner h

-- ===========================================================================
-- The direct limit as a setoid on staged representatives.
-- ===========================================================================

/-- A **staged representative** of a colimit element: a vector `vec : CVec stage` at some finite
    stage. -/
structure DLimRaw where
  stage : Nat
  vec : CVec stage

/-- Two representatives are **equal in the colimit** iff they agree after inclusion into some common
    higher stage `K`. -/
def DLimEq (a b : DLimRaw) : Prop :=
  ∃ K, ∃ (haK : a.stage ≤ K) (hbK : b.stage ≤ K), CVecEq (cvInc haK a.vec) (cvInc hbK b.vec)

/-- Reflexivity of `DLimEq`. -/
theorem DLimEq_refl (a : DLimRaw) : DLimEq a a :=
  ⟨a.stage, Nat.le_refl _, Nat.le_refl _, CVecEq_refl _⟩

/-- Symmetry of `DLimEq`. -/
theorem DLimEq_symm {a b : DLimRaw} (h : DLimEq a b) : DLimEq b a := by
  obtain ⟨K, haK, hbK, hab⟩ := h
  exact ⟨K, hbK, haK, CVecEq_symm hab⟩

/-- **Lifting an agreement to a higher stage**: if `a` and `b` agree (already included) at `K`, and
    `K ≤ K'`, they agree at `K'` — via `cvInc_comp` and `cvInc_congr`. -/
private theorem dlimEq_lift {a b : DLimRaw} {K K' : Nat} (hKK' : K ≤ K')
    (haK : a.stage ≤ K) (hbK : b.stage ≤ K) (hab : CVecEq (cvInc haK a.vec) (cvInc hbK b.vec)) :
    CVecEq (cvInc (Nat.le_trans haK hKK') a.vec) (cvInc (Nat.le_trans hbK hKK') b.vec) :=
  CVecEq_trans (CVecEq_symm (cvInc_comp haK hKK' a.vec))
    (CVecEq_trans (cvInc_congr hKK' hab) (cvInc_comp hbK hKK' b.vec))

/-- Transitivity of `DLimEq` (go to a common higher stage). -/
theorem DLimEq_trans {a b c : DLimRaw} (h₁ : DLimEq a b) (h₂ : DLimEq b c) : DLimEq a c := by
  obtain ⟨K₁, haK₁, hbK₁, hab⟩ := h₁
  obtain ⟨K₂, hbK₂, hcK₂, hbc⟩ := h₂
  refine ⟨max K₁ K₂, Nat.le_trans haK₁ (Nat.le_max_left _ _),
    Nat.le_trans hcK₂ (Nat.le_max_right _ _), ?_⟩
  have e₁ := dlimEq_lift (Nat.le_max_left K₁ K₂) haK₁ hbK₁ hab
  have e₂ := dlimEq_lift (Nat.le_max_right K₁ K₂) hbK₂ hcK₂ hbc
  exact CVecEq_trans e₁ e₂

/-- The colimit setoid on staged representatives. -/
instance dlimSetoid : Setoid DLimRaw where
  r := DLimEq
  iseqv := ⟨DLimEq_refl, fun h => DLimEq_symm h, fun h₁ h₂ => DLimEq_trans h₁ h₂⟩

-- ===========================================================================
-- The colimit inner product and its stage / representative independence.
-- ===========================================================================

/-- The colimit inner product on representatives: include both to the common stage `max` and pair. -/
def dlimInner (a b : DLimRaw) : Complex :=
  cInner (max a.stage b.stage)
    (cvInc (Nat.le_max_left a.stage b.stage) a.vec)
    (cvInc (Nat.le_max_right a.stage b.stage) b.vec)

/-- **Stage evaluation** — the crux consumer of the isometry property `cvInc_inner`: pairing two
    representatives at ANY common stage `K ≥` both source stages gives the same value as `dlimInner`
    (which pairs them at `max`). So the pairing is stage-independent. -/
theorem dlimInner_eval (p q : DLimRaw) {K : Nat} (hpK : p.stage ≤ K) (hqK : q.stage ≤ K) :
    Ceq (cInner K (cvInc hpK p.vec) (cvInc hqK q.vec)) (dlimInner p q) := by
  have hpm : p.stage ≤ max p.stage q.stage := Nat.le_max_left _ _
  have hqm : q.stage ≤ max p.stage q.stage := Nat.le_max_right _ _
  have hmK : max p.stage q.stage ≤ K := Nat.max_le.mpr ⟨hpK, hqK⟩
  refine Ceq_trans (cInner_congr ?_ ?_) (cvInc_inner hmK (cvInc hpm p.vec) (cvInc hqm q.vec))
  · exact CVecEq_symm (cvInc_comp hpm hmK p.vec)
  · exact CVecEq_symm (cvInc_comp hqm hmK q.vec)

/-- **Well-definedness (representative + stage independence)** of the colimit inner product: `a ≈ a'`
    and `b ≈ b'` give `⟨a, b⟩ ≈ ⟨a', b'⟩`. Evaluate all four at the common stage `max Ka Kb`, where the
    agreements `a ≈ a'`, `b ≈ b'` already hold (lifted), and apply `cInner_congr`; the two sides equal
    their `dlimInner` values by stage evaluation. The load-bearing consumer of `cvInc_inner`. -/
theorem dlimInner_wd {a a' b b' : DLimRaw} (ha : DLimEq a a') (hb : DLimEq b b') :
    Ceq (dlimInner a b) (dlimInner a' b') := by
  obtain ⟨Ka, haKa, ha'Ka, hAA⟩ := ha
  obtain ⟨Kb, hbKb, hb'Kb, hBB⟩ := hb
  have haK : a.stage ≤ max Ka Kb := Nat.le_trans haKa (Nat.le_max_left Ka Kb)
  have ha'K : a'.stage ≤ max Ka Kb := Nat.le_trans ha'Ka (Nat.le_max_left Ka Kb)
  have hbK : b.stage ≤ max Ka Kb := Nat.le_trans hbKb (Nat.le_max_right Ka Kb)
  have hb'K : b'.stage ≤ max Ka Kb := Nat.le_trans hb'Kb (Nat.le_max_right Ka Kb)
  refine Ceq_trans (Ceq_symm (dlimInner_eval a b haK hbK))
    (Ceq_trans (cInner_congr ?_ ?_) (dlimInner_eval a' b' ha'K hb'K))
  · exact dlimEq_lift (Nat.le_max_left Ka Kb) haKa ha'Ka hAA
  · exact dlimEq_lift (Nat.le_max_right Ka Kb) hbKb hb'Kb hBB

-- ===========================================================================
-- The colimit receives each finite stage; the `cvInc` maps become the identity.
-- ===========================================================================

/-- **The inclusion is the identity in the colimit**: the stage-`M` representative `ι x` and the
    stage-`N` representative `x` are equal in the direct limit. So the colimit is exactly the
    finite-support quotient of the `cvInc` system. -/
theorem dlimMk_cvInc {N M : Nat} (h : N ≤ M) (x : CVec N) :
    DLimEq ⟨M, cvInc h x⟩ ⟨N, x⟩ :=
  ⟨M, Nat.le_refl M, h, cvInc_id (cvInc h x)⟩

/-- **The colimit inner product extends `cInner`**: at a single stage `N` it restricts to
    `⟨x, y⟩_N` — so `dlimInner` is a genuine extension of the finite pre-Hilbert inner product. -/
theorem dlimInner_mk (N : Nat) (x y : CVec N) :
    Ceq (dlimInner ⟨N, x⟩ ⟨N, y⟩) (cInner N x y) :=
  Ceq_trans (Ceq_symm (dlimInner_eval ⟨N, x⟩ ⟨N, y⟩ (Nat.le_refl N) (Nat.le_refl N)))
    (cInner_congr (cvInc_id x) (cvInc_id y))

end UOR.Bridge.F1Square.Square
