/-
F1 square — **the finite-support direct limit** of the `cvInc` isometry system, the FIRST REAL
CONSUMER of `finPreHilbert` and `cvInc`. This bundles the inclusions into a typed linear-isometry
object (`LinIsometry`), forms the colimit of `(CVec N, cvInc)` as a genuine setoid `DLimRaw`/`DLimEq`,
and — the load-bearing result — proves the colimit inner product `dlimInner` is INDEPENDENT of the
representative and the stage at which it is evaluated (`dlimInner_wd`, `dlimInner_eval`), consuming
the isometry property `cvInc_inner`. It also shows the colimit receives each finite stage
(`dlimMk`) and that the `cvInc` maps become the identity in the limit (`dlimMk_cvInc`), so `cInner`
is genuinely extended (`dlimInner_mk`).

**The colimit is itself a Bishop pre-Hilbert object.** With the limit operations `dlimAdd`/`dlimSmul`/
`dlimNeg`/`dlimZero` (each proved well-defined against `DLimEq`), the complex-module laws, and the
sesquilinear/Hermitian/positivity/definiteness laws of `dlimInner`, the direct limit is packaged as a
`FinPreHilbert` instance `dlimPreHilbert` — a genuine (finite-support, infinite-dimensional) pre-Hilbert
space, the SAME record the finite stages `finPreHilbert N` instantiate. The inner-product laws are
DERIVED from the stagewise `finPreHilbert` laws through the isometry `cvIncIso`.

This is the finite-support ℓ²-precursor: a colimit element is a finitely-supported vector, presented
at some finite stage; the metric completion (next brick) will complete it under the `dlimInner` norm.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; fully zeta-free. Crux `none`.
-/

import F1Square.Square.FinPreHilbert

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

set_option maxHeartbeats 1000000

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

-- ===========================================================================
-- Limit-level complex-module operations, well-defined against `DLimEq`.
-- ===========================================================================

/-- The injection of a stage-`N` vector into the colimit. -/
def dlimMk {N : Nat} (x : CVec N) : DLimRaw := ⟨N, x⟩

/-- The colimit zero (the empty-stage zero vector). -/
def dlimZero : DLimRaw := ⟨0, cvZero 0⟩

/-- Colimit negation (stage-preserving). -/
def dlimNeg (a : DLimRaw) : DLimRaw := ⟨a.stage, cvNeg a.vec⟩

/-- Colimit scalar multiplication (stage-preserving). -/
def dlimSmul (c : Complex) (a : DLimRaw) : DLimRaw := ⟨a.stage, cvSmul c a.vec⟩

/-- Colimit addition: include both representatives to the common stage `max` and add. -/
def dlimAdd (a b : DLimRaw) : DLimRaw :=
  ⟨max a.stage b.stage,
    cvAdd (cvInc (Nat.le_max_left a.stage b.stage) a.vec)
          (cvInc (Nat.le_max_right a.stage b.stage) b.vec)⟩

/-- **Inclusion of a colimit sum**: `ι_K (a ⊕ b) ≈ ι_K a ⊕ ι_K b` at any common stage `K` (via
    `cvInc_add` + `cvInc_comp`). The reducer that turns colimit-addition goals into stagewise ones. -/
theorem dlimAdd_incl {Na Nb K : Nat} (haK : Na ≤ K) (hbK : Nb ≤ K) (hmK : max Na Nb ≤ K)
    (a : CVec Na) (b : CVec Nb) :
    CVecEq (cvInc hmK (cvAdd (cvInc (Nat.le_max_left Na Nb) a) (cvInc (Nat.le_max_right Na Nb) b)))
           (cvAdd (cvInc haK a) (cvInc hbK b)) :=
  CVecEq_trans (cvInc_add hmK _ _)
    (cvAdd_congr (cvInc_comp (Nat.le_max_left Na Nb) hmK a)
                 (cvInc_comp (Nat.le_max_right Na Nb) hmK b))

/-- Negation respects `DLimEq`. -/
theorem dlimNeg_wd {a a' : DLimRaw} (h : DLimEq a a') : DLimEq (dlimNeg a) (dlimNeg a') := by
  obtain ⟨K, haK, ha'K, hAA⟩ := h
  exact ⟨K, haK, ha'K, CVecEq_trans (cvInc_neg haK a.vec)
    (CVecEq_trans (cvNeg_congr hAA) (CVecEq_symm (cvInc_neg ha'K a'.vec)))⟩

/-- Scalar multiplication respects `DLimEq` (in both scalar and vector). -/
theorem dlimSmul_wd {c c' : Complex} {a a' : DLimRaw} (hc : Ceq c c') (h : DLimEq a a') :
    DLimEq (dlimSmul c a) (dlimSmul c' a') := by
  obtain ⟨K, haK, ha'K, hAA⟩ := h
  exact ⟨K, haK, ha'K, CVecEq_trans (cvInc_smul haK c a.vec)
    (CVecEq_trans (cvSmul_congr hc hAA) (CVecEq_symm (cvInc_smul ha'K c' a'.vec)))⟩

/-- Addition respects `DLimEq`. -/
theorem dlimAdd_wd {a a' b b' : DLimRaw} (ha : DLimEq a a') (hb : DLimEq b b') :
    DLimEq (dlimAdd a b) (dlimAdd a' b') := by
  obtain ⟨Ka, haKa, ha'Ka, hAA⟩ := ha
  obtain ⟨Kb, hbKb, hb'Kb, hBB⟩ := hb
  have haK : a.stage ≤ max Ka Kb := by omega
  have hbK : b.stage ≤ max Ka Kb := by omega
  have ha'K : a'.stage ≤ max Ka Kb := by omega
  have hb'K : b'.stage ≤ max Ka Kb := by omega
  have hlhs : max a.stage b.stage ≤ max Ka Kb := by omega
  have hrhs : max a'.stage b'.stage ≤ max Ka Kb := by omega
  refine ⟨max Ka Kb, hlhs, hrhs, ?_⟩
  refine CVecEq_trans (dlimAdd_incl haK hbK hlhs a.vec b.vec)
    (CVecEq_trans (cvAdd_congr ?_ ?_)
      (CVecEq_symm (dlimAdd_incl ha'K hb'K hrhs a'.vec b'.vec)))
  · exact dlimEq_lift (Nat.le_max_left Ka Kb) haKa ha'Ka hAA
  · exact dlimEq_lift (Nat.le_max_right Ka Kb) hbKb hb'Kb hBB

-- ===========================================================================
-- Limit-level complex-module laws (up to `DLimEq`).
-- ===========================================================================

/-- Commutativity of colimit addition. -/
theorem dlimAdd_comm (a b : DLimRaw) : DLimEq (dlimAdd a b) (dlimAdd b a) := by
  have ha : a.stage ≤ max a.stage b.stage := Nat.le_max_left _ _
  have hb : b.stage ≤ max a.stage b.stage := Nat.le_max_right _ _
  have hba : max b.stage a.stage ≤ max a.stage b.stage := by omega
  refine ⟨max a.stage b.stage, Nat.le_refl _, hba, ?_⟩
  refine CVecEq_trans (dlimAdd_incl ha hb (Nat.le_refl _) a.vec b.vec) ?_
  exact CVecEq_trans (cvAdd_comm _ _) (CVecEq_symm (dlimAdd_incl hb ha hba b.vec a.vec))

/-- Associativity of colimit addition. -/
theorem dlimAdd_assoc (a b c : DLimRaw) :
    DLimEq (dlimAdd (dlimAdd a b) c) (dlimAdd a (dlimAdd b c)) := by
  have ha : a.stage ≤ max (max a.stage b.stage) c.stage := by omega
  have hb : b.stage ≤ max (max a.stage b.stage) c.stage := by omega
  have hc : c.stage ≤ max (max a.stage b.stage) c.stage := by omega
  have hab : max a.stage b.stage ≤ max (max a.stage b.stage) c.stage := Nat.le_max_left _ _
  have hbc : max b.stage c.stage ≤ max (max a.stage b.stage) c.stage := by omega
  have hrhs : max a.stage (max b.stage c.stage) ≤ max (max a.stage b.stage) c.stage := by omega
  refine ⟨max (max a.stage b.stage) c.stage, Nat.le_refl _, hrhs, ?_⟩
  refine CVecEq_trans (dlimAdd_incl hab hc (Nat.le_refl _) _ c.vec) ?_
  refine CVecEq_trans (cvAdd_congr (dlimAdd_incl ha hb hab a.vec b.vec) (CVecEq_refl _)) ?_
  refine CVecEq_trans (cvAdd_assoc _ _ _) (CVecEq_symm ?_)
  refine CVecEq_trans (dlimAdd_incl ha hbc hrhs a.vec _) ?_
  exact cvAdd_congr (CVecEq_refl _) (dlimAdd_incl hb hc hbc b.vec c.vec)

/-- `0` is a right identity for colimit addition. -/
theorem dlimAdd_zero (a : DLimRaw) : DLimEq (dlimAdd a dlimZero) a := by
  have ha : a.stage ≤ a.stage := Nat.le_refl _
  have hz : (0 : Nat) ≤ a.stage := Nat.zero_le _
  have hm : max a.stage 0 ≤ a.stage := by omega
  refine ⟨a.stage, hm, Nat.le_refl _, ?_⟩
  refine CVecEq_trans (dlimAdd_incl ha hz hm a.vec (cvZero 0)) ?_
  refine CVecEq_trans (cvAdd_congr (CVecEq_refl _) ?_) (cvAdd_zero (cvInc ha a.vec))
  intro i; simp only [cvInc, cvZero]; split <;> exact Ceq_refl _

/-- `−a` is an additive inverse. -/
theorem dlimAdd_neg (a : DLimRaw) : DLimEq (dlimAdd a (dlimNeg a)) dlimZero := by
  have ha : a.stage ≤ a.stage := Nat.le_refl _
  have hm : max a.stage a.stage ≤ a.stage := by omega
  refine ⟨a.stage, hm, Nat.zero_le _, ?_⟩
  refine CVecEq_trans (dlimAdd_incl ha ha hm a.vec (cvNeg a.vec)) ?_
  refine CVecEq_trans (cvAdd_congr (CVecEq_refl _) (cvInc_neg ha a.vec)) ?_
  refine CVecEq_trans (cvAdd_neg (cvInc ha a.vec)) ?_
  intro i; simp only [cvInc, cvZero]; split <;> exact Ceq_refl _

/-- Scalar multiplication distributes over colimit addition. -/
theorem dlimSmul_dlimAdd (c : Complex) (a b : DLimRaw) :
    DLimEq (dlimSmul c (dlimAdd a b)) (dlimAdd (dlimSmul c a) (dlimSmul c b)) := by
  have ha : a.stage ≤ max a.stage b.stage := Nat.le_max_left _ _
  have hb : b.stage ≤ max a.stage b.stage := Nat.le_max_right _ _
  refine ⟨max a.stage b.stage, Nat.le_refl _, Nat.le_refl _, ?_⟩
  refine CVecEq_trans (cvInc_id _) (CVecEq_trans ?_ (CVecEq_symm (cvInc_id _)))
  exact CVecEq_trans (cvSmul_cvAdd c _ _)
    (cvAdd_congr (CVecEq_symm (cvInc_smul ha c a.vec)) (CVecEq_symm (cvInc_smul hb c b.vec)))

/-- Scalar multiplication distributes over scalar addition. -/
theorem dlimSmul_Cadd (c d : Complex) (a : DLimRaw) :
    DLimEq (dlimSmul (Cadd c d) a) (dlimAdd (dlimSmul c a) (dlimSmul d a)) := by
  have ha : a.stage ≤ a.stage := Nat.le_refl _
  have hmax : max a.stage a.stage ≤ a.stage := Nat.le_of_eq (Nat.max_self a.stage)
  refine ⟨a.stage, Nat.le_refl _, hmax, ?_⟩
  refine CVecEq_trans (cvInc_id _) (CVecEq_trans (cvSmul_Cadd c d a.vec) ?_)
  refine CVecEq_symm (CVecEq_trans (dlimAdd_incl ha ha hmax (cvSmul c a.vec) (cvSmul d a.vec)) ?_)
  exact cvAdd_congr (cvInc_id _) (cvInc_id _)

/-- Scalar-multiplication associativity. -/
theorem dlimSmul_assoc (c d : Complex) (a : DLimRaw) :
    DLimEq (dlimSmul c (dlimSmul d a)) (dlimSmul (Cmul c d) a) :=
  ⟨a.stage, Nat.le_refl _, Nat.le_refl _,
    CVecEq_trans (cvInc_id _) (CVecEq_trans (cvSmul_assoc c d a.vec) (CVecEq_symm (cvInc_id _)))⟩

/-- `1·a = a`. -/
theorem dlimSmul_one (a : DLimRaw) : DLimEq (dlimSmul Cone a) a :=
  ⟨a.stage, Nat.le_refl _, Nat.le_refl _,
    CVecEq_trans (cvInc_id _) (CVecEq_trans (cvSmul_one a.vec) (CVecEq_symm (cvInc_id _)))⟩

/-- `0·a = 0`. -/
theorem dlimZero_smul (a : DLimRaw) : DLimEq (dlimSmul Czero a) dlimZero := by
  refine ⟨a.stage, Nat.le_refl _, Nat.zero_le _, ?_⟩
  refine CVecEq_trans (cvInc_id _) (CVecEq_trans (cvZero_smul a.vec) ?_)
  intro i; simp only [cvInc, cvZero]; split <;> exact Ceq_refl _

/-- `c·0 = 0`. -/
theorem dlimSmul_zero (c : Complex) : DLimEq (dlimSmul c dlimZero) dlimZero :=
  ⟨0, Nat.le_refl _, Nat.le_refl _, fun i => i.elim0⟩

-- ===========================================================================
-- Limit-level inner-product laws (derived from the stagewise `finPreHilbert`).
-- ===========================================================================

/-- Additivity of the colimit inner product in the second slot (derived from
    `(finPreHilbert K).inner_add_right`). -/
theorem dlimInner_add_right (a b c : DLimRaw) :
    Ceq (dlimInner a (dlimAdd b c)) (Cadd (dlimInner a b) (dlimInner a c)) := by
  have haK : a.stage ≤ max a.stage (max b.stage c.stage) := by omega
  have hbK : b.stage ≤ max a.stage (max b.stage c.stage) := by omega
  have hcK : c.stage ≤ max a.stage (max b.stage c.stage) := by omega
  have hbcK : max b.stage c.stage ≤ max a.stage (max b.stage c.stage) := Nat.le_max_right _ _
  refine Ceq_trans (Ceq_symm (dlimInner_eval a (dlimAdd b c) haK hbcK)) ?_
  refine Ceq_trans (cInner_congr (CVecEq_refl _) (dlimAdd_incl hbK hcK hbcK b.vec c.vec)) ?_
  refine Ceq_trans ((finPreHilbert (max a.stage (max b.stage c.stage))).inner_add_right
    (cvInc haK a.vec) (cvInc hbK b.vec) (cvInc hcK c.vec)) ?_
  exact Cadd_congr (dlimInner_eval a b haK hbK) (dlimInner_eval a c haK hcK)

/-- Linearity of the colimit inner product in the second slot (from
    `(finPreHilbert K).inner_smul_right`). -/
theorem dlimInner_smul_right (r : Complex) (a b : DLimRaw) :
    Ceq (dlimInner a (dlimSmul r b)) (Cmul r (dlimInner a b)) := by
  have haK : a.stage ≤ max a.stage b.stage := Nat.le_max_left _ _
  have hbK : b.stage ≤ max a.stage b.stage := Nat.le_max_right _ _
  refine Ceq_trans (Ceq_symm (dlimInner_eval a (dlimSmul r b) haK hbK)) ?_
  refine Ceq_trans (cInner_congr (CVecEq_refl _) (cvInc_smul hbK r b.vec)) ?_
  refine Ceq_trans ((finPreHilbert (max a.stage b.stage)).inner_smul_right r
    (cvInc haK a.vec) (cvInc hbK b.vec)) ?_
  exact Cmul_congr (Ceq_refl r) (dlimInner_eval a b haK hbK)

/-- Hermitian symmetry of the colimit inner product (from `(finPreHilbert K).inner_conj`). -/
theorem dlimInner_conj (a b : DLimRaw) : Ceq (dlimInner a b) (Cconj (dlimInner b a)) := by
  have haK : a.stage ≤ max a.stage b.stage := Nat.le_max_left _ _
  have hbK : b.stage ≤ max a.stage b.stage := Nat.le_max_right _ _
  refine Ceq_trans (Ceq_symm (dlimInner_eval a b haK hbK)) ?_
  refine Ceq_trans ((finPreHilbert (max a.stage b.stage)).inner_conj
    (cvInc haK a.vec) (cvInc hbK b.vec)) ?_
  exact Cconj_congr (dlimInner_eval b a hbK haK)

/-- The colimit diagonal is real (`⟨a, a⟩` has zero imaginary part). Directly `cInner_self_im_zero`
    at the max stage — the two paired vectors are the same by `cvInc` proof-irrelevance. -/
theorem dlimInner_self_im (a : DLimRaw) : Req (dlimInner a a).im zero :=
  cInner_self_im_zero (max a.stage a.stage) (cvInc (Nat.le_max_left a.stage a.stage) a.vec)

/-- The colimit diagonal is nonnegative (positive-semidefiniteness). -/
theorem dlimInner_self_nonneg (a : DLimRaw) : Rnonneg (dlimInner a a).re :=
  cInner_self_re_nonneg (max a.stage a.stage) (cvInc (Nat.le_max_left a.stage a.stage) a.vec)

/-- **POSITIVE-DEFINITENESS at the limit**: `⟨a, a⟩ ≈ 0 ⟹ a ≈ 0` in the colimit setoid — via the
    stagewise definiteness `cInner_self_definite_vec`, then the empty-stage zero. -/
theorem dlimInner_self_definite (a : DLimRaw) (h : Ceq (dlimInner a a) Czero) :
    DLimEq a dlimZero := by
  have hK : a.stage ≤ max a.stage a.stage := Nat.le_max_left _ _
  have hx : CVecEq (cvInc hK a.vec) (cvZero (max a.stage a.stage)) :=
    cInner_self_definite_vec (max a.stage a.stage) (cvInc hK a.vec) h
  refine ⟨max a.stage a.stage, hK, Nat.zero_le _, ?_⟩
  refine CVecEq_trans hx ?_
  intro i; simp only [cvInc, cvZero]; split <;> exact Ceq_refl _

-- ===========================================================================
-- The direct limit, PACKAGED as a `FinPreHilbert` (the SAME record the finite
-- stages instantiate) — the finite-support, infinite-dimensional pre-Hilbert space.
-- ===========================================================================

/-- **The finite-support direct limit as a genuine Bishop pre-Hilbert space.** Every module and
    inner-product law is discharged by the results above; the inner-product laws are DERIVED from the
    stagewise `finPreHilbert` through the isometry `cvIncIso`/`cvInc_inner`. This is the ℓ²-precursor
    the norm completion will complete. -/
def dlimPreHilbert : FinPreHilbert where
  V := DLimRaw
  veq := DLimEq
  add := dlimAdd
  smul := dlimSmul
  vzero := dlimZero
  vneg := dlimNeg
  inner := dlimInner
  veq_refl := DLimEq_refl
  veq_symm := fun h => DLimEq_symm h
  veq_trans := fun h₁ h₂ => DLimEq_trans h₁ h₂
  add_congr := fun ha hb => dlimAdd_wd ha hb
  smul_congr := fun hc hx => dlimSmul_wd hc hx
  add_comm := dlimAdd_comm
  add_assoc := dlimAdd_assoc
  add_zero := dlimAdd_zero
  add_neg := dlimAdd_neg
  smul_add := dlimSmul_dlimAdd
  add_smul := dlimSmul_Cadd
  smul_assoc := dlimSmul_assoc
  one_smul := dlimSmul_one
  zero_smul := dlimZero_smul
  smul_zero := dlimSmul_zero
  inner_congr := fun hx hy => dlimInner_wd hx hy
  inner_add_right := dlimInner_add_right
  inner_smul_right := dlimInner_smul_right
  inner_conj := dlimInner_conj
  inner_self_im := dlimInner_self_im
  inner_self_nonneg := dlimInner_self_nonneg
  inner_self_definite := dlimInner_self_definite

end UOR.Bridge.F1Square.Square
