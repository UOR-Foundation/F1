/-
F1 square — **THE COUPLED WEIL FORM on a fixed `ClosedGeom` core** (`WeilCoupledForm.lean`,
AC-09–AC-13):

    `ArchForm    = PoleForm − (ArchConstForm + ArchTailForm)`
    `CoupledForm = ArchForm − PrimeForm`

with `PrimeForm` the existing genuine two-test prime form (symmetric, biadditive, diagonal
prime-fold readback — reused, not rebuilt).  PROVED: symmetry and biadditivity of `ArchForm` and
`CoupledForm` from the component laws (`PoleForm_*`, `ArchTailForm_*`, `ArchConstForm_*`,
`PrimeForm_*`, support certificates reconciled by `coreTest_add`); THE EXACT OFF-DIAGONAL IDENTITY
`CoupledForm = closedWeilBilin` (real rearrangement of the same four components); and the DIAGONAL
SEMANTIC READBACK `CoupledForm C.g C.g = weilValue (normAutocorrSlotSemantic C)` through
`PoleForm_diag`, `ArchTailForm_diag`, `ArchConstForm_diag`, `PrimeForm_diag_weilPrimePart`.
HONEST SCOPE: these are scalar-valued bilinear forms on tests — no operator, no Gram/PSD claim, no
positivity (= RH) anywhere.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.WeilArchTailLaws

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

/-- **The archimedean form** `ArchForm = PoleForm − (ArchConstForm + ArchTailForm)`. -/
def ArchForm (G : ClosedGeom) (f g : L2Test) (hf : CoreTest G f) (hg : CoreTest G g) : Real :=
  Rsub (PoleForm G f g hf hg)
    (Radd (ArchConstForm f g G.a G.han G.had G.w G.hw G.hwn) (ArchTailForm G f g hf hg))

/-- **The coupled form** `CoupledForm = ArchForm − PrimeForm`. -/
def CoupledForm (G : ClosedGeom) (X : Nat) (f g : L2Test) (hf : CoreTest G f) (hg : CoreTest G g) : Real :=
  Rsub (ArchForm G f g hf hg) (PrimeForm X f g G.a G.han G.had G.w G.hw G.hwn)

-- ===========================================================================
-- (1) Laws of `ArchForm`.
-- ===========================================================================

theorem ArchForm_symm (G : ClosedGeom) (f g : L2Test) (hf : CoreTest G f) (hg : CoreTest G g) :
    Req (ArchForm G f g hf hg) (ArchForm G g f hg hf) :=
  Rsub_congr (PoleForm_symm G f g hf hg)
    (Radd_congr (ArchConstForm_symm f g G.a G.han G.had G.w G.hw G.hwn) (ArchTailForm_symm G f g hf hg))

/-- Abstract: `(P₁+P₂) − ((C₁+C₂) + (T₁+T₂)) = (P₁ − (C₁+T₁)) + (P₂ − (C₂+T₂))`. -/
theorem arch_add_alg (P₁ P₂ C₁ C₂ T₁ T₂ : Real) :
    Req (Rsub (Radd P₁ P₂) (Radd (Radd C₁ C₂) (Radd T₁ T₂)))
        (Radd (Rsub P₁ (Radd C₁ T₁)) (Rsub P₂ (Radd C₂ T₂))) := by
  refine Req_trans (Radd_congr (Req_refl _) (Rneg_congr (Radd_add_add_comm _ _ _ _))) ?_
  refine Req_trans (Radd_congr (Req_refl _) (Rneg_Radd _ _)) ?_
  exact Radd_add_add_comm _ _ _ _

theorem ArchForm_add_left (G : ClosedGeom) (f₁ f₂ g : L2Test) (h₁ : CoreTest G f₁) (h₂ : CoreTest G f₂)
    (hg : CoreTest G g) :
    Req (ArchForm G (L2Test.add f₁ f₂) g (coreTest_add h₁ h₂) hg)
        (Radd (ArchForm G f₁ g h₁ hg) (ArchForm G f₂ g h₂ hg)) :=
  Req_trans (Rsub_congr (PoleForm_add_left G f₁ f₂ g h₁ h₂ hg)
    (Radd_congr (ArchConstForm_add_left f₁ f₂ g G.a G.han G.had G.w G.hw G.hwn)
      (ArchTailForm_add_left G f₁ f₂ g h₁ h₂ hg)))
    (arch_add_alg _ _ _ _ _ _)

theorem ArchForm_add_right (G : ClosedGeom) (f g₁ g₂ : L2Test) (hf : CoreTest G f) (h₁ : CoreTest G g₁)
    (h₂ : CoreTest G g₂) :
    Req (ArchForm G f (L2Test.add g₁ g₂) hf (coreTest_add h₁ h₂))
        (Radd (ArchForm G f g₁ hf h₁) (ArchForm G f g₂ hf h₂)) :=
  Req_trans (Rsub_congr (PoleForm_add_right G f g₁ g₂ hf h₁ h₂)
    (Radd_congr (ArchConstForm_add_right f g₁ g₂ G.a G.han G.had G.w G.hw G.hwn)
      (ArchTailForm_add_right G f g₁ g₂ hf h₁ h₂)))
    (arch_add_alg _ _ _ _ _ _)

-- ===========================================================================
-- (2) Laws of `CoupledForm`.
-- ===========================================================================

theorem CoupledForm_symm (G : ClosedGeom) (X : Nat) (f g : L2Test) (hf : CoreTest G f) (hg : CoreTest G g) :
    Req (CoupledForm G X f g hf hg) (CoupledForm G X g f hg hf) :=
  Rsub_congr (ArchForm_symm G f g hf hg)
    (PrimeForm_symm X f g G.a G.han G.had G.w G.hw G.hwn G.b G.hbd G.hbn hf.hgh hf.hgl hg.hgh hg.hgl G.hfit)

/-- Abstract: `(A₁+A₂) − (Q₁+Q₂) = (A₁ − Q₁) + (A₂ − Q₂)`. -/
theorem coupled_add_alg (A₁ A₂ Q₁ Q₂ : Real) :
    Req (Rsub (Radd A₁ A₂) (Radd Q₁ Q₂)) (Radd (Rsub A₁ Q₁) (Rsub A₂ Q₂)) :=
  Req_trans (Radd_congr (Req_refl _) (Rneg_Radd _ _)) (Radd_add_add_comm _ _ _ _)

theorem CoupledForm_add_left (G : ClosedGeom) (X : Nat) (f₁ f₂ g : L2Test) (h₁ : CoreTest G f₁)
    (h₂ : CoreTest G f₂) (hg : CoreTest G g) :
    Req (CoupledForm G X (L2Test.add f₁ f₂) g (coreTest_add h₁ h₂) hg)
        (Radd (CoupledForm G X f₁ g h₁ hg) (CoupledForm G X f₂ g h₂ hg)) :=
  Req_trans (Rsub_congr (ArchForm_add_left G f₁ f₂ g h₁ h₂ hg)
    (PrimeForm_add_left X f₁ f₂ g G.a G.han G.had G.w G.hw G.hwn))
    (coupled_add_alg _ _ _ _)

theorem CoupledForm_add_right (G : ClosedGeom) (X : Nat) (f g₁ g₂ : L2Test) (hf : CoreTest G f)
    (h₁ : CoreTest G g₁) (h₂ : CoreTest G g₂) :
    Req (CoupledForm G X f (L2Test.add g₁ g₂) hf (coreTest_add h₁ h₂))
        (Radd (CoupledForm G X f g₁ hf h₁) (CoupledForm G X f g₂ hf h₂)) :=
  Req_trans (Rsub_congr (ArchForm_add_right G f g₁ g₂ hf h₁ h₂)
    (PrimeForm_add_right X f g₁ g₂ G.a G.han G.had G.w G.hw G.hwn))
    (coupled_add_alg _ _ _ _)

-- ===========================================================================
-- (3) THE EXACT IDENTITY with `closedWeilBilin` and the diagonal semantic readback.
-- ===========================================================================

/-- Abstract: `(P − (C + T)) − Q = P − (Q + (C + T))`. -/
theorem coupled_ident_alg (P C T Q : Real) :
    Req (Rsub (Rsub P (Radd C T)) Q) (Rsub P (Radd Q (Radd C T))) := by
  refine Req_trans (Radd_assoc _ _ _) ?_
  refine Radd_congr (Req_refl _) ?_
  exact Req_trans (Radd_comm _ _) (Req_symm (Rneg_Radd _ _))

/-- **THE EXACT OFF-DIAGONAL IDENTITY** `CoupledForm = closedWeilBilin` (same four constructed
    components, rearranged). -/
theorem CoupledForm_eq_closedWeilBilin (G : ClosedGeom) (X : Nat) (f g : L2Test) (hf : CoreTest G f)
    (hg : CoreTest G g) :
    Req (CoupledForm G X f g hf hg) (closedWeilBilin G X f g hf hg) :=
  coupled_ident_alg _ _ _ _

/-- **THE DIAGONAL SEMANTIC READBACK**: on the context's own test the coupled form is the Weil
    functional of the semantic slot (pole = independent Mellin pole, tail = independent unsplit
    archimedean integral) — via `PoleForm_diag`, `ArchTailForm_diag`, `ArchConstForm_diag`,
    `PrimeForm_diag_weilPrimePart`. -/
theorem CoupledForm_diag_semantic (C : NormCtx) :
    Req (CoupledForm C.geom C.X C.g C.g (normCtx_core C) (normCtx_core C))
        (weilValue (normAutocorrSlotSemantic C)) :=
  Req_trans (CoupledForm_eq_closedWeilBilin C.geom C.X C.g C.g (normCtx_core C) (normCtx_core C))
    (closedWeilBilin_diag_semantic C)

/-- The readback spelled out: `CoupledForm(g,g) = MellinPole − (weilPrimePart + (weilArchConst + ArchIntegral))`. -/
theorem CoupledForm_diag_components (C : NormCtx) :
    Req (CoupledForm C.geom C.X C.g C.g (normCtx_core C) (normCtx_core C))
        (Rsub (MellinPole C C.g C.g)
          (Radd (weilPrimePart (normAutocorrTest C))
            (Radd (weilArchConst (normAutocorrTest C))
              (ArchIntegral C C.g C.g (normCtx_core C) (normCtx_core C))))) :=
  CoupledForm_diag_semantic C

end UOR.Bridge.F1Square.Square
