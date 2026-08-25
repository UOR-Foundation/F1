/-
F1 square — **the complete closed Weil bilinear form and its acceptance theorem**
(`ClosedWeilBilin.lean`):

  `closedWeilBilin = PoleForm − (PrimeForm + ArchConstForm + ArchTailForm)`

with EVERY component CONSTRUCTED (no free `Real` inputs anywhere):
  • `PoleForm`      — the improper `∫₁^∞ (F_{f,g}+F_{g,f})(1+1/x) dx` (decay proved);
  • `PrimeForm`     — the symmetric biadditive finite-prime Haar fold (all-scale reciprocity);
  • `ArchConstForm` — `(log 4π + γ)·B₁(f,g)` from the built constants;
  • `ArchTailForm`  — `½·(Reg + Near + Far)`: the split-kernel archimedean tail
      `∫₁^∞ (F_{f,g}+F_{g,f}−2F(1)/x)/(x−x⁻¹) dx` with the `x = 1` treated by the PROVED lower-end
      improper limit (`ArchNearPart`) and the `−2F(1)/(x²−1)` subtraction tail RETAINED in the
      improper regular/far parts.

`NormCtx.geom` derives the closed geometry CANONICALLY from a `NormCtx` — `Bd := B := N := X+1`,
`hband := hband_hi`, `hBdS := hTS` — no extra data, no arbitrary geometry; `normCtx_core` shows the
context's own test is a core test (its support data, never vacuous by fiat).
`normAutocorrSlotConstructed C` is a `WeilSlot` whose `poles` and `archTail` are the CONSTRUCTED
`PoleForm`/`ArchTailForm` diagonals — NO free `Real` inputs.

**`closedWeilBilin_diag`** — the ASSEMBLY (packaging) lemma: on the diagonal `(C.g, C.g)` the closed
form equals `weilValue (normAutocorrSlotConstructed C)`, whose pole/tail fields are the constructed
integrals themselves (their readback is definitional).  The SEMANTIC acceptance theorem — both hard
fields independent — is `closedWeilBilin_diag_semantic` (`WeilArchSemantic.lean`): pole field
`MellinPole` via `PoleForm_diag` (`WeilMellinPole.lean`), tail field `ArchIntegral` via
`ArchTailForm_diag` (`WeilArchIdent.lean`/`WeilArchSemantic.lean`).  The exact off-diagonal identity
with the coupled form is `CoupledForm_eq_closedWeilBilin` (`WeilCoupledForm.lean`).  Positivity of the
closed form (= RH) is asserted NOWHERE.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.WeilArchNear

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- (1) The complete archimedean tail.
-- ===========================================================================

/-- **THE COMPLETE ARCHIMEDEAN TAIL** `ArchTailForm(f,g) = ½·(Reg + Near + Far)` — the split-kernel
    realization of `∫₁^∞ (F_{f,g}+F_{g,f}−2F_{f,g}(1)/x)/(x−x⁻¹) dx` (partial fractions
    `1/(x−x⁻¹) = ½(1/(x−1)+1/(x+1))` on `x > 1`): the regular part (kernel `1/(x+1)`, improper), the
    near part (the PROVED `x = 1` lower-end improper limit), and the far part (`∫₂^∞ N/(x−1)`,
    improper) — each CONSTRUCTED with proved decay/regularity, the subtraction tail RETAINED. -/
def ArchTailForm (G : ClosedGeom) (f g : L2Test) (hf : CoreTest G f) (hg : CoreTest G g) : Real :=
  Rmul (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1))
    (Radd (ArchRegPart G f g hf hg)
      (Radd (ArchNearPart G f g) (ArchFarPart G f g hf hg)))

-- ===========================================================================
-- (2) The closed geometry, derived CANONICALLY from a `NormCtx` (no extra data).
-- ===========================================================================

/-- **The canonical closed geometry of a `NormCtx`** — every field derives from the context:
    `Bd := X+1` (the support bound), `B := X+1` (the weight band cap), `N := X+1` (the scale witness),
    `hband := hband_hi`, `hBdS := hTS`.  NO arbitrary geometry. -/
def NormCtx.geom (C : NormCtx) : ClosedGeom where
  S := C.S
  hSd := C.hSd
  hSn := C.hSn
  hS1 := C.hS1
  a := C.a
  han := C.han
  had := C.had
  w := C.w
  hw := C.hw
  hwn := C.hwn
  b := C.b
  hbd := C.hbd
  hbn := C.hbnpos
  hfit := C.hfit
  B := ⟨((C.X + 1 : Nat) : Int), 1⟩
  hBd := Nat.one_pos
  hB1 := by
    show (1 : Int) * ((1 : Nat) : Int) ≤ ((C.X + 1 : Nat) : Int) * ((1 : Nat) : Int)
    push_cast
    omega
  N := C.X + 1
  hN := Nat.succ_pos C.X
  hBN := Qle_refl _
  Bd := ⟨((C.X + 1 : Nat) : Int), 1⟩
  hBdd := Nat.one_pos
  hBd1 := by
    show (1 : Int) * ((1 : Nat) : Int) ≤ ((C.X + 1 : Nat) : Int) * ((1 : Nat) : Int)
    push_cast
    omega
  hband := C.hband_hi
  hBdS := C.hTS
  hBdB := Qle_refl _

/-- The context's own test is a core test for its canonical geometry (from `NormCtx.hgh/hgl` —
    the test domain is exactly the context's support data, never vacuous by fiat). -/
theorem normCtx_core (C : NormCtx) : CoreTest C.geom C.g where
  hgh := C.hgh
  hgl := C.hgl

-- ===========================================================================
-- (3) The complete closed Weil form.
-- ===========================================================================

/-- **★ THE COMPLETE CLOSED WEIL BILINEAR FORM**
    `closedWeilBilin = PoleForm − (PrimeForm + ArchConstForm + ArchTailForm)` — every component a
    CONSTRUCTED integral/fold of the two tests over the fixed geometry.  NO free `Real` inputs. -/
def closedWeilBilin (G : ClosedGeom) (X : Nat) (f g : L2Test)
    (hf : CoreTest G f) (hg : CoreTest G g) : Real :=
  Rsub (PoleForm G f g hf hg)
    (Radd (PrimeForm X f g G.a G.han G.had G.w G.hw G.hwn)
      (Radd (ArchConstForm f g G.a G.han G.had G.w G.hw G.hwn)
        (ArchTailForm G f g hf hg)))

/-- **THE CONSTRUCTED SLOT** — `poles` and `archTail` are the CONSTRUCTED `PoleForm`/`ArchTailForm`
    diagonals of the context's own test.  NO free `Real` inputs (contrast `normAutocorrSlot`). -/
def normAutocorrSlotConstructed (C : NormCtx) : WeilSlot where
  test := normAutocorrTest C
  poles := PoleForm C.geom C.g C.g (normCtx_core C) (normCtx_core C)
  archTail := ArchTailForm C.geom C.g C.g (normCtx_core C) (normCtx_core C)

/-- **THE ASSEMBLY (PACKAGING) LEMMA** — superseded as an acceptance theorem by
    `closedWeilBilin_diag_semantic`: on the diagonal, the closed Weil bilinear form IS the Weil
    functional of the constructed slot —

      `closedWeilBilin C.geom C.X C.g C.g ≈ weilValue (normAutocorrSlotConstructed C)`

    for EVERY `NormCtx` (geometry canonical, no free data): the finite-prime side is
    `weilPrimePart (normAutocorrTest)` (`PrimeForm_diag_weilPrimePart`), the archimedean constant is
    `weilArchConst (normAutocorrTest)` (`ArchConstForm_diag`), and the pole/tail fields are the
    constructed integrals themselves (definitional readback — see `closedWeilBilin_diag_semantic`
    for the substantive one).  The slot has NO free `poles`/`archTail`.  Positivity of either side
    (= RH) is asserted NOWHERE. -/
theorem closedWeilBilin_diag (C : NormCtx) :
    Req (closedWeilBilin C.geom C.X C.g C.g (normCtx_core C) (normCtx_core C))
        (weilValue (normAutocorrSlotConstructed C)) := by
  show Req
    (Rsub (PoleForm C.geom C.g C.g (normCtx_core C) (normCtx_core C))
      (Radd (PrimeForm C.X C.g C.g C.a C.han C.had C.w C.hw C.hwn)
        (Radd (ArchConstForm C.g C.g C.a C.han C.had C.w C.hw C.hwn)
          (ArchTailForm C.geom C.g C.g (normCtx_core C) (normCtx_core C)))))
    (Rsub (PoleForm C.geom C.g C.g (normCtx_core C) (normCtx_core C))
      (Radd (weilPrimePart (normAutocorrTest C))
        (Radd (weilArchConst (normAutocorrTest C))
          (ArchTailForm C.geom C.g C.g (normCtx_core C) (normCtx_core C)))))
  exact Rsub_congr (Req_refl _)
    (Radd_congr (PrimeForm_diag_weilPrimePart C)
      (Radd_congr (ArchConstForm_diag C) (Req_refl _)))

end UOR.Bridge.F1Square.Square
