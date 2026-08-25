/-
F1 square — **THE SUBSTANTIVE `ArchTailForm_diag` and the semantic acceptance theorem**
(`WeilArchSemantic.lean`):

  • `ArchTailForm_diag C : ArchTailForm C.geom C.g C.g = ArchIntegral C C.g C.g` — the constructed
    split tail equals the INDEPENDENTLY defined unsplit archimedean integral of the context's own test
    (`ArchIntegral_eq_ArchTailForm`, no field copied);
  • `normAutocorrSlotSemantic C` — the slot with BOTH hard fields independent:
        `poles := MellinPole C C.g C.g`,  `archTail := ArchIntegral C C.g C.g`;
  • **`closedWeilBilin_diag_semantic`** — `closedWeilBilin` on the diagonal equals the Weil functional
    of that slot, discharged by `PoleForm_diag` and `ArchTailForm_diag` (both substantive) and the
    prime/archimedean-constant readbacks: NO component-level reflexivity for either hard field.
Positivity of either side (= RH) is asserted NOWHERE.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.WeilArchIdent

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

/-- **THE SUBSTANTIVE `ArchTailForm_diag`**: on the diagonal the constructed archimedean tail is the
    independent unsplit archimedean integral of the context's own test. -/
theorem ArchTailForm_diag (C : NormCtx) :
    Req (ArchTailForm C.geom C.g C.g (normCtx_core C) (normCtx_core C))
        (ArchIntegral C C.g C.g (normCtx_core C) (normCtx_core C)) :=
  Req_symm (ArchIntegral_eq_ArchTailForm C C.g C.g (normCtx_core C) (normCtx_core C))

/-- **THE SEMANTIC SLOT**: both hard fields are the INDEPENDENT objects — the two-window Mellin pole
    term and the unsplit archimedean integral — of the context's own test. -/
def normAutocorrSlotSemantic (C : NormCtx) : WeilSlot where
  test := normAutocorrTest C
  poles := MellinPole C C.g C.g
  archTail := ArchIntegral C C.g C.g (normCtx_core C) (normCtx_core C)

/-- **★★ THE SEMANTIC ACCEPTANCE THEOREM**: `closedWeilBilin` on the diagonal IS the Weil functional of
    the semantic slot — pole component by `PoleForm_diag` (folding theorem), archimedean tail by
    `ArchTailForm_diag` (unsplit-integral identification), finite-prime side by
    `PrimeForm_diag_weilPrimePart`, archimedean constant by `ArchConstForm_diag`.  No field is copied;
    no component is discharged by reflexivity. -/
theorem closedWeilBilin_diag_semantic (C : NormCtx) :
    Req (closedWeilBilin C.geom C.X C.g C.g (normCtx_core C) (normCtx_core C))
        (weilValue (normAutocorrSlotSemantic C)) := by
  show Req
    (Rsub (PoleForm C.geom C.g C.g (normCtx_core C) (normCtx_core C))
      (Radd (PrimeForm C.X C.g C.g C.a C.han C.had C.w C.hw C.hwn)
        (Radd (ArchConstForm C.g C.g C.a C.han C.had C.w C.hw C.hwn)
          (ArchTailForm C.geom C.g C.g (normCtx_core C) (normCtx_core C)))))
    (Rsub (MellinPole C C.g C.g)
      (Radd (weilPrimePart (normAutocorrTest C))
        (Radd (weilArchConst (normAutocorrTest C))
          (ArchIntegral C C.g C.g (normCtx_core C) (normCtx_core C)))))
  exact Rsub_congr (PoleForm_diag C)
    (Radd_congr (PrimeForm_diag_weilPrimePart C)
      (Radd_congr (ArchConstForm_diag C) (ArchTailForm_diag C)))

end UOR.Bridge.F1Square.Square
