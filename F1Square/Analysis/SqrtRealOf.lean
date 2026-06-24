/-
F1 square — **square-root Lipschitz bound and the real-radicand √**.

The constructive √ of a *rational* (`Rsqrt`) is Lipschitz-½ on `[1, ∞)`:
`|√x − √y| ≤ ½|x − y|` for `x, y ≥ 1` (`Rsqrt_lipschitz`). The engine is the difference-of-squares
factoring `(√x − √y)(√x + √y) = x − y` (from `(√·)² = ·`) divided through by `√x + √y ≥ 2` — but the
lower bound `2 ≤ |√x + √y|` is read off `√x + √y ≥ 2` via `x ≤ |x|` (no `|·|`-of-nonnegative needed),
keeping the argument multiplicative throughout (`Rabs_Rmul`).

This is the regularity modulus (`½ · 2/(j+1) = 1/(j+1)`) for the real-radicand square root: the limit
of the rational √'s of the (clamped-to-`≥1`) rational approximants of `a ≥ 1` — the `√t` factor of the
theta modular transform at a real argument.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by `scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.SqrtRealCmp
import F1Square.Analysis.RabsLemmas

namespace UOR.Bridge.F1Square.Analysis

/-- `(ofQ a) − (ofQ b) ≈ ofQ (a − b)` (both are pointwise constant `a − b`). -/
private theorem Rsub_ofQ {a b : Q} (ha : 0 < a.den) (hb : 0 < b.den) :
    Req (Rsub (ofQ a ha) (ofQ b hb)) (ofQ (Qsub a b) (Qsub_den_pos ha hb)) :=
  Req_of_seq_Qeq (fun _ => Qeq_refl _)

/-- `½ · 2 · x ≈ x`. -/
private theorem Rhalf_two_mul (x : Real) :
    Req (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) x)) x := by
  refine Req_trans (Req_symm (Rmul_assoc _ _ _)) ?_
  refine Req_trans (Rmul_congr (Rmul_ofQ_ofQ (by decide) (by decide)) (Req_refl _)) ?_
  refine Req_trans (Rmul_congr
    (ofQ_congr (by decide) (by decide) (by decide : Qeq (mul (⟨1, 2⟩ : Q) (⟨2, 1⟩ : Q)) (⟨1, 1⟩ : Q)))
    (Req_refl _)) ?_
  exact Req_trans (Rmul_comm _ x) (Rmul_one x)

/-- **`Rsqrt` is Lipschitz-½ on `[1, ∞)`**: `|√x − √y| ≤ ½|x − y|` for rationals `x, y ≥ 1`. -/
theorem Rsqrt_lipschitz {x y : Q} (hxd : 0 < x.den) (hyd : 0 < y.den)
    (hx0 : Qle (⟨0, 1⟩ : Q) x) (hy0 : Qle (⟨0, 1⟩ : Q) y)
    (hx1 : Qle (⟨1, 1⟩ : Q) x) (hy1 : Qle (⟨1, 1⟩ : Q) y) :
    Rle (Rabs (Rsub (Rsqrt x hxd hx0) (Rsqrt y hyd hy0)))
        (ofQ (mul (⟨1, 2⟩ : Q) (Qabs (Qsub x y)))
          (Qmul_den_pos (by decide) (Qabs_den_pos (Qsub_den_pos hxd hyd)))) := by
  let s := Rsqrt x hxd hx0
  let t := Rsqrt y hyd hy0
  -- `2 ≤ |s + t|`, from `s, t ≥ 1` and `u ≤ |u|`.
  have hreq2 : Req (ofQ (⟨2, 1⟩ : Q) (by decide)) (Radd one one) :=
    Req_trans (ofQ_congr (by decide) (add_den_pos (by decide) (by decide))
        (by decide : Qeq (⟨2, 1⟩ : Q) (add (⟨1, 1⟩ : Q) (⟨1, 1⟩ : Q))))
      (Req_symm (Radd_ofQ_ofQ (by decide) (by decide)))
  have h2st : Rle (ofQ (⟨2, 1⟩ : Q) (by decide)) (Rabs (Radd s t)) :=
    Rle_trans (Rle_trans (Rle_of_Req hreq2)
        (Radd_le_add (Rsqrt_ge_one hxd hx0 hx1) (Rsqrt_ge_one hyd hy0 hy1)))
      (Rle_Rabs_self (Radd s t))
  -- `(s − t)(s + t) ≈ ofQ (x − y)`, so `|s − t|·|s + t| ≈ ofQ |x − y|`.
  have hprod : Req (Rmul (Rsub s t) (Radd s t)) (ofQ (Qsub x y) (Qsub_den_pos hxd hyd)) :=
    Req_trans (Rmul_sub_add_self s t)
      (Req_trans (Rsub_congr (Rsqrt_sq x hxd hx0) (Rsqrt_sq y hyd hy0))
        (Rsub_ofQ hxd hyd))
  have habs : Req (Rmul (Rabs (Rsub s t)) (Rabs (Radd s t)))
      (ofQ (Qabs (Qsub x y)) (Qabs_den_pos (Qsub_den_pos hxd hyd))) :=
    Req_trans (Req_symm (Rabs_Rmul (Rsub s t) (Radd s t)))
      (Req_trans (Rabs_congr hprod) (Rabs_ofQ (Qsub_den_pos hxd hyd)))
  -- `2·|s − t| ≤ |s + t|·|s − t| = |s − t|·|s + t| ≈ ofQ |x − y|`.
  have hchain : Rle (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) (Rabs (Rsub s t)))
      (ofQ (Qabs (Qsub x y)) (Qabs_den_pos (Qsub_den_pos hxd hyd))) :=
    Rle_trans (Rmul_le_Rmul_right (Rnonneg_Rabs (Rsub s t)) h2st)
      (Rle_of_Req (Req_trans (Rmul_comm (Rabs (Radd s t)) (Rabs (Rsub s t))) habs))
  -- multiply by `½ ≥ 0`: `|s − t| ≈ ½·2·|s − t| ≤ ½·ofQ|x − y| = ofQ (½|x − y|)`.
  refine Rle_trans (Rle_of_Req (Req_symm (Rhalf_two_mul (Rabs (Rsub s t))))) ?_
  refine Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ (by decide) (by decide)) hchain) ?_
  exact Rle_of_Req (Rmul_ofQ_ofQ (by decide) (Qabs_den_pos (Qsub_den_pos hxd hyd)))

end UOR.Bridge.F1Square.Analysis
