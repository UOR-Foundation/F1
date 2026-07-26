/-
F1 square — **reconstruction from moment data alone** (`MomentInversionRaw.lean`), the Mellin-inversion
front. The Bernstein–Durrmeyer operator `durrOp φ` already reads `φ` only through its moment sequence
(`durrOp_eq_momData`). This brick makes that explicit as an operator on a *raw* moment sequence
`μ : Nat → Real`, decoupled from any test:

  `durrOpMom μ n x = (n+1)·Σ_k b_{n,k}(x)·C(n,k)·(Δⁿ⁻ᵏμ)_k`,

with `durrOpMom (mellinMoment φ) = durrOp φ` (`durrOpMom_eq_durrOp`) and the reconstruction rate
`|durrOpMom (mellinMoment φ) ((k+3)²−2) x − φ(x)| ≤ φ.L/(k+3)` on `[0,1]` (`durrOpMom_converges`). So a
bounded-Lipschitz test is recovered **from its moment sequence alone** — the transform pair's inversion
stated purely on the moment data, the direction the surjectivity question asks about.

HONEST SCOPE. The reconstruction operator on raw moment sequences, and its convergence on the moment
sequences that arise from the bounded-Lipschitz class (`μ = mellinMoment φ`). It does NOT characterise
which raw sequences are moment sequences (the Hausdorff/complete-monotonicity question), NOT a completed
L² space, NOT positivity. Step 4 is RH; the crux fields stay `none`.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Square.DurrmeyerTendsTo

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

/-- **Raw forward finite differences** of an abstract moment sequence `μ`, the same Pascal recursion as
    `momDiff` but reading `μ` directly rather than a test's moments. -/
def momDiffRaw (μ : Nat → Real) (k : Nat) : Nat → Real
  | 0 => μ k
  | m + 1 => Rsub (momDiffRaw μ k m) (momDiffRaw μ (k + 1) m)

/-- `natScaleR` respects `Req` in its real argument. -/
private theorem natScaleR_congr_raw {a b : Real} (hab : Req a b) :
    ∀ k, Req (natScaleR k a) (natScaleR k b)
  | 0 => Req_refl _
  | k + 1 => Radd_congr hab (natScaleR_congr_raw hab k)

/-- **`momDiff` is the raw difference of the moment sequence**: `momDiff φ k m = (Δᵐ(mellinMoment φ))_k`.
    Both are the identical Pascal recursion, and `momDiff φ k 0 = mellinMoment φ k` definitionally. -/
theorem momDiff_eq_raw (φ : L2Test) (k : Nat) :
    ∀ m, Req (momDiff φ k m) (momDiffRaw (mellinMoment φ) k m)
  | 0 => Req_refl _
  | m + 1 => Rsub_congr (momDiff_eq_raw φ k m) (momDiff_eq_raw φ (k + 1) m)

/-- **THE DURRMEYER RECONSTRUCTION OPERATOR ON A RAW MOMENT SEQUENCE**: reads only `μ`, no test. -/
def durrOpMom (μ : Nat → Real) (n : Nat) (x : Real) : Real :=
  Rmul (RofNat (n + 1))
    (RsumN (fun k => Rmul (bernR x n k) (natScaleR (choose n k) (momDiffRaw μ k (n - k)))) (n + 1))

/-- Raw finite differences respect `Req` of the moment sequence. -/
theorem momDiffRaw_congr {μ ν : Nat → Real} (h : ∀ n, Req (μ n) (ν n)) (k : Nat) :
    ∀ m, Req (momDiffRaw μ k m) (momDiffRaw ν k m)
  | 0 => h k
  | m + 1 => Rsub_congr (momDiffRaw_congr h k m) (momDiffRaw_congr h (k + 1) m)

/-- **The reconstruction depends only on the moment sequence's values**: `Req`-equal moment sequences
    give `Req` reconstructions. -/
theorem durrOpMom_congr {μ ν : Nat → Real} (h : ∀ n, Req (μ n) (ν n)) (n : Nat) (x : Real) :
    Req (durrOpMom μ n x) (durrOpMom ν n x) :=
  Rmul_congr (Req_refl _) (RsumN_congr (n + 1) (fun k _ =>
    Rmul_congr (Req_refl _) (natScaleR_congr_raw (momDiffRaw_congr h k (n - k)) (choose n k))))

/-- **THE OPERATOR READS ONLY THE MOMENTS**: `durrOpMom (mellinMoment φ) = durrOp φ`, so the whole
    Durrmeyer reconstruction is a function of the moment sequence alone. -/
theorem durrOpMom_eq_durrOp (φ : L2Test) (n : Nat) (x : Real) :
    Req (durrOpMom (mellinMoment φ) n x) (durrOp φ n x) := by
  refine Req_trans ?_ (Req_symm (durrOp_eq_momData φ n x))
  refine Rmul_congr (Req_refl _) (RsumN_congr (n + 1) (fun k _ => ?_))
  exact Rmul_congr (Req_refl _)
    (natScaleR_congr_raw (Req_symm (momDiff_eq_raw φ k (n - k))) (choose n k))

/-- **★ RECONSTRUCTION FROM MOMENT DATA ALONE**: a bounded-Lipschitz test is recovered from its moment
    sequence at the certified rate `|durrOpMom (mellinMoment φ) ((k+3)²−2) x − φ(x)| ≤ φ.L/(k+3)` on
    `[0,1]` — the transform pair's inversion stated purely on the moments. -/
theorem durrOpMom_converges (φ : L2Test) (x : Real) (h0 : Rle zero x) (h1 : Rle x one) (k : Nat) :
    Rle (Rabs (Rsub (durrOpMom (mellinMoment φ) ((k + 3) * (k + 3) - 2) x) (φ.f x)))
        (ofQ (mul φ.L (⟨1, k + 3⟩ : Q)) (Qmul_den_pos φ.hLd (Nat.succ_pos (k + 2)))) := by
  refine Rle_trans (Rle_of_Req (Rabs_congr (Rsub_congr
    (durrOpMom_eq_durrOp φ ((k + 3) * (k + 3) - 2) x) (Req_refl _)))) ?_
  exact durrOp_converges φ x h0 h1 k

end UOR.Bridge.F1Square.Square
