/-
F1 square — the dynamical zeta / **Euler product** over tropical primes (**R5**), kernel-checked —
completing another realization of the UOR content-addressing / cycle-dynamics stack.

Companion `characteristic_1_constructions.md` §3: the Artin–Mazur / Bowen–Lanford dynamical zeta of the
running example's 0/1 adjacency `B = adjOfW` (`WalkCounts.lean`) factors over the primitive cycles
(tropical primes) and equals the reciprocal determinant, `∏_{primitive γ} (1 − t^{|γ|})^{-1} =
1/det(I − tB)`, a RATIONAL function (Bowen–Lanford). Term-by-term:

    `det(I − tB) = 1 − t² − 2t³`,
    `1/det(I − tB) = 1 + t² + 2t³ + t⁴ + 4t⁵ + 5t⁶ + 6t⁷ + 13t⁸ + …`    (`R5`).

Kernel-checked with a minimal integer-polynomial layer: `R5_det` computes the characteristic
denominator `det(I − tB)` from `B` (a 4×4 polynomial determinant), and `R5_euler_product` verifies the
zeta series is its reciprocal to order 8 — `det(I−tB) · zeta ≡ 1 (mod t⁹)` — the "Euler product = zeta,
verified term-by-term." The dynamical zeta factors over the tropical primes exactly as `ζ` factors over
the primes; the cycles are the prime closed orbits.

HONEST SCOPE. Finite integer-polynomial / closed-walk computation — an embeddings-model realization,
independent of RH and of the ζ/Li stack (no `λ`, no zeros, no `StieltjesEta`). It is the characteristic-1
Euler-product SHADOW, not the ζ Euler product; the crux fields stay `none`.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; `by decide`.
-/

import F1Square.Tropical.WalkCounts

namespace UOR.Bridge.F1Square.Tropical

/-- A polynomial as its coefficient list (low degree first), over `ℤ`. -/
abbrev Poly : Type := List Int

/-- Polynomial addition (coefficientwise, with the longer tail carried over). -/
def pAdd : Poly → Poly → Poly
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: pAdd p q

/-- Polynomial negation. -/
def pNeg (p : Poly) : Poly := p.map (fun a => -a)

/-- Polynomial multiplication (convolution). -/
def pMul : Poly → Poly → Poly
  | [], _ => []
  | a :: p, q => pAdd (q.map (fun b => a * b)) (0 :: pMul p q)

/-- Delete index `k` from a list (for extracting matrix minors). -/
def dropIdx {α : Type} (k : Nat) (xs : List α) : List α := xs.take k ++ xs.drop (k + 1)

/-- The `(0,j)` minor of a polynomial matrix: drop row `0` and column `j`. -/
def pMinor (m : List (List Poly)) (j : Nat) : List (List Poly) :=
  (dropIdx 0 m).map (dropIdx j)

/-- Determinant of an `n×n` polynomial matrix by cofactor expansion along the first row
    (`n` = explicit fuel = matrix size). -/
def pDetN : Nat → List (List Poly) → Poly
  | 0,     _ => [1]
  | n + 1, m =>
    (List.range (n + 1)).foldl (fun acc j =>
      let term := pMul ((m.getD 0 []).getD j []) (pDetN n (pMinor m j))
      pAdd acc (if j % 2 = 0 then term else pNeg term)) []

/-- The polynomial matrix `I − t·B` for `B = adjOfW`: entry `(i,j)` is the degree-1 polynomial
    `[δᵢⱼ, −Bᵢⱼ]` (constant `δᵢⱼ`, `t`-coefficient `−Bᵢⱼ`). -/
def IminusTB : List (List Poly) :=
  (List.range 4).map (fun i => (List.range 4).map (fun j =>
    [(if i = j then (1 : Int) else 0), -(nGet adjOfW i j : Int)]))

/-- **The characteristic denominator** `det(I − tB) = 1 − t² − 2t³`, computed from `B = adjOfW`
    (coefficient list `[1, 0, −1, −2]`). One adjacency eigenvalue is `0`, dropping the degree to 3. -/
theorem R5_det : (pDetN 4 IminusTB).take 4 = [1, 0, -1, -2] := by decide

/-- **R5.** The Euler product = dynamical zeta, verified term-by-term: `1/det(I − tB) =
    1 + t² + 2t³ + t⁴ + 4t⁵ + 5t⁶ + 6t⁷ + 13t⁸ + …`. Checked as `det(I−tB) · zeta ≡ 1 (mod t⁹)`, i.e.
    the coefficient list of the product truncated to degree 8 is the unit `[1,0,…,0]`. So the zeta
    series `[1,0,1,2,1,4,5,6,13]` is the reciprocal of `det(I−tB)` to order 8 — the dynamical zeta
    factors over the tropical primes (cycles) exactly as `ζ` factors over the primes, and is rational. -/
theorem R5_euler_product :
    (pMul (pDetN 4 IminusTB) [1, 0, 1, 2, 1, 4, 5, 6, 13]).take 9
      = [1, 0, 0, 0, 0, 0, 0, 0, 0] := by decide

/-- A degree-`≤3` integer polynomial `[c₀,c₁,c₂,c₃]` evaluated at `t = p/q` and cleared by `q³`:
    `c₀·q³ + c₁·p·q² + c₂·p²·q + c₃·p³` — the sign of the true value at `p/q` (for `q > 0`). -/
def clearedEval3 (c : Poly) (p q : Int) : Int :=
  c.getD 0 0 * q ^ 3 + c.getD 1 0 * p * q ^ 2 + c.getD 2 0 * p ^ 2 * q + c.getD 3 0 * p ^ 3

/-- **The dynamical zeta's leading pole = the topological-entropy base, bracketed** (a fragment of the
    prime-orbit theorem R8). The zeta's smallest positive pole is the smallest positive root `t*` of the
    denominator `det(I − tB) = 1 − t² − 2t³` (`R5_det`), and `t* = 1/ρ(B)` for `ρ(B)` the Perron
    eigenvalue = `e^{h}`, `h` the topological entropy. The denominator changes sign between `t = 13/20`
    and `t = 33/50`: positive at `0.65` (`clearedEval3 … 13 20 = 226 > 0`), negative at `0.66`
    (`clearedEval3 … 33 50 = −1324 < 0`), computed directly from the determinant. So `t* ∈ (0.65, 0.66)`,
    i.e. `ρ(B) ∈ (1.51, 1.54)` and `h = log ρ(B) ∈ (0.41, 0.44)` — consistent with the doc's
    `h ≈ 0.4196`. (The full asymptotic `π(L) ~ e^{hL}/L` is analysis, not formalized here.) -/
theorem entropy_pole_bracket :
    0 < clearedEval3 (pDetN 4 IminusTB) 13 20
    ∧ clearedEval3 (pDetN 4 IminusTB) 33 50 < 0 := by decide

end UOR.Bridge.F1Square.Tropical
