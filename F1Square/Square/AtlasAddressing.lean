/-
F1 square — **Atlas addressing: a FINITE FIXTURE of the scale-invariant addressing tower**
(`AtlasAddressing.lean`). HONEST-SCOPE REPAIR (operator-frontier checkpoint, task 1): this module is
a *finite fixture* of the first levels of the addressing tower (§2/§5/§8), NOT an unbounded prime
skeleton and NOT the full explicit-formula prime side.

WHAT IS ACTUALLY BUILT (finite fixture, all proved):
- `atlasPrime` is a **4-entry table** (`0,1,2,3 ↦ 5,7,11,13`), returning `0` for every `k ≥ 4`
  (`atlasPrime_finite`). It is a fixture, not an enumeration of the primes.
- Consequently the modulus tower `atlasModulus` **degenerates to `0`** from `k = 5` on
  (`atlasModulus_degenerate`: `atlasModulus (k+5) = 0`). The genuine values are the four fixtures
  `m_0..m_3 = 96, 480, 3360, 36960` (`atlasModulus_values`) — with `m_4 = 36960·13 = 480480` and
  `m_k = 0` thereafter. So `atlasModulus_dvd_succ` holds for every `k`, but *vacuously* past the
  fixture (everything divides `0`); there is **no terminal inverse limit `A_∞`** constructed here.
- The von Mangoldt weights are carried for the **finite prime set `{2,3,5}`** only
  (`atlas_prime_skeleton`), i.e. `Λ(p) = log p` for three primes — a finite fixture of the
  explicit-formula prime side, **not** "the left side in full".

WHAT IS NOT BUILT (the honest gap, OPEN): an exact *unbounded* prime enumeration `Nat → Nat` with a
proof that each value is prime and that the moduli stay nonzero, and the terminal inverse limit
`A_∞ = lim A_k` as the `Spec ℤ` prime skeleton. Implementing that (or discharging it as a named
obligation) is the addressing side of the operator contract; it is not present. No claim of a full
prime skeleton is retained.

STATUS: finite fixture (proved) + the unbounded skeleton OPEN. This module asserts nothing about
positivity, the archimedean place, or the operator; the crux fields stay `none`.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Square.AtlasCharacteristics
import F1Square.Analysis.Mangoldt

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- §5/§8 — the addressing tower, AS A FINITE FIXTURE.
-- ===========================================================================

/-- The chain-prime **fixture table**: `0,1,2,3 ↦ 5,7,11,13` and `0` for every `k ≥ 4`
    (`atlasPrime_finite`). This is a finite table, NOT a prime enumeration — beyond index 3 the
    tower degenerates. -/
def atlasPrime : Nat → Nat
  | 0 => 5
  | 1 => 7
  | 2 => 11
  | 3 => 13
  | _ => 0

/-- **The table is finite**: `atlasPrime k = 0` for every `k ≥ 4` — the honest scope, making the
    tower's degeneration explicit. -/
theorem atlasPrime_finite : ∀ k, 4 ≤ k → atlasPrime k = 0
  | 0, h => absurd h (by decide)
  | 1, h => absurd h (by decide)
  | 2, h => absurd h (by decide)
  | 3, h => absurd h (by decide)
  | _ + 4, _ => rfl

/-- The addressing modulus tower `m_0 = 96`, `m_{k+1} = m_k · atlasPrime k`. Because `atlasPrime`
    is a finite fixture, this DEGENERATES to `0` from `k = 5` on (`atlasModulus_degenerate`); only
    `m_0..m_4` are the intended nonzero fixtures. -/
def atlasModulus : Nat → Nat
  | 0 => 96
  | k + 1 => atlasModulus k * atlasPrime k

/-- **The four fixture moduli** (Atlas §5): `96, 480, 3360, 36960`. These are the genuine tower
    levels; the tower does not extend (see `atlasModulus_degenerate`). -/
theorem atlasModulus_values :
    atlasModulus 0 = 96 ∧ atlasModulus 1 = 480
    ∧ atlasModulus 2 = 3360 ∧ atlasModulus 3 = 36960 := by decide

/-- **The tower DEGENERATES**: `atlasModulus (k+5) = 0` for every `k` — because `atlasPrime 4 = 0`
    forces `m_5 = m_4 · 0 = 0` and zero propagates. So there is no unbounded modulus tower and no
    terminal `A_∞` here; this is the explicit honest boundary of the fixture. -/
theorem atlasModulus_degenerate : ∀ k, atlasModulus (k + 5) = 0
  | 0 => by decide
  | k + 1 => by
      show atlasModulus (k + 5) * atlasPrime (k + 5) = 0
      rw [atlasModulus_degenerate k]; exact Nat.zero_mul _

/-- **`m_0 = 2^(O−T)·T = 2⁵·3 = 96`** (Atlas §8): the base modulus is `2`-adically deep (`2⁵`) and
    carries the single factor `T = 3`. -/
theorem atlasModulus_zero_factored : (96 : Nat) = 2 ^ (8 - 3) * 3 := by decide

/-- **Divisibility `m_k ∣ m_{k+1}`** for every `k` — a projection exists at every level. NOTE: past
    the fixture (`k ≥ 4`) this holds *vacuously* (`m_{k+1} = 0`, and everything divides `0`), so it
    does NOT witness a genuine infinite inverse system; only the fixture levels are substantive
    (`atlasModulus_degenerate`). -/
theorem atlasModulus_dvd_succ (k : Nat) : atlasModulus k ∣ atlasModulus (k + 1) :=
  ⟨atlasPrime k, rfl⟩

/-- **The base boundary `B_k = m_k · 2^(O−1) = m_k · 128`** (Atlas §2/§5), a fixture value. -/
def atlasBoundary (k : Nat) : Nat := atlasModulus k * 2 ^ (8 - 1)

/-- The base boundary `B_0 = 96·128 = 12288` (Atlas §2). -/
theorem atlasBoundary_zero : atlasBoundary 0 = 12288 := by decide

-- ===========================================================================
-- §8 — the parametric constants (a fact about {T,O}, not about the tower's length).
-- ===========================================================================

/-- **Parametric generation** (Atlas §8): the class count `2^(O−T)·T = 96`, stride `T·O = 24`,
    scope `2^(O−2T) = 4`, context `2^(O−1) = 128` — the model's numbers as this family at
    `(T,O) = (3,8)`. (A statement about the constants, independent of the tower's finiteness.) -/
theorem atlas_parametric_generation :
    (2 ^ (8 - 3) * 3 = 96)        -- class count
    ∧ (3 * 8 = 24)                -- stride T·O
    ∧ (2 ^ (8 - 2 * 3) = 4)       -- scope 2^(O−2T)
    ∧ (2 ^ (8 - 1) = 128) := by   -- 2^(O−1)
  decide

-- ===========================================================================
-- §10/§12 — von Mangoldt weights for the FINITE fixture prime set {2,3,5}.
-- ===========================================================================

/-- A bounded primality certificate for a concrete `p`: checking divisors up to `p` suffices
    (`d ∣ p ⟹ d ≤ p`), so primality is decidable for a literal. -/
theorem primality_of_bounded {p : Nat} (hp0 : 0 < p)
    (h : ∀ d, d < p + 1 → (d ∣ p → d = 1 ∨ d = p)) :
    ∀ d, d ∣ p → d = 1 ∨ d = p :=
  fun d hd => h d (Nat.lt_succ_of_le (Nat.le_of_dvd hp0 hd)) hd

/-- **The fixture prime `5` carries `Λ(5) = log 5`** — the first chain prime past the base `{2,3}`. -/
theorem atlasPrime_five_vonMangoldt : Req (vonMangoldt 5) (logN 5 (by omega)) :=
  vonMangoldt_prime (by omega) (primality_of_bounded (by omega) (by decide))

/-- **The fixture carries `Λ(p) = log p` for the FINITE prime set `{2,3,5}`** — three primes, a
    finite fixture of the explicit-formula prime side. This is NOT the full prime skeleton: the
    table stops (`atlasPrime_finite`) and the tower degenerates (`atlasModulus_degenerate`). The
    unbounded prime side and the archimedean coupling are the open content; the crux stays `none`. -/
theorem atlas_prime_skeleton :
    Req (vonMangoldt 2) (logN 2 (by omega))
    ∧ Req (vonMangoldt 3) (logN 3 (by omega))
    ∧ Req (vonMangoldt 5) (logN 5 (by omega)) :=
  ⟨vonMangoldt_two, vonMangoldt_three, atlasPrime_five_vonMangoldt⟩

end UOR.Bridge.F1Square.Square
