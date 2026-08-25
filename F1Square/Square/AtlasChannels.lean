/-
F1 square — **address-indexed cut and cycle channels of the Atlas fiber** (`AtlasChannels.lean`).

For an Atlas address `(d, ℓ)` (`d < 3`, `ℓ < 8`) two rank-one fiber vectors are sourced:

    `p_ℓ(x)    = x · (𝟙 ⊗ (2/3)·e_ℓ)`                       (a CUT vector: image of `Bᵀ`),
    `q_{d,ℓ}(x) = x · ((e_d − e_{d+1}) ⊗ (e_ℓ − e_{ℓ+1}))`      (a four-CYCLE: kernel of `B`),

with `[v, w]_M := ⟨v, M w⟩ = pairF v (atlasOp w)` the physical Atlas pairing.  THE CHANNEL LAWS,
proved UNIFORMLY over every valid address (`pCh_pCh`, `qCh_qCh`, `pCh_qCh`, `qCh_pCh`):

    `[p(x), p(y)]_M = 4xy`,   `[q(x), q(y)]_M = −4xy`,   `[p(x), q(y)]_M = [q(x), p(y)]_M = 0`.

The readback values do not depend on the address: the address is a GAUGE (`classDecode` may select
one deterministically downstream; nothing here claims a semantic scale-to-class map).  All from the
single rank-one formula `pairF_tens_M` for `⟨s⊗t, M(s'⊗t')⟩`.  Pure finite Atlas algebra.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasBundle

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- `RsumN` is never unfolded here (all sums go through lemmas); sealing it stops the unifier from
-- expanding `RsumN _ 8` / `RsumN _ 3` into `Radd` towers on a failed syntactic match.
attribute [local irreducible] RsumN

-- ===========================================================================
-- (0) Small real-algebra helpers (local names).
-- ===========================================================================

theorem Rzero_mul_ch (x : Real) : Req (Rmul zero x) zero :=
  Req_trans (Rmul_comm zero x) (Rmul_zero x)

/-- `(a·b)·(c·d) ≈ (a·c)·(b·d)`. -/
theorem mul4_swap_ch (a b c d : Real) :
    Req (Rmul (Rmul a b) (Rmul c d)) (Rmul (Rmul a c) (Rmul b d)) := by
  refine Req_trans (Rmul_assoc a b (Rmul c d)) ?_
  refine Req_trans (Rmul_congr (Req_refl a) (Req_symm (Rmul_assoc b c d))) ?_
  refine Req_trans (Rmul_congr (Req_refl a) (Rmul_congr (Rmul_comm b c) (Req_refl d))) ?_
  refine Req_trans (Rmul_congr (Req_refl a) (Rmul_assoc c b d)) ?_
  exact Req_symm (Rmul_assoc a c (Rmul b d))

/-- `(a·b)·(c·d) ≈ (a·(c·d))·b`. -/
theorem mul4_swap2_ch (a b c d : Real) :
    Req (Rmul (Rmul a b) (Rmul c d)) (Rmul (Rmul a (Rmul c d)) b) := by
  refine Req_trans (Rmul_assoc a b (Rmul c d)) ?_
  refine Req_trans (Rmul_congr (Req_refl a) (Rmul_comm b (Rmul c d))) ?_
  exact Req_symm (Rmul_assoc a (Rmul c d) b)

-- ===========================================================================
-- (1) Rank-one fiber vectors and the general `M`-pairing formula.
-- ===========================================================================

/-- The rank-one fiber vector `(s ⊗ t)_{ij} = s_i · t_j`. -/
def tens (s t : Nat → Real) (i j : Nat) : Real := Rmul (s i) (t j)

/-- `s · s' = Σ_{i<n} s_i s'_i`. -/
def dotN (s s' : Nat → Real) (n : Nat) : Real := RsumN (fun i => Rmul (s i) (s' i)) n

theorem rowSum_tens (s t : Nat → Real) (i : Nat) :
    Req (rowSum (tens s t) i) (Rmul (s i) (RsumN t 8)) :=
  RsumN_smul_ai (s i) t 8

theorem colSum_tens (s t : Nat → Real) (j : Nat) :
    Req (colSum (tens s t) j) (Rmul (RsumN s 3) (t j)) :=
  RsumN_smul_right_ai (t j) s 3

/-- `M(s'⊗t')_{ij} = (Σs')·t'_j + s'_i·(Σt') − s'_i t'_j`. -/
theorem atlasOp_tens (s' t' : Nat → Real) (i j : Nat) :
    Req (atlasOp (tens s' t') i j)
        (Rsub (Radd (Rmul (RsumN s' 3) (t' j)) (Rmul (s' i) (RsumN t' 8))) (Rmul (s' i) (t' j))) :=
  Rsub_congr (Radd_congr (colSum_tens s' t' j) (rowSum_tens s' t' i)) (Req_refl _)

/-- The pointwise expansion `(s_i t_j)·(S' t'_j + s'_i T' − s'_i t'_j)`. -/
theorem tens_pt_expand (si tj S' t'j s'i T' : Real) :
    Req (Rmul (Rmul si tj) (Rsub (Radd (Rmul S' t'j) (Rmul s'i T')) (Rmul s'i t'j)))
        (Radd (Rmul (Rmul si S') (Rmul tj t'j))
              (Rsub (Rmul (Rmul si (Rmul s'i T')) tj) (Rmul (Rmul si s'i) (Rmul tj t'j)))) := by
  refine Req_trans (Rmul_sub_distrib _ _ _) ?_
  refine Req_trans (Rsub_congr (Rmul_distrib _ _ _) (mul4_swap_ch si tj s'i t'j)) ?_
  refine Req_trans (Rsub_congr (Radd_congr (mul4_swap_ch si tj S' t'j) (mul4_swap2_ch si tj s'i T'))
    (Req_refl _)) ?_
  -- (A + B) − C ≈ A + (B − C)
  exact Radd_assoc _ _ _

/-- **THE RANK-ONE `M`-PAIRING FORMULA**
    `⟨s⊗t, M(s'⊗t')⟩ = (Σs)(Σs')·(t·t') + ((s·s')·(Σt'))·(Σt) − (s·s')·(t·t')`. -/
theorem pairF_tens_M (s t s' t' : Nat → Real) :
    Req (pairF (tens s t) (atlasOp (tens s' t')))
        (Radd (Rmul (Rmul (RsumN s 3) (RsumN s' 3)) (dotN t t' 8))
              (Rsub (Rmul (Rmul (dotN s s' 3) (RsumN t' 8)) (RsumN t 8))
                    (Rmul (dotN s s' 3) (dotN t t' 8)))) := by
  unfold pairF dotN
  -- names for the four scalar sums
  generalize hS' : RsumN s' 3 = S'
  generalize hT' : RsumN t' 8 = T'
  generalize hT : RsumN t 8 = T
  generalize hTT : RsumN (fun j => Rmul (t j) (t' j)) 8 = TT
  -- pointwise expansion
  have hpt : ∀ i j, Req (Rmul (tens s t i j) (atlasOp (tens s' t') i j))
      (Radd (Rmul (Rmul (s i) S') (Rmul (t j) (t' j)))
            (Rsub (Rmul (Rmul (s i) (Rmul (s' i) T')) (t j))
                  (Rmul (Rmul (s i) (s' i)) (Rmul (t j) (t' j))))) := by
    intro i j
    have h1 := atlasOp_tens s' t' i j
    rw [hS', hT'] at h1
    exact Req_trans (Rmul_congr (Req_refl (tens s t i j)) h1) (tens_pt_expand (s i) (t j) S' (t' j) (s' i) T')
  -- inner sums over `j`
  have hin : ∀ i, Req (RsumN (fun j => Rmul (tens s t i j) (atlasOp (tens s' t') i j)) 8)
      (Radd (Rmul (Rmul (s i) S') TT)
            (Rsub (Rmul (Rmul (s i) (Rmul (s' i) T')) T)
                  (Rmul (Rmul (s i) (s' i)) TT))) := by
    intro i
    refine Req_trans (RsumN_congr (F := fun j => Rmul (tens s t i j) (atlasOp (tens s' t') i j)) (G := fun j =>
      Radd (Rmul (Rmul (s i) S') (Rmul (t j) (t' j)))
           (Rsub (Rmul (Rmul (s i) (Rmul (s' i) T')) (t j))
                 (Rmul (Rmul (s i) (s' i)) (Rmul (t j) (t' j))))) 8 (fun j _ => hpt i j)) ?_
    have hA := RsumN_smul_ai (Rmul (s i) S') (fun j => Rmul (t j) (t' j)) 8
    have hB := RsumN_smul_ai (Rmul (s i) (Rmul (s' i) T')) t 8
    have hC := RsumN_smul_ai (Rmul (s i) (s' i)) (fun j => Rmul (t j) (t' j)) 8
    rw [hTT] at hA hC
    rw [hT] at hB
    refine Req_trans (RsumN_Radd (fun j => Rmul (Rmul (s i) S') (Rmul (t j) (t' j)))
      (fun j => Rsub (Rmul (Rmul (s i) (Rmul (s' i) T')) (t j)) (Rmul (Rmul (s i) (s' i)) (Rmul (t j) (t' j)))) 8) ?_
    refine Radd_congr hA ?_
    refine Req_trans (RsumN_Rsub (fun j => Rmul (Rmul (s i) (Rmul (s' i) T')) (t j))
      (fun j => Rmul (Rmul (s i) (s' i)) (Rmul (t j) (t' j))) 8) ?_
    exact Rsub_congr hB hC
  refine Req_trans (RsumN_congr (F := fun i => RsumN (fun j => Rmul (tens s t i j) (atlasOp (tens s' t') i j)) 8)
    (G := fun i => Radd (Rmul (Rmul (s i) S') TT)
            (Rsub (Rmul (Rmul (s i) (Rmul (s' i) T')) T) (Rmul (Rmul (s i) (s' i)) TT))) 3
    (fun i _ => hin i)) ?_
  refine Req_trans (RsumN_Radd (fun i => Rmul (Rmul (s i) S') TT)
    (fun i => Rsub (Rmul (Rmul (s i) (Rmul (s' i) T')) T) (Rmul (Rmul (s i) (s' i)) TT)) 3) ?_
  refine Radd_congr ?_ ?_
  · -- Σ_i (s_i S')·TT = (S·S')·TT
    have hA := RsumN_smul_right_ai TT (fun i => Rmul (s i) S') 3
    have hA2 := RsumN_smul_right_ai S' s 3
    exact Req_trans hA (Rmul_congr hA2 (Req_refl TT))
  · refine Req_trans (RsumN_Rsub (fun i => Rmul (Rmul (s i) (Rmul (s' i) T')) T)
      (fun i => Rmul (Rmul (s i) (s' i)) TT) 3) ?_
    have hC := RsumN_smul_right_ai TT (fun i => Rmul (s i) (s' i)) 3
    refine Rsub_congr ?_ hC
    -- Σ_i (s_i (s'_i T'))·T = ((s·s')·T')·T
    have hB := RsumN_smul_right_ai T (fun i => Rmul (s i) (Rmul (s' i) T')) 3
    refine Req_trans hB (Rmul_congr ?_ (Req_refl T))
    refine Req_trans (RsumN_congr (F := fun i => Rmul (s i) (Rmul (s' i) T'))
      (G := fun i => Rmul (Rmul (s i) (s' i)) T') 3
      (fun i _ => Req_symm (Rmul_assoc (s i) (s' i) T'))) ?_
    exact RsumN_smul_right_ai T' (fun i => Rmul (s i) (s' i)) 3

-- ===========================================================================
-- (2) Indicators and signed pairs.
-- ===========================================================================

/-- `e_k(i) = [i = k]`. -/
def indicCh (k i : Nat) : Real := if i = k then one else zero

/-- `e_k − e_{k'}`. -/
def sgCh (k k' i : Nat) : Real := Rsub (indicCh k i) (indicCh k' i)

theorem RsumN_indic (k n : Nat) (hk : k < n) : Req (RsumN (indicCh k) n) one :=
  RsumN_indicator_ai (fun _ => one) k n hk

/-- `Σ_i c·e_k(i) = c`. -/
theorem RsumN_smul_indic (c : Real) (k n : Nat) (hk : k < n) :
    Req (RsumN (fun i => Rmul c (indicCh k i)) n) c :=
  Req_trans (RsumN_smul_ai c (indicCh k) n) (Req_trans (Rmul_congr (Req_refl c) (RsumN_indic k n hk)) (Rmul_one c))

/-- `(c·e_k(i))·(c'·e_k(i)) ≈ [i = k]·(c c')` pointwise. -/
theorem smul_indic_sq_pt (c c' : Real) (k i : Nat) :
    Req (Rmul (Rmul c (indicCh k i)) (Rmul c' (indicCh k i))) (if i = k then Rmul c c' else zero) := by
  unfold indicCh
  by_cases h : i = k
  · rw [if_pos h, if_pos h]
    exact Rmul_congr (Rmul_one c) (Rmul_one c')
  · rw [if_neg h, if_neg h]
    exact Req_trans (Rmul_congr (Rmul_zero c) (Req_refl _)) (Rzero_mul_ch _)

theorem dotN_smul_indic (c c' : Real) (k n : Nat) (hk : k < n) :
    Req (dotN (fun i => Rmul c (indicCh k i)) (fun i => Rmul c' (indicCh k i)) n) (Rmul c c') := by
  unfold dotN
  refine Req_trans (RsumN_congr (G := fun i => if i = k then Rmul c c' else zero) n
    (fun i _ => smul_indic_sq_pt c c' k i)) ?_
  exact RsumN_indicator_ai (fun _ => Rmul c c') k n hk

/-- `Σ_i (e_k − e_{k'})(i) = 0` for `k, k' < n`. -/
theorem RsumN_sg (k k' n : Nat) (hk : k < n) (hk' : k' < n) : Req (RsumN (sgCh k k') n) zero := by
  unfold sgCh
  refine Req_trans (RsumN_Rsub _ _ n) ?_
  exact Req_trans (Rsub_congr (RsumN_indic k n hk) (RsumN_indic k' n hk')) (Radd_neg one)

/-- `(e_k − e_{k'})(i)² ≈ e_k(i) + e_{k'}(i)` for `k ≠ k'`. -/
theorem sg_sq_pt (k k' i : Nat) (hkk : k ≠ k') :
    Req (Rmul (sgCh k k' i) (sgCh k k' i)) (Radd (indicCh k i) (indicCh k' i)) := by
  unfold sgCh indicCh
  by_cases h : i = k
  · have h' : ¬ (i = k') := by intro h2; exact hkk (h.symm.trans h2)
    rw [if_pos h, if_neg h']
    have h1 : Req (Rsub one zero) one := Rsub_zero one
    exact Req_trans (Rmul_congr h1 h1) (Req_trans (Rmul_one one) (Req_symm (Radd_zero one)))
  · rw [if_neg h]
    by_cases h' : i = k'
    · rw [if_pos h']
      have h1 : Req (Rsub zero one) (Rneg one) :=
        Req_trans (Radd_comm zero (Rneg one)) (Radd_zero (Rneg one))
      refine Req_trans (Rmul_congr h1 h1) ?_
      refine Req_trans (Rmul_neg_left _ _) ?_
      refine Req_trans (Rneg_congr (Rmul_neg_right _ _)) ?_
      refine Req_trans (Rneg_neg _) ?_
      exact Req_trans (Rmul_one one) (Req_symm (Req_trans (Radd_comm zero one) (Radd_zero one)))
    · rw [if_neg h']
      have h1 : Req (Rsub zero zero) zero := Radd_neg zero
      exact Req_trans (Rmul_congr h1 h1) (Req_trans (Rmul_zero zero) (Req_symm (Radd_zero zero)))

/-- `Σ_i (e_k − e_{k'})(i)² = 1 + 1` for distinct `k, k' < n`. -/
theorem dotN_sg (k k' n : Nat) (hk : k < n) (hk' : k' < n) (hkk : k ≠ k') :
    Req (dotN (sgCh k k') (sgCh k k') n) (Radd one one) := by
  unfold dotN
  refine Req_trans (RsumN_congr (G := fun i => Radd (indicCh k i) (indicCh k' i)) n
    (fun i _ => sg_sq_pt k k' i hkk)) ?_
  exact Req_trans (RsumN_Radd _ _ n) (Radd_congr (RsumN_indic k n hk) (RsumN_indic k' n hk'))

/-- `Σ_i x·sgCh(i) = 0`. -/
theorem RsumN_smul_sg (x : Real) (k k' n : Nat) (hk : k < n) (hk' : k' < n) :
    Req (RsumN (fun i => Rmul x (sgCh k k' i)) n) zero :=
  Req_trans (RsumN_smul_ai x _ n) (Req_trans (Rmul_congr (Req_refl x) (RsumN_sg k k' n hk hk')) (Rmul_zero x))

/-- `Σ_i (x·sgCh(i))(y·sgCh(i)) = (x·y)·(1 + 1)`. -/
theorem dotN_smul_sg (x y : Real) (k k' n : Nat) (hk : k < n) (hk' : k' < n) (hkk : k ≠ k') :
    Req (dotN (fun i => Rmul x (sgCh k k' i)) (fun i => Rmul y (sgCh k k' i)) n)
        (Rmul (Rmul x y) (Radd one one)) := by
  unfold dotN
  refine Req_trans (RsumN_congr (G := fun i => Rmul (Rmul x y) (Rmul (sgCh k k' i) (sgCh k k' i))) n
    (fun i _ => mul4_swap_ch x _ y _)) ?_
  refine Req_trans (RsumN_smul_ai _ _ n) (Rmul_congr (Req_refl _) ?_)
  exact dotN_sg k k' n hk hk' hkk

/-- `Σ_i x·(y·sgCh(i)) = 0`. -/
theorem dotN_const_smul_sg (x y : Real) (k k' n : Nat) (hk : k < n) (hk' : k' < n) :
    Req (dotN (fun _ => x) (fun i => Rmul y (sgCh k k' i)) n) zero := by
  unfold dotN
  refine Req_trans (RsumN_smul_ai x _ n) ?_
  exact Req_trans (Rmul_congr (Req_refl x) (RsumN_smul_sg y k k' n hk hk')) (Rmul_zero x)

/-- `Σ_i (x·sgCh(i))·y = 0`. -/
theorem dotN_smul_sg_const (x y : Real) (k k' n : Nat) (hk : k < n) (hk' : k' < n) :
    Req (dotN (fun i => Rmul x (sgCh k k' i)) (fun _ => y) n) zero := by
  unfold dotN
  refine Req_trans (RsumN_smul_right_ai y _ n) ?_
  exact Req_trans (Rmul_congr (RsumN_smul_sg x k k' n hk hk') (Req_refl y)) (Rzero_mul_ch y)


-- ===========================================================================
-- (3) The channels.
-- ===========================================================================

/-- `2/3`. -/
def c23 : Real := ofQ (⟨2, 3⟩ : Q) (by decide)
/-- `4`. -/
def c4 : Real := ofQ (⟨4, 1⟩ : Q) Nat.one_pos

/-- **The cut channel at column address `ℓ`**: `p_ℓ(x) = x · (𝟙 ⊗ (2/3)e_ℓ)`. -/
def pCh (ℓ : Nat) (x : Real) : Nat → Nat → Real :=
  tens (fun _ => x) (fun j => Rmul c23 (indicCh ℓ j))

/-- **The cycle channel at address `(d, ℓ)`**: `q_{d,ℓ}(x) = x · ((e_d − e_{d+1}) ⊗ (e_ℓ − e_{ℓ+1}))`
    (row and column successors taken mod `3`, `8`). -/
def qCh (d ℓ : Nat) (x : Real) : Nat → Nat → Real :=
  tens (fun i => Rmul x (sgCh d ((d + 1) % 3) i)) (sgCh ℓ ((ℓ + 1) % 8))

theorem succ_mod3 : ∀ d : Nat, d < 3 → (d + 1) % 3 < 3 ∧ d ≠ (d + 1) % 3
  | 0, _ => by decide
  | 1, _ => by decide
  | 2, _ => by decide
  | (n + 3), h => absurd h (by omega)
theorem succ_mod8 : ∀ ℓ : Nat, ℓ < 8 → (ℓ + 1) % 8 < 8 ∧ ℓ ≠ (ℓ + 1) % 8
  | 0, _ => by decide
  | 1, _ => by decide
  | 2, _ => by decide
  | 3, _ => by decide
  | 4, _ => by decide
  | 5, _ => by decide
  | 6, _ => by decide
  | 7, _ => by decide
  | (n + 8), h => absurd h (by omega)

/-- `(3x)(3y)·((2/3)(2/3)) ≈ 4·(xy)`. -/
theorem pp_const_collapse (x y : Real) :
    Req (Rmul (Rmul (Rmul (RofNat 3) x) (Rmul (RofNat 3) y)) (Rmul c23 c23)) (Rmul c4 (Rmul x y)) := by
  refine Req_trans (Rmul_congr (mul4_swap_ch _ _ _ _) (Req_refl _)) ?_
  refine Req_trans (Rmul_assoc _ _ _) ?_
  refine Req_trans (Rmul_congr (Req_refl _) (Rmul_comm _ _)) ?_
  refine Req_trans (Req_symm (Rmul_assoc _ _ _)) ?_
  refine Rmul_congr ?_ (Req_refl _)
  -- (3·3)·((2/3)(2/3)) ≈ 4
  refine Req_trans (Rmul_congr (Rmul_ofQ_ofQ Nat.one_pos Nat.one_pos) (Rmul_ofQ_ofQ (by decide) (by decide))) ?_
  refine Req_trans (Rmul_ofQ_ofQ _ _) ?_
  exact ofQ_congr _ Nat.one_pos (by decide)

/-- `((xy)(1+1))(1+1) ≈ 4·(xy)`. -/
theorem qq_const_collapse (x y : Real) :
    Req (Rmul (Rmul (Rmul x y) (Radd one one)) (Radd one one)) (Rmul c4 (Rmul x y)) := by
  refine Req_trans (Rmul_assoc _ _ _) ?_
  refine Req_trans (Rmul_comm _ _) ?_
  refine Rmul_congr ?_ (Req_refl _)
  have h2 : Req (Radd one one) (ofQ (⟨2, 1⟩ : Q) Nat.one_pos) := Radd_ofQ_ofQ (by decide) (by decide)
  refine Req_trans (Rmul_congr h2 h2) ?_
  refine Req_trans (Rmul_ofQ_ofQ Nat.one_pos Nat.one_pos) ?_
  exact ofQ_congr _ Nat.one_pos (by decide)

/-- **`[p(x), p(y)]_M = 4xy`** at every column address `ℓ < 8`. -/
theorem pCh_pCh (ℓ : Nat) (hℓ : ℓ < 8) (x y : Real) :
    Req (pairF (pCh ℓ x) (atlasOp (pCh ℓ y))) (Rmul c4 (Rmul x y)) := by
  unfold pCh
  refine Req_trans (pairF_tens_M _ _ _ _) ?_
  have hS : Req (RsumN (fun _ => x) 3) (Rmul (RofNat 3) x) := RsumN_const x 3
  have hS' : Req (RsumN (fun _ => y) 3) (Rmul (RofNat 3) y) := RsumN_const y 3
  have hTT : Req (dotN (fun j => Rmul c23 (indicCh ℓ j)) (fun j => Rmul c23 (indicCh ℓ j)) 8) (Rmul c23 c23) :=
    dotN_smul_indic c23 c23 ℓ 8 hℓ
  have hT : Req (RsumN (fun j => Rmul c23 (indicCh ℓ j)) 8) c23 := RsumN_smul_indic c23 ℓ 8 hℓ
  have hSS : Req (dotN (fun _ => x) (fun _ => y) 3) (Rmul (RofNat 3) (Rmul x y)) := RsumN_const (Rmul x y) 3
  refine Req_trans (Radd_congr (Rmul_congr (Rmul_congr hS hS') hTT)
    (Rsub_congr (Rmul_congr (Rmul_congr hSS hT) hT) (Rmul_congr hSS hTT))) ?_
  -- the second group cancels: ((SS'·c)·c) − SS'·(c·c) ≈ 0
  have hcancel : Req (Rsub (Rmul (Rmul (Rmul (RofNat 3) (Rmul x y)) c23) c23)
      (Rmul (Rmul (RofNat 3) (Rmul x y)) (Rmul c23 c23))) zero :=
    Req_trans (Rsub_congr (Rmul_assoc _ _ _) (Req_refl _)) (Radd_neg _)
  refine Req_trans (Radd_congr (Req_refl _) hcancel) ?_
  exact Req_trans (Radd_zero _) (pp_const_collapse x y)

/-- **`[q(x), q(y)]_M = −4xy`** at every address `d < 3`, `ℓ < 8`. -/
theorem qCh_qCh (d ℓ : Nat) (hd : d < 3) (hℓ : ℓ < 8) (x y : Real) :
    Req (pairF (qCh d ℓ x) (atlasOp (qCh d ℓ y))) (Rneg (Rmul c4 (Rmul x y))) := by
  unfold qCh
  obtain ⟨hd3, hdd⟩ := succ_mod3 d hd
  obtain ⟨hℓ8, hℓℓ⟩ := succ_mod8 ℓ hℓ
  refine Req_trans (pairF_tens_M _ _ _ _) ?_
  have hS : Req (RsumN (fun i => Rmul x (sgCh d ((d + 1) % 3) i)) 3) zero := RsumN_smul_sg x _ _ 3 hd hd3
  have hS' : Req (RsumN (fun i => Rmul y (sgCh d ((d + 1) % 3) i)) 3) zero := RsumN_smul_sg y _ _ 3 hd hd3
  have hT : Req (RsumN (sgCh ℓ ((ℓ + 1) % 8)) 8) zero := RsumN_sg _ _ 8 hℓ hℓ8
  have hTT : Req (dotN (sgCh ℓ ((ℓ + 1) % 8)) (sgCh ℓ ((ℓ + 1) % 8)) 8) (Radd one one) := dotN_sg _ _ 8 hℓ hℓ8 hℓℓ
  have hSS : Req (dotN (fun i => Rmul x (sgCh d ((d + 1) % 3) i)) (fun i => Rmul y (sgCh d ((d + 1) % 3) i)) 3)
      (Rmul (Rmul x y) (Radd one one)) := dotN_smul_sg x y _ _ 3 hd hd3 hdd
  refine Req_trans (Radd_congr (Rmul_congr (Rmul_congr hS hS') hTT)
    (Rsub_congr (Rmul_congr (Rmul_congr hSS hT) hT) (Rmul_congr hSS hTT))) ?_
  have h1 : Req (Rmul (Rmul zero zero) (Radd one one)) zero :=
    Req_trans (Rmul_congr (Rmul_zero zero) (Req_refl _)) (Rzero_mul_ch _)
  have h2 : Req (Rmul (Rmul (Rmul (Rmul x y) (Radd one one)) zero) zero) zero := Rmul_zero _
  refine Req_trans (Radd_congr h1 (Rsub_congr h2 (Req_refl _))) ?_
  refine Req_trans (Radd_comm _ _) ?_
  refine Req_trans (Radd_zero _) ?_
  refine Req_trans (Radd_comm _ _) ?_
  refine Req_trans (Radd_zero _) ?_
  exact Rneg_congr (qq_const_collapse x y)

/-- **`[p(x), q(y)]_M = 0`** at every address. -/
theorem pCh_qCh (d ℓ : Nat) (hd : d < 3) (hℓ : ℓ < 8) (x y : Real) :
    Req (pairF (pCh ℓ x) (atlasOp (qCh d ℓ y))) zero := by
  unfold pCh qCh
  obtain ⟨hd3, _⟩ := succ_mod3 d hd
  obtain ⟨hℓ8, _⟩ := succ_mod8 ℓ hℓ
  refine Req_trans (pairF_tens_M _ _ _ _) ?_
  have hS' : Req (RsumN (fun i => Rmul y (sgCh d ((d + 1) % 3) i)) 3) zero := RsumN_smul_sg y _ _ 3 hd hd3
  have hT' : Req (RsumN (sgCh ℓ ((ℓ + 1) % 8)) 8) zero := RsumN_sg _ _ 8 hℓ hℓ8
  have hSS : Req (dotN (fun _ => x) (fun i => Rmul y (sgCh d ((d + 1) % 3) i)) 3) zero :=
    dotN_const_smul_sg x y _ _ 3 hd hd3
  refine Req_trans (Radd_congr (Rmul_congr (Rmul_congr (Req_refl _) hS') (Req_refl _))
    (Rsub_congr (Rmul_congr (Rmul_congr hSS hT') (Req_refl _)) (Rmul_congr hSS (Req_refl _)))) ?_
  refine Req_trans (Radd_congr
    (Req_trans (Rmul_congr (Rmul_zero _) (Req_refl _)) (Rzero_mul_ch _))
    (Rsub_congr (Req_trans (Rmul_congr (Rmul_zero _) (Req_refl _)) (Rzero_mul_ch _)) (Rzero_mul_ch _))) ?_
  exact Req_trans (Radd_congr (Req_refl _) (Radd_neg zero)) (Radd_zero zero)

/-- **`[q(x), p(y)]_M = 0`** at every address. -/
theorem qCh_pCh (d ℓ : Nat) (hd : d < 3) (hℓ : ℓ < 8) (x y : Real) :
    Req (pairF (qCh d ℓ x) (atlasOp (pCh ℓ y))) zero := by
  unfold pCh qCh
  obtain ⟨hd3, _⟩ := succ_mod3 d hd
  obtain ⟨hℓ8, _⟩ := succ_mod8 ℓ hℓ
  refine Req_trans (pairF_tens_M _ _ _ _) ?_
  have hS : Req (RsumN (fun i => Rmul x (sgCh d ((d + 1) % 3) i)) 3) zero := RsumN_smul_sg x _ _ 3 hd hd3
  have hT : Req (RsumN (sgCh ℓ ((ℓ + 1) % 8)) 8) zero := RsumN_sg _ _ 8 hℓ hℓ8
  have hSS : Req (dotN (fun i => Rmul x (sgCh d ((d + 1) % 3) i)) (fun _ => y) 3) zero :=
    dotN_smul_sg_const x y _ _ 3 hd hd3
  refine Req_trans (Radd_congr (Rmul_congr (Rmul_congr hS (Req_refl _)) (Req_refl _))
    (Rsub_congr (Rmul_congr (Rmul_congr hSS (Req_refl _)) hT) (Rmul_congr hSS (Req_refl _)))) ?_
  refine Req_trans (Radd_congr
    (Req_trans (Rmul_congr (Rzero_mul_ch _) (Req_refl _)) (Rzero_mul_ch _))
    (Rsub_congr (Rmul_zero _) (Rzero_mul_ch _))) ?_
  exact Req_trans (Radd_congr (Req_refl _) (Radd_neg zero)) (Radd_zero zero)

-- ===========================================================================
-- (4) Linearity of the channels in the scalar (used by the atom readback).
-- ===========================================================================

theorem pCh_smul_pt (ℓ : Nat) (x : Real) (i j : Nat) :
    pCh ℓ x i j = Rmul x (Rmul c23 (indicCh ℓ j)) := rfl

theorem qCh_smul_pt (d ℓ : Nat) (x : Real) (i j : Nat) :
    qCh d ℓ x i j = Rmul (Rmul x (sgCh d ((d + 1) % 3) i)) (sgCh ℓ ((ℓ + 1) % 8) j) := rfl

/-- `p(x + x') = p(x) + p(x')` pointwise. -/
theorem pCh_add (ℓ : Nat) (x x' : Real) (i j : Nat) :
    Req (pCh ℓ (Radd x x') i j) (Radd (pCh ℓ x i j) (pCh ℓ x' i j)) :=
  Rmul_distrib_right _ _ _

/-- `q(x + x') = q(x) + q(x')` pointwise. -/
theorem qCh_add (d ℓ : Nat) (x x' : Real) (i j : Nat) :
    Req (qCh d ℓ (Radd x x') i j) (Radd (qCh d ℓ x i j) (qCh d ℓ x' i j)) := by
  show Req (Rmul (Rmul (Radd x x') (sgCh d ((d + 1) % 3) i)) (sgCh ℓ ((ℓ + 1) % 8) j))
           (Radd (Rmul (Rmul x (sgCh d ((d + 1) % 3) i)) (sgCh ℓ ((ℓ + 1) % 8) j))
                 (Rmul (Rmul x' (sgCh d ((d + 1) % 3) i)) (sgCh ℓ ((ℓ + 1) % 8) j)))
  refine Req_trans (Rmul_congr (Rmul_distrib_right _ _ _) (Req_refl _)) ?_
  exact Rmul_distrib_right _ _ _

/-- `p(x·y) = x·p(y)` pointwise. -/
theorem pCh_scale (ℓ : Nat) (x y : Real) (i j : Nat) :
    Req (pCh ℓ (Rmul x y) i j) (Rmul x (pCh ℓ y i j)) :=
  Rmul_assoc _ _ _

/-- `q(x·y) = x·q(y)` pointwise. -/
theorem qCh_scale (d ℓ : Nat) (x y : Real) (i j : Nat) :
    Req (qCh d ℓ (Rmul x y) i j) (Rmul x (qCh d ℓ y i j)) := by
  show Req (Rmul (Rmul (Rmul x y) (sgCh d ((d + 1) % 3) i)) (sgCh ℓ ((ℓ + 1) % 8) j))
           (Rmul x (Rmul (Rmul y (sgCh d ((d + 1) % 3) i)) (sgCh ℓ ((ℓ + 1) % 8) j)))
  refine Req_trans (Rmul_congr (Rmul_assoc _ _ _) (Req_refl _)) ?_
  exact Rmul_assoc _ _ _

end UOR.Bridge.F1Square.Square
