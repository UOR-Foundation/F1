/-
F1 square — **the canonical cut/cycle decomposition of the Atlas fiber and the bundled bilinear
readback** (`AtlasBundle.lean`).  For a raw fiber vector `v` (`i < 3`, `j < 8`):

    `a_v(i) = row_i(v)/8 − total(v)/24`,   `b_v(j) = col_j(v)/3`,
    `P_cut v = a_v ⊕ b_v`,   `R_cyc v = v − P_cut v`,

with `Σ_i a_v(i) = 0` automatically, `R_cyc v ∈ ker B` (zero row and column sums), the cut and cycle
parts orthogonal, and THE UNIVERSAL ALL-PAIRS READBACK

    `⟨v, M w⟩ = 56·Σ_i a_v(i)a_w(i) + 6·Σ_j b_v(j)b_w(j) + 3·(Σ_j b_v(j))(Σ_j b_w(j)) − ⟨R_cyc v, R_cyc w⟩`

(`atlas_bilinear_readback`) — the cut part is a positively weighted Gram form, the cycle part enters
with the sign `−1` of the `−I` term.  Pure finite Atlas algebra; no test, form or sign is involved.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasIncidence

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- (1) The pairing and its bilinearity.
-- ===========================================================================

/-- `⟨v, w⟩ = Σ_ij v_ij w_ij`. -/
def pairF (v w : Nat → Nat → Real) : Real := RsumN (fun i => RsumN (fun j => Rmul (v i j) (w i j)) 8) 3

theorem pairF_congr {v v' w w' : Nat → Nat → Real} (hv : ∀ i j, i < 3 → j < 8 → Req (v i j) (v' i j))
    (hw : ∀ i j, i < 3 → j < 8 → Req (w i j) (w' i j)) : Req (pairF v w) (pairF v' w') :=
  RsumN_congr 3 (fun i hi => RsumN_congr 8 (fun j hj => Rmul_congr (hv i j hi hj) (hw i j hi hj)))

theorem pairF_comm (v w : Nat → Nat → Real) : Req (pairF v w) (pairF w v) :=
  RsumN_congr 3 (fun i _ => RsumN_congr 8 (fun j _ => Rmul_comm _ _))

theorem pairF_add_right (v w w' : Nat → Nat → Real) :
    Req (pairF v (fun i j => Radd (w i j) (w' i j))) (Radd (pairF v w) (pairF v w')) := by
  unfold pairF
  refine Req_trans (RsumN_congr (G := fun i => Radd (RsumN (fun j => Rmul (v i j) (w i j)) 8)
    (RsumN (fun j => Rmul (v i j) (w' i j)) 8)) 3 (fun i _ => ?_)) (RsumN_Radd _ _ 3)
  refine Req_trans (RsumN_congr (G := fun j => Radd (Rmul (v i j) (w i j)) (Rmul (v i j) (w' i j))) 8
    (fun j _ => Rmul_distrib _ _ _)) (RsumN_Radd _ _ 8)

theorem pairF_neg_right (v w : Nat → Nat → Real) :
    Req (pairF v (fun i j => Rneg (w i j))) (Rneg (pairF v w)) := by
  unfold pairF
  refine Req_trans (RsumN_congr (G := fun i => Rneg (RsumN (fun j => Rmul (v i j) (w i j)) 8)) 3
    (fun i _ => ?_)) (RsumN_Rneg _ 3)
  refine Req_trans (RsumN_congr (G := fun j => Rneg (Rmul (v i j) (w i j))) 8
    (fun j _ => Rmul_neg_right _ _)) (RsumN_Rneg _ 8)

-- ===========================================================================
-- (2) The canonical decomposition.
-- ===========================================================================

def totalF (v : Nat → Nat → Real) : Real := RsumN (fun i => rowSum v i) 3
def aOf (v : Nat → Nat → Real) (i : Nat) : Real :=
  Rsub (Rmul (ofQ (⟨1, 8⟩ : Q) (by decide)) (rowSum v i)) (Rmul (ofQ (⟨1, 24⟩ : Q) (by decide)) (totalF v))
def bOf (v : Nat → Nat → Real) (j : Nat) : Real := Rmul (ofQ (⟨1, 3⟩ : Q) (by decide)) (colSum v j)
def Pcut (v : Nat → Nat → Real) : Nat → Nat → Real := cutVec (aOf v) (bOf v)
def Rcyc (v : Nat → Nat → Real) (i j : Nat) : Real := Rsub (v i j) (Pcut v i j)

/-- `total = Σ_j col_j` (double-sum swap). -/
theorem totalF_cols (v : Nat → Nat → Real) : Req (totalF v) (RsumN (fun j => colSum v j) 8) :=
  RsumN_swap_ai v 8 3

/-- `Σ_i a_v(i) = 0`. -/
theorem aOf_sum_zero (v : Nat → Nat → Real) : Req (RsumN (aOf v) 3) zero := by
  unfold aOf
  refine Req_trans (RsumN_Rsub _ _ 3) ?_
  refine Req_trans (Rsub_congr (RsumN_smul_ai _ _ 3) (RsumN_const _ 3)) ?_
  -- (1/8)·T − 3·((1/24)·T) = 0
  refine Req_trans (Rsub_congr (Req_refl _) (Req_trans (Req_symm (Rmul_assoc _ _ _))
    (Rmul_congr (Req_trans (Rmul_ofQ_ofQ Nat.one_pos (by decide)) (ofQ_congr _ (by decide)
      (by decide : Qeq (mul (⟨3, 1⟩ : Q) (⟨1, 24⟩ : Q)) (⟨1, 8⟩ : Q)))) (Req_refl _)))) ?_
  exact Radd_neg _

/-- `Σ_j b_v(j) = total/3`. -/
theorem bOf_sum (v : Nat → Nat → Real) :
    Req (RsumN (bOf v) 8) (Rmul (ofQ (⟨1, 3⟩ : Q) (by decide)) (totalF v)) := by
  unfold bOf
  exact Req_trans (RsumN_smul_ai _ _ 8) (Rmul_congr (Req_refl _) (Req_symm (totalF_cols v)))

/-- `v = P_cut v + R_cyc v` pointwise. -/
theorem decomp_pt (v : Nat → Nat → Real) (i j : Nat) : Req (v i j) (Radd (Pcut v i j) (Rcyc v i j)) := by
  show Req (v i j) (Radd (Pcut v i j) (Radd (v i j) (Rneg (Pcut v i j))))
  refine Req_symm ?_
  refine Req_trans (Req_symm (Radd_assoc _ _ _)) ?_
  refine Req_trans (Radd_congr (Radd_comm _ _) (Req_refl _)) ?_
  refine Req_trans (Radd_assoc _ _ _) ?_
  exact Req_trans (Radd_congr (Req_refl _) (Radd_neg _)) (Radd_zero _)

/-- `8·a_v(i) = row_i − T/3`. -/
theorem eight_aOf (v : Nat → Nat → Real) (i : Nat) :
    Req (Rmul (RofNat 8) (aOf v i)) (Rsub (rowSum v i) (Rmul (ofQ (⟨1, 3⟩ : Q) (by decide)) (totalF v))) := by
  unfold aOf
  rw [RofNat_eq]
  refine Req_trans (Rmul_sub_distrib _ _ _) (Rsub_congr ?_ ?_)
  · refine Req_trans (Req_symm (Rmul_assoc _ _ _)) ?_
    refine Req_trans (Rmul_congr (Req_trans (Rmul_ofQ_ofQ Nat.one_pos (by decide))
      (ofQ_congr _ (by decide) (by decide : Qeq (mul (⟨8, 1⟩ : Q) (⟨1, 8⟩ : Q)) (⟨1, 1⟩ : Q)))) (Req_refl _)) ?_
    exact Rone_mul _
  · refine Req_trans (Req_symm (Rmul_assoc _ _ _)) ?_
    exact Rmul_congr (Req_trans (Rmul_ofQ_ofQ Nat.one_pos (by decide))
      (ofQ_congr _ (by decide) (by decide : Qeq (mul (⟨8, 1⟩ : Q) (⟨1, 24⟩ : Q)) (⟨1, 3⟩ : Q)))) (Req_refl _)

/-- `3·b_v(j) = col_j`. -/
theorem three_bOf (v : Nat → Nat → Real) (j : Nat) : Req (Rmul (RofNat 3) (bOf v j)) (colSum v j) := by
  unfold bOf
  rw [RofNat_eq]
  refine Req_trans (Req_symm (Rmul_assoc _ _ _)) ?_
  refine Req_trans (Rmul_congr (Req_trans (Rmul_ofQ_ofQ Nat.one_pos (by decide))
    (ofQ_congr _ (by decide) (by decide : Qeq (mul (⟨3, 1⟩ : Q) (⟨1, 3⟩ : Q)) (⟨1, 1⟩ : Q)))) (Req_refl _)) ?_
  exact Rone_mul _

/-- `R_cyc v` has zero row sums. -/
theorem Rcyc_row_zero (v : Nat → Nat → Real) (i : Nat) : Req (rowSum (Rcyc v) i) zero := by
  unfold Rcyc rowSum
  refine Req_trans (RsumN_Rsub _ _ 8) ?_
  refine Req_trans (Rsub_congr (Req_refl _) (rowSum_cut (aOf v) (bOf v) i)) ?_
  refine Req_trans (Rsub_congr (Req_refl _) (Radd_congr (eight_aOf v i) (bOf_sum v))) ?_
  -- r − ((r − t) + t) = 0
  refine Req_trans (Rsub_congr (Req_refl _) (Req_trans (Radd_assoc _ _ _)
    (Req_trans (Radd_congr (Req_refl _) (Req_trans (Radd_comm _ _) (Radd_neg _))) (Radd_zero _)))) ?_
  exact Radd_neg _

/-- `R_cyc v` has zero column sums. -/
theorem Rcyc_col_zero (v : Nat → Nat → Real) (j : Nat) : Req (colSum (Rcyc v) j) zero := by
  unfold Rcyc colSum
  refine Req_trans (RsumN_Rsub _ _ 3) ?_
  refine Req_trans (Rsub_congr (Req_refl _) (colSum_cut (aOf v) (bOf v) j)) ?_
  refine Req_trans (Rsub_congr (Req_refl _) (Radd_congr (aOf_sum_zero v) (three_bOf v j))) ?_
  refine Req_trans (Rsub_congr (Req_refl _) (Req_trans (Radd_comm _ _) (Radd_zero _))) ?_
  exact Radd_neg _

theorem Rcyc_isCycle (v : Nat → Nat → Real) : IsCycle (Rcyc v) :=
  ⟨fun i _ => Rcyc_row_zero v i, fun j _ => Rcyc_col_zero v j⟩

-- ===========================================================================
-- (3) Orthogonality of cut and cycle, linearity of `M`.
-- ===========================================================================

/-- `⟨a⊕b, R⟩ = 0` for `R ∈ ker B`. -/
theorem pairF_cut_cycle (a b : Nat → Real) (R : Nat → Nat → Real) (hR : IsCycle R) :
    Req (pairF (cutVec a b) R) zero := by
  unfold pairF
  -- inner: Σ_j (a_i + b_j)·R_ij = a_i·row_i(R) + Σ_j b_j·R_ij
  have hin : ∀ i, Req (RsumN (fun j => Rmul (cutVec a b i j) (R i j)) 8)
      (Radd (Rmul (a i) (rowSum R i)) (RsumN (fun j => Rmul (b j) (R i j)) 8)) := by
    intro i
    refine Req_trans (RsumN_congr (G := fun j => Radd (Rmul (a i) (R i j)) (Rmul (b j) (R i j))) 8
      (fun j _ => Rmul_distrib_right _ _ _)) ?_
    refine Req_trans (RsumN_Radd _ _ 8) (Radd_congr (RsumN_smul_ai (a i) (fun j => R i j) 8) (Req_refl _))
  refine Req_trans (RsumN_congr (G := fun i => Radd (Rmul (a i) (rowSum R i)) (RsumN (fun j => Rmul (b j) (R i j)) 8)) 3
    (fun i _ => hin i)) ?_
  refine Req_trans (RsumN_Radd _ _ 3) ?_
  -- first: Σ_i a_i·0 = 0
  have h1 : Req (RsumN (fun i => Rmul (a i) (rowSum R i)) 3) zero := by
    refine Req_trans (RsumN_congr (G := fun _ => zero) 3 (fun i hi =>
      Req_trans (Rmul_congr (Req_refl _) (hR.1 i hi)) (Rmul_zero _))) ?_
    exact Req_trans (RsumN_const zero 3) (Rmul_zero _)
  -- second: Σ_i Σ_j b_j R_ij = Σ_j b_j col_j(R) = 0
  have h2 : Req (RsumN (fun i => RsumN (fun j => Rmul (b j) (R i j)) 8) 3) zero := by
    refine Req_trans (RsumN_swap_ai (fun i j => Rmul (b j) (R i j)) 8 3) ?_
    refine Req_trans (RsumN_congr (G := fun _ => zero) 8 (fun j hj => ?_)) ?_
    · refine Req_trans (RsumN_smul_ai (b j) (fun i => R i j) 3) ?_
      exact Req_trans (Rmul_congr (Req_refl _) (hR.2 j hj)) (Rmul_zero _)
    · exact Req_trans (RsumN_const zero 8) (Rmul_zero _)
  exact Req_trans (Radd_congr h1 h2) (Radd_zero _)

theorem rowSum_add (v w : Nat → Nat → Real) (i : Nat) :
    Req (rowSum (fun i j => Radd (v i j) (w i j)) i) (Radd (rowSum v i) (rowSum w i)) := RsumN_Radd _ _ 8
theorem colSum_add (v w : Nat → Nat → Real) (j : Nat) :
    Req (colSum (fun i j => Radd (v i j) (w i j)) j) (Radd (colSum v j) (colSum w j)) := RsumN_Radd _ _ 3

/-- `M` is additive. -/
theorem atlasOp_add (v w : Nat → Nat → Real) (i j : Nat) :
    Req (atlasOp (fun i j => Radd (v i j) (w i j)) i j) (Radd (atlasOp v i j) (atlasOp w i j)) := by
  unfold atlasOp
  refine Req_trans (Rsub_congr (Radd_congr (colSum_add v w j) (rowSum_add v w i)) (Req_refl _)) ?_
  -- ((c + c') + (r + r')) − (v + w) = ((c + r) − v) + ((c' + r') − w)
  refine Req_trans (Radd_congr (Radd_regroup _ _ _ _) (Rneg_Radd _ _)) ?_
  exact Radd_regroup _ _ _ _

theorem rowSum_congr {v w : Nat → Nat → Real} (h : ∀ i j, i < 3 → j < 8 → Req (v i j) (w i j)) (i : Nat) (hi : i < 3) :
    Req (rowSum v i) (rowSum w i) := RsumN_congr 8 (fun j hj => h i j hi hj)
theorem colSum_congr {v w : Nat → Nat → Real} (h : ∀ i j, i < 3 → j < 8 → Req (v i j) (w i j)) (j : Nat) (hj : j < 8) :
    Req (colSum v j) (colSum w j) := RsumN_congr 3 (fun i hi => h i j hi hj)

theorem atlasOp_congr {v w : Nat → Nat → Real} (h : ∀ i j, i < 3 → j < 8 → Req (v i j) (w i j))
    (i j : Nat) (hi : i < 3) (hj : j < 8) : Req (atlasOp v i j) (atlasOp w i j) :=
  Rsub_congr (Radd_congr (colSum_congr h j hj) (rowSum_congr h i hi)) (h i j hi hj)

-- ===========================================================================
-- (4) The bilinear cut formula.
-- ===========================================================================

/-- `x·(7x' + 2y') = 7xx' + 2xy'`, `y·(7x' + 2y') = 7yx' + 2yy'`. -/
theorem x_mul_lin2 (x x' y' : Real) :
    Req (Rmul x (Radd (Rmul c7 x') (Rmul c2 y'))) (Radd (Rmul c7 (Rmul x x')) (Rmul c2 (Rmul x y'))) := by
  refine Req_trans (Rmul_distrib _ _ _) (Radd_congr ?_ ?_)
  · exact Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Rmul_congr (Rmul_comm _ _) (Req_refl _)) (Rmul_assoc _ _ _))
  · exact Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Rmul_congr (Rmul_comm _ _) (Req_refl _)) (Rmul_assoc _ _ _))

/-- **The bilinear term expansion**
    `(x+y)·((7x'+2y')+S') = ((7xx' + (2xy' + 7yx')) + (2yy' + xS')) + yS'`. -/
theorem cut_term_expand2 (x y x' y' S' : Real) :
    Req (Rmul (Radd x y) (Radd (Radd (Rmul c7 x') (Rmul c2 y')) S'))
        (Radd (Radd (Radd (Rmul c7 (Rmul x x')) (Radd (Rmul c2 (Rmul x y')) (Rmul c7 (Rmul y x'))))
          (Radd (Rmul c2 (Rmul y y')) (Rmul x S'))) (Rmul y S')) := by
  have h1 : Req (Rmul (Radd x y) (Radd (Radd (Rmul c7 x') (Rmul c2 y')) S'))
      (Radd (Radd (Rmul x (Radd (Rmul c7 x') (Rmul c2 y'))) (Rmul y (Radd (Rmul c7 x') (Rmul c2 y'))))
            (Radd (Rmul x S') (Rmul y S'))) :=
    Req_trans (Rmul_distrib _ _ _) (Radd_congr (Rmul_distrib_right _ _ _) (Rmul_distrib_right _ _ _))
  have h2 : Req (Radd (Rmul x (Radd (Rmul c7 x') (Rmul c2 y'))) (Rmul y (Radd (Rmul c7 x') (Rmul c2 y'))))
      (Radd (Radd (Rmul c7 (Rmul x x')) (Rmul c2 (Rmul x y'))) (Radd (Rmul c7 (Rmul y x')) (Rmul c2 (Rmul y y')))) :=
    Radd_congr (x_mul_lin2 x x' y') (x_mul_lin2 y x' y')
  -- ((A + B) + (C + D)) = ((A + (B + C)) + D)
  have h3 : Req (Radd (Radd (Rmul c7 (Rmul x x')) (Rmul c2 (Rmul x y'))) (Radd (Rmul c7 (Rmul y x')) (Rmul c2 (Rmul y y'))))
      (Radd (Radd (Rmul c7 (Rmul x x')) (Radd (Rmul c2 (Rmul x y')) (Rmul c7 (Rmul y x')))) (Rmul c2 (Rmul y y'))) := by
    refine Req_trans (Radd_assoc _ _ _) ?_
    refine Req_trans (Radd_congr (Req_refl _) (Req_symm (Radd_assoc _ _ _))) ?_
    exact Req_symm (Radd_assoc _ _ _)
  have h4 : Req (Radd (Radd (Radd (Rmul c7 (Rmul x x')) (Radd (Rmul c2 (Rmul x y')) (Rmul c7 (Rmul y x'))))
        (Rmul c2 (Rmul y y'))) (Radd (Rmul x S') (Rmul y S')))
      (Radd (Radd (Radd (Rmul c7 (Rmul x x')) (Radd (Rmul c2 (Rmul x y')) (Rmul c7 (Rmul y x'))))
        (Radd (Rmul c2 (Rmul y y')) (Rmul x S'))) (Rmul y S')) := by
    refine Req_trans (Req_symm (Radd_assoc _ _ _)) ?_
    exact Radd_congr (Radd_assoc _ _ _) (Req_refl _)
  exact Req_trans h1 (Req_trans (Radd_congr (Req_trans h2 h3) (Req_refl _)) h4)

/-- Inner sum over `j < 8` (`S = Σb`, `S' = Σb'`). -/
theorem cut_inner_sum2 (x x' : Real) (b b' : Nat → Real) :
    Req (RsumN (fun j => Radd (Radd (Radd (Rmul c7 (Rmul x x')) (Radd (Rmul c2 (Rmul x (b' j))) (Rmul c7 (Rmul (b j) x'))))
          (Radd (Rmul c2 (Rmul (b j) (b' j))) (Rmul x (RsumN b' 8)))) (Rmul (b j) (RsumN b' 8))) 8)
        (Radd (Radd (Radd (Rmul (RofNat 8) (Rmul c7 (Rmul x x')))
            (Radd (Rmul c2 (Rmul x (RsumN b' 8))) (Rmul c7 (Rmul (RsumN b 8) x'))))
          (Radd (Rmul c2 (RsumN (fun j => Rmul (b j) (b' j)) 8)) (Rmul (RofNat 8) (Rmul x (RsumN b' 8)))))
          (Rmul (RsumN b 8) (RsumN b' 8))) := by
  refine Req_trans (RsumN_Radd
    (fun j => Radd (Radd (Rmul c7 (Rmul x x')) (Radd (Rmul c2 (Rmul x (b' j))) (Rmul c7 (Rmul (b j) x'))))
      (Radd (Rmul c2 (Rmul (b j) (b' j))) (Rmul x (RsumN b' 8))))
    (fun j => Rmul (b j) (RsumN b' 8)) 8) (Radd_congr ?_ (RsumN_smul_right_ai (RsumN b' 8) b 8))
  refine Req_trans (RsumN_Radd (fun j => Radd (Rmul c7 (Rmul x x')) (Radd (Rmul c2 (Rmul x (b' j))) (Rmul c7 (Rmul (b j) x'))))
    (fun j => Radd (Rmul c2 (Rmul (b j) (b' j))) (Rmul x (RsumN b' 8))) 8) (Radd_congr ?_ ?_)
  · refine Req_trans (RsumN_Radd (fun _ => Rmul c7 (Rmul x x'))
      (fun j => Radd (Rmul c2 (Rmul x (b' j))) (Rmul c7 (Rmul (b j) x'))) 8) (Radd_congr (RsumN_const _ 8) ?_)
    refine Req_trans (RsumN_Radd (fun j => Rmul c2 (Rmul x (b' j))) (fun j => Rmul c7 (Rmul (b j) x')) 8) (Radd_congr ?_ ?_)
    · exact Req_trans (RsumN_smul_ai c2 (fun j => Rmul x (b' j)) 8) (Rmul_congr (Req_refl _) (RsumN_smul_ai x b' 8))
    · exact Req_trans (RsumN_smul_ai c7 (fun j => Rmul (b j) x') 8) (Rmul_congr (Req_refl _) (RsumN_smul_right_ai x' b 8))
  · exact Req_trans (RsumN_Radd (fun j => Rmul c2 (Rmul (b j) (b' j))) (fun _ => Rmul x (RsumN b' 8)) 8)
      (Radd_congr (RsumN_smul_ai c2 (fun j => Rmul (b j) (b' j)) 8) (RsumN_const _ 8))

/-- Outer sum over `i < 3` with `Σa = Σa' = 0`. -/
theorem cut_outer_sum2 (a a' : Nat → Real) (S S' T : Real) (hS : Req (RsumN a 3) zero) (hS' : Req (RsumN a' 3) zero) :
    Req (RsumN (fun i => Radd (Radd (Radd (Rmul (RofNat 8) (Rmul c7 (Rmul (a i) (a' i))))
            (Radd (Rmul c2 (Rmul (a i) S')) (Rmul c7 (Rmul S (a' i)))))
          (Radd (Rmul c2 T) (Rmul (RofNat 8) (Rmul (a i) S')))) (Rmul S S')) 3)
        (Radd (Rmul c56 (RsumN (fun i => Rmul (a i) (a' i)) 3)) (Radd (Rmul c6 T) (Rmul c3 (Rmul S S')))) := by
  refine Req_trans (RsumN_Radd _ _ 3) ?_
  refine Req_trans (Radd_congr (RsumN_Radd _ _ 3) (RsumN_const _ 3)) ?_
  refine Req_trans (Radd_congr (Radd_congr (RsumN_Radd _ _ 3) (RsumN_Radd _ _ 3)) (Req_refl _)) ?_
  refine Req_trans (Radd_congr (Radd_congr (Radd_congr (Req_refl _) (RsumN_Radd _ _ 3)) (Req_refl _)) (Req_refl _)) ?_
  have h1 : Req (RsumN (fun i => Rmul (RofNat 8) (Rmul c7 (Rmul (a i) (a' i)))) 3)
      (Rmul c56 (RsumN (fun i => Rmul (a i) (a' i)) 3)) := by
    refine Req_trans (RsumN_smul_ai _ _ 3) ?_
    refine Req_trans (Rmul_congr (Req_refl _) (RsumN_smul_ai c7 _ 3)) ?_
    refine Req_trans (Req_symm (Rmul_assoc _ _ _)) (Rmul_congr ?_ (Req_refl _))
    exact Req_trans (Rmul_ofQ_ofQ Nat.one_pos Nat.one_pos) (ofQ_congr _ Nat.one_pos (by decide))
  have hzL : ∀ c : Real, Req (RsumN (fun i => Rmul c (Rmul (a i) S')) 3) zero := by
    intro c
    refine Req_trans (RsumN_smul_ai c _ 3) ?_
    refine Req_trans (Rmul_congr (Req_refl _) (RsumN_smul_right_ai S' a 3)) ?_
    refine Req_trans (Rmul_congr (Req_refl _) (Rmul_congr hS (Req_refl _))) ?_
    exact Req_trans (Rmul_congr (Req_refl _) (Req_trans (Rmul_comm _ _) (Rmul_zero _))) (Rmul_zero _)
  have hzR : Req (RsumN (fun i => Rmul c7 (Rmul S (a' i))) 3) zero := by
    refine Req_trans (RsumN_smul_ai c7 _ 3) ?_
    refine Req_trans (Rmul_congr (Req_refl _) (RsumN_smul_ai S a' 3)) ?_
    refine Req_trans (Rmul_congr (Req_refl _) (Rmul_congr (Req_refl _) hS')) ?_
    exact Req_trans (Rmul_congr (Req_refl _) (Rmul_zero _)) (Rmul_zero _)
  have h3 : Req (RsumN (fun _ => Rmul c2 T) 3) (Rmul c6 T) := by
    refine Req_trans (RsumN_const _ 3) ?_
    refine Req_trans (Req_symm (Rmul_assoc _ _ _)) (Rmul_congr ?_ (Req_refl _))
    exact Req_trans (Rmul_ofQ_ofQ Nat.one_pos Nat.one_pos) (ofQ_congr _ Nat.one_pos (by decide))
  refine Req_trans (Radd_congr (Radd_congr (Radd_congr h1 (Radd_congr (hzL c2) hzR))
    (Radd_congr h3 (hzL (RofNat 8)))) (Req_refl _)) ?_
  refine Req_trans (Radd_congr (Radd_congr (Req_trans (Radd_congr (Req_refl _) (Radd_zero _)) (Radd_zero _))
    (Radd_zero _)) (Req_refl _)) ?_
  exact Radd_assoc _ _ _

set_option maxHeartbeats 1000000 in
/-- **The bilinear cut formula**: with `Σa = Σa' = 0`,
    `⟨a⊕b, M(a'⊕b')⟩ = 56·Σ_i a_i a'_i + 6·Σ_j b_j b'_j + 3·(Σb)(Σb')`. -/
theorem pairF_cut_Mcut (a b a' b' : Nat → Real) (hS : Req (RsumN a 3) zero) (hS' : Req (RsumN a' 3) zero) :
    Req (pairF (cutVec a b) (atlasOp (cutVec a' b')))
        (Radd (Rmul c56 (RsumN (fun i => Rmul (a i) (a' i)) 3))
              (Radd (Rmul c6 (RsumN (fun j => Rmul (b j) (b' j)) 8)) (Rmul c3 (Rmul (RsumN b 8) (RsumN b' 8))))) := by
  unfold pairF
  refine Req_trans (RsumN_congr
    (G := fun i => RsumN (fun j => Radd (Radd (Radd (Rmul c7 (Rmul (a i) (a' i)))
      (Radd (Rmul c2 (Rmul (a i) (b' j))) (Rmul c7 (Rmul (b j) (a' i)))))
      (Radd (Rmul c2 (Rmul (b j) (b' j))) (Rmul (a i) (RsumN b' 8)))) (Rmul (b j) (RsumN b' 8))) 8) 3
    (fun i _ => RsumN_congr
      (G := fun j => Radd (Radd (Radd (Rmul c7 (Rmul (a i) (a' i)))
        (Radd (Rmul c2 (Rmul (a i) (b' j))) (Rmul c7 (Rmul (b j) (a' i)))))
        (Radd (Rmul c2 (Rmul (b j) (b' j))) (Rmul (a i) (RsumN b' 8)))) (Rmul (b j) (RsumN b' 8))) 8
      (fun j _ => Req_trans (Rmul_congr (Req_refl _) (atlasOp_cut a' b' hS' i j))
        (cut_term_expand2 (a i) (b j) (a' i) (b' j) (RsumN b' 8))))) ?_
  refine Req_trans (RsumN_congr 3 (fun i _ => cut_inner_sum2 (a i) (a' i) b b')) ?_
  exact cut_outer_sum2 a a' (RsumN b 8) (RsumN b' 8) (RsumN (fun j => Rmul (b j) (b' j)) 8) hS hS'

-- ===========================================================================
-- (5) THE BUNDLED ALL-PAIRS READBACK.
-- ===========================================================================

/-- `M(a'⊕b')` is itself a cut vector `(7a') ⊕ (2b' + Σb')`. -/
theorem atlasOp_cut_is_cut (a' b' : Nat → Real) (hS' : Req (RsumN a' 3) zero) (i j : Nat) :
    Req (atlasOp (cutVec a' b') i j)
        (cutVec (fun i => Rmul c7 (a' i)) (fun j => Radd (Rmul c2 (b' j)) (RsumN b' 8)) i j) :=
  Req_trans (atlasOp_cut a' b' hS' i j) (Radd_assoc _ _ _)

set_option maxHeartbeats 1000000 in
/-- **★ THE BUNDLED READBACK**: for all raw fiber vectors `v, w`,
    `⟨v, Mw⟩ = 56·Σ a_v a_w + 6·Σ b_v b_w + 3·(Σb_v)(Σb_w) − ⟨R_cyc v, R_cyc w⟩`. -/
theorem atlas_bilinear_readback (v w : Nat → Nat → Real) :
    Req (pairF v (atlasOp w))
        (Rsub (Radd (Rmul c56 (RsumN (fun i => Rmul (aOf v i) (aOf w i)) 3))
                (Radd (Rmul c6 (RsumN (fun j => Rmul (bOf v j) (bOf w j)) 8))
                      (Rmul c3 (Rmul (RsumN (bOf v) 8) (RsumN (bOf w) 8)))))
              (pairF (Rcyc v) (Rcyc w))) := by
  -- decompose both arguments
  have hdec : ∀ (u : Nat → Nat → Real) i j, i < 3 → j < 8 → Req (u i j) (Radd (Pcut u i j) (Rcyc u i j)) :=
    fun u i j _ _ => decomp_pt u i j
  refine Req_trans (pairF_congr (hdec v) (fun i j hi hj => Req_trans (atlasOp_congr (hdec w) i j hi hj)
    (atlasOp_add (Pcut w) (Rcyc w) i j))) ?_
  -- expand the pairing
  refine Req_trans (pairF_add_right _ _ _) ?_
  refine Req_trans (Radd_congr (Req_trans (pairF_comm _ _) (Req_trans (pairF_add_right _ _ _)
    (Radd_congr (pairF_comm _ _) (pairF_comm _ _))))
    (Req_trans (pairF_comm _ _) (Req_trans (pairF_add_right _ _ _)
    (Radd_congr (pairF_comm _ _) (pairF_comm _ _))))) ?_
  -- ⟨Rv, M Pw⟩ = 0, ⟨Pv, M Rw⟩ = 0, ⟨Rv, M Rw⟩ = −⟨Rv, Rw⟩
  have hRP : Req (pairF (Rcyc v) (atlasOp (Pcut w))) zero := by
    refine Req_trans (pairF_congr (fun _ _ _ _ => Req_refl _)
      (fun i j hi hj => atlasOp_cut_is_cut (aOf w) (bOf w) (aOf_sum_zero w) i j)) ?_
    exact Req_trans (pairF_comm _ _) (pairF_cut_cycle _ _ _ (Rcyc_isCycle v))
  have hMR : ∀ i j, i < 3 → j < 8 → Req (atlasOp (Rcyc w) i j) (Rneg (Rcyc w i j)) :=
    fun i j hi hj => atlasOp_cycle _ (Rcyc_isCycle w) i j hi hj
  have hPR : Req (pairF (Pcut v) (atlasOp (Rcyc w))) zero := by
    refine Req_trans (pairF_congr (fun _ _ _ _ => Req_refl _) hMR) ?_
    refine Req_trans (pairF_neg_right _ _) ?_
    exact Req_trans (Rneg_congr (pairF_cut_cycle _ _ _ (Rcyc_isCycle w))) (Req_of_seq_Qeq (fun _ => Qeq_refl _))
  have hRR : Req (pairF (Rcyc v) (atlasOp (Rcyc w))) (Rneg (pairF (Rcyc v) (Rcyc w))) :=
    Req_trans (pairF_congr (fun _ _ _ _ => Req_refl _) hMR) (pairF_neg_right _ _)
  have hPP := pairF_cut_Mcut (aOf v) (bOf v) (aOf w) (bOf w) (aOf_sum_zero v) (aOf_sum_zero w)
  refine Req_trans (Radd_congr (Radd_congr hPP hRP) (Radd_congr hPR hRR)) ?_
  refine Req_trans (Radd_congr (Radd_zero _) (Req_trans (Radd_comm _ _) (Radd_zero _))) ?_
  exact Req_refl _

end UOR.Bridge.F1Square.Square
