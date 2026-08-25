/-
F1 square — **the physical Atlas operator on the `3×8` fiber IS `BᵀB − I` for the `K_{3,8}` incidence**
(`AtlasIncidence.lean`).  The fiber is `T·O = 3·8`; vectors are `v : Nat → Nat → Real` read on
`i < 3`, `j < 8`.  Sourced (Atlas §5/§6.6): `M = (O+2)·I − T·Π_T − O·Π_O` with `Π_T`, `Π_O` the
projections onto the parts non-constant in the `T`-index / the `O`-index.  PROVED here, as linear
maps (not merely by matching spectra):
  • `atlasOp_sourced`   — `(O+2)v − T·Π_T v − O·Π_O v = −v + (J₃⊗I₈)v + (I₃⊗J₈)v`;
  • `atlasOp_eq_BtB`    — `Mv = Bᵀ(Bv) − v` for the genuine 0/1 vertex–edge incidence `B` of `K_{3,8}`
    (vertices `L i`, `R j`; edge `(i,j)` joins `L i` and `R j`);
  • the CYCLE space `ker B` (zero row and column sums) is the `−1` eigenspace (`atlasOp_cycle`);
  • the CUT space `{a_i + b_j}` (the range of `Bᵀ`) carries `M(a⊕b) = 7a_i + 2b_j + Σa + Σb`
    (`atlasOp_cut`);
  • **the square-root-free compression** — with `Σ_i a_i = 0`,
        `Q_M(a⊕b) = Σ_ij (a_i+b_j)·(M(a⊕b))_ij = 56·Σ_i a_i² + 6·Σ_j b_j² + 3·(Σ_j b_j)²`
    (`Qform_cut`), hence `Q_M ≥ 0` on that cut slice (`Qform_cut_nonneg`).
So the `(10¹, 7², 2⁷, (−1)¹⁴)` spectrum is the cut/cycle decomposition: the `14`-dimensional cycle
space is the negative direction, the cut slice is where the form is a sum of squares.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasSpectralCore
import F1Square.Analysis.RiemannSum
import F1Square.Analysis.GammaTwoBracket

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- (0) Sum toolkit.
-- ===========================================================================

theorem RsumN_smul_ai (c : Real) (F : Nat → Real) :
    ∀ N, Req (RsumN (fun i => Rmul c (F i)) N) (Rmul c (RsumN F N))
  | 0 => Req_symm (Rmul_zero c)
  | (N + 1) => by
      show Req (Radd (RsumN (fun i => Rmul c (F i)) N) (Rmul c (F N))) (Rmul c (Radd (RsumN F N) (F N)))
      exact Req_trans (Radd_congr (RsumN_smul_ai c F N) (Req_refl _)) (Req_symm (Rmul_distrib c _ _))

theorem RsumN_smul_right_ai (c : Real) (F : Nat → Real) :
    ∀ N, Req (RsumN (fun i => Rmul (F i) c) N) (Rmul (RsumN F N) c)
  | 0 => Req_symm (Req_trans (Rmul_comm _ _) (Rmul_zero c))
  | (N + 1) => by
      show Req (Radd (RsumN (fun i => Rmul (F i) c) N) (Rmul (F N) c)) (Rmul (Radd (RsumN F N) (F N)) c)
      exact Req_trans (Radd_congr (RsumN_smul_right_ai c F N) (Req_refl _)) (Req_symm (Rmul_distrib_right _ _ _))

/-- `Σ_{i<N} [i = k]·w i = w k` for `k < N`. -/
theorem RsumN_indicator_ai (w : Nat → Real) (k : Nat) :
    ∀ N, k < N → Req (RsumN (fun i => if i = k then w i else zero) N) (w k)
  | 0, h => absurd h (Nat.not_lt_zero k)
  | (N + 1), h => by
      show Req (Radd (RsumN (fun i => if i = k then w i else zero) N) (if N = k then w N else zero)) (w k)
      rcases Nat.lt_or_ge k N with hk | hk
      · have hne : ¬ (N = k) := by omega
        rw [if_neg hne]
        exact Req_trans (Radd_zero _) (RsumN_indicator_ai w k N hk)
      · have heq : N = k := by omega
        subst heq
        rw [if_pos rfl]
        have hzero : Req (RsumN (fun i => if i = N then w i else zero) N) zero := by
          refine Req_trans (RsumN_congr N (fun i hi => ?_)) (Req_trans (RsumN_const zero N) (Rmul_zero _))
          show Req (if i = N then w i else zero) zero
          rw [if_neg (by omega)]; exact Req_refl _
        exact Req_trans (Radd_congr hzero (Req_refl _)) (Req_trans (Radd_comm _ _) (Radd_zero _))

/-- Block splitting `Σ_{e<n+m} G e = Σ_{e<n} G e + Σ_{j<m} G (n+j)`. -/
theorem RsumN_add_block_ai (G : Nat → Real) (n : Nat) :
    ∀ m, Req (RsumN G (n + m)) (Radd (RsumN G n) (RsumN (fun j => G (n + j)) m))
  | 0 => Req_symm (Radd_zero _)
  | (m + 1) => by
      show Req (Radd (RsumN G (n + m)) (G (n + m))) (Radd (RsumN G n) (Radd (RsumN (fun j => G (n + j)) m) (G (n + m))))
      exact Req_trans (Radd_congr (RsumN_add_block_ai G n m) (Req_refl _)) (Radd_assoc _ _ _)

/-- The `3×8` block sum `Σ_{e<24} F (e/8) (e%8) = Σ_{i<3} Σ_{j<8} F i j`. -/
theorem RsumN_block38_ai (F : Nat → Nat → Real) :
    Req (RsumN (fun e => F (e / 8) (e % 8)) 24) (RsumN (fun i => RsumN (fun j => F i j) 8) 3) := by
  have hb : ∀ n, Req (RsumN (fun e => F (e / 8) (e % 8)) (8 * (n + 1)))
      (Radd (RsumN (fun e => F (e / 8) (e % 8)) (8 * n)) (RsumN (fun j => F n j) 8)) := by
    intro n
    have h := RsumN_add_block_ai (fun e => F (e / 8) (e % 8)) (8 * n) 8
    rw [show 8 * (n + 1) = 8 * n + 8 by omega]
    refine Req_trans h (Radd_congr (Req_refl _) (RsumN_congr 8 (fun j hj => ?_)))
    show Req (F ((8 * n + j) / 8) ((8 * n + j) % 8)) (F n j)
    have h1 : (8 * n + j) / 8 = n := by omega
    have h2 : (8 * n + j) % 8 = j := by omega
    rw [h1, h2]; exact Req_refl _
  show Req (RsumN (fun e => F (e / 8) (e % 8)) (8 * 3)) _
  refine Req_trans (hb 2) ?_
  refine Req_trans (Radd_congr (Req_trans (hb 1) (Radd_congr (hb 0) (Req_refl _))) (Req_refl _)) ?_
  show Req (Radd (Radd (Radd (RsumN _ 0) _) _) _) (Radd (Radd (Radd zero _) _) _)
  exact Req_refl _

/-- Double-sum swap. -/
theorem RsumN_swap_ai (F : Nat → Nat → Real) (m : Nat) :
    ∀ n, Req (RsumN (fun i => RsumN (fun j => F i j) m) n) (RsumN (fun j => RsumN (fun i => F i j) n) m)
  | 0 => Req_symm (Req_trans (RsumN_congr m (fun _ _ => Req_refl _)) (Req_trans (RsumN_const zero m) (Rmul_zero _)))
  | (n + 1) => by
      show Req (Radd (RsumN (fun i => RsumN (fun j => F i j) m) n) (RsumN (fun j => F n j) m))
        (RsumN (fun j => Radd (RsumN (fun i => F i j) n) (F n j)) m)
      exact Req_trans (Radd_congr (RsumN_swap_ai F m n) (Req_refl _)) (Req_symm (RsumN_Radd _ _ m))

-- ===========================================================================
-- (1) The fiber, row/column sums, the physical operator, the sourced formula.
-- ===========================================================================

/-- `(I₃⊗J₈)v` at `(i,j)`: the row sum over the `O`-index. -/
def rowSum (v : Nat → Nat → Real) (i : Nat) : Real := RsumN (fun j => v i j) 8
/-- `(J₃⊗I₈)v` at `(i,j)`: the column sum over the `T`-index. -/
def colSum (v : Nat → Nat → Real) (j : Nat) : Real := RsumN (fun i => v i j) 3

/-- **The physical Atlas operator** `M = −I + J₃⊗I₈ + I₃⊗J₈` on fiber vectors. -/
def atlasOp (v : Nat → Nat → Real) (i j : Nat) : Real := Rsub (Radd (colSum v j) (rowSum v i)) (v i j)

/-- `Π_T`: the part non-constant in the `T`-index, `v − (1/T)·(J₃⊗I₈)v`. -/
def piT (v : Nat → Nat → Real) (i j : Nat) : Real :=
  Rsub (v i j) (Rmul (ofQ (⟨1, 3⟩ : Q) (by decide)) (colSum v j))
/-- `Π_O`: the part non-constant in the `O`-index, `v − (1/O)·(I₃⊗J₈)v`. -/
def piO (v : Nat → Nat → Real) (i j : Nat) : Real :=
  Rsub (v i j) (Rmul (ofQ (⟨1, 8⟩ : Q) (by decide)) (rowSum v i))

/-- `x − (a − c) = (x − a) + c`. -/
theorem Rsub_Rsub_eq (x a c : Real) : Req (Rsub x (Rsub a c)) (Radd (Rsub x a) c) := by
  refine Req_trans (Radd_congr (Req_refl _) (Rneg_Radd _ _)) ?_
  refine Req_trans (Radd_congr (Req_refl _) (Radd_congr (Req_refl _) (Rneg_neg c))) ?_
  exact Req_symm (Radd_assoc _ _ _)

/-- `T·Π_T v = T·v − colSum`. -/
theorem three_piT (v : Nat → Nat → Real) (i j : Nat) :
    Req (Rmul (ofQ (⟨3, 1⟩ : Q) Nat.one_pos) (piT v i j))
        (Rsub (Rmul (ofQ (⟨3, 1⟩ : Q) Nat.one_pos) (v i j)) (colSum v j)) := by
  refine Req_trans (Rmul_sub_distrib _ _ _) (Rsub_congr (Req_refl _) ?_)
  refine Req_trans (Req_symm (Rmul_assoc _ _ _)) ?_
  refine Req_trans (Rmul_congr (Req_trans (Rmul_ofQ_ofQ Nat.one_pos (by decide))
    (ofQ_congr (Qmul_den_pos Nat.one_pos (by decide)) (by decide)
      (by decide : Qeq (mul (⟨3, 1⟩ : Q) (⟨1, 3⟩ : Q)) (⟨1, 1⟩ : Q)))) (Req_refl _)) ?_
  exact Rone_mul _

theorem eight_piO (v : Nat → Nat → Real) (i j : Nat) :
    Req (Rmul (ofQ (⟨8, 1⟩ : Q) Nat.one_pos) (piO v i j))
        (Rsub (Rmul (ofQ (⟨8, 1⟩ : Q) Nat.one_pos) (v i j)) (rowSum v i)) := by
  refine Req_trans (Rmul_sub_distrib _ _ _) (Rsub_congr (Req_refl _) ?_)
  refine Req_trans (Req_symm (Rmul_assoc _ _ _)) ?_
  refine Req_trans (Rmul_congr (Req_trans (Rmul_ofQ_ofQ Nat.one_pos (by decide))
    (ofQ_congr (Qmul_den_pos Nat.one_pos (by decide)) (by decide)
      (by decide : Qeq (mul (⟨8, 1⟩ : Q) (⟨1, 8⟩ : Q)) (⟨1, 1⟩ : Q)))) (Req_refl _)) ?_
  exact Rone_mul _

/-- `10v − 3v − 8v = −v`. -/
theorem ten_sub_three_sub_eight (x : Real) :
    Req (Rsub (Rsub (Rmul (ofQ (⟨10, 1⟩ : Q) Nat.one_pos) x) (Rmul (ofQ (⟨3, 1⟩ : Q) Nat.one_pos) x))
          (Rmul (ofQ (⟨8, 1⟩ : Q) Nat.one_pos) x)) (Rneg x) := by
  refine Req_trans (Rsub_congr (Req_symm (Rmul_sub_distrib_right _ _ _)) (Req_refl _)) ?_
  refine Req_trans (Req_symm (Rmul_sub_distrib_right _ _ _)) ?_
  -- ((10 − 3) − 8)·x = (−1)·x = −x
  have hc : Req (Rsub (Rsub (ofQ (⟨10, 1⟩ : Q) Nat.one_pos) (ofQ (⟨3, 1⟩ : Q) Nat.one_pos))
      (ofQ (⟨8, 1⟩ : Q) Nat.one_pos)) (Rneg one) := by
    refine Req_trans (Rsub_congr (Rsub_ofQ_ofQ Nat.one_pos Nat.one_pos) (Req_refl _)) ?_
    refine Req_trans (Rsub_ofQ_ofQ (add_den_pos Nat.one_pos Nat.one_pos) Nat.one_pos) ?_
    refine Req_trans (ofQ_congr (add_den_pos (add_den_pos Nat.one_pos Nat.one_pos) Nat.one_pos) Nat.one_pos
      (by decide : Qeq (add (add (⟨10, 1⟩ : Q) (neg (⟨3, 1⟩ : Q))) (neg (⟨8, 1⟩ : Q))) (neg (⟨1, 1⟩ : Q)))) ?_
    exact Req_symm (Rneg_ofQ (⟨1, 1⟩ : Q) Nat.one_pos)
  refine Req_trans (Rmul_congr hc (Req_refl x)) ?_
  refine Req_trans (Rmul_comm _ _) ?_
  refine Req_trans (Rmul_neg_right _ _) ?_
  exact Rneg_congr (Rmul_one x)

/-- **THE SOURCED FORMULA IS THE PHYSICAL OPERATOR**: `(O+2)v − T·Π_T v − O·Π_O v = Mv`. -/
theorem atlasOp_sourced (v : Nat → Nat → Real) (i j : Nat) :
    Req (Rsub (Rsub (Rmul (ofQ (⟨10, 1⟩ : Q) Nat.one_pos) (v i j))
                (Rmul (ofQ (⟨3, 1⟩ : Q) Nat.one_pos) (piT v i j)))
              (Rmul (ofQ (⟨8, 1⟩ : Q) Nat.one_pos) (piO v i j)))
        (atlasOp v i j) := by
  refine Req_trans (Rsub_congr (Rsub_congr (Req_refl _) (three_piT v i j)) (eight_piO v i j)) ?_
  -- (10v − (3v − c)) − (8v − r) = ((10v − 3v) + c) − (8v − r) = (((10v − 3v) + c) − 8v) + r
  refine Req_trans (Rsub_congr (Rsub_Rsub_eq _ _ _) (Req_refl _)) ?_
  refine Req_trans (Rsub_Rsub_eq _ _ _) ?_
  -- ((A + c) − 8v) + r  with A = 10v − 3v:  = ((A − 8v) + c) + r = (−v + c) + r = (c + r) − v
  have h1 : Req (Rsub (Radd (Rsub (Rmul (ofQ (⟨10, 1⟩ : Q) Nat.one_pos) (v i j))
      (Rmul (ofQ (⟨3, 1⟩ : Q) Nat.one_pos) (v i j))) (colSum v j)) (Rmul (ofQ (⟨8, 1⟩ : Q) Nat.one_pos) (v i j)))
      (Radd (Rneg (v i j)) (colSum v j)) := by
    refine Req_trans (Radd_assoc _ _ _) ?_
    refine Req_trans (Radd_congr (Req_refl _) (Radd_comm _ _)) ?_
    refine Req_trans (Req_symm (Radd_assoc _ _ _)) ?_
    exact Radd_congr (ten_sub_three_sub_eight (v i j)) (Req_refl _)
  refine Req_trans (Radd_congr h1 (Req_refl _)) ?_
  show Req (Radd (Radd (Rneg (v i j)) (colSum v j)) (rowSum v i)) (Radd (Radd (colSum v j) (rowSum v i)) (Rneg (v i j)))
  refine Req_trans (Radd_assoc _ _ _) (Req_trans (Radd_comm _ _) (Req_refl _))


-- ===========================================================================
-- (2) The genuine `K_{3,8}` incidence and `Mv = Bᵀ(Bv) − v`.
-- ===========================================================================

/-- Vertices `u < 11`: `u < 3` are the `L`-vertices, `u = 3 + j` the `R`-vertices; edges `e < 24` are
    `e = 8·i + j`.  The unsigned incidence `B u e ∈ {0,1}`. -/
def incB (u e : Nat) : Real :=
  if (u < 3 ∧ u = e / 8) ∨ (3 ≤ u ∧ u - 3 = e % 8) then one else zero

/-- `(Bv)_u = Σ_e B u e · v_e`. -/
def incBv (v : Nat → Nat → Real) (u : Nat) : Real :=
  RsumN (fun e => Rmul (incB u e) (v (e / 8) (e % 8))) 24

/-- `(Bᵀw)_e = Σ_u B u e · w_u`. -/
def incBt (w : Nat → Real) (e : Nat) : Real := RsumN (fun u => Rmul (incB u e) (w u)) 11

/-- `(Bv)_{L i} = rowSum v i` for `i < 3`. -/
theorem incBv_left (v : Nat → Nat → Real) (i : Nat) (hi : i < 3) : Req (incBv v i) (rowSum v i) := by
  unfold incBv rowSum
  refine Req_trans (RsumN_block38_ai (fun a b => Rmul (incB i (8 * a + b)) (v a b))
    |> fun h => Req_trans (RsumN_congr 24 (fun e _ => ?_)) h) ?_
  · show Req (Rmul (incB i e) (v (e / 8) (e % 8))) (Rmul (incB i (8 * (e / 8) + e % 8)) (v (e / 8) (e % 8)))
    rw [Nat.div_add_mod e 8]; exact Req_refl _
  · -- Σ_a Σ_b [a = i]·v a b = Σ_b v i b
    refine Req_trans (RsumN_congr (G := fun a => RsumN (fun b => if a = i then v a b else zero) 8) 3
      (fun a _ => RsumN_congr (G := fun b => if a = i then v a b else zero) 8 (fun b hb => ?_))) ?_
    · show Req (Rmul (incB i (8 * a + b)) (v a b)) (if a = i then v a b else zero)
      unfold incB
      have h1 : (8 * a + b) / 8 = a := by omega
      have h2 : (8 * a + b) % 8 = b := by omega
      rw [h1, h2]
      by_cases hai : a = i
      · subst hai
        rw [if_pos (Or.inl ⟨hi, rfl⟩), if_pos rfl]; exact Rone_mul _
      · have hne : ¬ ((i < 3 ∧ i = a) ∨ (3 ≤ i ∧ i - 3 = b)) := by omega
        rw [if_neg hne, if_neg hai]; exact Req_trans (Rmul_comm _ _) (Rmul_zero _)
    · refine Req_trans (RsumN_congr 3 (fun a _ => ?_)) (RsumN_indicator_ai (fun a => RsumN (fun b => v a b) 8) i 3 hi)
      show Req (RsumN (fun b => if a = i then v a b else zero) 8) (if a = i then RsumN (fun b => v a b) 8 else zero)
      by_cases hai : a = i
      · rw [if_pos hai]; exact RsumN_congr 8 (fun b _ => by rw [if_pos hai]; exact Req_refl _)
      · rw [if_neg hai]
        exact Req_trans (RsumN_congr 8 (fun b _ => by rw [if_neg hai]; exact Req_refl _))
          (Req_trans (RsumN_const zero 8) (Rmul_zero _))

/-- `(Bv)_{R j} = colSum v j` for `j < 8`. -/
theorem incBv_right (v : Nat → Nat → Real) (j : Nat) (hj : j < 8) : Req (incBv v (3 + j)) (colSum v j) := by
  unfold incBv colSum
  refine Req_trans (RsumN_block38_ai (fun a b => Rmul (incB (3 + j) (8 * a + b)) (v a b))
    |> fun h => Req_trans (RsumN_congr 24 (fun e _ => ?_)) h) ?_
  · show Req (Rmul (incB (3 + j) e) (v (e / 8) (e % 8))) (Rmul (incB (3 + j) (8 * (e / 8) + e % 8)) (v (e / 8) (e % 8)))
    rw [Nat.div_add_mod e 8]; exact Req_refl _
  · refine Req_trans (RsumN_congr (G := fun a => RsumN (fun b => if b = j then v a b else zero) 8) 3
      (fun a _ => RsumN_congr (G := fun b => if b = j then v a b else zero) 8 (fun b _ => ?_))) ?_
    · show Req (Rmul (incB (3 + j) (8 * a + b)) (v a b)) (if b = j then v a b else zero)
      unfold incB
      have h1 : (8 * a + b) / 8 = a := by omega
      have h2 : (8 * a + b) % 8 = b := by omega
      rw [h1, h2]
      by_cases hbj : b = j
      · subst hbj
        rw [if_pos (Or.inr ⟨by omega, by omega⟩), if_pos rfl]; exact Rone_mul _
      · have hne : ¬ ((3 + j < 3 ∧ 3 + j = a) ∨ (3 ≤ 3 + j ∧ 3 + j - 3 = b)) := by omega
        rw [if_neg hne, if_neg hbj]; exact Req_trans (Rmul_comm _ _) (Rmul_zero _)
    · exact RsumN_congr 3 (fun a _ => RsumN_indicator_ai (fun b => v a b) j 8 hj)

/-- `(Bᵀw)_e = w_{L (e/8)} + w_{R (e%8)}` for `e < 24`. -/
theorem incBt_eq (w : Nat → Real) (e : Nat) (he : e < 24) :
    Req (incBt w e) (Radd (w (e / 8)) (w (3 + e % 8))) := by
  unfold incBt
  have hi : e / 8 < 3 := by omega
  have hj : e % 8 < 8 := by omega
  refine Req_trans (RsumN_add_block_ai (fun u => Rmul (incB u e) (w u)) 3 8) ?_
  refine Radd_congr ?_ ?_
  · refine Req_trans (RsumN_congr 3 (fun u hu => ?_)) (RsumN_indicator_ai w (e / 8) 3 hi)
    show Req (Rmul (incB u e) (w u)) (if u = e / 8 then w u else zero)
    unfold incB
    by_cases h : u = e / 8
    · rw [if_pos (Or.inl ⟨hu, h⟩), if_pos h]; exact Rone_mul _
    · have hne : ¬ ((u < 3 ∧ u = e / 8) ∨ (3 ≤ u ∧ u - 3 = e % 8)) := by omega
      rw [if_neg hne, if_neg h]; exact Req_trans (Rmul_comm _ _) (Rmul_zero _)
  · refine Req_trans (RsumN_congr 8 (fun j hj' => ?_)) (RsumN_indicator_ai (fun j => w (3 + j)) (e % 8) 8 hj)
    show Req (Rmul (incB (3 + j) e) (w (3 + j))) (if j = e % 8 then w (3 + j) else zero)
    unfold incB
    by_cases h : j = e % 8
    · rw [if_pos (Or.inr ⟨by omega, by omega⟩), if_pos h]; exact Rone_mul _
    · have hne : ¬ ((3 + j < 3 ∧ 3 + j = e / 8) ∨ (3 ≤ 3 + j ∧ 3 + j - 3 = e % 8)) := by omega
      rw [if_neg hne, if_neg h]; exact Req_trans (Rmul_comm _ _) (Rmul_zero _)

/-- **`M = BᵀB − I`**: `(Bᵀ(Bv))_e − v_e = (Mv)_{(e/8, e%8)}` for every edge `e < 24`. -/
theorem atlasOp_eq_BtB (v : Nat → Nat → Real) (e : Nat) (he : e < 24) :
    Req (Rsub (incBt (incBv v) e) (v (e / 8) (e % 8))) (atlasOp v (e / 8) (e % 8)) := by
  have hi : e / 8 < 3 := by omega
  have hj : e % 8 < 8 := by omega
  refine Rsub_congr (Req_trans (incBt_eq _ e he) ?_) (Req_refl _)
  refine Req_trans (Radd_congr (incBv_left v _ hi) (incBv_right v _ hj)) (Radd_comm _ _)

-- ===========================================================================
-- (3) The cycle space (`−1` eigenspace) and the cut space.
-- ===========================================================================

/-- `ker B`: zero row and column sums (the cycle/interaction space). -/
def IsCycle (v : Nat → Nat → Real) : Prop :=
  (∀ i, i < 3 → Req (rowSum v i) zero) ∧ (∀ j, j < 8 → Req (colSum v j) zero)

/-- **The cycle space is the `−1` eigenspace**: `Mv = −v` on `ker B`. -/
theorem atlasOp_cycle (v : Nat → Nat → Real) (h : IsCycle v) (i j : Nat) (hi : i < 3) (hj : j < 8) :
    Req (atlasOp v i j) (Rneg (v i j)) := by
  unfold atlasOp
  refine Req_trans (Rsub_congr (Radd_congr (h.2 j hj) (h.1 i hi)) (Req_refl _)) ?_
  exact Req_trans (Rsub_congr (Radd_zero zero) (Req_refl _)) (Req_trans (Radd_comm _ _) (Radd_zero _))

/-- A four-cycle circulation `e_{ij} − e_{ij'} − e_{i'j} + e_{i'j'}`. -/
def fourCycle (i j i' j' : Nat) (a b : Nat) : Real :=
  Radd (Radd (if a = i ∧ b = j then one else zero) (Rneg (if a = i ∧ b = j' then one else zero)))
       (Radd (Rneg (if a = i' ∧ b = j then one else zero)) (if a = i' ∧ b = j' then one else zero))

/-- The cut vector `a_i + b_j` (the range of `Bᵀ`). -/
def cutVec (a b : Nat → Real) (i j : Nat) : Real := Radd (a i) (b j)

theorem rowSum_cut (a b : Nat → Real) (i : Nat) :
    Req (rowSum (cutVec a b) i) (Radd (Rmul (RofNat 8) (a i)) (RsumN b 8)) :=
  Req_trans (RsumN_Radd (fun _ => a i) b 8) (Radd_congr (RsumN_const (a i) 8) (Req_refl _))

theorem colSum_cut (a b : Nat → Real) (j : Nat) :
    Req (colSum (cutVec a b) j) (Radd (RsumN a 3) (Rmul (RofNat 3) (b j))) :=
  Req_trans (RsumN_Radd a (fun _ => b j) 3) (Radd_congr (Req_refl _) (RsumN_const (b j) 3))

/-- `(a+b)+(c+d) = (a+c)+(b+d)`. -/
theorem Radd_regroup (a b c d : Real) : Req (Radd (Radd a b) (Radd c d)) (Radd (Radd a c) (Radd b d)) := by
  refine Req_trans (Radd_assoc a b (Radd c d)) ?_
  refine Req_trans (Radd_congr (Req_refl a) (Req_symm (Radd_assoc b c d))) ?_
  refine Req_trans (Radd_congr (Req_refl a) (Radd_congr (Radd_comm b c) (Req_refl d))) ?_
  refine Req_trans (Radd_congr (Req_refl a) (Radd_assoc c b d)) ?_
  exact Req_symm (Radd_assoc a c (Radd b d))

/-- `n·x − x = (n−1)·x` at the rational scalars `8 ↦ 7` and `3 ↦ 2`. -/
theorem eight_sub_one (x : Real) :
    Req (Rsub (Rmul (ofQ (⟨8, 1⟩ : Q) Nat.one_pos) x) x) (Rmul (ofQ (⟨7, 1⟩ : Q) Nat.one_pos) x) := by
  refine Req_trans (Rsub_congr (Req_refl _) (Req_symm (Rone_mul x))) ?_
  refine Req_trans (Req_symm (Rmul_sub_distrib_right _ _ _)) ?_
  refine Rmul_congr ?_ (Req_refl x)
  exact Req_trans (Rsub_ofQ_ofQ Nat.one_pos Nat.one_pos) (ofQ_congr _ Nat.one_pos (by decide))

theorem three_sub_one (x : Real) :
    Req (Rsub (Rmul (ofQ (⟨3, 1⟩ : Q) Nat.one_pos) x) x) (Rmul (ofQ (⟨2, 1⟩ : Q) Nat.one_pos) x) := by
  refine Req_trans (Rsub_congr (Req_refl _) (Req_symm (Rone_mul x))) ?_
  refine Req_trans (Req_symm (Rmul_sub_distrib_right _ _ _)) ?_
  refine Rmul_congr ?_ (Req_refl x)
  exact Req_trans (Rsub_ofQ_ofQ Nat.one_pos Nat.one_pos) (ofQ_congr _ Nat.one_pos (by decide))

theorem RofNat_eq (n : Nat) : RofNat n = ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos := rfl

/-- `(3b + (8a + S)) − (a + b) = (7a + 2b) + S`. -/
theorem cut_regroup (a b S : Real) :
    Req (Rsub (Radd (Rmul (ofQ (⟨3, 1⟩ : Q) Nat.one_pos) b) (Radd (Rmul (ofQ (⟨8, 1⟩ : Q) Nat.one_pos) a) S))
          (Radd a b))
        (Radd (Radd (Rmul (ofQ (⟨7, 1⟩ : Q) Nat.one_pos) a) (Rmul (ofQ (⟨2, 1⟩ : Q) Nat.one_pos) b)) S) := by
  -- (3b + (8a + S)) + (−a + −b) = ((8a + 3b) + S) + (−a + −b) = ((8a + 3b) + (−a + −b)) + S
  refine Req_trans (Radd_congr (Req_trans (Req_symm (Radd_assoc _ _ _))
    (Radd_congr (Radd_comm _ _) (Req_refl S))) (Rneg_Radd a b)) ?_
  refine Req_trans (Radd_assoc _ _ _) ?_
  refine Req_trans (Radd_congr (Req_refl _) (Radd_comm _ _)) ?_
  refine Req_trans (Req_symm (Radd_assoc _ _ _)) ?_
  refine Radd_congr ?_ (Req_refl S)
  refine Req_trans (Radd_regroup _ _ _ _) ?_
  exact Radd_congr (eight_sub_one a) (three_sub_one b)

set_option maxHeartbeats 1000000 in
/-- **The cut action** with `Σ_i a_i = 0`: `M(a⊕b)_{ij} = 7·a_i + 2·b_j + Σ_j b_j`. -/
theorem atlasOp_cut (a b : Nat → Real) (hS : Req (RsumN a 3) zero) (i j : Nat) :
    Req (atlasOp (cutVec a b) i j)
        (Radd (Radd (Rmul (ofQ (⟨7, 1⟩ : Q) Nat.one_pos) (a i)) (Rmul (ofQ (⟨2, 1⟩ : Q) Nat.one_pos) (b j)))
              (RsumN b 8)) := by
  unfold atlasOp
  refine Req_trans (Rsub_congr (Radd_congr (colSum_cut a b j) (rowSum_cut a b i)) (Req_refl _)) ?_
  rw [RofNat_eq, RofNat_eq]
  refine Req_trans (Rsub_congr (Radd_congr (Req_trans (Radd_congr hS (Req_refl _))
    (Req_trans (Radd_comm _ _) (Radd_zero _))) (Req_refl _)) (Req_refl _)) ?_
  exact cut_regroup (a i) (b j) (RsumN b 8)


-- ===========================================================================
-- (4) THE SQUARE-ROOT-FREE COMPRESSION `Q_M(a⊕b) = 56·Σa² + 6·Σb² + 3·(Σb)²`.
-- ===========================================================================

/-- The quadratic form `Q_M(v) = Σ_ij v_ij·(Mv)_ij`. -/
def Qform (v : Nat → Nat → Real) : Real :=
  RsumN (fun i => RsumN (fun j => Rmul (v i j) (atlasOp v i j)) 8) 3

def sq (x : Real) : Real := Rmul x x
def c7 : Real := ofQ (⟨7, 1⟩ : Q) Nat.one_pos
def c2 : Real := ofQ (⟨2, 1⟩ : Q) Nat.one_pos
def c9 : Real := ofQ (⟨9, 1⟩ : Q) Nat.one_pos
def c8 : Real := ofQ (⟨8, 1⟩ : Q) Nat.one_pos
def c3 : Real := ofQ (⟨3, 1⟩ : Q) Nat.one_pos
def c56 : Real := ofQ (⟨56, 1⟩ : Q) Nat.one_pos
def c6 : Real := ofQ (⟨6, 1⟩ : Q) Nat.one_pos

/-- `x·(7x + 2y) = 7x² + 2xy`. -/
theorem x_mul_lin (x y : Real) :
    Req (Rmul x (Radd (Rmul c7 x) (Rmul c2 y))) (Radd (Rmul c7 (sq x)) (Rmul c2 (Rmul x y))) := by
  refine Req_trans (Rmul_distrib _ _ _) (Radd_congr ?_ ?_)
  · exact Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Rmul_congr (Rmul_comm _ _) (Req_refl _)) (Rmul_assoc _ _ _))
  · exact Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Rmul_congr (Rmul_comm _ _) (Req_refl _)) (Rmul_assoc _ _ _))

/-- `y·(7x + 2y) = 7xy + 2y²`. -/
theorem y_mul_lin (x y : Real) :
    Req (Rmul y (Radd (Rmul c7 x) (Rmul c2 y))) (Radd (Rmul c7 (Rmul x y)) (Rmul c2 (sq y))) := by
  refine Req_trans (Rmul_distrib _ _ _) (Radd_congr ?_ ?_)
  · refine Req_trans (Req_symm (Rmul_assoc _ _ _)) ?_
    refine Req_trans (Rmul_congr (Rmul_comm _ _) (Req_refl _)) ?_
    exact Req_trans (Rmul_assoc _ _ _) (Rmul_congr (Req_refl _) (Rmul_comm _ _))
  · exact Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Rmul_congr (Rmul_comm _ _) (Req_refl _)) (Rmul_assoc _ _ _))

/-- `2p + 7p = 9p`. -/
theorem two_add_seven (p : Real) : Req (Radd (Rmul c2 p) (Rmul c7 p)) (Rmul c9 p) := by
  refine Req_trans (Req_symm (Rmul_distrib_right _ _ _)) (Rmul_congr ?_ (Req_refl _))
  exact Req_trans (Radd_ofQ_ofQ Nat.one_pos Nat.one_pos) (ofQ_congr _ Nat.one_pos (by decide))

/-- **The term expansion** `(x+y)·((7x+2y)+S) = ((7x² + 9xy) + (2y² + xS)) + yS`. -/
theorem cut_term_expand (x y S : Real) :
    Req (Rmul (Radd x y) (Radd (Radd (Rmul c7 x) (Rmul c2 y)) S))
        (Radd (Radd (Radd (Rmul c7 (sq x)) (Rmul c9 (Rmul x y))) (Radd (Rmul c2 (sq y)) (Rmul x S))) (Rmul y S)) := by
  -- step 1: distribute
  have h1 : Req (Rmul (Radd x y) (Radd (Radd (Rmul c7 x) (Rmul c2 y)) S))
      (Radd (Radd (Rmul x (Radd (Rmul c7 x) (Rmul c2 y))) (Rmul y (Radd (Rmul c7 x) (Rmul c2 y))))
            (Radd (Rmul x S) (Rmul y S))) :=
    Req_trans (Rmul_distrib _ _ _) (Radd_congr (Rmul_distrib_right _ _ _) (Rmul_distrib_right _ _ _))
  -- step 2: the two inner products
  have h2 : Req (Radd (Rmul x (Radd (Rmul c7 x) (Rmul c2 y))) (Rmul y (Radd (Rmul c7 x) (Rmul c2 y))))
      (Radd (Radd (Rmul c7 (sq x)) (Rmul c2 (Rmul x y))) (Radd (Rmul c7 (Rmul x y)) (Rmul c2 (sq y)))) :=
    Radd_congr (x_mul_lin x y) (y_mul_lin x y)
  -- step 3: regroup ((A + B) + (C + D)) = ((A + (B + C)) + D) with B + C = 9xy
  have h3 : Req (Radd (Radd (Rmul c7 (sq x)) (Rmul c2 (Rmul x y))) (Radd (Rmul c7 (Rmul x y)) (Rmul c2 (sq y))))
      (Radd (Radd (Rmul c7 (sq x)) (Rmul c9 (Rmul x y))) (Rmul c2 (sq y))) := by
    refine Req_trans (Radd_assoc _ _ _) ?_
    refine Req_trans (Radd_congr (Req_refl _) (Req_symm (Radd_assoc _ _ _))) ?_
    refine Req_trans (Req_symm (Radd_assoc _ _ _)) ?_
    exact Radd_congr (Radd_congr (Req_refl _) (two_add_seven (Rmul x y))) (Req_refl _)
  -- step 4: ((P + 2y²) + (xS + yS)) = ((P + (2y² + xS)) + yS)
  have h4 : Req (Radd (Radd (Radd (Rmul c7 (sq x)) (Rmul c9 (Rmul x y))) (Rmul c2 (sq y))) (Radd (Rmul x S) (Rmul y S)))
      (Radd (Radd (Radd (Rmul c7 (sq x)) (Rmul c9 (Rmul x y))) (Radd (Rmul c2 (sq y)) (Rmul x S))) (Rmul y S)) := by
    refine Req_trans (Req_symm (Radd_assoc _ _ _)) ?_
    exact Radd_congr (Radd_assoc _ _ _) (Req_refl _)
  exact Req_trans h1 (Req_trans (Radd_congr (Req_trans h2 h3) (Req_refl _)) h4)

/-- Inner sum over `j < 8` of the expanded term, with `S = Σ_j b_j`. -/
theorem cut_inner_sum (x : Real) (b : Nat → Real) :
    Req (RsumN (fun j => Radd (Radd (Radd (Rmul c7 (sq x)) (Rmul c9 (Rmul x (b j))))
          (Radd (Rmul c2 (sq (b j))) (Rmul x (RsumN b 8)))) (Rmul (b j) (RsumN b 8))) 8)
        (Radd (Radd (Radd (Rmul (RofNat 8) (Rmul c7 (sq x))) (Rmul c9 (Rmul x (RsumN b 8))))
          (Radd (Rmul c2 (RsumN (fun j => sq (b j)) 8)) (Rmul (RofNat 8) (Rmul x (RsumN b 8)))))
          (Rmul (RsumN b 8) (RsumN b 8))) := by
  refine Req_trans (RsumN_Radd
    (fun j => Radd (Radd (Rmul c7 (sq x)) (Rmul c9 (Rmul x (b j)))) (Radd (Rmul c2 (sq (b j))) (Rmul x (RsumN b 8))))
    (fun j => Rmul (b j) (RsumN b 8)) 8) (Radd_congr ?_ (RsumN_smul_right_ai (RsumN b 8) b 8))
  refine Req_trans (RsumN_Radd (fun j => Radd (Rmul c7 (sq x)) (Rmul c9 (Rmul x (b j))))
    (fun j => Radd (Rmul c2 (sq (b j))) (Rmul x (RsumN b 8))) 8) (Radd_congr ?_ ?_)
  · refine Req_trans (RsumN_Radd (fun _ => Rmul c7 (sq x)) (fun j => Rmul c9 (Rmul x (b j))) 8)
      (Radd_congr (RsumN_const _ 8) ?_)
    exact Req_trans (RsumN_smul_ai c9 (fun j => Rmul x (b j)) 8) (Rmul_congr (Req_refl _) (RsumN_smul_ai x b 8))
  · exact Req_trans (RsumN_Radd (fun j => Rmul c2 (sq (b j))) (fun _ => Rmul x (RsumN b 8)) 8)
      (Radd_congr (RsumN_smul_ai c2 (fun j => sq (b j)) 8) (RsumN_const _ 8))

/-- Outer sum over `i < 3` with `Σ_i a_i = 0`. -/
theorem cut_outer_sum (a : Nat → Real) (S T : Real) (hS : Req (RsumN a 3) zero) :
    Req (RsumN (fun i => Radd (Radd (Radd (Rmul (RofNat 8) (Rmul c7 (sq (a i)))) (Rmul c9 (Rmul (a i) S)))
          (Radd (Rmul c2 T) (Rmul (RofNat 8) (Rmul (a i) S)))) (Rmul S S)) 3)
        (Radd (Rmul c56 (RsumN (fun i => sq (a i)) 3)) (Radd (Rmul c6 T) (Rmul c3 (Rmul S S)))) := by
  refine Req_trans (RsumN_Radd _ _ 3) ?_
  refine Req_trans (Radd_congr (RsumN_Radd _ _ 3) (RsumN_const _ 3)) ?_
  refine Req_trans (Radd_congr (Radd_congr (RsumN_Radd _ _ 3) (RsumN_Radd _ _ 3)) (Req_refl _)) ?_
  -- pieces: Σ 8·7a² = 8·7·Σa²;  Σ 9·(a S) = 9·(Σa)·S = 0;  Σ 2T = 3·2T;  Σ 8 a S = 0
  have h1 : Req (RsumN (fun i => Rmul (RofNat 8) (Rmul c7 (sq (a i)))) 3)
      (Rmul c56 (RsumN (fun i => sq (a i)) 3)) := by
    refine Req_trans (RsumN_smul_ai _ _ 3) ?_
    refine Req_trans (Rmul_congr (Req_refl _) (RsumN_smul_ai c7 _ 3)) ?_
    refine Req_trans (Req_symm (Rmul_assoc _ _ _)) (Rmul_congr ?_ (Req_refl _))
    exact Req_trans (Rmul_ofQ_ofQ Nat.one_pos Nat.one_pos) (ofQ_congr _ Nat.one_pos (by decide))
  have hzero : ∀ c : Real, Req (RsumN (fun i => Rmul c (Rmul (a i) S)) 3) zero := by
    intro c
    refine Req_trans (RsumN_smul_ai c _ 3) ?_
    refine Req_trans (Rmul_congr (Req_refl _) (RsumN_smul_right_ai S a 3)) ?_
    refine Req_trans (Rmul_congr (Req_refl _) (Rmul_congr hS (Req_refl _))) ?_
    exact Req_trans (Rmul_congr (Req_refl _) (Req_trans (Rmul_comm _ _) (Rmul_zero _))) (Rmul_zero _)
  have h3 : Req (RsumN (fun _ => Rmul c2 T) 3) (Rmul c6 T) := by
    refine Req_trans (RsumN_const _ 3) ?_
    refine Req_trans (Req_symm (Rmul_assoc _ _ _)) (Rmul_congr ?_ (Req_refl _))
    exact Req_trans (Rmul_ofQ_ofQ Nat.one_pos Nat.one_pos) (ofQ_congr _ Nat.one_pos (by decide))
  refine Req_trans (Radd_congr (Radd_congr (Radd_congr h1 (hzero c9)) (Radd_congr h3 (hzero (RofNat 8)))) (Req_refl _)) ?_
  -- ((56Σa² + 0) + (6T + 0)) + 3·S² = 56Σa² + (6T + 3S²)
  refine Req_trans (Radd_congr (Radd_congr (Radd_zero _) (Radd_zero _)) (Req_refl _)) ?_
  exact Radd_assoc _ _ _

set_option maxHeartbeats 1000000 in
/-- **THE COMPRESSION FORMULA**: with `Σ_i a_i = 0`,
    `Q_M(a⊕b) = 56·Σ_i a_i² + 6·Σ_j b_j² + 3·(Σ_j b_j)²`. -/
theorem Qform_cut (a b : Nat → Real) (hS : Req (RsumN a 3) zero) :
    Req (Qform (cutVec a b))
        (Radd (Rmul c56 (RsumN (fun i => sq (a i)) 3))
              (Radd (Rmul c6 (RsumN (fun j => sq (b j)) 8)) (Rmul c3 (Rmul (RsumN b 8) (RsumN b 8))))) := by
  unfold Qform
  refine Req_trans (RsumN_congr
    (G := fun i => RsumN (fun j => Radd (Radd (Radd (Rmul c7 (sq (a i))) (Rmul c9 (Rmul (a i) (b j))))
      (Radd (Rmul c2 (sq (b j))) (Rmul (a i) (RsumN b 8)))) (Rmul (b j) (RsumN b 8))) 8) 3
    (fun i _ => RsumN_congr
      (G := fun j => Radd (Radd (Radd (Rmul c7 (sq (a i))) (Rmul c9 (Rmul (a i) (b j))))
        (Radd (Rmul c2 (sq (b j))) (Rmul (a i) (RsumN b 8)))) (Rmul (b j) (RsumN b 8))) 8 (fun j _ => ?_))) ?_
  · exact Req_trans (Rmul_congr (Req_refl _) (atlasOp_cut a b hS i j)) (cut_term_expand (a i) (b j) (RsumN b 8))
  · refine Req_trans (RsumN_congr 3 (fun i _ => cut_inner_sum (a i) b)) ?_
    exact cut_outer_sum a (RsumN b 8) (RsumN (fun j => sq (b j)) 8) hS

/-- **`Q_M ≥ 0` on the cut slice** `Σ_i a_i = 0` (a sum of squares with positive weights). -/
theorem Qform_cut_nonneg (a b : Nat → Real) (hS : Req (RsumN a 3) zero) : Rnonneg (Qform (cutVec a b)) := by
  refine Rnonneg_congr (Req_symm (Qform_cut a b hS)) ?_
  have hsq : ∀ (F : Nat → Real) N, Rnonneg (RsumN (fun i => sq (F i)) N) := by
    intro F N
    induction N with
    | zero => exact Rnonneg_of_Rle_zero (Rle_refl _)
    | succ N ih => exact Rnonneg_Radd ih (Rnonneg_Rmul_self _)
  refine Rnonneg_Radd (Rnonneg_Rmul (Rnonneg_ofQ Nat.one_pos (by decide)) (hsq a 3)) ?_
  exact Rnonneg_Radd (Rnonneg_Rmul (Rnonneg_ofQ Nat.one_pos (by decide)) (hsq b 8))
    (Rnonneg_Rmul (Rnonneg_ofQ Nat.one_pos (by decide)) (Rnonneg_Rmul_self _))


end UOR.Bridge.F1Square.Square
