/-
F1 square — **finite weighted carriers with disjoint tags, and the transfer gate** (`AtlasCarrier.lean`).

A STAGE `σ` fixes the quadrature: `Nt+1` Haar points `t_i = a + w·i/(Nt+1)` and `Nx+1` scale points
`x_j = 1 + (B−1)·j/(Nx+1)` (so `x_0 = 1`), with the source-exact KERNEL FLOOR `dyQ k = 2^{-k}` of `archTrunc`
(only the floor is source-exact here: this grid samples `[1, B]`, while `archTrunc k` integrates
`[1 + 2^{-k}, ∞)`; the exact split of `archTrunc` is `AtlasTailSplit.lean`).  Every summand of the
coupled form gets its own DISJOINT tag (`Site`): `prime (m, side, i)`, `pole (j, i)`, `cst i`,
`tail (j, i)`.  The 24 Atlas address is only an internal gauge of each fiber; the tags are external,
so no cross terms between summands exist.  Each site carries

 * a NONNEGATIVE weight `siteWeight` (quadrature cell × external density; `siteWeight_nonneg`),
 * the CUT coordinate `A` and the CYCLE coordinate `B` of the site's fiber (`cutStage`, `cycleStage`),
   `⟨Φ_f, MΦ_g⟩ = 4A_fA_g − 4B_fB_g` at every site (`stagePair_split`).

THE TRANSFER GATE.  `atlasTransferStage σ : CutCarrier → CycleCarrier` is the EXPLICIT linear map

    `(Kc)(prime m side i) = c(prime m side i) + c(pole 0 i)`,
    `(Kc)(pole j i)       = c(pole j i) − c(pole 0 i)`,
    `(Kc)(cst i)          = c(pole 0 i)`,
    `(Kc)(tail j i)       = c(tail j i) + (1/max(x_j,1))·c(pole 0 i)`,

and the FACTORIZATION holds for EVERY test: `cycleStage σ f = atlasTransferStage σ (cutStage σ f)`
(`mixedCycleStage_factor`).  The mechanism: the pole site at `x_0 = 1` has cut coordinate
`A = (U_1 + V)/4 = V/2` (`cut_pole_zero`, from `Uc_one_eq_Vc`), which is exactly the datum every
cycle coordinate needs beyond its own cut coordinate — so the transfer genuinely mixes the pole
column into the prime, constant and tail coordinates.  The NECESSARY KERNEL CONDITION follows
(`atlasTransfer_kernel`): `cutStage σ f = 0 → cycleStage σ f = 0`.

THE CONTRACTION TEST.  `atlasTransferStage_not_contract` is only a WEAK REVERSE MASS BOUND: for the pulse
`c₀` at the single site `pole 0 i₀` and a fine enough scale quadrature, `cutMass σ c₀ ≤ cycleMass σ (K c₀)`.
It is not a proof of `¬ Contractive`; the pulse lies outside `range cutStage` only when `α ≠ 0`, and
that non-membership is NOT proved here — it only falsifies this endpoint-copying extension off the
range.  THE GENERIC NO-GO (`shear_no_go`, `shear_no_go_transfer`) is CONDITIONAL: for any transfer of
shear form `(Tc)_p = c_p + L(c)` at a prime site `p`, with `L` additive, blind to the prime axis at `p`,
and injecting an anchor `a` as `L(a)_p = β`, the witness `c_M = Mβ·e_p + a` satisfies
`cycleMass(T c_M) ≥ cutMass(c_M) + 4·w_p·β²` for every `M` with `cutMass a ≤ 8M·w_p·β²`.  The existence
of such an `M` (Archimedean, when `w_p·β² > 0`) and the positivity `w_p·β² > 0` needed for a STRICT
excess are hypotheses, so this does not formally establish `¬ Contractive`; it excludes the additive
prime-blind shear architecture quantitatively, including weighted pole–tail averages in place of the
`x = 1` anchor.  Contractivity restricted to `range cutStage` is not addressed — it is the coupling
sign itself.  AMBIENT TYPE: `Site → Real` is an infinite seminormed ambient space; the carrier is
finite only through the finite site ranges of `siteSum` (`m < X`, `side < 2`, `i ≤ Nt`, `j ≤ Nx`).
Nothing here asserts `CurrentArchDominatesPrime`.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasFibers

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

attribute [local irreducible] RsumN

-- ===========================================================================
-- (1) Stages, sites, points.
-- ===========================================================================

/-- A quadrature stage: `Nt+1` Haar points, `Nx+1` scale points, and the tail truncation index `k`
    (the SOURCE-EXACT kernel floor `dyQ k = 2^{-k}` of `archTrunc`: `K_k(x) = 1/max(x − 1/max(x,1), 2^{-k})`). -/
structure Stage where
  Nt : Nat
  Nx : Nat
  k : Nat

/-- The disjoint site tags. -/
inductive Site
  | prime (m side i : Nat)
  | pole (j i : Nat)
  | cst (i : Nat)
  | tail (j i : Nat)

/-- The Haar quadrature point `t_i = a + w·(i/(Nt+1))`. -/
def tPt (C : NormCtx) (σ : Stage) (i : Nat) : Real :=
  affC C (ofQ (⟨(i : Int), σ.Nt + 1⟩ : Q) (Nat.succ_pos _))

theorem canonBm1_den (C : NormCtx) : 0 < (Qsub (canonB C) (⟨1, 1⟩ : Q)).den := Qsub_den_pos (canonB_den C) Nat.one_pos
theorem canonBm1_num (C : NormCtx) : 0 ≤ (Qsub (canonB C) (⟨1, 1⟩ : Q)).num := Qsub_num_nonneg (canonB_one C)

/-- The scale quadrature point `x_j = 1 + (B−1)·(j/(Nx+1))`. -/
def xPt (C : NormCtx) (σ : Stage) (j : Nat) : Real :=
  affineMap (⟨1, 1⟩ : Q) (Qsub (canonB C) (⟨1, 1⟩ : Q)) (by decide) (canonBm1_den C)
    (ofQ (⟨(j : Int), σ.Nx + 1⟩ : Q) (Nat.succ_pos _))

/-- `x_0 = 1`. -/
theorem xPt_zero (C : NormCtx) (σ : Stage) : Req (xPt C σ 0) one := by
  unfold xPt affineMap
  have h0 : Req (Rmul (ofQ (Qsub (canonB C) (⟨1, 1⟩ : Q)) (canonBm1_den C)) (ofQ (⟨((0 : Nat) : Int), σ.Nx + 1⟩ : Q) (Nat.succ_pos _)))
      (ofQ (⟨0, 1⟩ : Q) Nat.one_pos) := by
    refine Req_trans (Rmul_ofQ_ofQ (canonBm1_den C) (Nat.succ_pos _)) (ofQ_congr _ Nat.one_pos ?_)
    show (Qsub (canonB C) (⟨1, 1⟩ : Q)).num * ((0 : Nat) : Int) * ((1 : Nat) : Int)
        = 0 * (((Qsub (canonB C) (⟨1, 1⟩ : Q)).den * (σ.Nx + 1) : Nat) : Int)
    simp
  refine Req_trans (Radd_congr (Req_refl _) h0) ?_
  exact Req_trans (Radd_ofQ_ofQ (by decide) Nat.one_pos) (ofQ_congr _ (by decide) (by decide))

-- ===========================================================================
-- (2) Weights and coordinates.
-- ===========================================================================

/-- The nonnegative site weight: quadrature cell × external density. -/
def siteWeight (C : NormCtx) (σ : Stage) : Site → Real
  | .prime m side i => Rmul (ofQ (⟨1, σ.Nt + 1⟩ : Q) (Nat.succ_pos _)) (Rmul (ofQ C.w C.hw) (primeMeasure C m side (tPt C σ i)))
  | .pole j i => Rmul (Rmul (ofQ (Qsub (canonB C) (⟨1, 1⟩ : Q)) (canonBm1_den C)) (ofQ (⟨1, σ.Nx + 1⟩ : Q) (Nat.succ_pos _)))
      (Rmul (ofQ (⟨1, σ.Nt + 1⟩ : Q) (Nat.succ_pos _)) (poleDensity C (xPt C σ j) (tPt C σ i)))
  | .cst i => Rmul (ofQ (⟨1, σ.Nt + 1⟩ : Q) (Nat.succ_pos _)) (constDensity C (tPt C σ i))
  | .tail j i => Rmul (Rmul (ofQ (Qsub (canonB C) (⟨1, 1⟩ : Q)) (canonBm1_den C)) (ofQ (⟨1, σ.Nx + 1⟩ : Q) (Nat.succ_pos _)))
      (Rmul (ofQ (⟨1, σ.Nt + 1⟩ : Q) (Nat.succ_pos _)) (tailDensity C (tPt C σ i)))

theorem cellT_nonneg (σ : Stage) : Rnonneg (ofQ (⟨1, σ.Nt + 1⟩ : Q) (Nat.succ_pos _)) :=
  Rnonneg_ofQ _ (show (0 : Int) ≤ 1 by decide)
theorem cellX_nonneg (C : NormCtx) (σ : Stage) :
    Rnonneg (Rmul (ofQ (Qsub (canonB C) (⟨1, 1⟩ : Q)) (canonBm1_den C)) (ofQ (⟨1, σ.Nx + 1⟩ : Q) (Nat.succ_pos _))) :=
  Rnonneg_Rmul (Rnonneg_ofQ _ (canonBm1_num C)) (Rnonneg_ofQ _ (show (0 : Int) ≤ 1 by decide))

/-- **All site weights are nonnegative.** -/
theorem siteWeight_nonneg (C : NormCtx) (σ : Stage) : ∀ s, Rnonneg (siteWeight C σ s)
  | .prime m side i => Rnonneg_Rmul (cellT_nonneg σ) (Rnonneg_Rmul (Rnonneg_ofQ C.hw C.hwn) (primeMeasure_nonneg C m side _))
  | .pole j i => Rnonneg_Rmul (cellX_nonneg C σ) (Rnonneg_Rmul (cellT_nonneg σ) (poleDensity_nonneg C _ _))
  | .cst i => Rnonneg_Rmul (cellT_nonneg σ) (constDensity_nonneg C _)
  | .tail j i => Rnonneg_Rmul (cellX_nonneg C σ) (Rnonneg_Rmul (cellT_nonneg σ) (tailDensity_nonneg C _))

/-- The raw evaluation pair `(u, v)` of a test at a site (the fiber is `gammaAtom addr 1 u v`). -/
def siteU (C : NormCtx) (σ : Stage) (f : L2Test) : Site → Real
  | .prime m side i => uEv C (placeData C m side) f (tPt C σ i)
  | .pole j i => Uc C (xPt C σ j) f (tPt C σ i)
  | .cst i => Vc C f (tPt C σ i)
  | .tail j i => Zc C (dyQ σ.k) (dyQ_num σ.k) (dyQ_den σ.k) (xPt C σ j) f (tPt C σ i)
def siteV (C : NormCtx) (σ : Stage) (f : L2Test) : Site → Real
  | .prime m side i => vEv C f (tPt C σ i)
  | .pole j i => Rneg (Vc C f (tPt C σ i))
  | .cst i => Vc C f (tPt C σ i)
  | .tail j i => Wc C (xPt C σ j) f (tPt C σ i)

/-- The address gauge of a site (internal to the fiber; the tag is external). -/
def siteAddr : Site → Nat × Nat
  | .prime m _ _ => primeAddr m
  | _ => archAddr
theorem siteAddr_valid : ∀ s, (siteAddr s).1 < 3 ∧ (siteAddr s).2 < 8
  | .prime m _ _ => primeAddr_valid m
  | .pole _ _ => archAddr_valid
  | .cst _ => archAddr_valid
  | .tail _ _ => archAddr_valid

/-- **The site fiber** — the prime/pole/constant/tail fiber of `f` at the site. -/
def siteFiber (C : NormCtx) (σ : Stage) (f : L2Test) (s : Site) : Nat → Nat → Real :=
  gammaAtom (siteAddr s).1 (siteAddr s).2 one (siteU C σ f s) (siteV C σ f s)

theorem siteFiber_prime (C : NormCtx) (σ : Stage) (f : L2Test) (m side i : Nat) :
    siteFiber C σ f (.prime m side i) = primeField C m side f (tPt C σ i) := rfl
theorem siteFiber_pole (C : NormCtx) (σ : Stage) (f : L2Test) (j i : Nat) :
    siteFiber C σ f (.pole j i) = poleFiber C (xPt C σ j) f (tPt C σ i) := rfl
theorem siteFiber_cst (C : NormCtx) (σ : Stage) (f : L2Test) (i : Nat) :
    siteFiber C σ f (.cst i) = constFiber C f (tPt C σ i) := rfl
theorem siteFiber_tail (C : NormCtx) (σ : Stage) (f : L2Test) (j i : Nat) :
    siteFiber C σ f (.tail j i) = tailFiber C (dyQ σ.k) (dyQ_num σ.k) (dyQ_den σ.k) (xPt C σ j) f (tPt C σ i) := rfl

/-- **The CUT coordinate** `A = (u − v)/4` of the site fiber. -/
def cutStage (C : NormCtx) (σ : Stage) (f : L2Test) (s : Site) : Real := aCoefGa one (siteU C σ f s) (siteV C σ f s)
/-- **The CYCLE coordinate** `B = (u + v)/4` of the site fiber. -/
def cycleStage (C : NormCtx) (σ : Stage) (f : L2Test) (s : Site) : Real := bCoefGa one (siteU C σ f s) (siteV C σ f s)

/-- Pointwise: `⟨Φ_f, MΦ_g⟩ = 4A_fA_g − 4B_fB_g` at every site. -/
theorem siteFiber_split (C : NormCtx) (σ : Stage) (f g : L2Test) (s : Site) :
    Req (pairF (siteFiber C σ f s) (atlasOp (siteFiber C σ g s)))
        (Rsub (Rmul c4 (Rmul (cutStage C σ f s) (cutStage C σ g s)))
              (Rmul c4 (Rmul (cycleStage C σ f s) (cycleStage C σ g s)))) :=
  gamma_bilinear _ _ (siteAddr_valid s).1 (siteAddr_valid s).2 _ _ _ _

-- ===========================================================================
-- (3) Site sums, masses, the stage pairing.
-- ===========================================================================

/-- The finite sum over all sites of the stage. -/
def siteSum (C : NormCtx) (σ : Stage) (F : Site → Real) : Real :=
  Radd (RsumN (fun m => RsumN (fun side => RsumN (fun i => F (.prime m side i)) (σ.Nt + 1)) 2) C.X)
    (Radd (RsumN (fun j => RsumN (fun i => F (.pole j i)) (σ.Nt + 1)) (σ.Nx + 1))
      (Radd (RsumN (fun i => F (.cst i)) (σ.Nt + 1))
            (RsumN (fun j => RsumN (fun i => F (.tail j i)) (σ.Nt + 1)) (σ.Nx + 1))))

theorem siteSum_congr (C : NormCtx) (σ : Stage) {F G : Site → Real} (h : ∀ s, Req (F s) (G s)) :
    Req (siteSum C σ F) (siteSum C σ G) := by
  unfold siteSum
  refine Radd_congr (RsumN_congr _ (fun m _ => RsumN_congr _ (fun side _ => RsumN_congr _ (fun i _ => h _))))
    (Radd_congr (RsumN_congr _ (fun j _ => RsumN_congr _ (fun i _ => h _)))
      (Radd_congr (RsumN_congr _ (fun i _ => h _)) (RsumN_congr _ (fun j _ => RsumN_congr _ (fun i _ => h _)))))

theorem siteSum_sub (C : NormCtx) (σ : Stage) (F G : Site → Real) :
    Req (siteSum C σ (fun s => Rsub (F s) (G s))) (Rsub (siteSum C σ F) (siteSum C σ G)) := by
  unfold siteSum
  have hP : Req (RsumN (fun m => RsumN (fun side => RsumN (fun i => Rsub (F (.prime m side i)) (G (.prime m side i))) (σ.Nt + 1)) 2) C.X)
      (Rsub (RsumN (fun m => RsumN (fun side => RsumN (fun i => F (.prime m side i)) (σ.Nt + 1)) 2) C.X)
            (RsumN (fun m => RsumN (fun side => RsumN (fun i => G (.prime m side i)) (σ.Nt + 1)) 2) C.X)) := by
    refine Req_trans (RsumN_congr _ (fun m _ => Req_trans (RsumN_congr _ (fun side _ => RsumN_Rsub _ _ _)) (RsumN_Rsub _ _ _))) ?_
    exact RsumN_Rsub _ _ _
  have hO : Req (RsumN (fun j => RsumN (fun i => Rsub (F (.pole j i)) (G (.pole j i))) (σ.Nt + 1)) (σ.Nx + 1))
      (Rsub (RsumN (fun j => RsumN (fun i => F (.pole j i)) (σ.Nt + 1)) (σ.Nx + 1))
            (RsumN (fun j => RsumN (fun i => G (.pole j i)) (σ.Nt + 1)) (σ.Nx + 1))) :=
    Req_trans (RsumN_congr _ (fun j _ => RsumN_Rsub _ _ _)) (RsumN_Rsub _ _ _)
  have hC : Req (RsumN (fun i => Rsub (F (.cst i)) (G (.cst i))) (σ.Nt + 1))
      (Rsub (RsumN (fun i => F (.cst i)) (σ.Nt + 1)) (RsumN (fun i => G (.cst i)) (σ.Nt + 1))) := RsumN_Rsub _ _ _
  have hT : Req (RsumN (fun j => RsumN (fun i => Rsub (F (.tail j i)) (G (.tail j i))) (σ.Nt + 1)) (σ.Nx + 1))
      (Rsub (RsumN (fun j => RsumN (fun i => F (.tail j i)) (σ.Nt + 1)) (σ.Nx + 1))
            (RsumN (fun j => RsumN (fun i => G (.tail j i)) (σ.Nt + 1)) (σ.Nx + 1))) :=
    Req_trans (RsumN_congr _ (fun j _ => RsumN_Rsub _ _ _)) (RsumN_Rsub _ _ _)
  refine Req_trans (Radd_congr hP (Radd_congr hO (Radd_congr hC hT))) ?_
  refine Req_trans (Radd_congr (Req_refl _) (Radd_congr (Req_refl _) (Req_symm (Rsub_Radd_Radd _ _ _ _)))) ?_
  refine Req_trans (Radd_congr (Req_refl _) (Req_symm (Rsub_Radd_Radd _ _ _ _))) ?_
  exact Req_symm (Rsub_Radd_Radd _ _ _ _)

theorem siteSum_nonneg (C : NormCtx) (σ : Stage) {F : Site → Real} (h : ∀ s, Rnonneg (F s)) :
    Rnonneg (siteSum C σ F) := by
  unfold siteSum
  refine Rnonneg_Radd (Rnonneg_RsumN _ (fun m _ => Rnonneg_RsumN _ (fun side _ => Rnonneg_RsumN _ (fun i _ => h _))))
    (Rnonneg_Radd (Rnonneg_RsumN _ (fun j _ => Rnonneg_RsumN _ (fun i _ => h _)))
      (Rnonneg_Radd (Rnonneg_RsumN _ (fun i _ => h _)) (Rnonneg_RsumN _ (fun j _ => Rnonneg_RsumN _ (fun i _ => h _)))))

/-- The weighted cut mass of a cut-carrier vector `c`: `Σ_s weight(s)·4·c(s)²`. -/
def cutMass (C : NormCtx) (σ : Stage) (c : Site → Real) : Real :=
  siteSum C σ (fun s => Rmul (siteWeight C σ s) (Rmul c4 (Rmul (c s) (c s))))
/-- The weighted cycle mass of a cycle-carrier vector. -/
def cycleMass (C : NormCtx) (σ : Stage) (c : Site → Real) : Real :=
  siteSum C σ (fun s => Rmul (siteWeight C σ s) (Rmul c4 (Rmul (c s) (c s))))

/-- **The stage pairing** `Σ_s weight(s)·⟨Φ_f(s), MΦ_g(s)⟩` — the finite quadrature of the mixed direct integral. -/
def stagePair (C : NormCtx) (σ : Stage) (f g : L2Test) : Real :=
  siteSum C σ (fun s => Rmul (siteWeight C σ s) (pairF (siteFiber C σ f s) (atlasOp (siteFiber C σ g s))))
def cutPair (C : NormCtx) (σ : Stage) (f g : L2Test) : Real :=
  siteSum C σ (fun s => Rmul (siteWeight C σ s) (Rmul c4 (Rmul (cutStage C σ f s) (cutStage C σ g s))))
def cyclePair (C : NormCtx) (σ : Stage) (f g : L2Test) : Real :=
  siteSum C σ (fun s => Rmul (siteWeight C σ s) (Rmul c4 (Rmul (cycleStage C σ f s) (cycleStage C σ g s))))

/-- **`stagePair = cutPair − cyclePair`** at every stage. -/
theorem stagePair_split (C : NormCtx) (σ : Stage) (f g : L2Test) :
    Req (stagePair C σ f g) (Rsub (cutPair C σ f g) (cyclePair C σ f g)) := by
  unfold stagePair cutPair cyclePair
  refine Req_trans (siteSum_congr C σ (fun s => Req_trans (Rmul_congr (Req_refl _) (siteFiber_split C σ f g s))
    (Rmul_sub_distrib _ _ _))) ?_
  exact siteSum_sub C σ _ _

theorem cutPair_diag_eq_mass (C : NormCtx) (σ : Stage) (f : L2Test) :
    cutPair C σ f f = cutMass C σ (cutStage C σ f) := rfl
theorem cyclePair_diag_eq_mass (C : NormCtx) (σ : Stage) (f : L2Test) :
    cyclePair C σ f f = cycleMass C σ (cycleStage C σ f) := rfl

/-- Weighted masses are nonnegative. -/
theorem cutMass_nonneg (C : NormCtx) (σ : Stage) (c : Site → Real) : Rnonneg (cutMass C σ c) :=
  siteSum_nonneg C σ (fun s => Rnonneg_Rmul (siteWeight_nonneg C σ s)
    (Rnonneg_Rmul (Rnonneg_ofQ Nat.one_pos (by decide)) (Rnonneg_Rmul_self _)))
theorem cycleMass_nonneg (C : NormCtx) (σ : Stage) (c : Site → Real) : Rnonneg (cycleMass C σ c) :=
  cutMass_nonneg C σ c

-- ===========================================================================
-- (4) ★ THE TRANSFER GATE: the explicit transfer, the factorization, the kernel condition.
-- ===========================================================================

/-- **The transfer** `CutCarrier → CycleCarrier`: every cycle coordinate is its own cut coordinate plus a
    multiple of the `x = 1` pole column `c(pole 0 i)`. -/
def atlasTransferStage (C : NormCtx) (σ : Stage) (c : Site → Real) : Site → Real
  | .prime m side i => Radd (c (.prime m side i)) (c (.pole 0 i))
  | .pole j i => Rsub (c (.pole j i)) (c (.pole 0 i))
  | .cst i => c (.pole 0 i)
  | .tail j i => Radd (c (.tail j i)) (Rmul (rOne (xPt C σ j)) (c (.pole 0 i)))

/-- `B = A + ½v` for `gammaAtom 1 u v`. -/
theorem b_eq_a_add_half (u v : Real) : Req (bCoefGa one u v) (Radd (aCoefGa one u v) (Rmul cH v)) := by
  unfold aCoefGa bCoefGa
  -- ¼(u' + v) ≈ ¼(u' − v) + ½v  (u' = 1·u)
  have h : Req (Radd (Rmul one u) v) (Radd (Rsub (Rmul one u) v) (Rmul cTwo v)) := by
    refine Req_symm ?_
    refine Req_trans (Radd_congr (Req_refl _) (cTwo_mul v)) ?_
    show Req (Radd (Radd (Rmul one u) (Rneg v)) (Radd v v)) (Radd (Rmul one u) v)
    refine Req_trans (Radd_assoc _ _ _) (Radd_congr (Req_refl _) ?_)
    refine Req_trans (Req_symm (Radd_assoc _ _ _)) ?_
    exact Req_trans (Radd_congr (Req_trans (Radd_comm _ _) (Radd_neg v)) (Req_refl v)) (Req_trans (Radd_comm _ _) (Radd_zero v))
  refine Req_trans (Rmul_congr (Req_refl cQ) h) ?_
  refine Req_trans (Rmul_distrib _ _ _) (Radd_congr (Req_refl _) ?_)
  refine Req_trans (Req_symm (Rmul_assoc cQ cTwo v)) (Rmul_congr ?_ (Req_refl v))
  exact Req_trans (Rmul_ofQ_ofQ (by decide) Nat.one_pos) (ofQ_congr _ (by decide) (by decide))

/-- `B = A − ½v` for `gammaAtom 1 u (−v)` (the pole fiber). -/
theorem b_eq_a_sub_half (u v : Real) : Req (bCoefGa one u (Rneg v)) (Rsub (aCoefGa one u (Rneg v)) (Rmul cH v)) := by
  refine Req_trans (b_eq_a_add_half u (Rneg v)) ?_
  exact Radd_congr (Req_refl _) (Rmul_neg_right cH v)

/-- **The `x = 1` pole site's cut coordinate is `½·V`** (`U_1 = V`). -/
theorem cut_pole_zero (C : NormCtx) (σ : Stage) (f : L2Test) (i : Nat) :
    Req (cutStage C σ f (.pole 0 i)) (Rmul cH (Vc C f (tPt C σ i))) := by
  unfold cutStage siteU siteV aCoefGa
  have hU : Req (Uc C (xPt C σ 0) f (tPt C σ i)) (Vc C f (tPt C σ i)) :=
    Req_trans (Uc_congr_x C (xPt_zero C σ) f _) (Uc_one_eq_Vc C f _)
  -- ¼(1·U − (−V)) ≈ ¼(V + V) ≈ ½V
  refine Req_trans (Rmul_congr (Req_refl cQ) (Rsub_congr (Req_trans (Rone_mul _) hU) (Req_refl _))) ?_
  show Req (Rmul cQ (Radd (Vc C f (tPt C σ i)) (Rneg (Rneg (Vc C f (tPt C σ i)))))) _
  refine Req_trans (Rmul_congr (Req_refl cQ) (Radd_congr (Req_refl _) (Rneg_neg _))) ?_
  refine Req_trans (Rmul_congr (Req_refl cQ) (Req_symm (cTwo_mul _))) ?_
  refine Req_trans (Req_symm (Rmul_assoc cQ cTwo _)) (Rmul_congr ?_ (Req_refl _))
  exact Req_trans (Rmul_ofQ_ofQ (by decide) Nat.one_pos) (ofQ_congr _ (by decide) (by decide))

/-- **★ THE FACTORIZATION** `cycleStage σ f = atlasTransferStage σ (cutStage σ f)` for EVERY test and site. -/
theorem mixedCycleStage_factor (C : NormCtx) (σ : Stage) (f : L2Test) :
    ∀ s, Req (cycleStage C σ f s) (atlasTransferStage C σ (cutStage C σ f) s)
  | .prime m side i => by
      show Req (bCoefGa one (uEv C (placeData C m side) f (tPt C σ i)) (vEv C f (tPt C σ i)))
               (Radd (cutStage C σ f (.prime m side i)) (cutStage C σ f (.pole 0 i)))
      refine Req_trans (b_eq_a_add_half _ _) (Radd_congr (Req_refl _) ?_)
      exact Req_symm (cut_pole_zero C σ f i)
  | .pole j i => by
      show Req (bCoefGa one (Uc C (xPt C σ j) f (tPt C σ i)) (Rneg (Vc C f (tPt C σ i))))
               (Rsub (cutStage C σ f (.pole j i)) (cutStage C σ f (.pole 0 i)))
      refine Req_trans (b_eq_a_sub_half _ _) (Rsub_congr (Req_refl _) ?_)
      exact Req_symm (cut_pole_zero C σ f i)
  | .cst i => by
      show Req (bCoefGa one (Vc C f (tPt C σ i)) (Vc C f (tPt C σ i))) (cutStage C σ f (.pole 0 i))
      refine Req_trans ?_ (Req_symm (cut_pole_zero C σ f i))
      unfold bCoefGa
      refine Req_trans (Rmul_congr (Req_refl cQ) (Radd_congr (Rone_mul _) (Req_refl _))) ?_
      refine Req_trans (Rmul_congr (Req_refl cQ) (Req_symm (cTwo_mul _))) ?_
      refine Req_trans (Req_symm (Rmul_assoc cQ cTwo _)) (Rmul_congr ?_ (Req_refl _))
      exact Req_trans (Rmul_ofQ_ofQ (by decide) Nat.one_pos) (ofQ_congr _ (by decide) (by decide))
  | .tail j i => by
      show Req (bCoefGa one (Zc C (dyQ σ.k) (dyQ_num σ.k) (dyQ_den σ.k) (xPt C σ j) f (tPt C σ i)) (Wc C (xPt C σ j) f (tPt C σ i)))
               (Radd (cutStage C σ f (.tail j i)) (Rmul (rOne (xPt C σ j)) (cutStage C σ f (.pole 0 i))))
      refine Req_trans (b_eq_a_add_half _ _) (Radd_congr (Req_refl _) ?_)
      -- ½·(rOne·V) ≈ rOne·(½V)
      unfold Wc
      refine Req_trans (Req_symm (Rmul_assoc cH _ _)) ?_
      refine Req_trans (Rmul_congr (Rmul_comm cH _) (Req_refl _)) (Req_trans (Rmul_assoc _ _ _) ?_)
      exact Rmul_congr (Req_refl _) (Req_symm (cut_pole_zero C σ f i))

/-- The transfer of the zero vector is zero. -/
theorem atlasTransferStage_zero (C : NormCtx) (σ : Stage) {c : Site → Real} (h : ∀ s, Req (c s) zero) :
    ∀ s, Req (atlasTransferStage C σ c s) zero
  | .prime m side i => Req_trans (Radd_congr (h _) (h _)) (Radd_zero zero)
  | .pole j i => Req_trans (Rsub_congr (h _) (h _)) (Radd_neg zero)
  | .cst i => h _
  | .tail j i => Req_trans (Radd_congr (h _) (Req_trans (Rmul_congr (Req_refl _) (h _)) (Rmul_zero _))) (Radd_zero zero)

/-- **★ THE NECESSARY KERNEL CONDITION**: `cutStage σ f = 0 → cycleStage σ f = 0`. -/
theorem atlasTransfer_kernel (C : NormCtx) (σ : Stage) (f : L2Test)
    (h : ∀ s, Req (cutStage C σ f s) zero) : ∀ s, Req (cycleStage C σ f s) zero :=
  fun s => Req_trans (mixedCycleStage_factor C σ f s) (atlasTransferStage_zero C σ h s)

/-- The transfer is additive (a linear map of carriers). -/
theorem atlasTransferStage_add (C : NormCtx) (σ : Stage) (c c' : Site → Real) :
    ∀ s, Req (atlasTransferStage C σ (fun s => Radd (c s) (c' s)) s)
             (Radd (atlasTransferStage C σ c s) (atlasTransferStage C σ c' s))
  | .prime m side i => Radd_swap _ _ _ _
  | .pole j i => Rsub_Radd_Radd _ _ _ _
  | .cst i => Req_refl _
  | .tail j i => Req_trans (Radd_congr (Req_refl _) (Rmul_distrib _ _ _)) (Radd_swap _ _ _ _)

-- ===========================================================================
-- (5) ★ THE CONTRACTION TEST on the full carrier: the `x = 1` pole pulse.
-- ===========================================================================

/-- The pulse `α` at the single site `pole 0 i₀`. -/
def polePulse (i₀ : Nat) (α : Real) : Site → Real
  | .pole 0 i => if i = i₀ then α else zero
  | _ => zero

theorem polePulse_prime (i₀ : Nat) (α : Real) (m side i : Nat) : polePulse i₀ α (.prime m side i) = zero := rfl
theorem polePulse_cst (i₀ : Nat) (α : Real) (i : Nat) : polePulse i₀ α (.cst i) = zero := rfl
theorem polePulse_tail (i₀ : Nat) (α : Real) (j i : Nat) : polePulse i₀ α (.tail j i) = zero := rfl
theorem polePulse_pole_succ (i₀ : Nat) (α : Real) (j i : Nat) : polePulse i₀ α (.pole (j + 1) i) = zero := rfl
theorem polePulse_pole_zero (i₀ : Nat) (α : Real) (i : Nat) : polePulse i₀ α (.pole 0 i) = (if i = i₀ then α else zero) := rfl

/-- `w·(4·(0·0)) ≈ 0`. -/
theorem mass_zero_term (w : Real) : Req (Rmul w (Rmul c4 (Rmul zero zero))) zero :=
  Req_trans (Rmul_congr (Req_refl w) (Req_trans (Rmul_congr (Req_refl c4) (Rmul_zero zero)) (Rmul_zero c4))) (Rmul_zero w)

theorem RsumN_zero_terms {F : Nat → Real} (n : Nat) (h : ∀ i, i < n → Req (F i) zero) : Req (RsumN F n) zero :=
  Req_trans (RsumN_congr n h) (Req_trans (RsumN_const zero n) (Rmul_zero _))

/-- The pointwise indicator mass term. -/
theorem indicator_term (wi α : Real) (i i₀ : Nat) :
    Req (Rmul wi (Rmul c4 (Rmul (if i = i₀ then α else zero) (if i = i₀ then α else zero))))
        (if i = i₀ then Rmul wi (Rmul c4 (Rmul α α)) else zero) := by
  split
  · exact Req_refl _
  · exact mass_zero_term _

/-- The mass of an `i`-indicator family: `Σ_i w_i·4·([i = i₀]α)² = w_{i₀}·4α²`. -/
theorem indicator_mass (w : Nat → Real) (i₀ : Nat) (α : Real) (n : Nat) (hi : i₀ < n) :
    Req (RsumN (fun i => Rmul (w i) (Rmul c4 (Rmul (if i = i₀ then α else zero) (if i = i₀ then α else zero)))) n)
        (Rmul (w i₀) (Rmul c4 (Rmul α α))) :=
  Req_trans (RsumN_congr (G := fun i => if i = i₀ then Rmul (w i) (Rmul c4 (Rmul α α)) else zero) n
      (fun i _ => indicator_term (w i) α i i₀))
    (RsumN_indicator_ai (fun i => Rmul (w i) (Rmul c4 (Rmul α α))) i₀ n hi)

/-- **`cutMass σ (pulse) = weight(pole 0 i₀)·4α²`** (`i₀ ≤ Nt`). -/
theorem cutMass_polePulse (C : NormCtx) (σ : Stage) (i₀ : Nat) (hi : i₀ < σ.Nt + 1) (α : Real) :
    Req (cutMass C σ (polePulse i₀ α)) (Rmul (siteWeight C σ (.pole 0 i₀)) (Rmul c4 (Rmul α α))) := by
  unfold cutMass siteSum
  have hP : Req (RsumN (fun m => RsumN (fun side => RsumN (fun i =>
      Rmul (siteWeight C σ (.prime m side i)) (Rmul c4 (Rmul (polePulse i₀ α (.prime m side i)) (polePulse i₀ α (.prime m side i))))) (σ.Nt + 1)) 2) C.X) zero :=
    RsumN_zero_terms _ (fun m _ => RsumN_zero_terms _ (fun side _ => RsumN_zero_terms _ (fun i _ => by
      rw [polePulse_prime]; exact mass_zero_term _)))
  have hC : Req (RsumN (fun i => Rmul (siteWeight C σ (.cst i)) (Rmul c4 (Rmul (polePulse i₀ α (.cst i)) (polePulse i₀ α (.cst i))))) (σ.Nt + 1)) zero :=
    RsumN_zero_terms _ (fun i _ => by rw [polePulse_cst]; exact mass_zero_term _)
  have hT : Req (RsumN (fun j => RsumN (fun i => Rmul (siteWeight C σ (.tail j i)) (Rmul c4 (Rmul (polePulse i₀ α (.tail j i)) (polePulse i₀ α (.tail j i))))) (σ.Nt + 1)) (σ.Nx + 1)) zero :=
    RsumN_zero_terms _ (fun j _ => RsumN_zero_terms _ (fun i _ => by rw [polePulse_tail]; exact mass_zero_term _))
  have hO : Req (RsumN (fun j => RsumN (fun i => Rmul (siteWeight C σ (.pole j i)) (Rmul c4 (Rmul (polePulse i₀ α (.pole j i)) (polePulse i₀ α (.pole j i))))) (σ.Nt + 1)) (σ.Nx + 1))
      (Rmul (siteWeight C σ (.pole 0 i₀)) (Rmul c4 (Rmul α α))) := by
    refine Req_trans (RsumN_congr (G := fun j => if j = 0 then Rmul (siteWeight C σ (.pole 0 i₀)) (Rmul c4 (Rmul α α)) else zero)
      (σ.Nx + 1) (fun j _ => ?_)) (RsumN_indicator_ai _ 0 (σ.Nx + 1) (Nat.succ_pos _))
    cases j with
    | zero =>
        show Req _ (if (0 : Nat) = 0 then Rmul (siteWeight C σ (.pole 0 i₀)) (Rmul c4 (Rmul α α)) else zero)
        rw [if_pos rfl]
        exact indicator_mass (fun i => siteWeight C σ (.pole 0 i)) i₀ α (σ.Nt + 1) hi
    | succ j =>
        show Req _ (if j + 1 = 0 then Rmul (siteWeight C σ (.pole 0 i₀)) (Rmul c4 (Rmul α α)) else zero)
        rw [if_neg (Nat.succ_ne_zero j)]
        exact RsumN_zero_terms _ (fun i _ => by rw [polePulse_pole_succ]; exact mass_zero_term _)
  refine Req_trans (Radd_congr hP (Radd_congr hO (Radd_congr hC hT))) ?_
  refine Req_trans (Radd_congr (Req_refl _) (Radd_congr (Req_refl _) (Radd_zero zero))) ?_
  refine Req_trans (Radd_congr (Req_refl _) (Radd_zero _)) ?_
  exact Req_trans (Radd_comm _ _) (Radd_zero _)

theorem Rle_add_nonneg_left {x y : Real} (hy : Rnonneg y) : Rle x (Radd y x) := by
  refine Rle_of_Rnonneg_Rsub (Rnonneg_congr ?_ hy)
  show Req y (Radd (Radd y x) (Rneg x))
  exact Req_symm (Req_trans (Radd_assoc y x (Rneg x)) (Req_trans (Radd_congr (Req_refl y) (Radd_neg x)) (Radd_zero y)))
theorem Rle_add_nonneg_right {x y : Real} (hy : Rnonneg y) : Rle x (Radd x y) :=
  Rle_trans (Rle_add_nonneg_left hy) (Rle_of_Req (Radd_comm y x))

/-- **The constant-site slice of `cycleMass σ (K pulse)` is `weight(cst i₀)·4α²`, and it bounds the mass below.** -/
theorem cycleMass_transfer_pulse_ge (C : NormCtx) (σ : Stage) (i₀ : Nat) (hi : i₀ < σ.Nt + 1) (α : Real) :
    Rle (Rmul (siteWeight C σ (.cst i₀)) (Rmul c4 (Rmul α α)))
        (cycleMass C σ (atlasTransferStage C σ (polePulse i₀ α))) := by
  unfold cycleMass siteSum
  have hCeq : Req (RsumN (fun i => Rmul (siteWeight C σ (.cst i)) (Rmul c4 (Rmul (atlasTransferStage C σ (polePulse i₀ α) (.cst i))
      (atlasTransferStage C σ (polePulse i₀ α) (.cst i))))) (σ.Nt + 1))
      (Rmul (siteWeight C σ (.cst i₀)) (Rmul c4 (Rmul α α))) := by
    refine Req_trans (RsumN_congr (G := fun i => Rmul (siteWeight C σ (.cst i)) (Rmul c4 (Rmul (if i = i₀ then α else zero) (if i = i₀ then α else zero))))
      (σ.Nt + 1) (fun i _ => ?_)) (indicator_mass _ i₀ α _ hi)
    show Req (Rmul (siteWeight C σ (.cst i)) (Rmul c4 (Rmul (polePulse i₀ α (.pole 0 i)) (polePulse i₀ α (.pole 0 i))))) _
    rw [polePulse_pole_zero]; exact Req_refl _
  have hnn : ∀ s, Rnonneg (Rmul (siteWeight C σ s) (Rmul c4 (Rmul (atlasTransferStage C σ (polePulse i₀ α) s)
      (atlasTransferStage C σ (polePulse i₀ α) s)))) :=
    fun s => Rnonneg_Rmul (siteWeight_nonneg C σ s) (Rnonneg_Rmul (Rnonneg_ofQ Nat.one_pos (by decide)) (Rnonneg_Rmul_self _))
  refine Rle_trans (Rle_of_Req (Req_symm hCeq)) ?_
  refine Rle_trans (Rle_add_nonneg_right (Rnonneg_RsumN (σ.Nx + 1) (fun j _ => Rnonneg_RsumN (σ.Nt + 1) (fun i _ => hnn (.tail j i))))) ?_
  refine Rle_trans (Rle_add_nonneg_left (Rnonneg_RsumN (σ.Nx + 1) (fun j _ => Rnonneg_RsumN (σ.Nt + 1) (fun i _ => hnn (.pole j i))))) ?_
  exact Rle_add_nonneg_left (Rnonneg_RsumN C.X (fun m _ => Rnonneg_RsumN 2 (fun side _ => Rnonneg_RsumN (σ.Nt + 1) (fun i _ => hnn (.prime m side i)))))

/-- `cX·(cT·(P·WR)) ≈ cT·((P·cX)·WR)`. -/
theorem pole_w_rearr (cX cT P WR : Real) :
    Req (Rmul cX (Rmul cT (Rmul P WR))) (Rmul cT (Rmul (Rmul P cX) WR)) := by
  refine Req_trans (Req_symm (Rmul_assoc cX cT _)) ?_
  refine Req_trans (Rmul_congr (Rmul_comm cX cT) (Req_refl _)) (Req_trans (Rmul_assoc cT cX _) (Rmul_congr (Req_refl cT) ?_))
  refine Req_trans (Req_symm (Rmul_assoc cX P WR)) (Rmul_congr (Rmul_comm cX P) (Req_refl WR))

/-- `weight(pole 0 i₀) ≤ weight(cst i₀)` once `4(B−1)/(Nx+1) ≤ 2.53038 ≤ log 4π` (fine scale quadrature). -/
theorem poleWeight_le_cstWeight (C : NormCtx) (σ : Stage) (i₀ : Nat)
    (hNx : Qle (mul (⟨4, 1⟩ : Q) (mul (Qsub (canonB C) (⟨1, 1⟩ : Q)) (⟨1, σ.Nx + 1⟩ : Q))) (⟨253038, 100000⟩ : Q)) :
    Rle (siteWeight C σ (.pole 0 i₀)) (siteWeight C σ (.cst i₀)) := by
  show Rle (Rmul (Rmul (ofQ (Qsub (canonB C) (⟨1, 1⟩ : Q)) (canonBm1_den C)) (ofQ (⟨1, σ.Nx + 1⟩ : Q) (Nat.succ_pos _)))
              (Rmul (ofQ (⟨1, σ.Nt + 1⟩ : Q) (Nat.succ_pos _)) (poleDensity C (xPt C σ 0) (tPt C σ i₀))))
           (Rmul (ofQ (⟨1, σ.Nt + 1⟩ : Q) (Nat.succ_pos _)) (constDensity C (tPt C σ i₀)))
  unfold poleDensity constDensity
  -- the pole factor `2·(1 + 1/max(x_0,1)) ≈ 4`
  have h4 : Req (Rmul cTwo (Radd one (rOne (xPt C σ 0)))) (ofQ (⟨4, 1⟩ : Q) Nat.one_pos) := by
    have hr : Req (rOne (xPt C σ 0)) one :=
      Req_trans (clampedInv_congr _ _ _ (xPt_zero C σ)) rOne_one
    refine Req_trans (Rmul_congr (Req_refl cTwo) (Req_trans (Radd_congr (Req_refl one) hr) (Radd_ofQ_ofQ (by decide) (by decide)))) ?_
    exact Req_trans (Rmul_ofQ_ofQ Nat.one_pos Nat.one_pos) (ofQ_congr _ Nat.one_pos (by decide))
  -- rearrange the pole weight to `cellT · ((P·cellX)·(w r))`, then `P ≈ 4`
  refine Rle_trans (Rle_of_Req (pole_w_rearr _ _ _ _)) ?_
  refine Rle_trans (Rle_of_Req (Rmul_congr (Req_refl _) (Rmul_congr (Rmul_congr h4 (Req_refl _)) (Req_refl _)))) ?_
  refine Rmul_le_Rmul_left (Rnonneg_ofQ _ (show (0 : Int) ≤ 1 by decide)) ?_
  refine Rmul_le_Rmul_right (Rnonneg_Rmul (Rnonneg_ofQ C.hw C.hwn) (Rnonneg_clampedInv C.a C.han C.had _)) ?_
  -- 4·cX = ofQ(4·((B−1)/(Nx+1))) ≤ 2.53038 ≤ log 4π ≤ log 4π + γ
  have hq : Req (Rmul (ofQ (⟨4, 1⟩ : Q) Nat.one_pos)
      (Rmul (ofQ (Qsub (canonB C) (⟨1, 1⟩ : Q)) (canonBm1_den C)) (ofQ (⟨1, σ.Nx + 1⟩ : Q) (Nat.succ_pos _))))
      (ofQ (mul (⟨4, 1⟩ : Q) (mul (Qsub (canonB C) (⟨1, 1⟩ : Q)) (⟨1, σ.Nx + 1⟩ : Q)))
        (Qmul_den_pos Nat.one_pos (Qmul_den_pos (canonBm1_den C) (Nat.succ_pos _)))) :=
    Req_trans (Rmul_congr (Req_refl _) (Rmul_ofQ_ofQ _ _)) (Rmul_ofQ_ofQ _ _)
  refine Rle_trans (Rle_of_Req hq) ?_
  refine Rle_trans (Rle_ofQ_ofQ _ (by decide) hNx) ?_
  refine Rle_trans Rlog4pic_ge ?_
  exact Rle_add_nonneg_right Rgamma_h_nonneg

/-- **The weak reverse mass bound for the `x = 1` pole pulse** (any `α`, any fine enough scale quadrature):
    `cutMass σ c₀ ≤ cycleMass σ (K c₀)`.  This is NOT `¬ Contractive`; the pulse is outside `range cutStage`,
    so it falsifies only this endpoint-copying extension off the range.  The generic statement is `shear_no_go`. -/
theorem atlasTransferStage_not_contract (C : NormCtx) (σ : Stage) (i₀ : Nat) (hi : i₀ < σ.Nt + 1) (α : Real)
    (hNx : Qle (mul (⟨4, 1⟩ : Q) (mul (Qsub (canonB C) (⟨1, 1⟩ : Q)) (⟨1, σ.Nx + 1⟩ : Q))) (⟨253038, 100000⟩ : Q)) :
    Rle (cutMass C σ (polePulse i₀ α)) (cycleMass C σ (atlasTransferStage C σ (polePulse i₀ α))) := by
  refine Rle_trans (Rle_of_Req (cutMass_polePulse C σ i₀ hi α)) ?_
  refine Rle_trans (Rmul_le_Rmul_right (Rnonneg_Rmul (Rnonneg_ofQ Nat.one_pos (by decide)) (Rnonneg_Rmul_self α))
    (poleWeight_le_cstWeight C σ i₀ hNx)) ?_
  exact cycleMass_transfer_pulse_ge C σ i₀ hi α

-- ===========================================================================
-- (6) ★ THE GENERIC SHEAR NO-GO.
-- ===========================================================================

/-- A term of a nonnegative family is at most the whole sum. -/
theorem Rle_term_RsumN {F : Nat → Real} (hF : ∀ i, Rnonneg (F i)) (k : Nat) :
    ∀ n, k < n → Rle (F k) (RsumN F n)
  | 0, h => absurd h (Nat.not_lt_zero k)
  | (n + 1), h => by
      rw [RsumN_succ_fl]
      rcases Nat.lt_or_ge k n with hk | hk
      · exact Rle_trans (Rle_term_RsumN hF k n hk) (Rle_add_nonneg_right (hF n))
      · have hkn : k = n := by omega
        rw [hkn]
        exact Rle_add_nonneg_left (Rnonneg_RsumN n (fun i _ => hF i))

/-- The prime-site term of a nonnegative site family is at most the site sum. -/
theorem Rle_prime_term_siteSum (C : NormCtx) (σ : Stage) {F : Site → Real} (hF : ∀ s, Rnonneg (F s))
    (m₀ side₀ i₀ : Nat) (hm : m₀ < C.X) (hs : side₀ < 2) (hi : i₀ < σ.Nt + 1) :
    Rle (F (.prime m₀ side₀ i₀)) (siteSum C σ F) := by
  unfold siteSum
  refine Rle_trans ?_ (Rle_add_nonneg_right (Rnonneg_Radd (Rnonneg_RsumN _ (fun j _ => Rnonneg_RsumN _ (fun i _ => hF (.pole j i))))
    (Rnonneg_Radd (Rnonneg_RsumN _ (fun i _ => hF (.cst i))) (Rnonneg_RsumN _ (fun j _ => Rnonneg_RsumN _ (fun i _ => hF (.tail j i)))))))
  refine Rle_trans (Rle_term_RsumN (fun i => hF (.prime m₀ side₀ i)) i₀ (σ.Nt + 1) hi) ?_
  refine Rle_trans (Rle_term_RsumN (F := fun side => RsumN (fun i => F (.prime m₀ side i)) (σ.Nt + 1))
    (fun side => Rnonneg_RsumN _ (fun i _ => hF _)) side₀ 2 hs) ?_
  exact Rle_term_RsumN (F := fun m => RsumN (fun side => RsumN (fun i => F (.prime m side i)) (σ.Nt + 1)) 2)
    (fun m => Rnonneg_RsumN _ (fun side _ => Rnonneg_RsumN _ (fun i _ => hF _))) m₀ C.X hm

/-- The unit cut vector at the prime site `(m₀, side₀, i₀)`. -/
def primeUnit (m₀ side₀ i₀ : Nat) : Site → Real
  | .prime m side i => if m = m₀ then (if side = side₀ then (if i = i₀ then one else zero) else zero) else zero
  | _ => zero

theorem primeUnit_self (m₀ side₀ i₀ : Nat) : primeUnit m₀ side₀ i₀ (.prime m₀ side₀ i₀) = one := by
  show (if m₀ = m₀ then (if side₀ = side₀ then (if i₀ = i₀ then one else zero) else zero) else zero) = one
  rw [if_pos rfl, if_pos rfl, if_pos rfl]
theorem primeUnit_pole (m₀ side₀ i₀ j i : Nat) : primeUnit m₀ side₀ i₀ (.pole j i) = zero := rfl
theorem primeUnit_cst (m₀ side₀ i₀ i : Nat) : primeUnit m₀ side₀ i₀ (.cst i) = zero := rfl
theorem primeUnit_tail (m₀ side₀ i₀ j i : Nat) : primeUnit m₀ side₀ i₀ (.tail j i) = zero := rfl

/-- `Σ_i G i·[i = i₀]` over a nested triple indicator collapses to the `(m₀, side₀, i₀)` term. -/
theorem ind3_sum (G : Nat → Nat → Nat → Real) (m₀ side₀ i₀ X n : Nat) (hm : m₀ < X) (hs : side₀ < 2) (hi : i₀ < n) :
    Req (RsumN (fun m => RsumN (fun side => RsumN (fun i =>
          if m = m₀ then (if side = side₀ then (if i = i₀ then G m side i else zero) else zero) else zero) n) 2) X)
        (G m₀ side₀ i₀) := by
  refine Req_trans (RsumN_congr (G := fun m => if m = m₀ then G m side₀ i₀ else zero) X (fun m _ => ?_))
    (RsumN_indicator_ai (fun m => G m side₀ i₀) m₀ X hm)
  show Req (RsumN (fun side => RsumN (fun i =>
      if m = m₀ then (if side = side₀ then (if i = i₀ then G m side i else zero) else zero) else zero) n) 2)
    (if m = m₀ then G m side₀ i₀ else zero)
  by_cases hmm : m = m₀
  · rw [if_pos hmm]
    refine Req_trans (RsumN_congr (G := fun side => if side = side₀ then G m side i₀ else zero) 2 (fun side _ => ?_))
      (RsumN_indicator_ai (fun side => G m side i₀) side₀ 2 hs)
    show Req (RsumN (fun i => if m = m₀ then (if side = side₀ then (if i = i₀ then G m side i else zero) else zero) else zero) n)
      (if side = side₀ then G m side i₀ else zero)
    by_cases hss : side = side₀
    · rw [if_pos hss]
      refine Req_trans (RsumN_congr (G := fun i => if i = i₀ then G m side i else zero) n (fun i _ => ?_))
        (RsumN_indicator_ai (G m side) i₀ n hi)
      show Req (if m = m₀ then (if side = side₀ then (if i = i₀ then G m side i else zero) else zero) else zero)
        (if i = i₀ then G m side i else zero)
      rw [if_pos hmm, if_pos hss]; exact Req_refl _
    · rw [if_neg hss]
      refine RsumN_zero_terms n (fun i _ => ?_)
      show Req (if m = m₀ then (if side = side₀ then (if i = i₀ then G m side i else zero) else zero) else zero) zero
      rw [if_pos hmm, if_neg hss]; exact Req_refl _
  · rw [if_neg hmm]
    refine RsumN_zero_terms 2 (fun side _ => RsumN_zero_terms n (fun i _ => ?_))
    show Req (if m = m₀ then (if side = side₀ then (if i = i₀ then G m side i else zero) else zero) else zero) zero
    rw [if_neg hmm]; exact Req_refl _

/-- The prime-part of the site sum, and the rest. -/
def primePart (C : NormCtx) (σ : Stage) (F : Site → Real) : Real :=
  RsumN (fun m => RsumN (fun side => RsumN (fun i => F (.prime m side i)) (σ.Nt + 1)) 2) C.X
def restPart (C : NormCtx) (σ : Stage) (F : Site → Real) : Real :=
  Radd (RsumN (fun j => RsumN (fun i => F (.pole j i)) (σ.Nt + 1)) (σ.Nx + 1))
    (Radd (RsumN (fun i => F (.cst i)) (σ.Nt + 1))
          (RsumN (fun j => RsumN (fun i => F (.tail j i)) (σ.Nt + 1)) (σ.Nx + 1)))
theorem siteSum_eq_parts (C : NormCtx) (σ : Stage) (F : Site → Real) :
    siteSum C σ F = Radd (primePart C σ F) (restPart C σ F) := rfl

/-- The mass term `w·4·c²`. -/
def massTerm (w c : Real) : Real := Rmul w (Rmul c4 (Rmul c c))

/-- The witness vector `c_M = (Mβ)·e_p + a`. -/
def shearWitness (m₀ side₀ i₀ : Nat) (M β : Real) (a : Site → Real) : Site → Real :=
  fun s => Radd (Rmul (Rmul M β) (primeUnit m₀ side₀ i₀ s)) (a s)

/-- `w·4·((M+1)β)² = w·4·(Mβ)² + M·(8wβ²) + 4wβ²`. -/
theorem sq_succ_expand (w M β : Real) :
    Req (massTerm w (Rmul (Radd M one) β))
        (Radd (Radd (massTerm w (Rmul M β)) (Rmul M (Rmul c8 (Rmul w (Rmul β β))))) (Rmul c4 (Rmul w (Rmul β β)))) := by
  unfold massTerm
  -- ((M+1)β)² = (Mβ)² + (2M)β² + β²
  have hsq : Req (Rmul (Rmul (Radd M one) β) (Rmul (Radd M one) β))
      (Radd (Radd (Rmul (Rmul M β) (Rmul M β)) (Rmul (Rmul cTwo M) (Rmul β β))) (Rmul β β)) := by
    have h1 : Req (Rmul (Radd M one) β) (Radd (Rmul M β) β) :=
      Req_trans (Rmul_distrib_right _ _ _) (Radd_congr (Req_refl _) (Rone_mul β))
    refine Req_trans (Rmul_congr h1 h1) ?_
    refine Req_trans (add_mul_add_ga _ _ _ _) ?_
    -- ((Mβ)(Mβ) + (Mβ)β) + (β(Mβ) + ββ) ≈ ((Mβ)(Mβ) + (2M)(ββ)) + ββ
    refine Req_trans (Radd_assoc _ _ _) ?_
    refine Req_trans (Radd_congr (Req_refl _) (Req_symm (Radd_assoc _ _ _))) ?_
    refine Req_trans (Req_symm (Radd_assoc _ _ _)) (Radd_congr (Radd_congr (Req_refl _) ?_) (Req_refl _))
    -- (Mβ)β + β(Mβ) ≈ (2M)(ββ)
    have h2 : Req (Rmul (Rmul M β) β) (Rmul M (Rmul β β)) := Rmul_assoc _ _ _
    have h3 : Req (Rmul β (Rmul M β)) (Rmul M (Rmul β β)) :=
      Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Rmul_congr (Rmul_comm β M) (Req_refl _)) (Rmul_assoc _ _ _))
    refine Req_trans (Radd_congr h2 h3) ?_
    exact Req_trans (Req_symm (cTwo_mul _)) (Req_symm (Rmul_assoc _ _ _))
  refine Req_trans (Rmul_congr (Req_refl w) (Rmul_congr (Req_refl c4) hsq)) ?_
  refine Req_trans (Rmul_congr (Req_refl w) (Rmul_distrib c4 _ _)) ?_
  refine Req_trans (Rmul_distrib w _ _) ?_
  refine Radd_congr ?_ ?_
  · refine Req_trans (Rmul_congr (Req_refl w) (Rmul_distrib c4 _ _)) (Req_trans (Rmul_distrib w _ _) (Radd_congr (Req_refl _) ?_))
    -- w·(4·((2M)(ββ))) ≈ M·(8·(w·(ββ)))
    refine Req_trans (Rmul_congr (Req_refl w) (Req_symm (Rmul_assoc c4 _ _))) ?_
    refine Req_trans (Rmul_congr (Req_refl w) (Rmul_congr (Req_symm (Rmul_assoc c4 cTwo M)) (Req_refl _))) ?_
    have h42 : Req (Rmul c4 cTwo) c8 :=
      Req_trans (Rmul_ofQ_ofQ Nat.one_pos Nat.one_pos) (ofQ_congr _ Nat.one_pos (by decide))
    refine Req_trans (Rmul_congr (Req_refl w) (Rmul_congr (Rmul_congr h42 (Req_refl M)) (Req_refl _))) ?_
    -- w·((8M)(ββ)) ≈ M·(8·(w(ββ)))
    refine Req_trans (Rmul_congr (Req_refl w) (Rmul_congr (Rmul_comm c8 M) (Req_refl _))) ?_
    refine Req_trans (Rmul_congr (Req_refl w) (Rmul_assoc M c8 _)) ?_
    refine Req_trans (Req_symm (Rmul_assoc w M _)) (Req_trans (Rmul_congr (Rmul_comm w M) (Req_refl _))
      (Req_trans (Rmul_assoc M w _) (Rmul_congr (Req_refl M) ?_)))
    exact Req_trans (Req_symm (Rmul_assoc w c8 _)) (Req_trans (Rmul_congr (Rmul_comm w c8) (Req_refl _)) (Rmul_assoc c8 w _))
  · -- w·(4·(ββ)) ≈ 4·(w·(ββ))
    exact Req_trans (Req_symm (Rmul_assoc w c4 _)) (Req_trans (Rmul_congr (Rmul_comm w c4) (Req_refl _)) (Rmul_assoc c4 w _))

/-- The prime part of the witness's mass is the single term `w_p·4·(Mβ)²`. -/
theorem primePart_mass_witness (C : NormCtx) (σ : Stage) (m₀ side₀ i₀ : Nat)
    (hm : m₀ < C.X) (hs : side₀ < 2) (hi : i₀ < σ.Nt + 1) (M β : Real) (a : Site → Real)
    (ha : ∀ m side i, Req (a (.prime m side i)) zero) :
    Req (primePart C σ (fun s => massTerm (siteWeight C σ s) (shearWitness m₀ side₀ i₀ M β a s)))
        (massTerm (siteWeight C σ (.prime m₀ side₀ i₀)) (Rmul M β)) := by
  unfold primePart
  refine Req_trans (RsumN_congr (G := fun m => RsumN (fun side => RsumN (fun i =>
      if m = m₀ then (if side = side₀ then (if i = i₀ then massTerm (siteWeight C σ (.prime m side i)) (Rmul M β) else zero) else zero) else zero)
      (σ.Nt + 1)) 2) C.X (fun m _ => RsumN_congr 2 (fun side _ => RsumN_congr (σ.Nt + 1) (fun i _ => ?_))))
    (ind3_sum (fun m side i => massTerm (siteWeight C σ (.prime m side i)) (Rmul M β)) m₀ side₀ i₀ C.X (σ.Nt + 1) hm hs hi)
  show Req (massTerm (siteWeight C σ (.prime m side i))
      (Radd (Rmul (Rmul M β) (if m = m₀ then (if side = side₀ then (if i = i₀ then one else zero) else zero) else zero)) (a (.prime m side i))))
    (if m = m₀ then (if side = side₀ then (if i = i₀ then massTerm (siteWeight C σ (.prime m side i)) (Rmul M β) else zero) else zero) else zero)
  have hz : ∀ w : Real, Req (massTerm w (Radd (Rmul (Rmul M β) zero) (a (.prime m side i)))) zero := fun w => by
    unfold massTerm
    refine Req_trans (Rmul_congr (Req_refl w) (Rmul_congr (Req_refl c4) (Rmul_congr
      (Req_trans (Radd_congr (Rmul_zero _) (ha m side i)) (Radd_zero zero))
      (Req_trans (Radd_congr (Rmul_zero _) (ha m side i)) (Radd_zero zero))))) ?_
    exact mass_zero_term w
  by_cases hmm : m = m₀
  · simp only [if_pos hmm]
    by_cases hss : side = side₀
    · simp only [if_pos hss]
      by_cases hii : i = i₀
      · simp only [if_pos hii]
        unfold massTerm
        have hc : Req (Radd (Rmul (Rmul M β) one) (a (.prime m side i))) (Rmul M β) :=
          Req_trans (Radd_congr (Rmul_one _) (ha m side i)) (Radd_zero _)
        exact Rmul_congr (Req_refl _) (Rmul_congr (Req_refl c4) (Rmul_congr hc hc))
      · simp only [if_neg hii]; exact hz _
    · simp only [if_neg hss]; exact hz _
  · simp only [if_neg hmm]; exact hz _

/-- The prime part of the anchor's mass vanishes (its prime coordinates are zero). -/
theorem primePart_mass_anchor (C : NormCtx) (σ : Stage) (a : Site → Real)
    (ha : ∀ m side i, Req (a (.prime m side i)) zero) :
    Req (primePart C σ (fun s => massTerm (siteWeight C σ s) (a s))) zero := by
  unfold primePart
  refine RsumN_zero_terms _ (fun m _ => RsumN_zero_terms _ (fun side _ => RsumN_zero_terms _ (fun i _ => ?_)))
  show Req (massTerm (siteWeight C σ (.prime m side i)) (a (.prime m side i))) zero
  unfold massTerm
  exact Req_trans (Rmul_congr (Req_refl _) (Rmul_congr (Req_refl c4) (Rmul_congr (ha m side i) (ha m side i)))) (mass_zero_term _)

/-- Off the prime axis the witness IS the anchor, so the rest parts of the masses agree. -/
theorem restPart_mass_witness (C : NormCtx) (σ : Stage) (m₀ side₀ i₀ : Nat) (M β : Real) (a : Site → Real) :
    Req (restPart C σ (fun s => massTerm (siteWeight C σ s) (shearWitness m₀ side₀ i₀ M β a s)))
        (restPart C σ (fun s => massTerm (siteWeight C σ s) (a s))) := by
  have hpt : ∀ s, (∀ m side i, s ≠ .prime m side i) → Req (shearWitness m₀ side₀ i₀ M β a s) (a s) := by
    intro s hs
    unfold shearWitness
    cases s with
    | prime m side i => exact absurd rfl (hs m side i)
    | pole j i => exact Req_trans (Radd_congr (Rmul_zero _) (Req_refl _)) (Req_trans (Radd_comm _ _) (Radd_zero _))
    | cst i => exact Req_trans (Radd_congr (Rmul_zero _) (Req_refl _)) (Req_trans (Radd_comm _ _) (Radd_zero _))
    | tail j i => exact Req_trans (Radd_congr (Rmul_zero _) (Req_refl _)) (Req_trans (Radd_comm _ _) (Radd_zero _))
  have hm : ∀ s, (∀ m side i, s ≠ .prime m side i) →
      Req (massTerm (siteWeight C σ s) (shearWitness m₀ side₀ i₀ M β a s)) (massTerm (siteWeight C σ s) (a s)) :=
    fun s hs => Rmul_congr (Req_refl _) (Rmul_congr (Req_refl c4) (Rmul_congr (hpt s hs) (hpt s hs)))
  unfold restPart
  refine Radd_congr (RsumN_congr _ (fun j _ => RsumN_congr _ (fun i _ => hm _ (fun _ _ _ h => Site.noConfusion h))))
    (Radd_congr (RsumN_congr _ (fun i _ => hm _ (fun _ _ _ h => Site.noConfusion h)))
      (RsumN_congr _ (fun j _ => RsumN_congr _ (fun i _ => hm _ (fun _ _ _ h => Site.noConfusion h)))))

/-- **★ THE GENERIC SHEAR NO-GO.**  Let `T` be any transfer of shear form at the prime site
    `p = (m₀, side₀, i₀)`: `(Tc)_p = c_p + L(c)_p`, with `L` additive at `p`, blind to the prime axis at
    `p`, and injecting the anchor `a` (zero on the prime axis) as `L(a)_p = β`.  Then for every `M` with
    `cutMass a ≤ M·8·w_p·β²`, the witness `c_M = (Mβ)·e_p + a` satisfies
    `cutMass c_M + 4·w_p·β² ≤ cycleMass (T c_M)`.  CONDITIONAL: the existence of such an `M` and the
    positivity `w_p·β² > 0` (for a strict excess) are hypotheses, so this is not a formal `¬ Contractive`;
    it excludes the shear architecture quantitatively.  No property of `T` off the site `p` is used. -/
theorem shear_no_go (C : NormCtx) (σ : Stage) (T L : (Site → Real) → Site → Real)
    (m₀ side₀ i₀ : Nat) (hm : m₀ < C.X) (hs : side₀ < 2) (hi : i₀ < σ.Nt + 1)
    (hT : ∀ c, Req (T c (.prime m₀ side₀ i₀)) (Radd (c (.prime m₀ side₀ i₀)) (L c (.prime m₀ side₀ i₀))))
    (hLadd : ∀ c c', Req (L (fun s => Radd (c s) (c' s)) (.prime m₀ side₀ i₀))
        (Radd (L c (.prime m₀ side₀ i₀)) (L c' (.prime m₀ side₀ i₀))))
    (hLblind : ∀ M : Real, Req (L (fun s => Rmul M (primeUnit m₀ side₀ i₀ s)) (.prime m₀ side₀ i₀)) zero)
    (a : Site → Real) (ha : ∀ m side i, Req (a (.prime m side i)) zero)
    (β : Real) (hβ : Req (L a (.prime m₀ side₀ i₀)) β) (M : Real)
    (hM : Rle (cutMass C σ a) (Rmul M (Rmul c8 (Rmul (siteWeight C σ (.prime m₀ side₀ i₀)) (Rmul β β))))) :
    Rle (Radd (cutMass C σ (shearWitness m₀ side₀ i₀ M β a))
              (Rmul c4 (Rmul (siteWeight C σ (.prime m₀ side₀ i₀)) (Rmul β β))))
        (cycleMass C σ (T (shearWitness m₀ side₀ i₀ M β a))) := by
  -- the transferred coordinate at `p` is `(M+1)β`
  have hTp : Req (T (shearWitness m₀ side₀ i₀ M β a) (.prime m₀ side₀ i₀)) (Rmul (Radd M one) β) := by
    refine Req_trans (hT _) ?_
    have hc : Req (shearWitness m₀ side₀ i₀ M β a (.prime m₀ side₀ i₀)) (Rmul M β) := by
      unfold shearWitness
      rw [primeUnit_self]
      exact Req_trans (Radd_congr (Rmul_one _) (ha _ _ _)) (Radd_zero _)
    have hL : Req (L (shearWitness m₀ side₀ i₀ M β a) (.prime m₀ side₀ i₀)) β := by
      unfold shearWitness
      refine Req_trans (hLadd (fun s => Rmul (Rmul M β) (primeUnit m₀ side₀ i₀ s)) a) ?_
      exact Req_trans (Radd_congr (hLblind (Rmul M β)) hβ) (Req_trans (Radd_comm _ _) (Radd_zero β))
    refine Req_trans (Radd_congr hc hL) ?_
    exact Req_symm (Req_trans (Rmul_distrib_right M one β) (Radd_congr (Req_refl _) (Rone_mul β)))
  -- the cycle mass dominates its `p`-term
  have hcyc : Rle (massTerm (siteWeight C σ (.prime m₀ side₀ i₀)) (Rmul (Radd M one) β))
      (cycleMass C σ (T (shearWitness m₀ side₀ i₀ M β a))) := by
    refine Rle_trans (Rle_of_Req (Rmul_congr (Req_refl _) (Rmul_congr (Req_refl c4)
      (Rmul_congr (Req_symm hTp) (Req_symm hTp))))) ?_
    exact Rle_prime_term_siteSum C σ (F := fun s => massTerm (siteWeight C σ s) (T (shearWitness m₀ side₀ i₀ M β a) s))
      (fun s => Rnonneg_Rmul (siteWeight_nonneg C σ s) (Rnonneg_Rmul (Rnonneg_ofQ Nat.one_pos (by decide)) (Rnonneg_Rmul_self _)))
      m₀ side₀ i₀ hm hs hi
  -- the cut mass of the witness: prime term + the anchor's rest
  have hcut : Req (cutMass C σ (shearWitness m₀ side₀ i₀ M β a))
      (Radd (massTerm (siteWeight C σ (.prime m₀ side₀ i₀)) (Rmul M β)) (cutMass C σ a)) := by
    show Req (Radd (primePart C σ (fun s => massTerm (siteWeight C σ s) (shearWitness m₀ side₀ i₀ M β a s)))
                   (restPart C σ (fun s => massTerm (siteWeight C σ s) (shearWitness m₀ side₀ i₀ M β a s))))
             (Radd _ (Radd (primePart C σ (fun s => massTerm (siteWeight C σ s) (a s)))
                           (restPart C σ (fun s => massTerm (siteWeight C σ s) (a s)))))
    refine Radd_congr (primePart_mass_witness C σ m₀ side₀ i₀ hm hs hi M β a ha) ?_
    refine Req_trans (restPart_mass_witness C σ m₀ side₀ i₀ M β a) ?_
    exact Req_symm (Req_trans (Radd_congr (primePart_mass_anchor C σ a ha) (Req_refl _)) (Req_trans (Radd_comm _ _) (Radd_zero _)))
  refine Rle_trans (Rle_of_Req (Radd_congr hcut (Req_refl _))) ?_
  refine Rle_trans (Radd_le_add (Radd_le_add (Rle_refl _) hM) (Rle_refl _)) ?_
  exact Rle_trans (Rle_of_Req (Req_symm (sq_succ_expand _ M β))) hcyc

/-- The pole-column injection of `atlasTransferStage` at prime sites. -/
def poleColumn (c : Site → Real) : Site → Real
  | .prime _ _ i => c (.pole 0 i)
  | _ => zero

/-- **★ The transfer of §4 is a shear at every prime site and falls under the no-go**: for the pole
    pulse `a = polePulse i₀ α` and every `M` with `cutMass a ≤ M·8·w_p·α²`,
    `cutMass c_M + 4·w_p·α² ≤ cycleMass (K c_M)`. -/
theorem shear_no_go_transfer (C : NormCtx) (σ : Stage) (m₀ side₀ i₀ : Nat)
    (hm : m₀ < C.X) (hs : side₀ < 2) (hi : i₀ < σ.Nt + 1) (α M : Real)
    (hM : Rle (cutMass C σ (polePulse i₀ α)) (Rmul M (Rmul c8 (Rmul (siteWeight C σ (.prime m₀ side₀ i₀)) (Rmul α α))))) :
    Rle (Radd (cutMass C σ (shearWitness m₀ side₀ i₀ M α (polePulse i₀ α)))
              (Rmul c4 (Rmul (siteWeight C σ (.prime m₀ side₀ i₀)) (Rmul α α))))
        (cycleMass C σ (atlasTransferStage C σ (shearWitness m₀ side₀ i₀ M α (polePulse i₀ α)))) :=
  shear_no_go C σ (atlasTransferStage C σ) poleColumn m₀ side₀ i₀ hm hs hi
    (fun _ => Req_refl _) (fun _ _ => Req_refl _)
    (fun M => by show Req (Rmul M zero) zero; exact Rmul_zero M)
    (polePulse i₀ α) (fun _ _ _ => Req_refl _) α
    (by show Req (if i₀ = i₀ then α else zero) α; rw [if_pos rfl]; exact Req_refl _) M hM

end UOR.Bridge.F1Square.Square
