/-
F1 square — **THE F1 DECODING OF THE COUPLING COORDINATE** (`AtlasOrbitDecode.lean`, target-free).

The coupling addresses of `AtlasOrbitAddress` (finite sites `(n,t)`, Archimedean sites `(x,s)`, coupled when
`n·s = x·t`) are decoded into the coherent scale field of `AtlasScaleField`:

    `decodeFin  (n,t) = (U_n(f,t), V(f,t))`,      `decodeArch (x,s) = (U_x(f,s), V(f,s))`,

and the AC-23 source laws become EQUIVARIANCE OF DECODING:
 * `decode_orbit_equivariance` — on a coupling address, `invSq(x)·U_n(f,t) = invSq(n)·U_x(f,s)`
   (the `U`-coordinates of the two legs agree up to the exact weight ratio, `Uc_orbit`);
 * `decode_anchor` — the finite leg's anchor `V(f,t)` sits at `t = n·s/x` (`anchorT`), NOT at `s`: the
   coupling is nonlocal in the Haar coordinate;
 * `decode_zero_row` — support-forced zero rows of the finite leg (`Uc_zero_row`);
 * the actual marginals at decoded sites: the atomic prime weight `2Λ(n)·w·r(t)` IS `primeFoldDensity`, the
   pole weight `2(1+1/x)·w·r(s)` IS `poleDensity`, and the constant, compact-tail, far weights are the
   existing densities (all nonnegative).

HONEST SCOPE: decoding and its laws only.  No resolver, no colligation, no kernel, no readback identity,
no positivity: the generator semantics of the Atlas calculus (`mark … evaluate`) are not in the repository,
and nothing here invents them.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasOrbitAddress
import F1Square.Square.AtlasSourceLaws

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

/-- The real scale of a prime-power address. -/
def PrimePowerAddr.r (n : PrimePowerAddr) : Real := ofQ n.q (primePowerAddr_q_den n)
/-- The real Haar coordinate of a finite site. -/
def FiniteLocalAddr.tr (p : FiniteLocalAddr) : Real := ofQ p.t p.htd
def ArchLocalAddr.xr (q : ArchLocalAddr) : Real := ofQ q.x q.hxd
def ArchLocalAddr.sr (q : ArchLocalAddr) : Real := ofQ q.s q.hsd

/-- **Decoding a finite site** into the scale field: `(U_n(f,t), V(f,t))`. -/
def decodeFin (C : NormCtx) (f : L2Test) (p : FiniteLocalAddr) : Real × Real :=
  (Uc C p.n.r f p.tr, Vc C f p.tr)
/-- **Decoding an Archimedean site**: `(U_x(f,s), V(f,s))`. -/
def decodeArch (C : NormCtx) (f : L2Test) (q : ArchLocalAddr) : Real × Real :=
  (Uc C q.xr f q.sr, Vc C f q.sr)

/-- The division-free coincidence, read as reals: `x·t ≈ n·s`. -/
theorem onOrbit_real {p : FiniteLocalAddr} {q : ArchLocalAddr} (h : OnOrbit p q) :
    Req (Rmul q.xr p.tr) (Rmul p.n.r q.sr) := by
  unfold ArchLocalAddr.xr FiniteLocalAddr.tr PrimePowerAddr.r ArchLocalAddr.sr
  refine Req_trans (Rmul_ofQ_ofQ q.hxd p.htd) (Req_trans (ofQ_congr _ _ (Qeq_symm h)) (Req_symm (Rmul_ofQ_ofQ (primePowerAddr_q_den p.n) q.hsd)))

/-- **★ EQUIVARIANCE OF DECODING**: on a coupling address (both sites in the band `[0,S]`, both Haar
    coordinates `≥ a`), `invSq(x)·U_n(f,t) = invSq(n)·U_x(f,s)`. -/
theorem decode_orbit_equivariance (C : NormCtx) (f : L2Test) (c : CouplingAddr)
    (hnS : Rle c.fin.n.r (ofQ C.S C.hSd)) (hxS : Rle c.arch.xr (ofQ C.S C.hSd))
    (ht : Rle (ofQ C.a C.had) c.fin.tr) (hs : Rle (ofQ C.a C.had) c.arch.sr) :
    Req (Rmul (invSq C c.arch.xr) (decodeFin C f c.fin).1) (Rmul (invSq C c.fin.n.r) (decodeArch C f c.arch).1) :=
  Uc_orbit C f (Rle_ofQ_ofQ (by decide) _ (by
      show (0 : Int) * (c.fin.n.q.den : Int) ≤ c.fin.n.q.num * ((1 : Nat) : Int)
      have := (primePowerAddr_q_num c.fin.n); push_cast; omega)) hnS
    (Rle_ofQ_ofQ (by decide) _ (by
      show (0 : Int) * (c.arch.x.den : Int) ≤ c.arch.x.num * ((1 : Nat) : Int)
      have := c.arch.hxn; push_cast; omega)) hxS ht hs (onOrbit_real (couplingAddr_onOrbit c))

/-- **The anchor is nonlocal**: the finite leg of a coupling address built from an Archimedean site `(x,s)`
    and a prime power `n` has Haar coordinate `t = n·s/x` (`anchorT`), so its `V`-coordinate is `V(f, n·s/x)`. -/
def coupleArch (q : ArchLocalAddr) (n : PrimePowerAddr) : CouplingAddr :=
  ⟨(⟨n, anchorT q n, Qmul_num_pos (Qmul_num_pos (primePowerAddr_q_num n) q.hsn) (Qinv_num_pos q.hxd),
      Qmul_den_pos (Qmul_den_pos (primePowerAddr_q_den n) q.hsd) (Qinv_den_pos q.hxn)⟩, q), anchor_exists_arch q n⟩

theorem decode_anchor (C : NormCtx) (f : L2Test) (q : ArchLocalAddr) (n : PrimePowerAddr) :
    (decodeFin C f (coupleArch q n).fin).2 = Vc C f (ofQ (anchorT q n) (Qmul_den_pos (Qmul_den_pos (primePowerAddr_q_den n) q.hsd) (Qinv_den_pos q.hxn))) := rfl

/-- **Support-forced zero rows of the finite leg**: `t ≤ a·n` ⟹ `U_n(f,t) = 0` for a core test (`n ≤ S`). -/
theorem decode_zero_row (C : NormCtx) (f : L2Test) (hf : CoreTest C.geom f) (p : FiniteLocalAddr)
    (hnS : Qle p.n.q C.S) (ht : Rle p.tr (ofQ (mul C.a p.n.q) (Qmul_den_pos C.had (primePowerAddr_q_den p.n)))) :
    Req (decodeFin C f p).1 zero :=
  Uc_zero_row C f hf p.n.q (primePowerAddr_q_den p.n) (by
    show (1 : Int) * ((1 : Nat) : Int) ≤ ((p.n.1 : Nat) : Int) * ((1 : Nat) : Int)
    have := (primePowerAddr_two_le p.n); push_cast; omega) hnS ht

-- ===========================================================================
-- The actual marginals at decoded sites.
-- ===========================================================================

/-- The atomic prime weight at a finite site: `2·Λ(n)·w·r(t)`. -/
def primeMarginal (C : NormCtx) (p : FiniteLocalAddr) : Real :=
  Rmul cTwo (Rmul (vonMangoldt p.n.1) (Rmul (ofQ C.w C.hw) (rEv C p.tr)))
/-- It IS `primeFoldDensity` at `m = n − 1`. -/
theorem primeMarginal_eq (C : NormCtx) (p : FiniteLocalAddr) :
    primeMarginal C p = primeFoldDensity C (p.n.1 - 1) p.tr := by
  unfold primeMarginal primeFoldDensity
  have h : p.n.1 - 1 + 1 = p.n.1 := Nat.sub_add_cancel (Nat.le_trans (by decide) (primePowerAddr_two_le p.n))
  rw [h]
theorem primeMarginal_nonneg (C : NormCtx) (p : FiniteLocalAddr) : Rnonneg (primeMarginal C p) := by
  rw [primeMarginal_eq]; exact primeFoldDensity_nonneg C _ _

/-- The pole weight at an Archimedean site: `2(1 + 1/x)·w·r(s)` — `poleDensity`. -/
def poleMarginal (C : NormCtx) (q : ArchLocalAddr) : Real := poleDensity C q.xr q.sr
theorem poleMarginal_nonneg (C : NormCtx) (q : ArchLocalAddr) : Rnonneg (poleMarginal C q) := poleDensity_nonneg C _ _
/-- The constant weight `(log 4π + γ)·w·r(s)` — `constDensity`. -/
def constMarginal (C : NormCtx) (q : ArchLocalAddr) : Real := constDensity C q.sr
theorem constMarginal_nonneg (C : NormCtx) (q : ArchLocalAddr) : Rnonneg (constMarginal C q) := constDensity_nonneg C _
/-- The compact-tail weight `2·w·r(s)` — `tailDensity` (the kernel sits inside the coordinate `Z`). -/
def tailMarginal (C : NormCtx) (q : ArchLocalAddr) : Real := tailDensity C q.sr
theorem tailMarginal_nonneg (C : NormCtx) (q : ArchLocalAddr) : Rnonneg (tailMarginal C q) := tailDensity_nonneg C _
/-- The far weight `2·K_k(x)·(1/x)·w·r(s)`. -/
def farMarginal (C : NormCtx) (k : Nat) (q : ArchLocalAddr) : Real :=
  Rmul cTwo (Rmul (Rmul (Kfl (dyQ k) (dyQ_num k) (dyQ_den k) q.xr) (rOne q.xr)) (Rmul (ofQ C.w C.hw) (rEv C q.sr)))
theorem farMarginal_nonneg (C : NormCtx) (k : Nat) (q : ArchLocalAddr) : Rnonneg (farMarginal C k q) := by
  unfold farMarginal Kfl rOne
  exact Rnonneg_Rmul (Rnonneg_ofQ Nat.one_pos (by decide))
    (Rnonneg_Rmul (Rnonneg_Rmul (Rnonneg_clampedInv (dyQ k) (dyQ_num k) (dyQ_den k) _)
        (Rnonneg_clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) _))
      (Rnonneg_Rmul (Rnonneg_ofQ C.hw C.hwn) (Rnonneg_clampedInv C.a C.han C.had _)))

end UOR.Bridge.F1Square.Square
