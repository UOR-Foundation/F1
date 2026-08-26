/-
F1 square — **THE COUPLING COORDINATE: finite and Archimedean local sites over a common multiplicative
orbit** (`AtlasOrbitAddress.lean`).  Independent of F1: this module names no test, no context, no form.

  * `PrimePowerAddr = { n : Nat // isPrimePow n = true }` — the canonical arithmetic substrate
    (`Mangoldt.lean`: `spf`, `isPrimePow`, `vonMangoldt_prime_pow`); no chosen enumeration, no table.
  * `FiniteLocalAddr` — a prime-power site `(n, t)` with a positive rational Haar coordinate `t`.
  * `ArchLocalAddr`  — a continuous site `(x, s)` with positive rational scale `x` and Haar coordinate `s`.
  * `ScaleOrbitAddr` — the multiplicative orbit coordinate `u` (a positive rational); both site types map to
    it by `u = n/t`, resp. `u = x/s`.
  * `OnOrbit p q` — the DIVISION-FREE coincidence `n·s = x·t` (⟺ `n/t = x/s`, `onOrbit_iff_orbit`).
  * `CouplingAddr` — THE PULLBACK `FiniteLocalAddr ×_{ScaleOrbitAddr} ArchLocalAddr`: pairs of sites on one
    orbit, with its projections and its universal property (`couplingAddr_universal`,
    `couplingAddr_unique`: any pair of orbit-compatible maps factors uniquely through it).
  * Existence and uniqueness of the anchor: for a prime site `(n,t)` and a scale `x` there is a Haar coordinate
    `s = x·t/n` with `n·s = x·t` (`anchor_exists`), unique up to `Qeq` (`anchor_unique`); symmetrically
    `t = n·s/x` (`anchor_exists_arch`).  This is the nonlocal anchor relation `t = n·s/x` of the coupling.

Nothing here is a measure, a kernel, or a sign: it is the address on which a coupling would have to live.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Analysis.Mangoldt

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

/-- **The prime-power addresses**: the canonical arithmetic substrate of the finite places. -/
def PrimePowerAddr := { n : Nat // isPrimePow n = true }

theorem primePowerAddr_two_le (n : PrimePowerAddr) : 2 ≤ n.1 := by
  have h := n.2
  unfold isPrimePow at h
  cases hd : decide (2 ≤ n.1) with
  | false => rw [hd] at h; simp at h
  | true => exact of_decide_eq_true hd

/-- The scale of a prime-power address as a rational `n/1`. -/
def PrimePowerAddr.q (n : PrimePowerAddr) : Q := ⟨((n.1 : Nat) : Int), 1⟩
theorem primePowerAddr_q_num (n : PrimePowerAddr) : 0 < n.q.num := by
  show (0 : Int) < ((n.1 : Nat) : Int); have := (primePowerAddr_two_le n); omega
theorem primePowerAddr_q_den (n : PrimePowerAddr) : 0 < n.q.den := Nat.one_pos

/-- **A finite local site** `(n, t)`: a prime-power scale and a positive rational Haar coordinate. -/
structure FiniteLocalAddr where
  n : PrimePowerAddr
  t : Q
  htn : 0 < t.num
  htd : 0 < t.den

/-- **An Archimedean local site** `(x, s)`: a positive rational scale and Haar coordinate. -/
structure ArchLocalAddr where
  x : Q
  hxn : 0 < x.num
  hxd : 0 < x.den
  s : Q
  hsn : 0 < s.num
  hsd : 0 < s.den

/-- **The multiplicative-orbit coordinate** `u > 0`. -/
structure ScaleOrbitAddr where
  u : Q
  hun : 0 < u.num
  hud : 0 < u.den

theorem Qmul_num_pos {a b : Q} (ha : 0 < a.num) (hb : 0 < b.num) : 0 < (mul a b).num := Int.mul_pos ha hb

/-- `u = n/t` for a finite site. -/
def FiniteLocalAddr.orbit (p : FiniteLocalAddr) : ScaleOrbitAddr :=
  ⟨mul p.n.q (Qinv p.t), Qmul_num_pos (primePowerAddr_q_num p.n) (Qinv_num_pos p.htd), Qmul_den_pos (primePowerAddr_q_den p.n) (Qinv_den_pos p.htn)⟩

/-- `u = x/s` for an Archimedean site. -/
def ArchLocalAddr.orbit (q : ArchLocalAddr) : ScaleOrbitAddr :=
  ⟨mul q.x (Qinv q.s), Qmul_num_pos q.hxn (Qinv_num_pos q.hsd), Qmul_den_pos q.hxd (Qinv_den_pos q.hsn)⟩

/-- **The division-free coincidence** `n·s = x·t`. -/
def OnOrbit (p : FiniteLocalAddr) (q : ArchLocalAddr) : Prop := Qeq (mul p.n.q q.s) (mul q.x p.t)

/-- `n·s = x·t ⟺ n/t = x/s`: the division-free form IS equality of the orbit coordinates. -/
theorem onOrbit_iff_orbit (p : FiniteLocalAddr) (q : ArchLocalAddr) :
    OnOrbit p q ↔ Qeq p.orbit.u q.orbit.u := by
  have hn := (primePowerAddr_q_num p.n)
  have ht := p.htn; have hs := q.hsn
  have htd := p.htd; have hsd := q.hsd
  have ht' : ((p.t.num.toNat : Nat) : Int) = p.t.num := Int.toNat_of_nonneg (Int.le_of_lt ht)
  have hs' : ((q.s.num.toNat : Nat) : Int) = q.s.num := Int.toNat_of_nonneg (Int.le_of_lt hs)
  show (p.n.q.num * q.s.num) * ((q.x.den * p.t.den : Nat) : Int) = (q.x.num * p.t.num) * ((p.n.q.den * q.s.den : Nat) : Int)
    ↔ (p.n.q.num * (p.t.den : Int)) * ((q.x.den * q.s.num.toNat : Nat) : Int)
        = (q.x.num * (q.s.den : Int)) * ((p.n.q.den * p.t.num.toNat : Nat) : Int)
  push_cast
  rw [ht', hs']
  have hd1 : (p.n.q.den : Int) = 1 := rfl
  rw [hd1]
  constructor
  · intro h
    -- n·s·x_d·t_d = x·t·s_d  ⟹  n·t_d·(x_d·s) = x·s_d·(1·t): multiply both sides by t·s and cancel t_d... direct: both are
    -- polynomial consequences after cross-multiplying by t.num·s.num; use nonzero cancellation.
    have hts : p.t.num * q.s.num ≠ 0 := Int.ne_of_gt (Int.mul_pos ht hs)
    apply Int.eq_of_mul_eq_mul_right hts
    have e1 : p.n.q.num * (p.t.den : Int) * ((q.x.den : Int) * q.s.num) * (p.t.num * q.s.num)
        = (p.n.q.num * q.s.num * ((q.x.den : Int) * (p.t.den : Int))) * (p.t.num * q.s.num) := by ring_uor
    have e2 : q.x.num * (q.s.den : Int) * (1 * p.t.num) * (p.t.num * q.s.num)
        = (q.x.num * p.t.num * (1 * (q.s.den : Int))) * (p.t.num * q.s.num) := by ring_uor
    rw [e1, e2, h]
  · intro h
    have hds : (p.t.den : Int) * (q.s.den : Int) ≠ 0 := Int.ne_of_gt (Int.mul_pos (Int.ofNat_pos.mpr htd) (Int.ofNat_pos.mpr hsd))
    apply Int.eq_of_mul_eq_mul_right hds
    have e1 : p.n.q.num * q.s.num * ((q.x.den : Int) * (p.t.den : Int)) * ((p.t.den : Int) * (q.s.den : Int))
        = (p.n.q.num * (p.t.den : Int) * ((q.x.den : Int) * q.s.num)) * ((p.t.den : Int) * (q.s.den : Int)) := by ring_uor
    have e2 : q.x.num * p.t.num * (1 * (q.s.den : Int)) * ((p.t.den : Int) * (q.s.den : Int))
        = (q.x.num * (q.s.den : Int) * (1 * p.t.num)) * ((p.t.den : Int) * (q.s.den : Int)) := by ring_uor
    rw [e1, e2, h]

-- ===========================================================================
-- (1) THE PULLBACK `FiniteLocalAddr ×_{ScaleOrbitAddr} ArchLocalAddr`.
-- ===========================================================================

/-- **The coupling address**: a finite site and an Archimedean site on one orbit. -/
def CouplingAddr := { pq : FiniteLocalAddr × ArchLocalAddr // OnOrbit pq.1 pq.2 }

def CouplingAddr.fin (c : CouplingAddr) : FiniteLocalAddr := c.1.1
def CouplingAddr.arch (c : CouplingAddr) : ArchLocalAddr := c.1.2
theorem couplingAddr_onOrbit (c : CouplingAddr) : OnOrbit c.fin c.arch := c.2

/-- The two legs agree on the orbit coordinate. -/
theorem couplingAddr_orbit_eq (c : CouplingAddr) : Qeq c.fin.orbit.u c.arch.orbit.u :=
  (onOrbit_iff_orbit c.fin c.arch).1 (couplingAddr_onOrbit c)

/-- **Universal property (existence)**: orbit-compatible maps `Z → FiniteLocalAddr`, `Z → ArchLocalAddr`
    factor through the pullback. -/
def couplingAddr_universal {Z : Type} (F : Z → FiniteLocalAddr) (G : Z → ArchLocalAddr)
    (h : ∀ z, OnOrbit (F z) (G z)) : Z → CouplingAddr := fun z => ⟨(F z, G z), h z⟩

theorem couplingAddr_universal_fin {Z : Type} (F : Z → FiniteLocalAddr) (G : Z → ArchLocalAddr)
    (h : ∀ z, OnOrbit (F z) (G z)) (z : Z) : (couplingAddr_universal F G h z).fin = F z := rfl
theorem couplingAddr_universal_arch {Z : Type} (F : Z → FiniteLocalAddr) (G : Z → ArchLocalAddr)
    (h : ∀ z, OnOrbit (F z) (G z)) (z : Z) : (couplingAddr_universal F G h z).arch = G z := rfl

/-- **Universal property (uniqueness)**: a map into the pullback is determined by its two legs. -/
theorem couplingAddr_unique {Z : Type} (m m' : Z → CouplingAddr)
    (hf : ∀ z, (m z).fin = (m' z).fin) (ha : ∀ z, (m z).arch = (m' z).arch) : ∀ z, m z = m' z := by
  intro z
  apply Subtype.ext
  exact Prod.ext (hf z) (ha z)

-- ===========================================================================
-- (2) THE ANCHOR: existence and uniqueness of the coupled Haar coordinate.
-- ===========================================================================

theorem Qeq_mul_cancel_left {a b c : Q} (han : 0 < a.num) (had : 0 < a.den) (h : Qeq (mul a b) (mul a c)) : Qeq b c := by
  simp only [Qeq, mul] at h ⊢
  push_cast at h
  have hne : a.num * (a.den : Int) ≠ 0 := Int.ne_of_gt (Int.mul_pos han (Int.ofNat_pos.mpr had))
  apply Int.eq_of_mul_eq_mul_left hne
  have e1 : a.num * (a.den : Int) * (b.num * (c.den : Int)) = a.num * b.num * ((a.den : Int) * (c.den : Int)) := by ring_uor
  have e2 : a.num * (a.den : Int) * (c.num * (b.den : Int)) = a.num * c.num * ((a.den : Int) * (b.den : Int)) := by ring_uor
  rw [e1, e2]; exact h

/-- **The anchor exists**: for a prime site `(n,t)` and a scale `x`, the Haar coordinate `s = x·t/n` satisfies `n·s = x·t`. -/
def anchorS (p : FiniteLocalAddr) (x : Q) : Q := mul (mul x p.t) (Qinv p.n.q)

theorem anchor_exists (p : FiniteLocalAddr) (x : Q) : Qeq (mul p.n.q (anchorS p x)) (mul x p.t) := by
  unfold anchorS
  simp only [Qeq, mul, Qinv, PrimePowerAddr.q]
  push_cast
  simp only [Int.toNat_ofNat, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm, Int.one_mul, Int.mul_one]

/-- **The anchor is unique** (up to `Qeq`): `n·s = x·t` and `n·s' = x·t` force `s ≈ s'`. -/
theorem anchor_unique (p : FiniteLocalAddr) (x : Q) (hxd : 0 < x.den) (s s' : Q)
    (hs : Qeq (mul p.n.q s) (mul x p.t)) (hs' : Qeq (mul p.n.q s') (mul x p.t)) : Qeq s s' :=
  Qeq_mul_cancel_left (primePowerAddr_q_num p.n) (primePowerAddr_q_den p.n) (Qeq_trans (Qmul_den_pos hxd p.htd) hs (Qeq_symm hs'))

/-- Symmetrically, the finite Haar coordinate `t = n·s/x` is forced by the Archimedean site. -/
def anchorT (q : ArchLocalAddr) (n : PrimePowerAddr) : Q := mul (mul n.q q.s) (Qinv q.x)

theorem anchor_exists_arch (q : ArchLocalAddr) (n : PrimePowerAddr) : Qeq (mul n.q q.s) (mul q.x (anchorT q n)) := by
  have hx' : ((q.x.num.toNat : Nat) : Int) = q.x.num := Int.toNat_of_nonneg (Int.le_of_lt q.hxn)
  unfold anchorT
  simp only [Qeq, mul, Qinv, PrimePowerAddr.q]
  push_cast [hx']
  simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm, Int.one_mul, Int.mul_one]

end UOR.Bridge.F1Square.Square
