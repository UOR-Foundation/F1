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

/-- **Positive rationals** (numerator and denominator positive). -/
structure PosRat where
  q : Q
  hn : 0 < q.num
  hd : 0 < q.den

theorem posRat_eqv_refl (a : PosRat) : Qeq a.q a.q := Qeq_refl _
theorem posRat_eqv_symm {a b : PosRat} (h : Qeq a.q b.q) : Qeq b.q a.q := Qeq_symm h
theorem posRat_eqv_trans {a b c : PosRat} (h₁ : Qeq a.q b.q) (h₂ : Qeq b.q c.q) : Qeq a.q c.q := Qeq_trans b.hd h₁ h₂

/-- `Qeq` is an equivalence on positive rationals. -/
instance posRatSetoid : Setoid PosRat where
  r a b := Qeq a.q b.q
  iseqv := ⟨posRat_eqv_refl, posRat_eqv_symm, posRat_eqv_trans⟩

/-- **The multiplicative-orbit coordinate**: positive rationals modulo `Qeq` — a genuine quotient, so
    equality of orbit addresses is Lean equality. -/
def ScaleOrbitAddr := Quotient posRatSetoid

theorem Qmul_num_pos {a b : Q} (ha : 0 < a.num) (hb : 0 < b.num) : 0 < (mul a b).num := Int.mul_pos ha hb

/-- `u = n/t` for a finite site (as a positive rational, then its class). -/
def FiniteLocalAddr.orbitRat (p : FiniteLocalAddr) : PosRat :=
  ⟨mul p.n.q (Qinv p.t), Qmul_num_pos (primePowerAddr_q_num p.n) (Qinv_num_pos p.htd), Qmul_den_pos (primePowerAddr_q_den p.n) (Qinv_den_pos p.htn)⟩
def FiniteLocalAddr.orbit (p : FiniteLocalAddr) : ScaleOrbitAddr := Quotient.mk posRatSetoid p.orbitRat

/-- `u = x/s` for an Archimedean site. -/
def ArchLocalAddr.orbitRat (q : ArchLocalAddr) : PosRat :=
  ⟨mul q.x (Qinv q.s), Qmul_num_pos q.hxn (Qinv_num_pos q.hsd), Qmul_den_pos q.hxd (Qinv_den_pos q.hsn)⟩
def ArchLocalAddr.orbit (q : ArchLocalAddr) : ScaleOrbitAddr := Quotient.mk posRatSetoid q.orbitRat

/-- **The division-free coincidence** `n·s = x·t`. -/
def OnOrbit (p : FiniteLocalAddr) (q : ArchLocalAddr) : Prop := Qeq (mul p.n.q q.s) (mul q.x p.t)

/-- `n·s = x·t ⟺ n/t ≈ x/s` (as rationals). -/
theorem onOrbit_iff_orbitRat (p : FiniteLocalAddr) (q : ArchLocalAddr) :
    OnOrbit p q ↔ Qeq p.orbitRat.q q.orbitRat.q := by
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

/-- **`n·s = x·t ⟺ equal orbit addresses`** (Lean equality in the quotient). -/
theorem onOrbit_iff_orbit (p : FiniteLocalAddr) (q : ArchLocalAddr) : OnOrbit p q ↔ p.orbit = q.orbit :=
  ⟨fun h => Quotient.sound ((onOrbit_iff_orbitRat p q).1 h),
   fun h => (onOrbit_iff_orbitRat p q).2 (Quotient.exact h)⟩

-- ===========================================================================
-- (1) THE PULLBACK `FiniteLocalAddr ×_{ScaleOrbitAddr} ArchLocalAddr` over EQUALITY of orbit addresses.
-- ===========================================================================

/-- **The coupling address**: a finite site and an Archimedean site with the SAME orbit address. -/
def CouplingAddr := { pq : FiniteLocalAddr × ArchLocalAddr // pq.1.orbit = pq.2.orbit }

def CouplingAddr.fin (c : CouplingAddr) : FiniteLocalAddr := c.1.1
def CouplingAddr.arch (c : CouplingAddr) : ArchLocalAddr := c.1.2
theorem couplingAddr_orbit_eq (c : CouplingAddr) : c.fin.orbit = c.arch.orbit := c.2
theorem couplingAddr_onOrbit (c : CouplingAddr) : OnOrbit c.fin c.arch := (onOrbit_iff_orbit c.fin c.arch).2 c.2

/-- **Universal property (existence)**: maps `Z → FiniteLocalAddr`, `Z → ArchLocalAddr` with equal orbit
    composites factor through the pullback. -/
def couplingAddr_universal {Z : Type} (F : Z → FiniteLocalAddr) (G : Z → ArchLocalAddr)
    (h : ∀ z, (F z).orbit = (G z).orbit) : Z → CouplingAddr := fun z => ⟨(F z, G z), h z⟩

theorem couplingAddr_universal_fin {Z : Type} (F : Z → FiniteLocalAddr) (G : Z → ArchLocalAddr)
    (h : ∀ z, (F z).orbit = (G z).orbit) (z : Z) : (couplingAddr_universal F G h z).fin = F z := rfl
theorem couplingAddr_universal_arch {Z : Type} (F : Z → FiniteLocalAddr) (G : Z → ArchLocalAddr)
    (h : ∀ z, (F z).orbit = (G z).orbit) (z : Z) : (couplingAddr_universal F G h z).arch = G z := rfl

/-- **Universal property (uniqueness)**: a map into the pullback is determined by its two legs. -/
theorem couplingAddr_unique {Z : Type} (m m' : Z → CouplingAddr)
    (hf : ∀ z, (m z).fin = (m' z).fin) (ha : ∀ z, (m z).arch = (m' z).arch) : ∀ z, m z = m' z := by
  intro z
  apply Subtype.ext
  exact Prod.ext (hf z) (ha z)

theorem Qeq_mul_cancel_left {a b c : Q} (han : 0 < a.num) (had : 0 < a.den) (h : Qeq (mul a b) (mul a c)) : Qeq b c := by
  simp only [Qeq, mul] at h ⊢
  push_cast at h
  have hne : a.num * (a.den : Int) ≠ 0 := Int.ne_of_gt (Int.mul_pos han (Int.ofNat_pos.mpr had))
  apply Int.eq_of_mul_eq_mul_left hne
  have e1 : a.num * (a.den : Int) * (b.num * (c.den : Int)) = a.num * b.num * ((a.den : Int) * (c.den : Int)) := by ring_uor
  have e2 : a.num * (a.den : Int) * (c.num * (b.den : Int)) = a.num * c.num * ((a.den : Int) * (b.den : Int)) := by ring_uor
  rw [e1, e2]; exact h


-- ===========================================================================
-- (1') COMPLETENESS: the orbit address is the quotient by simultaneous positive scaling.
-- ===========================================================================

/-- `Qinv` respects `Qeq` on positive rationals (local, F1-free). -/
theorem Qinv_congr_pr {a b : Q} (han : 0 < a.num) (hbn : 0 < b.num) (h : Qeq a b) : Qeq (Qinv a) (Qinv b) := by
  have ha' : ((a.num.toNat : Nat) : Int) = a.num := Int.toNat_of_nonneg (Int.le_of_lt han)
  have hb' : ((b.num.toNat : Nat) : Int) = b.num := Int.toNat_of_nonneg (Int.le_of_lt hbn)
  simp only [Qeq, Qinv] at h ⊢
  push_cast [ha', hb']
  rw [Int.mul_comm (a.den : Int) b.num, Int.mul_comm (b.den : Int) a.num]
  exact h.symm

/-- `a/b ≈ c/d ⟺ a·d ≈ c·b` for positive `b, d` (division-free form of equal ratios). -/
theorem Qdiv_eq_iff {a b c d : Q} (hbn : 0 < b.num) (hdn : 0 < d.num) :
    Qeq (mul a (Qinv b)) (mul c (Qinv d)) ↔ Qeq (mul a d) (mul c b) := by
  have hb' : ((b.num.toNat : Nat) : Int) = b.num := Int.toNat_of_nonneg (Int.le_of_lt hbn)
  have hd' : ((d.num.toNat : Nat) : Int) = d.num := Int.toNat_of_nonneg (Int.le_of_lt hdn)
  simp only [Qeq, mul, Qinv]
  push_cast [hb', hd']
  constructor
  · intro h
    have e1 : a.num * d.num * ((c.den : Int) * (b.den : Int)) = a.num * (b.den : Int) * ((c.den : Int) * d.num) := by ring_uor
    have e2 : c.num * b.num * ((a.den : Int) * (d.den : Int)) = c.num * (d.den : Int) * ((a.den : Int) * b.num) := by ring_uor
    rw [e1, e2]; exact h
  · intro h
    have e1 : a.num * (b.den : Int) * ((c.den : Int) * d.num) = a.num * d.num * ((c.den : Int) * (b.den : Int)) := by ring_uor
    have e2 : c.num * (d.den : Int) * ((a.den : Int) * b.num) = c.num * b.num * ((a.den : Int) * (d.den : Int)) := by ring_uor
    rw [e1, e2]; exact h

/-- Scaling an Archimedean site by a positive rational `λ`: `(x,s) ↦ (λx, λs)`. -/
def ArchLocalAddr.scale (l : PosRat) (q : ArchLocalAddr) : ArchLocalAddr :=
  ⟨mul l.q q.x, Qmul_num_pos l.hn q.hxn, Qmul_den_pos l.hd q.hxd, mul l.q q.s, Qmul_num_pos l.hn q.hsn, Qmul_den_pos l.hd q.hsd⟩

/-- **Same orbit ⟺ `x·s' = x'·s`** (division-free), for Archimedean sites. -/
theorem orbit_eq_iff_cross (q q' : ArchLocalAddr) : q.orbit = q'.orbit ↔ Qeq (mul q.x q'.s) (mul q'.x q.s) :=
  ⟨fun h => (Qdiv_eq_iff q.hsn q'.hsn).1 (Quotient.exact h),
   fun h => Quotient.sound ((Qdiv_eq_iff q.hsn q'.hsn).2 h)⟩

/-- The scaling factor between two sites: `λ = x'/x`. -/
def scaleBetween (q q' : ArchLocalAddr) : PosRat :=
  ⟨mul q'.x (Qinv q.x), Qmul_num_pos q'.hxn (Qinv_num_pos q.hxd), Qmul_den_pos q'.hxd (Qinv_den_pos q.hxn)⟩

/-- **★ COMPLETENESS (existence)**: equal orbit addresses ⟹ `q' = λ·q` coordinatewise with `λ = x'/x`. -/
theorem orbit_eq_imp_scale (q q' : ArchLocalAddr) (h : q.orbit = q'.orbit) :
    Qeq q'.x (mul (scaleBetween q q').q q.x) ∧ Qeq q'.s (mul (scaleBetween q q').q q.s) := by
  have hc : Qeq (mul q.x q'.s) (mul q'.x q.s) := (orbit_eq_iff_cross q q').1 h
  have hx' : ((q.x.num.toNat : Nat) : Int) = q.x.num := Int.toNat_of_nonneg (Int.le_of_lt q.hxn)
  refine ⟨?_, ?_⟩
  · show Qeq q'.x (mul (mul q'.x (Qinv q.x)) q.x)
    simp only [Qeq, mul, Qinv]; push_cast [hx']; ring_uor
  · -- s' ≈ (x'/x)·s: multiply out with x·s' = x'·s
    show Qeq q'.s (mul (mul q'.x (Qinv q.x)) q.s)
    have hc' := hc
    simp only [Qeq, mul, Qinv] at hc' ⊢
    push_cast [hx'] at hc' ⊢
    -- goal: s'.num * (x'.den * (x.num * s.den)) = x'.num * x.den * s.num * s'.den ; hc' : x.num * s'.num * (x'.den * s.den) = x'.num * s.num * (x.den * s'.den)
    have e1 : q'.s.num * ((q'.x.den : Int) * q.x.num * (q.s.den : Int)) = q.x.num * q'.s.num * ((q'.x.den : Int) * (q.s.den : Int)) := by ring_uor
    have e2 : q'.x.num * (q.x.den : Int) * q.s.num * (q'.s.den : Int) = q'.x.num * q.s.num * ((q.x.den : Int) * (q'.s.den : Int)) := by ring_uor
    rw [e1, e2]; exact hc'

/-- **★ COMPLETENESS (converse)**: `q' = λ·q` coordinatewise ⟹ equal orbit addresses. -/
theorem scale_imp_orbit_eq (q q' : ArchLocalAddr) (l : PosRat) (hx : Qeq q'.x (mul l.q q.x)) (hs : Qeq q'.s (mul l.q q.s)) :
    q.orbit = q'.orbit := by
  refine (orbit_eq_iff_cross q q').2 ?_
  -- x·s' ≈ x·(λ s) ≈ λ·(x s) ≈ (λ x)·s ≈ x'·s
  refine Qeq_trans (Qmul_den_pos q.hxd (Qmul_den_pos l.hd q.hsd)) (Qmul_congr (Qeq_refl _) hs) ?_
  refine Qeq_trans (Qmul_den_pos (Qmul_den_pos l.hd q.hxd) q.hsd) ?_ (Qmul_congr (Qeq_symm hx) (Qeq_refl _))
  -- x·(λ·s) ≈ (λ·x)·s
  refine Qeq_trans (Qmul_den_pos (Qmul_den_pos q.hxd l.hd) q.hsd) (Qeq_symm (Qmul_assoc _ _ _)) ?_
  exact Qmul_congr (Qmul_comm _ _) (Qeq_refl _)

/-- **★ COMPLETENESS (uniqueness)**: the scaling is unique up to `Qeq`. -/
theorem scale_unique (q q' : ArchLocalAddr) (l l' : PosRat) (hx : Qeq q'.x (mul l.q q.x)) (hx' : Qeq q'.x (mul l'.q q.x)) :
    Qeq l.q l'.q := by
  have h : Qeq (mul q.x l.q) (mul q.x l'.q) :=
    Qeq_trans (Qmul_den_pos l.hd q.hxd) (Qmul_comm _ _)
      (Qeq_trans q'.hxd (Qeq_symm hx) (Qeq_trans (Qmul_den_pos l'.hd q.hxd) hx' (Qmul_comm _ _)))
  exact Qeq_mul_cancel_left q.hxn q.hxd h

-- ===========================================================================
-- (1'') CHANNEL-INDEXED ADDRESSES: each channel has its own base and band.
-- ===========================================================================

/-- The five source channels. -/
inductive Channel | prime | pole | const | tail | far
  deriving DecidableEq, Repr

/-- The compact-tail floor `1 + 2^{-k}` as a rational. -/
def tailFloor (k : Nat) : Q := add ⟨1, 1⟩ ⟨1, 2 ^ k⟩

/-- **Channel-indexed site types** at truncation `k` and band cap `B`: the prime channel lives on finite
    sites, the pole/tail/far channels on Archimedean sites in their own bands, the constant channel on
    the Haar coordinate ALONE (it is `s`-only and is not duplicated over `x`). -/
def ChannelAddr (k : Nat) (B : Q) : Channel → Type
  | .prime => FiniteLocalAddr
  | .pole  => { q : ArchLocalAddr // Qle (⟨1, 1⟩ : Q) q.x ∧ Qle q.x B }
  | .const => PosRat
  | .tail  => { q : ArchLocalAddr // Qle (tailFloor k) q.x ∧ Qle q.x B }
  | .far   => { q : ArchLocalAddr // Qle B q.x }

/-- The Haar coordinate of a channel address. -/
def ChannelAddr.haar {k : Nat} {B : Q} : (ch : Channel) → ChannelAddr k B ch → PosRat
  | .prime, p => ⟨p.t, p.htn, p.htd⟩
  | .pole,  q => ⟨q.1.s, q.1.hsn, q.1.hsd⟩
  | .const, s => s
  | .tail,  q => ⟨q.1.s, q.1.hsn, q.1.hsd⟩
  | .far,   q => ⟨q.1.s, q.1.hsn, q.1.hsd⟩

/-- The orbit address of a channel address (the constant channel has no scale: its orbit is `1/s`). -/
def ChannelAddr.orbit {k : Nat} {B : Q} : (ch : Channel) → ChannelAddr k B ch → ScaleOrbitAddr
  | .prime, p => FiniteLocalAddr.orbit p
  | .pole,  q => ArchLocalAddr.orbit q.1
  | .const, s => Quotient.mk posRatSetoid ⟨Qinv s.q, Qinv_num_pos s.hd, Qinv_den_pos s.hn⟩
  | .tail,  q => ArchLocalAddr.orbit q.1
  | .far,   q => ArchLocalAddr.orbit q.1

-- ===========================================================================
-- (2) THE ANCHOR: existence and uniqueness of the coupled Haar coordinate.
-- ===========================================================================

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
