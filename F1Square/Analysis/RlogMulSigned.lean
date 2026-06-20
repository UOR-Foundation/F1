import F1Square.Analysis.ClogAddBounded
import F1Square.Analysis.Gamma

/-!
# Signed-τ artanh/exp substrate — toward general-modulus `Rlog`/`Clog` additivity

The bounded-modulus discharge (`RlogMulPos`, `ClogAddBounded`) requires squared moduli `≥ 1`
(so the `tmap` arguments are `≥ 0`). Extending to the symmetric band `[1/B, B]` (moduli near 1,
above *and* below) needs the artanh/exp identities for **signed** arguments.

The key observation that sidesteps re-deriving the `t≥0` corner bounds: `exp(2·artanh τ) =
(1+τ)/(1−τ)` for `τ < 0` follows from the nonnegative case by **oddness**
(`artanh(−σ) = −artanh σ`, `Rartanh_neg`) and **exp-of-negation** (`exp(−x)·exp(x) = 1`,
`RexpReal_add`), with the addition law lifted through `RexpReal_inj_gen` (no nonneg restriction).

This file builds that substrate bottom-up.
-/

namespace UOR.Bridge.F1Square.Analysis

/-- **`artanh` is odd**: `Rartanh(−t) = −Rartanh t`. Per diagonal index the partial sum negates
    (`artSum_neg`), since the artanh series has only odd-degree terms. The bound for `−t` follows
    from the bound for `t` (`Qabs_neg`). -/
theorem Rartanh_neg (t : Real) (ρ : Q) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den) (hlt : ρ.num.toNat < ρ.den)
    (hb : ∀ n, Qle (Qabs (t.seq n)) ρ)
    (hb' : ∀ n, Qle (Qabs ((Rneg t).seq n)) ρ) :
    Req (Rartanh (Rneg t) ρ hρ0 hρd hlt hb') (Rneg (Rartanh t ρ hρ0 hρd hlt hb)) := by
  refine Req_of_seq_Qeq (fun j => ?_)
  show Qeq (artSum ((Rneg t).seq (Rartanh_R ρ j)) (Rartanh_R ρ j))
        (neg (artSum (t.seq (Rartanh_R ρ j)) (Rartanh_R ρ j)))
  exact artSum_neg (t.den_pos _) (Rartanh_R ρ j)

/-- **`artanh` of a negated rational constant**: `RartanhConst(−τ) = −RartanhConst τ` (at any valid
    radius). Per-diagonal `artSum (neg τ) N = neg(artSum τ N)` (`artSum_neg`); no small-radius needed. -/
theorem RartanhConst_neg (τ ρ : Q) (hτd : 0 < τ.den) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (hρlt : ρ.num.toNat < ρ.den) (hb : Qle (Qabs τ) ρ) (hbn : Qle (Qabs (neg τ)) ρ) :
    Req (RartanhConst (neg τ) ρ (by exact hτd) hρ0 hρd hρlt hbn)
        (Rneg (RartanhConst τ ρ hτd hρ0 hρd hρlt hb)) := by
  refine Req_of_seq_Qeq (fun j => ?_)
  show Qeq (artSum (neg τ) (Rartanh_R ρ j)) (neg (artSum τ (Rartanh_R ρ j)))
  exact artSum_neg hτd (Rartanh_R ρ j)

/-- **`2·artanh` of a negated rational constant**: `TwoArtanhConst(−τ) = −TwoArtanhConst τ`. -/
theorem TwoArtanhConst_neg (τ ρ : Q) (hτd : 0 < τ.den) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (hρlt : ρ.num.toNat < ρ.den) (hb : Qle (Qabs τ) ρ) (hbn : Qle (Qabs (neg τ)) ρ) :
    Req (TwoArtanhConst (neg τ) ρ (by exact hτd) hρ0 hρd hρlt hbn)
        (Rneg (TwoArtanhConst τ ρ hτd hρ0 hρd hρlt hb)) :=
  Req_trans (Rmul_congr (Req_refl _) (RartanhConst_neg τ ρ hτd hρ0 hρd hρlt hb hbn))
    (Rmul_neg_right (ofQ ⟨2, 1⟩ (by decide)) (RartanhConst τ ρ hτd hρ0 hρd hρlt hb))

set_option maxHeartbeats 800000 in
/-- **★ The signed exp/artanh identity** `exp(2·artanh τ) = (1+τ)/(1−τ)` for `τ < 0`, derived from the
    nonnegative case (`hσid`, supplied for `σ = −τ > 0`) by oddness + exp-of-negation — *no* re-derivation
    of the `t ≥ 0` corner bounds. With `gσ = (1+σ)/(1−σ) > 1` (`hgσwit`) and `gτ·gσ = 1` (`hrecip`,
    i.e. `gτ = 1/gσ = (1+τ)/(1−τ)`): `exp(2artanh τ) = exp(−2artanh σ) = 1/exp(2artanh σ) = 1/gσ = gτ`. -/
theorem Rexp_TwoArtanh_of_neg (τ ρ gσ gτ : Q) (hτd : 0 < τ.den)
    (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den) (hρlt : ρ.num.toNat < ρ.den)
    (hb : Qle (Qabs τ) ρ) (hbn : Qle (Qabs (neg τ)) ρ)
    (hgσd : 0 < gσ.den) (hgτd : 0 < gτ.den)
    (hgσwit : Qlt (Qbound 0) gσ) (hrecip : Qeq (mul gτ gσ) ⟨1, 1⟩)
    (hσid : Req (RexpReal (TwoArtanhConst (neg τ) ρ (by exact hτd) hρ0 hρd hρlt hbn)) (ofQ gσ hgσd)) :
    Req (RexpReal (TwoArtanhConst τ ρ hτd hρ0 hρd hρlt hb)) (ofQ gτ hgτd) := by
  let Y := TwoArtanhConst (neg τ) ρ (by exact hτd) hρ0 hρd hρlt hbn
  let Yτ := TwoArtanhConst τ ρ hτd hρ0 hρd hρlt hb
  have hA : Req Y (Rneg Yτ) := TwoArtanhConst_neg τ ρ hτd hρ0 hρd hρlt hb hbn
  have htac : Req Yτ (Rneg Y) := Req_symm (Req_trans (Rneg_congr hA) (Rneg_neg Yτ))
  have hsum0 : Req (Radd (Rneg Y) Y) zero := Req_trans (Radd_comm (Rneg Y) Y) (Radd_neg Y)
  have hprod1 : Req (Rmul (RexpReal (Rneg Y)) (RexpReal Y)) one :=
    Req_trans (Req_symm (RexpReal_add (Rneg Y) Y))
      (Req_trans (RexpReal_congr hsum0) RexpReal_zero)
  have hprodσ : Req (Rmul (RexpReal (Rneg Y)) (ofQ gσ hgσd)) one :=
    Req_trans (Rmul_congr (Req_refl _) (Req_symm hσid)) hprod1
  have hprodgτ : Req (Rmul (ofQ gτ hgτd) (ofQ gσ hgσd)) one :=
    Req_trans (Rmul_ofQ_ofQ hgτd hgσd) (ofQ_congr (Qmul_den_pos hgτd hgσd) (by decide) hrecip)
  have hk : Qlt (Qbound 0) ((ofQ gσ hgσd).seq 0) := hgσwit
  have hcancel : Req (RexpReal (Rneg Y)) (ofQ gτ hgτd) :=
    Rmul_right_cancel hk (Req_trans hprodσ (Req_symm hprodgτ))
  exact Req_trans (RexpReal_congr htac) hcancel

end UOR.Bridge.F1Square.Analysis
