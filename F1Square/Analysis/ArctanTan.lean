/-
# `tan(arctan t) = t` and the `cos(arctan t)` closed form

Building on the value-level identity `sin(arctan t) = t·cos(arctan t)`
(`Rsin_arctan_value_eq`, `ArctanODE.lean`) and the genuine Pythagorean identity
`cos² + sin² = 1` (`Rcos_sq_add_sin_sq`, `CosSinAdd.lean`):

* `Rcos_arctan_sq` — `cos²(arctan t)·(1+t²) = 1`, the closed form `cos²(arctan t) = 1/(1+t²)`.
  Substituting `sin = t·cos` into Pythagoras collapses to `cos²·(1+t²) = 1`. Since the right side
  is `1 > 0`, this is the gateway to `cos(arctan t) ≠ 0` and hence `tan(arctan t) = t`.

All RH-*independent* (the `arctan`-addition substrate feeding `arg(zw) = arg z + arg w`); crux
fields stay `none`, RH open.
-/
import F1Square.Analysis.ArctanODE
import F1Square.Analysis.RMulNF

namespace UOR.Bridge.F1Square.Analysis

set_option maxHeartbeats 1000000 in
/-- **`cos²(arctan t)·(1+t²) = 1`** (`|t| ≤ ρ < 1/16`), i.e. the closed form `cos²(arctan t) =
    1/(1+t²)`. Substitute `sin(arctan t) = t·cos(arctan t)` (`Rsin_arctan_value_eq`) into the
    Pythagorean identity `cos² + sin² = 1` (`Rcos_sq_add_sin_sq`): `cos² + t²·cos² = cos²·(1+t²) = 1`.
    The right side `1 > 0` gives `cos(arctan t) ≠ 0`, the gateway to `tan(arctan t) = t`. -/
theorem Rcos_arctan_sq (t₀ ρ : Q) (htd : 0 < t₀.den) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (hlt : ρ.num.toNat < ρ.den) (htρ : Qle (Qabs t₀) ρ)
    (hlt16 : (mul ⟨16, 1⟩ ρ).num.toNat < (mul ⟨16, 1⟩ ρ).den)
    (h2ρ : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul ⟨2, 1⟩ ρ)).num)
    (hhalf : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ⟨2, 1⟩ ρ))) (hρ4 : Qle (mul ⟨4, 1⟩ ρ) ⟨1, 1⟩)
    (hρ2 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ρ ρ))) (hρ8 : Qle (mul ⟨2, 1⟩ ρ) ⟨1, 1⟩)
    (hρ1 : Qle ρ ⟨1, 1⟩) :
    Req (Rmul (Rmul (Rcos (Rarctan t₀ htd hρ0 hρd hlt htρ)) (Rcos (Rarctan t₀ htd hρ0 hρd hlt htρ)))
          (Radd one (Rmul (ofQ t₀ htd) (ofQ t₀ htd)))) one := by
  have hval := Rsin_arctan_value_eq t₀ ρ htd hρ0 hρd hlt htρ hlt16 h2ρ hhalf hρ4 hρ2 hρ8 hρ1
  have hpyth := Rcos_sq_add_sin_sq (Rarctan t₀ htd hρ0 hρd hlt htρ)
  -- t²·cos² = sin²  (substitute sin = t·cos and reassociate)
  have hT2 : Req (Rmul (Rmul (Rcos (Rarctan t₀ htd hρ0 hρd hlt htρ))
        (Rcos (Rarctan t₀ htd hρ0 hρd hlt htρ))) (Rmul (ofQ t₀ htd) (ofQ t₀ htd)))
      (Rmul (Rsin (Rarctan t₀ htd hρ0 hρd hlt htρ)) (Rsin (Rarctan t₀ htd hρ0 hρd hlt htρ))) := by
    refine Req_trans (Rmul_comm (Rmul (Rcos (Rarctan t₀ htd hρ0 hρd hlt htρ))
      (Rcos (Rarctan t₀ htd hρ0 hρd hlt htρ))) (Rmul (ofQ t₀ htd) (ofQ t₀ htd))) ?_
    refine Req_trans (Req_symm (prod_sq_reassoc (ofQ t₀ htd)
      (Rcos (Rarctan t₀ htd hρ0 hρd hlt htρ)))) ?_
    exact Req_symm (Rmul_congr hval hval)
  -- cos²·(1+t²) = cos²·1 + cos²·t² = cos² + sin² = 1
  refine Req_trans (Rmul_distrib (Rmul (Rcos (Rarctan t₀ htd hρ0 hρd hlt htρ))
    (Rcos (Rarctan t₀ htd hρ0 hρd hlt htρ))) one (Rmul (ofQ t₀ htd) (ofQ t₀ htd))) ?_
  refine Req_trans (Radd_congr (Rmul_one (Rmul (Rcos (Rarctan t₀ htd hρ0 hρd hlt htρ))
    (Rcos (Rarctan t₀ htd hρ0 hρd hlt htρ)))) hT2) ?_
  exact hpyth

/-- **`cos(arctan t)` has the explicit inverse `cos(arctan t)·(1+t²)`** (no `sqrt`, no apartness
    witness): `cos · (cos·(1+t²)) = 1`. Reassociates `Rcos_arctan_sq` (`cos²·(1+t²)=1`). -/
theorem Rcos_arctan_inv (t₀ ρ : Q) (htd : 0 < t₀.den) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (hlt : ρ.num.toNat < ρ.den) (htρ : Qle (Qabs t₀) ρ)
    (hlt16 : (mul ⟨16, 1⟩ ρ).num.toNat < (mul ⟨16, 1⟩ ρ).den)
    (h2ρ : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul ⟨2, 1⟩ ρ)).num)
    (hhalf : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ⟨2, 1⟩ ρ))) (hρ4 : Qle (mul ⟨4, 1⟩ ρ) ⟨1, 1⟩)
    (hρ2 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ρ ρ))) (hρ8 : Qle (mul ⟨2, 1⟩ ρ) ⟨1, 1⟩)
    (hρ1 : Qle ρ ⟨1, 1⟩) :
    Req (Rmul (Rcos (Rarctan t₀ htd hρ0 hρd hlt htρ))
          (Rmul (Rcos (Rarctan t₀ htd hρ0 hρd hlt htρ)) (Radd one (Rmul (ofQ t₀ htd) (ofQ t₀ htd)))))
      one :=
  Req_trans (Req_symm (Rmul_assoc (Rcos (Rarctan t₀ htd hρ0 hρd hlt htρ))
      (Rcos (Rarctan t₀ htd hρ0 hρd hlt htρ)) (Radd one (Rmul (ofQ t₀ htd) (ofQ t₀ htd)))))
    (Rcos_arctan_sq t₀ ρ htd hρ0 hρd hlt htρ hlt16 h2ρ hhalf hρ4 hρ2 hρ8 hρ1)

/-- **★ `tan(arctan t) = t` (value level, division-free)**: `Rsin(arctan t) · (cos(arctan t)·(1+t²))
    = t` for `|t| ≤ ρ < 1/16`. Using the explicit inverse `cos(arctan t)·(1+t²)` of `cos(arctan t)`
    (`Rcos_arctan_inv`), `tan(arctan t) = sin·cos⁻¹ = (t·cos)·(cos·(1+t²)) = t·(cos²·(1+t²)) = t`.
    The `sqrt`-free, `Rinv`-free value form of `tan∘arctan = id` — the arctan-addition substrate. -/
theorem Rtan_arctan_eq (t₀ ρ : Q) (htd : 0 < t₀.den) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (hlt : ρ.num.toNat < ρ.den) (htρ : Qle (Qabs t₀) ρ)
    (hlt16 : (mul ⟨16, 1⟩ ρ).num.toNat < (mul ⟨16, 1⟩ ρ).den)
    (h2ρ : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul ⟨2, 1⟩ ρ)).num)
    (hhalf : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ⟨2, 1⟩ ρ))) (hρ4 : Qle (mul ⟨4, 1⟩ ρ) ⟨1, 1⟩)
    (hρ2 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ρ ρ))) (hρ8 : Qle (mul ⟨2, 1⟩ ρ) ⟨1, 1⟩)
    (hρ1 : Qle ρ ⟨1, 1⟩) :
    Req (Rmul (Rsin (Rarctan t₀ htd hρ0 hρd hlt htρ))
          (Rmul (Rcos (Rarctan t₀ htd hρ0 hρd hlt htρ)) (Radd one (Rmul (ofQ t₀ htd) (ofQ t₀ htd)))))
      (ofQ t₀ htd) := by
  have hval := Rsin_arctan_value_eq t₀ ρ htd hρ0 hρd hlt htρ hlt16 h2ρ hhalf hρ4 hρ2 hρ8 hρ1
  refine Req_trans (Rmul_congr hval (Req_refl _)) ?_
  refine Req_trans (Rmul_assoc (ofQ t₀ htd) (Rcos (Rarctan t₀ htd hρ0 hρd hlt htρ))
    (Rmul (Rcos (Rarctan t₀ htd hρ0 hρd hlt htρ)) (Radd one (Rmul (ofQ t₀ htd) (ofQ t₀ htd))))) ?_
  refine Req_trans (Rmul_congr (Req_refl _)
    (Rcos_arctan_inv t₀ ρ htd hρ0 hρd hlt htρ hlt16 h2ρ hhalf hρ4 hρ2 hρ8 hρ1)) ?_
  exact Rmul_one (ofQ t₀ htd)

-- ===========================================================================
-- Angle-addition given the tangent: sin(A+B), cos(A+B) for sin = (tan)·cos.
-- ===========================================================================

/-- `x·(y·z) ≈ y·(x·z)` (left-commutativity of `Rmul`). -/
theorem Rmul_left_comm_loc (x y z : Real) : Req (Rmul x (Rmul y z)) (Rmul y (Rmul x z)) :=
  Req_trans (Req_symm (Rmul_assoc x y z))
    (Req_trans (Rmul_congr (Rmul_comm x y) (Req_refl z)) (Rmul_assoc y x z))

/-- `1·x ≈ x`. -/
theorem Rone_mul_loc (x : Real) : Req (Rmul one x) x := Req_trans (Rmul_comm one x) (Rmul_one x)

/-- `(a·c)·(b·d) ≈ (a·b)·(c·d)` (regroup the four factors), via the `RprodL` product normal form. -/
theorem Rmul_pair_regroup (a b c d : Real) :
    Req (Rmul (Rmul a c) (Rmul b d)) (Rmul (Rmul a b) (Rmul c d)) :=
  Req_trans (Rmul_pair_eq_RprodL4 a c b d)
    (Req_trans (RprodL_perm (List.Perm.cons a (List.Perm.swap b c [d])))
      (Req_symm (Rmul_pair_eq_RprodL4 a b c d)))

/-- **sin angle-addition given the tangent**: if `sin A = a·cos A` and `sin B = b·cos B` then
    `sin(A+B) = (a+b)·(cos A·cos B)`. (`Rsin_add` + substitution + reassociation/distribution.) -/
theorem Rsin_add_of_tan {A B : Real} {a b : Q} (ha : 0 < a.den) (hb : 0 < b.den)
    (hA : Req (Rsin A) (Rmul (ofQ a ha) (Rcos A))) (hB : Req (Rsin B) (Rmul (ofQ b hb) (Rcos B))) :
    Req (Rsin (Radd A B)) (Rmul (Radd (ofQ a ha) (ofQ b hb)) (Rmul (Rcos A) (Rcos B))) := by
  refine Req_trans (Rsin_add A B) ?_
  refine Req_trans (Radd_congr (Rmul_congr (Req_refl _) hB) (Rmul_congr hA (Req_refl _))) ?_
  refine Req_trans (Radd_congr (Rmul_left_comm_loc (Rcos A) (ofQ b hb) (Rcos B))
    (Rmul_assoc (ofQ a ha) (Rcos A) (Rcos B))) ?_
  refine Req_trans (Req_symm (Rmul_distrib_right (ofQ b hb) (ofQ a ha) (Rmul (Rcos A) (Rcos B)))) ?_
  exact Rmul_congr (Radd_comm (ofQ b hb) (ofQ a ha)) (Req_refl _)

/-- **cos angle-addition given the tangent**: if `sin A = a·cos A` and `sin B = b·cos B` then
    `cos(A+B) = (1−a·b)·(cos A·cos B)`. (`Rcos_add` + substitution + the four-factor regroup.) -/
theorem Rcos_add_of_tan {A B : Real} {a b : Q} (ha : 0 < a.den) (hb : 0 < b.den)
    (hA : Req (Rsin A) (Rmul (ofQ a ha) (Rcos A))) (hB : Req (Rsin B) (Rmul (ofQ b hb) (Rcos B))) :
    Req (Rcos (Radd A B))
      (Rmul (Rsub one (Rmul (ofQ a ha) (ofQ b hb))) (Rmul (Rcos A) (Rcos B))) := by
  refine Req_trans (Rcos_add A B) ?_
  refine Req_trans (Rsub_congr (Req_refl _) (Rmul_congr hA hB)) ?_
  refine Req_trans (Rsub_congr (Req_symm (Rone_mul_loc (Rmul (Rcos A) (Rcos B))))
    (Rmul_pair_regroup (ofQ a ha) (ofQ b hb) (Rcos A) (Rcos B))) ?_
  exact Req_symm (Rmul_sub_distrib_right one (Rmul (ofQ a ha) (ofQ b hb)) (Rmul (Rcos A) (Rcos B)))

end UOR.Bridge.F1Square.Analysis
