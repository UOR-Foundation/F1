/-
F1 square — the certificate front, workstream 2: **THE GATE-A FINITE-LIST TEMPLATE**
(`GateA_of_finiteList`), and the first candidate-class prune through it (workstream 1 record).

THE TEMPLATE (REMAINING_WORK "The certificate front", workstream 2). Gate A for the genuine
square is the uniform diagonal identity `gramOf ι D n n ≈ 2λₙ` for ALL `n > 0`
(`realizesDiag_genuine_iff`) — a `∀ n` statement, structurally different from any finite rung.
This brick specifies Gate A as a FINITE exact hypothesis list around a generating recurrence:
fix `D`, fix an order `K` and coefficients `a`, and require

  (base)     the K base identities   `gramOf ι D (1+i) (1+i) ≈ 2λ_{1+i}`, `i < K`;
  (gramRec)  the embedding's squared-norm diagonal satisfies the order-K linear recurrence;
  (lamRec)   the doubled genuine Li sequence satisfies the SAME recurrence.

`GateA_of_finiteList` proves: the list implies `RealizesDiag` — i.e. Gate A, i.e. (through
`gateA_is_liNonneg`) Li-nonnegativity of the genuine sequence. The reduction engine is
`linRec_unique`: two sequences satisfying one order-K linear recurrence over the constructive
reals with `≈`-equal initial K values are `≈`-equal everywhere (course-of-values induction —
kernel-checked, no analysis). Any candidate `(ι, D, K, a)` is henceforth checked against this
one list; each item is an exact kernel statement.

DIFFICULTY CONSERVATION (the honest ledger). The template does not manufacture positivity:
`lamRec` is a statement about the λ-sequence itself, and base+lamRec+gramRec together are
exactly as strong as Gate A on the candidate. NOTHING here asserts the list is satisfiable
for the genuine square — by `finiteList_is_liNonneg` a satisfiable instance would prove
`LiNonneg (genuineLamSeq)`, which is RH. The crux fields stay `none`.

TWO-SIDED GUARDS (the no-smuggling discipline of `GateA.lean`, extended to the list):
- `finiteList_satisfiable`: the list is not vacuously false — at the template square the
  constant rule passes the whole list and the reduction DELIVERS `RealizesDiag` end to end;
- `finiteList_can_fail`: the recurrence hypotheses alone never suffice — the zero rule
  satisfies both recurrences yet its base identity is REFUTED. The base carries content.

THE FIRST PRUNE (workstream 1 record, as REMAINING_WORK prescribes: "failure of any
hypothesis is recorded and prunes the candidate class"). The order-1 CONSTANT class
`(K, a) = (1, 1)` — every rule whose diagonal is eventually constant from `n = 1`, i.e.
period-one candidates — forces `2λ₂ ≈ 2λ₁` through `lamRec`. The certified gap
`λ₁ ≉ λ₂` (`Rlambda1_ne_Rlambda2`, `Analysis/LambdaGap.lean`) refutes that for EVERY
anchored η-data, every rule `ι`, and every dimension `D` at once
(`constantClass_pruned`). This is the template doing its job: one finite certified fact
kills an infinite candidate class.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Square.GateA
import F1Square.Analysis.LambdaGap

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis
open UOR.Bridge.F1Square.Li

-- ===========================================================================
-- The generating recurrence over the constructive reals.
-- ===========================================================================

/-- A sequence `s` **satisfies the order-`K` linear recurrence** with coefficient family `a`:
    `s(n+K) ≈ Σ_{i<K} aᵢ · s(n+i)` for every `n`. (`K = 0` degenerates to `s ≈ 0`.) -/
def SatisfiesRec (a : Nat → Real) (K : Nat) (s : Nat → Real) : Prop :=
  ∀ n, Req (s (n + K)) (RsumN (fun i => Rmul (a i) (s (n + i))) K)

/-- `SatisfiesRec` transports along a pointwise `≈` of sequences. -/
theorem SatisfiesRec_congr {a : Nat → Real} {K : Nat} {s t : Nat → Real}
    (hst : ∀ n, Req (s n) (t n)) (hs : SatisfiesRec a K s) : SatisfiesRec a K t :=
  fun n => Req_trans (Req_symm (hst (n + K))) (Req_trans (hs n)
    (RsumN_congr K (fun i _ => Rmul_congr (Req_refl (a i)) (hst (n + i)))))

/-- **THE REDUCTION ENGINE**: two sequences satisfying the SAME order-`K` recurrence with
    `≈`-equal initial `K` values are `≈`-equal at every index — course-of-values induction,
    entirely finite/kernel-checked. This is what turns the `∀ n` diagonal identity into a
    finite hypothesis list. -/
theorem linRec_unique {a : Nat → Real} {K : Nat} {s t : Nat → Real}
    (hs : SatisfiesRec a K s) (ht : SatisfiesRec a K t)
    (hbase : ∀ i, i < K → Req (s i) (t i)) : ∀ n, Req (s n) (t n) := by
  have H : ∀ N n, n < N → Req (s n) (t n) := by
    intro N
    induction N with
    | zero => exact fun n hn => absurd hn (Nat.not_lt_zero n)
    | succ N ih =>
      intro n hn
      by_cases hK : n < K
      · exact hbase n hK
      · by_cases hlt : n < N
        · exact ih n hlt
        · obtain ⟨p, hp⟩ : ∃ p, n = p + K := ⟨n - K, by omega⟩
          subst hp
          refine Req_trans (hs p) (Req_trans (RsumN_congr K (fun i hi =>
            Rmul_congr (Req_refl (a i)) (ih (p + i) (by omega)))) (Req_symm (ht p)))
  exact fun n => H (n + 1) n (Nat.lt_succ_self n)

/-- The order-1 constant recurrence (`a = 1`) holds for a step-wise constant sequence. -/
theorem satisfiesRec_const {s : Nat → Real} (hconst : ∀ n, Req (s (n + 1)) (s n)) :
    SatisfiesRec (fun _ => one) 1 s := by
  intro n
  refine Req_trans (hconst n) ?_
  exact Req_symm (Req_trans (Radd_comm zero (Rmul one (s n)))
    (Req_trans (Radd_zero (Rmul one (s n))) (Req_trans (Rmul_comm one (s n)) (Rmul_one (s n)))))

/-- Conversely, the order-1 constant recurrence forces consecutive `≈`-equality. -/
theorem satisfiesRec_const_step {s : Nat → Real}
    (h : SatisfiesRec (fun _ => one) 1 s) (n : Nat) : Req (s (n + 1)) (s n) := by
  refine Req_trans (h n) ?_
  exact Req_trans (Radd_comm zero (Rmul one (s n)))
    (Req_trans (Radd_zero (Rmul one (s n))) (Req_trans (Rmul_comm one (s n)) (Rmul_one (s n))))

-- ===========================================================================
-- The reduction: finite list ⟹ RealizesDiag (generic square, then Gate A).
-- ===========================================================================

/-- **The finite list implies the diagonal realization** — generic in the spectral square:
    `K` base identities + the two recurrence facts reduce the `∀ n` to `linRec_unique`. -/
theorem realizesDiag_of_finiteList (S : SpectralSquare) (ι : AtlasRule) (D K : Nat)
    (a : Nat → Real)
    (hbase : ∀ i, i < K → Req (gramOf ι D (1 + i) (1 + i)) (Rneg (S.cSq (1 + i))))
    (hgram : SatisfiesRec a K (fun m => gramOf ι D (1 + m) (1 + m)))
    (htarget : SatisfiesRec a K (fun m => Rneg (S.cSq (1 + m)))) :
    RealizesDiag S ι D := by
  intro n hn
  obtain ⟨m, hm⟩ : ∃ m, n = 1 + m := ⟨n - 1, by omega⟩
  subst hm
  exact linRec_unique hgram htarget hbase m

/-- **THE GATE-A FINITE LIST** for the genuine square, in the `2λ` form a candidate targets:
    the `K` base identities, the recurrence on the embedding diagonal, and the SAME recurrence
    on the doubled genuine Li sequence. Each field is an exact kernel statement. -/
structure GateAList (E : StieltjesEta) (ι : AtlasRule) (D K : Nat) (a : Nat → Real) : Prop where
  /-- base identities: `gramOf ι D (1+i) (1+i) ≈ 2λ_{1+i}` for `i < K` -/
  base : ∀ i, i < K → Req (gramOf ι D (1 + i) (1 + i))
      (Radd (genuineLamSeq E.eta (1 + i)) (genuineLamSeq E.eta (1 + i)))
  /-- the embedding's squared-norm diagonal satisfies the generating recurrence -/
  gramRec : SatisfiesRec a K (fun m => gramOf ι D (1 + m) (1 + m))
  /-- the doubled genuine Li sequence satisfies the SAME recurrence -/
  lamRec : SatisfiesRec a K
      (fun m => Radd (genuineLamSeq E.eta (1 + m)) (genuineLamSeq E.eta (1 + m)))

/-- **`GateA_of_finiteList` — the workstream-2 deliverable**: the finite list implies Gate A.
    (Gate B is free, so with `gateA_is_liNonneg` the list implies `LiNonneg (genuineLamSeq)`;
    NOTHING asserts the list is satisfiable for the genuine square — that is RH.) -/
theorem GateA_of_finiteList {E : StieltjesEta} {ι : AtlasRule} {D K : Nat} {a : Nat → Real}
    (h : GateAList E ι D K a) : GateA E ι D := by
  refine (realizesDiag_genuine_iff E ι D).mpr ?_
  intro n hn
  obtain ⟨m, hm⟩ : ∃ m, n = 1 + m := ⟨n - 1, by omega⟩
  subst hm
  exact linRec_unique h.gramRec h.lamRec h.base m

/-- **The honest ledger, explicit**: a satisfied list IS Li-nonnegativity of the genuine
    sequence (= the crux content). This is what "the difficulty did not leave Gate A" means
    at the template level: `lamRec` + `base` carry the full weight. NEVER asserted. -/
theorem finiteList_is_liNonneg {E : StieltjesEta} {ι : AtlasRule} {D K : Nat} {a : Nat → Real}
    (h : GateAList E ι D K a) : LiNonneg (genuineLamSeq E.eta) :=
  gateA_is_liNonneg E ι D (GateA_of_finiteList h)

-- ===========================================================================
-- The two-sided guards: the list is a real constraint, and the reduction really fires.
-- ===========================================================================

/-- **Guard #1 (SATISFIABLE, end to end)**: at the template square the constant rule passes
    the whole list — and the reduction DELIVERS `RealizesDiag`. The template is not
    vacuously false, and `GateA_of_finiteList`'s engine genuinely fires. -/
theorem finiteList_satisfiable :
    ∃ (S : SpectralSquare) (ι : AtlasRule) (D K : Nat) (a : Nat → Real),
      (∀ i, i < K → Req (gramOf ι D (1 + i) (1 + i)) (Rneg (S.cSq (1 + i))))
      ∧ SatisfiesRec a K (fun m => gramOf ι D (1 + m) (1 + m))
      ∧ SatisfiesRec a K (fun m => Rneg (S.cSq (1 + m)))
      ∧ RealizesDiag S ι D := by
  have hb : ∀ i, i < 1 → Req (gramOf (fun _ _ => one) 2 (1 + i) (1 + i))
      (Rneg (spectralTemplate.cSq (1 + i))) := by
    intro i _
    -- gramOf 2 = (0 + 1·1) + 1·1 ≈ 1 + 1 ; −cSq = −−(1+1) ≈ 1 + 1
    have hzo : Req (Radd zero one) one := Req_trans (Radd_comm zero one) (Radd_zero one)
    have hL : Req (Radd (Radd zero (Rmul one one)) (Rmul one one)) (Radd one one) :=
      Radd_congr (Req_trans (Radd_congr (Req_refl zero) (Rmul_one one)) hzo) (Rmul_one one)
    exact Req_trans hL (Req_symm (Rneg_neg (Radd one one)))
  have hg : SatisfiesRec (fun _ => one) 1
      (fun m => gramOf (fun _ _ => one) 2 (1 + m) (1 + m)) :=
    satisfiesRec_const (fun _ => Req_refl _)
  have ht : SatisfiesRec (fun _ => one) 1
      (fun m => Rneg (spectralTemplate.cSq (1 + m))) :=
    satisfiesRec_const (fun _ => Req_refl _)
  exact ⟨spectralTemplate, (fun _ _ => one), 2, 1, (fun _ => one), hb, hg, ht,
    realizesDiag_of_finiteList spectralTemplate (fun _ _ => one) 2 1 (fun _ => one) hb hg ht⟩

/-- **Guard #2 (NON-TRIVIAL)**: the recurrence hypotheses alone never suffice — the zero rule
    satisfies BOTH recurrences at the template square, yet its base identity is refuted
    (`0 ≉ 2`). The base list carries content; nothing is definitional. -/
theorem finiteList_can_fail :
    ∃ (S : SpectralSquare) (ι : AtlasRule) (D K : Nat) (a : Nat → Real),
      SatisfiesRec a K (fun m => gramOf ι D (1 + m) (1 + m))
      ∧ SatisfiesRec a K (fun m => Rneg (S.cSq (1 + m)))
      ∧ ¬ (∀ i, i < K → Req (gramOf ι D (1 + i) (1 + i)) (Rneg (S.cSq (1 + i)))) := by
  refine ⟨spectralTemplate, (fun _ _ => zero), 1, 1, (fun _ => one),
    satisfiesRec_const (fun _ => Req_refl _), satisfiesRec_const (fun _ => Req_refl _), ?_⟩
  intro h
  have h0 := h 0 (by omega)
  have hg : Req (Radd zero (Rmul zero zero)) (Radd zero zero) :=
    Radd_congr (Req_refl zero) (Rmul_zero zero)
  have hc : Req (Rneg (spectralTemplate.cSq 1)) (Radd one one) := Rneg_neg (Radd one one)
  have hbad : Req (Radd zero zero) (Radd one one) :=
    Req_trans (Req_symm hg) (Req_trans h0 hc)
  exact not_Pos_zero_double (Pos_congr (Req_symm hbad) (Pos_Radd_self Pos_one))

-- ===========================================================================
-- The first prune (workstream 1 record): the constant class is dead.
-- ===========================================================================

/-- **The constant class fails `lamRec`**: the order-1 constant recurrence on the doubled
    genuine Li sequence forces `2λ₂ ≈ 2λ₁`, refuted by the certified gap
    `λ₁ ≉ λ₂` (`Rlambda1_ne_Rlambda2`) — for EVERY anchored η-data. -/
theorem constantClass_lamRec_fails (E : StieltjesEta) :
    ¬ SatisfiesRec (fun _ => one) 1
        (fun m => Radd (genuineLamSeq E.eta (1 + m)) (genuineLamSeq E.eta (1 + m))) := by
  intro h
  have h10 : Req (Radd (genuineLamSeq E.eta 2) (genuineLamSeq E.eta 2))
      (Radd (genuineLamSeq E.eta 1) (genuineLamSeq E.eta 1)) := satisfiesRec_const_step h 0
  have h21 : Req (Radd Rlambda2 Rlambda2) (Radd Rlambda1 Rlambda1) :=
    Req_trans (Radd_congr (Req_symm (genuineLam_two E)) (Req_symm (genuineLam_two E)))
      (Req_trans h10 (Radd_congr (genuineLam_one E) (genuineLam_one E)))
  exact Rlambda1_ne_Rlambda2 (Rdouble_inj (Req_symm h21))

/-- **THE PRUNE, RECORDED**: no Gate-A finite list exists in the constant class
    `(K, a) = (1, 1)` — for every anchored η-data `E`, every atlas rule `ι`, and every
    dimension `D`. Period-one diagonals are dead as Gate-A candidates; the growth of `2λₙ`
    is already felt at `n = 2`. One finite certified fact kills the whole class. -/
theorem constantClass_pruned (E : StieltjesEta) (ι : AtlasRule) (D : Nat) :
    ¬ GateAList E ι D 1 (fun _ => one) :=
  fun h => constantClass_lamRec_fails E h.lamRec

end UOR.Bridge.F1Square.Square
