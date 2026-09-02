import Setlec.SetR.Interp2.IndTeleP
import Setlec.SetR.Interp2.Step2.IotaKitP

/-!
# The P-tier frame kit (task #161, IND TIER part 3, step 1)

`Install/IndFrameS.lean`'s machinery at the validated-reading currency
— the environment vocabulary the surviving modeled-iota stages
(`zipperS`/`pointS`/`reductS`/`annotS`) are stated in.

**What this file is, and what it deliberately is not.**  The part-2
correction budgeted a fresh ~350-line transposition of the whole of
`IndFrameS`.  A per-name survey of the four surviving stages says the
kit they actually read is much narrower, and that part 2 had already
landed its core under another name:

* **the chain already exists.**  `consN` (`IndTeleP.lean:262`) is
  `consChain` definitionally — same cons order, same fold — and
  `consN_shift`/`consN_getElem?` are `chainE_ge`/`chainE_lt`'s content
  at bare values.  So `chainP` below is a *wrapper*: the chain of a
  spine's **readings**, `consN (ws.map (interp2 V ρ)) ρ`, and its two
  lookup lemmas are three lines each rather than two inductions;
* **`chainFrom` and its three lemmas do not transpose.**  v1 needs the
  value/base split because `chainE` is defined by a `foldl` over
  *expressions*; going through `consN` there is nothing to split, and
  the survey confirms `chainFrom_cons`/`chainFrom_lt`/`chainFrom_ge`
  have zero occurrences in `IndStagesS.lean` anyway;
* **six more names are dead weight** and are not transposed:
  `padE_zero`, `consChain_nil`, `consChain_cons`,
  `chainE_eq_consChain` (definitional here), `TeleFitV.appN_val` and
  `annotOkV_descend` — the first five have no occurrence anywhere in
  `IndStagesS.lean`, and the last is consumed only by `fireS`, which
  part 2's four-move firing already retired.

What *is* transposed is what the stages consume: the chain and its two
lookups, the `instSeq` pivot between chain-reading and
substituted-reading, and the padding pair — which never appears in a
stage's statement, but is introduced and stripped inside the zipper's
strong induction (`sat_pad_of_mems` up, `padE_shiftE` down).

**The currency delta that matters.**  `Sat` becomes `Sat2` and the
context becomes a `List AVExpr`, so the padding slot is `AVExpr.sort 0`
and its value fact is `empty_mem_univ 0` through `interp2_sort` —
`interp2` of a sort is `univ` on the nose, so the `.sort 0`/`empty`
trick transposes with no `dummyPropT` detour at all.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The reading chain

`chainE`'s twin: the environment a fired spine's *readings* build over
the ambient one, outermost first, so `.bvar 0` names the innermost
(last) argument and indices past the spine read the ambient
environment shifted. -/

/-- The value chain of a spine of readings (outermost first). -/
noncomputable def chainP (V : Type w) [SetTheory V] (ρ : Nat → V)
    (ws : List AVExpr) : Nat → V :=
  consN (ws.map (interp2 V ρ)) ρ

@[simp] theorem chainP_nil (ρ : Nat → V) : chainP V ρ [] = ρ := rfl

theorem chainP_cons (ρ : Nat → V) (w : AVExpr) (ws : List AVExpr) :
    chainP V ρ (w :: ws)
      = consN (ws.map (interp2 V ρ)) (cons (interp2 V ρ w) ρ) := rfl

/-- Chain lookup at or above the spine: the ambient environment,
shifted (`chainE_ge`). -/
theorem chainP_ge {ρ : Nat → V} {ws : List AVExpr} {i : Nat}
    (hi : ws.length ≤ i) : chainP V ρ ws i = ρ (i - ws.length) := by
  have hlen : (ws.map (interp2 V ρ)).length = ws.length := by simp
  have h := consN_shift (ws.map (interp2 V ρ)) ρ (i - ws.length)
  rw [hlen, show i - ws.length + ws.length = i from by omega] at h
  exact h

/-- Chain lookup below the spine: the reading of the
`(len - 1 - i)`-th spine element (`chainE_lt`). -/
theorem chainP_lt {ρ : Nat → V} {ws : List AVExpr} {i : Nat}
    (hi : i < ws.length) :
    chainP V ρ ws i = interp2 V ρ (ws.getD (ws.length - 1 - i) default) := by
  have hlen : (ws.map (interp2 V ρ)).length = ws.length := by simp
  have h := consN_getElem? (ws.map (interp2 V ρ)) ρ i (by rw [hlen]; exact hi)
  rw [hlen] at h
  have hlt : ws.length - 1 - i < ws.length := by omega
  obtain ⟨w, hw⟩ : ∃ w, ws[ws.length - 1 - i]? = some w :=
    ⟨ws[ws.length - 1 - i]'hlt, List.getElem?_eq_getElem hlt⟩
  rw [List.getElem?_map, hw] at h
  simp only [Option.map_some, Option.some.injEq] at h
  rw [List.getD, hw]
  exact h.symm

/-- The tail of a chain at an entry position is the partial chain of
the outer readings (`chainE_tail`). -/
theorem chainP_tail {ρ : Nat → V} {ws : List AVExpr} {i : Nat}
    (hi : i < ws.length) :
    (fun j => chainP V ρ ws (j + i + 1))
      = chainP V ρ (ws.take (ws.length - 1 - i)) := by
  funext j
  have htk : (ws.take (ws.length - 1 - i)).length = ws.length - 1 - i := by
    rw [List.length_take]; omega
  by_cases hj : j + i + 1 < ws.length
  · have hYlt : ws.length - 1 - i - 1 - j < ws.length - 1 - i := by omega
    rw [chainP_lt hj, chainP_lt (by rw [htk]; omega), htk,
      show ws.length - 1 - (j + i + 1)
          = ws.length - 1 - i - 1 - j from by omega,
      List.getD, List.getD, List.getElem?_take_of_lt hYlt]
  · rw [chainP_ge (by omega), chainP_ge (by rw [htk]; omega), htk]
    congr 1
    omega

/-- Inserting the outermost chain reading is `instE` at the spine's
length (`chainE_cons_eq_instE`). -/
theorem chainP_cons_eq_instE (ρ : Nat → V) (w : AVExpr)
    (ws : List AVExpr) :
    chainP V ρ (w :: ws)
      = instE ws.length (interp2 V ρ w) (chainP V ρ ws) := by
  funext i
  unfold instE
  by_cases h1 : i < ws.length
  · rw [if_pos h1, chainP_lt h1,
      chainP_lt (ws := w :: ws) (by simp only [List.length_cons]; omega),
      show (w :: ws).length - 1 - i = (ws.length - 1 - i) + 1 from by
        simp only [List.length_cons]; omega,
      List.getD_cons_succ]
  · rw [if_neg h1]
    by_cases h2 : i = ws.length
    · rw [if_pos h2, h2, chainP_lt (ws := w :: ws)
        (by simp only [List.length_cons]; omega),
        show (w :: ws).length - 1 - ws.length = 0 from by
          simp only [List.length_cons]; omega,
        List.getD_cons_zero]
    · rw [if_neg h2, chainP_ge (ws := ws) (by omega),
        chainP_ge (ws := w :: ws)
          (by simp only [List.length_cons]; omega)]
      congr 1
      simp only [List.length_cons]
      omega

/-! ## Evaluation is instantiation

The design's central saving, one currency over: interpreting a fully
spine-instantiated reading is interpreting the open reading at the
value chain.  `AVExpr.instSeq` is `VExpr.instSeq`'s twin — outermost
argument first, at descending cuts. -/

/-- Instantiate a spine of readings at descending cuts, outermost
first (`VExpr.instSeq`'s twin). -/
def _root_.Setlec.SetR.AVExpr.instSeq :
    List AVExpr → Nat → AVExpr → AVExpr
  | [], _, e => e
  | a :: as, t, e => Setlec.SetR.AVExpr.instSeq as (t - 1) (e.inst a t)

@[simp] theorem AVExpr.instSeq_nil (t : Nat) (e : AVExpr) :
    Setlec.SetR.AVExpr.instSeq [] t e = e := rfl

theorem AVExpr.instSeq_cons (a : AVExpr) (as : List AVExpr) (t : Nat)
    (e : AVExpr) :
    Setlec.SetR.AVExpr.instSeq (a :: as) t e
      = Setlec.SetR.AVExpr.instSeq as (t - 1) (e.inst a t) := rfl

/-- **Evaluation is instantiation** (`interp_instSeq`'s twin). -/
theorem interp2_instSeq :
    ∀ (ws : List AVExpr) (e : AVExpr) (ρ : Nat → V),
      interp2 V ρ (Setlec.SetR.AVExpr.instSeq ws (ws.length - 1) e)
        = interp2 V (chainP V ρ ws) e := by
  intro ws
  induction ws with
  | nil => intro e ρ; rfl
  | cons w ws ih =>
    intro e ρ
    rw [show (w :: ws).length - 1 = ws.length from by simp,
      AVExpr.instSeq_cons, ih (e.inst w ws.length) ρ, interp2_inst]
    congr 1
    funext i
    show instE ws.length
        (interp2 V (shiftE ws.length 0 (chainP V ρ ws)) w)
        (chainP V ρ ws) i
      = chainP V ρ (w :: ws) i
    have hsh : shiftE ws.length 0 (chainP V ρ ws) = ρ := by
      funext j
      show chainP V ρ ws (j + ws.length) = ρ j
      rw [chainP_ge (by omega), Nat.add_sub_cancel]
    rw [hsh, chainP_cons_eq_instE]

/-! ## The padding

An untouched inner context slot is `.sort 0`, its chain value `empty`,
and `empty ∈ˢ univ 0` — so a partially-fitted chain satisfies a
full-depth context with no strengthening lemma.  `interp2` of a sort
is `univ` on the nose (`interp2_sort`), so the trick is even shorter
here than in v1. -/

/-- Pad an environment with `m` copies of `empty` below (`padE`). -/
noncomputable def padE2 (V : Type w) [SetTheory V] (m : Nat)
    (ρ' : Nat → V) : Nat → V :=
  fun i => if i < m then SetTheory.empty else ρ' (i - m)

/-- Shifting past the padding cancels it — the strip half of the
zipper's introduce/strip pair. -/
theorem padE2_shiftE (m : Nat) (ρ' : Nat → V) :
    shiftE m 0 (padE2 V m ρ') = ρ' := by
  funext i
  show (if i < 0 then _ else padE2 V m ρ' (i + m)) = _
  rw [if_neg (Nat.not_lt_zero i)]
  show (if i + m < m then SetTheory.empty else ρ' (i + m - m)) = _
  rw [if_neg (by omega), Nat.add_sub_cancel]

/-- **A padded prefix keeps a context satisfied** (`sat_padded`): the
padding entries are `.sort 0`, their values `empty`, and every older
entry's reading consults only the environment above the padding. -/
theorem sat2_padded {Δa : List AVExpr} {ρ' : Nat → V} (m : Nat)
    (h : Sat2 V Δa ρ') :
    Sat2 V (List.replicate m (.sort 0) ++ Δa) (padE2 V m ρ') := by
  intro i Aa hi
  by_cases him : i < m
  · rw [List.getElem?_append_left (by simpa using him),
      List.getElem?_replicate_of_lt him] at hi
    obtain rfl := Option.some.inj hi
    show padE2 V m ρ' i ∈ˢ interp2 V _ (.sort 0)
    rw [interp2_sort, show padE2 V m ρ' i = SetTheory.empty from by
      simp [padE2, him]]
    exact empty_mem_univ 0
  · rw [List.getElem?_append_right (by simpa using him)] at hi
    simp only [List.length_replicate] at hi
    have h1 := h (i - m) Aa hi
    have henv : (fun j => padE2 V m ρ' (j + i + 1))
        = (fun j => ρ' (j + (i - m) + 1)) := by
      funext j
      show padE2 V m ρ' (j + i + 1) = ρ' (j + (i - m) + 1)
      rw [show padE2 V m ρ' (j + i + 1) = ρ' (j + i + 1 - m) from by
        simp only [padE2, if_neg (show ¬ j + i + 1 < m by omega)],
        show j + i + 1 - m = j + (i - m) + 1 from by omega]
    show padE2 V m ρ' i ∈ˢ interp2 V (fun j => padE2 V m ρ' (j + i + 1)) Aa
    rw [show padE2 V m ρ' i = ρ' (i - m) from by simp [padE2, him], henv]
    exact h1

end Setlec.SetR.Interp2
