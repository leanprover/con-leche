module

public import InLeanProof.EnvPresI
public import InLeanProof.Range
/- `Expr.hasLooseBVars`/`looseBVarRange` are read through the data field (as in `Ops.lean`). -/
import all Lean.Expr
import ConLeche.Verify.FastOps

/-!
# A structure's projection bodies through the translation (task #451, lanes P3r, projBody)

InLean builds field `i`'s projection body at use (`projBodyAt`): field `i`'s
domain in the constructor type, instantiated in one walk at the parameters'
variables `bvar nP, …, bvar 1` and the subject's projections
`.proj T j (bvar 0)` of the fields before it (`projBodyArgs`).  con-leche's
install computes every body once (`structProjBodies`: `instPisAtLift` at
`structProjPs nP`, then `structProjBodiesGo`), one binder at a time.  Both
substitute *open* values, lifted under binders; `toExpr_instantiate` reads
instantiation at closed values only.

**Main results.**
* `instLift`: instantiation at open values in one walk, on con-leche's side;
  `instSeqLift_eq_instLift`: substituting one binder at a time down a
  telescope is that one walk.
* `toExpr_instantiateRevO`: InLean's `instantiateRev` at open values in range
  reads as `instLift`.
* `projBodyAt_tr`: field `i`'s body as InLean builds it reads as con-leche's
  `structProjBodies`' entry `i`, given the constructor type in range and the
  parameter variables in range (`projBodyOk`).
* `hasPis_iff_structProjBodies`: InLean's table test (`hasPis (nP + nF)`) is
  con-leche's `structProjBodies` succeeding.

The body itself can be out of range where the constructor type is not (a
parameter reference is lifted by one past the subject's binder); reading it
does not need its range, and InLean tests it where a body is read further
(`projBodyOk`, `FEnv.projBodiesInRange`).
-/

public section

namespace InLeanProof

open Lean InLean

/-! ## Instantiation at open values, on con-leche's side -/

/-- **Instantiation at open values in one walk**: `bvar (k + j)` (`j` below
the values' count) becomes value `j` lifted past the `k` binders crossed; the
variables above the values are lowered by their count. -/
@[expose] def instLift (vs : List ConLeche.Expr) : ConLeche.Expr → Nat → ConLeche.Expr
  | .bvar i, k =>
    if i < k then .bvar i
    else if h : i - k < vs.length then vs[i - k].liftLooseBVars k 0
    else .bvar (i - vs.length)
  | .fvar idx ty, _ => .fvar idx ty
  | .sort u, _ => .sort u
  | .const n us, _ => .const n us
  | .app f a, k => .app (instLift vs f k) (instLift vs a k)
  | .lam t b, k => .lam (instLift vs t k) (instLift vs b (k + 1))
  | .forallE t b, k => .forallE (instLift vs t k) (instLift vs b (k + 1))
  | .letE t v b, k => .letE (instLift vs t k) (instLift vs v k) (instLift vs b (k + 1))
  | .lit l, _ => .lit l
  | .proj s i e, k => .proj s i (instLift vs e k)

theorem instLift_eq_self (vs : List ConLeche.Expr) :
    ∀ (e : ConLeche.Expr) (k : Nat), e.looseBVarsBounded k = true → instLift vs e k = e := by
  intro e
  induction e <;> intro k h <;> simp_all [instLift, ConLeche.Expr.looseBVarsBounded]

theorem instLift_nil : ∀ (e : ConLeche.Expr) (k : Nat), instLift [] e k = e := by
  intro e
  induction e <;> intro k <;> simp_all [instLift]

/-- A term lifted past the values and `k` more binders is the term lifted
past the `k` binders, after the values' walk. -/
theorem instLift_lift (ws : List ConLeche.Expr) (k : Nat) :
    ∀ (v : ConLeche.Expr) (c : Nat),
      instLift ws (v.liftLooseBVars (k + ws.length) c) (k + c) = v.liftLooseBVars k c := by
  intro v
  induction v with
  | bvar i =>
    intro c
    simp only [ConLeche.Expr.liftLooseBVars]
    by_cases hic : i ≥ c
    · simp only [hic, ↓reduceIte, instLift, show ¬ i + (k + ws.length) < k + c by omega,
        show ¬ i + (k + ws.length) - (k + c) < ws.length by omega, ↓reduceDIte,
        ConLeche.Expr.bvar.injEq]
      omega
    · simp only [hic, ↓reduceIte, instLift, show i < k + c by omega]
  | lam t b iht ihb =>
    intro c
    simp only [ConLeche.Expr.liftLooseBVars, instLift, iht c, ← ihb (c + 1), Nat.add_assoc]
  | forallE t b iht ihb =>
    intro c
    simp only [ConLeche.Expr.liftLooseBVars, instLift, iht c, ← ihb (c + 1), Nat.add_assoc]
  | letE t w b iht ihw ihb =>
    intro c
    simp only [ConLeche.Expr.liftLooseBVars, instLift, iht c, ihw c, ← ihb (c + 1),
      Nat.add_assoc]
  | _ => intro c; simp_all [ConLeche.Expr.liftLooseBVars, instLift]

/-- **One more value is one more binder substituted**, at the depth past the
others. -/
theorem instLift_snoc (ws : List ConLeche.Expr) (v : ConLeche.Expr) :
    ∀ (e : ConLeche.Expr) (k : Nat),
      instLift (ws ++ [v]) e k = instLift ws (e.instantiate1Lift v (k + ws.length)) k := by
  intro e
  induction e with
  | bvar i =>
    intro k
    simp only [ConLeche.Expr.instantiate1Lift]
    by_cases hik : i < k
    · simp only [show ¬ i = k + ws.length by omega, show ¬ i > k + ws.length by omega,
        ↓reduceIte]
      simp [instLift, hik]
    · by_cases hin : i - k < ws.length
      · simp only [show ¬ i = k + ws.length by omega, show ¬ i > k + ws.length by omega,
          ↓reduceIte]
        simp only [instLift, hik, ↓reduceIte, List.length_append, List.length_singleton,
          show i - k < ws.length + 1 by omega, ↓reduceDIte, hin]
        rw [List.getElem_append_left hin]
      · by_cases heq : i = k + ws.length
        · subst heq
          have := instLift_lift ws k v 0
          simp only [Nat.add_zero] at this
          simp only [↓reduceIte, this]
          simp only [instLift, show ¬ k + ws.length < k by omega, ↓reduceIte]
          simp
        · simp only [heq, show i > k + ws.length by omega, ↓reduceIte]
          simp only [instLift, hik, ↓reduceIte, List.length_append, List.length_singleton,
            show ¬ i - k < ws.length + 1 by omega, ↓reduceDIte, show ¬ i - 1 < k by omega,
            show ¬ i - 1 - k < ws.length by omega, ConLeche.Expr.bvar.injEq]
          omega
  | lam t b iht ihb =>
    intro k
    simp only [instLift, ConLeche.Expr.instantiate1Lift, iht k, ihb (k + 1),
      Nat.add_right_comm k 1]
  | forallE t b iht ihb =>
    intro k
    simp only [instLift, ConLeche.Expr.instantiate1Lift, iht k, ihb (k + 1),
      Nat.add_right_comm k 1]
  | letE t w b iht ihw ihb =>
    intro k
    simp only [instLift, ConLeche.Expr.instantiate1Lift, iht k, ihw k, ihb (k + 1),
      Nat.add_right_comm k 1]
  | _ => intro k; simp_all [instLift, ConLeche.Expr.instantiate1Lift]

/-- **Substituting a telescope's binders one at a time is one walk**: the
per-domain effect of `instPisAtLift` (`instSeqLift`) is `instLift` at the
values innermost first. -/
theorem instSeqLift_eq_instLift :
    ∀ (vs : List ConLeche.Expr) (e : ConLeche.Expr),
      ConLeche.Expr.instSeqLift vs (vs.length - 1) e = instLift vs.reverse e 0
  | [], e => by simp [ConLeche.Expr.instSeqLift, instLift_nil]
  | a :: as, e => by
    simp only [ConLeche.Expr.instSeqLift, List.length_cons, Nat.add_sub_cancel,
      List.reverse_cons]
    rw [instSeqLift_eq_instLift as, instLift_snoc, List.length_reverse, Nat.zero_add]

/-! ## Instantiation at open values, InLean's walk -/

variable {fv : FVarId → Option ConLeche.Expr}

/-- The substitution reads, entry by entry, as the list `cvs` of (possibly
open) terms, and is in range. -/
structure OpenSubstReads (fv : FVarId → Option ConLeche.Expr) (subst : Array Expr)
    (cvs : List ConLeche.Expr) : Prop where
  len : cvs.length = subst.size
  entry : ∀ j (hj : j < subst.size), toExpr fv subst[j] = some (cvs[j]'(len ▸ hj))
  range : ∀ j (hj : j < subst.size), Expr.RangeOk subst[j]

theorem OpenSubstReads.reverse {subst : Array Expr} {cvs : List ConLeche.Expr}
    (hs : OpenSubstReads fv subst cvs) : OpenSubstReads fv subst.reverse cvs.reverse where
  len := by simp [hs.len]
  entry j hj := by
    have hj' : j < subst.size := by simpa using hj
    have hlen := hs.len
    rw [Array.getElem_reverse, hs.entry _ (by omega)]
    simp only [List.getElem_reverse, Option.some.injEq]
    congr 1; omega
  range j hj := by
    have hj' : j < subst.size := by simpa using hj
    rw [Array.getElem_reverse]; exact hs.range _ (by omega)

theorem instO_cut (hfv : FVarsOnly fv) (subst : Array Expr) (cvs : List ConLeche.Expr)
    {x : Expr} {k : Nat} {c : ConLeche.Expr} (hr : Expr.RangeOk x)
    (hc : x.looseBVarRange ≤ k) (h : toExpr fv x = some c) :
    toExpr fv (mapSpec (instF subst) x k) = some (instLift cvs c k) := by
  have hf : instF subst x k = some x := by simp [instF, hc]
  rw [mapSpec_eq_of_some hf, h, instLift_eq_self cvs c k
    (ConLeche.Expr.looseBVarsBounded_mono (by rw [Expr.looseBVarRange_eq hr] at hc; exact hc)
      (toExpr_bounded hfv x c h))]

theorem toExpr_mapSpec_instO (hfv : FVarsOnly fv) {subst : Array Expr} {cvs : List ConLeche.Expr}
    (hs : OpenSubstReads fv subst cvs) :
    ∀ (e : Expr), Expr.RangeOk e → ∀ (k : Nat) (c : ConLeche.Expr), toExpr fv e = some c →
      toExpr fv (mapSpec (instF subst) e k) = some (instLift cvs c k) := by
  intro e
  induction e with
  | bvar i =>
    intro hr k c h
    by_cases hcut : (Expr.bvar i).looseBVarRange ≤ k
    · exact instO_cut hfv subst cvs hr hcut h
    · simp only [toExpr, Option.some.injEq] at h
      subst h
      have hcut' := hcut
      rw [Expr.looseBVarRange_eq hr] at hcut'
      have hik : ¬ i < k := by simp only [rangeS] at hcut'; omega
      by_cases hin : i - k < subst.size
      · have hj : i - k < cvs.length := hs.len ▸ hin
        have hf : instF subst (.bvar i) k = some (EO.liftLooseBVars subst[i - k] 0 k) := by
          simp [instF, hcut, hik, hin]
        rw [mapSpec_eq_of_some hf, toExpr_liftLooseBVars hfv (hs.range _ hin) (hs.entry _ hin)]
        simp [instLift, hik, hj]
      · have hf : instF subst (.bvar i) k = some (.bvar (i - subst.size)) := by
          simp [instF, hcut, hik, hin]
        rw [mapSpec_eq_of_some hf]
        simp [toExpr, instLift, hik, hs.len, hin]
  | fvar id =>
    intro hr k c h
    exact instO_cut hfv subst cvs hr (by rw [Expr.looseBVarRange_eq hr]; simp [rangeS]) h
  | mvar m => intro _ k c h; simp [toExpr] at h
  | sort u =>
    intro hr k c h
    exact instO_cut hfv subst cvs hr (by rw [Expr.looseBVarRange_eq hr]; simp [rangeS]) h
  | const n us =>
    intro hr k c h
    exact instO_cut hfv subst cvs hr (by rw [Expr.looseBVarRange_eq hr]; simp [rangeS]) h
  | lit l =>
    intro hr k c h
    exact instO_cut hfv subst cvs hr (by rw [Expr.looseBVarRange_eq hr]; simp [rangeS]) h
  | app g a ihg iha =>
    intro hr k c h
    by_cases hcut : (Expr.app g a).looseBVarRange ≤ k
    · exact instO_cut hfv subst cvs hr hcut h
    · have hf : instF subst (.app g a) k = none := by simp [instF, hcut]
      simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨cg, hg, ca, ha, rfl⟩ := h
      simp [mapSpec, hf, toExpr, ihg hr.1 k cg hg, iha hr.2 k ca ha, instLift]
  | lam n t b bi iht ihb =>
    intro hr k c h
    by_cases hcut : (Expr.lam n t b bi).looseBVarRange ≤ k
    · exact instO_cut hfv subst cvs hr hcut h
    · have hf : instF subst (.lam n t b bi) k = none := by simp [instF, hcut]
      simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ct, ht, cb, hb, rfl⟩ := h
      simp [mapSpec, hf, toExpr, iht hr.1 k ct ht, ihb hr.2 (k + 1) cb hb, instLift]
  | forallE n t b bi iht ihb =>
    intro hr k c h
    by_cases hcut : (Expr.forallE n t b bi).looseBVarRange ≤ k
    · exact instO_cut hfv subst cvs hr hcut h
    · have hf : instF subst (.forallE n t b bi) k = none := by simp [instF, hcut]
      simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ct, ht, cb, hb, rfl⟩ := h
      simp [mapSpec, hf, toExpr, iht hr.1 k ct ht, ihb hr.2 (k + 1) cb hb, instLift]
  | letE n t v b nd iht ihv ihb =>
    intro hr k c h
    by_cases hcut : (Expr.letE n t v b nd).looseBVarRange ≤ k
    · exact instO_cut hfv subst cvs hr hcut h
    · have hf : instF subst (.letE n t v b nd) k = none := by simp [instF, hcut]
      simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ct, ht, cv, hv, cb, hb, rfl⟩ := h
      simp [mapSpec, hf, toExpr, iht hr.1 k ct ht, ihv hr.2.1 k cv hv, ihb hr.2.2 (k + 1) cb hb,
        instLift]
  | mdata m x ih =>
    intro hr k c h
    by_cases hcut : (Expr.mdata m x).looseBVarRange ≤ k
    · exact instO_cut hfv subst cvs hr hcut h
    · have hf : instF subst (.mdata m x) k = none := by simp [instF, hcut]
      simp only [toExpr] at h
      simp [mapSpec, hf, toExpr, ih hr k c h]
  | proj sn i x ih =>
    intro hr k c h
    by_cases hcut : (Expr.proj sn i x).looseBVarRange ≤ k
    · exact instO_cut hfv subst cvs hr hcut h
    · have hf : instF subst (.proj sn i x) k = none := by simp [instF, hcut]
      simp only [toExpr, Option.map_eq_some_iff] at h
      obtain ⟨cx, hx, rfl⟩ := h
      simp [mapSpec, hf, toExpr, ih hr k cx hx, instLift]

/-- **InLean's instantiation at open values** (in range) reads as `instLift`,
on a term in range. -/
theorem toExpr_instantiateO (hfv : FVarsOnly fv) {subst : Array Expr} {cvs : List ConLeche.Expr}
    (hs : OpenSubstReads fv subst cvs) {e : Expr} {c : ConLeche.Expr} (hr : Expr.RangeOk e)
    (h : toExpr fv e = some c) :
    toExpr fv (EO.instantiate e subst) = some (instLift cvs c 0) := by
  rw [instantiate_eq]
  split
  · rename_i hn
    by_cases hn0 : subst.size = 0
    · have : cvs = [] := List.eq_nil_of_length_eq_zero (hs.len.trans hn0)
      subst this
      rw [instLift_nil]; exact h
    · have hl : e.looseBVarRange = 0 := by
        have : (!e.hasLooseBVars) = true := by simpa [hn0] using hn
        simpa [Expr.hasLooseBVars] using this
      rw [Expr.looseBVarRange_eq hr] at hl
      have hb := toExpr_bounded hfv e c h
      rw [hl] at hb
      rw [instLift_eq_self cvs c 0 hb]; exact h
  · exact toExpr_mapSpec_instO hfv hs e hr 0 c h

/-- **InLean's `instantiateRev` at open values** reads as `instLift` at the
reversed list. -/
theorem toExpr_instantiateRevO (hfv : FVarsOnly fv) {subst : Array Expr}
    {cvs : List ConLeche.Expr} (hs : OpenSubstReads fv subst cvs) {e : Expr} {c : ConLeche.Expr}
    (hr : Expr.RangeOk e) (h : toExpr fv e = some c) :
    toExpr fv (EO.instantiateRev e subst) = some (instLift cvs.reverse c 0) := by
  rw [instantiateRev_eq]; exact toExpr_instantiateO hfv hs.reverse hr h

/-! ## The telescope -/

theorem RangeOk_binderDom : ∀ (k : Nat) {e d : Expr}, Expr.RangeOk e →
    InLean.binderDom k e = some d → Expr.RangeOk d := by
  intro k e
  induction e generalizing k with
  | mdata m x ih => intro d hr h; simp only [InLean.binderDom] at h; exact ih k hr h
  | forallE n t b bi _ ihb =>
    intro d hr h
    cases k with
    | zero => simp only [InLean.binderDom, Option.some.injEq] at h; subst h; exact hr.1
    | succ k => simp only [InLean.binderDom] at h; exact ihb k hr.2 h
  | _ => intro d _ h; cases k <;> simp [InLean.binderDom] at h

theorem binderDom_of_stripPis : ∀ (m k : Nat) {e : ConLeche.Expr} {bs : List ConLeche.Expr}
    {body : ConLeche.Expr}, e.stripPis m = some (bs, body) → k < m →
      ConLeche.Expr.binderDom k e = bs[k]? := by
  intro m
  induction m with
  | zero => intro k _ _ _ _ hk; omega
  | succ m ih =>
    intro k e bs body h hk
    match e, h with
    | .forallE A B, h =>
      simp only [ConLeche.Expr.stripPis] at h
      cases hs : B.stripPis m with
      | none => rw [hs] at h; cases h
      | some p =>
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq] at h
        cases h
        cases k with
        | zero => rfl
        | succ k =>
          simp only [ConLeche.Expr.binderDom, List.getElem?_cons_succ]
          exact ih k hs (by omega)

/-- **The field loop** substitutes the earlier fields' projections down the
telescope: field `i`'s body is the head domain after `i` of them. -/
theorem structProjBodiesGo_head (S : ConLeche.Name) : ∀ (i j n : Nat) (r : ConLeche.Expr)
    (l : List ConLeche.Expr), ConLeche.structProjBodiesGo S n j r = some l → i < n →
      ∃ rest, ConLeche.Expr.instPisAtLift
        ((List.range i).map fun m => ConLeche.structProjArgP S (j + m)) r =
          some (.forallE (l.getD i default) rest) := by
  intro i
  induction i with
  | zero =>
    intro j n r l h hn
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    cases r with
    | forallE fdom body =>
      simp only [ConLeche.structProjBodiesGo, Option.map_eq_some_iff] at h
      obtain ⟨l', -, rfl⟩ := h
      exact ⟨body, by simp [ConLeche.Expr.instPisAtLift]⟩
    | _ => simp [ConLeche.structProjBodiesGo] at h
  | succ i ih =>
    intro j n r l h hn
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    cases r with
    | forallE fdom body =>
      simp only [ConLeche.structProjBodiesGo, Option.map_eq_some_iff] at h
      obtain ⟨l', hl', rfl⟩ := h
      obtain ⟨rest, hrest⟩ := ih (j + 1) n' _ l' hl' (by omega)
      refine ⟨rest, ?_⟩
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [Nat.add_zero, ConLeche.Expr.instPisAtLift, Function.comp_def,
        List.getD_cons_succ]
      simpa [Nat.add_assoc, Nat.add_comm 1] using hrest
    | _ => simp [ConLeche.structProjBodiesGo] at h

/-- `projBodyArgs` reads as con-leche's parameter variables and earlier
fields' projections, in range where the parameter variables are. -/
theorem projBodyArgs_reads (T : Name) {nP : Nat} (i : Nat) (hnP : nP ≤ EO.maxBVarIdx) :
    OpenSubstReads (fun _ => none) (projBodyArgs T nP i)
      (ConLeche.structProjPs nP ++ (List.range i).map (ConLeche.structProjArgP (toName T))) where
  len := by simp [projBodyArgs, ConLeche.structProjPs]
  entry j hj := by
    by_cases hjn : j < nP
    · simp [projBodyArgs, hjn, ConLeche.structProjPs, toExpr]
    · simp only [projBodyArgs]
      rw [Array.getElem_append_right (by simp; omega),
        List.getElem_append_right (by simp [ConLeche.structProjPs]; omega)]
      simp [toExpr, ConLeche.structProjArgP, ConLeche.structProjPs]
  range j hj := by
    have hmax : EO.maxBVarIdx = 1048574 := rfl
    have hmr : maxRange = 1048575 := rfl
    by_cases hjn : j < nP
    · simp [projBodyArgs, hjn, Expr.RangeOk]
      omega
    · simp only [projBodyArgs]
      rw [Array.getElem_append_right (by simp; omega)]
      simp [Expr.RangeOk, hmr]

/-! ## The table test: enough binders -/

/-- con-leche's term binds at least `n` syntactic `∀`s (`hasPis`' twin). -/
@[expose] def cPis : Nat → ConLeche.Expr → Bool
  | 0, _ => true
  | n + 1, .forallE _ b => cPis n b
  | _ + 1, _ => false

theorem hasPis_tr : ∀ (n : Nat) {e : Expr} {ce : ConLeche.Expr}, toExprC e = some ce →
    hasPis n e = cPis n ce
  | 0, _, _, _ => by simp [hasPis, cPis]
  | n + 1, e, ce, h => by
    cases e with
    | mdata m x => exact hasPis_tr (n + 1) (e := x) h
    | forallE nm t b bi =>
      simp only [toExprC, toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ct, -, cb, hb, rfl⟩ := h
      simp only [hasPis, cPis]
      exact hasPis_tr n hb
    | fvar _ => simp [toExprC, toExpr] at h
    | bvar _ | mvar _ | sort _ | const _ _ | app _ _ | lam _ _ _ _ | letE _ _ _ _ _ | lit _
    | proj _ _ _ =>
      simp only [toExprC, toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq, Option.map_eq_some_iff] at h
      first
        | (obtain ⟨_, _, rfl⟩ := h; rfl)
        | (obtain ⟨_, _, _, _, rfl⟩ := h; rfl)
        | (obtain ⟨_, _, _, _, _, _, rfl⟩ := h; rfl)
        | (subst h; rfl)
        | (cases h)

/-- A value whose lifts are no `∀` (a variable, a projection). -/
@[expose] def NoPiLift (v : ConLeche.Expr) : Prop :=
  ∀ k c a b, ConLeche.Expr.liftLooseBVars k c v ≠ .forallE a b

theorem noPiLift_bvar (m : Nat) : NoPiLift (.bvar m) := by
  intro k c a b h; simp only [ConLeche.Expr.liftLooseBVars] at h; split at h <;> cases h

theorem noPiLift_proj (S : ConLeche.Name) (j : Nat) (x : ConLeche.Expr) : NoPiLift (.proj S j x) := by
  intro k c a b h; simp [ConLeche.Expr.liftLooseBVars] at h

theorem cPis_instantiate1Lift {v : ConLeche.Expr} (hv : NoPiLift v) :
    ∀ (n : Nat) (e : ConLeche.Expr) (d : Nat), cPis n (e.instantiate1Lift v d) = cPis n e
  | 0, _, _ => by simp [cPis]
  | n + 1, e, d => by
    cases e with
    | forallE a b =>
      simp only [ConLeche.Expr.instantiate1Lift, cPis]
      exact cPis_instantiate1Lift hv n b (d + 1)
    | bvar i =>
      simp only [ConLeche.Expr.instantiate1Lift]
      split
      · cases h : ConLeche.Expr.liftLooseBVars d 0 v with
        | forallE a b => exact absurd h (hv d 0 a b)
        | _ => rfl
      · split <;> rfl
    | _ => simp [ConLeche.Expr.instantiate1Lift, cPis]

theorem instPisAtLift_cPis : ∀ (as : List ConLeche.Expr), (∀ a ∈ as, NoPiLift a) →
    ∀ (ce : ConLeche.Expr) (n : Nat),
      match ConLeche.Expr.instPisAtLift as ce with
      | some r => cPis n r = cPis (as.length + n) ce
      | none => cPis (as.length + n) ce = false
  | [], _, ce, n => by simp [ConLeche.Expr.instPisAtLift]
  | a :: as, ha, ce, n => by
    cases ce with
    | forallE x body =>
      simp only [ConLeche.Expr.instPisAtLift, List.length_cons]
      have ih := instPisAtLift_cPis as (fun a h => ha a (List.mem_cons_of_mem _ h))
        (body.instantiate1Lift a) n
      rw [show as.length + 1 + n = (as.length + n) + 1 by omega]
      simp only [cPis]
      rw [cPis_instantiate1Lift (ha a List.mem_cons_self)] at ih
      exact ih
    | _ =>
      simp only [ConLeche.Expr.instPisAtLift, List.length_cons]
      rw [show as.length + 1 + n = (as.length + n) + 1 by omega]
      rfl

theorem go_isSome (S : ConLeche.Name) : ∀ (m j : Nat) (r : ConLeche.Expr),
    (ConLeche.structProjBodiesGo S m j r).isSome = cPis m r
  | 0, _, _ => by simp [ConLeche.structProjBodiesGo, cPis]
  | m + 1, j, r => by
    cases r with
    | forallE x body =>
      simp only [ConLeche.structProjBodiesGo, Option.isSome_map, cPis]
      rw [go_isSome S m (j + 1)]
      exact cPis_instantiate1Lift (noPiLift_proj _ _ _) m body 0
    | _ => simp [ConLeche.structProjBodiesGo, cPis]

theorem structProjPs_noPi (nP : Nat) : ∀ a ∈ ConLeche.structProjPs nP, NoPiLift a := by
  intro a ha
  simp only [ConLeche.structProjPs, List.mem_map] at ha
  obtain ⟨_, _, rfl⟩ := ha
  exact noPiLift_bvar _

/-- **InLean's table test is con-leche's bodies succeeding**: the constructor
type binds the parameters and the fields. -/
theorem hasPis_iff_structProjBodies {S : ConLeche.Name} {nP nF : Nat} {cty : Expr}
    {ccty : ConLeche.Expr} (hc : toExprC cty = some ccty) :
    hasPis (nP + nF) cty = (ConLeche.structProjBodies S nP nF ccty).isSome := by
  rw [hasPis_tr _ hc]
  have h := instPisAtLift_cPis (ConLeche.structProjPs nP) (structProjPs_noPi nP) ccty nF
  unfold ConLeche.structProjBodies
  have hlen : (ConLeche.structProjPs nP).length = nP := by simp [ConLeche.structProjPs]
  rw [hlen] at h
  cases hr : ConLeche.Expr.instPisAtLift (ConLeche.structProjPs nP) ccty with
  | none => rw [hr] at h; simp only at h; rw [h]; rfl
  | some r =>
    rw [hr] at h; simp only at h
    simp only [Option.isSome_map]
    rw [go_isSome, h]


/-! ## Field `i`'s body -/

theorem stripPis_of_cPis : ∀ (n : Nat) {e : ConLeche.Expr}, cPis n e = true →
    ∃ bs body, e.stripPis n = some (bs, body)
  | 0, e, _ => ⟨[], e, rfl⟩
  | n + 1, .forallE A B, h => by
    obtain ⟨bs, body, hb⟩ := stripPis_of_cPis n (e := B) h
    exact ⟨A :: bs, body, by simp [ConLeche.Expr.stripPis, hb]⟩
  | _ + 1, .bvar _, h | _ + 1, .fvar _ _, h | _ + 1, .sort _, h | _ + 1, .const _ _, h
  | _ + 1, .app _ _, h | _ + 1, .lam _ _, h | _ + 1, .letE _ _ _, h | _ + 1, .lit _, h
  | _ + 1, .proj _ _ _, h => by simp [cPis] at h

/-- **Field `i`'s body, as InLean builds it, is con-leche's**, given the
constructor type in range and the parameter variables in range
(`projBodyOk`). -/
theorem projBodyAt_tr {T : Name} {nP nF i : Nat} {cty : Expr} {ccty : ConLeche.Expr}
    {bodies : Array ConLeche.Expr} (hok : projBodyOk T nP i cty = true) (hr : Expr.RangeOk cty)
    (hc : toExprC cty = some ccty)
    (hs : ConLeche.structProjBodies (toName T) nP nF ccty = some bodies) (hi : i < nF) :
    ∃ b, projBodyAt T nP i cty = some b ∧ fvarS b = false ∧
      toExprC b = some (bodies.getD i default) := by
  have hnP : nP ≤ EO.maxBVarIdx := by
    unfold projBodyOk at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    exact hok.1
  -- con-leche's telescope and its domain `nP + i`
  have hpis : cPis (nP + nF) ccty = true := by
    rw [← hasPis_tr _ hc, hasPis_iff_structProjBodies (S := toName T) hc, hs]; rfl
  obtain ⟨bs, body, hstrip⟩ := stripPis_of_cPis _ hpis
  have hlen := ConLeche.Expr.stripPis_length _ hstrip
  have hD : bs[nP + i]? = some bs[nP + i] := List.getElem?_eq_getElem (by omega)
  -- InLean's domain reads as it
  have hrel := binderDom_tr fvarsOnly_none cty ccty (nP + i) hc
  rw [binderDom_of_stripPis _ _ hstrip (by omega), hD] at hrel
  cases hd : InLean.binderDom (nP + i) cty with
  | none => rw [hd] at hrel; simp [ORel] at hrel
  | some d =>
  rw [hd] at hrel
  have hrel' : toExpr (fun _ => none) d = some bs[nP + i] := hrel
  have hdr := RangeOk_binderDom _ hr hd
  -- con-leche's body: the head domain after the parameters and `i` fields
  unfold ConLeche.structProjBodies at hs
  cases hr' : ConLeche.Expr.instPisAtLift (ConLeche.structProjPs nP) ccty with
  | none => rw [hr'] at hs; cases hs
  | some r =>
  rw [hr'] at hs
  simp only [Option.map_eq_some_iff] at hs
  obtain ⟨l, hl, rfl⟩ := hs
  obtain ⟨rest, hrest⟩ := structProjBodiesGo_head (toName T) i 0 nF r l hl hi
  simp only [Nat.zero_add] at hrest
  have hargs : (ConLeche.structProjPs nP ++
      (List.range i).map (ConLeche.structProjArgP (toName T))).length = nP + i := by
    simp [ConLeche.structProjPs]
  have happ : ConLeche.Expr.instPisAtLift (ConLeche.structProjPs nP ++
      (List.range i).map (ConLeche.structProjArgP (toName T))) ccty =
        some (.forallE (l.getD i default) rest) := by
    rw [ConLeche.instPisAtLift_append, hr']; exact hrest
  obtain ⟨bodyR, hhead⟩ := ConLeche.Expr.instPisAtLift_head _ (mrem := nF - i - 1) happ
    (by rw [hargs, show nP + i + (nF - i - 1 + 1) = nP + nF by omega]; exact hstrip)
    (by rw [hargs]; exact hD)
  simp only [ConLeche.Expr.forallE.injEq] at hhead
  rw [instSeqLift_eq_instLift] at hhead
  have hb := toExpr_instantiateRevO fvarsOnly_none (projBodyArgs_reads T i hnP) hdr hrel'
  refine ⟨_, by simp only [projBodyAt, hd, Option.map_some]; rfl, fvarS_of_toExprC hb, ?_⟩
  refine hb.trans ?_
  rw [← hhead.1]
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

end InLeanProof
