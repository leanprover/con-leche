module

public import InLeanProof.EnvPresI
public import InLeanProof.Range
/- `Expr.hasLooseBVars`/`looseBVarRange` are read through the data field (as in `Ops.lean`). -/
import all Lean.Expr
import ConLeche.Verify.Subst

/-!
# A structure's projection bodies through the translation (task #451, lanes P3r, projBody, sync3)

InLean builds field `i`'s projection body at use (`projBodyAt`): field `i`'s
domain in the constructor type, instantiated in one walk at the parameters'
variables `bvar nP, …, bvar 1` and the subject's projections
`.proj T j (bvar 0)` of the fields before it (`projBodyArgs`).  con-leche's
install computes every body in one walk of the field telescope
(`structProjBodies`, task #495): field `i`'s raw domain substituted once by
`Expr.instantiateLift` at the same values, innermost first.  Both substitute
*open* values, lifted under binders; `toExpr_instantiate` reads instantiation
at closed values only.

**Main results.**
* `toExpr_instantiateRevO`: InLean's `instantiateRev` at open values in range
  reads as `Expr.instantiateLift` at the reversed list.
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

/-- A term whose loose variables are below `k` is left alone by
`instantiateLift` at depth `k`. -/
theorem instantiateLift_eq_self (vs : List ConLeche.Expr) :
    ∀ (e : ConLeche.Expr) (k : Nat), e.looseBVarsBounded k = true →
      ConLeche.Expr.instantiateLift e vs k = e := by
  intro e
  induction e <;> intro k h <;>
    simp_all [ConLeche.Expr.instantiateLift, ConLeche.Expr.looseBVarsBounded]

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
    toExpr fv (mapSpec (instF subst) x k) = some (ConLeche.Expr.instantiateLift c cvs k) := by
  have hf : instF subst x k = some x := by simp [instF, hc]
  rw [mapSpec_eq_of_some hf, h, instantiateLift_eq_self cvs c k
    (ConLeche.Expr.looseBVarsBounded_mono (by rw [Expr.looseBVarRange_eq hr] at hc; exact hc)
      (toExpr_bounded hfv x c h))]

theorem toExpr_mapSpec_instO (hfv : FVarsOnly fv) {subst : Array Expr} {cvs : List ConLeche.Expr}
    (hs : OpenSubstReads fv subst cvs) :
    ∀ (e : Expr), Expr.RangeOk e → ∀ (k : Nat) (c : ConLeche.Expr), toExpr fv e = some c →
      toExpr fv (mapSpec (instF subst) e k) = some (ConLeche.Expr.instantiateLift c cvs k) := by
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
        simp [ConLeche.Expr.instantiateLift, hik, hj]
      · have hf : instF subst (.bvar i) k = some (.bvar (i - subst.size)) := by
          simp [instF, hcut, hik, hin]
        rw [mapSpec_eq_of_some hf]
        simp [toExpr, ConLeche.Expr.instantiateLift, hik, hs.len, hin]
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
      simp [mapSpec, hf, toExpr, ihg hr.1 k cg hg, iha hr.2 k ca ha, ConLeche.Expr.instantiateLift]
  | lam n t b bi iht ihb =>
    intro hr k c h
    by_cases hcut : (Expr.lam n t b bi).looseBVarRange ≤ k
    · exact instO_cut hfv subst cvs hr hcut h
    · have hf : instF subst (.lam n t b bi) k = none := by simp [instF, hcut]
      simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ct, ht, cb, hb, rfl⟩ := h
      simp [mapSpec, hf, toExpr, iht hr.1 k ct ht, ihb hr.2 (k + 1) cb hb, ConLeche.Expr.instantiateLift]
  | forallE n t b bi iht ihb =>
    intro hr k c h
    by_cases hcut : (Expr.forallE n t b bi).looseBVarRange ≤ k
    · exact instO_cut hfv subst cvs hr hcut h
    · have hf : instF subst (.forallE n t b bi) k = none := by simp [instF, hcut]
      simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ct, ht, cb, hb, rfl⟩ := h
      simp [mapSpec, hf, toExpr, iht hr.1 k ct ht, ihb hr.2 (k + 1) cb hb, ConLeche.Expr.instantiateLift]
  | letE n t v b nd iht ihv ihb =>
    intro hr k c h
    by_cases hcut : (Expr.letE n t v b nd).looseBVarRange ≤ k
    · exact instO_cut hfv subst cvs hr hcut h
    · have hf : instF subst (.letE n t v b nd) k = none := by simp [instF, hcut]
      simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ct, ht, cv, hv, cb, hb, rfl⟩ := h
      simp [mapSpec, hf, toExpr, iht hr.1 k ct ht, ihv hr.2.1 k cv hv, ihb hr.2.2 (k + 1) cb hb,
        ConLeche.Expr.instantiateLift]
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
      simp [mapSpec, hf, toExpr, ih hr k cx hx, ConLeche.Expr.instantiateLift]

/-- **InLean's instantiation at open values** (in range) reads as master's `Expr.instantiateLift`,
on a term in range. -/
theorem toExpr_instantiateO (hfv : FVarsOnly fv) {subst : Array Expr} {cvs : List ConLeche.Expr}
    (hs : OpenSubstReads fv subst cvs) {e : Expr} {c : ConLeche.Expr} (hr : Expr.RangeOk e)
    (h : toExpr fv e = some c) :
    toExpr fv (EO.instantiate e subst) = some (ConLeche.Expr.instantiateLift c cvs 0) := by
  rw [instantiate_eq]
  split
  · rename_i hn
    by_cases hn0 : subst.size = 0
    · have : cvs = [] := List.eq_nil_of_length_eq_zero (hs.len.trans hn0)
      subst this
      rw [ConLeche.Expr.instantiateLift_nil]; exact h
    · have hl : e.looseBVarRange = 0 := by
        have : (!e.hasLooseBVars) = true := by simpa [hn0] using hn
        simpa [Expr.hasLooseBVars] using this
      rw [Expr.looseBVarRange_eq hr] at hl
      have hb := toExpr_bounded hfv e c h
      rw [hl] at hb
      rw [instantiateLift_eq_self cvs c 0 hb]; exact h
  · exact toExpr_mapSpec_instO hfv hs e hr 0 c h

/-- **InLean's `instantiateRev` at open values** reads as `Expr.instantiateLift` at the
reversed list. -/
theorem toExpr_instantiateRevO (hfv : FVarsOnly fv) {subst : Array Expr}
    {cvs : List ConLeche.Expr} (hs : OpenSubstReads fv subst cvs) {e : Expr} {c : ConLeche.Expr}
    (hr : Expr.RangeOk e) (h : toExpr fv e = some c) :
    toExpr fv (EO.instantiateRev e subst) = some (ConLeche.Expr.instantiateLift c cvs.reverse 0) := by
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

/-- **The field loop**: entry `i` is the telescope's raw domain `i`,
substituted at the earlier fields' projections (innermost first) before the
values `vs`. -/
theorem structProjBodiesGo_entry (S : ConLeche.Name) : ∀ (i j n : Nat) (r : ConLeche.Expr)
    (vs l : List ConLeche.Expr), ConLeche.structProjBodiesGo S vs n j r = some l → i < n →
      ∃ dom, ConLeche.Expr.binderDom i r = some dom ∧
        l.getD i default = ConLeche.Expr.instantiateLift dom
          (((List.range i).map fun m => ConLeche.structProjArgP S (j + m)).reverse ++ vs) := by
  intro i
  induction i with
  | zero =>
    intro j n r vs l h hn
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    cases r with
    | forallE fdom body =>
      simp only [ConLeche.structProjBodiesGo, Option.map_eq_some_iff] at h
      obtain ⟨l', -, rfl⟩ := h
      exact ⟨fdom, rfl, by simp⟩
    | _ => simp [ConLeche.structProjBodiesGo] at h
  | succ i ih =>
    intro j n r vs l h hn
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    cases r with
    | forallE fdom body =>
      simp only [ConLeche.structProjBodiesGo, Option.map_eq_some_iff] at h
      obtain ⟨l', hl', rfl⟩ := h
      obtain ⟨dom, hdom, hent⟩ := ih (j + 1) n' body _ l' hl' (by omega)
      refine ⟨dom, by simpa [ConLeche.Expr.binderDom] using hdom, ?_⟩
      rw [List.getD_cons_succ, hent, List.range_succ_eq_map, List.map_cons, List.map_map]
      simp [Function.comp_def, Nat.add_assoc, Nat.add_comm 1]
    | _ => simp [ConLeche.structProjBodiesGo] at h

theorem binderDom_add_of_stripPis : ∀ (m k : Nat) {e : ConLeche.Expr} {bs : List ConLeche.Expr}
    {body : ConLeche.Expr}, e.stripPis m = some (bs, body) →
      ConLeche.Expr.binderDom (m + k) e = ConLeche.Expr.binderDom k body := by
  intro m
  induction m with
  | zero => intro k e bs body h; simp only [ConLeche.Expr.stripPis, Option.some.injEq] at h; cases h; simp
  | succ m ih =>
    intro k e bs body h
    match e, h with
    | .forallE A B, h =>
      simp only [ConLeche.Expr.stripPis] at h
      cases hs : B.stripPis m with
      | none => rw [hs] at h; cases h
      | some p =>
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq] at h
        cases h
        rw [show m + 1 + k = (m + k) + 1 by omega]
        simp only [ConLeche.Expr.binderDom]
        exact ih k hs

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

theorem go_isSome (S : ConLeche.Name) : ∀ (vs : List ConLeche.Expr) (m j : Nat) (r : ConLeche.Expr),
    (ConLeche.structProjBodiesGo S vs m j r).isSome = cPis m r
  | _, 0, _, _ => by simp [ConLeche.structProjBodiesGo, cPis]
  | vs, m + 1, j, r => by
    cases r with
    | forallE x body =>
      simp only [ConLeche.structProjBodiesGo, Option.isSome_map, cPis]
      exact go_isSome S _ m (j + 1) body
    | _ => simp [ConLeche.structProjBodiesGo, cPis]

theorem cPis_add_of_stripPis : ∀ (m n : Nat) {e : ConLeche.Expr},
    cPis (m + n) e = match e.stripPis m with
      | some (_, r) => cPis n r
      | none => false
  | 0, n, e => by simp [ConLeche.Expr.stripPis]
  | m + 1, n, e => by
    rw [show m + 1 + n = (m + n) + 1 by omega]
    cases e with
    | forallE A B =>
      simp only [cPis, ConLeche.Expr.stripPis]
      rw [cPis_add_of_stripPis m n]
      cases B.stripPis m <;> rfl
    | _ => simp [cPis, ConLeche.Expr.stripPis]

/-- **InLean's table test is con-leche's bodies succeeding**: the constructor
type binds the parameters and the fields. -/
theorem hasPis_iff_structProjBodies {S : ConLeche.Name} {nP nF : Nat} {cty : Expr}
    {ccty : ConLeche.Expr} (hc : toExprC cty = some ccty) :
    hasPis (nP + nF) cty = (ConLeche.structProjBodies S nP nF ccty).isSome := by
  rw [hasPis_tr _ hc, cPis_add_of_stripPis]
  unfold ConLeche.structProjBodies
  cases ccty.stripPis nP with
  | none => rfl
  | some p => simp only [Option.isSome_map]; rw [go_isSome]


/-! ## Field `i`'s body -/

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
  -- con-leche's telescope: the parameters stripped, the field loop
  unfold ConLeche.structProjBodies at hs
  cases hsp : ccty.stripPis nP with
  | none => rw [hsp] at hs; cases hs
  | some pr =>
  obtain ⟨ps, r⟩ := pr
  rw [hsp] at hs
  simp only [Option.map_eq_some_iff] at hs
  obtain ⟨l, hl, rfl⟩ := hs
  obtain ⟨dom, hdom, hent⟩ := structProjBodiesGo_entry (toName T) i 0 nF r _ l hl hi
  -- InLean's domain reads as it
  have hrel := binderDom_tr fvarsOnly_none cty ccty (nP + i) hc
  rw [binderDom_add_of_stripPis _ _ hsp, hdom] at hrel
  cases hd : InLean.binderDom (nP + i) cty with
  | none => rw [hd] at hrel; simp [ORel] at hrel
  | some d =>
  rw [hd] at hrel
  have hrel' : toExpr (fun _ => none) d = some dom := hrel
  have hdr := RangeOk_binderDom _ hr hd
  have hb := toExpr_instantiateRevO fvarsOnly_none (projBodyArgs_reads T i hnP) hdr hrel'
  refine ⟨_, by simp only [projBodyAt, hd, Option.map_some]; rfl, fvarS_of_toExprC hb, ?_⟩
  refine hb.trans ?_
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD, hent]
  simp [List.reverse_append]

end InLeanProof
