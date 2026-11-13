module

public import InLeanProof.WalksDefeq
public import InLeanProof.IotaViews
public import InLeanProof.Statement
/- `ConstantInfo.type`/`levelParams` and the derived `BEq` of `QuotKind` are not exposed: the
proof reads them as projections of `toConstantVal`. -/
import all Lean.Declaration
/- `FEnv.push` (not exposed in `InLean/Push.lean`): its flags (`LitFlagsI.push`). -/
import all InLean.Push

/-!
# O4: InLean's at-use readers against con-leche's install (task #451, lane P3a)

The core walks read the environment through six named hypotheses:
`EnvRelI`, `EnvDomI`, `EnvDefnI` (`WalksWhnf.lean`, `StateOpsI.lean`),
`EnvViewI` (`WalksIota.lean`), `EnvRecI` (`IotaViews.lean`) and `DefeqEnvI`
(`WalksDefeq.lean`).  This file states **one relation** between InLean's
environment `fe` and con-leche's `L`, `EnvPresI fe L`, proves each of the
six from it (`envRelI_of`, `envDomI_of`, `envDefnI_of`, `envViewI_of`,
`envRecI_of`, `defeqEnvI_of`), and proves it is kept by adding a declaration
group, the shape the assembly (P4) folds over:

* `EnvPresI fe L` is pointwise.  At every name InLean finds an entry exactly
  where con-leche finds one at the translated name, and the two are related
  (`EntryRelI`: the name, levels and type; a definition's value and hint; an
  inductive's capabilities as `capsOf` reads them; a constructor's counts; a
  recursor's counts, K flag and rules with their firing mode as `recFireAt`
  computes it; the quotient package as InLean's views read it).  Every
  structure's projection table is related to what InLean's `findTable?`/
  `projBodyAt` read off the former and its constructor (`TableRelI`), and
  every stored table belongs to a stored constant.
* `presI_push`: adding a group of fresh constants keeps the relation once the
  group's own names are related (its installed constants and tables against
  Lean's entries).  Old names keep their entries: a former's constructors are
  stored (`EntryRelI`'s `inductInfo` clause), so the table readers read the
  same after the push.
* Per kind: `presI_axiom` (a safe axiom, `sorryAx` included: con-leche
  installs nothing for it and InLean hides it unless `coreAxioms`), `presI_defn`,
  `presI_thm`, `presI_opaque` (safe ones); the quotient record and an inductive block are
  stated (`QuotGroupPres`, `IndGroupPres`) with the facts InLean checks as
  premises, for a later lane.
* `presI_empty`: an environment InLean finds nothing in is related to
  `Env.empty`.
* **What a check sees** (rulings of 2026-11-08).  The relation reads
  `FEnv.find?`, which hides `sorryAx` at con-leche's policy and, in a safe
  check, every `unsafe` or `partial` constant (`FEnv.sees`): so it covers the
  safe constants only, and Lean's `sorryAx` stands against nothing on
  con-leche's side.  Inside an inductive block's job the members are marked
  (`FEnv.pending`): a marked former has no table, as in master's staged
  environments, so a former's constructors need be stored only when it is
  unmarked.
-/

public section

namespace InLeanProof

open Lean InLean

/-! ## The relation -/

/-- A recursor rule against con-leche's: `RuleRel` and the right-hand side a
stored term. -/
@[expose] def RuleRelS (fire : InLean.RecRuleFire) (rl : Lean.RecursorRule)
    (crl : ConLeche.RecRule) : Prop :=
  RuleRel fire rl crl ∧ StoredT rl.rhs crl.rhs

/-- A recursor (`isQuot`: a quotient eliminator) against con-leche's record:
the counts read off Lean's, the K flag, and the rules with their firing mode
as InLean computes it at use. -/
@[expose] def RecRelI (rv : RecursorVal) (isQuot : Bool) (cci : ConLeche.ConstantInfo) : Prop :=
  ∃ ccv crules, cci = .recInfo ccv (majorIdxOf rv) (rulePrefixOf rv) rv.k crules ∧
    CVRel rv.toConstantVal ccv ∧ LRel (RuleRelS (recFireAt rv isQuot)) rv.rules crules

/-- **Lean's entry against con-leche's at the translated name.**  An
`opaque` is stored by con-leche as an axiom, a theorem by its statement; the
quotient package as InLean's views read it (`indView?`, `ctorView?`,
`recAt?`).  A former's capabilities are `capsOf`'s; its constructors are
stored, or it is a member of the block being checked (`FEnv.pending`, which
has no table), so that what the table readers read does not change when the
environment grows. -/
@[expose] def EntryRelI (fe : InLean.FEnv) : Lean.ConstantInfo → ConLeche.ConstantInfo → Prop
  | .axiomInfo v, .axiomInfo ccv => CVRel v.toConstantVal ccv
  | .opaqueInfo v, .axiomInfo ccv => CVRel v.toConstantVal ccv
  | .thmInfo v, .thmInfo ccv => CVRel v.toConstantVal ccv
  | .defnInfo v, .defnInfo ccv cval h =>
    CVRel v.toConstantVal ccv ∧ StoredT v.value cval ∧ h = trHint v.hints
  | .inductInfo v, .indInfo ccv caps =>
    CVRel v.toConstantVal ccv ∧ caps = toCaps (capsOf v) ∧
      (fe.isPending v.name = true ∨ ∀ c ∈ v.ctors, (fe.find? c).isSome)
  | .ctorInfo v, .ctorInfo ccv nP nF T =>
    CVRel v.toConstantVal ccv ∧ nP = v.numParams ∧ nF = v.numFields ∧ T = toName v.induct
  | .recInfo rv, cci => RecRelI rv false cci
  | .quotInfo q, cci =>
    match q.kind with
    | .type => ∃ ccv, cci = .indInfo ccv {} ∧ CVRel q.toConstantVal ccv
    | .ctor => ∃ ccv, cci = .ctorInfo ccv 2 1 ConLeche.quotName ∧ CVRel q.toConstantVal ccv
    | _ => ∃ rv, quotRecVal q (quotRuleRhs q) = some rv ∧ RecRelI rv true cci
  | _, _ => False

/-- **A structure's projection table against InLean's readers**: none where
`findTable?` finds none; otherwise the table InLean reads off the former
and its one constructor (`findProj?`), field by field the body
`projBodyAt` builds, a term without free variables translating to the
stored one, the structure not a member of the block being checked. -/
@[expose] def TableRelI (fe : InLean.FEnv) (T : Name) : Option ConLeche.ProjTable → Prop
  | none => fe.findTable? T = none
  | some tbl => ∃ v c cv, fe.find? T = some (.inductInfo v) ∧ fe.isPending v.name = false ∧
      v.ctors = [c] ∧ v.numIndices = 0 ∧
      fe.find? c = some (.ctorInfo cv) ∧ hasPis (v.numParams + cv.numFields) cv.type = true ∧
      tbl.structName = toName T ∧ tbl.levelParams = v.levelParams.map toName ∧
      tbl.numParams = v.numParams ∧ tbl.ctor = toName c ∧ tbl.numFields = cv.numFields ∧
      ∀ i < cv.numFields, ∃ b, projBodyAt T v.numParams i cv.type = some b ∧ fvarS b = false ∧
        toExprC b = some (tbl.bodies.getD i default)

/-- **O4's relation: con-leche's environment `L` presents what InLean reads
off `fe`.**  Pointwise: InLean finds an entry at `n` exactly where con-leche
finds one at `toName n` (every con-leche name is one, `fromName`), related by
`EntryRelI`; every structure's table is related by `TableRelI`; every stored
table belongs to a stored constant (so a table is never revealed by a later
push).  Kept by the install of each declaration group (`presI_push` and the
per-kind lemmas). -/
structure EnvPresI (fe : InLean.FEnv) (L : ConLeche.Env) : Prop where
  entry : ∀ n ci, fe.find? n = some ci →
    ∃ cci, L.find? (toName n) = some cci ∧ EntryRelI fe ci cci
  none : ∀ n, fe.find? n = none → L.find? (toName n) = none
  table : ∀ T, TableRelI fe T (L.findTable? (toName T))
  tabNames : ∀ tbl ∈ L.tables, (L.find? tbl.structName).isSome = true

/-! ## Basic facts -/

/-- `FEnv.find?` is Lean's lookup filtered by `FEnv.sees`. -/
theorem FEnv.find?_eq_filter (fe : InLean.FEnv) (n : Name) :
    fe.find? n = (fe.env.find? n).filter (fe.sees n) := by
  unfold InLean.FEnv.find?
  cases fe.env.find? n <;> rfl

/-- Two environments with the same policy and safety see the same constant
where they store the same. -/
theorem FEnv.find?_congr {fe fe' : InLean.FEnv} (hc : fe'.coreAxioms = fe.coreAxioms)
    (hs : fe'.safety = fe.safety) {n : Name} (h : fe'.env.find? n = fe.env.find? n) :
    fe'.find? n = fe.find? n := by
  have he : fe'.sees n = fe.sees n := by
    funext ci; simp only [InLean.FEnv.sees, InLean.seesAt, hc, hs]
  simp only [FEnv.find?_eq_filter, h, he]

theorem toName_fromName : ∀ n : ConLeche.Name, toName (fromName n) = n
  | .anonymous => rfl
  | .str p s => by simp [toName, fromName, toName_fromName p]
  | .num p n => by simp [toName, fromName, toName_fromName p]

theorem toCaps_empty : toCaps ({} : InLean.IndCaps) = ({} : ConLeche.IndCaps) := rfl

theorem quotRecVal_cv {q : QuotVal} {rhs : Expr} {rv : RecursorVal}
    (h : quotRecVal q rhs = some rv) : rv.toConstantVal = q.toConstantVal := by
  revert h; unfold quotRecVal
  repeat' split
  all_goals intro h; simp only [Option.some.injEq, reduceCtorEq] at h
  all_goals first | (subst h; rfl) | simp at h

theorem ci_cv_type (ci : Lean.ConstantInfo) : ci.type = ci.toConstantVal.type := by
  cases ci <;> rfl

theorem ci_cv_lps (ci : Lean.ConstantInfo) : ci.levelParams = ci.toConstantVal.levelParams := by
  cases ci <;> rfl

theorem RecRelI.cv {rv : RecursorVal} {b : Bool} {cci : ConLeche.ConstantInfo}
    (h : RecRelI rv b cci) : CVRel rv.toConstantVal cci.toConstantVal := by
  obtain ⟨ccv, crules, rfl, hcv, -⟩ := h; exact hcv

/-- Every related pair relates the name, levels and type. -/
theorem EntryRelI.cv {fe : InLean.FEnv} {ci : Lean.ConstantInfo}
    {cci : ConLeche.ConstantInfo} (h : EntryRelI fe ci cci) :
    CVRel ci.toConstantVal cci.toConstantVal := by
  cases ci with
  | quotInfo q =>
    simp only [EntryRelI] at h
    split at h
    · obtain ⟨ccv, rfl, h2⟩ := h; exact h2
    · obtain ⟨ccv, rfl, h2⟩ := h; exact h2
    · obtain ⟨rv, hq, hr⟩ := h
      have := RecRelI.cv hr; rwa [quotRecVal_cv hq] at this
  | recInfo rv => exact RecRelI.cv h
  | _ => cases cci <;> simp only [EntryRelI] at h <;> first | exact h | exact h.1

/-! ## Inversions: what Lean's entry is, given con-leche's -/

section Inv

variable {fe : InLean.FEnv} {ci : Lean.ConstantInfo}

theorem EntryRelI.inv_defn {ccv : ConLeche.ConstantVal} {cval : ConLeche.Expr}
    {h : ConLeche.ReducibilityHint} (hr : EntryRelI fe ci (.defnInfo ccv cval h)) :
    ∃ v, ci = .defnInfo v ∧ CVRel v.toConstantVal ccv ∧ StoredT v.value cval ∧ h = trHint v.hints := by
  cases ci with
  | defnInfo v => exact ⟨v, rfl, hr⟩
  | quotInfo q =>
    simp only [EntryRelI] at hr
    split at hr
    · obtain ⟨_, h1, -⟩ := hr; cases h1
    · obtain ⟨_, h1, -⟩ := hr; cases h1
    · obtain ⟨_, -, _, _, h1, -⟩ := hr; cases h1
  | recInfo rv => obtain ⟨_, _, h1, -⟩ := hr; cases h1
  | _ => simp only [EntryRelI] at hr

theorem EntryRelI.inv_ind {ccv : ConLeche.ConstantVal} {caps : ConLeche.IndCaps}
    (hr : EntryRelI fe ci (.indInfo ccv caps)) :
    (∃ v, ci = .inductInfo v ∧ CVRel v.toConstantVal ccv ∧ caps = toCaps (capsOf v) ∧
      (fe.isPending v.name = true ∨ ∀ c ∈ v.ctors, (fe.find? c).isSome)) ∨
    (∃ q, ci = .quotInfo q ∧ q.kind = .type ∧ caps = {} ∧ CVRel q.toConstantVal ccv) := by
  cases ci with
  | inductInfo v => exact .inl ⟨v, rfl, hr⟩
  | quotInfo q =>
    simp only [EntryRelI] at hr
    split at hr
    · rename_i hk
      obtain ⟨_, h1, h2⟩ := hr
      simp only [ConLeche.ConstantInfo.indInfo.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      exact .inr ⟨q, rfl, hk, rfl, h2⟩
    · obtain ⟨_, h1, -⟩ := hr; cases h1
    · obtain ⟨_, -, _, _, h1, -⟩ := hr; cases h1
  | recInfo rv => obtain ⟨_, _, h1, -⟩ := hr; cases h1
  | _ => simp only [EntryRelI] at hr

theorem EntryRelI.inv_ctor {ccv : ConLeche.ConstantVal} {nP nF : Nat} {T : ConLeche.Name}
    (hr : EntryRelI fe ci (.ctorInfo ccv nP nF T)) :
    (∃ v, ci = .ctorInfo v ∧ CVRel v.toConstantVal ccv ∧ nP = v.numParams ∧ nF = v.numFields ∧
      T = toName v.induct) ∨
    (∃ q, ci = .quotInfo q ∧ q.kind = .ctor ∧ nP = 2 ∧ nF = 1 ∧ T = ConLeche.quotName ∧
      CVRel q.toConstantVal ccv) := by
  cases ci with
  | ctorInfo v => exact .inl ⟨v, rfl, hr⟩
  | quotInfo q =>
    simp only [EntryRelI] at hr
    split at hr
    · obtain ⟨_, h1, -⟩ := hr; cases h1
    · rename_i hk
      obtain ⟨_, h1, h2⟩ := hr
      simp only [ConLeche.ConstantInfo.ctorInfo.injEq] at h1
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
      exact .inr ⟨q, rfl, hk, rfl, rfl, rfl, h2⟩
    · obtain ⟨_, -, _, _, h1, -⟩ := hr; cases h1
  | recInfo rv => obtain ⟨_, _, h1, -⟩ := hr; cases h1
  | _ => simp only [EntryRelI] at hr

theorem EntryRelI.inv_rec {cci : ConLeche.ConstantInfo} (hr : EntryRelI fe ci cci)
    {ccv : ConLeche.ConstantVal} {mI rP : Nat} {isK : Bool} {rules : List ConLeche.RecRule}
    (hc : cci = .recInfo ccv mI rP isK rules) :
    (∃ rv, ci = .recInfo rv ∧ RecRelI rv false cci) ∨
    (∃ q rv, ci = .quotInfo q ∧ quotRecVal q (quotRuleRhs q) = some rv ∧ RecRelI rv true cci) := by
  subst hc
  cases ci with
  | recInfo rv => exact .inl ⟨rv, rfl, hr⟩
  | quotInfo q =>
    simp only [EntryRelI] at hr
    split at hr
    · obtain ⟨_, h1, -⟩ := hr; cases h1
    · obtain ⟨_, h1, -⟩ := hr; cases h1
    · obtain ⟨rv, hq, h⟩ := hr
      exact .inr ⟨q, rv, rfl, hq, h⟩
  | _ => simp only [EntryRelI] at hr

end Inv

/-! ## The six hypotheses -/

section Six

variable {fe : InLean.FEnv} {L : ConLeche.Env}

/-- **`EnvDomI`** from the relation. -/
theorem envDomI_of (hP : EnvPresI fe L) (hl : LitFlagsI fe) : EnvDomI fe L := by
  refine EnvDomI.of (fun n => ?_) hl
  cases hf : fe.find? n with
  | none => rw [hP.none n hf]; rfl
  | some ci => obtain ⟨cci, hL, -⟩ := hP.entry n ci hf; rw [hL]; rfl

/-- **`EnvDefnI`** from the relation. -/
theorem envDefnI_of (hP : EnvPresI fe L) : EnvDefnI fe L := by
  intro n cv v h hL
  unfold InLean.FEnv.defnView?
  cases hf : fe.find? n with
  | none => rw [hP.none n hf] at hL; cases hL
  | some ci =>
    obtain ⟨cci, hL', hr⟩ := hP.entry n ci hf
    rw [hL] at hL'; cases hL'
    obtain ⟨w, rfl, -⟩ := hr.inv_defn
    rfl

/-- The definition view through the relation. -/
theorem defnView_rel (hP : EnvPresI fe L) {n : Name} {cv : ConstantVal} {v : Expr}
    {h : ReducibilityHints} (hd : fe.defnView? n = some (cv, v, h)) :
    ∃ ccv cval, L.find? (toName n) = some (.defnInfo ccv cval (trHint h)) ∧ CVRel cv ccv ∧
      StoredT v cval := by
  unfold InLean.FEnv.defnView? at hd
  cases hf : fe.find? n with
  | none => rw [hf] at hd; cases hd
  | some ci =>
    rw [hf] at hd
    cases ci with
    | defnInfo w =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl, rfl⟩ := hd
      obtain ⟨cci, hL, hr⟩ := hP.entry n _ hf
      cases cci <;> simp only [EntryRelI] at hr
      obtain ⟨h1, h2, rfl⟩ := hr
      exact ⟨_, _, hL, h1, h2⟩
    | _ => cases hd

/-- A definition is absent from InLean's view exactly where con-leche stores none. -/
theorem defnView_none (hP : EnvPresI fe L) {n : Name} (hd : fe.defnView? n = none) :
    ∀ ccv cval h, L.find? (toName n) ≠ some (.defnInfo ccv cval h) := by
  intro ccv cval h hL
  have := envDefnI_of hP n ccv cval h hL
  rw [hd] at this; cases this

theorem quotRecVal_kind {q : QuotVal} {rhs : Expr} {rv : RecursorVal}
    (h : quotRecVal q rhs = some rv) : q.kind ≠ .type ∧ q.kind ≠ .ctor := by
  revert h; unfold quotRecVal
  cases q.kind <;> simp (config := { decide := true })

/-- The recursor view through the relation. -/
theorem recAt_rel (hP : EnvPresI fe L) {n : Name} {rv : RecursorVal} {q : Bool}
    (h : fe.recAt? n = some (rv, q)) : ∃ cci, L.find? (toName n) = some cci ∧ RecRelI rv q cci := by
  unfold InLean.FEnv.recAt? at h
  cases hf : fe.find? n with
  | none => rw [hf] at h; cases h
  | some ci =>
    rw [hf] at h
    obtain ⟨cci, hL, hr⟩ := hP.entry n ci hf
    cases ci with
    | recInfo w =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨cci, hL, hr⟩
    | quotInfo q' =>
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨rv', hq, rfl, rfl⟩ := h
      have hk := quotRecVal_kind hq
      simp only [EntryRelI] at hr
      split at hr
      · exact absurd ‹_› hk.1
      · exact absurd ‹_› hk.2
      · obtain ⟨rv'', hq', hr'⟩ := hr
        rw [hq] at hq'; cases hq'
        exact ⟨cci, hL, hr'⟩
    | _ => cases h

/-- A recursor is absent from InLean's view exactly where con-leche stores none. -/
theorem recAt_none (hP : EnvPresI fe L) {n : Name} (h : fe.recAt? n = none) :
    ∀ ccv mI rP isK rules, L.find? (toName n) ≠ some (.recInfo ccv mI rP isK rules) := by
  intro ccv mI rP isK rules hL
  unfold InLean.FEnv.recAt? at h
  cases hf : fe.find? n with
  | none => rw [hP.none n hf] at hL; cases hL
  | some ci =>
    rw [hf] at h
    obtain ⟨cci, hL', hr⟩ := hP.entry n ci hf
    rw [hL] at hL'; cases hL'
    rcases hr.inv_rec rfl with ⟨rv, rfl, -⟩ | ⟨q, rv, rfl, hq, -⟩
    · cases h
    · simp [hq] at h

theorem LRel.mono {α β : Type} {R S : α → β → Prop} (hRS : ∀ a b, R a b → S a b) :
    ∀ {as : List α} {bs : List β}, LRel R as bs → LRel S as bs
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons (hRS _ _ h) (LRel.mono hRS hs)

/-- The rule found for a constructor, through the stored-rule relation. -/
theorem find_rule_relS {fire : InLean.RecRuleFire} :
    ∀ {rules : List Lean.RecursorRule} {crules : List ConLeche.RecRule},
      LRel (RuleRelS fire) rules crules → ∀ (cj : Name) (rl : Lean.RecursorRule),
      rules.find? (fun r' => r'.ctor == cj) = some rl →
      ∃ crl, crules.find? (fun r' => r'.ctor == toName cj) = some crl ∧ RuleRelS fire rl crl
  | [], [], .nil, _, _, h => by cases h
  | rl :: rules, crl :: crules, .cons h hs, cj, rl', hf => by
    simp only [List.find?_cons] at hf ⊢
    rw [h.1.1, toName_beq]
    cases hc : rl.ctor == cj with
    | true => rw [hc] at hf; cases hf; exact ⟨crl, rfl, h⟩
    | false => rw [hc] at hf; exact find_rule_relS hs cj rl' hf

/-- **`EnvRecI`** from the relation. -/
theorem envRecI_of (hP : EnvPresI fe L) : EnvRecI fe L where
  recv := by
    intro n rv q h
    obtain ⟨cci, hL, ccv, crules, rfl, hcv, hrules⟩ := recAt_rel hP h
    exact ⟨ccv, crules, hcv, hL, hrules.mono fun _ _ h => h.1⟩
  recNone := fun n h => recAt_none hP h

/-- **`EnvRelI`** from the relation. -/
theorem envRelI_of (hP : EnvPresI fe L) : EnvRelI fe L where
  ty := by
    intro n ci hf
    obtain ⟨cci, hL, hr⟩ := hP.entry n ci hf
    obtain ⟨h1, h2, h3⟩ := hr.cv
    refine ⟨cci, cci.toConstantVal.type, hL, ?_, rfl, ?_, ?_, ?_⟩
    · rw [ci_cv_type]; exact h3.2.2
    · rw [h2, ci_cv_lps]
    · rw [ci_cv_type]; exact h3.1
    · rw [ci_cv_type]; exact h3.2.1
  val := by
    intro n cv v h hd
    obtain ⟨ccv, cval, hL, hcv, hv⟩ := defnView_rel hP hd
    exact ⟨ccv, cval, trHint h, hL, hv.2.2, hcv.2.1, hv.1, hv.2.1⟩
  rule := by
    intro c rv b j rl hra hrl
    obtain ⟨cci, hL, ccv, crules, rfl, hcv, hrules⟩ := recAt_rel hP hra
    obtain ⟨crl, hcrl, -, hst⟩ := find_rule_relS hrules j rl hrl
    exact ⟨ccv, _, _, _, crules, crl, hL, hcrl, hst.2.2, hcv.2.1, hst.1, hst.2.1⟩

/-- The former view through the relation (`EnvViewI.ind`). -/
theorem indView_rel (hP : EnvPresI fe L) {n : Name} {cv : ConstantVal} {caps : InLean.IndCaps}
    (h : fe.indView? n = some (cv, caps)) :
    ∃ ccv, CVRel cv ccv ∧ L.find? (toName n) = some (.indInfo ccv (toCaps caps)) := by
  unfold InLean.FEnv.indView? at h
  cases hf : fe.find? n with
  | none => rw [hf] at h; cases h
  | some ci =>
    rw [hf] at h
    obtain ⟨cci, hL, hr⟩ := hP.entry n ci hf
    cases ci with
    | inductInfo v =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      cases cci <;> simp only [EntryRelI] at hr
      obtain ⟨h1, rfl, -⟩ := hr
      exact ⟨_, h1, hL⟩
    | quotInfo q =>
      simp only [EntryRelI] at hr
      revert h hr
      cases hk : q.kind <;> simp (config := { decide := true }) [hk]
      rintro rfl rfl ccv rfl h2
      exact ⟨ccv, h2, hL⟩
    | _ => cases h

theorem indView_none (hP : EnvPresI fe L) {n : Name} (h : fe.indView? n = none) :
    ∀ ccv caps, L.find? (toName n) ≠ some (.indInfo ccv caps) := by
  intro ccv caps hL
  unfold InLean.FEnv.indView? at h
  cases hf : fe.find? n with
  | none => rw [hP.none n hf] at hL; cases hL
  | some ci =>
    rw [hf] at h
    obtain ⟨cci, hL', hr⟩ := hP.entry n ci hf
    rw [hL] at hL'; cases hL'
    rcases hr.inv_ind with ⟨v, rfl, -⟩ | ⟨q, rfl, hk, -⟩
    · cases h
    · simp (config := { decide := true }) [hk] at h

/-- The constructor view through the relation (`EnvViewI.ctor`). -/
theorem ctorView_rel (hP : EnvPresI fe L) {n : Name} {cv : ConstantVal} {nP nF : Nat} {T : Name}
    (h : fe.ctorView? n = some (cv, nP, nF, T)) :
    ∃ ccv, CVRel cv ccv ∧ L.find? (toName n) = some (.ctorInfo ccv nP nF (toName T)) := by
  unfold InLean.FEnv.ctorView? at h
  cases hf : fe.find? n with
  | none => rw [hf] at h; cases h
  | some ci =>
    rw [hf] at h
    obtain ⟨cci, hL, hr⟩ := hP.entry n ci hf
    cases ci with
    | ctorInfo v =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      cases cci <;> simp only [EntryRelI] at hr
      obtain ⟨h1, rfl, rfl, rfl⟩ := hr
      exact ⟨_, h1, hL⟩
    | quotInfo q =>
      simp only [EntryRelI] at hr
      revert h hr
      cases hk : q.kind <;> simp (config := { decide := true }) [hk]
      rintro rfl rfl rfl rfl ccv rfl h2
      exact ⟨ccv, h2, hL⟩
    | _ => cases h

theorem ctorView_none (hP : EnvPresI fe L) {n : Name} (h : fe.ctorView? n = none) :
    ∀ ccv nP nF T, L.find? (toName n) ≠ some (.ctorInfo ccv nP nF T) := by
  intro ccv nP nF T hL
  unfold InLean.FEnv.ctorView? at h
  cases hf : fe.find? n with
  | none => rw [hP.none n hf] at hL; cases hL
  | some ci =>
    rw [hf] at h
    obtain ⟨cci, hL', hr⟩ := hP.entry n ci hf
    rw [hL] at hL'; cases hL'
    rcases hr.inv_ctor with ⟨v, rfl, -⟩ | ⟨q, rfl, hk, -⟩
    · cases h
    · simp (config := { decide := true }) [hk] at h

/-- No table InLean reads: no projection entry. -/
theorem findProj_none_of {T : Name} (h : fe.findTable? T = none) (i : Nat) :
    fe.findProj? T i = none := by
  unfold InLean.FEnv.findProj?
  rw [h]

/-- A table InLean reads, off the former and its one constructor. -/
theorem findTable_of {T c : Name} {v : InductiveVal} {cv : ConstructorVal}
    (hT : fe.find? T = some (.inductInfo v)) (hpd : fe.isPending v.name = false)
    (hcs : v.ctors = [c]) (hI : v.numIndices = 0)
    (hc : fe.find? c = some (.ctorInfo cv)) (hp : hasPis (v.numParams + cv.numFields) cv.type = true) :
    fe.findTable? T = some ⟨T, v.levelParams, v.numParams, c, cv.numFields, cv.type⟩ := by
  unfold InLean.FEnv.findTable?
  simp [hT, hpd, hcs, hI, hc, hp]

/-- A table InLean reads: its entries. -/
theorem findProj_of {T c : Name} {v : InductiveVal} {cv : ConstructorVal}
    (hT : fe.find? T = some (.inductInfo v)) (hpd : fe.isPending v.name = false)
    (hcs : v.ctors = [c]) (hI : v.numIndices = 0)
    (hc : fe.find? c = some (.ctorInfo cv)) (hp : hasPis (v.numParams + cv.numFields) cv.type = true)
    (i : Nat) :
    fe.findProj? T i = if i < cv.numFields then
      some ⟨T, i, v.levelParams, v.numParams, c, cv.numFields, cv.type⟩ else none := by
  unfold InLean.FEnv.findProj?
  rw [findTable_of hT hpd hcs hI hc hp]
  rfl

/-- **`EnvViewI`** from the relation. -/
theorem envViewI_of (hP : EnvPresI fe L) : EnvViewI fe L where
  ind := fun _ _ _ h => indView_rel hP h
  indNone := fun _ h => indView_none hP h
  ctor := fun _ _ _ _ _ h => ctorView_rel hP h
  ctorNone := fun _ h => ctorView_none hP h
  table := by
    intro T t h
    have ht := hP.table T
    cases hL : L.findTable? (toName T) with
    | none =>
      rw [hL] at ht
      rw [ht] at h; cases h
    | some tbl =>
      rw [hL] at ht
      obtain ⟨v, c, cv, hT, hpd, hcs, hI, hc, hp, -, h2, h3, h4, h5, -⟩ := ht
      rw [findTable_of hT hpd hcs hI hc hp] at h
      cases h
      exact ⟨tbl, rfl, h4, h5, h3, h2⟩
  tableNone := by
    intro T h
    have ht := hP.table T
    cases hL : L.findTable? (toName T) with
    | none => rfl
    | some tbl =>
      rw [hL] at ht
      obtain ⟨v, c, cv, hT, hpd, hcs, hI, hc, hp, -⟩ := ht
      rw [findTable_of hT hpd hcs hI hc hp] at h
      cases h

/-! ### The prop-ness readers through the translation

InLean's `proofPW` family against con-leche's (`ConLeche/Kernel/PropRead.lean`),
on a term with a reading under any id translation `fv` whose free variables'
types are `fvTy`'s (`FvTyRel`): the walks agree node by node, `mdata` a
stuttering step, a constant's stored type, a definition's value and a
table's body read through the relation. -/

/-- The id translation `fv` reads a free variable as con-leche's `.fvar d cty`,
`cty` the translation of the type `fvTy` reads. -/
@[expose] def FvTyRel (fv : FVarId → Option ConLeche.Expr) (fvTy : FVarId → Option Expr) : Prop :=
  ∀ id c, fv id = some c → ∃ d ty cty, c = .fvar d cty ∧ fvTy id = some ty ∧ toExpr fv ty = some cty

/-- Two optional terms, one the translation of the other. -/
@[expose] def ORel (fv : FVarId → Option ConLeche.Expr) : Option Expr → Option ConLeche.Expr → Prop
  | some x, some c => toExpr fv x = some c
  | none, none => True
  | _, _ => False

theorem toLevel_eq_trL : ∀ {u : Level} {c : ConLeche.Level}, toLevel u = some c → c = trL u
  | .zero, c, h => by simp [toLevel] at h; subst h; rfl
  | .succ u, c, h => by
    simp only [toLevel, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, rfl⟩ := h; rw [toLevel_eq_trL ha]; rfl
  | .max u v, c, h => by
    simp only [toLevel, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h; rw [toLevel_eq_trL ha, toLevel_eq_trL hb]; rfl
  | .imax u v, c, h => by
    simp only [toLevel, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h; rw [toLevel_eq_trL ha, toLevel_eq_trL hb]; rfl
  | .param n, c, h => by simp [toLevel] at h; subst h; rfl
  | .mvar _, c, h => by simp [toLevel] at h

theorem toLevels_eq_map : ∀ {us : List Level} {cus : List ConLeche.Level},
    toLevels us = some cus → cus = us.map trL
  | [], cus, h => by simp [toLevels] at h; subst h; rfl
  | u :: us, cus, h => by
    simp only [toLevels, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    rw [toLevel_eq_trL ha, toLevels_eq_map hb]; rfl

theorem mapM_length {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → l'.length = l.length
  | [], l', h => by simp at h; subst h; rfl
  | a :: l, l', h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, -, bs, hbs, rfl⟩ := h
    simp [mapM_length hbs]

theorem mapM_getD {α β : Type} {f : α → Option β} {d : α} {d' : β} (hd : f d = some d') :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ i, f (l.getD i d) = some (l'.getD i d')
  | [], l', h, i => by simp at h; subst h; simpa using hd
  | a :: l, l', h, i => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    cases i with
    | zero => simpa using hb
    | succ i => simpa using mapM_getD hd hbs i

theorem array_getD_toList {α : Type} (a : Array α) (i : Nat) (d : α) :
    a.getD i d = a.toList.getD i d := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem numArgs_eq : ∀ e : ConLeche.Expr, ConLeche.Expr.numArgs e = e.getAppArgs.length
  | .app f _ => by simp [ConLeche.Expr.numArgs, ConLeche.Expr.getAppArgs, numArgs_eq f]
  | .bvar _ | .fvar .. | .sort _ | .const .. | .lam .. | .forallE .. | .letE .. | .lit _
  | .proj .. => rfl

theorem fvarsOnly_none : FVarsOnly (fun _ => none) := fun _ _ h => by cases h

/-- A stored term reads the same under every id translation. -/
theorem toExpr_stored {fv : FVarId → Option ConLeche.Expr} {t : Expr} {c : ConLeche.Expr}
    (h : StoredT t c) : toExpr fv t = some c := by
  rw [toExpr_noFVar t h.1]; exact h.2.2

section Walks

variable {fv : FVarId → Option ConLeche.Expr} (hfv : FVarsOnly fv)
include hfv

theorem lamProj_tr : ∀ (v : Expr) (cv : ConLeche.Expr) (k : Nat), toExpr fv v = some cv →
    InLean.lamProj? k v = ConLeche.lamProj? k cv := by
  intro v
  induction v with
  | mdata _ x ih => intro cv k h; exact ih cv k h
  | lam _ t b _ _ ihb =>
    intro cv k h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ct, -, cb, hb, rfl⟩ := h
    simp only [InLean.lamProj?, ConLeche.lamProj?]; exact ihb cb (k + 1) hb
  | bvar j => intro cv k h; simp [toExpr] at h; subst h; rfl
  | fvar id =>
    intro cv k h
    obtain ⟨d, ty, rfl⟩ := hfv id cv h; rfl
  | mvar _ => intro cv k h; simp [toExpr] at h
  | sort u => intro cv k h; simp only [toExpr, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; rfl
  | const n us => intro cv k h; simp only [toExpr, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; rfl
  | app f a _ _ =>
    intro cv k h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨_, -, _, -, rfl⟩ := h; rfl
  | forallE _ t b _ _ _ =>
    intro cv k h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨_, -, _, -, rfl⟩ := h; rfl
  | letE _ t v b _ _ _ _ =>
    intro cv k h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨_, -, _, -, _, -, rfl⟩ := h; rfl
  | lit l => intro cv k h; simp [toExpr] at h; subst h; rfl
  | proj _ _ x _ => intro cv k h; simp only [toExpr, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; rfl

end Walks

/-- The head constructor of con-leche's term. -/
@[expose] def tagC : ConLeche.Expr → Nat
  | .bvar _ => 0 | .fvar .. => 1 | .sort _ => 3 | .const .. => 4 | .app .. => 5 | .lam .. => 6
  | .forallE .. => 7 | .letE .. => 8 | .lit _ => 9 | .proj .. => 10

/-- The head constructor of Lean's term. -/
@[expose] def tagL : Expr → Nat
  | .bvar _ => 0 | .fvar _ => 1 | .mvar _ => 2 | .sort _ => 3 | .const .. => 4 | .app .. => 5
  | .lam .. => 6 | .forallE .. => 7 | .letE .. => 8 | .lit _ => 9 | .proj .. => 10 | .mdata .. => 11

/-- The translation keeps the head constructor (but `mdata`'s). -/
theorem tag_tr {fv : FVarId → Option ConLeche.Expr} (hfv : FVarsOnly fv) {x : Expr}
    {c : ConLeche.Expr} (h : toExpr fv x = some c) (hm : ∀ m y, x ≠ .mdata m y) :
    tagC c = tagL x := by
  cases x with
  | fvar id => obtain ⟨d, ty, rfl⟩ := hfv id c h; rfl
  | mdata m y => exact absurd rfl (hm m y)
  | mvar _ => simp [toExpr] at h
  | bvar _ | lit _ => simp only [toExpr, Option.some.injEq] at h; subst h; rfl
  | sort _ | const _ _ | proj _ _ _ =>
    simp only [toExpr, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; rfl
  | app _ _ | lam _ _ _ _ | forallE _ _ _ _ =>
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨_, -, _, -, rfl⟩ := h; rfl
  | letE _ _ _ _ _ =>
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨_, -, _, -, _, -, rfl⟩ := h; rfl

theorem toExpr_forallE_inv {fv : FVarId → Option ConLeche.Expr} {n : Name} {t b : Expr}
    {bi : BinderInfo} {c : ConLeche.Expr} (h : toExpr fv (.forallE n t b bi) = some c) :
    ∃ ct cb, toExpr fv t = some ct ∧ toExpr fv b = some cb ∧ c = .forallE ct cb := by
  simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨ct, ht, cb, hb, rfl⟩ := h; exact ⟨ct, cb, ht, hb, rfl⟩

theorem toExpr_lam_inv {fv : FVarId → Option ConLeche.Expr} {n : Name} {t b : Expr}
    {bi : BinderInfo} {c : ConLeche.Expr} (h : toExpr fv (.lam n t b bi) = some c) :
    ∃ ct cb, toExpr fv t = some ct ∧ toExpr fv b = some cb ∧ c = .lam ct cb := by
  simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨ct, ht, cb, hb, rfl⟩ := h; exact ⟨ct, cb, ht, hb, rfl⟩

theorem toExpr_app_inv {fv : FVarId → Option ConLeche.Expr} {f a : Expr}
    {c : ConLeche.Expr} (h : toExpr fv (.app f a) = some c) :
    ∃ cf ca, toExpr fv f = some cf ∧ toExpr fv a = some ca ∧ c = .app cf ca := by
  simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨cf, hf, ca, ha, rfl⟩ := h; exact ⟨cf, ca, hf, ha, rfl⟩

theorem toExpr_letE_inv {fv : FVarId → Option ConLeche.Expr} {n : Name} {t v b : Expr}
    {nd : Bool} {c : ConLeche.Expr} (h : toExpr fv (.letE n t v b nd) = some c) :
    ∃ ct cv cb, toExpr fv b = some cb ∧ c = .letE ct cv cb := by
  simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨ct, -, cv, -, cb, hb, rfl⟩ := h; exact ⟨ct, cv, cb, hb, rfl⟩

theorem toExpr_sort_inv {fv : FVarId → Option ConLeche.Expr} {u : Level} {c : ConLeche.Expr}
    (h : toExpr fv (.sort u) = some c) : c = .sort (trL u) := by
  simp only [toExpr, Option.map_eq_some_iff] at h
  obtain ⟨cu, hu, rfl⟩ := h; rw [toLevel_eq_trL hu]

theorem toExpr_const_inv {fv : FVarId → Option ConLeche.Expr} {n : Name} {us : List Level}
    {c : ConLeche.Expr} (h : toExpr fv (.const n us) = some c) :
    c = .const (toName n) (us.map trL) := by
  simp only [toExpr, Option.map_eq_some_iff] at h
  obtain ⟨cus, hu, rfl⟩ := h; rw [toLevels_eq_map hu]

theorem toExpr_proj_inv {fv : FVarId → Option ConLeche.Expr} {S : Name} {i : Nat} {x : Expr}
    {c : ConLeche.Expr} (h : toExpr fv (.proj S i x) = some c) :
    ∃ cx, c = .proj (toName S) i cx := by
  simp only [toExpr, Option.map_eq_some_iff] at h
  obtain ⟨cx, -, rfl⟩ := h; exact ⟨cx, rfl⟩

/-! #### con-leche's fall-through equations -/

theorem unwrapC_other {find? : ConLeche.Name → Option ConLeche.ConstantInfo} {fuel : Nat}
    {e : ConLeche.Expr} (h : ∀ n us, e.getAppFn ≠ .const n us) :
    ConLeche.unwrapIdDefs find? (fuel + 1) e = e := by
  rw [ConLeche.unwrapIdDefs]
  split
  all_goals first | rfl | (rename_i hh; exact absurd hh (h _ _))

theorem peelPisWC_other {find? : ConLeche.Name → Option ConLeche.ConstantInfo} {k : Nat}
    {e : ConLeche.Expr} (h : tagC e ≠ 7) :
    ConLeche.peelPisW find? (k + 1) e = match ConLeche.unwrapIdDefs find? 4 e with
      | .forallE _ b => ConLeche.peelPisW find? k b
      | _ => none := by
  cases e <;> first | rfl | exact absurd rfl h

theorem peelPisW_other {fe : InLean.FEnv} {k : Nat} {e : Expr} (h1 : tagL e ≠ 7) (h2 : tagL e ≠ 11) :
    InLean.peelPisW fe (k + 1) e = match EO.stripTop (InLean.unwrapIdDefs fe 4 e) with
      | .forallE _ _ b _ => InLean.peelPisW fe k b
      | _ => none := by
  cases e <;> simp only [tagL, ne_eq, not_true_eq_false] at h1 h2 <;> (rw [InLean.peelPisW.eq_def]; rfl)

theorem typeSortPWGoC_other {find? : ConLeche.Name → Option ConLeche.ConstantInfo}
    {root R : ConLeche.Expr} {d : Nat} (h1 : tagC R ≠ 7) (h2 : tagC R ≠ 3) :
    ConLeche.typeSortPWGo find? root R d =
      ConLeche.headTypePW find? root d R.getAppFn (ConLeche.Expr.numArgs R) := by
  cases R <;> first | rfl | exact absurd rfl h1 | exact absurd rfl h2

theorem typeSortPWGo_other {fe : InLean.FEnv} {fvTy : FVarId → Option Expr} {root R : Expr}
    {d : Nat} (h1 : tagL R ≠ 7) (h2 : tagL R ≠ 3) (h3 : tagL R ≠ 11) :
    InLean.typeSortPWGo fe fvTy root R d =
      InLean.headTypePW fe fvTy root d R.getAppFnT R.getAppNumArgsT := by
  cases R <;> simp only [tagL, ne_eq, not_true_eq_false] at h1 h2 h3 <;>
    (rw [InLean.typeSortPWGo.eq_def]; try rfl)

theorem proofPWC_other {find? : ConLeche.Name → Option ConLeche.ConstantInfo}
    {ft : ConLeche.Name → Option ConLeche.ProjTable} {e : ConLeche.Expr}
    (h1 : tagC e ≠ 5) (h2 : tagC e ≠ 6) (h3 : tagC e ≠ 8) :
    ConLeche.proofPW find? ft e = ConLeche.headProofPW find? ft e := by
  cases e <;> first | rfl | exact absurd rfl h1 | exact absurd rfl h2 | exact absurd rfl h3

theorem trPW_isProp (p : InLean.PropWhen) : (trPW p).isProp = p.isProp := by
  cases p with
  | never => rfl
  | ifAllZero ps => cases ps <;> rfl

theorem trPW_comp_substPW (ks : List Name) (us : List Level) :
    trPW ∘ InLean.Lvl.substPW ks us =
      ConLeche.Level.substPW (ks.map toName) (us.map trL) ∘ trPW :=
  funext (trPW_substPW ks us)

section Walks2

variable {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L)
  {fv : FVarId → Option ConLeche.Expr} (hfv : FVarsOnly fv)
include hP hfv

theorem unwrap_tr : ∀ (fuel : Nat) (e : Expr) (ce : ConLeche.Expr), toExpr fv e = some ce →
    toExpr fv (InLean.unwrapIdDefs fe fuel e) = some (ConLeche.unwrapIdDefs L.find? fuel ce)
  | 0, e, ce, h => by simpa [InLean.unwrapIdDefs, ConLeche.unwrapIdDefs] using h
  | fuel + 1, e, ce, h => by
    have hfn := toExpr_getAppFnT hfv e ce h
    rw [InLean.unwrapIdDefs]
    split
    · rename_i c us heq
      rw [heq] at hfn
      have hc := toExpr_const_inv hfn
      simp only [ConLeche.unwrapIdDefs, hc]
      cases hv : fe.defnView? c with
      | none =>
        have hn := defnView_none hP hv
        simp only
        all_goals first
          | exact h
          | (split <;> first | exact h | (rename_i hh; exact absurd hh (hn _ _ _)))
      | some x =>
        obtain ⟨cv, v, hint⟩ := x
        obtain ⟨ccv, cval, hL, -, hst⟩ := defnView_rel hP hv
        simp only [hL]
        rw [lamProj_tr fvarsOnly_none v cval 0 hst.2.2]
        cases hl : ConLeche.lamProj? 0 cval with
        | none => exact h
        | some kj =>
          obtain ⟨k, j⟩ := kj
          have hargs := toExpr_getAppArgsT hfv h
          have hlen := mapM_length hargs
          simp only [Array.length_toList] at hlen
          simp only []
          rw [← hlen]
          by_cases hcond : (decide (k ≤ ce.getAppArgs.length) && ce.getAppArgs.length == k) = true
          · simp only [hcond, ↓reduceIte]
            rw [array_getD_toList]
            exact unwrap_tr fuel _ _ (mapM_getD h hargs _)
          · simp only [hcond, Bool.false_eq_true, ↓reduceIte]; exact h
    · rename_i hne
      have hm : ∀ m y, Expr.getAppFnT e ≠ .mdata m y := fun m y hh => getAppFnT_ne_mdata hh
      have ht := tag_tr hfv hfn hm
      rw [unwrapC_other]
      · exact h
      · intro n us hh
        rw [hh] at ht
        generalize hx : Expr.getAppFnT e = x at ht hne
        cases x <;> simp [tagC, tagL] at ht
        exact hne _ _ rfl

theorem peelPisW_fall (k : Nat)
    (ih : ∀ e ce, toExpr fv e = some ce →
      ORel fv (InLean.peelPisW fe k e) (ConLeche.peelPisW L.find? k ce))
    (e : Expr) (ce : ConLeche.Expr) (h : toExpr fv e = some ce) (h7 : tagL e ≠ 7)
    (h11 : tagL e ≠ 11) :
    ORel fv (InLean.peelPisW fe (k + 1) e) (ConLeche.peelPisW L.find? (k + 1) ce) := by
  have ht := tag_tr hfv h (fun m y hc => by rw [hc] at h11; exact h11 rfl)
  rw [peelPisW_other h7 h11, peelPisWC_other (by rw [ht]; exact h7)]
  have hu := unwrap_tr hP hfv 4 e ce h
  rw [← toExpr_stripTop] at hu
  have hnm : ∀ m y, EO.stripTop (InLean.unwrapIdDefs fe 4 e) ≠ .mdata m y :=
    fun m y hh => stripTop_ne_mdata hh
  generalize EO.stripTop (InLean.unwrapIdDefs fe 4 e) = u at hu hnm ⊢
  generalize ConLeche.unwrapIdDefs L.find? 4 ce = cu at hu ⊢
  cases u with
  | forallE n t b bi =>
    obtain ⟨ct, cb, -, hb, rfl⟩ := toExpr_forallE_inv hu
    exact ih b cb hb
  | mdata m y => exact absurd rfl (hnm m y)
  | _ =>
    have ht' := tag_tr hfv hu (by intro m y hc; cases hc)
    cases cu <;> simp_all [tagC, tagL, ORel]

theorem peelPisW_tr : ∀ (k : Nat) (e : Expr) (ce : ConLeche.Expr), toExpr fv e = some ce →
    ORel fv (InLean.peelPisW fe k e) (ConLeche.peelPisW L.find? k ce)
  | 0, e, ce, h => by
    simp only [InLean.peelPisW, ConLeche.peelPisW, ORel]; exact unwrap_tr hP hfv 4 e ce h
  | k + 1, e, ce, h => by
    induction e generalizing ce with
    | forallE n t b bi _ _ =>
      obtain ⟨ct, cb, -, hb, rfl⟩ := toExpr_forallE_inv h
      simp only [InLean.peelPisW, ConLeche.peelPisW]
      exact peelPisW_tr k b cb hb
    | mdata m x ih => simp only [InLean.peelPisW]; exact ih ce h
    | _ => exact peelPisW_fall hP hfv k (peelPisW_tr k) _ ce h (by simp [tagL]) (by simp [tagL])

end Walks2

theorem residualPW_tr {fv : FVarId → Option ConLeche.Expr} (hfv : FVarsOnly fv) :
    ∀ {o : Option Expr} {co : Option ConLeche.Expr}, ORel fv o co →
      (InLean.residualPW o).map trPW = ConLeche.residualPW co
  | none, none, _ => rfl
  | some x, some c, h => by
    simp only [ORel] at h
    rw [← toExpr_stripTop] at h
    have hnm : ∀ m y, EO.stripTop x ≠ .mdata m y := fun m y hh => stripTop_ne_mdata hh
    simp only [InLean.residualPW]
    generalize EO.stripTop x = y at h hnm ⊢
    cases y with
    | sort u => rw [toExpr_sort_inv h]; simp [ConLeche.residualPW, trPW_zeronessOf]
    | mdata m y => exact absurd rfl (hnm m y)
    | _ =>
      have ht := tag_tr hfv h (by intro m y hc; cases hc)
      cases c <;> simp_all [tagC, tagL, ConLeche.residualPW]
  | none, some _, h | some _, none, h => by simp [ORel] at h

theorem binderDom_tr {fv : FVarId → Option ConLeche.Expr} (hfv : FVarsOnly fv) :
    ∀ (root : Expr) (croot : ConLeche.Expr) (k : Nat), toExpr fv root = some croot →
      ORel fv (InLean.binderDom k root) (ConLeche.Expr.binderDom k croot) := by
  intro root
  induction root with
  | mdata m x ih => intro croot k h; simp only [InLean.binderDom]; exact ih croot k h
  | forallE n t b bi _ ihb =>
    intro croot k h
    obtain ⟨ct, cb, ht, hb, rfl⟩ := toExpr_forallE_inv h
    cases k with
    | zero => simpa [InLean.binderDom, ConLeche.Expr.binderDom, ORel] using ht
    | succ k => simp only [InLean.binderDom, ConLeche.Expr.binderDom]; exact ihb cb k hb
  | _ =>
    intro croot k h
    have ht := tag_tr hfv h (by intro m y hc; cases hc)
    cases croot <;> simp [tagC, tagL] at ht <;>
      cases k <;> simp [InLean.binderDom, ConLeche.Expr.binderDom, ORel]

section Walks3

variable {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L)
  {fv : FVarId → Option ConLeche.Expr} (hfv : FVarsOnly fv)
  {fvTy : FVarId → Option Expr} (hty : FvTyRel fv fvTy)
include hP hfv hty

omit hty in
/-- A constant's stored type, level-instantiated, read through the relation. -/
theorem constPW_tr {I : Name} {us : List Level} {ci : Lean.ConstantInfo}
    (hf : fe.find? I = some ci) (n : Nat) :
    ((if us.length == ci.levelParams.length then
        (InLean.residualPW (InLean.peelPisW fe n ci.type)).map (Lvl.substPW ci.levelParams us)
      else none).map trPW) =
      match L.find? (toName I) with
      | some cci =>
        if (us.map trL).length = cci.toConstantVal.levelParams.length then
          (ConLeche.residualPW (ConLeche.peelPisW L.find? n cci.toConstantVal.type)).map
            (ConLeche.Level.substPW cci.toConstantVal.levelParams (us.map trL))
        else none
      | none => none := by
  obtain ⟨cci, hL, hr⟩ := hP.entry I ci hf
  obtain ⟨-, hlps, hst⟩ := hr.cv
  rw [hL]
  simp only [hlps, ← ci_cv_lps, List.length_map]
  by_cases hlen : us.length = ci.levelParams.length
  · simp only [hlen, BEq.rfl, ↓reduceIte, Option.map_map, trPW_comp_substPW]
    rw [← Option.map_map, residualPW_tr hfv (peelPisW_tr hP hfv n _ _ (by
      rw [ci_cv_type]; exact toExpr_stored hst))]
  · simp [hlen]

theorem headTypePW_tr {root : Expr} {croot : ConLeche.Expr} (hroot : toExpr fv root = some croot)
    (d : Nat) : ∀ (h : Expr) (ch : ConLeche.Expr) (n : Nat), toExpr fv h = some ch →
      (InLean.headTypePW fe fvTy root d h n).map trPW = ConLeche.headTypePW L.find? croot d ch n := by
  intro h
  induction h with
  | mdata m x ih => intro ch n hh; simp only [InLean.headTypePW]; exact ih ch n hh
  | const I us =>
    intro ch n hh
    rw [toExpr_const_inv hh]
    simp only [InLean.headTypePW, ConLeche.headTypePW]
    cases hf : fe.find? I with
    | none => rw [hP.none I hf]; rfl
    | some ci => exact constPW_tr hP hfv hf n
  | fvar id =>
    intro ch n hh
    obtain ⟨d', ty, cty, rfl, hfty, htr⟩ := hty id ch hh
    simp only [InLean.headTypePW, ConLeche.headTypePW, hfty]
    exact residualPW_tr hfv (peelPisW_tr hP hfv n ty cty htr)
  | bvar i =>
    intro ch n hh
    simp only [toExpr, Option.some.injEq] at hh; subst hh
    simp only [InLean.headTypePW, ConLeche.headTypePW]
    by_cases hi : i < d
    · simp only [hi, ↓reduceIte]
      have hb := binderDom_tr hfv root croot (d - 1 - i) hroot
      revert hb
      cases InLean.binderDom (d - 1 - i) root <;> cases ConLeche.Expr.binderDom (d - 1 - i) croot <;>
        simp only [ORel, imp_self, Option.map_none, false_implies]
      intro hb
      exact residualPW_tr hfv (peelPisW_tr hP hfv n _ _ hb)
    · simp [hi]
  | _ =>
    intro ch n hh
    have ht := tag_tr hfv hh (by intro m y hc; cases hc)
    cases ch <;> simp [tagC, tagL] at ht <;>
      simp [InLean.headTypePW, ConLeche.headTypePW]

theorem typeSortPWGo_tr {root : Expr} {croot : ConLeche.Expr} (hroot : toExpr fv root = some croot) :
    ∀ (R : Expr) (cR : ConLeche.Expr) (d : Nat), toExpr fv R = some cR →
      (InLean.typeSortPWGo fe fvTy root R d).map trPW = ConLeche.typeSortPWGo L.find? croot cR d := by
  intro R
  induction R with
  | mdata m x ih => intro cR d h; simp only [InLean.typeSortPWGo]; exact ih cR d h
  | forallE n t b bi _ ihb =>
    intro cR d h
    obtain ⟨ct, cb, -, hb, rfl⟩ := toExpr_forallE_inv h
    simp only [InLean.typeSortPWGo, ConLeche.typeSortPWGo]
    exact ihb cb (d + 1) hb
  | sort u =>
    intro cR d h
    rw [toExpr_sort_inv h]; rfl
  | _ =>
    intro cR d h
    have ht := tag_tr hfv h (by intro m y hc; cases hc)
    rw [typeSortPWGo_other (by simp [tagL]) (by simp [tagL]) (by simp [tagL]),
      typeSortPWGoC_other (by rw [ht]; simp [tagL]) (by rw [ht]; simp [tagL]), numArgs_eq,
      ← getAppNumArgsT_eq hfv _ cR h]
    exact headTypePW_tr hP hfv hty hroot d _ _ _ (toExpr_getAppFnT hfv _ cR h)

theorem typeSortPW_tr {T : Expr} {cT : ConLeche.Expr} (h : toExpr fv T = some cT) :
    (InLean.typeSortPW fe fvTy T).map trPW = ConLeche.typeSortPW L.find? cT :=
  typeSortPWGo_tr hP hfv hty h T cT 0 h

theorem headProofPW_tr : ∀ (h : Expr) (ch : ConLeche.Expr), toExpr fv h = some ch →
    (InLean.headProofPW fe fvTy h).map trPW = ConLeche.headProofPW L.find? L.findTable? ch := by
  intro h
  induction h with
  | mdata m x ih => intro ch hh; simp only [InLean.headProofPW]; exact ih ch hh
  | const I us =>
    intro ch hh
    rw [toExpr_const_inv hh]
    simp only [InLean.headProofPW, ConLeche.headProofPW]
    cases hf : fe.find? I with
    | none => rw [hP.none I hf]; rfl
    | some ci =>
      obtain ⟨cci, hL, hr⟩ := hP.entry I ci hf
      obtain ⟨-, hlps, hst⟩ := hr.cv
      rw [hL]
      simp only [hlps, ← ci_cv_lps, List.length_map]
      by_cases hlen : us.length = ci.levelParams.length
      · simp only [hlen, BEq.rfl, ↓reduceIte, Option.map_map, trPW_comp_substPW]
        rw [← Option.map_map, typeSortPW_tr hP hfv hty (by rw [ci_cv_type]; exact toExpr_stored hst)]
      · simp [hlen]
  | fvar id =>
    intro ch hh
    obtain ⟨d', ty, cty, rfl, hfty, htr⟩ := hty id ch hh
    simp only [InLean.headProofPW, ConLeche.headProofPW, hfty]
    exact typeSortPW_tr hP hfv hty htr
  | sort u => intro ch hh; rw [toExpr_sort_inv hh]; rfl
  | forallE n t b bi _ _ =>
    intro ch hh; obtain ⟨ct, cb, -, -, rfl⟩ := toExpr_forallE_inv hh; rfl
  | lit l => intro ch hh; simp only [toExpr, Option.some.injEq] at hh; subst hh; rfl
  | proj S i x _ =>
    intro ch hh
    obtain ⟨cx, rfl⟩ := toExpr_proj_inv hh
    simp only [InLean.headProofPW, ConLeche.headProofPW]
    have ht := hP.table S
    cases hL : L.findTable? (toName S) with
    | none =>
      rw [hL] at ht
      rw [findProj_none_of ht]; rfl
    | some tbl =>
      rw [hL] at ht
      obtain ⟨v, c, cv, hT, hpd, hcs, hI, hc, hp, -, -, -, -, h5, hb⟩ := ht
      rw [findProj_of hT hpd hcs hI hc hp]
      by_cases hi : i < cv.numFields
      · obtain ⟨b, hb1, hb2, hb3⟩ := hb i hi
        simp only [hi, ↓reduceIte, h5, hb1]
        have hts := typeSortPW_tr hP hfv hty (fv := fv)
          (show toExpr fv b = some (tbl.entry i).body by
            rw [toExpr_noFVar b hb2]; exact hb3)
        revert hts
        cases InLean.typeSortPW fe fvTy b <;>
          cases ConLeche.typeSortPW L.find? (tbl.entry i).body <;> simp
        intro hpw; subst hpw
        rw [trPW_isNever]
        all_goals (try split) <;> rfl
      · simp [hi, h5]
  | _ =>
    intro ch hh
    have ht := tag_tr hfv hh (by intro m y hc; cases hc)
    cases ch <;> simp [tagC, tagL] at ht <;>
      simp [InLean.headProofPW, ConLeche.headProofPW]

theorem proofPW_tr : ∀ (e : Expr) (ce : ConLeche.Expr), toExpr fv e = some ce →
    (InLean.proofPW fe fvTy e).map trPW = ConLeche.proofPW L.find? L.findTable? ce := by
  intro e
  induction e with
  | mdata m x ih => intro ce h; simp only [InLean.proofPW]; exact ih ce h
  | lam n t b bi _ ihb =>
    intro ce h
    obtain ⟨ct, cb, -, hb, rfl⟩ := toExpr_lam_inv h
    simp only [InLean.proofPW, ConLeche.proofPW]; exact ihb cb hb
  | letE n t v b nd _ _ ihb =>
    intro ce h
    obtain ⟨ct, cv, cb, hb, rfl⟩ := toExpr_letE_inv h
    simp only [InLean.proofPW, ConLeche.proofPW]; exact ihb cb hb
  | app f a ihf _ =>
    intro ce h
    obtain ⟨cf, ca, hf, -, rfl⟩ := toExpr_app_inv h
    simp only [InLean.proofPW, ConLeche.proofPW]; exact ihf cf hf
  | _ =>
    intro ce h
    have ht := tag_tr hfv h (by intro m y hc; cases hc)
    rw [proofPWC_other (by rw [ht]; simp [tagL]) (by rw [ht]; simp [tagL])
      (by rw [ht]; simp [tagL])]
    have := headProofPW_tr hP hfv hty _ ce h
    rw [← this]
    rfl

end Walks3

/-- The free-variable types a state's readers see (`fvTyOf`) are the ones the
translation carries. -/
theorem fvTyRel_state (s : InLean.CState) :
    FvTyRel (FVarTable.trans (tableOf s)) (fvTyOf s.fvTys) := by
  intro id c h
  obtain ⟨d, cty, rfl⟩ := FVarTable.trans_fvarsOnly _ id c h
  obtain ⟨n, ty, hp, hty, htr⟩ := TransS_fvar (s := s) (id := id) h
  exact ⟨d, ty, cty, rfl, by simp [fvTyOf, hp, hty], htr⟩

/-- The η constructor-shape gate through the relation (`DefeqEnvI.etaShape`). -/
theorem etaShape_of (hP : EnvPresI fe L) (s : InLean.CState) (a : Expr) (ha : OkS s a = true) :
    etaCtorShapeC fe a = ConLeche.etaCtorShape L (TrS s a) := by
  unfold etaCtorShapeC ConLeche.etaCtorShape
  rcases head_cases s a with ⟨n, us, hx, hc⟩ | ⟨hx, hc⟩
  · rw [hx, hc]
    simp only
    cases hv : fe.ctorView? n with
    | some x =>
      obtain ⟨cv, nP, nF⟩ := x
      obtain ⟨ccv, -, hL⟩ := ctorView_rel hP hv
      rw [hL, numArgs_TrS ha]
    | none =>
      have hn := ctorView_none hP hv
      simp only
      all_goals first
        | rfl
        | (split <;> first | rfl | (rename_i h; exact absurd h (hn _ _ _)))
  · split
    · rename_i h; exact absurd h (hx _ _)
    · split
      · rename_i h; exact absurd h (hc _ _)
      · rfl

theorem unfoldable_of (hP : EnvPresI fe L) (s : InLean.CState) (e : Expr) :
    unfoldableHeadC fe e = ConLeche.unfoldableHead L (TrS s e) := by
  unfold unfoldableHeadC ConLeche.unfoldableHead
  rcases head_cases s e with ⟨n, us, hx, hc⟩ | ⟨hx, hc⟩
  · rw [hx, hc]
    simp only
    cases hv : fe.defnView? n with
    | some x =>
      obtain ⟨cv, v, h⟩ := x
      obtain ⟨ccv, cval, hL, hcv, -⟩ := defnView_rel hP hv
      rw [hL]; simp [hcv.2.1]
    | none =>
      have hn := defnView_none hP hv
      simp only
      all_goals first
        | rfl
        | (split <;> first | rfl | (rename_i h; exact absurd h (hn _ _ _)))
  · split
    · rename_i h; exact absurd h (hx _ _)
    · split
      · rename_i h; exact absurd h (hc _ _)
      · rfl

theorem headHint_of (hP : EnvPresI fe L) (s : InLean.CState) (e : Expr) :
    trHint (headHintC fe e) = ConLeche.headHint L (TrS s e) := by
  unfold headHintC ConLeche.headHint
  rcases head_cases s e with ⟨n, us, hx, hc⟩ | ⟨hx, hc⟩
  · rw [hx, hc]
    simp only
    cases hv : fe.defnView? n with
    | some x =>
      obtain ⟨cv, v, h⟩ := x
      obtain ⟨ccv, cval, hL, -, -⟩ := defnView_rel hP hv
      rw [hL]
    | none =>
      have hn := defnView_none hP hv
      simp only
      all_goals first
        | rfl
        | (split <;> first | rfl | (rename_i h; exact absurd h (hn _ _ _)))
  · split
    · rename_i h; exact absurd h (hx _ _)
    · split
      · rename_i h; exact absurd h (hc _ _)
      · rfl

theorem ctorRd_of (hP : EnvPresI fe L) (c : Name) :
    ctorRd L (toName c) = (fe.ctorView? c).map ctorGateI := by
  unfold ctorRd
  cases hv : fe.ctorView? c with
  | some x =>
    obtain ⟨cv, nP, nF, T⟩ := x
    obtain ⟨ccv, hcv, hL⟩ := ctorView_rel hP hv
    rw [hL]; simp [ctorGateI, hcv.2.1]
  | none =>
    have hn := ctorView_none hP hv
    split
    · rename_i h; exact absurd h (hn _ _ _ _)
    · rfl

theorem indRd_of (hP : EnvPresI fe L) (T : Name) :
    indRd L (toName T) = (fe.indView? T).map indGateI := by
  unfold indRd
  cases hv : fe.indView? T with
  | some x =>
    obtain ⟨cv, caps⟩ := x
    obtain ⟨ccv, hcv, hL⟩ := indView_rel hP hv
    rw [hL]; simp [indGateI, hcv.2.1, toCaps]
  | none =>
    have hn := indView_none hP hv
    split
    · rename_i h; exact absurd h (hn _ _)
    · rfl

/-- The prop-ness datum at a state, through the relation. -/
theorem proofPW_state (hP : EnvPresI fe L) (s : InLean.CState) {a : Expr} (ha : OkS s a = true) :
    (InLean.proofPW fe (fvTyOf s.fvTys) a).map trPW =
      ConLeche.proofPW L.find? L.findTable? (TrS s a) :=
  proofPW_tr hP (FVarTable.trans_fvarsOnly _) (fvTyRel_state s) a _ (TransS_of_ok ha)

/-- **`DefeqEnvI`** from the relation. -/
theorem defeqEnvI_of (hP : EnvPresI fe L) (hl : LitFlagsI fe) : DefeqEnvI fe L where
  notProof := by
    intro s a _ ha
    have h := proofPW_state hP s ha
    unfold notProofFastV ConLeche.notProofFast
    rw [← h]
    cases InLean.proofPW fe (fvTyOf s.fvTys) a <;> simp [trPW_isProp]
  isProof := by
    intro s a _ ha
    have h := proofPW_state hP s ha
    unfold isProofFastV ConLeche.isProofFast
    rw [← h]
    cases InLean.proofPW fe (fvTyOf s.fvTys) a <;> simp [trPW_isProp]
  etaShape := etaShape_of hP
  unfoldable := fun s e _ => unfoldable_of hP s e
  headHint := fun s e _ => headHint_of hP s e
  strLit := strLit_I (envDomI_of hP hl)
  ctor := ctorRd_of hP
  ind := indRd_of hP
  view := envViewI_of hP

/-- **All six** environment hypotheses of the core walks, from the relation and
the literal flags' meaning. -/
theorem envHyps_of (hP : EnvPresI fe L) (hl : LitFlagsI fe) :
    EnvRelI fe L ∧ EnvDomI fe L ∧ EnvDefnI fe L ∧ EnvViewI fe L ∧ EnvRecI fe L ∧ DefeqEnvI fe L :=
  ⟨envRelI_of hP, envDomI_of hP hl, envDefnI_of hP, envViewI_of hP, envRecI_of hP,
    defeqEnvI_of hP hl⟩

end Six

/-! ## Preservation: adding a declaration group -/

section Push

theorem FEnv.env_of_find {fe : InLean.FEnv} {n : Name} {ci : Lean.ConstantInfo}
    (h : fe.find? n = some ci) : fe.env.find? n = some ci := by
  simp only [FEnv.find?_eq_filter, Option.filter_eq_some_iff] at h
  exact h.1

theorem pushDelta_find (L : ConLeche.Env) (news : List ConLeche.ConstantInfo)
    (tabs : List ConLeche.ProjTable) (x : ConLeche.Name) :
    (L.pushDelta news tabs).find? x =
      match news.reverse.find? (·.name == x) with
      | some c => some c
      | none => L.find? x := by
  simp only [ConLeche.Env.find?, ConLeche.Env.pushDelta, List.find?_append]
  cases news.reverse.find? (·.name == x) <;> rfl

theorem find_none_of_forall {α : Type} {p : α → Bool} {l : List α} (h : ∀ a ∈ l, p a = false) :
    l.find? p = none := by
  rw [List.find?_eq_none]; intro a ha; simp [h a ha]

/-- **Adding a group keeps the relation**, once the group's own names are
related.  `names` are the group's Lean names, fresh in `fe`; `fe'` is `fe`
with them added (every other name reads as before; the policy, the safety
and the block mark kept); `news` and `tabs` are what con-leche installs, all
at the group's names. -/
theorem presI_push {fe fe' : InLean.FEnv} {L : ConLeche.Env}
    {news : List ConLeche.ConstantInfo} {tabs : List ConLeche.ProjTable} {names : List Name}
    (hP : EnvPresI fe L)
    (hcore : fe'.coreAxioms = fe.coreAxioms) (hsafe : fe'.safety = fe.safety)
    (hpend : fe'.pending = fe.pending)
    (hfresh : ∀ n ∈ names, fe.env.find? n = none)
    (hold : ∀ n, n ∉ names → fe'.env.find? n = fe.env.find? n)
    (hnewC : ∀ c ∈ news, ∃ n ∈ names, c.name = toName n)
    (hnewT : ∀ t ∈ tabs, ∃ n ∈ names, t.structName = toName n)
    (hentry : ∀ n ∈ names, ∀ ci, fe'.find? n = some ci →
      ∃ cci, (L.pushDelta news tabs).find? (toName n) = some cci ∧ EntryRelI fe' ci cci)
    (hnone : ∀ n ∈ names, fe'.find? n = none → (L.pushDelta news tabs).find? (toName n) = none)
    (htab : ∀ T ∈ names, TableRelI fe' T ((L.pushDelta news tabs).findTable? (toName T)))
    (htabFound : ∀ t ∈ tabs, ((L.pushDelta news tabs).find? t.structName).isSome) :
    EnvPresI fe' (L.pushDelta news tabs) := by
  -- old names read as before, on both sides
  have hfeOld : ∀ n, n ∉ names → fe'.find? n = fe.find? n := fun n hn =>
    FEnv.find?_congr hcore hsafe (hold n hn)
  have hext : ∀ n, (fe.find? n).isSome → fe'.find? n = fe.find? n := by
    intro n hs
    apply hfeOld
    intro hn
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.1 hs
    have := FEnv.env_of_find hci
    rw [hfresh n hn] at this; cases this
  have hip : ∀ T, fe'.isPending T = fe.isPending T := by
    intro T; simp only [InLean.FEnv.isPending, hpend]
  have hnotin : ∀ n, n ∉ names → ∀ c ∈ news, (c.name == toName n) = false := by
    intro n hn c hc
    obtain ⟨m, hm, he⟩ := hnewC c hc
    rw [he, toName_beq]
    cases h : m == n
    · rfl
    · rw [eq_of_beq h] at hm; exact absurd hm hn
  have hLOld : ∀ n, n ∉ names → (L.pushDelta news tabs).find? (toName n) = L.find? (toName n) := by
    intro n hn
    rw [pushDelta_find, find_none_of_forall (fun c hc => hnotin n hn c (List.mem_reverse.1 hc))]
  have hLtabOld : ∀ T, T ∉ names →
      (L.pushDelta news tabs).findTable? (toName T) = L.findTable? (toName T) := by
    intro T hT
    unfold ConLeche.Env.findTable?
    rw [hLOld T hT]
    simp only [ConLeche.Env.pushDelta, List.find?_append]
    rw [find_none_of_forall (p := fun (t : ConLeche.ProjTable) => t.structName == toName T)]
    · rfl
    · intro t ht
      obtain ⟨m, hm, he⟩ := hnewT t (List.mem_reverse.1 ht)
      rw [he, toName_beq]
      cases h : m == T
      · rfl
      · rw [eq_of_beq h] at hm; exact absurd hm hT
  have hentryExt : ∀ ci cci, EntryRelI fe ci cci → EntryRelI fe' ci cci := by
    intro ci cci hr
    cases ci <;> cases cci <;> simp only [EntryRelI] at hr ⊢ <;> try exact hr
    rename_i v ccv caps
    obtain ⟨h1, h2, h3⟩ := hr
    refine ⟨h1, h2, ?_⟩
    rw [hip]
    exact h3.imp id fun h c hc => by rw [hext c (h c hc)]; exact h c hc
  -- a name found in `fe` is not new
  have hfoundOld : ∀ n ci, fe.find? n = some ci → n ∉ names := by
    intro n ci hf hn
    have := FEnv.env_of_find hf
    rw [hfresh n hn] at this; cases this
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n ci hf
    by_cases hn : n ∈ names
    · exact hentry n hn ci hf
    · rw [hfeOld n hn] at hf
      obtain ⟨cci, hL, hr⟩ := hP.entry n ci hf
      exact ⟨cci, by rw [hLOld n hn, hL], hentryExt ci cci hr⟩
  · intro n hf
    by_cases hn : n ∈ names
    · exact hnone n hn hf
    · rw [hfeOld n hn] at hf; rw [hLOld n hn]; exact hP.none n hf
  · intro T
    by_cases hT : T ∈ names
    · exact htab T hT
    · rw [hLtabOld T hT]
      have ht := hP.table T
      cases ho : L.findTable? (toName T) with
      | none =>
        rw [ho] at ht
        simp only [TableRelI] at ht ⊢
        unfold InLean.FEnv.findTable? at ht ⊢
        rw [hfeOld T hT]
        cases hf : fe.find? T with
        | none => rfl
        | some ci =>
          rw [hf] at ht
          cases ci with
          | inductInfo v =>
            obtain ⟨cci, -, hr⟩ := hP.entry T _ hf
            have hcl : fe.isPending v.name = true ∨ ∀ c ∈ v.ctors, (fe.find? c).isSome := by
              cases cci <;> simp only [EntryRelI] at hr; exact hr.2.2
            simp only [hip] at ht ⊢
            split
            · rfl
            · rename_i hnp
              simp only [hnp] at ht
              split
              · rename_i c hcs
                have hcl' : (fe.find? c).isSome := by
                  rcases hcl with h | h
                  · exact absurd h hnp
                  · exact h c (by simp [hcs])
                rw [hext c hcl']
                rw [hcs] at ht; exact ht
              · rfl
          | _ => rfl
      | some tbl =>
        rw [ho] at ht
        obtain ⟨v, c, cv, hTf, hpd, hcs, hI, hc, hp, rest⟩ := ht
        exact ⟨v, c, cv, by rw [hfeOld T hT]; exact hTf, by rw [hip]; exact hpd, hcs, hI,
          by rw [hfeOld c (hfoundOld c _ hc)]; exact hc, hp, rest⟩
  · intro tbl ht
    simp only [ConLeche.Env.pushDelta, List.mem_append, List.mem_reverse] at ht
    rcases ht with ht | ht
    · exact htabFound tbl ht
    · have h := hP.tabNames tbl ht
      rw [pushDelta_find]
      split
      · rfl
      · exact h

end Push

/-! ## Per kind: one constant -/

section One

variable {fe : InLean.FEnv} {L : ConLeche.Env}

theorem toName_sorryAxName : toName InLean.sorryAxName = ConLeche.sorryAxName := rfl
theorem toName_quotSoundName : toName InLean.quotSoundName = ConLeche.quotSoundName := rfl

theorem toHint_eq_trHint (h : ReducibilityHints) : toHint h = trHint h := by cases h <;> rfl

theorem ci_cv_name (ci : Lean.ConstantInfo) : ci.name = ci.toConstantVal.name := by
  cases ci <;> rfl

/-- A term with a closed reading has no free variable. -/
theorem fvarS_of_toExprC : ∀ {e : Expr} {c : ConLeche.Expr}, toExprC e = some c → fvarS e = false := by
  intro e
  induction e with
  | fvar _ => intro c h; simp [toExprC, toExpr] at h
  | app f a ihf iha | lam _ f a _ ihf iha | forallE _ f a _ ihf iha =>
    intro c h
    simp only [toExprC, toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨cf, hf, ca, ha, -⟩ := h
    simp [fvarS, ihf hf, iha ha]
  | letE _ t v b _ iht ihv ihb =>
    intro c h
    simp only [toExprC, toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨ct, ht, cv, hv, cb, hb, -⟩ := h
    simp [fvarS, iht ht, ihv hv, ihb hb]
  | mdata _ x ih => intro c h; exact ih h
  | proj _ _ x ih =>
    intro c h
    simp only [toExprC, toExpr, Option.map_eq_some_iff] at h
    obtain ⟨cx, hx, -⟩ := h
    exact ih hx
  | _ => intro _ _; rfl

/-- A stored term: in range, with a closed reading. -/
theorem StoredT_of {t : Expr} {c : ConLeche.Expr} (hr : Expr.RangeOk t) (h : toExprC t = some c) :
    StoredT t c := ⟨fvarS_of_toExprC h, hr, h⟩

theorem CVRel_of_toCV {v : Lean.ConstantVal} {ccv : ConLeche.ConstantVal} (h : toCV v = some ccv)
    (hr : Expr.RangeOk v.type) : CVRel v ccv := by
  simp only [toCV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨cty, hty, rfl⟩ := h
  exact ⟨rfl, rfl, StoredT_of hr hty⟩

/-- The pushed environment's lookups (`EnvLaws`). -/
theorem find_addConst (hlaws : EnvLaws) {E : Kernel.Environment} {ci : Lean.ConstantInfo}
    (hfresh : E.find? ci.name = none) (n : Name) :
    (InLean.addConst E ci).find? n = if n = ci.name then some ci else E.find? n :=
  hlaws.1 E ci n hfresh

/-- **A push of a fresh name keeps the literal flags' meaning** (twin of
master's `FEnv.push_flags`): before string literals are expandable a push of
one of the ten names recomputes them; any other push leaves them, since a
fresh name is not one of the ten once they are all seen, and the other
names' lookups are unchanged (`EnvLaws`). -/
theorem LitFlagsI.push (hlaws : EnvLaws) {fe : InLean.FEnv} (hl : LitFlagsI fe)
    {ci : Lean.ConstantInfo} (hfresh : fe.env.find? ci.name = none) :
    LitFlagsI (fe.push ci) := by
  have hfind : ∀ n, n ≠ ci.name → (fe.push ci).find? n = fe.find? n := by
    intro n hn
    show InLean.findAt (InLean.addConst fe.env ci) fe.safety fe.coreAxioms n =
      InLean.findAt fe.env fe.safety fe.coreAxioms n
    unfold InLean.findAt
    rw [find_addConst hlaws hfresh n, ite_eq_right hn]
  have hlit : InLean.litName ci.name = true → fe.strLit = false := by
    intro hn
    cases hs : fe.strLit
    · rfl
    exfalso
    have h : InLean.strLitStoredBy fe.find? = true := hl.str ▸ hs
    have hnone : fe.find? ci.name = none := by
      unfold InLean.FEnv.find?; rw [hfresh]
    simp only [InLean.litName, Bool.or_eq_true, beq_iff_eq] at hn
    simp only [InLean.strLitStoredBy, InLean.strSupportBy, InLean.natLitStoredBy,
      Bool.and_eq_true] at h
    rcases hn with ((((((((h1 | h1) | h1) | h1) | h1) | h1) | h1) | h1) | h1) | h1 <;>
      rw [h1] at hnone <;> simp_all
  have hkeep : (!fe.strLit && InLean.litName ci.name) = false →
      ∀ n, InLean.litName n = true → (fe.push ci).find? n = fe.find? n := by
    intro hu n hn
    have hc : InLean.litName ci.name = false := by
      cases h : InLean.litName ci.name
      · rfl
      · rw [h, hlit h] at hu; cases hu
    exact hfind n fun he => by rw [he, hc] at hn; cases hn
  constructor
  · show (if (!fe.strLit && InLean.litName ci.name) = true then
        InLean.natLitStoredBy (InLean.findAt (InLean.addConst fe.env ci) fe.safety fe.coreAxioms)
      else fe.natLit) = _
    split
    · rfl
    · rename_i hu
      rw [hl.nat]
      exact natLitStoredBy_congr fun n hn => (hkeep (Bool.eq_false_iff.2 hu) n hn).symm
  · show (if (!fe.strLit && InLean.litName ci.name) = true then
        InLean.strLitStoredBy (InLean.findAt (InLean.addConst fe.env ci) fe.safety fe.coreAxioms)
      else fe.strLit) = _
    split
    · rfl
    · rename_i hu
      rw [hl.str]
      exact strLitStoredBy_congr fun n hn => (hkeep (Bool.eq_false_iff.2 hu) n hn).symm

/-- **A fresh push**: the flags' meaning kept, every other name's entry
unchanged (the step of the stage lemmas `litFlagsI_consSumCtorsF`, …). -/
theorem LitFlagsI.push_fresh (hlaws : EnvLaws) {fe : InLean.FEnv} (hl : LitFlagsI fe)
    {ci : Lean.ConstantInfo} (hfresh : fe.env.find? ci.name = none) :
    LitFlagsI (fe.push ci) ∧ ∀ n, n ≠ ci.name → (fe.push ci).env.find? n = fe.env.find? n :=
  ⟨hl.push hlaws hfresh, fun n hn => by
    show (InLean.addConst fe.env ci).find? n = _
    rw [find_addConst hlaws hfresh n, ite_eq_right hn]⟩

/-- **Fresh distinct pushes** keep the flags' meaning (`FEnv.pushAll`). -/
theorem LitFlagsI.pushAll (hlaws : EnvLaws) :
    ∀ (cs : List Lean.ConstantInfo) {fe : InLean.FEnv}, LitFlagsI fe →
      (∀ ci ∈ cs, fe.env.find? ci.name = none) → (cs.map (·.name)).Nodup →
      LitFlagsI (fe.pushAll cs)
  | [], _, hl, _, _ => hl
  | ci :: cs, fe, hl, hfr, hnd => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    obtain ⟨hl1, hold⟩ := hl.push_fresh hlaws (hfr ci List.mem_cons_self)
    exact LitFlagsI.pushAll hlaws cs hl1
      (fun d hd => by
        rw [hold _ fun h => hnd.1 ⟨d, hd, h⟩]; exact hfr d (List.mem_cons_of_mem _ hd))
      hnd.2

/-- No table for a fresh name: every stored table belongs to a stored constant. -/
theorem findTable_fresh (hP : EnvPresI fe L) {n : Name} (hn : fe.find? n = none)
    (news : List ConLeche.ConstantInfo) :
    (L.pushDelta news []).findTable? (toName n) = none := by
  unfold ConLeche.Env.findTable?
  split
  · simp only [ConLeche.Env.pushDelta, List.reverse_nil, List.nil_append]
    apply find_none_of_forall
    intro tbl ht
    have h := hP.tabNames tbl ht
    cases hb : tbl.structName == toName n
    · rfl
    · rw [eq_of_beq hb, hP.none n hn] at h; cases h
  · rfl

/-- The one-constant step, by `presI_push`: `news` is what con-leche installs,
related to `ci` where InLean sees it, empty where it hides it (`FEnv.sees`:
`sorryAx` at con-leche's policy, an `unsafe` or `partial` constant in a safe
check). -/
theorem presI_one (hlaws : EnvLaws) (hP : EnvPresI fe L) {ci : Lean.ConstantInfo}
    (hfresh : fe.env.find? ci.name = none) (hnotInd : ∀ v, ci ≠ .inductInfo v)
    {news : List ConLeche.ConstantInfo}
    (hnews : (news = [] ∧ fe.sees ci.name ci = false) ∨
      (∃ cci, news = [cci] ∧ cci.name = toName ci.name ∧
        EntryRelI { fe with env := InLean.addConst fe.env ci } ci cci ∧
        fe.sees ci.name ci = true)) :
    EnvPresI { fe with env := InLean.addConst fe.env ci } (L.pushDelta news []) := by
  have hfeNone : fe.find? ci.name = none := by
    simp only [FEnv.find?_eq_filter, hfresh, Option.filter_none]
  have hfe' : ({ fe with env := InLean.addConst fe.env ci } : InLean.FEnv).find? ci.name =
      if fe.sees ci.name ci = true then some ci else none := by
    simp only [FEnv.find?_eq_filter, find_addConst hlaws hfresh, ↓reduceIte, Option.filter_some]
    rfl
  apply presI_push (fe' := { fe with env := InLean.addConst fe.env ci }) (names := [ci.name]) hP
    rfl rfl rfl
  · intro n hn; simp only [List.mem_singleton] at hn; subst hn; exact hfresh
  · intro n hn
    simp only [List.mem_singleton] at hn
    show (InLean.addConst fe.env ci).find? n = _
    rw [find_addConst hlaws hfresh]; simp only [hn, ↓reduceIte]
  · intro c hc
    rcases hnews with ⟨rfl, -⟩ | ⟨cci, rfl, hname, -⟩
    · cases hc
    · simp only [List.mem_singleton] at hc; subst hc; exact ⟨ci.name, by simp, hname⟩
  · intro t ht; cases ht
  · intro n hn ci' hf
    simp only [List.mem_singleton] at hn; subst hn
    rw [hfe'] at hf
    rcases hnews with ⟨rfl, hs⟩ | ⟨cci, rfl, hname, hrel, hvis⟩
    · simp [hs] at hf
    · simp only [hvis, ↓reduceIte, Option.some.injEq] at hf
      subst hf
      refine ⟨cci, ?_, hrel⟩
      rw [pushDelta_find]
      simp [hname]
  · intro n hn hf
    simp only [List.mem_singleton] at hn; subst hn
    rw [hfe'] at hf
    rcases hnews with ⟨rfl, hs⟩ | ⟨cci, rfl, hname, hrel, hvis⟩
    · rw [pushDelta_find]; exact hP.none _ hfeNone
    · simp [hvis] at hf
  · intro T hT
    simp only [List.mem_singleton] at hT; subst hT
    rw [findTable_fresh hP hfeNone]
    simp only [TableRelI]
    unfold InLean.FEnv.findTable?
    rw [hfe']
    split
    · rename_i v heq
      split at heq
      · cases heq; exact absurd rfl (hnotInd v)
      · cases heq
    · rfl
  · intro t ht; cases ht

/-- A safe constant is seen unless it is `sorryAx` at con-leche's policy. -/
theorem sees_safe {fe : InLean.FEnv} {n : Name} {ci : Lean.ConstantInfo}
    (hs : InLean.safeConst ci = true) (hn : n = InLean.sorryAxName → fe.coreAxioms = true) :
    fe.sees n ci = true := by
  unfold InLean.FEnv.sees InLean.seesAt
  by_cases h : n = InLean.sorryAxName
  · rw [hn h]; cases fe.safety <;> simp [hs]
  · cases fe.safety <;> simp [h, hs]

/-- **An axiom** (`sorryAx` included: con-leche installs nothing for it, and
InLean hides it unless `coreAxioms`, so the relation needs `coreAxioms` off
there), safe (an unsafe one is hidden from the safe checks the relation is
about).  `Quot.sound` is installed as the quotient pin's slot; its step is
`presI_quotSound` (`StepPres.lean`). -/
theorem presI_axiom (hlaws : EnvLaws) (hP : EnvPresI fe L) {v : AxiomVal}
    {d : ConLeche.Declaration} (hd : toDecl [.axiomInfo v] = some d)
    (hfresh : fe.env.find? v.name = none) (hr : Expr.RangeOk v.type)
    (hq : v.name ≠ InLean.quotSoundName) (hsafe : v.isUnsafe = false)
    (hsorry : v.name = InLean.sorryAxName → fe.coreAxioms = false) :
    EnvPresI { fe with env := InLean.addConst fe.env (.axiomInfo v) }
      (L.pushDelta (ConLeche.declConstants d) (ConLeche.declTables d)) := by
  simp only [toDecl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hd
  obtain ⟨cv, hcv, rfl⟩ := hd
  have hrel := CVRel_of_toCV hcv hr
  have hname : cv.name = toName v.name := hrel.1
  have hq' : cv.name ≠ ConLeche.quotSoundName := by
    rw [hname, ← toName_quotSoundName]; exact fun h => hq (toName_inj h)
  simp only [ConLeche.declConstants, ConLeche.declTables, hq', ↓reduceIte]
  by_cases hs : v.name = InLean.sorryAxName
  · have hs' : cv.name = ConLeche.sorryAxName := by rw [hname, hs]; rfl
    simp only [hs', ↓reduceIte]
    exact presI_one (ci := .axiomInfo v) hlaws hP hfresh (fun _ h => by cases h)
      (.inl ⟨rfl, by
        simp [InLean.FEnv.sees, InLean.seesAt, show (Lean.ConstantInfo.axiomInfo v).name = v.name from rfl, hs,
          hsorry hs]⟩)
  · have hs' : cv.name ≠ ConLeche.sorryAxName := by
      rw [hname, ← toName_sorryAxName]; exact fun h => hs (toName_inj h)
    simp only [hs', ↓reduceIte]
    exact presI_one (ci := .axiomInfo v) hlaws hP hfresh (fun _ h => by cases h)
      (.inr ⟨_, rfl, hname, hrel,
        sees_safe (by simp [InLean.safeConst, Lean.ConstantInfo.isUnsafe, hsafe])
          (fun h => absurd h hs)⟩)

/-- **A safe definition** (an `unsafe` or `partial` one is hidden from the
safe checks the relation is about). -/
theorem presI_defn (hlaws : EnvLaws) (hP : EnvPresI fe L) {v : DefinitionVal}
    {d : ConLeche.Declaration} (hd : toDecl [.defnInfo v] = some d)
    (hfresh : fe.env.find? v.name = none) (hr : Expr.RangeOk v.type)
    (hrv : Expr.RangeOk v.value) (hsafe : v.safety = .safe)
    (hsorry : v.name = InLean.sorryAxName → fe.coreAxioms = true) :
    EnvPresI { fe with env := InLean.addConst fe.env (.defnInfo v) }
      (L.pushDelta (ConLeche.declConstants d) (ConLeche.declTables d)) := by
  simp only [toDecl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hd
  obtain ⟨cv, hcv, cval, hval, rfl⟩ := hd
  have hrel := CVRel_of_toCV hcv hr
  simp only [ConLeche.declConstants, ConLeche.declTables]
  exact presI_one (ci := .defnInfo v) hlaws hP hfresh (fun _ h => by cases h)
    (.inr ⟨_, rfl, hrel.1, ⟨hrel, StoredT_of hrv hval, toHint_eq_trHint _⟩,
      sees_safe (by simp only [InLean.safeConst, hsafe]) hsorry⟩)

/-- **A theorem** (con-leche stores its statement). -/
theorem presI_thm (hlaws : EnvLaws) (hP : EnvPresI fe L) {v : TheoremVal}
    {d : ConLeche.Declaration} (hd : toDecl [.thmInfo v] = some d)
    (hfresh : fe.env.find? v.name = none) (hr : Expr.RangeOk v.type)
    (hsorry : v.name = InLean.sorryAxName → fe.coreAxioms = true) :
    EnvPresI { fe with env := InLean.addConst fe.env (.thmInfo v) }
      (L.pushDelta (ConLeche.declConstants d) (ConLeche.declTables d)) := by
  simp only [toDecl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hd
  obtain ⟨cv, hcv, cval, -, rfl⟩ := hd
  have hrel := CVRel_of_toCV hcv hr
  simp only [ConLeche.declConstants, ConLeche.declTables]
  exact presI_one (ci := .thmInfo v) hlaws hP hfresh (fun _ h => by cases h)
    (.inr ⟨_, rfl, hrel.1, hrel,
      sees_safe (by simp [InLean.safeConst, Lean.ConstantInfo.isUnsafe]) hsorry⟩)

/-- **A safe `opaque`** (con-leche stores it as an axiom). -/
theorem presI_opaque (hlaws : EnvLaws) (hP : EnvPresI fe L) {v : OpaqueVal}
    {d : ConLeche.Declaration} (hd : toDecl [.opaqueInfo v] = some d)
    (hfresh : fe.env.find? v.name = none) (hr : Expr.RangeOk v.type)
    (hsafe : v.isUnsafe = false)
    (hsorry : v.name = InLean.sorryAxName → fe.coreAxioms = true) :
    EnvPresI { fe with env := InLean.addConst fe.env (.opaqueInfo v) }
      (L.pushDelta (ConLeche.declConstants d) (ConLeche.declTables d)) := by
  simp only [toDecl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hd
  obtain ⟨cv, hcv, cval, -, rfl⟩ := hd
  have hrel := CVRel_of_toCV hcv hr
  simp only [ConLeche.declConstants, ConLeche.declTables]
  exact presI_one (ci := .opaqueInfo v) hlaws hP hfresh (fun _ h => by cases h)
    (.inr ⟨_, rfl, hrel.1, hrel,
      sees_safe (by simp [InLean.safeConst, Lean.ConstantInfo.isUnsafe, hsafe]) hsorry⟩)

/-- **The start**: an environment InLean finds nothing in is related to
`Env.empty`. -/
theorem presI_empty (h : ∀ n, fe.find? n = none) : EnvPresI fe ConLeche.Env.empty where
  entry n ci hf := by rw [h n] at hf; cases hf
  none _ _ := rfl
  table T := by
    simp only [ConLeche.Env.findTable?, ConLeche.Env.find?, ConLeche.Env.empty, List.find?_nil,
      Option.isSome_none, Bool.false_eq_true, ↓reduceIte, TableRelI]
    unfold InLean.FEnv.findTable?
    rw [h T]
  tabNames _ ht := by cases ht

end One

/-! ## The groups stated, not proved here

The quotient package and an inductive block, each with what InLean checks as
the premise: InLean's own check of the group accepted (`checkQuotC`,
`checkIndDeclC` at the verified mode), the generated constants fresh, distinct
and in range, and the records `toDecl` reads off them.  What is left to prove
(a later lane's, with O7): the installed constants and tables against Lean's
entries, through `presI_push` — the capabilities (`capsOf` against
`blockCapsAt`, by `genEntriesAgree`), the firing modes (`recFireAt` against
`recFire`: both read the major's domain at the record's `majorIdx`), the
projection tables (`findTable?`/`projBodyAt` against `blockTables`/
`structProjBodies`), a pinned block's pins against the generated entries,
and the quotient pins at the record's names. -/

/-- **The quotient group keeps the relation** (stated). -/
@[expose] def QuotGroupPres : Prop :=
  EnvLaws → ∀ (fe : InLean.FEnv) (L : ConLeche.Env) (s s' : InLean.CState) (a : InLean.Added)
    (ds : List ConLeche.Declaration),
    EnvPresI fe L → (InLean.checkQuotC fe).run s = .ok (a, s') →
    a.consts.toList.mapM (fun ci => toDecl [ci]) = some ds →
    EnvPresI { fe with env := InLean.markQuot (a.consts.foldl InLean.addConst fe.env) }
      (ds.foldl (fun L d => L.pushDelta (ConLeche.declConstants d) (ConLeche.declTables d)) L)

/-- **An inductive block keeps the relation** (stated): the generator's
constants `consts`, accepted by InLean's inductive check as the stored block
(`storedBlock`), read as one record `d`. -/
@[expose] def IndGroupPres : Prop :=
  EnvLaws → ∀ (fe : InLean.FEnv) (L : ConLeche.Env) (consts : Array Lean.ConstantInfo) (nP : Nat)
    (s s' : InLean.CState) (d : ConLeche.Declaration),
    EnvPresI fe L →
    (∀ ci ∈ consts.toList, fe.env.find? ci.name = none) → (consts.toList.map (·.name)).Nodup →
    (∀ ci ∈ consts.toList, fe.sees ci.name ci = true) →
    consts.all InLean.constInRange = true →
    (InLean.checkIndDeclC .verified fe (InLean.storedBlock consts) nP).run s = .ok ((), s') →
    toDecl (InLean.storedBlock consts) = some d →
    EnvPresI { fe with env := consts.foldl InLean.addConst fe.env }
      (L.pushDelta (ConLeche.declConstants d) (ConLeche.declTables d))

end InLeanProof
