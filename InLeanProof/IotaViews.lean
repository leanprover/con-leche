module

public import InLeanProof.WalksIota
public import ConLeche.Verify.Cached.DiscC3
import ConLeche.Verify.InstList

/-!
# The ι step's readers through the translation (task #451, lane P2-whnf)

What InLean's ι step (`iotaRecI`, `prepareMajorI`, `majorToCtorI`) reads off
the environment and the terms, against what con-leche's pure ι step reads:

* **the recursor view** `EnvRecI fe env` (O4, lane P3's, beside `EnvViewI`):
  InLean's `recAt?` is the translation of con-leche's `.recInfo` record at
  the translated name, its counts `majorIdxOf`/`rulePrefixOf`, its K flag,
  and rule by rule its constructor, field count and firing mode
  (`recFireAt`, computed at use, against each rule's stored `fire`; a nested
  rule's pins are stored open terms, `StoredT`);
* the rescue's readers: `isCtorAppC`, `etaRescueTable?` (at the family's
  projection table), `andRescueSlotsF`;
* the level substitution `substLevelTreesM` and the nested rule's pins
  `pinArgsI` (the reversed-array instantiation is `instSpine`, master's
  `instSpine_eq_instantiateList`).
-/

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached
open scoped Lean.Order

variable {mode : ConLeche.CheckMode} {mi : InLean.CheckMode} {eager : Bool} {env : ConLeche.Env}

/-! ## Names -/

theorem cl_andName : ConLeche.andName = toName InLean.andName := rfl
theorem cl_andIntroName : ConLeche.andIntroName = toName InLean.andIntroName := rfl
theorem cl_quotMkName : ConLeche.quotMkName = toName InLean.quotMkName := rfl

/-- Membership through the (injective) name translation. -/
theorem contains_map_toName (l : List Name) (n : Name) :
    (l.map toName).contains (toName n) = l.contains n := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.contains_cons, ih, name_beq_eq_decide]
    by_cases h : toName n = toName a <;> simp [h]

/-! ## Level substitution -/

theorem trL_subst (ks : List Name) (vs : List Level) :
    ∀ {u : Level}, okL u = true →
      trL (Lvl.subst ks vs u) = ConLeche.Level.subst (ks.map toName) (vs.map trL) (trL u)
  | .zero, _ => rfl
  | .param n, _ => trL_substGo_gen ks vs n
  | .mvar _, h => by simp [okL] at h
  | .succ u, h => by
    simp only [okL] at h; simp only [Lvl.subst, trL, ConLeche.Level.subst, trL_subst ks vs h]
  | .max u w, h => by
    simp only [okL, Bool.and_eq_true] at h
    simp only [Lvl.subst, trL, ConLeche.Level.subst, trL_subst ks vs h.1, trL_subst ks vs h.2]
  | .imax u w, h => by
    simp only [okL, Bool.and_eq_true] at h
    simp only [Lvl.subst, trL, ConLeche.Level.subst, trL_subst ks vs h.1, trL_subst ks vs h.2]

theorem okL_substGoL : ∀ (ks : List Name) (vs : List Level) (n : Name),
    vs.all okL = true → okL (Lvl.substGo ks vs n) = true
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | k :: ks, v :: vs, n, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [Lvl.substGo]
    split
    · exact h.1
    · exact okL_substGoL ks vs n h.2

theorem okL_substL (ks : List Name) (vs : List Level) (hvs : vs.all okL = true) :
    ∀ {u : Level}, okL u = true → okL (Lvl.subst ks vs u) = true := by
  intro u
  induction u with
  | zero => intro _; rfl
  | param n => intro _; exact okL_substGoL ks vs n hvs
  | mvar _ => intro h; simp [okL] at h
  | succ u ih => intro h; simp only [okL, Lvl.subst] at h ⊢; exact ih h
  | max u w ihu ihw =>
    intro h; simp only [okL, Lvl.subst, Bool.and_eq_true] at h ⊢; exact ⟨ihu h.1, ihw h.2⟩
  | imax u w ihu ihw =>
    intro h; simp only [okL, Lvl.subst, Bool.and_eq_true] at h ⊢; exact ⟨ihu h.1, ihw h.2⟩

theorem okL_of_okLv {us : List Level} (h : us.all okLv = true) : us.all okL = true := by
  simp only [List.all_eq_true, okLv, Bool.and_eq_true] at h ⊢; exact fun u hu => (h u hu).1

/-- **The checked level substitution** (`substLevelTrees`' twin, at levels
with a reading). -/
theorem substLevelTreesM_specI {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀)
    {ks : List Name} {us ls : List Level} (hus : us.all okLv = true) (hls : ls.all okLv = true) :
    ⦃fun s => s = s₀⦄ InLean.substLevelTreesM ks us ls
    ⦃fun r s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ r.all okLv = true ∧
      r.map trL = (ls.map trL).map (ConLeche.Level.subst (ks.map toName) (us.map trL)); ⊤⦄ := by
  refine tripleI_iff_run.2 fun r s' hr => ?_
  have hus' : ∀ u ∈ us, depthS u ≤ maxLevelDepth := by
    intro u hu
    simp only [List.all_eq_true, okLv, Bool.and_eq_true, decide_eq_true_eq] at hus
    exact (hus u hu).2
  cases hc : EO.substLevelsChecked? ks us ls with
  | none =>
    simp [InLean.substLevelTreesM, hc, throw, throwThe, MonadExceptOf.throw, StateT.lift,
      Functor.map, Except.map] at hr
  | some r' =>
    simp only [InLean.substLevelTreesM, hc, pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    unfold EO.substLevelsChecked? at hc
    dsimp only at hc
    split at hc
    · rename_i hfit
      cases hc
      refine ⟨hs, TabLe.refl _, ?_, ?_⟩
      · simp only [List.all_eq_true, List.mem_map, okLv, Bool.and_eq_true,
          decide_eq_true_eq] at hls hfit ⊢
        rintro _ ⟨u, hu, rfl⟩
        exact ⟨okL_substL ks us (okL_of_okLv hus) (hls u hu).1,
          depthS_subst_of_fits hus' (hls u hu).2 (hfit u hu)⟩
      · simp only [List.map_map]
        apply List.map_congr_left
        intro u hu
        simp only [List.all_eq_true, okLv, Bool.and_eq_true] at hls
        exact trL_subst ks us (hls u hu).1
    · cases hc

/-! ## The rescue's readers -/

section Readers

variable {fe : InLean.FEnv}

/-- **Constructor-headedness** through the translation (no reading needed:
an untranslatable head is no constant on either side). -/
theorem isCtorAppC_TrS (hv : EnvViewI fe env) (s : InLean.CState) (e : Expr) :
    InLean.isCtorAppC fe e = ConLeche.isCtorApp env (TrS s e) := by
  unfold InLean.isCtorAppC ConLeche.isCtorApp
  split
  · rename_i cn us h
    rw [TrS_getAppFn_const s h]
    simp only
    cases hcv : fe.ctorView? cn with
    | none =>
      simp only [Option.isSome_none]
      split
      · rename_i cv nP nF T hf; exact absurd hf (hv.ctorNone cn hcv cv nP nF T)
      · rfl
    | some p =>
      obtain ⟨cv, nP, nF, T⟩ := p
      obtain ⟨ccv, -, hf⟩ := hv.ctor cn cv nP nF T hcv
      simp [hf]
  · rename_i h
    have hn := TrS_getAppFn_notConst s (fun n us he => h n us he)
    split
    · rename_i c us' h'; exact absurd h' (hn c us')
    · rfl

theorem map_toName_beq (a b : List Name) : (a.map toName == b.map toName) = (a == b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor
  · intro h
    induction a generalizing b with
    | nil => cases b <;> simp_all
    | cons x a ih =>
      cases b with
      | nil => simp at h
      | cons y b =>
        simp only [List.map_cons, List.cons.injEq] at h
        rw [toName_inj h.1, ih b h.2]
  · intro h; rw [h]

theorem toName_beq (a b : Name) : (toName a == toName b) = (a == b) := by
  rw [name_beq_eq_decide]
  by_cases h : toName a = toName b <;> simp [h]

theorem toName_bne (a b : Name) : (toName a != toName b) = (a != b) := by
  simp only [bne, toName_beq]

/-- **The structure-η rescue's standing condition** through the views: where
InLean's holds at the family's table, con-leche's holds at the related one. -/
theorem etaRescueTable_V_some (hv : EnvViewI fe env) {ctor T : Name} {cvj cvT : Lean.ConstantVal}
    {ccvj ccvT : ConLeche.ConstantVal} (hj : CVRel cvj ccvj) (hT : CVRel cvT ccvT)
    {caps : InLean.IndCaps} {t : InLean.TableView}
    (h : InLean.etaRescueTable? (fe.findTable? T) ctor cvj cvT caps = some t) :
    ∃ ct, ConLeche.etaRescueTable? (env.findTable? (toName T)) (toName ctor) ccvj ccvT
        (toCaps caps) = some ct ∧
      ct.ctor = toName t.ctor ∧ ct.numFields = t.numFields ∧ ct.numParams = t.numParams := by
  unfold InLean.etaRescueTable? at h
  unfold ConLeche.etaRescueTable?
  cases ht : fe.findTable? T with
  | none => rw [ht] at h; cases h
  | some t' =>
    rw [ht] at h
    obtain ⟨ct, hct, h1, h2, h3, -⟩ := hv.table T t' ht
    rw [hct]
    have hcond : ((toCaps caps).eta && ct.ctor == toName ctor &&
        ccvj.levelParams == ccvT.levelParams && toName ctor != ConLeche.andIntroName) =
        (caps.eta && t'.ctor == ctor && cvj.levelParams == cvT.levelParams &&
          ctor != InLean.andIntroName) := by
      rw [h1, hj.2.1, hT.2.1, cl_andIntroName]
      simp only [toCaps, toName_beq, map_toName_beq, toName_bne]
    simp only [hcond]
    cases hc : (caps.eta && t'.ctor == ctor && cvj.levelParams == cvT.levelParams &&
        ctor != InLean.andIntroName) with
    | false => simp [hc] at h
    | true =>
      simp only [hc, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨ct, by simp, h1, h2, h3⟩

/-- Where InLean's standing condition fails, con-leche's does. -/
theorem etaRescueTable_V_none (hv : EnvViewI fe env) {ctor T : Name} {cvj cvT : Lean.ConstantVal}
    {ccvj ccvT : ConLeche.ConstantVal} (hj : CVRel cvj ccvj) (hT : CVRel cvT ccvT)
    {caps : InLean.IndCaps}
    (h : InLean.etaRescueTable? (fe.findTable? T) ctor cvj cvT caps = none) :
    ConLeche.etaRescueTable? (env.findTable? (toName T)) (toName ctor) ccvj ccvT
        (toCaps caps) = none := by
  unfold InLean.etaRescueTable? at h
  unfold ConLeche.etaRescueTable?
  cases ht : fe.findTable? T with
  | none => rw [hv.tableNone T ht]
  | some t' =>
    rw [ht] at h
    obtain ⟨ct, hct, h1, -, -, -⟩ := hv.table T t' ht
    rw [hct]
    have hcond : ((toCaps caps).eta && ct.ctor == toName ctor &&
        ccvj.levelParams == ccvT.levelParams && toName ctor != ConLeche.andIntroName) =
        (caps.eta && t'.ctor == ctor && cvj.levelParams == cvT.levelParams &&
          ctor != InLean.andIntroName) := by
      rw [h1, hj.2.1, hT.2.1, cl_andIntroName]
      simp only [toCaps, toName_beq, map_toName_beq, toName_bne]
    simp only [hcond]
    cases hc : (caps.eta && t'.ctor == ctor && cvj.levelParams == cvT.levelParams &&
        ctor != InLean.andIntroName) with
    | false => simp
    | true => simp [hc] at h

/-- **`And`'s slots** through the views. -/
theorem andRescueSlotsF_V (hv : EnvViewI fe env) (ctor : Name) (nP : Nat) :
    fe.andRescueSlotsF ctor nP = ConLeche.andRescueSlots env (toName ctor) nP := by
  unfold InLean.FEnv.andRescueSlotsF ConLeche.andRescueSlots ConLeche.andRescueSlotsOf
  rw [cl_andName]
  congr 1
  funext j
  cases h : fe.findProj? InLean.andName j with
  | none => rw [hv.projNone _ j h]
  | some e =>
    obtain ⟨ce, hce, h1, h2, h3, -⟩ := hv.proj _ j e h
    rw [hce]
    simp only [h1, h2, h3, toName_beq]

end Readers

/-! ## The recursor view (O4, P3's) -/

/-- Two lists related elementwise. -/
inductive LRel {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : LRel R [] []
  | cons {a b as bs} : R a b → LRel R as bs → LRel R (a :: as) (b :: bs)

/-- A firing mode against con-leche's stored one: the levels translate, a
nested rule's pins are stored open terms. -/
@[expose] def FireRel : InLean.RecRuleFire → ConLeche.RecRuleFire → Prop
  | .plain, .plain => True
  | .nested lvls pins, .nested clvls cpins =>
    lvls.all okLv = true ∧ clvls = lvls.map trL ∧ LRel StoredT pins cpins
  | .levels lvls, .levels clvls => lvls.all okLv = true ∧ clvls = lvls.map trL
  | _, _ => False

/-- A rule against con-leche's: its constructor, its field count, and the
firing mode InLean computes at use against the one con-leche stores. -/
@[expose] def RuleRel (fire : InLean.RecRuleFire) (rl : Lean.RecursorRule)
    (crl : ConLeche.RecRule) : Prop :=
  crl.ctor = toName rl.ctor ∧ crl.nfields = rl.nfields ∧ FireRel fire crl.fire

/-- **The recursor view** (O4 with `EnvRelI`/`EnvViewI`, P3's): InLean's
recursor at a name (`recAt?`, the quotient eliminators included) is the
translation of con-leche's `.recInfo` record at the translated name, with
the counts read off Lean's (`majorIdxOf`, `rulePrefixOf`), the K flag, and
rule by rule the constructor, field count and firing mode (`recFireAt`,
computed at use); InLean has none exactly where con-leche records none. -/
structure EnvRecI (fe : InLean.FEnv) (env : ConLeche.Env) : Prop where
  recv : ∀ n rv q, fe.recAt? n = some (rv, q) → ∃ ccv crules, CVRel rv.toConstantVal ccv ∧
    env.find? (toName n) =
      some (.recInfo ccv (majorIdxOf rv) (rulePrefixOf rv) rv.k crules) ∧
    LRel (RuleRel (recFireAt rv q)) rv.rules crules
  recNone : ∀ n, fe.recAt? n = none →
    ∀ ccv mI rP isK rules, env.find? (toName n) ≠ some (.recInfo ccv mI rP isK rules)

/-- The rule found for a constructor, through the rule relation. -/
theorem find_rule_rel {fire : InLean.RecRuleFire} :
    ∀ {rules : List Lean.RecursorRule} {crules : List ConLeche.RecRule},
      LRel (RuleRel fire) rules crules → ∀ cj : Name,
      match rules.find? (fun r' => r'.ctor == cj) with
      | some rl => ∃ crl, crules.find? (fun r' => r'.ctor == toName cj) = some crl ∧
          RuleRel fire rl crl
      | none => crules.find? (fun r' => r'.ctor == toName cj) = none
  | [], [], .nil, _ => rfl
  | rl :: rules, crl :: crules, .cons h hs, cj => by
    have ih := find_rule_rel hs cj
    simp only [List.find?_cons]
    rw [h.1, toName_beq]
    cases hc : rl.ctor == cj with
    | true => exact ⟨crl, rfl, h⟩
    | false => exact ih

/-! ## The nested rule's pins -/

/-- **A nested rule's pins at use**: InLean's checked level instantiation and
reversed-array instantiation at closed leading arguments is master's
`pinInst` at the translation. -/
theorem pinArgsI_TrS {s : InLean.CState} {lps : List Name} {us : List Level}
    (hus : us.all okLv = true) {args : List Expr} (hargs : OkSL s args = true)
    (hcl : AllClosed (TrSL s args) = true) :
    ∀ {pins : List Expr} {cpins : List ConLeche.Expr} {ps : List Expr},
      LRel StoredT pins cpins →
      InLean.pinArgsI lps us args pins = some ps →
      OkSL s ps = true ∧
        TrSL s ps = cpins.map (pinInst (lps.map toName) (us.map trL) (TrSL s args)
          (args.length - 1))
  | [], [], ps, .nil, h => by
    simp only [InLean.pinArgsI, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  | p :: pins, cp :: cpins, ps, .cons hp hps, h => by
    simp only [InLean.pinArgsI] at h
    cases hq : EO.instLevelParamsChecked? p lps us with
    | none => simp [hq] at h
    | some q =>
      cases hr : InLean.pinArgsI lps us args pins with
      | none => simp [hq, hr] at h
      | some rs =>
        simp only [hq, hr, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        obtain ⟨ih1, ih2⟩ := pinArgsI_TrS hus hargs hcl hps hr
        have hus' : ∀ u ∈ us, depthS u ≤ maxLevelDepth := by
          intro u hu
          simp only [List.all_eq_true, okLv, Bool.and_eq_true, decide_eq_true_eq] at hus
          exact (hus u hu).2
        have hl : toLevels us = some (us.map trL) := toLevels_of_okLv hus
        obtain ⟨rfl, hrr, hm⟩ := instLevelParamsChecked_ok hp.2.1 hus' hq
        have htp : TransS s p = some cp := by
          unfold TransS; rw [toExpr_noFVar p hp.1]; exact hp.2.2
        have h := toExpr_instantiateLevelParams (fv := FVarTable.trans (tableOf s))
          hp.2.1 hp.1 htp lps hl hm
        obtain ⟨hokq, htrq⟩ := ok_of_TransS hrr h
        have hrev : OkSL s args.reverse = true := by
          simp only [OkSL, List.all_reverse] at hargs ⊢; exact hargs
        have hclr : AllClosed (TrSL s args.reverse) = true := by
          simp only [TrSL, AllClosed, List.map_reverse, List.all_reverse] at hcl ⊢; exact hcl
        obtain ⟨hok, htr⟩ := TrS_instI hokq hrev hclr
        rw [List.reverse_toArray] at *
        refine ⟨?_, ?_⟩
        · simp only [OkSL, List.all_cons, Bool.and_eq_true] at ih1 ⊢
          exact ⟨hok, ih1⟩
        · rw [TrSL_cons, ih2, List.map_cons, htr, htrq]
          congr 1
          unfold pinInst
          cases hA : args with
          | nil => simp [TrSL, ConLeche.Expr.instSpine, ConLeche.Expr.instantiateList_nil]
          | cons a as =>
            rw [ConLeche.Expr.instSpine_eq_instantiateList _ _ _ (by simp [TrSL])]
            simp [TrSL, List.map_reverse]

end InLeanProof
