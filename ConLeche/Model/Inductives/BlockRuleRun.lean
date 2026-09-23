module

public import ConLeche.Model.Inductives.BlockRuleFit
import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Model.Inductives.BlockFieldRead
import ConLeche.Model.Inductives.BlockRecOpenerRead
import ConLeche.Model.Inductives.BlockRecRegimes
import ConLeche.Verify.Rules.Bridge
import ConLeche.Verify.Inductives.BlockRecInv
import ConLeche.Model.Rules.Recompose
import ConLeche.Model.Tiers
import ConLeche.Model.Inductives.BlockRecIdxConv

public section

/-!
# The rule stage's peel obligation at the run (task #315, lane RM50)

`BlockRuleBodyOwed` (`BlockRuleFit.lean` §10) is what the residue
producer asks of the rule stage: at the contract's telescope and the
peel's outputs, `BlockRuleBodyInputs` at the lane's `ihs`/`Rb0`.  Its
function variables were unpinned — the peel came back existentially
and no definition computed `ihs` or `Rb0` — so it had no producer.

§A.9b (`BlockRecData.lean`) pins the peel's outputs to definitions;
this file pins the two function variables the same way
(`blockRuleIhsRunAV`, `blockRuleRbAV`) and produces the obligation's
rows from the run.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo BlockRuleFrame)

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## 1. `FieldReadAt` determines its readings -/

section FieldRead

/-- **`FieldReadAt`'s two readings are FUNCTIONS of its subject**: the
telescope's entries are `(0, bit, reading)` and the index readings are
the spine's.  So any datum a record hands `FieldReadAt` at is the
spelled one. -/
theorem fieldReadAt_eq {env : Env} {m : EnvModel V env} {ψ : Name → Nat} {nP nF q : Nat}
    {cty : Expr} {fvs0 : List Expr} {tl : List (Nat × Nat × AnnotTerm)} {Eis : List AnnotTerm}
    (h : FieldReadAt m ψ nP nF q cty fvs0 tl Eis) :
    tl = (List.range (ConLeche.structFieldTeleOf cty nP nF q).length).map (fun k =>
      ((0 : Nat), pwBit ψ ((ConLeche.structFieldTeleOf cty nP nF q).getD k default).2.pw,
        (denoteMeta m.acval env ψ (nP + q + k)
          (Expr.instSeq (fvs0.take (nP + q) ++ openFvars (nP + q) k) (nP + q + k - 1)
            ((ConLeche.structFieldTeleOf cty nP nF q).getD k default).1)).getD default)) ∧
    Eis = ((ConLeche.structFieldIdxOf cty nP nF q).map
        (Expr.instSeq (fvs0.take (nP + q)
          ++ openFvars (nP + q) (ConLeche.structFieldTeleOf cty nP nF q).length)
          (nP + q + (ConLeche.structFieldTeleOf cty nP nF q).length - 1))).map fun e =>
      (denoteMeta m.acval env ψ (nP + q + (ConLeche.structFieldTeleOf cty nP nF q).length)
        e).getD default := by
  obtain ⟨hlen, hent, hsp⟩ := h
  refine ⟨List.ext_getElem? fun k => ?_, ?_⟩
  · rw [List.getElem?_map]
    rcases Nat.lt_or_ge k (ConLeche.structFieldTeleOf cty nP nF q).length with hk | hk
    · rw [List.getElem?_range hk, Option.map_some]
      obtain ⟨b, hb⟩ : ∃ b, (ConLeche.structFieldTeleOf cty nP nF q)[k]? = some b :=
        ⟨_, List.getElem?_eq_getElem hk⟩
      obtain ⟨pr, hpr⟩ : ∃ pr, tl[k]? = some pr :=
        ⟨_, List.getElem?_eq_getElem (by rw [hlen]; exact hk)⟩
      obtain ⟨h1, h2, h3⟩ := hent k b pr hb hpr
      have hbd : (ConLeche.structFieldTeleOf cty nP nF q).getD k default = b := by
        rw [List.getD_eq_getElem?_getD, hb]; rfl
      rw [hpr, hbd, h3, Option.getD_some, ← h1, ← h2]
    · rw [List.getElem?_eq_none (by rw [hlen]; exact hk),
        List.getElem?_eq_none (by rw [List.length_range]; exact hk)]
      rfl
  · rw [hlen] at hsp
    exact (denoteMetaSpine_map_getD hsp).symm

end FieldRead

/-! ## 1b. Opener lists -/

section Openers

omit [SetTheory V] in
/-- The empty opening list. -/
theorem fvarList_nil : FvarList 0 [] :=
  ⟨rfl, fun _ hj => absurd hj (Nat.not_lt_zero _), fun _ hx => nomatch hx⟩

omit [SetTheory V] in
/-- **An opening EXTENDS an opener list**: opening `n` binders of a
subject scoped at `E`, at depth `E`, prepends the new openers (reversed)
to an `E`-long list. -/
theorem fvarList_of_open {E n : Nat} {L : List Expr} {e : Expr} {fvs : List Expr} {o : Expr}
    (hL : FvarList E L) (hop : ConLeche.openPisAtFvars n e E = some (fvs, o))
    (hw : Expr.WScoped E e) :
    FvarList (E + n) (fvs.reverse ++ L) := by
  have hlen : fvs.length = n := openPisAtFvars_length n hop
  have h := FvarList.openerExtend (r := n) hL
    (fun j x hx => ConLeche.openPisAtFvars_index n e E hop j x hx)
    (fun j x hx => openPisAtFvars_typeWScoped n hop hw j x hx) (by omega)
  rwa [List.take_of_length_le (by omega)] at h

end Openers

/-! ## 1c. Two generic facts: a field's parts past the telescope, and the
opened residue -/

section Generic

omit [SetTheory V] in
/-- **The field parts are BOUNDED at their own depth**, at every field
index (past the telescope both are empty). -/
theorem structFieldParts_bounded {cty : Expr} {nP nF : Nat}
    (hCf : cty.hasFvar = false) (hCb : cty.looseBVarsBounded 0 = true)
    (hstripC : (cty.stripPis (nP + nF)).isSome = true) (i : Nat) :
    (∀ (k : Nat) (b : Expr × ConLeche.BinderMeta),
        (ConLeche.structFieldTeleOf cty nP nF i)[k]? = some b →
        b.1.looseBVarsBounded (nP + i + k) = true) ∧
      ∀ e ∈ ConLeche.structFieldIdxOf cty nP nF i,
        e.looseBVarsBounded (nP + i + (ConLeche.structFieldTeleOf cty nP nF i).length) = true := by
  by_cases hi : i < nF
  · obtain ⟨htl, hix⟩ := structFieldTele_props (nP := nP) hCf hCb hstripC hi
    exact ⟨fun k b hk => (htl k b hk).2, fun e he => (hix e he).2⟩
  · obtain ⟨⟨cbs, cbody⟩, hs⟩ := Option.isSome_iff_exists.mp hstripC
    have hlenbs : cbs.length = nP + nF := Expr.stripPis_length _ hs
    have hdef : cbs.getD (nP + i) default = default :=
      getD_of_le _ (by omega)
    have htl : ConLeche.structFieldTeleOf cty nP nF i = [] := by
      simp only [ConLeche.structFieldTeleOf, hs, hdef]
      rfl
    have hix : ConLeche.structFieldIdxOf cty nP nF i = [] := by
      simp only [ConLeche.structFieldIdxOf, hs, hdef]
      show List.drop nP (default : Expr × ConLeche.BinderMeta).1.piBinders.2.getAppArgs = []
      rw [show (default : Expr × ConLeche.BinderMeta).1.piBinders.2.getAppArgs = [] from rfl,
        List.drop_nil]
    rw [htl, hix]
    exact ⟨fun k b hk => by simp at hk, fun e he => absurd he List.not_mem_nil⟩

omit [SetTheory V] in
/-- Past the telescope a field has no parts. -/
theorem structFieldParts_nil {cty : Expr} {nP nF i : Nat}
    (hstripC : (cty.stripPis (nP + nF)).isSome = true) (hi : ¬ i < nF) :
    ConLeche.structFieldTeleOf cty nP nF i = [] ∧ ConLeche.structFieldIdxOf cty nP nF i = [] := by
  obtain ⟨⟨cbs, cbody⟩, hs⟩ := Option.isSome_iff_exists.mp hstripC
  have hlenbs : cbs.length = nP + nF := Expr.stripPis_length _ hs
  have hdef : cbs.getD (nP + i) default = default :=
    getD_of_le _ (by omega)
  refine ⟨?_, ?_⟩
  · simp only [ConLeche.structFieldTeleOf, hs, hdef]
    rfl
  · simp only [ConLeche.structFieldIdxOf, hs, hdef]
    show List.drop nP (default : Expr × ConLeche.BinderMeta).1.piBinders.2.getAppArgs = []
    rw [show (default : Expr × ConLeche.BinderMeta).1.piBinders.2.getAppArgs = [] from rfl,
      List.drop_nil]

omit [SetTheory V] in
/-- **Opening a Π-tower's frame and then its binders is ONE opening of
its body**: the opened body is the stripped body instantiated at the
new openers (reversed) followed by the frame's list. -/
theorem openPis_body_instantiateList {n D : Nat} {e body0 o : Expr}
    {bs : List (Expr × ConLeche.BinderMeta)} {L fvs : List Expr}
    (hst : e.stripPis n = some (bs, body0))
    (hop : ConLeche.openPisAtFvars n (e.instantiateList L) D = some (fvs, o)) :
    o = body0.instantiateList (fvs.reverse ++ L) 0 := by
  obtain ⟨bs', hst', -, -⟩ := stripPis_instantiateList L n 0 hst
  have ho := ConLeche.Verify.openPisAtFvars_instSeq n hop hst'
  have hlen : fvs.length = n := openPisAtFvars_length n hop
  have hsplit := instantiateList_split fvs.reverse L body0 0
  rw [Nat.zero_add, List.length_reverse, hlen] at hsplit
  rw [ho, Nat.zero_add, ← hsplit]
  cases n with
  | zero =>
    obtain rfl : fvs = [] := List.eq_nil_of_length_eq_zero hlen
    rw [List.reverse_nil, Expr.instantiateList_nil]; rfl
  | succ n' =>
    rw [← Expr.instSpine_eq_instSeq]
    exact Expr.instSpine_eq_instantiateList fvs n' _ hlen

end Generic

/-! ## 1d. The constant-scoping kit

`ConstsBound` through the five term operations the rule stage's
frame is built from: lifting, the lifting instantiation, spines, the
two Π-instantiations and the `ih` tower — and through the abstraction
itself, from the recursors' environment down to the constructors'. -/

section ConstsKit

variable {env : Env}

omit [SetTheory V] in
theorem constsBound_liftLooseBVars (n : Nat) :
    ∀ (e : Expr) (c : Nat), ConstsBound env e → ConstsBound env (e.liftLooseBVars n c) := by
  intro e
  induction e with
  | bvar i => intro c _; rw [Expr.liftLooseBVars]; split <;> simp
  | sort u => intro c _; rw [Expr.liftLooseBVars]; simp
  | const nm us => intro c h; rw [Expr.liftLooseBVars]; exact h
  | fvar idx ty => intro c h; rw [Expr.liftLooseBVars]; exact h
  | lit l => intro c _; rw [Expr.liftLooseBVars]; simp
  | app f a ihf iha =>
    intro c h
    rw [constsBound_app] at h
    rw [Expr.liftLooseBVars, constsBound_app]
    exact ⟨ihf c h.1, iha c h.2⟩
  | lam ty b m ihty ihb =>
    intro c h
    rw [constsBound_lam] at h
    rw [Expr.liftLooseBVars, constsBound_lam]
    exact ⟨ihty c h.1, ihb (c + 1) h.2⟩
  | forallE ty b m ihty ihb =>
    intro c h
    rw [constsBound_forallE] at h
    rw [Expr.liftLooseBVars, constsBound_forallE]
    exact ⟨ihty c h.1, ihb (c + 1) h.2⟩
  | letE t val b iht ihval ihb =>
    intro c h
    rw [constsBound_letE] at h
    rw [Expr.liftLooseBVars, constsBound_letE]
    exact ⟨iht c h.1, ihval c h.2.1, ihb (c + 1) h.2.2⟩
  | proj s i e ihe =>
    intro c h
    rw [constsBound_proj] at h
    rw [Expr.liftLooseBVars, constsBound_proj]
    exact ihe c h

omit [SetTheory V] in
theorem constsBound_instantiate1Lift {v : Expr} (hv : ConstsBound env v) :
    ∀ (e : Expr) (d : Nat), ConstsBound env e →
      ConstsBound env (e.instantiate1Lift v d) := by
  intro e
  induction e with
  | bvar i =>
    intro d _
    rw [Expr.instantiate1Lift]
    split
    · exact constsBound_liftLooseBVars d v 0 hv
    · split <;> simp
  | sort u => intro d _; rw [Expr.instantiate1Lift]; simp
  | const n us => intro d h; rw [Expr.instantiate1Lift]; exact h
  | fvar idx ty => intro d h; rw [Expr.instantiate1Lift]; exact h
  | lit l => intro d _; rw [Expr.instantiate1Lift]; simp
  | app f a ihf iha =>
    intro d h
    rw [constsBound_app] at h
    rw [Expr.instantiate1Lift, constsBound_app]
    exact ⟨ihf d h.1, iha d h.2⟩
  | lam ty b m ihty ihb =>
    intro d h
    rw [constsBound_lam] at h
    rw [Expr.instantiate1Lift, constsBound_lam]
    exact ⟨ihty d h.1, ihb (d + 1) h.2⟩
  | forallE ty b m ihty ihb =>
    intro d h
    rw [constsBound_forallE] at h
    rw [Expr.instantiate1Lift, constsBound_forallE]
    exact ⟨ihty d h.1, ihb (d + 1) h.2⟩
  | letE t val b iht ihval ihb =>
    intro d h
    rw [constsBound_letE] at h
    rw [Expr.instantiate1Lift, constsBound_letE]
    exact ⟨iht d h.1, ihval d h.2.1, ihb (d + 1) h.2.2⟩
  | proj s i e ihe =>
    intro d h
    rw [constsBound_proj] at h
    rw [Expr.instantiate1Lift, constsBound_proj]
    exact ihe d h

omit [SetTheory V] in
theorem constsBound_mkAppN :
    ∀ (as : List Expr) {f : Expr}, ConstsBound env f → (∀ a ∈ as, ConstsBound env a) →
      ConstsBound env (Expr.mkAppN f as)
  | [], _, hf, _ => hf
  | a :: as, f, hf, has => by
    show ConstsBound env (Expr.mkAppN (Expr.app f a) as)
    refine constsBound_mkAppN as ?_ (fun x hx => has x (List.mem_cons_of_mem _ hx))
    rw [constsBound_app]
    exact ⟨hf, has a List.mem_cons_self⟩

omit [SetTheory V] in
theorem constsBound_instPisAtLift :
    ∀ (sp : List Expr) {e r : Expr}, Expr.instPisAtLift sp e = some r →
      ConstsBound env e → (∀ a ∈ sp, ConstsBound env a) → ConstsBound env r
  | [], e, r, h, he, _ => by
    simp only [Expr.instPisAtLift, Option.some.injEq] at h
    exact h ▸ he
  | a :: sp, e, r, h, he, hsp => by
    match e, h with
    | .forallE _ body _, h =>
      simp only [Expr.instPisAtLift] at h
      rw [constsBound_forallE] at he
      exact constsBound_instPisAtLift sp h
        (constsBound_instantiate1Lift (hsp a List.mem_cons_self) body 0 he.2)
        (fun x hx => hsp x (List.mem_cons_of_mem _ hx))

omit [SetTheory V] in
theorem constsBound_instPisAt :
    ∀ (sp : List Expr) {e : Expr} {ds : List Expr} {r : Expr},
      Expr.instPisAt sp e = some (ds, r) →
      ConstsBound env e → (∀ a ∈ sp, ConstsBound env a) → ConstsBound env r
  | [], e, ds, r, h, he, _ => by
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    exact h.2 ▸ he
  | a :: sp, e, ds, r, h, he, hsp => by
    match e, h with
    | .forallE _ body _, h =>
      simp only [Expr.instPisAt, Option.map_eq_some_iff] at h
      obtain ⟨⟨ds', r'⟩, h', heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨-, rfl⟩ := heq
      rw [constsBound_forallE] at he
      exact constsBound_instPisAt sp h'
        (ConstsBound.instantiate1 (hsp a List.mem_cons_self) body 0 he.2)
        (fun x hx => hsp x (List.mem_cons_of_mem _ hx))

omit [SetTheory V] in
theorem constsBound_mkPisOf :
    ∀ (bs : List (Expr × ConLeche.BinderMeta)) {body : Expr},
      (∀ b ∈ bs, ConstsBound env b.1) → ConstsBound env body →
      ConstsBound env (Expr.mkPisOf bs body)
  | [], _, _, hb => hb
  | (ty, mt) :: bs, body, hbs, hb => by
    show ConstsBound env (.forallE ty (Expr.mkPisOf bs body) mt)
    rw [constsBound_forallE]
    exact ⟨hbs (ty, mt) List.mem_cons_self,
      constsBound_mkPisOf bs (fun b hb' => hbs b (List.mem_cons_of_mem _ hb')) hb⟩

omit [SetTheory V] in
/-- **The generated `ih` tower keeps the constants of its pieces.** -/
theorem constsBound_blockIhPis {nP rP nF : Nat} {pw : ConLeche.PropWhen}
    {recTyOf : Nat → Expr} {teleOf : Nat → List (Expr × ConLeche.BinderMeta)}
    {idxOf : Nat → List Expr}
    (hrec : ∀ c, ConstsBound env (recTyOf c))
    (htele : ∀ i, ∀ b ∈ teleOf i, ConstsBound env b.1)
    (hidx : ∀ i, ∀ e ∈ idxOf i, ConstsBound env e) :
    ∀ (is : List (Nat × Nat)) (l : Nat) (body ihTele : Expr), ConstsBound env body →
      ConLeche.blockIhPis nP rP nF pw recTyOf teleOf idxOf is l body = some ihTele →
      ConstsBound env ihTele := by
  intro is
  induction is with
  | nil =>
    intro l body ihTele hb h
    rw [ConLeche.blockIhPis] at h
    cases Option.some.inj h; exact hb
  | cons ic is ih =>
    obtain ⟨i, c⟩ := ic
    intro l body ihTele hb h
    rw [ConLeche.blockIhPis] at h
    split at h
    · exact nomatch h
    · rename_i concl hinst
      rw [Option.map_eq_some_iff] at h
      obtain ⟨rest, hrest, rfl⟩ := h
      rw [constsBound_forallE]
      refine ⟨constsBound_mkPisOf _ (fun b hb' => ?_) ?_, ih (l + 1) body rest hb hrest⟩
      · simp only [ConLeche.structTeleAt, List.mem_map, List.mem_range] at hb'
        obtain ⟨k, hk, rfl⟩ := hb'
        show ConstsBound env (ConLeche.structIdxAt _ _ _ _ _ _)
        rw [ConLeche.structIdxAt]
        refine constsBound_liftLooseBVars _ _ _ (constsBound_liftLooseBVars _ _ _ ?_)
        exact htele i _ (getD_mem _ hk)
      · refine constsBound_instPisAtLift _ hinst (hrec c) (fun a ha => ?_)
        rcases List.mem_append.mp ha with ha | ha
        · rcases List.mem_append.mp ha with ha | ha
          · obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha; simp
          · obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
            rw [ConLeche.structIdxAt]
            exact constsBound_liftLooseBVars _ _ _ (constsBound_liftLooseBVars _ _ _ (hidx i e he))
        · obtain rfl := List.mem_singleton.mp ha
          refine constsBound_mkAppN _ (by simp) (fun x hx => ?_)
          obtain ⟨q, -, rfl⟩ := List.mem_map.mp hx; simp

omit [SetTheory V] in
/-- `stripLams`' binders and body inherit a term's bound. -/
theorem constsBound_stripLams :
    ∀ (n : Nat) {e : Expr} {bs : List (Expr × ConLeche.BinderMeta)} {body : Expr},
      ConstsBound env e → e.stripLams n = some (bs, body) → ConstsBound env body
  | 0, e, bs, body, he, h => by
    simp only [ConLeche.Expr.stripLams, Option.some.injEq, Prod.mk.injEq] at h
    exact h.2 ▸ he
  | n + 1, e, bs, body, he, h => by
    match e with
    | .lam ty b mb =>
      rw [constsBound_lam] at he
      simp only [ConLeche.Expr.stripLams, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs₀, body₀⟩, hst, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨-, rfl⟩ := heq
      exact constsBound_stripLams n he.2 hst
    | .bvar _ | .sort _ | .const _ _ | .lit _ | .fvar _ _ | .app _ _ | .forallE _ _ _
    | .letE _ _ _ | .proj _ _ _ => exact absurd h (by simp [ConLeche.Expr.stripLams])

omit [SetTheory V] in
/-- **The abstraction's residue is bounded BELOW the recursors**: every
constant it keeps is one the rule mentioned outside a guarded call, and
no such constant is a block recursor. -/
theorem abstractIh_constsBound {envC env' : Env} {fr : ConLeche.BlockRuleFrame}
    (hmono : ∀ n : Name, (env'.find? n).isSome = true →
      fr.recNames.contains n = false → (envC.find? n).isSome = true) :
    ∀ {e e'' : Expr} {d : Nat}, ConLeche.abstractIh fr d e = some e'' →
      ConstsBound env' e → ConstsBound envC e''
  | .bvar j, e'', d, hab, _ => by
    rw [ConLeche.abstractIh_bvar] at hab
    rw [← Option.some.inj hab]
    split <;> simp
  | .sort _, _, _, hab, _ | .lit _, _, _, hab, _ => by rw [← Option.some.inj hab]; simp
  | .const n us, e'', d, hab, hcb => by
    rw [ConLeche.abstractIh_const] at hab
    split at hab
    · exact nomatch hab
    · rename_i hn
      rw [← Option.some.inj hab, constsBound_const]
      rw [constsBound_const] at hcb
      exact hmono n hcb (by simpa using hn)
  | .fvar _ _, _, _, hab, _ => nomatch hab
  | .lam ty b bi, e'', d, hab, hcb => by
    rw [constsBound_lam] at hcb
    rw [ConLeche.abstractIh, Option.bind_eq_some_iff] at hab
    obtain ⟨ty', hty', hab⟩ := hab
    rw [Option.map_eq_some_iff] at hab
    obtain ⟨b', hb', rfl⟩ := hab
    rw [constsBound_lam]
    exact ⟨abstractIh_constsBound hmono hty' hcb.1, abstractIh_constsBound hmono hb' hcb.2⟩
  | .forallE ty b bi, e'', d, hab, hcb => by
    rw [constsBound_forallE] at hcb
    rw [ConLeche.abstractIh, Option.bind_eq_some_iff] at hab
    obtain ⟨ty', hty', hab⟩ := hab
    rw [Option.map_eq_some_iff] at hab
    obtain ⟨b', hb', rfl⟩ := hab
    rw [constsBound_forallE]
    exact ⟨abstractIh_constsBound hmono hty' hcb.1, abstractIh_constsBound hmono hb' hcb.2⟩
  | .letE ty v b, e'', d, hab, hcb => by
    rw [constsBound_letE] at hcb
    rw [ConLeche.abstractIh, Option.bind_eq_some_iff] at hab
    obtain ⟨ty', hty', hab⟩ := hab
    rw [Option.bind_eq_some_iff] at hab
    obtain ⟨v', hv', hab⟩ := hab
    rw [Option.map_eq_some_iff] at hab
    obtain ⟨b', hb', rfl⟩ := hab
    rw [constsBound_letE]
    exact ⟨abstractIh_constsBound hmono hty' hcb.1, abstractIh_constsBound hmono hv' hcb.2.1,
      abstractIh_constsBound hmono hb' hcb.2.2⟩
  | .proj sn i e, e'', d, hab, hcb => by
    rw [constsBound_proj] at hcb
    rw [ConLeche.abstractIh] at hab
    split at hab
    · exact nomatch hab
    rw [Option.map_eq_some_iff] at hab
    obtain ⟨e', he', rfl⟩ := hab
    rw [constsBound_proj]
    exact abstractIh_constsBound hmono he' hcb
  | .app f a, e'', d, hab, hcb => by
    rw [ConLeche.abstractIh_app] at hab
    revert hab
    cases hc : ConLeche.blockIhCall? fr d (.app f a) with
    | some ra =>
      intro hab
      obtain ⟨r, as⟩ := ra
      obtain rfl := Option.some.inj hab
      have has := blockIhCall?_args_constsBound hmono hc hcb
      refine constsBound_mkAppN _ (by simp) (fun x hx => ?_)
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact constsBound_liftLooseBVars _ y _ (has y hy)
    | none =>
      intro hab
      rw [constsBound_app] at hcb
      rw [Option.bind_eq_some_iff] at hab
      obtain ⟨f', hf', hab⟩ := hab
      rw [Option.map_eq_some_iff] at hab
      obtain ⟨a', ha', rfl⟩ := hab
      rw [constsBound_app]
      exact ⟨abstractIh_constsBound hmono hf' hcb.1, abstractIh_constsBound hmono ha' hcb.2⟩

omit [SetTheory V] in
/-- The recursors' bare environment finds only the recursors' names and
what the constructors' environment finds. -/
theorem find?_consBlockRecsBare_isSome {p : ConLeche.BlockShape} :
    ∀ (m : Nat) (cvRas : List (ConstantVal × Nat)) (env₀ : Env) (n : Name),
      ((ConLeche.consBlockRecsBare p m cvRas env₀).find? n).isSome = true →
      n ∈ cvRas.map (·.1.name) ∨ (env₀.find? n).isSome = true
  | _, [], _, _, h => Or.inr h
  | m, (cvRa, nIdx) :: rest, env₀, n, h => by
    rw [ConLeche.consBlockRecsBare] at h
    rcases find?_consBlockRecsBare_isSome (m + 1) rest _ n h with h' | h'
    · exact Or.inl (List.mem_cons_of_mem _ h')
    · rw [ConLeche.Env.find?_cons] at h'
      split at h'
      · rename_i heq
        exact Or.inl (by simp only [List.map_cons, List.mem_cons]; exact Or.inl heq.symm)
      · exact Or.inr h'

end ConstsKit

/-! ## 2. `ihs`, as a function of the run -/

section IhsRun

variable (pp : ConLeche.BlockParts)
  (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
  (acval : Name → (Name → Nat) → AnnotTerm) (envC : Env)

/-- **`ihs`, PINNED** — `blockRuleIhsAV` (§8 of `BlockRuleFit.lean`)
at the run's own frame, the checked elimination level and the spelled
field readings.  No choice is made anywhere, so the list is a function
of `ψ` through the readings alone. -/
@[expose] def blockRuleIhsRunAV (ψ : Name → Nat) (c i : Nat) : List AnnotTerm :=
  blockRuleIhsAV (Level.eval ψ (ConLeche.structElimLevel pp.elim pp.large)) rs.length
    (pp.toBlockShape.rulePrefixAt c - pp.nP) (blockRuleFrameAt pp rs c i)
    (blockRuleCtorOf rs c i).1.type ψ (blockRuleTlAV pp rs acval envC ψ c i)
    (blockRuleEisAV pp rs acval envC ψ c i)

end IhsRun

/-! ## 3. `BlockRuleBodyInputs` at the run -/

section BodyRun

open ConLeche (checkBlockRecK BlockParts BlockFieldKind)

variable {envC : Env} {p : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}

/-- **The rule's opened frame at the run** — the facts about the pinned
frame, residue and openers that need no reading of the constructor's
fields: the tower's scoping, the three opener lists, the openers'
closedness, constants and leaves, the residue's constants, and the
opened residue — the residue opened at the whole frame, scoped,
bvar-closed and TYPED there (so every valuation reads it).

`_Full` also returns the generated `ih` tower's three facts at the
prefix and field openers — its closedness, its leaves and its constants
(`blockRuleCerts_of_run`'s `hb₃`/`hfv₃`/`hc₃`, lane RM56); the unsuffixed
form below drops them. -/
theorem blockRuleOpenedFull_run (mpC : EnvModelM V μ envC)
    (h : checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[j]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    (hCf : cA.1.type.hasFvar = false) (hCb : cA.1.type.looseBVarsBounded 0 = true)
    (hcbC : ConstsBound envC cA.1.type)
    (hstripC : (cA.1.type.stripPis (p.nP + cA.2)).isSome = true)
    (hksLen : (blockRuleKsOf p j i).length = cA.2) :
    (blockRuleIhTeleAt p rs j i).hasFvar = false ∧
    FvarList (p.toBlockShape.rulePrefixAt j + cA.2)
      ((blockRuleFieldFvs p.toBlockShape rs j i).reverse
        ++ (blockRulePrefFvs p.toBlockShape rs j).reverse) ∧
    FvarList (p.toBlockShape.rulePrefixAt j + cA.2 + (blockRuleFrameAt p rs j i).nR)
      ((blockRuleFvsIhAt p rs j i).reverse ++ ((blockRuleFieldFvs p.toBlockShape rs j i).reverse
        ++ (blockRulePrefFvs p.toBlockShape rs j).reverse)) ∧
    (∀ x ∈ (blockRulePrefFvs p.toBlockShape rs j ++ blockRuleFieldFvs p.toBlockShape rs j i
        ++ blockRuleFvsIhAt p rs j i), (Expr.fvarTypeD x).looseBVarsBounded 0 = true) ∧
    (∀ x ∈ (blockRulePrefFvs p.toBlockShape rs j ++ blockRuleFieldFvs p.toBlockShape rs j i
        ++ blockRuleFvsIhAt p rs j i), ConstsBound envC x) ∧
    (∀ x ∈ (blockRulePrefFvs p.toBlockShape rs j ++ blockRuleFieldFvs p.toBlockShape rs j i
        ++ blockRuleFvsIhAt p rs j i), ∀ l ∈ (Expr.fvarTypeD x).fvarLeaves,
      Expr.fvar l.1 l.2 ∈ (blockRulePrefFvs p.toBlockShape rs j ++ blockRuleFieldFvs p.toBlockShape rs j i
        ++ blockRuleFvsIhAt p rs j i)) ∧
    ConstsBound envC (blockRuleResidAt p rs j i) ∧
    blockRuleBodyOAt p rs j i
      = (blockRuleResidAt p rs j i).instantiateList (blockRulePrefFvs p.toBlockShape rs j ++ blockRuleFieldFvs p.toBlockShape rs j i
        ++ blockRuleFvsIhAt p rs j i).reverse 0 ∧
    Expr.WScoped (p.toBlockShape.rulePrefixAt j + cA.2 + (blockRuleFrameAt p rs j i).nR) (blockRuleBodyOAt p rs j i) ∧
    (blockRuleBodyOAt p rs j i).looseBVarsBounded 0 = true ∧
    (∀ l ∈ (blockRuleBodyOAt p rs j i).fvarLeaves,
      Expr.fvar l.1 l.2 ∈ (blockRulePrefFvs p.toBlockShape rs j ++ blockRuleFieldFvs p.toBlockShape rs j i
        ++ blockRuleFvsIhAt p rs j i)) ∧
    Expr.WScoped (p.toBlockShape.rulePrefixAt j + cA.2)
      ((blockRuleIhTeleAt p rs j i).instantiateList (blockRulePrefFvs p.toBlockShape rs j
        ++ blockRuleFieldFvs p.toBlockShape rs j i).reverse) ∧
    (∀ ψ : Name → Nat, ∃ B, denoteMeta mpC.base2.acval envC ψ (p.toBlockShape.rulePrefixAt j + cA.2 + (blockRuleFrameAt p rs j i).nR)
      (blockRuleBodyOAt p rs j i) = some B) ∧
    ((blockRuleIhTeleAt p rs j i).instantiateList (blockRulePrefFvs p.toBlockShape rs j
      ++ blockRuleFieldFvs p.toBlockShape rs j i).reverse).looseBVarsBounded 0 = true ∧
    (∀ l ∈ ((blockRuleIhTeleAt p rs j i).instantiateList
        (blockRulePrefFvs p.toBlockShape rs j
          ++ blockRuleFieldFvs p.toBlockShape rs j i).reverse).fvarLeaves,
      Expr.fvar l.1 l.2 ∈ blockRulePrefFvs p.toBlockShape rs j
        ++ blockRuleFieldFvs p.toBlockShape rs j i) ∧
    ConstsBound envC ((blockRuleIhTeleAt p rs j i).instantiateList
      (blockRulePrefFvs p.toBlockShape rs j ++ blockRuleFieldFvs p.toBlockShape rs j i).reverse) := by
  have hct : blockRuleCtorOf rs j i = cA := blockRuleCtorOf_eq hr hcA
  obtain ⟨hfrP, hfrR, hfrF, hnames0, htgts, htele, hidxF, hpw⟩ :=
    blockRuleFrameAt_rows (pp := p) hct
  have hj : j < rs.length := (List.getElem?_eq_some_iff.mp hr).1
  obtain ⟨rbs, ty, concl, hstrip, hab, hpis, hopen, hinf, hconcl, hdeq⟩ :=
    blockRuleResidueData_runP h hr hcA hrhs
  obtain ⟨o₁, cpref, rbs', body', ldoms, lrest, h₁, hinstC, h₂, -, -, -, -, -⟩ :=
    blockRuleData_run h hr hcA hrhs
  -- the stored facts of the recursor type and of the rule
  obtain ⟨hTf, -, -, hTb, hrhsF⟩ := ConLeche.checkBlockRecK_facts h r (List.mem_of_getElem? hr)
  obtain ⟨hrf, -, -, hrb⟩ := hrhsF rhs (List.mem_of_getElem? hrhs)
  have hw₁ : Expr.WScoped 0 r.1.type := (checkBlockRecK_tyClosed h hr).1
  have hbodyF : (blockRuleBodyAt p rs j i).hasFvar = false :=
    (ConLeche.stripLams_not_hasFvar _ hstrip hrf).2
  have hresF : (blockRuleResidAt p rs j i).hasFvar = false := abstractIh_hasFvar hab hbodyF
  have hrecF : ∀ c' : Nat, ((rs.map (·.1.type)).getD c' (Expr.sort .zero)).hasFvar = false := by
    intro c'
    by_cases hc' : c' < rs.length
    · have hr' : rs[c']? = some rs[c'] := List.getElem?_eq_getElem hc'
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, hr']
      exact (ConLeche.checkBlockRecK_facts h _ (List.mem_of_getElem? hr')).1
    · rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by rw [List.length_map]; omega)]
      rfl
  have hihfv : (blockRuleIhTeleAt p rs j i).hasFvar = false := by
    refine blockIhPis_hasFvar (teleOf := (blockRuleFrameAt p rs j i).teleOf)
      (idxOf := (blockRuleFrameAt p rs j i).idxOf) hrecF (fun q b hb => ?_) (fun q e he => ?_)
      _ 0 _ _ hresF hpis
    · rw [htele] at hb; exact (structFieldParts_hasFvar hCf hCb hstripC).1 b hb
    · rw [hidxF] at he; exact (structFieldParts_hasFvar hCf hCb hstripC).2 e he
  -- the frame's three opener lists
  have hL1 : FvarList (p.toBlockShape.rulePrefixAt j)
      (blockRulePrefFvs p.toBlockShape rs j).reverse := by
    have := fvarList_of_open fvarList_nil h₁ hw₁
    rwa [Nat.zero_add, List.append_nil] at this
  have hL2 : FvarList (p.toBlockShape.rulePrefixAt j + cA.2)
      ((blockRuleFieldFvs p.toBlockShape rs j i).reverse
        ++ (blockRulePrefFvs p.toBlockShape rs j).reverse) :=
    fvarList_of_open hL1 h₂ (blockRuleHw2_of h₁ hw₁ hCf hinstC)
  have hL3 : FvarList (p.toBlockShape.rulePrefixAt j + cA.2 + (blockRuleFrameAt p rs j i).nR)
      ((blockRuleFvsIhAt p rs j i).reverse ++ ((blockRuleFieldFvs p.toBlockShape rs j i).reverse
        ++ (blockRulePrefFvs p.toBlockShape rs j).reverse)) := by
    have hopen' := hopen
    rw [List.reverse_append] at hopen'
    exact fvarList_of_open hL2 hopen' (wscoped_instantiateList hL2 _ hihfv 0)
  have hkeys : (blockRuleFrameAt p rs j i).ihKeys
      = ConLeche.blockIhKeys (p.toBlockShape.rulePrefixAt j)
        ((List.range p.recs.length).map p.toBlockShape.rulePrefixAt) p.recTgts
        (blockRuleKsOf p j i) := rfl
  have hrecB : ∀ c' : Nat,
      ((rs.map (·.1.type)).getD c' (Expr.sort .zero)).looseBVarsBounded 0 = true := by
    intro c'
    by_cases hc' : c' < rs.length
    · have hr' : rs[c']? = some rs[c'] := List.getElem?_eq_getElem hc'
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, hr']
      exact (ConLeche.checkBlockRecK_facts h _ (List.mem_of_getElem? hr')).2.2.2.1
    · rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by rw [List.length_map]; omega)]
      rfl
  have hopen2 : ConLeche.openPisAtFvars (blockRuleFrameAt p rs j i).nR
      ((blockRuleIhTeleAt p rs j i).instantiateList (blockRulePrefFvs p.toBlockShape rs j
        ++ blockRuleFieldFvs p.toBlockShape rs j i).reverse)
      (p.toBlockShape.rulePrefixAt j + cA.2)
      = some (blockRuleFvsIhAt p rs j i, blockRuleBodyOAt p rs j i) := hopen
  have hnPr : p.nP ≤ p.toBlockShape.rulePrefixAt j := by
    obtain ⟨-, hlenR, hall⟩ := checkBlockRecK_recNames h
    obtain ⟨-, -, -, -, -, -, hle, -⟩ := hall j (by omega)
    exact hle
  have hpos : 0 < p.toBlockShape.rulePrefixAt j + cA.2 :=
    ConLeche.checkBlockRecK_rulePos h j r hr i cA hcA
  -- the three subjects' constant scoping
  have hcT : ConstsBound envC r.1.type :=
    constsBound_of_constsResolve _ (ConLeche.checkBlockRecK_facts h r
      (List.mem_of_getElem? hr)).2.2.1
  have hc₂ : ConstsBound envC (blockRuleCrest p.toBlockShape rs j i) :=
    constsBound_instPisAt _ hinstC hcbC
      (fun a ha => (openPisAtFvars_constsBound _ hcT h₁).1 a (List.mem_of_mem_take ha))
  have hmono : ∀ n : Name,
      ((ConLeche.consBlockRecsBare p.toBlockShape 0 (rs.map fun r => (r.1, r.2.2.1))
        envC).find? n).isSome = true →
      (blockRuleFrameAt p rs j i).recNames.contains n = false → (envC.find? n).isSome = true := by
    intro n hn hnot
    rcases find?_consBlockRecsBare_isSome 0 _ envC n hn with hm | hm
    · rw [hnames0, checkBlockRecK_recNamesEq h] at hnot
      rw [List.map_map] at hm
      exact absurd (List.contains_iff_mem.mpr hm) (by simpa using hnot)
    · exact hm
  have hcbRhs := (ConLeche.checkBlockRecK_facts h r (List.mem_of_getElem? hr)).2.2.2.2 rhs
    (List.mem_of_getElem? hrhs)
  have hcbR : ConstsBound envC (blockRuleResidAt p rs j i) :=
    abstractIh_constsBound hmono hab
      (constsBound_stripLams _ (constsBound_of_constsResolve _ hcbRhs.2.2.1) hstrip)
  have hcbI : ConstsBound envC (blockRuleIhTeleAt p rs j i) := by
    refine constsBound_blockIhPis (teleOf := (blockRuleFrameAt p rs j i).teleOf)
      (idxOf := (blockRuleFrameAt p rs j i).idxOf) (fun c' => ?_) (fun q b hb => ?_)
      (fun q e he => ?_) _ 0 _ _ hcbR hpis
    · by_cases hc' : c' < rs.length
      · have hr' : rs[c']? = some rs[c'] := List.getElem?_eq_getElem hc'
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, hr']
        exact constsBound_of_constsResolve _
          (ConLeche.checkBlockRecK_facts h _ (List.mem_of_getElem? hr')).2.2.1
      · rw [List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by rw [List.length_map]; omega)]
        simp
    · rw [htele] at hb
      by_cases hq : q < cA.2
      · exact (constsBound_structFieldParts hcbC hq).1 b hb
      · rw [(structFieldParts_nil hstripC hq).1] at hb; exact absurd hb List.not_mem_nil
    · rw [hidxF] at he
      by_cases hq : q < cA.2
      · exact (constsBound_structFieldParts hcbC hq).2 e he
      · rw [(structFieldParts_nil hstripC hq).2] at he; exact absurd he List.not_mem_nil
  have hc₃ : ConstsBound envC ((blockRuleIhTeleAt p rs j i).instantiateList
      (blockRulePrefFvs p.toBlockShape rs j ++ blockRuleFieldFvs p.toBlockShape rs j i).reverse) := by
    refine constsBound_instantiateList (by rw [List.reverse_append]; exact hL2) (fun x hx => ?_)
      _ hihfv hcbI 0
    rcases List.mem_append.mp (List.mem_reverse.mp hx) with hx' | hx'
    · exact (openPisAtFvars_constsBound _ hcT h₁).1 x hx'
    · exact (openPisAtFvars_constsBound _ hc₂ h₂).1 x hx'
  -- the three subjects' closedness, and the tower's
  have hb₂ : (blockRuleCrest p.toBlockShape rs j i).looseBVarsBounded 0 = true :=
    (instPisAt_bounded _ hinstC hCb
      (fun a ha => openPisAtFvars_fvars_closed h₁ a (List.mem_of_mem_take ha))).2
  have hbodyB : (blockRuleBodyAt p rs j i).looseBVarsBounded
      (0 + (p.toBlockShape.rulePrefixAt j + cA.2)) = true := by
    exact stripLams_body_bounded (p.toBlockShape.rulePrefixAt j + cA.2) (j := 0) hstrip hrb
  have hresB := abstractIh_looseBVarsBounded hab hbodyB
  have hihlb : (blockRuleIhTeleAt p rs j i).looseBVarsBounded
      (p.toBlockShape.rulePrefixAt j + cA.2) = true := by
    have hq := blockIhPis_looseBVarsBounded (teleOf := (blockRuleFrameAt p rs j i).teleOf)
      (idxOf := (blockRuleFrameAt p rs j i).idxOf) hnPr hrecB
      (fun q k b hb => by
        rw [htele] at hb; exact (structFieldParts_bounded hCf hCb hstripC q).1 k b hb)
      (fun q e he => by
        rw [hidxF] at he; rw [htele]; exact (structFieldParts_bounded hCf hCb hstripC q).2 e he)
      (blockRuleFrameAt p rs j i).ihKeys 0 _ _
      (fun ic hic => by
        rw [hkeys] at hic
        have := (mem_blockIhKeys_kind (i := ic.1) (c' := ic.2) hic).1
        omega)
      (by rw [Nat.add_zero, ← Nat.zero_add (p.toBlockShape.rulePrefixAt j + cA.2)]
          exact hresB) hpis
    rwa [Nat.add_zero] at hq
  have hLcl : ∀ x ∈ (blockRulePrefFvs p.toBlockShape rs j
      ++ blockRuleFieldFvs p.toBlockShape rs j i).reverse, x.looseBVarsBounded 0 = true := by
    intro x hx
    rcases List.mem_append.mp (List.mem_reverse.mp hx) with hx' | hx'
    · exact openPisAtFvars_fvars_closed h₁ x hx'
    · exact openPisAtFvars_fvars_closed h₂ x hx'
  have hb₃ : ((blockRuleIhTeleAt p rs j i).instantiateList (blockRulePrefFvs p.toBlockShape rs j
      ++ blockRuleFieldFvs p.toBlockShape rs j i).reverse).looseBVarsBounded 0 = true :=
    blockRuleIhTeleClosed (by rw [List.reverse_append]; exact hL2) hLcl hihlb hpos
  obtain ⟨hlbF, hbO⟩ := blockRuleHlbF_of h₁ h₂ hopen2 hTb hb₂ hb₃
  -- the prefix and field openers' leaf closure (an empty third opening)
  have hclF0 := blockRuleHclF_of (nR := 0) (ihTele' := Expr.sort .zero) (o₃ := Expr.sort .zero)
    (fvsIh := []) h₁ h₂ rfl hTf hCf hinstC (fun l hl => by simp [Expr.fvarLeaves] at hl)
  have hfv₃ : ∀ l ∈ ((blockRuleIhTeleAt p rs j i).instantiateList
      (blockRulePrefFvs p.toBlockShape rs j
        ++ blockRuleFieldFvs p.toBlockShape rs j i).reverse).fvarLeaves,
      Expr.fvar l.1 l.2 ∈ blockRulePrefFvs p.toBlockShape rs j
        ++ blockRuleFieldFvs p.toBlockShape rs j i := by
    intro l hl
    obtain ⟨x, hx, hlx⟩ := fvarLeaves_instantiateList
      (by rw [List.reverse_append]; exact hL2) _ hihfv 0 l hl
    have hx' := List.mem_reverse.mp hx
    obtain ⟨q, hq⟩ := List.getElem?_of_mem hx'
    have hidxq : ∃ ty, x = Expr.fvar q ty := by
      rcases Nat.lt_or_ge q (blockRulePrefFvs p.toBlockShape rs j).length with hq' | hq'
      · rw [List.getElem?_append_left hq'] at hq
        obtain ⟨ty, hty⟩ := ConLeche.openPisAtFvars_index _ _ _ h₁ q x hq
        exact ⟨ty, by rw [hty, Nat.zero_add]⟩
      · rw [List.getElem?_append_right hq', openPisAtFvars_length _ h₁] at hq
        obtain ⟨ty, hty⟩ := ConLeche.openPisAtFvars_index _ _ _ h₂ _ x hq
        exact ⟨ty, by rw [hty]; congr 1; rw [openPisAtFvars_length _ h₁] at hq'; omega⟩
    obtain ⟨ty, rfl⟩ := hidxq
    simp only [Expr.fvarLeaves, List.mem_cons] at hlx
    rcases hlx with hlx | hlx
    · rw [hlx]; exact hx'
    · have hq := hclF0 _ (List.mem_append_left _ hx') l hlx
      rwa [List.append_nil] at hq
  have hclF := blockRuleHclF_of h₁ h₂ hopen2 hTf hCf hinstC hfv₃
  -- the opened residue IS the residue opened at the whole frame
  obtain ⟨bsI, hstI, -, -⟩ := stripPis_blockIhPis _ 0 _ _ hpis
  have hbodyO : blockRuleBodyOAt p rs j i
      = (blockRuleResidAt p rs j i).instantiateList (blockRulePrefFvs p.toBlockShape rs j
          ++ blockRuleFieldFvs p.toBlockShape rs j i ++ blockRuleFvsIhAt p rs j i).reverse 0 := by
    rw [List.reverse_append (as := blockRulePrefFvs p.toBlockShape rs j
      ++ blockRuleFieldFvs p.toBlockShape rs j i)]
    exact openPis_body_instantiateList hstI hopen2
  have hWS : Expr.WScoped (p.toBlockShape.rulePrefixAt j + cA.2 + (blockRuleFrameAt p rs j i).nR) (blockRuleBodyOAt p rs j i) :=
    (ConLeche.openPisAtFvars_WScoped _ _ _ hopen2 (wscoped_instantiateList
      (by rw [List.reverse_append]; exact hL2) _ hihfv 0)).2
  refine ⟨hihfv, hL2, hL3, hlbF, blockRuleHcbF_of h₁ h₂ hopen2 hcT hc₂ hc₃, hclF, hcbR, hbodyO,
    hWS, hbO, blockRuleHleaf_of hopen2 hfv₃,
    wscoped_instantiateList (by rw [List.reverse_append]; exact hL2) _ hihfv 0, fun ψ => ?_,
    hb₃, hfv₃, hc₃⟩
  exact acceptedReads_of mpC.base2 ψ hinf hWS hbO
    (fun l hl => hlbF _ (blockRuleHleaf_of hopen2 hfv₃ l hl))

/-- **The rule's opened frame at the run** — `blockRuleOpenedFull_run`
without the tower's three facts. -/
theorem blockRuleOpened_run (mpC : EnvModelM V μ envC)
    (h : checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[j]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    (hCf : cA.1.type.hasFvar = false) (hCb : cA.1.type.looseBVarsBounded 0 = true)
    (hcbC : ConstsBound envC cA.1.type)
    (hstripC : (cA.1.type.stripPis (p.nP + cA.2)).isSome = true)
    (hksLen : (blockRuleKsOf p j i).length = cA.2) :
    (blockRuleIhTeleAt p rs j i).hasFvar = false ∧
    FvarList (p.toBlockShape.rulePrefixAt j + cA.2)
      ((blockRuleFieldFvs p.toBlockShape rs j i).reverse
        ++ (blockRulePrefFvs p.toBlockShape rs j).reverse) ∧
    FvarList (p.toBlockShape.rulePrefixAt j + cA.2 + (blockRuleFrameAt p rs j i).nR)
      ((blockRuleFvsIhAt p rs j i).reverse ++ ((blockRuleFieldFvs p.toBlockShape rs j i).reverse
        ++ (blockRulePrefFvs p.toBlockShape rs j).reverse)) ∧
    (∀ x ∈ (blockRulePrefFvs p.toBlockShape rs j ++ blockRuleFieldFvs p.toBlockShape rs j i
        ++ blockRuleFvsIhAt p rs j i), (Expr.fvarTypeD x).looseBVarsBounded 0 = true) ∧
    (∀ x ∈ (blockRulePrefFvs p.toBlockShape rs j ++ blockRuleFieldFvs p.toBlockShape rs j i
        ++ blockRuleFvsIhAt p rs j i), ConstsBound envC x) ∧
    (∀ x ∈ (blockRulePrefFvs p.toBlockShape rs j ++ blockRuleFieldFvs p.toBlockShape rs j i
        ++ blockRuleFvsIhAt p rs j i), ∀ l ∈ (Expr.fvarTypeD x).fvarLeaves,
      Expr.fvar l.1 l.2 ∈ (blockRulePrefFvs p.toBlockShape rs j ++ blockRuleFieldFvs p.toBlockShape rs j i
        ++ blockRuleFvsIhAt p rs j i)) ∧
    ConstsBound envC (blockRuleResidAt p rs j i) ∧
    blockRuleBodyOAt p rs j i
      = (blockRuleResidAt p rs j i).instantiateList (blockRulePrefFvs p.toBlockShape rs j ++ blockRuleFieldFvs p.toBlockShape rs j i
        ++ blockRuleFvsIhAt p rs j i).reverse 0 ∧
    Expr.WScoped (p.toBlockShape.rulePrefixAt j + cA.2 + (blockRuleFrameAt p rs j i).nR) (blockRuleBodyOAt p rs j i) ∧
    (blockRuleBodyOAt p rs j i).looseBVarsBounded 0 = true ∧
    (∀ l ∈ (blockRuleBodyOAt p rs j i).fvarLeaves,
      Expr.fvar l.1 l.2 ∈ (blockRulePrefFvs p.toBlockShape rs j ++ blockRuleFieldFvs p.toBlockShape rs j i
        ++ blockRuleFvsIhAt p rs j i)) ∧
    Expr.WScoped (p.toBlockShape.rulePrefixAt j + cA.2)
      ((blockRuleIhTeleAt p rs j i).instantiateList (blockRulePrefFvs p.toBlockShape rs j
        ++ blockRuleFieldFvs p.toBlockShape rs j i).reverse) ∧
    ∀ ψ : Name → Nat, ∃ B, denoteMeta mpC.base2.acval envC ψ (p.toBlockShape.rulePrefixAt j + cA.2 + (blockRuleFrameAt p rs j i).nR)
      (blockRuleBodyOAt p rs j i) = some B := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, -⟩ :=
    blockRuleOpenedFull_run mpC h hr hcA hrhs hCf hCb hcbC hstripC hksLen
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩


/-- **The rule frame's openers READ to its context** — the certificate
bundle's `hdoms` row at the pinned openers and domains: the prefix off
the recursor type's binder data, the fields off the constructors'
record, the `ih` openers off `blockIhOpenerDom_run`.  Factored out of
`blockRuleBodyInputs_run`, whose first frame row it is. -/
theorem blockRuleFrameReads_run (hμ : μ.verifiedChecks = true) {mpC : EnvModelM V μ envC}
    (h : checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[j]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    -- the constructor's record, at the block's datum
    {d : BlockData V} {lps : List Name} {p₁ : ConLeche.BlockShape} {isRec : Bool}
    {A : Nat → (Name → Nat) → AnnotTerm} {nc : Nat}
    (hcore : BlockCtorsCore mpC.base2 d lps cvTas p₁ isRec A nc)
    (hcj : (d.ctorsM (p.toBlockShape.recTgtAt j))[i]? = some cA)
    (hdnP : d.nP = p.nP)
    (hks : d.ksF (p.toBlockShape.recTgtAt j) i
      = (blockRuleKsOf p j i).map BlockFieldKind.toRec)
    -- the stored constructor type's well-formedness
    (hCf : cA.1.type.hasFvar = false) (hCb : cA.1.type.looseBVarsBounded 0 = true)
    (hcbC : ConstsBound envC cA.1.type)
    (ψ : Name → Nat) :
    ∀ (q : Nat) (x : Expr),
      (blockRulePrefFvs p.toBlockShape rs j ++ blockRuleFieldFvs p.toBlockShape rs j i
        ++ blockRuleFvsIhAt p rs j i)[q]? = some x →
      denoteMeta mpC.base2.acval envC ψ q (Expr.fvarTypeD x)
        = some (((blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i).reverse
            ++ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j
              ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ j i).reverse).getD
            (p.toBlockShape.rulePrefixAt j + cA.2 + (blockRuleFrameAt p rs j i).nR - 1 - q)
            default) := by
  have hct : blockRuleCtorOf rs j i = cA := blockRuleCtorOf_eq hr hcA
  obtain ⟨hfrP, hfrR, hfrF, hnames0, htgts, htele, hidxF, hpw⟩ :=
    blockRuleFrameAt_rows (pp := p) hct
  have hj : j < rs.length := (List.getElem?_eq_some_iff.mp hr).1
  obtain ⟨rbs, ty, concl, hstrip, hab, hpis, hopen, hinf, hconcl, hdeq⟩ :=
    blockRuleResidueData_runP h hr hcA hrhs
  obtain ⟨o₁, cpref, rbs', body', ldoms, lrest, h₁, hinstC, h₂, -, -, -, -, -⟩ :=
    blockRuleData_run h hr hcA hrhs
  -- the constructor's record, and its full opening
  have hcd := blockCtorData_of_core hcore hcj
  rw [hdnP] at hcd
  obtain ⟨crestC, hoP, hoF⟩ := hcd.opens
  have hop0 : ConLeche.openPisAtFvars (p.nP + cA.2) cA.1.type 0
      = some (d.fvsPF (p.toBlockShape.recTgtAt j) i ++ d.xFvsF (p.toBlockShape.recTgtAt j) i,
          d.xrestF (p.toBlockShape.recTgtAt j) i) :=
    openPisAtFvars_add p.nP hoP (by rw [Nat.zero_add]; exact hoF)
  have hcfv : blockRuleCtorFvs p rs j i
      = d.fvsPF (p.toBlockShape.recTgtAt j) i ++ d.xFvsF (p.toBlockShape.recTgtAt j) i := by
    rw [blockRuleCtorFvs, hct, hop0]; rfl
  obtain ⟨bsC, bodyC0, hstC, -, -, -⟩ := ConLeche.Verify.openPisAtFvars_stripPis _ hop0
  have hstripC : (cA.1.type.stripPis (p.nP + cA.2)).isSome = true := by rw [hstC]; rfl
  have hkeys : (blockRuleFrameAt p rs j i).ihKeys
      = ConLeche.blockIhKeys (p.toBlockShape.rulePrefixAt j)
        ((List.range p.recs.length).map p.toBlockShape.rulePrefixAt) p.recTgts
        (blockRuleKsOf p j i) := rfl
  have hksLen : (blockRuleKsOf p j i).length = cA.2 := by
    have := hcd.ksLen; rw [hks, List.length_map] at this; exact this
  obtain ⟨hihfv, hL2, hL3, hlbF, hcbF, hclF, hcbR, hbodyO, hWS, hbO, -, -, hreadAll⟩ :=
    blockRuleOpened_run mpC h hr hcA hrhs hCf hCb hcbC hstripC hksLen
  -- ROW: the constructor's opening
  have hrow1 : ConLeche.openPisAtFvars ((blockRuleFrameAt p rs j i).nP
      + (blockRuleFrameAt p rs j i).nF) cA.1.type 0
      = some (blockRuleCtorFvs p rs j i,
          ((ConLeche.openPisAtFvars (p.nP + cA.2) cA.1.type 0).map (·.2)).getD default) := by
    rw [hfrP, hfrF, hcfv, hop0]; rfl
  have hrow2 : (cA.1.type.stripPis ((blockRuleFrameAt p rs j i).nP
      + (blockRuleFrameAt p rs j i).nF)).isSome = true := by
    rw [hfrP, hfrF]; exact hstripC
  -- ROW: the telescope readings' lengths
  have hrow3 : ∀ q, (blockRuleTlAV p rs mpC.base2.acval envC ψ j i q).length
      = (ConLeche.structFieldTeleOf cA.1.type (blockRuleFrameAt p rs j i).nP
          (blockRuleFrameAt p rs j i).nF q).length := by
    intro q
    simp only [blockRuleTlAV, hct, hfrP, hfrF, List.length_map, List.length_range]
  -- ROW: the fields' readings, at every key
  have hfldM : ∀ q c' : Nat, (q, c') ∈ (blockRuleFrameAt p rs j i).ihKeys →
      q < (blockRuleFrameAt p rs j i).nF ∧
        FieldReadAt mpC.base2 ψ (blockRuleFrameAt p rs j i).nP (blockRuleFrameAt p rs j i).nF q
          cA.1.type (blockRuleCtorFvs p rs j i) (blockRuleTlAV p rs mpC.base2.acval envC ψ j i q)
          (blockRuleEisAV p rs mpC.base2.acval envC ψ j i q) := by
    intro q c' hm
    rw [hkeys] at hm
    obtain ⟨hqF, hk⟩ := mem_blockIhKeys_kind hm
    have hF := blockFieldReadAt_of (ψ := ψ) hcd hop0 (show q < cA.2 by omega)
      (by rw [hks]; exact hk)
    obtain ⟨e1, e2⟩ := fieldReadAt_eq hF
    have eT : blockRuleTlAV p rs mpC.base2.acval envC ψ j i q
        = ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD q []) := by
      rw [e1]; simp only [blockRuleTlAV, hct, hcfv]
    have eE : blockRuleEisAV p rs mpC.base2.acval envC ψ j i q
        = ((d.eissF (p.toBlockShape.recTgtAt j) i ψ).getD q []) := by
      rw [e2]; simp only [blockRuleEisAV, hct, hcfv]
    refine ⟨by rw [hfrF]; omega, ?_⟩
    rw [hfrP, hfrF, hcfv, eT, eE]
    exact hF
  have hrow4 : ∀ q c' k : Nat,
      ConLeche.pairIdxOf? (blockRuleFrameAt p rs j i).ihKeys (q, c') = some k →
      q < (blockRuleFrameAt p rs j i).nF ∧
        FieldReadAt mpC.base2 ψ (blockRuleFrameAt p rs j i).nP (blockRuleFrameAt p rs j i).nF q
          cA.1.type (blockRuleCtorFvs p rs j i) (blockRuleTlAV p rs mpC.base2.acval envC ψ j i q)
          (blockRuleEisAV p rs mpC.base2.acval envC ψ j i q) :=
    fun q c' _ hk => hfldM q c' (mem_of_pairIdxOf? hk)
  -- ROW: the callees' stored types, at every key (past the family: the default)
  have hrecTyM : ∀ c' : Nat,
      ((rs.map (·.1.type)).getD c' (Expr.sort .zero)).hasFvar = false ∧
        ((rs.map (·.1.type)).getD c' (Expr.sort .zero)).looseBVarsBounded 0 = true ∧
        ∃ TVa : AnnotTerm, denoteMeta mpC.base2.acval envC ψ 0
          ((rs.map (·.1.type)).getD c' (Expr.sort .zero)) = some TVa := by
    intro c'
    by_cases hc' : c' < rs.length
    · have hr' : rs[c']? = some rs[c'] := List.getElem?_eq_getElem hc'
      have hg : (rs.map (·.1.type)).getD c' (.sort .zero) = rs[c'].1.type := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, hr']; rfl
      rw [hg]
      obtain ⟨hf, -, -, hb, -⟩ := ConLeche.checkBlockRecK_facts h _ (List.mem_of_getElem? hr')
      obtain ⟨-, -, -, hread, -⟩ := checkBlockRecK_tyPis hμ mpC h hr' ψ
      exact ⟨hf, hb, _, hread⟩
    · rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by rw [List.length_map]; omega)]
      exact ⟨rfl, rfl, AnnotTerm.sort (Level.eval ψ Level.zero), by simp [denoteMeta]⟩
  have hrow5 : ∀ q c' k : Nat,
      ConLeche.pairIdxOf? (blockRuleFrameAt p rs j i).ihKeys (q, c') = some k →
      ((rs.map (·.1.type)).getD c' (Expr.sort .zero)).hasFvar = false ∧
        ((rs.map (·.1.type)).getD c' (Expr.sort .zero)).looseBVarsBounded 0 = true ∧
        ∃ TVa : AnnotTerm, denoteMeta mpC.base2.acval envC ψ 0
          ((rs.map (·.1.type)).getD c' (Expr.sort .zero)) = some TVa :=
    fun _ c' _ _ => hrecTyM c'
  -- ROW: the block's level arguments
  have hrow6 : (blockRuleFrameAt p rs j i).rlvls = r.1.levelParams.map Level.param := by
    obtain ⟨-, hlenR, hall⟩ := checkBlockRecK_recNames h
    obtain ⟨rc, r0, hrc, hr0, -, hcv, -⟩ := hall 0 (by omega)
    have hl0 : r0.1.levelParams = rc.cvR.levelParams := (ConLeche.checkConstantVal_lps hcv).2
    have hlr : r.1.levelParams = r0.1.levelParams := checkBlockRecK_lps h hr hr0
    show (p.recs.head?.map fun q => q.cvR.levelParams.map Level.param).getD [] = _
    rw [List.head?_eq_getElem?, hrc, hlr, hl0]
    rfl
  have hrow8 : FvarList ((blockRuleFrameAt p rs j i).rP + (blockRuleFrameAt p rs j i).nF)
      (blockRulePrefFvs p.toBlockShape rs j ++ blockRuleFieldFvs p.toBlockShape rs j i).reverse := by
    rw [hfrR, hfrF, List.reverse_append]; exact hL2
  -- ROWS: the three lengths
  have hlenP : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j).length
      = (blockRuleFrameAt p rs j i).rP := by
    rw [blockRulePdomsAV_length hμ mpC h hr ψ, hfrR]
  have hlenF : (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ j i).length
      = (blockRuleFrameAt p rs j i).nF := by
    rw [blockRuleFdomsAV, readOpenedDoms_length_eq, openPisAtFvars_length _ h₂, hfrF]
  have hopen2 : ConLeche.openPisAtFvars (blockRuleFrameAt p rs j i).nR
      ((blockRuleIhTeleAt p rs j i).instantiateList (blockRulePrefFvs p.toBlockShape rs j
        ++ blockRuleFieldFvs p.toBlockShape rs j i).reverse)
      (p.toBlockShape.rulePrefixAt j + cA.2)
      = some (blockRuleFvsIhAt p rs j i, blockRuleBodyOAt p rs j i) := hopen
  have hlenI : (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i).length
      = (blockRuleFrameAt p rs j i).nR := by
    rw [blockRuleIhdomsAV, readOpenedDoms_length_eq]
    exact openPisAtFvars_length _ hopen2
  -- the recursor's prefix floor, and the rule's non-empty frame
  have hnPr : p.nP ≤ p.toBlockShape.rulePrefixAt j := by
    obtain ⟨-, hlenR, hall⟩ := checkBlockRecK_recNames h
    obtain ⟨-, -, -, -, -, -, hle, -⟩ := hall j (by omega)
    exact hle
  have hpos : 0 < p.toBlockShape.rulePrefixAt j + cA.2 :=
    ConLeche.checkBlockRecK_rulePos h j r hr i cA hcA
  -- the `ih` openers' readings (`blockIhOpenerDom_run`)
  have hpisF : ConLeche.blockIhPis (blockRuleFrameAt p rs j i).nP (blockRuleFrameAt p rs j i).rP
      (blockRuleFrameAt p rs j i).nF (blockRuleFrameAt p rs j i).pw
      (fun c' => (rs.map (·.1.type)).getD c' (.sort .zero)) (blockRuleFrameAt p rs j i).teleOf
      (blockRuleFrameAt p rs j i).idxOf (blockRuleFrameAt p rs j i).ihKeys 0
      (blockRuleResidAt p rs j i) = some (blockRuleIhTeleAt p rs j i) := by
    rw [hfrP, hfrR, hfrF]; exact hpis
  have hopenF : ConLeche.openPisAtFvars (blockRuleFrameAt p rs j i).ihKeys.length
      ((blockRuleIhTeleAt p rs j i).instantiateList (blockRulePrefFvs p.toBlockShape rs j
        ++ blockRuleFieldFvs p.toBlockShape rs j i).reverse)
      ((blockRuleFrameAt p rs j i).rP + (blockRuleFrameAt p rs j i).nF)
      = some (blockRuleFvsIhAt p rs j i, blockRuleBodyOAt p rs j i) := by
    rw [hfrR, hfrF]; exact hopen2
  have hopDom := blockIhOpenerDom_run (mT := mpC.base2) (ψ := ψ)
    (o := p.toBlockShape.rulePrefixAt j - p.nP)
    (by rw [hfrR, hfrP]) (by rw [hfrP, hfrR]; omega) hrow1 hCf hCb hrow2
    (by rw [hfrP, hfrF]; exact htele) (by rw [hfrP, hfrF]; exact hidxF) hrow3
    (fun q c' _ hk => hfldM q c' (List.mem_of_getElem? hk))
    (fun _ c' _ _ => hrecTyM c') hpisF hihfv hrow8 hopenF
  have hexI : ∀ (l : Nat) (x : Expr), (blockRuleFvsIhAt p rs j i)[l]? = some x →
      ∃ A, denoteMeta mpC.base2.acval envC ψ (p.toBlockShape.rulePrefixAt j + cA.2 + l)
        (Expr.fvarTypeD x) = some A := by
    intro l x hx
    have hl : l < (blockRuleFrameAt p rs j i).ihKeys.length := by
      have := (List.getElem?_eq_some_iff.mp hx).1
      rw [openPisAtFvars_length _ hopenF] at this
      exact this
    obtain ⟨_, _, -, -, hread⟩ := hopDom ((blockRuleFrameAt p rs j i).ihKeys[l]).1
      ((blockRuleFrameAt p rs j i).ihKeys[l]).2 l x (List.getElem?_eq_getElem hl) hx
    rw [hfrR, hfrF] at hread
    exact ⟨_, hread⟩
  exact blockRuleHdoms_of (hlenP.trans hfrR) (hlenF.trans hfrF) hlenI
    (openPisAtFvars_length _ h₁) (openPisAtFvars_length _ h₂) (openPisAtFvars_length _ hopen2)
    (blockRulePdomsAV_reads hμ mpC h hr ψ h₁)
    (blockRuleFdomsAV_eq h hr hcA hrhs hcd hCf hnPr ψ).2
    (fun l x hx => by rw [blockRuleIhdomsAV, hct]; exact readOpenedDoms_reads hexI l x hx)

/-- **`BlockRuleBodyInputs` at the run**, at the pinned frame, residue,
openers, `ihs` and `Rb0`.  Every row is the check's or the model's:
the constructor's opening and its field readings (the constructors'
record, through `fieldReadAt_eq`), the callees' stored types, the level
arguments, the generated tower's scoping, closedness, constants and
leaves (§1c/§1d), the frame's openers and readings (`blockIhOpenerDom_run`
for the `ih` segment), and the residue's reading and typing (the opened
residue IS the residue opened at the whole frame,
`openPis_body_instantiateList`; `acceptedReads_of`; the certified
grade).  Two rows stay premises, neither the rule stage's: the
frame's grading `hokA` (the certificate lane's) and the `ih` fit
`hihFit` (the regime's). -/
theorem blockRuleBodyInputs_run (hμ : μ.verifiedChecks = true) {mpC : EnvModelM V μ envC}
    (h : checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[j]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    -- the constructor's record, at the block's datum
    {d : BlockData V} {lps : List Name} {p₁ : ConLeche.BlockShape} {isRec : Bool}
    {A : Nat → (Name → Nat) → AnnotTerm} {nc : Nat}
    (hcore : BlockCtorsCore mpC.base2 d lps cvTas p₁ isRec A nc)
    (hcj : (d.ctorsM (p.toBlockShape.recTgtAt j))[i]? = some cA)
    (hdnP : d.nP = p.nP)
    (hks : d.ksF (p.toBlockShape.recTgtAt j) i
      = (blockRuleKsOf p j i).map BlockFieldKind.toRec)
    -- the stored constructor type's well-formedness
    (hCf : cA.1.type.hasFvar = false) (hCb : cA.1.type.looseBVarsBounded 0 = true)
    (hcbC : ConstsBound envC cA.1.type)
    (ψ : Name → Nat) {σ : Nat → V} {xs fs : List V}
    -- the frame's GRADING (the certificate lane's: `blockRuleHokA_of_run`'s conclusion)
    (hokA : ∀ l, l < p.toBlockShape.rulePrefixAt j + cA.2 + (blockRuleFrameAt p rs j i).nR →
      ∀ (σ' : Nat → V) (ys : List V),
        SpineFit σ' ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j
            ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ j i
            ++ blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i).take l) ys →
        WellDenotedV V (consList ys σ')
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j
            ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ j i
            ++ blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i).getD l default))
    -- the `ih` openers' FIT (the regime's)
    (hihFit : SpineFit (consList (xs ++ fs) σ)
      (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i)
      ((blockRuleIhsRunAV p rs mpC.base2.acval envC ψ j i).map
        (interp V (consList (xs ++ fs) σ)))) :
    BlockRuleBodyInputs V mpC p rs ψ
      (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large))
      j i cA r.1.levelParams (blockRuleFrameAt p rs j i) (rs.map (·.1.type))
      (blockRuleResidAt p rs j i) (blockRuleIhTeleAt p rs j i) (blockRuleFvsIhAt p rs j i)
      (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j)
      (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ j i)
      σ xs fs (blockRuleIhsRunAV p rs mpC.base2.acval envC ψ j i)
      (blockRuleRbAV p rs mpC.base2.acval envC ψ j i) := by
  have hct : blockRuleCtorOf rs j i = cA := blockRuleCtorOf_eq hr hcA
  obtain ⟨hfrP, hfrR, hfrF, hnames0, htgts, htele, hidxF, hpw⟩ :=
    blockRuleFrameAt_rows (pp := p) hct
  have hj : j < rs.length := (List.getElem?_eq_some_iff.mp hr).1
  obtain ⟨rbs, ty, concl, hstrip, hab, hpis, hopen, hinf, hconcl, hdeq⟩ :=
    blockRuleResidueData_runP h hr hcA hrhs
  obtain ⟨o₁, cpref, rbs', body', ldoms, lrest, h₁, hinstC, h₂, -, -, -, -, -⟩ :=
    blockRuleData_run h hr hcA hrhs
  -- the constructor's record, and its full opening
  have hcd := blockCtorData_of_core hcore hcj
  rw [hdnP] at hcd
  obtain ⟨crestC, hoP, hoF⟩ := hcd.opens
  have hop0 : ConLeche.openPisAtFvars (p.nP + cA.2) cA.1.type 0
      = some (d.fvsPF (p.toBlockShape.recTgtAt j) i ++ d.xFvsF (p.toBlockShape.recTgtAt j) i,
          d.xrestF (p.toBlockShape.recTgtAt j) i) :=
    openPisAtFvars_add p.nP hoP (by rw [Nat.zero_add]; exact hoF)
  have hcfv : blockRuleCtorFvs p rs j i
      = d.fvsPF (p.toBlockShape.recTgtAt j) i ++ d.xFvsF (p.toBlockShape.recTgtAt j) i := by
    rw [blockRuleCtorFvs, hct, hop0]; rfl
  obtain ⟨bsC, bodyC0, hstC, -, -, -⟩ := ConLeche.Verify.openPisAtFvars_stripPis _ hop0
  have hstripC : (cA.1.type.stripPis (p.nP + cA.2)).isSome = true := by rw [hstC]; rfl
  have hkeys : (blockRuleFrameAt p rs j i).ihKeys
      = ConLeche.blockIhKeys (p.toBlockShape.rulePrefixAt j)
        ((List.range p.recs.length).map p.toBlockShape.rulePrefixAt) p.recTgts
        (blockRuleKsOf p j i) := rfl
  have hksLen : (blockRuleKsOf p j i).length = cA.2 := by
    have := hcd.ksLen; rw [hks, List.length_map] at this; exact this
  obtain ⟨hihfv, hL2, hL3, hlbF, hcbF, hclF, hcbR, hbodyO, hWS, hbO, -, -, hreadAll⟩ :=
    blockRuleOpened_run mpC h hr hcA hrhs hCf hCb hcbC hstripC hksLen
  -- ROW: the constructor's opening
  have hrow1 : ConLeche.openPisAtFvars ((blockRuleFrameAt p rs j i).nP
      + (blockRuleFrameAt p rs j i).nF) cA.1.type 0
      = some (blockRuleCtorFvs p rs j i,
          ((ConLeche.openPisAtFvars (p.nP + cA.2) cA.1.type 0).map (·.2)).getD default) := by
    rw [hfrP, hfrF, hcfv, hop0]; rfl
  have hrow2 : (cA.1.type.stripPis ((blockRuleFrameAt p rs j i).nP
      + (blockRuleFrameAt p rs j i).nF)).isSome = true := by
    rw [hfrP, hfrF]; exact hstripC
  -- ROW: the telescope readings' lengths
  have hrow3 : ∀ q, (blockRuleTlAV p rs mpC.base2.acval envC ψ j i q).length
      = (ConLeche.structFieldTeleOf cA.1.type (blockRuleFrameAt p rs j i).nP
          (blockRuleFrameAt p rs j i).nF q).length := by
    intro q
    simp only [blockRuleTlAV, hct, hfrP, hfrF, List.length_map, List.length_range]
  -- ROW: the fields' readings, at every key
  have hfldM : ∀ q c' : Nat, (q, c') ∈ (blockRuleFrameAt p rs j i).ihKeys →
      q < (blockRuleFrameAt p rs j i).nF ∧
        FieldReadAt mpC.base2 ψ (blockRuleFrameAt p rs j i).nP (blockRuleFrameAt p rs j i).nF q
          cA.1.type (blockRuleCtorFvs p rs j i) (blockRuleTlAV p rs mpC.base2.acval envC ψ j i q)
          (blockRuleEisAV p rs mpC.base2.acval envC ψ j i q) := by
    intro q c' hm
    rw [hkeys] at hm
    obtain ⟨hqF, hk⟩ := mem_blockIhKeys_kind hm
    have hF := blockFieldReadAt_of (ψ := ψ) hcd hop0 (show q < cA.2 by omega)
      (by rw [hks]; exact hk)
    obtain ⟨e1, e2⟩ := fieldReadAt_eq hF
    have eT : blockRuleTlAV p rs mpC.base2.acval envC ψ j i q
        = ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD q []) := by
      rw [e1]; simp only [blockRuleTlAV, hct, hcfv]
    have eE : blockRuleEisAV p rs mpC.base2.acval envC ψ j i q
        = ((d.eissF (p.toBlockShape.recTgtAt j) i ψ).getD q []) := by
      rw [e2]; simp only [blockRuleEisAV, hct, hcfv]
    refine ⟨by rw [hfrF]; omega, ?_⟩
    rw [hfrP, hfrF, hcfv, eT, eE]
    exact hF
  have hrow4 : ∀ q c' k : Nat,
      ConLeche.pairIdxOf? (blockRuleFrameAt p rs j i).ihKeys (q, c') = some k →
      q < (blockRuleFrameAt p rs j i).nF ∧
        FieldReadAt mpC.base2 ψ (blockRuleFrameAt p rs j i).nP (blockRuleFrameAt p rs j i).nF q
          cA.1.type (blockRuleCtorFvs p rs j i) (blockRuleTlAV p rs mpC.base2.acval envC ψ j i q)
          (blockRuleEisAV p rs mpC.base2.acval envC ψ j i q) :=
    fun q c' _ hk => hfldM q c' (mem_of_pairIdxOf? hk)
  -- ROW: the callees' stored types, at every key (past the family: the default)
  have hrecTyM : ∀ c' : Nat,
      ((rs.map (·.1.type)).getD c' (Expr.sort .zero)).hasFvar = false ∧
        ((rs.map (·.1.type)).getD c' (Expr.sort .zero)).looseBVarsBounded 0 = true ∧
        ∃ TVa : AnnotTerm, denoteMeta mpC.base2.acval envC ψ 0
          ((rs.map (·.1.type)).getD c' (Expr.sort .zero)) = some TVa := by
    intro c'
    by_cases hc' : c' < rs.length
    · have hr' : rs[c']? = some rs[c'] := List.getElem?_eq_getElem hc'
      have hg : (rs.map (·.1.type)).getD c' (.sort .zero) = rs[c'].1.type := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, hr']; rfl
      rw [hg]
      obtain ⟨hf, -, -, hb, -⟩ := ConLeche.checkBlockRecK_facts h _ (List.mem_of_getElem? hr')
      obtain ⟨-, -, -, hread, -⟩ := checkBlockRecK_tyPis hμ mpC h hr' ψ
      exact ⟨hf, hb, _, hread⟩
    · rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by rw [List.length_map]; omega)]
      exact ⟨rfl, rfl, AnnotTerm.sort (Level.eval ψ Level.zero), by simp [denoteMeta]⟩
  have hrow5 : ∀ q c' k : Nat,
      ConLeche.pairIdxOf? (blockRuleFrameAt p rs j i).ihKeys (q, c') = some k →
      ((rs.map (·.1.type)).getD c' (Expr.sort .zero)).hasFvar = false ∧
        ((rs.map (·.1.type)).getD c' (Expr.sort .zero)).looseBVarsBounded 0 = true ∧
        ∃ TVa : AnnotTerm, denoteMeta mpC.base2.acval envC ψ 0
          ((rs.map (·.1.type)).getD c' (Expr.sort .zero)) = some TVa :=
    fun _ c' _ _ => hrecTyM c'
  -- ROW: the block's level arguments
  have hrow6 : (blockRuleFrameAt p rs j i).rlvls = r.1.levelParams.map Level.param := by
    obtain ⟨-, hlenR, hall⟩ := checkBlockRecK_recNames h
    obtain ⟨rc, r0, hrc, hr0, -, hcv, -⟩ := hall 0 (by omega)
    have hl0 : r0.1.levelParams = rc.cvR.levelParams := (ConLeche.checkConstantVal_lps hcv).2
    have hlr : r.1.levelParams = r0.1.levelParams := checkBlockRecK_lps h hr hr0
    show (p.recs.head?.map fun q => q.cvR.levelParams.map Level.param).getD [] = _
    rw [List.head?_eq_getElem?, hrc, hlr, hl0]
    rfl
  have hrow8 : FvarList ((blockRuleFrameAt p rs j i).rP + (blockRuleFrameAt p rs j i).nF)
      (blockRulePrefFvs p.toBlockShape rs j ++ blockRuleFieldFvs p.toBlockShape rs j i).reverse := by
    rw [hfrR, hfrF, List.reverse_append]; exact hL2
  -- ROWS: the three lengths
  have hlenP : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j).length
      = (blockRuleFrameAt p rs j i).rP := by
    rw [blockRulePdomsAV_length hμ mpC h hr ψ, hfrR]
  have hlenF : (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ j i).length
      = (blockRuleFrameAt p rs j i).nF := by
    rw [blockRuleFdomsAV, readOpenedDoms_length_eq, openPisAtFvars_length _ h₂, hfrF]
  have hopen2 : ConLeche.openPisAtFvars (blockRuleFrameAt p rs j i).nR
      ((blockRuleIhTeleAt p rs j i).instantiateList (blockRulePrefFvs p.toBlockShape rs j
        ++ blockRuleFieldFvs p.toBlockShape rs j i).reverse)
      (p.toBlockShape.rulePrefixAt j + cA.2)
      = some (blockRuleFvsIhAt p rs j i, blockRuleBodyOAt p rs j i) := hopen
  have hlenI : (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i).length
      = (blockRuleFrameAt p rs j i).nR := by
    rw [blockRuleIhdomsAV, readOpenedDoms_length_eq]
    exact openPisAtFvars_length _ hopen2
  -- the recursor's prefix floor, and the rule's non-empty frame
  have hnPr : p.nP ≤ p.toBlockShape.rulePrefixAt j := by
    obtain ⟨-, hlenR, hall⟩ := checkBlockRecK_recNames h
    obtain ⟨-, -, -, -, -, -, hle, -⟩ := hall j (by omega)
    exact hle
  have hpos : 0 < p.toBlockShape.rulePrefixAt j + cA.2 :=
    ConLeche.checkBlockRecK_rulePos h j r hr i cA hcA
  have hreadO := hreadAll ψ
  refine (blockRuleBodyInputs_iff ..).mpr ⟨blockRuleCtorFvs p rs j i,
    ((ConLeche.openPisAtFvars (p.nP + cA.2) cA.1.type 0).map (·.2)).getD default,
    blockRuleTlAV p rs mpC.base2.acval envC ψ j i, blockRuleEisAV p rs mpC.base2.acval envC ψ j i,
    blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i,
    hrow1, hCf, hCb, hrow2, hcbC, hrow3, hrow4, hrow5, hrow6, hihfv, hrow8, hlenP, hlenF, hlenI,
    ?_, ?_, ?_, ?_, ?_, ?_, hihFit, ?_, ?_, ?_, ?_⟩
  · -- the frame's readings, segment by segment
    rw [hfrR, hfrF]
    exact blockRuleFrameReads_run hμ h hr hcA hrhs hcore hcj hdnP hks hCf hCb hcbC ψ
  · -- the frame's grading
    rw [hfrR, hfrF]
    exact blockRuleHokΔ_of (hlenP.trans hfrR) (hlenF.trans hfrF) hlenI hokA
  · exact hlbF
  · exact hcbF
  · exact hclF
  · -- `ihs` IS the pinned list
    simp only [blockRuleIhsRunAV, hfrR, hfrP, hct]
  · exact hcbR
  · -- the whole frame's openers
    rw [List.reverse_append, List.reverse_append]; exact hL3
  · -- the residue's reading: the opened residue is typed, so it reads
    obtain ⟨B, hB⟩ := hreadO
    rw [← hbodyO, hB, blockRuleRbAV, hct, ← hbodyO, hB]; rfl
  · -- the residue is typed at the certified grade
    rw [← hbodyO]
    obtain rfl := CheckMode.eq_verified hμ
    exact ⟨ty, ConLeche.Rules.inferTypeCore_bridge hinf⟩

/-- **The spelled field readings ARE the record's**, at every field the
frame keys an `ih` opener to (`fieldReadAt_eq` against the record's own
`FieldReadAt`) — so `ihs` is the record's `ih` list wherever it reads. -/
theorem blockRuleTlEis_eq_record {mpC : EnvModelM V μ envC}
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[j]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {d : BlockData V} {lps : List Name} {p₁ : ConLeche.BlockShape} {isRec : Bool}
    {A : Nat → (Name → Nat) → AnnotTerm} {nc : Nat}
    (hcore : BlockCtorsCore mpC.base2 d lps cvTas p₁ isRec A nc)
    (hcj : (d.ctorsM (p.toBlockShape.recTgtAt j))[i]? = some cA)
    (hdnP : d.nP = p.nP)
    (hks : d.ksF (p.toBlockShape.recTgtAt j) i
      = (blockRuleKsOf p j i).map BlockFieldKind.toRec)
    (ψ : Name → Nat) {q c' : Nat} (hm : (q, c') ∈ (blockRuleFrameAt p rs j i).ihKeys) :
    blockRuleTlAV p rs mpC.base2.acval envC ψ j i q
        = (d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD q [] ∧
      blockRuleEisAV p rs mpC.base2.acval envC ψ j i q
        = (d.eissF (p.toBlockShape.recTgtAt j) i ψ).getD q [] := by
  have hct : blockRuleCtorOf rs j i = cA := blockRuleCtorOf_eq hr hcA
  have hcd := blockCtorData_of_core hcore hcj
  rw [hdnP] at hcd
  obtain ⟨crestC, hoP, hoF⟩ := hcd.opens
  have hop0 : ConLeche.openPisAtFvars (p.nP + cA.2) cA.1.type 0
      = some (d.fvsPF (p.toBlockShape.recTgtAt j) i ++ d.xFvsF (p.toBlockShape.recTgtAt j) i,
          d.xrestF (p.toBlockShape.recTgtAt j) i) :=
    openPisAtFvars_add p.nP hoP (by rw [Nat.zero_add]; exact hoF)
  have hcfv : blockRuleCtorFvs p rs j i
      = d.fvsPF (p.toBlockShape.recTgtAt j) i ++ d.xFvsF (p.toBlockShape.recTgtAt j) i := by
    rw [blockRuleCtorFvs, hct, hop0]; rfl
  have hksLen : (blockRuleKsOf p j i).length = cA.2 := by
    have := hcd.ksLen; rw [hks, List.length_map] at this; exact this
  obtain ⟨hqF, hk⟩ := mem_blockIhKeys_kind (rPs := (List.range p.recs.length).map
    p.toBlockShape.rulePrefixAt) (recTgts := p.recTgts) (rP := p.toBlockShape.rulePrefixAt j) hm
  have hF := blockFieldReadAt_of (ψ := ψ) hcd hop0 (show q < cA.2 by omega)
    (by rw [hks]; exact hk)
  obtain ⟨e1, e2⟩ := fieldReadAt_eq hF
  exact ⟨by rw [e1]; simp only [blockRuleTlAV, hct, hcfv],
    by rw [e2]; simp only [blockRuleEisAV, hct, hcfv]⟩

/-- **`ihs` is bounded at the chain frame**: every `ih` opener's term
reads under the `K` chain binders and the rule's own frame. -/
theorem blockRuleIhsRunAV_below {mpC : EnvModelM V μ envC}
    (h : checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[j]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {d : BlockData V} {lps : List Name} {p₁ : ConLeche.BlockShape} {isRec : Bool}
    {A : Nat → (Name → Nat) → AnnotTerm} {nc : Nat}
    (hcore : BlockCtorsCore mpC.base2 d lps cvTas p₁ isRec A nc)
    (hcj : (d.ctorsM (p.toBlockShape.recTgtAt j))[i]? = some cA)
    (hdnP : d.nP = p.nP)
    (hks : d.ksF (p.toBlockShape.recTgtAt j) i
      = (blockRuleKsOf p j i).map BlockFieldKind.toRec)
    (ψ : Name → Nat) :
    ∀ v ∈ blockRuleIhsRunAV p rs mpC.base2.acval envC ψ j i,
      Term.bvarsBelow (rs.length + p.toBlockShape.rulePrefixAt j + cA.2) v.erase := by
  have hct : blockRuleCtorOf rs j i = cA := blockRuleCtorOf_eq hr hcA
  obtain ⟨hfrP, hfrR, hfrF, -, -, -, -, -⟩ := blockRuleFrameAt_rows (pp := p) hct
  have hcd := blockCtorData_of_core hcore hcj
  have hksLen : (blockRuleKsOf p j i).length = cA.2 := by
    have := hcd.ksLen; rw [hks, List.length_map] at this; exact this
  have hnPr : p.nP ≤ p.toBlockShape.rulePrefixAt j := by
    obtain ⟨-, hlenR, hall⟩ := checkBlockRecK_recNames h
    obtain ⟨-, -, -, -, -, -, hle, -⟩ := hall j (by
      have := (List.getElem?_eq_some_iff.mp hr).1; omega)
    exact hle
  have hlenR : rs.length = p.recs.length := (checkBlockRecK_recNames h).2.1
  intro v hv
  rw [blockRuleIhsRunAV, blockRuleIhsAV, blockRecIhsAt, List.mem_map] at hv
  obtain ⟨key, hkey, rfl⟩ := hv
  obtain ⟨q, c'⟩ := key
  have hkey' : (q, c') ∈ ConLeche.blockIhKeys (p.toBlockShape.rulePrefixAt j)
      ((List.range p.recs.length).map p.toBlockShape.rulePrefixAt) p.recTgts
      (blockRuleKsOf p j i) := hkey
  obtain ⟨hqF, -⟩ := mem_blockIhKeys_kind hkey'
  obtain ⟨hc', -, -⟩ := mem_blockIhKeys_rP hkey'
  have hc'K : c' < rs.length := by
    rw [ConLeche.BlockShape.recTgts, List.length_map, List.length_range] at hc'
    omega
  obtain ⟨eT, eE⟩ := blockRuleTlEis_eq_record hr hcA hcore hcj hdnP hks ψ hkey
  have hq : q < cA.2 := by omega
  simp only [hct, eT, eE, hfrR, hfrP, hfrF]
  rw [hdnP] at hcd
  have hTB : DomsBelow (p.nP + q) ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD q []) :=
    hcd.tssBelow ψ q
  have hEB := hcd.eissBelow ψ q
  refine mkLamsC_below ?_ ?_
  · -- the moved telescope
    have hq2 := ihTeleAtGo_below (nF := cA.2) (o := p.toBlockShape.rulePrefixAt j - p.nP) (i := q)
      (l := 0) (K := rs.length + p.nP + q) (k := 0)
      (tl := rebit (pwBit ψ (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large)))
        ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD q []))
      (by
        rw [Nat.add_zero]
        refine domsBelow_mono (k := p.nP + q) (by omega) ?_
        have : ∀ {k : Nat} (ds : List (Nat × Nat × AnnotTerm)) (b : Nat),
            DomsBelow k ds → DomsBelow k (rebit b ds) := by
          intro k ds b hd
          induction ds generalizing k with
          | nil => trivial
          | cons x xs ih => exact ⟨hd.1, ih hd.2⟩
        exact this _ _ hTB)
    rw [show rs.length + p.nP + q + (cA.2 - q + 0) + (p.toBlockShape.rulePrefixAt j - p.nP) + 0
      = rs.length + p.toBlockShape.rulePrefixAt j + cA.2 from by omega] at hq2
    exact hq2
  · -- the guarded call's spine
    rw [AnnotTerm.erase_mkAppN]
    refine VExprAux.bvarsBelow_mkAppN ?_ ?_
    · show _ < _
      rw [ihTeleAtR_length]
      simp only [rebit, List.length_map]
      omega
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      rcases List.mem_append.mp hy with hy | hy
      · rcases List.mem_append.mp hy with hy | hy
        · refine bvarsBelow_prefVarsAV ?_ y hy
          rw [ihTeleAtR_length]; simp only [rebit, List.length_map]; omega
        · obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hy
          have := ihIdxAtM_below (nF := cA.2) (o := p.toBlockShape.rulePrefixAt j - p.nP)
            (i := q) (l := 0)
            (m := (ConLeche.structFieldTeleOf cA.1.type p.nP cA.2 q).length) (hEB E hE)
          refine Term.bvarsBelow.mono ?_ this
          rw [ihTeleAtR_length]; simp only [rebit, List.length_map]
          omega
      · obtain rfl := List.mem_singleton.mp hy
        have hTL : ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD q []).length
            = (ConLeche.structFieldTeleOf cA.1.type p.nP cA.2 q).length := by
          rw [← eT]; simp only [blockRuleTlAV, hct, List.length_map, List.length_range]
        rw [AnnotTerm.erase_mkAppN]
        refine VExprAux.bvarsBelow_mkAppN ?_ ?_
        · show _ < _
          rw [ihTeleAtR_length]; simp only [rebit, List.length_map]
          omega
        · intro x hx
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hy
          have := List.mem_range.mp hk
          show _ < _
          rw [ihTeleAtR_length]; simp only [rebit, List.length_map]
          omega

/-- **`Rb0` reads the opened residue, and is bounded at the whole
frame**: the residue is typed there, so the reading exists
(`blockRuleOpened_run`), and a scoped, bvar-closed term reads below its
depth (`denote_bvarsBelow`). -/
theorem blockRuleRbAV_below {mpC : EnvModelM V μ envC}
    (h : checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[j]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    {d : BlockData V} {lps : List Name} {p₁ : ConLeche.BlockShape} {isRec : Bool}
    {A : Nat → (Name → Nat) → AnnotTerm} {nc : Nat}
    (hcore : BlockCtorsCore mpC.base2 d lps cvTas p₁ isRec A nc)
    (hcj : (d.ctorsM (p.toBlockShape.recTgtAt j))[i]? = some cA)
    (hdnP : d.nP = p.nP)
    (hks : d.ksF (p.toBlockShape.recTgtAt j) i
      = (blockRuleKsOf p j i).map BlockFieldKind.toRec)
    (hCf : cA.1.type.hasFvar = false) (hCb : cA.1.type.looseBVarsBounded 0 = true)
    (hcbC : ConstsBound envC cA.1.type) (ψ : Name → Nat) :
    Term.bvarsBelow (p.toBlockShape.rulePrefixAt j + cA.2 + (blockRuleFrameAt p rs j i).nR)
      (blockRuleRbAV p rs mpC.base2.acval envC ψ j i).erase := by
  have hct : blockRuleCtorOf rs j i = cA := blockRuleCtorOf_eq hr hcA
  have hcd := blockCtorData_of_core hcore hcj
  rw [hdnP] at hcd
  obtain ⟨crestC, hoP, hoF⟩ := hcd.opens
  have hop0 : ConLeche.openPisAtFvars (p.nP + cA.2) cA.1.type 0
      = some (d.fvsPF (p.toBlockShape.recTgtAt j) i ++ d.xFvsF (p.toBlockShape.recTgtAt j) i,
          d.xrestF (p.toBlockShape.recTgtAt j) i) :=
    openPisAtFvars_add p.nP hoP (by rw [Nat.zero_add]; exact hoF)
  obtain ⟨bsC, bodyC0, hstC, -, -, -⟩ := ConLeche.Verify.openPisAtFvars_stripPis _ hop0
  have hstripC : (cA.1.type.stripPis (p.nP + cA.2)).isSome = true := by rw [hstC]; rfl
  have hksLen : (blockRuleKsOf p j i).length = cA.2 := by
    have := hcd.ksLen; rw [hks, List.length_map] at this; exact this
  obtain ⟨-, -, -, -, -, -, -, hbodyO, hWS, hbO, -, -, hread⟩ :=
    blockRuleOpened_run mpC h hr hcA hrhs hCf hCb hcbC hstripC hksLen
  obtain ⟨B, hB⟩ := hread ψ
  have hRb : blockRuleRbAV p rs mpC.base2.acval envC ψ j i = B := by
    rw [blockRuleRbAV, hct, ← hbodyO, hB]; rfl
  rw [hRb]
  exact denote_bvarsBelow mpC.base2.cval_closed _ _ hWS hbO
    (denoteMeta_erase mpC.base2.acval_erase _ _ hB)

/-- **`ihdoms` is bounded at its own depths** — each `ih` opener is an
`fvar` at its depth (`openPisAtFvars_index`), scoped there by the
frame's `FvarList` and bvar-closed (`blockRuleOpened_run`), so its
reading mentions nothing past the openers before it.  With
`blockRuleRbAV_below` it is what makes the chain lift of the rule's
certificates the identity. -/
theorem blockRuleIhdomsAV_below {mpC : EnvModelM V μ envC}
    (h : checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[j]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    {d : BlockData V} {lps : List Name} {p₁ : ConLeche.BlockShape} {isRec : Bool}
    {A : Nat → (Name → Nat) → AnnotTerm} {nc : Nat}
    (hcore : BlockCtorsCore mpC.base2 d lps cvTas p₁ isRec A nc)
    (hcj : (d.ctorsM (p.toBlockShape.recTgtAt j))[i]? = some cA)
    (hdnP : d.nP = p.nP)
    (hks : d.ksF (p.toBlockShape.recTgtAt j) i
      = (blockRuleKsOf p j i).map BlockFieldKind.toRec)
    (hCf : cA.1.type.hasFvar = false) (hCb : cA.1.type.looseBVarsBounded 0 = true)
    (hcbC : ConstsBound envC cA.1.type) (ψ : Name → Nat) :
    ∀ q, q < (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i).length →
      Term.bvarsBelow (p.toBlockShape.rulePrefixAt j + cA.2 + q)
        ((blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i).getD q default).erase := by
  have hct : blockRuleCtorOf rs j i = cA := blockRuleCtorOf_eq hr hcA
  have hcd := blockCtorData_of_core hcore hcj
  rw [hdnP] at hcd
  obtain ⟨crestC, hoP, hoF⟩ := hcd.opens
  have hop0 : ConLeche.openPisAtFvars (p.nP + cA.2) cA.1.type 0
      = some (d.fvsPF (p.toBlockShape.recTgtAt j) i ++ d.xFvsF (p.toBlockShape.recTgtAt j) i,
          d.xrestF (p.toBlockShape.recTgtAt j) i) :=
    openPisAtFvars_add p.nP hoP (by rw [Nat.zero_add]; exact hoF)
  obtain ⟨bsC, bodyC0, hstC, -, -, -⟩ := ConLeche.Verify.openPisAtFvars_stripPis _ hop0
  have hstripC : (cA.1.type.stripPis (p.nP + cA.2)).isSome = true := by rw [hstC]; rfl
  have hksLen : (blockRuleKsOf p j i).length = cA.2 := by
    have := hcd.ksLen; rw [hks, List.length_map] at this; exact this
  obtain ⟨-, -, hL3, hlbF, -, -, -, -, -, -, -, -, -⟩ :=
    blockRuleOpened_run mpC h hr hcA hrhs hCf hCb hcbC hstripC hksLen
  obtain ⟨-, -, -, -, -, -, hopen, -, -, -⟩ := blockRuleResidueData_runP h hr hcA hrhs
  have hpos := ConLeche.checkBlockRecK_rulePos h j r hr i cA hcA
  rw [blockRuleIhdomsAV, hct, readOpenedDoms_length_eq]
  refine readOpenedDoms_below (m := mpC.base2) (ψ := ψ) _ _ hpos fun q x hx => ?_
  obtain ⟨ty, rfl⟩ := ConLeche.openPisAtFvars_index _ _ _ hopen q x hx
  have hmem : Expr.fvar (p.toBlockShape.rulePrefixAt j + cA.2 + q) ty
      ∈ blockRuleFvsIhAt p rs j i := List.mem_of_getElem? hx
  have hw := hL3.2.2 _ (List.mem_append_left _ (List.mem_reverse.mpr hmem))
  simp only [Expr.WScoped] at hw
  exact ⟨hw.2, hlbF _ (List.mem_append_right _ hmem)⟩

/-- **Bit validity from a grading** — the `AnnotValid` twin of
`fieldsOkB_zero_of_spineGrading`: a binder list each of whose entries is
valid under every spine fitting the entries before it is hereditarily
valid. -/
theorem fieldsValid_of_grading :
    ∀ (L : List AnnotTerm) {σ : Nat → V},
      (∀ l, l < L.length → ∀ ys : List V,
        SpineFit σ (L.take l) ys → AnnotValid V (consList ys σ) (L.getD l default)) →
      FieldsValid σ L
  | [], _, _ => trivial
  | F :: Fs, σ, hok => by
    refine ⟨?_, fun a ha => ?_⟩
    · simpa using hok 0 (by simp) [] trivial
    · refine fieldsValid_of_grading Fs (fun l hl ys hys => ?_)
      have hstep : SpineFit σ ((F :: Fs).take (l + 1)) (a :: ys) := ⟨ha, hys⟩
      have hq := hok (l + 1) (by simp only [List.length_cons]; omega) (a :: ys) hstep
      simpa using hq

/-- **A typed term reads graded at its context** — `checkSoundAt`'s
inference half (`inferReads_of` for the type's reading), the residue
half of `residueMem_of_certs` without the conclusion. -/
theorem wellDenotedV_of_infer {envT : Env} (hμ : μ.verifiedChecks = true)
    (mp : EnvModelM V μ envT) {ψ : Name → Nat} {F d : Nat}
    {res ty : Expr} {Δa : List AnnotTerm} {Rb : AnnotTerm}
    (hinf : ConLeche.inferTypeCore μ envT F d res = .ok ty)
    (hwsR : Expr.WScoped d res) (hbR : res.looseBVarsBounded 0 = true)
    (hLR : Expr.LeavesBounded res)
    (hctxR : CtxOk mp.base2 ψ d Δa res)
    (hRb : denoteMeta mp.base2.acval envT ψ d res = some Rb) :
    ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ Rb := by
  obtain ⟨-, -, -, ihi⟩ := checkSoundAt (V := V) hμ (Rules.RulesInputs.ofSem mp ψ) F
  obtain ⟨ta, hta⟩ :=
    inferReads_of hμ (Rules.RulesInputs.ofSem mp ψ) hinf hwsR hbR hLR hctxR hRb
  exact (ihi hinf hwsR hbR hLR hctxR hRb hta).1

/-- **`Rb0` is graded at the rule's whole frame** — the opened residue
is TYPED there (the stage's own `inferTypeCore` run), its openers read
to the frame's context (`blockRuleFrameReads_run`) and the context is
graded (`hokA`, the certificate lane's `blockRuleHokA_of_run`
conclusion), so `checkSoundAt` grades its reading at every valuation
satisfying the frame. -/
theorem blockRuleRbAV_wdV_run (hμ : μ.verifiedChecks = true) {mpC : EnvModelM V μ envC}
    (h : checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[j]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    {d : BlockData V} {lps : List Name} {p₁ : ConLeche.BlockShape} {isRec : Bool}
    {A : Nat → (Name → Nat) → AnnotTerm} {nc : Nat}
    (hcore : BlockCtorsCore mpC.base2 d lps cvTas p₁ isRec A nc)
    (hcj : (d.ctorsM (p.toBlockShape.recTgtAt j))[i]? = some cA)
    (hdnP : d.nP = p.nP)
    (hks : d.ksF (p.toBlockShape.recTgtAt j) i
      = (blockRuleKsOf p j i).map BlockFieldKind.toRec)
    (hCf : cA.1.type.hasFvar = false) (hCb : cA.1.type.looseBVarsBounded 0 = true)
    (hcbC : ConstsBound envC cA.1.type) (ψ : Name → Nat)
    (hokA : ∀ l, l < p.toBlockShape.rulePrefixAt j + cA.2 + (blockRuleFrameAt p rs j i).nR →
      ∀ (σ' : Nat → V) (ys : List V),
        SpineFit σ' ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j
            ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ j i
            ++ blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i).take l) ys →
        WellDenotedV V (consList ys σ')
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j
            ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ j i
            ++ blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i).getD l default)) :
    ∀ σ' : Nat → V,
      Sat V ((blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i).reverse
        ++ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j
          ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ j i).reverse) σ' →
      WellDenotedV V σ' (blockRuleRbAV p rs mpC.base2.acval envC ψ j i) := by
  have hct : blockRuleCtorOf rs j i = cA := blockRuleCtorOf_eq hr hcA
  obtain ⟨rbs, ty, concl, -, -, -, hopen, hinf, -, -⟩ := blockRuleResidueData_runP h hr hcA hrhs
  obtain ⟨o₁, cpref, rbs', body', ldoms, lrest, h₁, hinstC, h₂, -⟩ :=
    blockRuleData_run h hr hcA hrhs
  have hcd := blockCtorData_of_core hcore hcj
  rw [hdnP] at hcd
  obtain ⟨crestC, hoP, hoF⟩ := hcd.opens
  have hop0 : ConLeche.openPisAtFvars (p.nP + cA.2) cA.1.type 0
      = some (d.fvsPF (p.toBlockShape.recTgtAt j) i ++ d.xFvsF (p.toBlockShape.recTgtAt j) i,
          d.xrestF (p.toBlockShape.recTgtAt j) i) :=
    openPisAtFvars_add p.nP hoP (by rw [Nat.zero_add]; exact hoF)
  obtain ⟨bsC, bodyC0, hstC, -, -, -⟩ := ConLeche.Verify.openPisAtFvars_stripPis _ hop0
  have hstripC : (cA.1.type.stripPis (p.nP + cA.2)).isSome = true := by rw [hstC]; rfl
  have hksLen : (blockRuleKsOf p j i).length = cA.2 := by
    have := hcd.ksLen; rw [hks, List.length_map] at this; exact this
  obtain ⟨-, -, -, hlbF, -, -, -, hbodyO, hWS, hbO, hleafO, hw₃, hreadAll⟩ :=
    blockRuleOpened_run mpC h hr hcA hrhs hCf hCb hcbC hstripC hksLen
  obtain ⟨B, hB⟩ := hreadAll ψ
  have hRb : blockRuleRbAV p rs mpC.base2.acval envC ψ j i = B := by
    rw [blockRuleRbAV, hct, ← hbodyO, hB]; rfl
  have hlenP := blockRulePdomsAV_length hμ mpC h hr ψ
  have hlenF : (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ j i).length = cA.2 := by
    rw [blockRuleFdomsAV, readOpenedDoms_length_eq, openPisAtFvars_length _ h₂]
  have hlenI : (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i).length
      = (blockRuleFrameAt p rs j i).nR := by
    rw [blockRuleIhdomsAV, readOpenedDoms_length_eq]
    exact openPisAtFvars_length _ hopen
  have hw₁ : Expr.WScoped 0 r.1.type := (checkBlockRecK_tyClosed h hr).1
  have hw₂ := blockRuleHw2_of h₁ hw₁ hCf hinstC
  have hdoms := blockRuleFrameReads_run hμ h hr hcA hrhs hcore hcj
    (by rw [hdnP]) hks hCf hCb hcbC ψ
  have hctx := ctxOk_blockFrame (m := mpC.base2) (φ := ψ) h₁ h₂ hopen hw₁ hw₂ hw₃
    (sat_blockFrame_length hlenP hlenF hlenI) hdoms
    (blockRuleHokΔ_of hlenP hlenF hlenI hokA) hleafO
  rw [hRb]
  exact wellDenotedV_of_infer hμ mpC hinf hWS hbO (leavesBounded_of_openers hlbF hleafO) hctx hB

/-- The `AnnotValid` twin of `interp_ihIdxAtM_rule`: one index expression
across the rule's frame and the field's frame. -/
theorem annotValid_ihIdxAtM_rule {ρ : Nat → V} {nF o i m : Nat} {xs fs bs as : List V}
    (hxl : xs.length = as.length + o) (htake : xs.take as.length = as)
    (hfl : fs.length = nF) (hbl : bs.length = m) (E : AnnotTerm) :
    AnnotValid V (consList bs (consList (xs ++ fs) ρ)) (ihIdxAtM nF o i 0 m E)
      ↔ AnnotValid V (consList bs (consList (fs.take i) (consList as ρ))) E := by
  have hdrop : (xs.drop as.length).length = o := by
    rw [List.length_drop, hxl]; omega
  have hfd : (fs.drop i).length = nF - i := by rw [List.length_drop, hfl]
  have e1 : shiftE o (nF + m) (consList bs (consList (xs ++ fs) ρ))
      = consList (fs ++ bs) (consList as ρ) := by
    rw [consList_ruleFrame,
      show nF + m = (fs ++ bs).length from by rw [List.length_append, hfl, hbl],
      shiftE_consList_len, shiftE_drop_consList xs as.length hdrop ρ, htake]
  have e2 : shiftE (nF - i) m (consList (fs ++ bs) (consList as ρ))
      = consList bs (consList (fs.take i) (consList as ρ)) := by
    rw [consList_append, ← hbl, shiftE_consList_len,
      shiftE_drop_consList fs i hfd (consList as ρ)]
  unfold ihIdxAtM
  simp only [Nat.add_zero]
  rw [AnnotValid_liftN, e1, AnnotValid_liftN, e2]

/-- **A field's telescope's validity, moved to the rule's frame** — the
validity twin of `spineFit_ihTeleAtGo_rule`. -/
theorem fieldsValid_ihTeleAtGo_rule {ρ : Nat → V} {nF o i : Nat} {xs fs as : List V}
    (hxl : xs.length = as.length + o) (htake : xs.take as.length = as)
    (hfl : fs.length = nF) :
    ∀ (tl : List (Nat × Nat × AnnotTerm)) (ws : List V),
      FieldsValid (consList ws (consList (fs.take i) (consList as ρ))) (tl.map (·.2.2)) →
      FieldsValid (consList ws (consList (xs ++ fs) ρ))
        ((ihTeleAtGo nF o i 0 ws.length tl).map (·.2.2))
  | [], _, _ => trivial
  | dd :: tl, ws, hF => by
    rw [List.map_cons] at hF
    obtain ⟨hv, hrest⟩ := hF
    show FieldsValid _ (ihIdxAtM nF o i 0 ws.length dd.2.2 ::
      (ihTeleAtGo nF o i 0 (ws.length + 1) tl).map (·.2.2))
    refine ⟨(annotValid_ihIdxAtM_rule hxl htake hfl rfl dd.2.2).mpr hv, fun b hb => ?_⟩
    rw [interp_ihIdxAtM_rule hxl htake hfl rfl dd.2.2] at hb
    have ih := fieldsValid_ihTeleAtGo_rule (i := i) hxl htake hfl tl (ws ++ [b])
      (by rw [← consList_snoc']; exact hrest b hb)
    rw [length_snoc', ← consList_snoc'] at ih
    exact ih

/-- **The `ih` terms are bit-valid at the rule's frame** — off the
GRADING's field segment alone: field `q`'s domain at the rule frame is
the constructors' record's entry lifted past the prefix's extra binders
(`blockRuleFdomsAV_eq`), and that entry IS the Π-tower over the field's
telescope of the target former at the parameters and the field's index
readings (`recEntry`/`reflEntry`); its validity hands the telescope's
and the index readings', which the `ih` term's λ-tower and spine carry
moved to the rule's frame (`fieldsValid_ihTeleAtGo_rule`,
`annotValid_ihIdxAtM_rule`). -/
theorem blockRuleIhsRunAV_valid_run (hμ : μ.verifiedChecks = true) {mpC : EnvModelM V μ envC}
    (h : checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[j]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    {d : BlockData V} {lps : List Name} {p₁ : ConLeche.BlockShape} {isRec : Bool}
    {A : Nat → (Name → Nat) → AnnotTerm} {nc : Nat}
    (hcore : BlockCtorsCore mpC.base2 d lps cvTas p₁ isRec A nc)
    (hcj : (d.ctorsM (p.toBlockShape.recTgtAt j))[i]? = some cA)
    (hdnP : d.nP = p.nP)
    (hks : d.ksF (p.toBlockShape.recTgtAt j) i
      = (blockRuleKsOf p j i).map BlockFieldKind.toRec)
    (hCf : cA.1.type.hasFvar = false) (ψ : Name → Nat)
    (hokA : ∀ l, l < p.toBlockShape.rulePrefixAt j + cA.2 + (blockRuleFrameAt p rs j i).nR →
      ∀ (σ' : Nat → V) (ys : List V),
        SpineFit σ' ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j
            ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ j i
            ++ blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i).take l) ys →
        WellDenotedV V (consList ys σ')
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j
            ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ j i
            ++ blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i).getD l default)) :
    ∀ (σ : Nat → V) (ys : List V),
      SpineFit σ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j
        ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ j i) ys →
      ∀ v ∈ blockRuleIhsRunAV p rs mpC.base2.acval envC ψ j i,
        AnnotValid V (consList ys σ) v := by
  intro σ ys hys v hv
  have hct : blockRuleCtorOf rs j i = cA := blockRuleCtorOf_eq hr hcA
  obtain ⟨hfrP, hfrR, hfrF, -, -, -, -, -⟩ := blockRuleFrameAt_rows (pp := p) hct
  have hcd := blockCtorData_of_core hcore hcj
  rw [hdnP] at hcd
  obtain ⟨o₁, cpref, rbs', body', ldoms, lrest, -, -, h₂, -⟩ := blockRuleData_run h hr hcA hrhs
  have hnPr : p.nP ≤ p.toBlockShape.rulePrefixAt j := by
    obtain ⟨-, hlenR, hall⟩ := checkBlockRecK_recNames h
    obtain ⟨-, -, -, -, -, -, hle, -⟩ := hall j (by
      have := (List.getElem?_eq_some_iff.mp hr).1; omega)
    exact hle
  have hpl := blockRulePdomsAV_length hμ mpC h hr ψ
  have hflen : (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ j i).length = cA.2 := by
    rw [blockRuleFdomsAV, readOpenedDoms_length_eq, openPisAtFvars_length _ h₂]
  have hFeq := (blockRuleFdomsAV_eq h hr hcA hrhs hcd hCf hnPr ψ).1
  obtain ⟨xs, fs, rfl, hxs, hfs⟩ := spineFit_append_inv hys
  have hxl : xs.length = p.toBlockShape.rulePrefixAt j := by rw [hxs.length_eq, hpl]
  have hfl : fs.length = cA.2 := by rw [hfs.length_eq, hflen]
  have hasl : (xs.take p.nP).length = p.nP := by rw [List.length_take]; omega
  have hxl' : xs.length = (xs.take p.nP).length + (p.toBlockShape.rulePrefixAt j - p.nP) := by
    rw [hasl]; omega
  have htake : xs.take (xs.take p.nP).length = xs.take p.nP := by rw [hasl]
  -- the key
  rw [blockRuleIhsRunAV, blockRuleIhsAV, blockRecIhsAt, List.mem_map] at hv
  obtain ⟨⟨q, c'⟩, hkey, rfl⟩ := hv
  have hkey' : (q, c') ∈ ConLeche.blockIhKeys (p.toBlockShape.rulePrefixAt j)
      ((List.range p.recs.length).map p.toBlockShape.rulePrefixAt) p.recTgts
      (blockRuleKsOf p j i) := hkey
  obtain ⟨hqK, hkind⟩ := mem_blockIhKeys_kind hkey'
  have hksLen : (blockRuleKsOf p j i).length = cA.2 := by
    have := hcd.ksLen; rw [hks, List.length_map] at this; exact this
  have hq : q < cA.2 := by omega
  rw [← hks] at hkind
  obtain ⟨eT, eE⟩ := blockRuleTlEis_eq_record hr hcA hcore hcj hdnP hks ψ hkey
  have hTL : ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD q []).length
      = (ConLeche.structFieldTeleOf cA.1.type p.nP cA.2 q).length := by
    rw [← eT]; simp only [blockRuleTlAV, hct, List.length_map, List.length_range]
  -- the field's domain, as the Π-tower over its telescope
  have hD : ((d.dsF (p.toBlockShape.recTgtAt j) i ψ).getD (p.nP + q) default).2.2
      = mkPisAV ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD q [])
          (AnnotTerm.mkAppN (mpC.base2.acval (d.memberName (d.tgts (p.toBlockShape.recTgtAt j) i q)) ψ)
            (paramBvarsAt p.nP (p.nP + q + ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD q []).length)
              ++ (d.eissF (p.toBlockShape.recTgtAt j) i ψ).getD q [])) := by
    rcases hkind with hk | hk
    · have hnr : (d.ksF (p.toBlockShape.recTgtAt j) i).getD q .ordinary ≠ .reflexive := by
        rw [hk]; exact nofun
      rw [hcd.recEntry ψ q hk hq, hcd.tssNone ψ q hnr]
      rfl
    · exact hcd.reflEntry ψ q hk hq
  -- the grading at the field's position
  have hfitG : SpineFit σ ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j
      ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ j i
      ++ blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i).take
        (p.toBlockShape.rulePrefixAt j + q)) (xs ++ fs.take q) := by
    rw [List.take_append_of_le_length (by rw [List.length_append, hpl, hflen]; omega),
      ← hpl, List.take_length_add_append]
    exact SpineFit.append hxs (spineFit_take_any hfs q)
  have hgd : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j
      ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ j i
      ++ blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i).getD
        (p.toBlockShape.rulePrefixAt j + q) default
      = (((d.dsF (p.toBlockShape.recTgtAt j) i ψ).getD (p.nP + q) default).2.2).liftN
          (p.toBlockShape.rulePrefixAt j - p.nP) q := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left
      (by rw [List.length_append, hpl, hflen]; omega),
      List.getElem?_append_right (by rw [hpl]; omega), hpl, Nat.add_sub_cancel_left,
      ← List.getD_eq_getElem?_getD, hFeq,
      liftDomsK_getD _ 0 _ q (by rw [List.length_map, List.length_drop, hcd.len ψ]; omega),
      Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_drop]
    rw [List.getElem?_eq_getElem (by rw [hcd.len ψ]; omega)]
    simp only [Option.map_some, Option.getD_some, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [hcd.len ψ]; omega : p.nP + q < (d.dsF _ i ψ).length)]
  have hg := (hokA _ (by omega) σ _ hfitG).2
  rw [hgd, AnnotValid_liftN] at hg
  have hsh : shiftE (p.toBlockShape.rulePrefixAt j - p.nP) q (consList (xs ++ fs.take q) σ)
      = consList (fs.take q) (consList (xs.take p.nP) σ) := by
    have hq' : (fs.take q).length = q := by rw [List.length_take]; omega
    have e := shiftE_consList_len (p.toBlockShape.rulePrefixAt j - p.nP) (fs.take q) (consList xs σ)
    rw [hq'] at e
    rw [consList_append, e, shiftE_drop_consList xs p.nP (by rw [List.length_drop]; omega) σ]
  rw [hsh, hD] at hg
  obtain ⟨hFV, hB⟩ := AnnotValid_mkPisAV_inv hg
  -- the `ih` term
  simp only [hct, eT, eE, hfrR, hfrP, hfrF]
  refine mkLamsC_validV (underTowerValid_of_fieldsValid ?_ fun bs hbs => ?_)
  · rw [ihTeleAtR, map_dom_ihTeleAtGo_rebit]
    have := fieldsValid_ihTeleAtGo_rule (ρ := σ) (i := q) hxl' htake hfl
      ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD q []) [] (by simpa using hFV)
    simpa using this
  · have hbs' := spineFit_ihTeleAtR_rule hxl' htake hfl hbs
    have hbl : bs.length = (ConLeche.structFieldTeleOf cA.1.type p.nP cA.2 q).length := by
      rw [hbs'.length_eq, List.length_map, hTL]
    obtain ⟨-, hargs⟩ := AnnotValid.mkAppN_inv (hB bs hbs')
    refine annotValid_mkAppN trivial (fun a ha => ?_)
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · simp only [prefVarsAV, List.mem_map] at ha
        obtain ⟨k, -, rfl⟩ := ha
        trivial
      · obtain ⟨E, hE, rfl⟩ := List.mem_map.mp ha
        exact (annotValid_ihIdxAtM_rule hxl' htake hfl hbl E).mpr
          (hargs E (List.mem_append_right _ hE))
    · rw [List.mem_singleton] at ha
      subst ha
      refine annotValid_mkAppN trivial (fun a ha => ?_)
      simp only [teleVarsAV, List.mem_map] at ha
      obtain ⟨k, -, rfl⟩ := ha
      trivial

/-- **The `ih` openers' FIT, at the residue producer's telescope** —
`BlockRuleBodyInputs`' one REGIME conjunct (`IndRegimeAt`'s fourth,
`KitRegimeAt`'s `hihChain`), stated at the pinned `ihs` and `ihdoms`
and quantified over exactly the telescope `BlockRuleBodyOwed` hands
(the contract's own, with its first conjunct at the base frame and the
leaf pin): nothing wider.  `blockRuleIhFit_seam` (`BlockDeclRun.lean`)
produces it: the leaf's tuple is typed, and the chain frame is its
`consList`, so it is the typed tuple's fit at the chain frame
(`blockIhFitChain_run`). -/
def BlockRuleIhFitOwed {envC : Env} (mpC : EnvModelM V μ envC) (p : BlockParts)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (s : (Name → Nat) → Nat) (nCt : Nat → Nat)
    (es0 : (Name → Nat) → Nat → Nat → List AnnotTerm) (mk0 : (Name → Nat) → Nat → Nat → AnnotTerm)
    (ctorTy : (Name → Nat) → AnnotTerm) (φ : Name → Nat) (j i : Nat)
    (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat))
    (cA : ConstantVal × Nat) (rl : ConLeche.RecRule) : Prop :=
 ∀ us : List Level, us.length = r.1.levelParams.length →
  Level.eval (Level.substFn φ r.1.levelParams us)
    (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) ≠ 0 →
  ∀ (usj : List Level) (ρ : Nat → V) (xs ys : List AnnotTerm) (restR restC : AnnotTerm),
    xs.length = p.toBlockShape.majorIdxAt j → ys.length = p.nP + cA.2 →
    usj.length = cA.1.levelParams.length →
    Level.substFn φ cA.1.levelParams usj
      = Level.substFn φ cA.1.levelParams
          (ConLeche.recFireComparands rl r.1.levelParams us cA.1.levelParams []
            (p.toBlockShape.rulePrefixAt j)).1 →
    IotaIndexPin (V := V) ρ restC p.nP
      (p.toBlockShape.majorIdxAt j) (p.toBlockShape.rulePrefixAt j) xs →
    TeleFitPA V ρ
      (blockRecTyAV mpC.base2.acval envC rs (Level.substFn φ r.1.levelParams us) j)
      (xs ++ [AnnotTerm.mkAppN
        (mpC.base2.acval cA.1.name (Level.substFn φ cA.1.levelParams usj)) ys]) restR →
    TeleFitPA V ρ (ctorTy (Level.substFn φ cA.1.levelParams usj)) ys restC →
    -- the contract's FIRST conjunct at this telescope (the residue
    -- producer's `hsp`): the prefix and the fields fit the rule's
    -- domains at the BASE frame
    SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs
          (Level.substFn φ r.1.levelParams us) j
        ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC
          (Level.substFn φ r.1.levelParams us) j i)
      ((xs.take (p.toBlockShape.rulePrefixAt j)).map (interp V ρ)
        ++ (ys.drop p.nP).map (interp V ρ)) →
  ∀ a : Nat → V,
    (∀ c', c' < rs.length →
      interp V ρ (blockRecLeafAV mpC.base2.acval envC rs s
        (blockRecEqs nCt rs (fun ψ' => blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ')
          (fun ψ' => blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ') es0
          (fun ψ' => blockRuleIhsRunAV p rs mpC.base2.acval envC ψ') mk0
          (fun ψ' => blockRuleRbAV p rs mpC.base2.acval envC ψ'))
        (Level.substFn φ r.1.levelParams us) c') = a c') →
    SpineFit (consList ((xs.take (p.toBlockShape.rulePrefixAt j)).map (interp V ρ)
        ++ (ys.drop p.nP).map (interp V ρ)) (chainFrame rs.length a ρ))
      (blockRuleIhdomsAV p rs mpC.base2.acval envC (Level.substFn φ r.1.levelParams us) j i)
      ((blockRuleIhsRunAV p rs mpC.base2.acval envC (Level.substFn φ r.1.levelParams us) j i).map
        (interp V (consList ((xs.take (p.toBlockShape.rulePrefixAt j)).map (interp V ρ)
          ++ (ys.drop p.nP).map (interp V ρ)) (chainFrame rs.length a ρ))))

/-- `BlockRuleIhFitOwed` UNFOLDED, for its producer. -/
theorem blockRuleIhFitOwed_iff {envC : Env} (mpC : EnvModelM V μ envC) (p : BlockParts)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (s : (Name → Nat) → Nat) (nCt : Nat → Nat)
    (es0 : (Name → Nat) → Nat → Nat → List AnnotTerm) (mk0 : (Name → Nat) → Nat → Nat → AnnotTerm)
    (ctorTy : (Name → Nat) → AnnotTerm) (φ : Name → Nat) (j i : Nat)
    (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat))
    (cA : ConstantVal × Nat) (rl : ConLeche.RecRule) :
    BlockRuleIhFitOwed mpC p rs s nCt es0 mk0 ctorTy φ j i r cA rl ↔
 ∀ us : List Level, us.length = r.1.levelParams.length →
  Level.eval (Level.substFn φ r.1.levelParams us)
    (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) ≠ 0 →
  ∀ (usj : List Level) (ρ : Nat → V) (xs ys : List AnnotTerm) (restR restC : AnnotTerm),
    xs.length = p.toBlockShape.majorIdxAt j → ys.length = p.nP + cA.2 →
    usj.length = cA.1.levelParams.length →
    Level.substFn φ cA.1.levelParams usj
      = Level.substFn φ cA.1.levelParams
          (ConLeche.recFireComparands rl r.1.levelParams us cA.1.levelParams []
            (p.toBlockShape.rulePrefixAt j)).1 →
    IotaIndexPin (V := V) ρ restC p.nP
      (p.toBlockShape.majorIdxAt j) (p.toBlockShape.rulePrefixAt j) xs →
    TeleFitPA V ρ
      (blockRecTyAV mpC.base2.acval envC rs (Level.substFn φ r.1.levelParams us) j)
      (xs ++ [AnnotTerm.mkAppN
        (mpC.base2.acval cA.1.name (Level.substFn φ cA.1.levelParams usj)) ys]) restR →
    TeleFitPA V ρ (ctorTy (Level.substFn φ cA.1.levelParams usj)) ys restC →
    -- the contract's FIRST conjunct at this telescope (the residue
    -- producer's `hsp`): the prefix and the fields fit the rule's
    -- domains at the BASE frame
    SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs
          (Level.substFn φ r.1.levelParams us) j
        ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC
          (Level.substFn φ r.1.levelParams us) j i)
      ((xs.take (p.toBlockShape.rulePrefixAt j)).map (interp V ρ)
        ++ (ys.drop p.nP).map (interp V ρ)) →
  ∀ a : Nat → V,
    (∀ c', c' < rs.length →
      interp V ρ (blockRecLeafAV mpC.base2.acval envC rs s
        (blockRecEqs nCt rs (fun ψ' => blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ')
          (fun ψ' => blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ') es0
          (fun ψ' => blockRuleIhsRunAV p rs mpC.base2.acval envC ψ') mk0
          (fun ψ' => blockRuleRbAV p rs mpC.base2.acval envC ψ'))
        (Level.substFn φ r.1.levelParams us) c') = a c') →
    SpineFit (consList ((xs.take (p.toBlockShape.rulePrefixAt j)).map (interp V ρ)
        ++ (ys.drop p.nP).map (interp V ρ)) (chainFrame rs.length a ρ))
      (blockRuleIhdomsAV p rs mpC.base2.acval envC (Level.substFn φ r.1.levelParams us) j i)
      ((blockRuleIhsRunAV p rs mpC.base2.acval envC (Level.substFn φ r.1.levelParams us) j i).map
        (interp V (consList ((xs.take (p.toBlockShape.rulePrefixAt j)).map (interp V ρ)
          ++ (ys.drop p.nP).map (interp V ρ)) (chainFrame rs.length a ρ)))) := Iff.rfl

/-- **`BlockRuleBodyOwed` at the run** — the rule stage's peel
obligation, at the PINNED `ihs`/`Rb0` (and the lane's own prefix and
field components), from the run, the constructor's record, the frame's
grading (`hokA`, the certificate lane's `blockRuleHokA_of_run`) and the
`ih` openers' fit (`hihFit`, the regime's). -/
theorem blockRuleBodyOwed_run (hμ : μ.verifiedChecks = true) {mpC : EnvModelM V μ envC}
    (h : checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[j]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    {d : BlockData V} {lps : List Name} {p₁ : ConLeche.BlockShape} {isRec : Bool}
    {A : Nat → (Name → Nat) → AnnotTerm} {nc : Nat}
    (hcore : BlockCtorsCore mpC.base2 d lps cvTas p₁ isRec A nc)
    (hcj : (d.ctorsM (p.toBlockShape.recTgtAt j))[i]? = some cA)
    (hdnP : d.nP = p.nP)
    (hks : d.ksF (p.toBlockShape.recTgtAt j) i
      = (blockRuleKsOf p j i).map BlockFieldKind.toRec)
    (hCf : cA.1.type.hasFvar = false) (hCb : cA.1.type.looseBVarsBounded 0 = true)
    (hcbC : ConstsBound envC cA.1.type)
    {s : (Name → Nat) → Nat} {nCt : Nat → Nat}
    {es0 : (Name → Nat) → Nat → Nat → List AnnotTerm} {mk0 : (Name → Nat) → Nat → Nat → AnnotTerm}
    {ctorTy : (Name → Nat) → AnnotTerm} {φ : Name → Nat} {rl : ConLeche.RecRule}
    (hokA : ∀ ψ : Name → Nat,
      ∀ l, l < p.toBlockShape.rulePrefixAt j + cA.2 + (blockRuleFrameAt p rs j i).nR →
      ∀ (σ' : Nat → V) (ys : List V),
        SpineFit σ' ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j
            ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ j i
            ++ blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i).take l) ys →
        WellDenotedV V (consList ys σ')
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j
            ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ j i
            ++ blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i).getD l default))
    (hihFit : BlockRuleIhFitOwed (V := V) mpC p rs s nCt es0 mk0 ctorTy φ j i r cA rl) :
    BlockRuleBodyOwed (V := V) mpC F p rs s nCt
      (fun ψ' => blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ')
      (fun ψ' => blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ') es0
      (fun ψ' => blockRuleIhsRunAV p rs mpC.base2.acval envC ψ') mk0
      (fun ψ' => blockRuleRbAV p rs mpC.base2.acval envC ψ')
      ctorTy φ j i r cA rl rhs r.1.levelParams := by
  rw [blockRuleBodyOwed_iff]
  intro us hus hℓ usj ρ xs ys restR restC hxl hyl husjl hψ hidx hfitR hfitC hsp a hleaf
    fr recTys rbody resid ihTele bodyO fvsIh rbs ty concl hfr hrec _ hres hih hfvs _
  intros
  subst hfr hrec hres hih hfvs
  exact blockRuleBodyInputs_run hμ h hr hcA hrhs hcore hcj hdnP hks hCf hCb hcbC _ (hokA _)
    (hihFit us hus hℓ usj ρ xs ys restR restC hxl hyl husjl hψ hidx hfitR hfitC hsp a hleaf)

end BodyRun

end ConLeche.Model
