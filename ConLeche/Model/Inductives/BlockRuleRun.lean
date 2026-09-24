module

public import ConLeche.Verify.Inductives.RecStage
public import ConLeche.Model.Inductives.BlockRuleFit
import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Model.Inductives.BlockFieldRead
import ConLeche.Model.Inductives.BlockRecOpenerRead
import ConLeche.Model.Inductives.BlockCallCerts
import ConLeche.Verify.Rules.Bridge
import ConLeche.Verify.Inductives.BlockRecInv
import ConLeche.Model.Rules.Recompose
import ConLeche.Model.Tiers
import ConLeche.Model.Inductives.BlockRecIdxConv
import ConLeche.Model.Inductives.FixIntro

public section

/-!
# The rule stage's peel obligation at the run

`BlockRuleBodyOwed` (`BlockRuleFit.lean` §10) is what the residue
producer asks of the rule stage: at the contract's telescope and the
peel's outputs, `BlockRuleBodyInputs` at the rule's `ihs`/`Rb0`.  A
producer needs those two function variables PINNED, not returned
existentially by the peel.

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
      fr.recNames.contains n = false → (envC.find? n).isSome = true)
    {e e'' : Expr} {d : Nat} (hab : ConLeche.abstractIh fr d e = some e'')
    (hcb : ConstsBound env' e) : ConstsBound envC e'' :=
  ConLeche.abstractIh_preserves (fun _ e => ConstsBound env' e) (fun _ e => ConstsBound envC e)
    (fun _ _ _ => by split <;> simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
    (fun _ n _ hn h => by
      rw [constsBound_const] at h ⊢; exact hmono n h hn)
    (fun _ _ _ _ _ hc h => by
      have has := blockIhCall?_args_constsBound hmono hc h
      refine constsBound_mkAppN _ (by simp) (fun x hx => ?_)
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact constsBound_liftLooseBVars _ y _ (has y hy))
    (fun _ _ _ _ _ _ h i1 i2 => by
      rw [constsBound_lam] at h ⊢; exact ⟨i1 h.1, i2 h.2⟩)
    (fun _ _ _ _ _ _ h i1 i2 => by
      rw [constsBound_forallE] at h ⊢; exact ⟨i1 h.1, i2 h.2⟩)
    (fun _ _ _ _ _ _ _ h i1 i2 i3 => by
      rw [constsBound_letE] at h ⊢; exact ⟨i1 h.1, i2 h.2.1, i3 h.2.2⟩)
    (fun _ _ _ _ _ h i1 => by rw [constsBound_proj] at h ⊢; exact i1 h)
    (fun _ _ _ _ _ h i1 i2 => by
      rw [constsBound_app] at h ⊢; exact ⟨i1 h.1, i2 h.2⟩)
    hab hcb

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

open ConLeche (BlockParts BlockFieldKind)

variable {envC : Env} {p : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}

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

end BodyRun

end ConLeche.Model
