module

public import ConLeche.Kernel.Inductives.Positivity
public import ConLeche.Verify.Shift
import ConLeche.Verify.Leaves
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.InferLeaves

public section

/-!
# The positivity walk's scoping

What both the cached simulation (`Verify/Cached/NestPosC.lean`) and the
model's consumer (`Model/Inductives/BlockPosRun.lean`) need of the terms
the walk reads: the member holes are variables above the parameters,
and a member constructor's abstracted type, instantiated at the
canonical parameters, is well scoped at the walk's depth.
-/

namespace ConLeche

open Expr

/-! ## Scoping -/

/-- A well-scoped term whose variables lie below `d'` is well scoped
there. -/
theorem WScoped.of_fvarsBelow : ∀ {e : Expr} {d d' : Nat}, WScoped d e →
    Expr.fvarsBelow d' e → WScoped d' e := by
  intro e
  induction e with
  | fvar idx ty _ =>
    intro d d' hw hb
    simp only [WScoped] at hw ⊢
    exact ⟨hb, hw.2⟩
  | app f a ihf iha =>
    intro d d' hw hb
    simp only [WScoped, Expr.fvarsBelow] at hw hb ⊢
    exact ⟨ihf hw.1 hb.1, iha hw.2 hb.2⟩
  | lam ty b m iht ihb =>
    intro d d' hw hb
    simp only [WScoped, Expr.fvarsBelow] at hw hb ⊢
    exact ⟨iht hw.1 hb.1, ihb hw.2 hb.2⟩
  | forallE ty b m iht ihb =>
    intro d d' hw hb
    simp only [WScoped, Expr.fvarsBelow] at hw hb ⊢
    exact ⟨iht hw.1 hb.1, ihb hw.2 hb.2⟩
  | letE ty v b iht ihv ihb =>
    intro d d' hw hb
    simp only [WScoped, Expr.fvarsBelow] at hw hb ⊢
    exact ⟨iht hw.1 hb.1, ihv hw.2.1 hb.2.1, ihb hw.2.2 hb.2.2⟩
  | proj s i e ih =>
    intro d d' hw hb
    simp only [WScoped, Expr.fvarsBelow] at hw hb ⊢
    exact ih hw hb
  | bvar _ => intros; simp [WScoped]
  | sort _ => intros; simp [WScoped]
  | const _ _ => intros; simp [WScoped]
  | lit _ => intros; simp [WScoped]

/-- Replacing constants of a closed term by well-scoped terms gives a
well-scoped term. -/
theorem WScoped.replaceConsts_closed {f : Name → List Level → Option Expr} {d : Nat}
    (hf : ∀ c us e, f c us = some e → WScoped d e) :
    ∀ (e : Expr), e.hasFvar = false → WScoped d (e.replaceConsts f) := by
  intro e
  induction e with
  | fvar idx ty _ => intro h; simp [Expr.hasFvar] at h
  | const c us =>
    intro _
    simp only [Expr.replaceConsts]
    cases hc : f c us with
    | none => simp [WScoped]
    | some e => exact hf c us e hc
  | app f a ihf iha =>
    intro h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [Expr.replaceConsts, WScoped]
    exact ⟨ihf h.1, iha h.2⟩
  | lam ty b m iht ihb =>
    intro h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [Expr.replaceConsts, WScoped]
    exact ⟨iht h.1, ihb h.2⟩
  | forallE ty b m iht ihb =>
    intro h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [Expr.replaceConsts, WScoped]
    exact ⟨iht h.1, ihb h.2⟩
  | letE ty v b iht ihv ihb =>
    intro h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [Expr.replaceConsts, WScoped]
    exact ⟨iht h.1.1, ihv h.1.2, ihb h.2⟩
  | proj s i e ih =>
    intro h
    simp only [Expr.hasFvar] at h
    simp only [Expr.replaceConsts, WScoped]
    exact ih h
  | bvar _ => intro _; simp [Expr.replaceConsts, WScoped]
  | sort _ => intro _; simp [Expr.replaceConsts, WScoped]
  | lit _ => intro _; simp [Expr.replaceConsts, WScoped]

/-- Instantiating a telescope at well-scoped arguments keeps a term well
scoped. -/
theorem wscoped_instPisWith {d : Nat} :
    ∀ {as : List Expr} {e r : Expr}, (∀ a ∈ as, WScoped d a) → WScoped d e →
      ConLeche.instPisWith as e = some r → WScoped d r
  | [], e, r, _, he, h => by
    simp only [ConLeche.instPisWith, Option.some.injEq] at h
    subst h; exact he
  | a :: as, e, r, ha, he, h => by
    match e, he, h with
    | .forallE t b m, he, h =>
      have h' : ConLeche.instPisWith as (b.instantiate1 a) = some r := h
      simp only [WScoped] at he
      exact wscoped_instPisWith (fun x hx => ha x (List.mem_cons_of_mem _ hx))
        (WScoped.instantiate1_gen (ha a List.mem_cons_self) 0 he.2) h'


/-- A context whose stored constants are closed. -/
@[expose] def NestCtxOk (ctx : NestCtx) : Prop :=
  (∀ ci ∈ ctx.consts, ci.toConstantVal.type.hasFvar = false) ∧
  (∀ n ci, ctx.find? n = some ci → ci.toConstantVal.type.hasFvar = false)

/-- An `Option` `mapM`'s outputs come from its inputs. -/
theorem option_mapM_mem {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ y ∈ l', ∃ x ∈ l, f x = some y
  | [], l', h, y, hy => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; exact nomatch hy
  | a :: l, l', h, y, hy => by
    rw [List.mapM_cons] at h
    cases hfa : f a with
    | none => rw [hfa] at h; exact nomatch h
    | some b =>
      rw [hfa] at h
      cases hl : l.mapM f with
      | none => simp [hl] at h
      | some bs =>
        simp only [hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨a, List.mem_cons_self, hfa⟩
        · obtain ⟨x, hx, hfx⟩ := option_mapM_mem hl y hy
          exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩

/-- The member holes are variables, well scoped above them. -/
theorem nestHoles_ok {ctx : NestCtx} (hc : NestCtxOk ctx) {holes : List Expr}
    (h : nestHoles ctx = some holes) :
    ∀ x ∈ holes, WScoped (ctx.hiAt 0) x ∧ ∃ i ty, x = .fvar i ty := by
  intro x hx
  obtain ⟨mm, hmm, hf⟩ := option_mapM_mem h x hx
  have hmm' := List.mem_range.mp hmm
  split at hf
  · next cv caps hfind =>
    simp only [Option.some.injEq] at hf
    subst hf
    refine ⟨?_, _, _, rfl⟩
    simp only [WScoped, NestCtx.hiAt]
    exact ⟨by omega, WScoped.of_not_hasFvar (hc.2 _ _ hfind)⟩
  · exact nomatch hf

/-- A member constructor's abstracted type, instantiated at the canonical
parameters, is well scoped at the walk's depth. -/
theorem memberCrest_wscoped {ctx : NestCtx} {holes : List Expr}
    (hholes : ∀ x ∈ holes, WScoped (ctx.hiAt 0) x ∧ ∃ i ty, x = .fvar i ty)
    (hpar : ∀ x ∈ ctx.params, WScoped (ctx.hiAt 0) x) {cty crest : Expr}
    (hcl : cty.hasFvar = false)
    (h : ConLeche.instPisWith ctx.params (nestAbstract ctx holes cty) = some crest) :
    WScoped (ctx.hiAt 0) crest := by
  refine wscoped_instPisWith hpar ?_ h
  unfold nestAbstract
  refine WScoped.replaceConsts_closed (fun c us e he => ?_) _ hcl
  split at he
  · split at he
    · exact (hholes e (List.mem_of_getElem? he)).1
    · exact nomatch he
  · exact nomatch he


/-! ## The abstracted, instantiated constructor type: leaves and bounds -/

/-- The leaves of a closed term with constants replaced are the
replacements' leaves. -/
theorem fvarLeaves_replaceConsts_closed {f : Name → List Level → Option Expr} :
    ∀ (e : Expr), e.hasFvar = false → ∀ l ∈ (e.replaceConsts f).fvarLeaves,
      ∃ c us r, f c us = some r ∧ l ∈ r.fvarLeaves := by
  intro e
  induction e with
  | bvar i => intro _ l hl; simp [Expr.replaceConsts, fvarLeaves] at hl
  | fvar idx ty _ => intro h; simp [Expr.hasFvar] at h
  | sort u => intro _ l hl; simp [Expr.replaceConsts, fvarLeaves] at hl
  | lit v => intro _ l hl; simp [Expr.replaceConsts, fvarLeaves] at hl
  | const c us =>
    intro _ l hl
    simp only [Expr.replaceConsts] at hl
    cases hc : f c us with
    | none => rw [hc] at hl; simp [fvarLeaves] at hl
    | some r => rw [hc] at hl; exact ⟨c, us, r, hc, hl⟩
  | app a b iha ihb =>
    intro h l hl
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [Expr.replaceConsts, fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact iha h.1 l hl
    · exact ihb h.2 l hl
  | lam ty b m iht ihb =>
    intro h l hl
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [Expr.replaceConsts, fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact iht h.1 l hl
    · exact ihb h.2 l hl
  | forallE ty b m iht ihb =>
    intro h l hl
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [Expr.replaceConsts, fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact iht h.1 l hl
    · exact ihb h.2 l hl
  | letE ty v b iht ihv ihb =>
    intro h l hl
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [Expr.replaceConsts, fvarLeaves, List.mem_append] at hl
    rcases hl with (hl | hl) | hl
    · exact iht h.1.1 l hl
    · exact ihv h.1.2 l hl
    · exact ihb h.2 l hl
  | proj s i e ihe =>
    intro h l hl
    simp only [Expr.hasFvar] at h
    simp only [Expr.replaceConsts, fvarLeaves] at hl
    exact ihe h l hl

/-- Replacing constants by closed terms keeps the loose-bvar bound. -/
theorem looseBVarsBounded_replaceConsts {f : Name → List Level → Option Expr}
    (hf : ∀ c us r, f c us = some r → r.looseBVarsBounded 0 = true) :
    ∀ (e : Expr) (k : Nat), e.looseBVarsBounded k = true →
      (e.replaceConsts f).looseBVarsBounded k = true := by
  intro e
  induction e with
  | bvar i => intro k h; simpa [Expr.replaceConsts] using h
  | fvar idx ty _ => intro k _; simp [Expr.replaceConsts, looseBVarsBounded]
  | sort u => intro k _; simp [Expr.replaceConsts, looseBVarsBounded]
  | lit v => intro k _; simp [Expr.replaceConsts, looseBVarsBounded]
  | const c us =>
    intro k _
    simp only [Expr.replaceConsts]
    cases hc : f c us with
    | none => simp [looseBVarsBounded]
    | some r => exact looseBVarsBounded_mono (Nat.zero_le k) (hf c us r hc)
  | app a b iha ihb =>
    intro k h
    simp only [looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.replaceConsts, looseBVarsBounded, Bool.and_eq_true]
    exact ⟨iha k h.1, ihb k h.2⟩
  | lam ty b m iht ihb =>
    intro k h
    simp only [looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.replaceConsts, looseBVarsBounded, Bool.and_eq_true]
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | forallE ty b m iht ihb =>
    intro k h
    simp only [looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.replaceConsts, looseBVarsBounded, Bool.and_eq_true]
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | letE ty v b iht ihv ihb =>
    intro k h
    simp only [looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.replaceConsts, looseBVarsBounded, Bool.and_eq_true]
    exact ⟨⟨iht k h.1.1, ihv k h.1.2⟩, ihb (k + 1) h.2⟩
  | proj s i e ihe =>
    intro k h
    simp only [looseBVarsBounded] at h
    simp only [Expr.replaceConsts, looseBVarsBounded]
    exact ihe k h

/-- The leaves of a Π-telescope instantiated at arguments come from the
telescope or the arguments. -/
theorem fvarLeaves_instPisWith :
    ∀ {as : List Expr} {e r : Expr}, instPisWith as e = some r →
      ∀ l ∈ r.fvarLeaves, l ∈ e.fvarLeaves ∨ ∃ a ∈ as, l ∈ a.fvarLeaves
  | [], e, r, h, l, hl => by
    simp only [instPisWith, Option.some.injEq] at h
    subst h; exact Or.inl hl
  | a :: as, e, r, h, l, hl => by
    match e, h with
    | .forallE t b m, h =>
      have h' : instPisWith as (b.instantiate1 a) = some r := h
      rcases fvarLeaves_instPisWith h' l hl with hl' | ⟨x, hx, hl'⟩
      · rcases fvarLeaves_instantiate1 b 0 hl' with hb | ha
        · left; simp only [fvarLeaves, List.mem_append]; exact Or.inr hb
        · exact Or.inr ⟨a, List.mem_cons_self, ha⟩
      · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, hl'⟩

/-- A Π-telescope instantiated at bvar-closed arguments stays bvar-closed. -/
theorem looseBVarsBounded_instPisWith :
    ∀ {as : List Expr} {e r : Expr}, (∀ a ∈ as, a.looseBVarsBounded 0 = true) →
      e.looseBVarsBounded 0 = true → instPisWith as e = some r →
      r.looseBVarsBounded 0 = true
  | [], e, r, _, he, h => by
    simp only [instPisWith, Option.some.injEq] at h
    subst h; exact he
  | a :: as, e, r, ha, he, h => by
    match e, he, h with
    | .forallE t b m, he, h =>
      have h' : instPisWith as (b.instantiate1 a) = some r := h
      simp only [looseBVarsBounded, Bool.and_eq_true] at he
      exact looseBVarsBounded_instPisWith (fun x hx => ha x (List.mem_cons_of_mem _ hx))
        (looseBVarsBounded_instantiate1_gen (ha a List.mem_cons_self) he.2) h'

/-- An `Option` `mapM`'s output, positionally. -/
theorem option_mapM_getElem? {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' →
      ∀ (i : Nat) (x : α), l[i]? = some x → ∃ y, f x = some y ∧ l'[i]? = some y
  | [], _, _, i, x, hx => by simp at hx
  | a :: l, l', h, i, x, hx => by
    rw [List.mapM_cons] at h
    cases hfa : f a with
    | none => rw [hfa] at h; exact nomatch h
    | some b =>
      rw [hfa] at h
      cases hl : l.mapM f with
      | none => simp [hl] at h
      | some bs =>
        simp only [hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
          subst hx
          exact ⟨b, hfa, rfl⟩
        | succ i =>
          simp only [List.getElem?_cons_succ] at hx ⊢
          exact option_mapM_getElem? hl i x hx

/-- **Member `t`'s hole** is the variable `nP + t` carrying the member's
stored type. -/
theorem nestHoles_getElem? {ctx : NestCtx} {holes : List Expr} (h : nestHoles ctx = some holes)
    {t : Nat} (ht : t < ctx.names.length) :
    ∃ cv caps, ctx.find? (ctx.names.getD t .anonymous) = some (.indInfo cv caps) ∧
      holes[t]? = some (.fvar (ctx.nP + t) cv.type) := by
  obtain ⟨y, hy, hget⟩ := option_mapM_getElem? h t t (List.getElem?_range ht)
  split at hy
  · next cv caps hfind =>
    simp only [Option.some.injEq] at hy
    subst hy
    exact ⟨cv, caps, hfind, hget⟩
  · exact nomatch hy

/-- An `Option` `mapM` keeps the length. -/
theorem option_mapM_length {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → l'.length = l.length
  | [], l', h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | a :: l, l', h => by
    rw [List.mapM_cons] at h
    cases hfa : f a with
    | none => rw [hfa] at h; exact nomatch h
    | some b =>
      rw [hfa] at h
      cases hl : l.mapM f with
      | none => simp [hl] at h
      | some bs =>
        simp only [hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        simp [option_mapM_length hl]

/-- One hole per member. -/
theorem nestHoles_length {ctx : NestCtx} {holes : List Expr} (h : nestHoles ctx = some holes) :
    holes.length = ctx.names.length := by
  rw [option_mapM_length h, List.length_range]

/-- Every hole is a member's variable, carrying the member's stored type. -/
theorem nestHoles_mem {ctx : NestCtx} {holes : List Expr} (h : nestHoles ctx = some holes) :
    ∀ x ∈ holes, ∃ i cv caps, ctx.find? (ctx.names.getD i .anonymous) = some (.indInfo cv caps) ∧
      x = .fvar (ctx.nP + i) cv.type := by
  intro x hx
  obtain ⟨mm, -, hf⟩ := option_mapM_mem h x hx
  split at hf
  · next cv caps hfind =>
    simp only [Option.some.injEq] at hf
    exact ⟨mm, cv, caps, hfind, hf.symm⟩
  · exact nomatch hf

/-! ## The seeds: their keys

A seed (`nestSeedKey?`) is read off a closed recursor type in the walk's
representation: its parameters are arguments of a binder domain of the
member-abstracted type instantiated at the canonical parameters, so their
leaves are the canonical variables' and the holes', and they are well
scoped at the walk's depth. -/

/-- A binder domain of a stripped `Π`-telescope: its leaves are the
term's, and it is well scoped where the term is. -/
theorem stripPis_dom {d : Nat} :
    ∀ (n : Nat) (e : Expr) (bs : List (Expr × BinderMeta)) (r : Expr),
      e.stripPis n = some (bs, r) → ∀ b ∈ bs,
        (∀ l ∈ b.1.fvarLeaves, l ∈ e.fvarLeaves) ∧ (WScoped d e → WScoped d b.1)
  | 0, e, bs, r, h, b, hb => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact nomatch hb
  | n + 1, .forallE ty body m, bs, r, h, b, hb => by
    simp only [Expr.stripPis] at h
    obtain ⟨⟨bs', r'⟩, h', he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨fun l hl => by simp only [fvarLeaves, List.mem_append]; exact Or.inl hl,
        fun hw => by simp only [WScoped] at hw; exact hw.1⟩
    · obtain ⟨h1, h2⟩ := stripPis_dom n body bs' _ h' b hb
      exact ⟨fun l hl => by simp only [fvarLeaves, List.mem_append]; exact Or.inr (h1 l hl),
        fun hw => by simp only [WScoped] at hw; exact h2 hw.2⟩
  | _ + 1, .bvar _, _, _, h, _, _ | _ + 1, .fvar .., _, _, h, _, _
  | _ + 1, .sort _, _, _, h, _, _ | _ + 1, .const .., _, _, h, _, _
  | _ + 1, .app .., _, _, h, _, _ | _ + 1, .lam .., _, _, h, _, _
  | _ + 1, .letE .., _, _, h, _, _ | _ + 1, .proj .., _, _, h, _, _
  | _ + 1, .lit _, _, _, h, _, _ => by simp [Expr.stripPis] at h

/-- **A seed's key** (`nestSeedKey?`): no member and not `Quot`, a stored
container at its parameter count, its parameters without loose bound
variables, their leaves the canonical variables' and the holes', and well
scoped at the walk's depth where the canonical variables and the holes
are. -/
theorem nestSeedKey?_spec {ctx : NestCtx} {holes : List Expr} {nB : Nat} {ty : Expr}
    {key : NestKey} {nPc : Nat} (h : nestSeedKey? ctx holes nB ty = some (key, nPc)) :
    ctx.names.contains key.cname = false ∧ key.cname ≠ quotName ∧
      (∃ L, nestContainer ctx key.cname = some (nPc, L)) ∧ key.ds.length = nPc ∧
      (∀ x ∈ key.ds, x.bvarB = 0 ∧ ∀ l ∈ x.fvarLeaves, ∃ a ∈ ctx.params ++ holes, l ∈ a.fvarLeaves) ∧
      ((∀ x ∈ holes, WScoped (ctx.hiAt 0) x ∧ ∃ i ty, x = .fvar i ty) →
        (∀ x ∈ ctx.params, WScoped (ctx.hiAt 0) x) → ∀ x ∈ key.ds, WScoped (ctx.hiAt 0) x) := by
  unfold nestSeedKey? at h
  split at h
  · exact nomatch h
  rename_i hty
  have hcl : ty.hasFvar = false := by simpa using hty
  split at h
  · exact nomatch h
  rename_i body hbody
  split at h
  · exact nomatch h
  rename_i bs r hstrip
  split at h
  · exact nomatch h
  rename_i mdom mm hlast
  have hmem : (mdom, mm) ∈ bs := List.mem_of_getLast? hlast
  obtain ⟨hleafD, hwD⟩ := stripPis_dom (d := ctx.hiAt 0) nB body bs r hstrip _ hmem
  split at h
  · rename_i I us hfn
    split at h
    · exact nomatch h
    rename_i hnq
    split at h
    · exact nomatch h
    rename_i nPc' L hC
    dsimp only at h
    split at h
    · rename_i hok
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hok
      simp only [Bool.or_eq_true, not_or, beq_iff_eq] at hnq
      have hargs : ∀ x ∈ mdom.getAppArgs.take nPc', x ∈ mdom.getAppArgs :=
        fun x hx => List.mem_of_mem_take hx
      refine ⟨by simpa using hnq.1, hnq.2, ⟨L, hC⟩, hok.1, fun x hx => ⟨by simpa using hok.2 x hx,
        fun l hl => ?_⟩, fun hholes hpar x hx => ?_⟩
      · have hl' := hleafD l (fvarLeaves_getAppArgs (hargs x hx) l hl)
        rcases fvarLeaves_instPisWith hbody l hl' with hl'' | ⟨a, ha, hla⟩
        · obtain ⟨c, us', r', hr', hlr⟩ := fvarLeaves_replaceConsts_closed _ hcl l hl''
          refine ⟨r', List.mem_append_right _ ?_, hlr⟩
          split at hr'
          · split at hr'
            · exact List.mem_of_getElem? hr'
            · exact nomatch hr'
          · exact nomatch hr'
        · exact ⟨a, List.mem_append_left _ ha, hla⟩
      · exact Expr.WScoped.getAppArgs (hwD (memberCrest_wscoped hholes hpar hcl hbody)) x
          (hargs x hx)
    · exact nomatch h
  · exact nomatch h

/-- A telescope closed over well-scoped pieces is well scoped. -/
theorem closeTelescope_wscoped :
    ∀ (nds : List (Expr × BinderMeta)) (i : Nat) (body : Expr),
      (∀ (k : Nat) (nd : Expr × BinderMeta), nds[k]? = some nd → WScoped (i + k) nd.1) →
      WScoped (i + nds.length) body → WScoped i (closeTelescope nds i body)
  | [], i, body, _, hb => by simpa [closeTelescope] using hb
  | (dom, bm) :: bs, i, body, h, hb => by
    simp only [closeTelescope, WScoped]
    refine ⟨by simpa using h 0 _ rfl, WScoped.abstract1 0 (closeTelescope_wscoped bs (i + 1) body
      (fun k nd hk => ?_) ?_)⟩
    · have := h (k + 1) nd (by simpa using hk)
      rwa [show i + (k + 1) = i + 1 + k by omega] at this
    · rw [show i + 1 + bs.length = i + (List.length ((dom, bm) :: bs)) by simp; omega]
      exact hb

end ConLeche
