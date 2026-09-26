module

public import ConLeche.Kernel.Inductives.Positivity
public import ConLeche.Verify.Shift
import ConLeche.Verify.Leaves
import ConLeche.Verify.InferLemmas

public section

/-!
# The positivity walk's scoping (lane HOLE2)

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

/-! ## The walk's syntactic pass: its keys are well scoped -/

/-- An occurrence's parameters are arguments of the application. -/
theorem nestSynApp?_ds {ctx : NestCtx} {hi : Nat} {e : Expr} {k : NestKey} (h : nestSynApp? ctx hi e = some k) :
    ∀ x ∈ k.ds, x ∈ e.getAppArgs := by
  unfold nestSynApp? at h
  split at h
  · split at h
    · exact nomatch h
    · split at h
      · dsimp only at h
        split at h
        · cases h
          intro x hx
          exact List.mem_of_mem_take hx
        · exact nomatch h
      · exact nomatch h
  · exact nomatch h

/-- The scan's keys are well scoped where its input is (their parameters
are arguments of subterms). -/
theorem nestSynGo_wscoped {ctx : NestCtx} {hi d : Nat} :
    ∀ (e : Expr) (acc : NestSynAcc), WScoped d e →
      (∀ k ∈ acc.keys.toList, ∀ x ∈ k.ds, WScoped d x) →
      ∀ k ∈ (nestSynGo ctx hi e acc).keys.toList, ∀ x ∈ k.ds, WScoped d x := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro acc hw hacc
    rw [nestSynGo]
    split
    · exact hacc
    · dsimp only
      split
      · rename_i k hk
        intro k' hk' x hx
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hk'
        rcases hk' with hk' | rfl
        · exact hacc k' hk' x hx
        · exact Expr.WScoped.getAppArgs hw x (nestSynApp?_ds hk x hx)
      · simp only [WScoped] at hw
        split
        · split
          · exact hacc
          · exact iha _ hw.2 (ihf _ hw.1 hacc)
        · exact iha _ hw.2 (ihf _ hw.1 hacc)
  | lam t b _ iht ihb =>
    intro acc hw hacc
    rw [nestSynGo]
    split
    · exact hacc
    · simp only [WScoped] at hw
      exact ihb _ hw.2 (iht _ hw.1 hacc)
  | forallE t b _ iht ihb =>
    intro acc hw hacc
    rw [nestSynGo]
    split
    · exact hacc
    · simp only [WScoped] at hw
      exact ihb _ hw.2 (iht _ hw.1 hacc)
  | letE t v b iht ihv ihb =>
    intro acc hw hacc
    rw [nestSynGo]
    split
    · exact hacc
    · simp only [WScoped] at hw
      exact ihb _ hw.2.2 (ihv _ hw.2.1 (iht _ hw.1 hacc))
  | proj s i x ih =>
    intro acc hw hacc
    rw [nestSynGo]
    split
    · exact hacc
    · simp only [WScoped] at hw
      exact ih _ hw hacc
  | bvar _ =>
    intro acc _ hacc
    rw [nestSynGo]
    split <;> exact hacc
  | fvar _ _ _ =>
    intro acc _ hacc
    rw [nestSynGo]
    split <;> exact hacc
  | sort _ =>
    intro acc _ hacc
    rw [nestSynGo]
    split <;> exact hacc
  | const _ _ =>
    intro acc _ hacc
    rw [nestSynGo]
    split <;> exact hacc
  | lit _ =>
    intro acc _ hacc
    rw [nestSynGo]
    split <;> exact hacc

/-- **The syntactic occurrences are well scoped** where the scanned term is. -/
theorem nestSynOccs_wscoped {ctx : NestCtx} {hi d : Nat} {e : Expr} (hw : WScoped d e) :
    ∀ k ∈ nestSynOccs ctx hi e, ∀ x ∈ k.ds, WScoped d x := by
  intro k hk x hx
  rw [nestSynOccs, List.mem_eraseDups] at hk
  exact nestSynGo_wscoped e {} hw (fun _ h => by simp at h) k hk x hx

end ConLeche
