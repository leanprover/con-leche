module

public import ConLeche.Kernel.Inductives.GenRec
public import ConLeche.Verify.Shift
import ConLeche.Verify.Abstract
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.InferLeaves
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Verify.Inductives.NestCallSyn
import ConLeche.Verify.Cached.NestPosC

public section

/-!
# The generated recursors are CLOSED

The generated recursor stage (`genRecCheck`,
`Kernel/Inductives/GenRec.lean`) GENERATES the recursor family
(`classGenRecTy`, `classGenRule`), checks the generated types as
constants and the generated rules at the empty context, and INSTALLS
them.  The model reads them as closed terms: no free variable, no loose
bound variable.  The stage guards it (reject-only: `checkConstantValF`,
`classRuleOk`); it holds anyway by the generator's syntax — every variable the
generator opens it closes again (`closeTelescope`, `closeLams`), in the
order it opened them — as soon as the generator's INPUTS are scoped the
way the stage builds them (`ClassGenScoped`):

* the canonical parameters are the variables `0 ..< nP`, each typed over
  the earlier ones;
* a class's parameters mention only the block's parameters; a class's
  former type is closed; a constructor's declared type and its walked
  telescope mention only the block's parameters;
* the recursors' prefix is the stream's order with every minor premise
  AFTER the motives it names (its own class's and its inductive
  hypotheses' callees') — the pre-pass reads a minor's classes off the
  motives BEFORE it (`classReadMinor`'s `motPos`);
* the stored prefix is `ClassGen.prefixBinders`' own output.

**Why this matters beyond hygiene.**  A free variable left in a generated
term is not rejected by inference: inference at depth `0` checks a
variable only against the depth it occurs AT, so a stray `fvar k` under
`k + 1` binders is accepted and typed by its own annotation.  Closedness is what makes the generated term's reading the
reading of a closed term.
-/

namespace ConLeche

open Expr

/-! ## Scoped and bounded -/

/-- Well scoped at depth `d`, and no loose bound variable. -/
@[expose] def ScB (d : Nat) (e : Expr) : Prop :=
  WScoped d e ∧ e.looseBVarsBounded 0 = true

theorem ScB.mono {d d' : Nat} {e : Expr} (h : d ≤ d') (he : ScB d e) : ScB d' e :=
  ⟨WScoped.mono h he.1, he.2⟩

theorem ScB.closed {e : Expr} (h : ScB 0 e) : e.hasFvar = false ∧ e.looseBVarsBounded 0 = true :=
  ⟨Expr.not_hasFvar_of_fvarsBelow_zero h.1.fvarsBelow, h.2⟩

theorem ScB.sort (d : Nat) (u : Level) : ScB d (.sort u) := ⟨by simp [WScoped], rfl⟩

theorem ScB.const (d : Nat) (n : Name) (us : List Level) : ScB d (.const n us) :=
  ⟨by simp [WScoped], rfl⟩

theorem ScB.fvar {d i : Nat} {ty : Expr} (hi : i < d) (hty : ScB i ty) : ScB d (.fvar i ty) :=
  ⟨by simp only [WScoped]; exact ⟨hi, hty.1⟩, rfl⟩

theorem ScB.mkAppN {d : Nat} {f : Expr} {xs : List Expr} (hf : ScB d f)
    (hxs : ∀ x ∈ xs, ScB d x) : ScB d (Expr.mkAppN f xs) :=
  ⟨WScoped.mkAppN hf.1 fun x hx => (hxs x hx).1,
    looseBVarsBounded_mkAppN hf.2 fun x hx => (hxs x hx).2⟩

theorem ScB.getAppArgs {d : Nat} {e : Expr} (he : ScB d e) : ∀ x ∈ e.getAppArgs, ScB d x :=
  fun x hx => ⟨WScoped.getAppArgs he.1 x hx, looseBVarsBounded_getAppArgs he.2 x hx⟩

/-! ## Closing -/

/-- `closeTelescope` over scoped pieces is scoped. -/
theorem ScB.of_closeTelescope {i : Nat} {nds : List (Expr × BinderMeta)} {body : Expr}
    (hn : ∀ (k : Nat) (nd : Expr × BinderMeta), nds[k]? = some nd → ScB (i + k) nd.1)
    (hb : ScB (i + nds.length) body) : ScB i (ConLeche.closeTelescope nds i body) :=
  ⟨Cached.closeTelescope_wscoped nds i body (fun k nd h => (hn k nd h).1) hb.1,
    closeTelescope_bounded nds i body (fun nd hnd => by
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hnd
      exact (hn k _ (List.getElem?_eq_getElem hk)).2) hb.2⟩

/-- `closeLams` over scoped pieces is scoped. -/
theorem ScB.of_closeLams :
    ∀ {i : Nat} {nds : List (Expr × BinderMeta)} {body : Expr},
      (∀ (k : Nat) (nd : Expr × BinderMeta), nds[k]? = some nd → ScB (i + k) nd.1) →
      ScB (i + nds.length) body → ScB i (ConLeche.closeLams nds i body)
  | i, [], body, _, hb => by simpa [ConLeche.closeLams] using hb
  | i, (dom, bm) :: bs, body, hn, hb => by
    have hrest : ScB (i + 1) (ConLeche.closeLams bs (i + 1) body) :=
      ScB.of_closeLams (fun k nd hk => by
          have := hn (k + 1) nd (by simpa using hk)
          rwa [show i + (k + 1) = i + 1 + k by omega] at this)
        (by rw [show i + 1 + bs.length = i + ((dom, bm) :: bs).length by simp; omega]; exact hb)
    have hd := hn 0 (dom, bm) rfl
    simp only [Nat.add_zero] at hd
    refine ⟨?_, ?_⟩
    · simp only [ConLeche.closeLams, WScoped]
      exact ⟨hd.1, WScoped.abstract1 0 hrest.1⟩
    · simp only [ConLeche.closeLams, Expr.looseBVarsBounded, Bool.and_eq_true]
      exact ⟨hd.2, looseBVarsBounded_abstract1 _ 0 hrest.2⟩

/-- The domain of an opened variable, as a binder. -/
theorem ScB.classBinder {d i : Nat} {x ty : Expr} (hx : x = .fvar i ty) (hty : ScB d ty) :
    ScB d (ConLeche.classBinder x).1 := by
  subst hx; exact hty

/-! ## Opening -/

/-- An opened telescope of a scoped term: its variables are `d, d+1, …`,
each typed over the earlier ones, and its body is scoped at the
extended depth. -/
theorem ScB.openPis {n d : Nat} {e : Expr} {fvs : List Expr} {body : Expr}
    (h : openPisAtFvars n e d = some (fvs, body)) (he : ScB d e) :
    fvs.length = n ∧
      (∀ (k : Nat) (x : Expr), fvs[k]? = some x → ∃ ty, x = .fvar (d + k) ty ∧ ScB (d + k) ty) ∧
      ScB (d + n) body := by
  obtain ⟨hfw, hbw⟩ := openPisAtFvars_WScoped n e d h he.1
  obtain ⟨hbb, hfb⟩ := ConLeche.Verify.openPisAtFvars_bounded n h he.2
  refine ⟨ConLeche.Verify.openPisAtFvars_length n h, fun k x hx => ?_, ⟨hbw, hbb⟩⟩
  obtain ⟨ty, rfl⟩ := openPisAtFvars_index n e d h k x hx
  have hmem : Expr.fvar (d + k) ty ∈ fvs := List.mem_of_getElem? hx
  have hw := hfw _ hmem
  simp only [WScoped] at hw
  exact ⟨ty, rfl, hw.2, by simpa [Expr.fvarTypeD] using hfb _ hmem⟩

/-- The domain of an opened variable, as a generated binder. -/
theorem ScB.binder (g : ClassGen) {d i : Nat} {x ty : Expr} (hx : x = .fvar i ty)
    (hty : ScB d ty) : ScB d (g.binder x).1 := by
  subst hx; exact hty

/-- The binders of an opened telescope, as a `closeTelescope` list (any
binder datum: `f` keeps the variable's domain). -/
theorem ScB.openPis_binders {n d : Nat} {e : Expr} {fvs : List Expr} {body : Expr}
    {f : Expr → Expr × BinderMeta} (hf : ∀ x, (f x).1 = x.fvarTypeD)
    (h : openPisAtFvars n e d = some (fvs, body)) (he : ScB d e) :
    ∀ (k : Nat) (nd : Expr × BinderMeta), (fvs.map f)[k]? = some nd →
      ScB (d + k) nd.1 := by
  intro k nd hk
  obtain ⟨-, hfvs, -⟩ := ScB.openPis h he
  rw [List.getElem?_map] at hk
  cases hx : fvs[k]? with
  | none => rw [hx] at hk; exact nomatch hk
  | some x =>
    rw [hx] at hk
    obtain rfl := (Option.some.inj hk).symm
    obtain ⟨ty, hxe, hty⟩ := hfvs k x hx
    rw [hf]; subst hxe; exact hty

theorem ScB.of_instPisWith {d : Nat} :
    ∀ {as : List Expr} {t r : Expr}, instPisWith as t = some r → ScB d t →
      (∀ a ∈ as, ScB d a) → ScB d r
  | [], t, r, h, ht, _ => by
    simp only [instPisWith, Option.some.injEq] at h
    exact h ▸ ht
  | a :: as, t, r, h, ht, ha => by
    match t, ht, h with
    | .forallE dom body mb, ht, h =>
      have h' : instPisWith as (body.instantiate1 a) = some r := h
      have ha0 := ha a List.mem_cons_self
      obtain ⟨htw, htb⟩ := ht
      have hw : WScoped d body := by simp only [WScoped] at htw; exact htw.2
      have hb : body.looseBVarsBounded 1 = true := by
        simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at htb; exact htb.2
      exact ScB.of_instPisWith h' ⟨WScoped.instantiate1_gen ha0.1 0 hw,
          looseBVarsBounded_instantiate1_gen ha0.2 hb⟩
        (fun x hx => ha x (List.mem_cons_of_mem _ hx))

/-- The domains `targetPiDomsWith` instantiates at scoped arguments are
scoped. -/
theorem ScB.targetPiDomsWith {d : Nat} :
    ∀ {as : List Expr} {t : Expr} {ws : List Expr}, ConLeche.targetPiDomsWith as t = some ws →
      ScB d t → (∀ a ∈ as, ScB d a) → ∀ w ∈ ws, ScB d w
  | [], t, ws, h, _, _ => by
    simp only [ConLeche.targetPiDomsWith, Option.some.injEq] at h
    subst h; intro w hw; exact nomatch hw
  | a :: as, t, ws, h, ht, ha => by
    match t, ht, h with
    | .forallE dom body mb, ht, h =>
      simp only [ConLeche.targetPiDomsWith] at h
      obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
      have ha0 := ha a List.mem_cons_self
      obtain ⟨htw, htb⟩ := ht
      have hdw : WScoped d dom := by simp only [WScoped] at htw; exact htw.1
      have hw : WScoped d body := by simp only [WScoped] at htw; exact htw.2
      have hdb : dom.looseBVarsBounded 0 = true := by
        simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at htb; exact htb.1
      have hb : body.looseBVarsBounded 1 = true := by
        simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at htb; exact htb.2
      intro w hw'
      rcases List.mem_cons.mp hw' with rfl | hw'
      · exact ⟨hdw, hdb⟩
      · exact ScB.targetPiDomsWith hr ⟨WScoped.instantiate1_gen ha0.1 0 hw,
          looseBVarsBounded_instantiate1_gen ha0.2 hb⟩
          (fun x hx => ha x (List.mem_cons_of_mem _ hx)) w hw'

/-- The `i`-th domain `targetPiDomsWith` instantiates, below its length,
is scoped. -/
theorem ScB.targetPiDomsWith_getD {d : Nat} {as : List Expr} {t : Expr} {ws : List Expr}
    (h : ConLeche.targetPiDomsWith as t = some ws) (ht : ScB d t) (ha : ∀ a ∈ as, ScB d a)
    {i : Nat} (hi : i < as.length) : ScB d (ws.getD i default) := by
  have hl := targetPiDomsWith_length as t ws h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  exact ScB.targetPiDomsWith h ht ha _ (List.getElem_mem _)

/-! ## Options, over lists -/

theorem option_filterMapM_mem {α β : Type} {f : α → Option (Option β)} :
    ∀ {l : List α} {ys : List β}, l.filterMapM f = some ys →
      ∀ y ∈ ys, ∃ a ∈ l, f a = some (some y) := by
  intro l
  induction l with
  | nil =>
    intro ys h y hy
    simp only [List.filterMapM_nil, pure, Option.some.injEq] at h
    subst h; exact nomatch hy
  | cons a l ih =>
    intro ys h y hy
    rw [List.filterMapM_cons] at h
    simp only [bind, Option.bind] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some oa =>
      simp only [ha] at h
      cases oa with
      | none =>
        obtain ⟨b, hb, hb'⟩ := ih h y hy
        exact ⟨b, List.mem_cons_of_mem _ hb, hb'⟩
      | some b =>
        simp only at h
        cases hl : l.filterMapM f with
        | none => simp [hl] at h
        | some ys' =>
          simp only [hl, pure, Option.some.injEq] at h
          subst h
          rcases List.mem_cons.mp hy with rfl | hy
          · exact ⟨a, List.mem_cons_self, ha⟩
          · obtain ⟨b', hb', hb''⟩ := ih hl y hy
            exact ⟨b', List.mem_cons_of_mem _ hb', hb''⟩

/-! ## The generator's inputs, scoped -/

/-- **What the generator needs of its inputs** for its output to be
closed — every field is how the stage builds them (see the module
docstring). -/
structure ClassGenScoped (g : ClassGen) : Prop where
  /-- the canonical parameters: `fvar i`, typed over the earlier ones -/
  params_len : g.params.length = g.nP
  params : ∀ (i : Nat) (x : Expr), g.params[i]? = some x → ∃ ty, x = .fvar i ty ∧ ScB i ty
  /-- a class's parameters mention only the block's parameters -/
  ds : ∀ c, ∀ e ∈ (g.cls.getD c default).ds, ScB g.nP e
  /-- a class's former type is closed -/
  former : ∀ c, c < g.cls.length → ScB 0 (g.formerTys.getD c default)
  /-- a walked constructor's telescope mentions only the block's parameters -/
  tyN : ∀ c, ∀ x ∈ g.ctors.getD c [], ScB g.nP x.tyN
  /-- a constructor's declared type (at the class's levels and parameters)
  mentions only the block's parameters -/
  tyD : ∀ c, ∀ x ∈ g.ctors.getD c [], ScB g.nP x.tyD
  /-- a minor premise comes after the motives it names -/
  order : ∀ s c C ihs, g.slots[s]? = some (.minor c C ihs) →
    (∃ s', s' < s ∧ ClassRead.motiveSlot ⟨g.slots, []⟩ c = some s') ∧
    ∀ x ∈ g.ctors.getD c [], x.cv.name = C → ∀ t tele, ClassField.recursive t tele ∈ x.kinds →
      ∃ s', s' < s ∧ ClassRead.motiveSlot ⟨g.slots, []⟩ t = some s'
  /-- the stored prefix is the generator's own -/
  pre : g.prefixBinders = some g.pre

theorem ClassRead.motiveSlot_lt {r : ClassRead} {c s : Nat} (h : r.motiveSlot c = some s) :
    s < r.slots.length := by
  unfold ClassRead.motiveSlot at h
  have hm := List.mem_of_getElem? h
  simp only [List.mem_filter, List.mem_range] at hm
  exact hm.1

theorem ClassGen.motVar_eq {g : ClassGen} {c s : Nat}
    (h : ClassRead.motiveSlot ⟨g.slots, []⟩ c = some s) :
    g.motVar c = .fvar (g.nP + s) (.sort .zero) := by
  simp [ClassGen.motVar, ClassGen.slotVar, h]

theorem ClassGen.major_inv {g : ClassGen} {c d : Nat} {ifs : List Expr} {maj : Expr}
    (h : g.major c d = some (ifs, maj)) :
    ∃ ty body, instPisWith (g.cls.getD c default).ds (g.formerTys.getD c default) = some ty ∧
      openPisAtFvars (g.cls.getD c default).nIdx ty d = some (ifs, body) ∧
      maj = Expr.mkAppN (.const (g.cls.getD c default).ind (g.cls.getD c default).lvls)
        ((g.cls.getD c default).ds ++ ifs) := by
  unfold ClassGen.major at h
  dsimp only at h
  cases hty : instPisWith (g.cls.getD c default).ds (g.formerTys.getD c default) with
  | none => rw [hty] at h; exact nomatch h
  | some ty =>
    rw [hty] at h
    dsimp only [Option.bind_eq_bind, Option.bind_some] at h
    cases hop : openPisAtFvars (g.cls.getD c default).nIdx ty d with
    | none => rw [hop] at h; exact nomatch h
    | some p =>
      obtain ⟨ifs', body⟩ := p
      rw [hop] at h
      simp only [Option.bind_some, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨ty, body, rfl, hop, rfl⟩

/-- **A class's index telescope and major**, opened at `d ≥ nP`: the
index variables are `d, d+1, …`, and the major is scoped past them. -/
theorem ClassGen.major_scoped {g : ClassGen} (hg : ClassGenScoped g) {c d : Nat}
    {ifs : List Expr} {maj : Expr} (hd : g.nP ≤ d) (h : g.major c d = some (ifs, maj)) :
    (∀ (k : Nat) (x : Expr), ifs[k]? = some x → ∃ ty, x = .fvar (d + k) ty ∧ ScB (d + k) ty) ∧
      ScB (d + ifs.length) maj := by
  obtain ⟨ty, body, hty, hop, rfl⟩ := ClassGen.major_inv h
  have hds : ∀ e ∈ (g.cls.getD c default).ds, ScB (d + ifs.length) e :=
    fun e he => (hg.ds c e he).mono (by omega)
  by_cases hc : c < g.cls.length
  · have hty' : ScB d ty := (ScB.of_instPisWith hty ((hg.former c hc).mono (Nat.zero_le _))
      (fun e he => (hg.ds c e he).mono hd))
    obtain ⟨hl, hfvs, -⟩ := ScB.openPis hop hty'
    refine ⟨hfvs, ScB.mkAppN (ScB.const _ _ _) fun e he => ?_⟩
    rcases List.mem_append.mp he with he | he
    · exact hds e he
    · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
      obtain ⟨ty', hx, hty''⟩ := hfvs k _ (List.getElem?_eq_getElem hk)
      rw [hx]
      exact ScB.fvar (by omega) hty''
  · have hdef : g.cls.getD c default = default := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    rw [hdef] at hop hds ⊢
    have h0 : (default : TargetMajor).nIdx = 0 := rfl
    rw [h0] at hop
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    refine ⟨fun k x hx => (nomatch hx), ScB.mkAppN (ScB.const _ _ _) fun e he => ?_⟩
    simp only [List.append_nil] at he
    exact hds e he

/-- **A motive's type** at `d ≥ nP` is scoped at `d`. -/
theorem ClassGen.motiveTy_scoped {g : ClassGen} (hg : ClassGenScoped g) {c d : Nat} {T : Expr}
    (hd : g.nP ≤ d) (h : g.motiveTy c d = some T) : ScB d T := by
  unfold ClassGen.motiveTy at h
  cases hm : g.major c d with
  | none => simp [hm] at h
  | some p =>
    obtain ⟨ifs, maj⟩ := p
    simp only [hm, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      Option.some.injEq] at h
    subst h
    obtain ⟨hifs, hmaj⟩ := ClassGen.major_scoped hg hd hm
    refine ScB.of_closeTelescope (fun k nd hk => ?_) ?_
    · rw [List.getElem?_map] at hk
      cases hx : ifs[k]? with
      | none => rw [hx] at hk; exact nomatch hk
      | some x =>
        rw [hx] at hk
        obtain rfl := (Option.some.inj hk).symm
        obtain ⟨ty, hxe, hty⟩ := hifs k x hx
        exact ScB.classBinder hxe hty
    · rw [List.length_map]
      refine ⟨?_, ?_⟩
      · simp only [WScoped]; exact ⟨hmaj.1, trivial⟩
      · simp only [Expr.looseBVarsBounded, Bool.and_eq_true]; exact ⟨hmaj.2, trivial⟩

theorem getD_mem_of_lt {α : Type} {L : List α} {n : Nat} (h : n < L.length) (d : α) :
    L.getD n d ∈ L := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem _

theorem ClassField.mem_of_getD {ks : List ClassField} {i t tele : Nat}
    (h : ks.getD i .ordinary = .recursive t tele) : ClassField.recursive t tele ∈ ks := by
  rw [List.getD_eq_getElem?_getD] at h
  cases hk : ks[i]? with
  | none => rw [hk] at h; exact nomatch h
  | some k =>
    rw [hk] at h
    simp only [Option.getD_some] at h
    subst h
    exact List.mem_of_getElem? hk

/-- The recursive fields' list `minorTy` walks: each entry is a field
below `nF` whose kind is recursive at its class. -/
theorem ClassGen.recs_mem {x : ClassCtor} {i t tele : Nat}
    (h : (i, t, tele) ∈ (List.range x.nF).filterMap fun i =>
      match x.kinds.getD i .ordinary with
      | .recursive t tele => some (i, t, tele)
      | .ordinary => none) :
    i < x.nF ∧ x.kinds.getD i .ordinary = .recursive t tele := by
  obtain ⟨i', hi', hg⟩ := List.mem_filterMap.mp h
  rw [List.mem_range] at hi'
  split at hg
  · next t' tele' hk =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hg
    obtain ⟨rfl, rfl, rfl⟩ := hg
    exact ⟨hi', hk⟩
  · exact nomatch hg

/-- **An inductive hypothesis's parts**: the telescope of a recursive
field's walked type `w` opened at `e`, and its index arguments. -/
theorem ClassGen.ihParts_scoped {g : ClassGen} {t tele d e : Nat} {w : Expr}
    {xs idx : List Expr} (hw : ScB d w) (hde : d ≤ e)
    (h : g.ihParts t tele w e = some (xs, idx)) :
    xs.length = tele ∧
      (∀ (k : Nat) (x : Expr), xs[k]? = some x → ∃ ty, x = .fvar (e + k) ty ∧ ScB (e + k) ty) ∧
      ∀ a ∈ idx, ScB (e + tele) a := by
  unfold ClassGen.ihParts at h
  obtain ⟨⟨xs', leaf⟩, hop, h⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hl, hxs, hleaf⟩ := ScB.openPis hop (hw.mono hde)
  exact ⟨hl, hxs, fun a ha => ScB.getAppArgs hleaf a (List.mem_of_mem_drop ha)⟩

/-- **A minor premise's type**, at its slot `s` (depth `nP + s`), is
scoped there: its fields, its inductive hypotheses and its conclusion
name only the parameters, the motives before it, and its own binders. -/
theorem ClassGen.minorTy_scoped {g : ClassGen} (hg : ClassGenScoped g) {s c : Nat} {C : Name}
    {ihs0 : List (Nat × Nat)} (hs : g.slots[s]? = some (.minor c C ihs0))
    {x : ClassCtor} (hx : x ∈ g.ctors.getD c []) (hxC : x.cv.name = C) {T : Expr}
    (h : g.minorTy c x (g.nP + s) = some T) : ScB (g.nP + s) T := by
  obtain ⟨⟨sc, hsc, hmc⟩, hmt⟩ := hg.order s c C ihs0 hs
  have htyD : ScB (g.nP + s) x.tyD := (hg.tyD c x hx).mono (by omega)
  unfold ClassGen.minorTy at h
  obtain ⟨⟨fvs, res⟩, hop, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hfl, hfvs, hres⟩ := ScB.openPis hop htyD
  obtain ⟨ws, hws, h⟩ := Option.bind_eq_some_iff.mp h
  have hwsB : ∀ i, i < x.nF → ScB (g.nP + s + x.nF) (ws.getD i default) := by
    intro i hi
    refine ScB.targetPiDomsWith_getD hws ((hg.tyN c x hx).mono (by omega)) (fun a ha => ?_)
      (by omega)
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
    obtain ⟨ty, hxe, hty⟩ := hfvs k _ (List.getElem?_eq_getElem hk)
    rw [hxe]
    exact ScB.fvar (by omega) hty
  obtain ⟨ihs, hihs, h⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.pure_def, Option.some.injEq] at h
  subst h
  have hihl := option_mapM_length hihs
  simp only [List.length_range] at hihl
  -- the fields
  have hfv : ∀ i, i < x.nF → ∃ ty, fvs.getD i default = .fvar (g.nP + s + i) ty ∧
      ScB (g.nP + s + i) ty := by
    intro i hi
    have hi' : i < fvs.length := by omega
    obtain ⟨ty, hxe, hty⟩ := hfvs i _ (List.getElem?_eq_getElem hi')
    refine ⟨ty, ?_, hty⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
    exact hxe
  -- the inductive hypotheses
  have hih : ∀ (l : Nat) (b : Expr × BinderMeta), ihs[l]? = some b →
      ScB (g.nP + s + x.nF + l) b.1 := by
    intro l b hb
    have hl : l < ihs.length := (List.getElem?_eq_some_iff.mp hb).1
    obtain ⟨y, hy, hyb⟩ := option_mapM_getElem? hihs l l (List.getElem?_range (by omega))
    rw [hb] at hyb
    obtain rfl := Option.some.inj hyb.symm
    simp only at hy
    have hlt := hihl ▸ hl
    generalize hrl : ((List.range x.nF).filterMap fun i =>
        match x.kinds.getD i .ordinary with
        | .recursive t tele => some (i, t, tele)
        | .ordinary => none).getD l default = rl at hy
    obtain ⟨i, t, tele⟩ := rl
    have hmem : (i, t, tele) ∈ (List.range x.nF).filterMap fun i =>
        match x.kinds.getD i .ordinary with
        | .recursive t tele => some (i, t, tele)
        | .ordinary => none := by
      rw [← hrl]
      exact getD_mem_of_lt hlt _
    obtain ⟨hi, hk⟩ := ClassGen.recs_mem hmem
    obtain ⟨st, hst, hmt'⟩ := hmt x hx hxC t tele (ClassField.mem_of_getD hk)
    obtain ⟨ty, hfe, hty⟩ := hfv i hi
    obtain ⟨⟨xs, idx⟩, hparts, hy⟩ := Option.bind_eq_some_iff.mp hy
    simp only [Option.pure_def, Option.some.injEq] at hy
    subst hy
    obtain ⟨hxl, hxs, hidx⟩ := ClassGen.ihParts_scoped (hwsB i hi) (by omega) hparts
    refine ScB.of_closeTelescope (fun k nd hk => ?_) ?_
    · rw [List.getElem?_map] at hk
      cases hxk : xs[k]? with
      | none => rw [hxk] at hk; exact nomatch hk
      | some xk =>
        rw [hxk] at hk
        obtain rfl := (Option.some.inj hk).symm
        obtain ⟨ty', hxe, hty'⟩ := hxs k xk hxk
        exact ScB.binder g hxe hty'
    · rw [List.length_map, hxl, ClassGen.motVar_eq hmt']
      refine ScB.mkAppN (ScB.fvar (by omega) (ScB.sort _ _)) fun a ha => ?_
      rcases List.mem_append.mp ha with ha | ha
      · exact hidx a ha
      · simp only [List.mem_singleton] at ha
        subst ha
        have hf' : ScB (g.nP + s + x.nF + l + tele) (.fvar (g.nP + s + i) ty) :=
          ScB.fvar (by omega) hty
        rw [hfe]
        refine ScB.mkAppN hf' fun b hb => ?_
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
        obtain ⟨ty', hxe, hty'⟩ := hxs k _ (List.getElem?_eq_getElem hk)
        rw [hxe]
        exact ScB.fvar (by omega) hty'
  refine ScB.of_closeTelescope (fun k nd hk => ?_) ?_
  · rcases Nat.lt_or_ge k fvs.length with hkl | hkl
    · rw [List.getElem?_append_left (by simpa using hkl)] at hk
      exact ScB.openPis_binders (fun _ => rfl) hop htyD k nd hk
    · rw [List.getElem?_append_right (by simpa using hkl)] at hk
      have := hih (k - (fvs.map g.binder).length) nd hk
      simp only [List.length_map] at this
      rwa [show g.nP + s + x.nF + (k - fvs.length) = g.nP + s + k by omega] at this
  · rw [ClassGen.motVar_eq hmc]
    simp only [List.length_append, List.length_map]
    refine ScB.mkAppN (ScB.fvar (by omega) (ScB.sort _ _)) fun a ha => ?_
    rcases List.mem_append.mp ha with ha | ha
    · exact (ScB.getAppArgs hres a (List.mem_of_mem_drop ha)).mono (by omega)
    · simp only [List.mem_singleton] at ha
      subst ha
      refine ScB.mkAppN (ScB.const _ _ _) fun b hb => ?_
      rcases List.mem_append.mp hb with hb | hb
      · exact (hg.ds c b hb).mono (by omega)
      · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
        obtain ⟨ty', hxe, hty'⟩ := hfvs k _ (List.getElem?_eq_getElem hk)
        rw [hxe]
        exact ScB.fvar (by omega) hty'

/-- **The prefix binders** (parameters, then every slot) are scoped at
their positions. -/
theorem ClassGen.prefixBinders_scoped {g : ClassGen} (hg : ClassGenScoped g)
    {pre : List (Expr × BinderMeta)} (h : g.prefixBinders = some pre) :
    pre.length = g.nP + g.slots.length ∧
      ∀ (k : Nat) (b : Expr × BinderMeta), pre[k]? = some b → ScB k b.1 := by
  unfold ClassGen.prefixBinders at h
  obtain ⟨slotBs, hsl, h⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.pure_def, Option.some.injEq] at h
  subst h
  have hsll := option_mapM_length hsl
  simp only [List.length_range] at hsll
  refine ⟨by simp [hsll, hg.params_len], fun k b hb => ?_⟩
  rcases Nat.lt_or_ge k g.nP with hk | hk
  · rw [List.getElem?_append_left (by simpa [hg.params_len] using hk), List.getElem?_map] at hb
    cases hx : g.params[k]? with
    | none => rw [hx] at hb; exact nomatch hb
    | some x =>
      rw [hx] at hb
      obtain rfl := (Option.some.inj hb).symm
      obtain ⟨ty, hxe, hty⟩ := hg.params k x hx
      exact ScB.binder g hxe hty
  · rw [List.getElem?_append_right (by simpa [hg.params_len] using hk)] at hb
    simp only [List.length_map, hg.params_len] at hb
    have hsl' : k - g.nP < g.slots.length := by
      have := (List.getElem?_eq_some_iff.mp hb).1
      omega
    obtain ⟨y, hy, hyb⟩ := option_mapM_getElem? hsl (k - g.nP) (k - g.nP)
      (List.getElem?_range hsl')
    rw [hb] at hyb
    obtain rfl := Option.some.inj hyb.symm
    have hkk : g.nP + (k - g.nP) = k := by omega
    have hslot : g.slots.getD (k - g.nP) default = g.slots[k - g.nP] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hsl', Option.getD_some]
    simp only at hy
    rw [hslot] at hy
    have hsget : g.slots[k - g.nP]? = some g.slots[k - g.nP] := List.getElem?_eq_getElem hsl'
    generalize g.slots[k - g.nP] = sl at hy hsget
    cases sl with
    | motive key =>
      simp only at hy
      obtain ⟨T, hT, hy⟩ := Option.bind_eq_some_iff.mp hy
      simp only [Option.pure_def, Option.some.injEq] at hy
      subst hy
      have := ClassGen.motiveTy_scoped hg (by omega) hT
      rwa [hkk] at this
    | minor c C ihs0 =>
      simp only at hy
      obtain ⟨x, hxf, hy⟩ := Option.bind_eq_some_iff.mp hy
      obtain ⟨T, hT, hy⟩ := Option.bind_eq_some_iff.mp hy
      simp only [Option.pure_def, Option.some.injEq] at hy
      subst hy
      have hxm := List.mem_of_find?_eq_some hxf
      have hxC : x.cv.name = C := by simpa using List.find?_some hxf
      have := ClassGen.minorTy_scoped hg hsget hxm hxC hT
      rwa [hkk] at this

/-! ## The generated terms are closed -/

/-- **The generated recursor type is closed** (at a class whose motive
the prefix has). -/
theorem classGenRecTy_scoped {g : ClassGen} (hg : ClassGenScoped g) {c : Nat} {s : Nat}
    (hm : ClassRead.motiveSlot ⟨g.slots, []⟩ c = some s) {ty : Expr}
    (h : classGenRecTy g c = some ty) : ScB 0 ty := by
  obtain ⟨hpl, hpre⟩ := ClassGen.prefixBinders_scoped hg hg.pre
  have hs : s < g.slots.length := ClassRead.motiveSlot_lt hm
  unfold classGenRecTy at h
  obtain ⟨⟨ifs, maj⟩, hmaj, h⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.pure_def, Option.some.injEq] at h
  subst h
  obtain ⟨hifs, hmajS⟩ := ClassGen.major_scoped hg (by omega) hmaj
  refine ScB.of_closeTelescope (fun k nd hk => ?_) ?_
  · rcases Nat.lt_or_ge k g.pre.length with hk1 | hk1
    · rw [List.append_assoc, List.getElem?_append_left hk1] at hk
      simpa using hpre k nd hk
    · rw [List.append_assoc, List.getElem?_append_right hk1] at hk
      rcases Nat.lt_or_ge (k - g.pre.length) ifs.length with hk2 | hk2
      · rw [List.getElem?_append_left (by simpa using hk2), List.getElem?_map] at hk
        cases hx : ifs[k - g.pre.length]? with
        | none => rw [hx] at hk; exact nomatch hk
        | some x =>
          rw [hx] at hk
          obtain rfl := (Option.some.inj hk).symm
          obtain ⟨ty, hxe, hty⟩ := hifs _ x hx
          rw [show g.pre.length + (k - g.pre.length) = k by omega] at hty
          simpa using ScB.binder g hxe hty
      · rw [List.getElem?_append_right (by simpa using hk2)] at hk
        simp only [List.length_map] at hk
        have hk0 : k - g.pre.length - ifs.length = 0 := by
          have := (List.getElem?_eq_some_iff.mp hk).1
          simp at this; omega
        rw [hk0] at hk
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        simpa [show g.pre.length + ifs.length = k by omega] using hmajS
  · simp only [List.length_append, List.length_map, List.length_singleton, Nat.zero_add]
    rw [ClassGen.motVar_eq hm]
    refine ScB.mkAppN (ScB.fvar (by omega) (ScB.sort _ _)) fun a ha => ?_
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
      obtain ⟨ty, hxe, hty⟩ := hifs k _ (List.getElem?_eq_getElem hk)
      rw [hxe]
      exact ScB.fvar (by omega) hty
    · simp only [List.mem_singleton] at ha
      subst ha
      exact ScB.fvar (by omega) hmajS

/-- **The generated rule is closed.** -/
theorem classGenRule_scoped {g : ClassGen} (hg : ClassGenScoped g) {recOf : Nat → Option Name}
    {rlvls : List Level} {c : Nat} {x : ClassCtor} (hx : x ∈ g.ctors.getD c []) {rule : Expr}
    (h : classGenRule g recOf rlvls c x = some rule) : ScB 0 rule := by
  obtain ⟨hpl, hpre⟩ := ClassGen.prefixBinders_scoped hg hg.pre
  have htyD : ScB g.pre.length x.tyD := (hg.tyD c x hx).mono (by omega)
  unfold classGenRule at h
  obtain ⟨⟨s, sl⟩, hs, h⟩ := Option.bind_eq_some_iff.mp h
  have hsl : s < g.slots.length := by
    have hm := List.mem_of_find?_eq_some hs
    have := (List.of_mem_zip hm).1
    simpa using this
  obtain ⟨⟨fvs, res⟩, hop, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hfl, hfvs, -⟩ := ScB.openPis hop htyD
  obtain ⟨ws, hws, h⟩ := Option.bind_eq_some_iff.mp h
  have hwsB : ∀ i, i < x.nF → ScB (g.pre.length + x.nF) (ws.getD i default) := by
    intro i hi
    refine ScB.targetPiDomsWith_getD hws ((hg.tyN c x hx).mono (by omega)) (fun a ha => ?_)
      (by omega)
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
    obtain ⟨ty, hxe, hty⟩ := hfvs k _ (List.getElem?_eq_getElem hk)
    rw [hxe]
    exact ScB.fvar (by omega) hty
  obtain ⟨ihs, hihs, h⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.pure_def, Option.some.injEq] at h
  subst h
  -- the prefix variables
  have hpv : ∀ a ∈ (List.range g.pre.length).map (fun i => if i < g.nP then
      g.params.getD i default else g.slotVar (i - g.nP)), ScB g.pre.length a := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    rw [List.mem_range] at hi
    split
    · next hiP =>
      have hiP' : i < g.params.length := by rw [hg.params_len]; exact hiP
      obtain ⟨ty, hxe, hty⟩ := hg.params i _ (List.getElem?_eq_getElem hiP')
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiP', Option.getD_some, hxe]
      exact ScB.fvar hi hty
    · next hiP =>
      simp only [ClassGen.slotVar]
      exact ScB.fvar (by omega) (ScB.sort _ _)
  -- the fields
  have hfv : ∀ i, i < x.nF → ∃ ty, fvs.getD i default = .fvar (g.pre.length + i) ty ∧
      ScB (g.pre.length + i) ty := by
    intro i hi
    have hi' : i < fvs.length := by omega
    obtain ⟨ty, hxe, hty⟩ := hfvs i _ (List.getElem?_eq_getElem hi')
    refine ⟨ty, ?_, hty⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
    exact hxe
  -- the inductive hypotheses
  have hih : ∀ a ∈ ihs, ScB (g.pre.length + x.nF) a := by
    intro a ha
    obtain ⟨i, hi, hia⟩ := option_filterMapM_mem hihs a ha
    rw [List.mem_range] at hi
    simp only at hia
    split at hia
    · exact nomatch hia
    · next t tele hk =>
      obtain ⟨⟨xs, idx⟩, hparts, hia⟩ := Option.bind_eq_some_iff.mp hia
      obtain ⟨r, -, hia⟩ := Option.bind_eq_some_iff.mp hia
      simp only [Option.pure_def, Option.some.injEq] at hia
      subst hia
      obtain ⟨ty, hfe, hty⟩ := hfv i hi
      obtain ⟨hxl, hxs, hidx⟩ := ClassGen.ihParts_scoped (hwsB i hi) (by omega) hparts
      refine ScB.of_closeLams (fun k nd hk => ?_) ?_
      · rw [List.getElem?_map] at hk
        cases hxk : xs[k]? with
        | none => rw [hxk] at hk; exact nomatch hk
        | some xk =>
          rw [hxk] at hk
          obtain rfl := (Option.some.inj hk).symm
          obtain ⟨ty', hxe, hty'⟩ := hxs k xk hxk
          exact ScB.binder g hxe hty'
      · rw [List.length_map, hxl, hfe]
        refine ScB.mkAppN (ScB.const _ _ _) fun b hb => ?_
        rcases List.mem_append.mp hb with hb | hb
        · rcases List.mem_append.mp hb with hb | hb
          · exact (hpv b hb).mono (by omega)
          · exact hidx b hb
        · simp only [List.mem_singleton] at hb
          subst hb
          have hf' : ScB (g.pre.length + x.nF + tele) (.fvar (g.pre.length + i) ty) :=
            ScB.fvar (by omega) hty
          refine ScB.mkAppN hf' fun b hb => ?_
          obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
          obtain ⟨ty', hxe, hty'⟩ := hxs k _ (List.getElem?_eq_getElem hk)
          rw [hxe]
          exact ScB.fvar (by omega) hty'
  refine ScB.of_closeLams (fun k nd hk => ?_) ?_
  · rcases Nat.lt_or_ge k g.pre.length with hk1 | hk1
    · rw [List.getElem?_append_left hk1] at hk
      simpa using hpre k nd hk
    · rw [List.getElem?_append_right hk1] at hk
      have := ScB.openPis_binders (fun _ => rfl) hop htyD _ nd hk
      simpa [show g.pre.length + (k - g.pre.length) = k by omega] using this
  · simp only [List.length_append, List.length_map, Nat.zero_add, hfl]
    refine ScB.mkAppN (ScB.fvar (by omega) (ScB.sort _ _))
      fun a ha => ?_
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
      obtain ⟨ty, hxe, hty⟩ := hfvs k _ (List.getElem?_eq_getElem hk)
      rw [hxe]
      exact ScB.fvar (by omega) hty
    · exact hih a ha

/-- **Closedness**, in the transfer's spelling. -/
theorem classGenRecTy_closed {g : ClassGen} (hg : ClassGenScoped g) {c s : Nat}
    (hm : ClassRead.motiveSlot ⟨g.slots, []⟩ c = some s) {ty : Expr}
    (h : classGenRecTy g c = some ty) : ty.hasFvar = false ∧ ty.looseBVarsBounded 0 = true :=
  (classGenRecTy_scoped hg hm h).closed

theorem classGenRule_closed {g : ClassGen} (hg : ClassGenScoped g) {recOf : Nat → Option Name}
    {rlvls : List Level} {c : Nat} {x : ClassCtor} (hx : x ∈ g.ctors.getD c []) {rule : Expr}
    (h : classGenRule g recOf rlvls c x = some rule) :
    rule.hasFvar = false ∧ rule.looseBVarsBounded 0 = true :=
  (classGenRule_scoped hg hx h).closed

/-! ## The generator's outputs, spelled out -/

/-- **The generated recursor type**, spelled out: the telescope of the
prefix, the class's index binders and its major, over the motive's
variable applied to the index variables and the major's. -/
theorem classGenRecTy_spec {g : ClassGen} (hg : ClassGenScoped g) {c : Nat} {ty : Expr}
    (h : classGenRecTy g c = some ty) :
    ∃ ifs maj, g.major c g.pre.length = some (ifs, maj) ∧
      ifs.length = (g.cls.getD c default).nIdx ∧
      ty = closeTelescope (g.pre ++ ifs.map g.binder ++ [(maj, g.bm)]) 0
        (Expr.mkAppN (g.motVar c) (ifs ++ [.fvar (g.pre.length + ifs.length) maj])) ∧
      (∀ p ∈ g.pre ++ ifs.map g.binder ++ [(maj, g.bm)], p.1.looseBVarsBounded 0 = true) ∧
      (Expr.mkAppN (g.motVar c) (ifs ++ [.fvar (g.pre.length + ifs.length) maj])).looseBVarsBounded
        0 = true := by
  obtain ⟨hpl, hpre⟩ := ClassGen.prefixBinders_scoped hg hg.pre
  unfold classGenRecTy at h
  obtain ⟨⟨ifs, maj⟩, hmaj, h⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.pure_def, Option.some.injEq] at h
  subst h
  obtain ⟨ty0, body0, -, hop, -⟩ := ClassGen.major_inv hmaj
  obtain ⟨hifs, hmajS⟩ := ClassGen.major_scoped hg (by omega) hmaj
  refine ⟨ifs, maj, hmaj, ConLeche.Verify.openPisAtFvars_length _ hop, rfl, fun p hp => ?_, ?_⟩
  · rcases List.mem_append.mp hp with hp | hp
    · rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
        exact (hpre k _ (List.getElem?_eq_getElem hk)).2
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
        obtain ⟨ty, hxe, hty⟩ := hifs k _ (List.getElem?_eq_getElem hk)
        rw [hxe]; exact hty.2
    · simp only [List.mem_singleton] at hp
      subst hp; exact hmajS.2
  · refine looseBVarsBounded_mkAppN (by simp [ClassGen.motVar, ClassGen.slotVar,
      Expr.looseBVarsBounded]) fun a ha => ?_
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
      obtain ⟨ty, hxe, -⟩ := hifs k _ (List.getElem?_eq_getElem hk)
      rw [hxe]; rfl
    · simp only [List.mem_singleton] at ha
      subst ha; rfl

/-- The number of motive slots before slot `s`. -/
@[expose] def ClassGen.motiveCount (slots : List ClassSlot) (s : Nat) : Nat :=
  ((List.range s).filter fun s' =>
    match slots.getD s' default with | .motive _ => true | _ => false).length

/-- **The prefix binder at a motive slot** is the motive type of the
class whose motive it is (the motives before it counted). -/
theorem ClassGen.prefixBinders_motive {g : ClassGen} (hg : ClassGenScoped g) {s : Nat}
    {key : ClassKey} (hs : g.slots[s]? = some (.motive key)) :
    ∃ T, g.motiveTy (ClassGen.motiveCount g.slots s) (g.nP + s) = some T ∧
      g.pre[g.nP + s]? = some (T, g.bm) := by
  have hpre := hg.pre
  unfold ClassGen.prefixBinders at hpre
  obtain ⟨slotBs, hsl, hpre⟩ := Option.bind_eq_some_iff.mp hpre
  simp only [Option.pure_def, Option.some.injEq] at hpre
  have hslen : s < g.slots.length := (List.getElem?_eq_some_iff.mp hs).1
  obtain ⟨y, hy, hyb⟩ := option_mapM_getElem? hsl s s (List.getElem?_range hslen)
  have hslot : g.slots.getD s default = .motive key := by
    rw [List.getD_eq_getElem?_getD, hs, Option.getD_some]
  simp only at hy
  rw [hslot] at hy
  simp only at hy
  obtain ⟨T, hT, hy⟩ := Option.bind_eq_some_iff.mp hy
  simp only [Option.pure_def, Option.some.injEq] at hy
  subst hy
  refine ⟨T, by exact hT, ?_⟩
  rw [← hpre, List.getElem?_append_right (by simp [hg.params_len])]
  simpa [hg.params_len] using hyb

end ConLeche
