module

public import ConLeche.Model.Inductives.GenRecAssembly
import ConLeche.Model.Inductives.NestPosOut
import ConLeche.Model.Inductives.ClassGenRead
import ConLeche.Model.Inductives.ClassGenMinor
import ConLeche.Model.Inductives.GenRecStage
import ConLeche.Verify.Inductives.ClassGenMinorSyn
import ConLeche.Verify.Inductives.ClassGenAnnot
import ConLeche.Verify.Inductives.ClassGenScope
import ConLeche.Verify.Inductives.NestCallSyn
import ConLeche.Verify.Abstract
import ConLeche.Model.StreamConsts
import ConLeche.Verify.InferLemmas

public section

/-!
# The stored generated rule, as syntax (lane GENREC-C)

The kernel stores the ANNOTATION of the reset generated rule
(`classRuleOk`: `annotate … 0 gen.resetMeta`), where

    gen = λ (prefix) (f⃗ : fields), minor_s f⃗ ih⃗,
    ih_l = λ a⃗, rec_t (prefix vars) e⃗ (f_i a⃗)

(`classGenRule`).  What the rule's reading needs of the stored term,
read off the generator's syntax and the annotation pass alone
(`genRule_shape`): opened at its `rP + nF` λs it is the minor's variable
applied to the fields' variables and one term per recursive field, each
of which opens its telescope to the call of the callee's recursor
constant at the prefix variables and further arguments.  Everything
holds up to the annotations of free variables (`Expr.ErasedEq`), which
no reading consults.

The λ-twins of the Π lemmas the type side uses
(`annotateCore_closeTelescope_gen`, `open_of_erasedEq_closeTelescope`)
are proved here.
-/

namespace ConLeche.Model
open ConLeche.Term ConLeche.Verify
open ConLeche (Env Expr Name Level ConstantVal BinderMeta ClassGen ClassCtor CheckMode
  closeLams)

variable {mode : CheckMode}

/-! ## `closeLams`, bounded and reset -/

theorem closeLams_bounded :
    ∀ (nds : List (Expr × BinderMeta)) (hi : Nat) (cur : Expr),
      (∀ nd ∈ nds, nd.1.looseBVarsBounded 0 = true) → cur.looseBVarsBounded 0 = true →
      (closeLams nds hi cur).looseBVarsBounded 0 = true
  | [], _, _, _, hc => hc
  | (nd, bm) :: rest, hi, cur, hn, hc => by
    simp only [closeLams, Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨hn _ List.mem_cons_self, ConLeche.looseBVarsBounded_abstract1 _ 0
      (closeLams_bounded rest (hi + 1) cur (fun x hx => hn x (List.mem_cons_of_mem _ hx)) hc)⟩

theorem resetMeta_closeLams :
    ∀ (nds : List (Expr × BinderMeta)) (i : Nat) (B : Expr),
      (closeLams nds i B).resetMeta
        = closeLams (nds.map fun q => (q.1.resetMeta, (⟨.never⟩ : BinderMeta))) i B.resetMeta
  | [], _, _ => rfl
  | (dom, bm) :: nds, i, B => by
    simp only [closeLams, List.map_cons, Expr.resetMeta, ConLeche.resetMeta_abstract1,
      resetMeta_closeLams nds (i + 1) B]

/-! ## Opening a term erasure-equal to a closed λ-telescope -/

/-- **Opening a term erasure-equal to a closed λ-telescope**: it opens
its λs, its body is the telescope's body and its binders the closed
pieces, up to erasure (the binder data equal). -/
theorem open_of_erasedEq_closeLams :
    ∀ (nds : List (Expr × BinderMeta)) (d : Nat) (body e : Expr),
      (∀ p ∈ nds, p.1.looseBVarsBounded 0 = true) → body.looseBVarsBounded 0 = true →
      Expr.ErasedEq e (closeLams nds d body) →
      ∃ bs rest, openLamsM nds.length e d = some (bs, rest) ∧ Expr.ErasedEq rest body ∧
        ∀ (i : Nat) (b nd : Expr × BinderMeta), bs[i]? = some b → nds[i]? = some nd →
          Expr.ErasedEq b.1 nd.1 ∧ b.2 = nd.2
  | [], d, body, e, _, _, he => by
    refine ⟨[], e, by simp [openLamsM], by simpa [closeLams] using he,
      fun i b nd hb _ => nomatch hb⟩
  | (dom, bm) :: nds, d, body, e, hcl, hb, he => by
    cases e with
    | lam a b bm' =>
      simp only [closeLams] at he
      obtain ⟨hm, ha, hbE⟩ := he
      have hcl' : ∀ p ∈ nds, p.1.looseBVarsBounded 0 = true :=
        fun p hp => hcl p (List.mem_cons_of_mem _ hp)
      have hC := closeLams_bounded nds (d + 1) body hcl' hb
      have hE : Expr.ErasedEq (b.instantiate1 (.fvar d a)) (closeLams nds (d + 1) body) :=
        Expr.ErasedEq.trans (Expr.ErasedEq.instantiate1 hbE (v' := .fvar d dom) rfl)
          (erasedEq_abstract1_instantiate1 _ 0 hC)
      obtain ⟨bs, rest, hop, hrest, hdoms⟩ :=
        open_of_erasedEq_closeLams nds (d + 1) body _ hcl' hb hE
      refine ⟨(a, bm') :: bs, rest, ?_, hrest, fun i b' nd hb' hnd => ?_⟩
      · simp only [List.length_cons, openLamsM, hop, Option.map_some]
      · cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hb' hnd
          subst hb' hnd
          exact ⟨ha, hm⟩
        | succ i =>
          simp only [List.getElem?_cons_succ] at hb' hnd
          exact hdoms i b' nd hb' hnd
    | _ => simp [closeLams, Expr.ErasedEq] at he

/-! ## Annotating a closed λ-telescope -/

/-- **Annotating (an erasure of) a closed λ-telescope**, over ANY body
(the λ-twin of `annotateCore_closeTelescope_gen`): the result is, up to
erasure, the λ-telescope of the annotated domains over the annotated
body, each annotated piece the annotation of an erasure of the raw one,
at its own depth, and scoped there. -/
theorem annotateCore_closeLams_gen {env : Env} :
    ∀ (nds : List (Expr × BinderMeta)) {F d : Nat} {B E e' : Expr},
      (∀ p ∈ nds, p.1.looseBVarsBounded 0 = true) → B.looseBVarsBounded 0 = true →
      Expr.ErasedEq E (closeLams nds d B) → Expr.WScoped d E →
      ConLeche.annotateCore mode env F d E = .ok e' →
      ∃ (nds' : List (Expr × BinderMeta)) (B' : Expr),
        nds'.length = nds.length ∧ Expr.ErasedEq e' (closeLams nds' d B') ∧
        (∃ (B₀ : Expr) (F' : Nat), Expr.ErasedEq B₀ B ∧ Expr.WScoped (d + nds.length) B₀ ∧
          ConLeche.annotateCore mode env F' (d + nds.length) B₀ = .ok B') ∧
        ∀ (k : Nat) (nd' : Expr × BinderMeta), nds'[k]? = some nd' →
          ∃ (X : Expr) (F' : Nat) (nd : Expr × BinderMeta), nds[k]? = some nd ∧
            Expr.ErasedEq X nd.1 ∧ Expr.WScoped (d + k) X ∧
            ConLeche.annotateCore mode env F' (d + k) X = .ok nd'.1
  | [], F, d, B, E, e', _, _, he, hw, h => by
    simp only [closeLams] at he
    exact ⟨[], e', rfl, by simpa [closeLams] using Expr.ErasedEq.rfl e',
      ⟨E, F, he, by simpa using hw, by simpa using h⟩, fun k nd' hk => nomatch hk⟩
  | (dom, bm) :: nds, F, d, B, E, e', hcl, hb, he, hw, h => by
    simp only [closeLams] at he
    match E, he with
    | .lam A b m, he =>
      obtain ⟨rfl, hA, hbE⟩ := he
      simp only [Expr.WScoped] at hw
      cases F with
      | zero => simp [ConLeche.annotateCore_zero, throw, throwThe, MonadExceptOf.throw] at h
      | succ F =>
        obtain ⟨A', b', pw, hA', hb', rfl⟩ := ConLeche.annotateCore_lam_inv h
        have hwA' : Expr.WScoped d A' := ConLeche.annotateCore_WScoped F A hA' hw.1
        have hcl' : ∀ p ∈ nds, p.1.looseBVarsBounded 0 = true :=
          fun p hp => hcl p (List.mem_cons_of_mem _ hp)
        have hC := closeLams_bounded nds (d + 1) B hcl' hb
        have hE : Expr.ErasedEq (b.instantiate1 (.fvar d A')) (closeLams nds (d + 1) B) :=
          Expr.ErasedEq.trans (Expr.ErasedEq.instantiate1 hbE (v' := .fvar d A') rfl)
            (Expr.erasedEq_abstract1_instantiate1 _ 0 hC)
        obtain ⟨nds', B', hl, he', ⟨B₀, F₀, hB₀, hwB₀, hannB⟩, hdoms⟩ :=
          annotateCore_closeLams_gen nds hcl' hb hE (hwA'.instantiate1 0 hw.2) hb'
        refine ⟨(A', ⟨pw⟩) :: nds', B', by simp [hl], ?_, ⟨B₀, F₀, hB₀, ?_, ?_⟩, ?_⟩
        · simp only [closeLams]
          exact ⟨rfl, Expr.ErasedEq.rfl _, Expr.ErasedEq.abstract1 0 he'⟩
        · rw [List.length_cons, show d + (nds.length + 1) = d + 1 + nds.length by omega]
          exact hwB₀
        · rw [List.length_cons, show d + (nds.length + 1) = d + 1 + nds.length by omega]
          exact hannB
        · intro k nd' hk
          cases k with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
            subst hk
            exact ⟨A, F, (dom, m), rfl, hA, by simpa using hw.1, by simpa using hA'⟩
          | succ k =>
            simp only [List.getElem?_cons_succ] at hk
            obtain ⟨X, F', nd, hnd, hX, hwX, hann⟩ := hdoms k nd' hk
            exact ⟨X, F', nd, by simpa using hnd, hX,
              by rw [show d + (k + 1) = d + 1 + k by omega]; exact hwX,
              by rw [show d + (k + 1) = d + 1 + k by omega]; exact hann⟩

/-- **Annotating an application spine, argument by argument**: the head
and every argument annotated (each at some fuel), the spine's length
kept. -/
theorem annotateCore_mkAppN_args {env : Env} :
    ∀ (as : List Expr) {F d : Nat} {f r : Expr},
      ConLeche.annotateCore mode env F d (Expr.mkAppN f as) = .ok r →
      ∃ (F' : Nat) (f' : Expr) (as' : List Expr),
        ConLeche.annotateCore mode env F' d f = .ok f' ∧ r = Expr.mkAppN f' as' ∧
        as'.length = as.length ∧
        ∀ (k : Nat) (a a' : Expr), as[k]? = some a → as'[k]? = some a' →
          ∃ F'', ConLeche.annotateCore mode env F'' d a = .ok a'
  | [], F, d, f, r, h => ⟨F, r, [], h, rfl, rfl, fun k a a' ha _ => nomatch ha⟩
  | a :: as, F, d, f, r, h => by
    obtain ⟨F₁, g, as', hg, rfl, hl, hargs⟩ := annotateCore_mkAppN_args as (f := .app f a) h
    cases F₁ with
    | zero => simp [ConLeche.annotateCore_zero, throw, throwThe, MonadExceptOf.throw] at hg
    | succ F₁ =>
      obtain ⟨f', a', hf, ha, rfl⟩ := ConLeche.annotateCore_app_inv hg
      refine ⟨F₁, f', a' :: as', hf, rfl, by simp [hl], fun k b b' hb hb' => ?_⟩
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hb hb'
        subst hb hb'
        exact ⟨F₁, ha⟩
      | succ k => exact hargs k b b' (by simpa using hb) (by simpa using hb')

/-! ## Lists: `find?` over an indexed zip, `filterMapM` against `filterMap` -/

theorem find?_congr_mem {α : Type} {p q : α → Bool} :
    ∀ (l : List α), (∀ x ∈ l, p x = q x) → l.find? p = l.find? q
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.find?_cons, h a List.mem_cons_self,
      find?_congr_mem l (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem find?_zip_range' {α : Type} [Inhabited α] (P : α → Bool) :
    ∀ (L : List α) (o : Nat),
      ((List.range' o L.length).zip L).find? (fun q => P q.2)
        = ((List.range' o L.length).find? (fun s => P (L.getD (s - o) default))).map
            (fun s => (s, L.getD (s - o) default))
  | [], o => rfl
  | a :: L, o => by
    rw [List.length_cons, List.range'_succ, List.zip_cons_cons, List.find?_cons, List.find?_cons]
    simp only [Nat.sub_self, List.getD_cons_zero]
    cases hP : P a with
    | true => simp
    | false =>
      simp only
      rw [find?_zip_range' P L (o + 1)]
      have hpred : ∀ s ∈ List.range' (o + 1) L.length,
          P (L.getD (s - (o + 1)) default) = P ((a :: L).getD (s - o) default) := by
        intro s hs
        rw [List.mem_range'_1] at hs
        rw [show s - o = (s - (o + 1)) + 1 by omega, List.getD_cons_succ]
      rw [find?_congr_mem _ hpred]
      cases hf : (List.range' (o + 1) L.length).find? (fun s => P ((a :: L).getD (s - o) default)) with
      | none => rfl
      | some s =>
        have hs := List.mem_range'_1.mp (List.mem_of_find?_eq_some hf)
        simp only [Option.map_some, true_and]
        rw [show s - o = (s - (o + 1)) + 1 by omega, List.getD_cons_succ]

theorem find?_zip_range {α : Type} [Inhabited α] (P : α → Bool) (L : List α) :
    ((List.range L.length).zip L).find? (fun q => P q.2)
      = ((List.range L.length).find? (fun s => P (L.getD s default))).map
          (fun s => (s, L.getD s default)) := by
  have := find?_zip_range' P L 0
  simp only [Nat.sub_zero] at this
  rw [List.range_eq_range']
  exact this

/-- **`filterMapM` against the matching `filterMap`**: where the
`filterMap`'s selector keeps an element, the monadic map kept a value;
where it drops one, the map dropped one. -/
theorem filterMapM_sel {α β γ : Type} (f : α → Option (Option β)) (sel : α → Option γ)
    (hsel : ∀ a ob, f a = some ob → ob.isSome = (sel a).isSome) :
    ∀ (L : List α) (out : List β), L.filterMapM f = some out →
      out.length = (L.filterMap sel).length ∧
      ∀ (l : Nat) (c : γ), (L.filterMap sel)[l]? = some c →
        ∃ a ∈ L, sel a = some c ∧ ∃ v, out[l]? = some v ∧ f a = some (some v)
  | [], out, h => by
    simp only [List.filterMapM_nil, pure, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun l c hc => by simp at hc⟩
  | a :: L, out, h => by
    rw [List.filterMapM_cons] at h
    simp only [bind, Option.bind] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some ob =>
      simp only [ha] at h
      have hs := hsel a ob ha
      cases ob with
      | none =>
        have hn : sel a = none := by
          cases hsa : sel a with
          | none => rfl
          | some _ => rw [hsa] at hs; exact nomatch hs
        obtain ⟨hl, hall⟩ := filterMapM_sel f sel hsel L out h
        rw [List.filterMap_cons_none hn]
        exact ⟨hl, fun l c hc => by
          obtain ⟨a', ha', h1, h2⟩ := hall l c hc
          exact ⟨a', List.mem_cons_of_mem _ ha', h1, h2⟩⟩
      | some b =>
        obtain ⟨c0, hc0⟩ : ∃ c0, sel a = some c0 := by
          cases hsa : sel a with
          | none => rw [hsa] at hs; exact nomatch hs
          | some c0 => exact ⟨c0, rfl⟩
        simp only at h
        cases hL : L.filterMapM f with
        | none => simp [hL] at h
        | some ys =>
          simp only [hL, pure, Option.some.injEq] at h
          subst h
          obtain ⟨hl, hall⟩ := filterMapM_sel f sel hsel L ys hL
          rw [List.filterMap_cons_some hc0]
          refine ⟨by simp [hl], fun l c hc => ?_⟩
          cases l with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
            subst hc
            exact ⟨a, List.mem_cons_self, hc0, b, rfl, ha⟩
          | succ l =>
            obtain ⟨a', ha', h1, v, hv, h2⟩ := hall l c (by simpa using hc)
            exact ⟨a', List.mem_cons_of_mem _ ha', h1, v, by simpa using hv, h2⟩

/-! ## The generated rule, spelled out -/

/-- The generated rule's prefix variables. -/
@[expose] def genPvars (g : ClassGen) : List Expr :=
  (List.range g.pre.length).map fun i =>
    if i < g.nP then g.params.getD i default else g.slotVar (i - g.nP)

/-- The minor premise's slot of class `c`'s constructor `C`, as the
generator searches it. -/
@[expose] def genSlotOf (g : ClassGen) (c : Nat) (C : Name) : Option Nat :=
  (List.range g.slots.length).find? fun s => match g.slots.getD s default with
    | .minor c' C' _ => c' == c && C' == C
    | _ => false

/-- **The generated rule, spelled out** (`classGenRule`): the λ-telescope
of the prefix and the declared fields over the minor's variable applied
to the fields and, per recursive field `(i, t, tele)` of `x.recs`, the
`ih` λ `λ a⃗, rec_t p⃗ e⃗ (f_i a⃗)`. -/
theorem classGenRule_spec {g : ClassGen} {recOf : Nat → Option Name} {rlvls : List Level}
    {c : Nat} {x : ClassCtor} {gen : Expr}
    (h : ConLeche.classGenRule g recOf rlvls c x = some gen) :
    ∃ (s : Nat) (fvs : List Expr) (res : Expr) (ws ihs : List Expr),
      genSlotOf g c x.cv.name = some s ∧ s < g.slots.length ∧
      ConLeche.openPisAtFvars x.nF x.tyD g.pre.length = some (fvs, res) ∧
      ConLeche.targetPiDomsWith fvs x.tyN = some ws ∧
      gen = closeLams (g.pre ++ fvs.map ConLeche.classBinder) 0
        (Expr.mkAppN (g.slotVar s) (fvs ++ ihs)) ∧
      ihs.length = x.recs.length ∧
      ∀ (l : Nat) (q : Nat × Nat × Nat), x.recs[l]? = some q →
        ∃ (xs idx : List Expr) (r : Name) (ih : Expr), ihs[l]? = some ih ∧
          g.ihParts q.2.1 q.2.2 (ws.getD q.1 default) (g.pre.length + x.nF) = some (xs, idx) ∧
          recOf q.2.1 = some r ∧
          ih = closeLams (xs.map ConLeche.classBinder) (g.pre.length + x.nF)
            (Expr.mkAppN (.const r rlvls) (genPvars g ++ idx ++
              [Expr.mkAppN (fvs.getD q.1 default) xs])) := by
  unfold ConLeche.classGenRule at h
  obtain ⟨⟨s, sl⟩, hs, h⟩ := Option.bind_eq_some_iff.mp h
  let P : ConLeche.ClassSlot → Bool := fun sl => match sl with
    | .minor c' C _ => c' == c && C == x.cv.name | _ => false
  have hs' : ((List.range g.slots.length).zip g.slots).find? (fun q => P q.2) = some (s, sl) := by
    rw [← hs]; exact find?_congr_mem _ (fun q _ => by cases q; rfl)
  rw [find?_zip_range P] at hs'
  obtain ⟨s', hs'', hss⟩ := Option.map_eq_some_iff.mp hs'
  obtain ⟨rfl, -⟩ := Prod.mk.inj hss
  have hsl : s' < g.slots.length := List.mem_range.mp (List.mem_of_find?_eq_some hs'')
  obtain ⟨⟨fvs, res⟩, hop, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ws, hws, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ihs, hihs, h⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.pure_def, Option.some.injEq] at h
  subst h
  obtain ⟨hlen, hall⟩ := filterMapM_sel _ (fun i => match x.kinds.getD i .ordinary with
      | .recursive t tele => some (i, t, tele)
      | .ordinary => none) (by
        intro a ob ha
        simp only at ha ⊢
        split at ha
        · next hk => simp only [hk, Option.some.injEq] at ha ⊢; subst ha; rfl
        · next t tele hk =>
          simp only [hk]
          obtain ⟨⟨xs, idx⟩, -, ha⟩ := Option.bind_eq_some_iff.mp ha
          obtain ⟨r, -, ha⟩ := Option.bind_eq_some_iff.mp ha
          simp only [Option.pure_def, Option.some.injEq] at ha
          subst ha; rfl) _ ihs hihs
  refine ⟨s', fvs, res, ws, ihs, ?_, hsl, hop, hws, rfl, by rw [hlen]; rfl, ?_⟩
  · unfold genSlotOf
    rw [← hs'']
    rfl
  · intro l q hq
    obtain ⟨i, -, hsel, v, hv, hfi⟩ := hall l q hq
    simp only at hsel hfi
    split at hsel
    · next t tele hk =>
      simp only [Option.some.injEq] at hsel
      subst hsel
      simp only [hk] at hfi
      obtain ⟨⟨xs, idx⟩, hparts, hfi⟩ := Option.bind_eq_some_iff.mp hfi
      obtain ⟨r, hr, hfi⟩ := Option.bind_eq_some_iff.mp hfi
      simp only [Option.pure_def, Option.some.injEq] at hfi
      exact ⟨xs, idx, r, v, hv, hparts, hr, hfi.symm⟩
    · exact nomatch hsel

/-! ## Erasure-equal to a variable or a constant -/

theorem erasedEq_fvar_inv {e : Expr} {i : Nat} {T : Expr} (h : Expr.ErasedEq e (.fvar i T)) :
    ∃ T', e = .fvar i T' := by
  cases e <;> simp_all [Expr.ErasedEq]

theorem erasedEq_const_inv {e : Expr} {n : Name} {us : List Level}
    (h : Expr.ErasedEq e (.const n us)) : e = .const n us := by
  cases e <;> simp_all [Expr.ErasedEq]

/-- The annotation of a term erasure-equal to a variable is a variable
at the same index. -/
theorem annotate_erasedEq_fvar {env : Env} {F d i : Nat} {T X X' : Expr}
    (hX : Expr.ErasedEq X (.fvar i T)) (h : ConLeche.annotateCore mode env F d X = .ok X') :
    ∃ T', X' = .fvar i T' := by
  obtain ⟨T₀, rfl⟩ := erasedEq_fvar_inv hX
  exact ⟨T₀, ConLeche.annotateCore_plain F (e := .fvar i T₀) trivial h⟩

/-! ## The generated `ih`s are scoped -/

open ConLeche (ScB ClassGenScoped) in
theorem genPvars_scoped {g : ClassGen} (hg : ClassGenScoped g) :
    ∀ (k : Nat) (a : Expr), (genPvars g)[k]? = some a → ∃ T, a = .fvar k T ∧ ScB k T := by
  intro k a hk
  unfold genPvars at hk
  rw [List.getElem?_map] at hk
  cases hr : (List.range g.pre.length)[k]? with
  | none => rw [hr] at hk; exact nomatch hk
  | some k' =>
    rw [hr] at hk
    obtain ⟨hk', rfl⟩ := List.getElem?_eq_some_iff.mp hr
    simp only [List.getElem_range, Option.map_some, Option.some.injEq] at hk
    subst hk
    split
    · next hiP =>
      have hiP' : k < g.params.length := by rw [hg.params_len]; exact hiP
      obtain ⟨ty, hxe, hty⟩ := hg.params k _ (List.getElem?_eq_getElem hiP')
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiP', Option.getD_some, hxe]
      exact ⟨ty, rfl, hty⟩
    · next hiP =>
      refine ⟨.sort .zero, ?_, ScB.sort _ _⟩
      simp only [ClassGen.slotVar]
      congr 1; omega

theorem genPvars_length (g : ClassGen) : (genPvars g).length = g.pre.length := by
  simp [genPvars]

end ConLeche.Model
