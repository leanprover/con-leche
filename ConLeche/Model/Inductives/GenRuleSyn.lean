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
        simp only [Option.map_some]
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

/-! ## The stored generated rule's shape -/

/-- An application whose head is a variable or a constant: its spine's
arguments, the head itself. -/
theorem getApp_mkAppN_atom {h : Expr} (hh : (∃ i T, h = .fvar i T) ∨ ∃ n us, h = .const n us)
    (as : List Expr) :
    (Expr.mkAppN h as).getAppFn = h ∧ (Expr.mkAppN h as).getAppArgs = as := by
  rw [ConLeche.Expr.getAppFn_mkAppN, ConLeche.Expr.getAppArgs_mkAppN]
  rcases hh with ⟨i, T, rfl⟩ | ⟨n, us, rfl⟩ <;> exact ⟨rfl, rfl⟩

/-- **An annotated spine, up to erasure**: a term erasure-equal to the
annotation of (an erasure of) an atom applied to `as` has an
erasure-equal head and, per argument, an erasure-equal annotation of an
erasure of the raw argument (scoped where the spine is). -/
theorem annot_spine {env : Env} {F d : Nat} {h : Expr}
    (hh : (∃ i T, h = .fvar i T) ∨ ∃ n us, h = .const n us) {as : List Expr} {Y Y' Z : Expr}
    (hY : Expr.ErasedEq Y (Expr.mkAppN h as)) (hwY : Expr.WScoped d Y)
    (hann : ConLeche.annotateCore mode env F d Y = .ok Y') (hZ : Expr.ErasedEq Z Y') :
    Expr.ErasedEq Z.getAppFn h ∧ Z.getAppArgs.length = as.length ∧
      ∀ (k : Nat) (a z : Expr), as[k]? = some a → Z.getAppArgs[k]? = some z →
        ∃ (X X' : Expr) (Fk : Nat), Expr.ErasedEq X a ∧ Expr.WScoped d X ∧
          ConLeche.annotateCore mode env Fk d X = .ok X' ∧ Expr.ErasedEq z X' := by
  obtain ⟨f₀, as₀, rfl, hf₀, hl₀⟩ := erasedEq_mkAppN_inv as hY
  have hf₀a : (∃ i T, f₀ = .fvar i T) ∨ ∃ n us, f₀ = .const n us := by
    rcases hh with ⟨i, T, rfl⟩ | ⟨n, us, rfl⟩
    · obtain ⟨T', rfl⟩ := erasedEq_fvar_inv hf₀; exact Or.inl ⟨i, T', rfl⟩
    · rw [erasedEq_const_inv hf₀]; exact Or.inr ⟨n, us, rfl⟩
  have hPl : Expr.Plain f₀ := by
    rcases hf₀a with ⟨i, T, rfl⟩ | ⟨n, us, rfl⟩ <;> trivial
  obtain ⟨F', f', as', hf', rfl, hl', hargs⟩ := annotateCore_mkAppN_args as₀ hann
  obtain rfl := ConLeche.annotateCore_plain F' hPl hf'
  obtain ⟨hfnY, haY⟩ := getApp_mkAppN_atom hf₀a as₀
  obtain ⟨hfnY', haY'⟩ := getApp_mkAppN_atom hf₀a as'
  obtain ⟨hfn, hlen, hpt⟩ := erasedEq_getApp Z _ hZ
  obtain ⟨-, -, hptY⟩ := erasedEq_getApp _ _ hY
  obtain ⟨hh1, hh2⟩ := getApp_mkAppN_atom hh as
  rw [hfnY'] at hfn
  rw [haY'] at hlen hpt
  rw [haY, hh2] at hptY
  refine ⟨Expr.ErasedEq.trans hfn hf₀, by rw [hlen, hl', hl₀], fun k a z ha hz => ?_⟩
  obtain ⟨a₀, ha₀⟩ : ∃ a₀, as₀[k]? = some a₀ :=
    ⟨_, List.getElem?_eq_getElem (by have := (List.getElem?_eq_some_iff.mp ha).1; omega)⟩
  obtain ⟨a', ha'⟩ : ∃ a', as'[k]? = some a' :=
    ⟨_, List.getElem?_eq_getElem (by have := (List.getElem?_eq_some_iff.mp ha).1; omega)⟩
  obtain ⟨Fk, hk⟩ := hargs k a₀ a' ha₀ ha'
  have hw := Expr.WScoped.getAppArgs hwY a₀ (by rw [haY]; exact List.mem_of_getElem? ha₀)
  exact ⟨a₀, a', Fk, hptY k a₀ a ha₀ ha, hw, hk, hpt k z a' hz ha'⟩

open ConLeche (ScB ClassGenScoped) in
/-- **The stored (annotated) generated rule, opened at its prefix and
fields**: the minor's variable applied to the fields' variables and, per
recursive field, a term opening its telescope to the call of the
callee's recursor constant at the prefix variables and further
arguments. -/
theorem genRule_shape {env : Env} {g : ClassGen} (hg : ClassGenScoped g)
    {recOf : Nat → Option Name} {rlvls : List Level} {c : Nat} {x : ClassCtor}
    (hx : x ∈ g.ctors.getD c []) {gen : Expr}
    (hgen : ConLeche.classGenRule g recOf rlvls c x = some gen) {F : Nat} {rhs : Expr}
    (hann : ConLeche.annotateCore mode env F 0 gen = .ok rhs) :
    ∃ (s : Nat) (bs : List (Expr × BinderMeta)) (body : Expr),
      genSlotOf g c x.cv.name = some s ∧ s < g.slots.length ∧
      openLamsM (g.pre.length + x.nF) rhs 0 = some (bs, body) ∧
      (∃ T, body.getAppFn = .fvar (g.nP + s) T) ∧
      body.getAppArgs.length = x.nF + x.recs.length ∧
      (∀ k, k < x.nF → ∃ T, body.getAppArgs[k]? = some (.fvar (g.pre.length + k) T)) ∧
      ∀ (l : Nat) (q : Nat × Nat × Nat), x.recs[l]? = some q →
        ∃ (r : Name) (bl : List (Expr × BinderMeta)) (call : Expr),
          recOf q.2.1 = some r ∧
          openLamsM q.2.2 (body.getAppArgs.getD (x.nF + l) default) (g.pre.length + x.nF)
            = some (bl, call) ∧
          call.getAppFn = .const r rlvls ∧ g.pre.length < call.getAppArgs.length ∧
          ∀ k, k < g.pre.length → ∃ T, call.getAppArgs[k]? = some (.fvar k T) := by
  obtain ⟨s, fvs, res, ws, ihs, hslot, hsl, hop, hws, rfl, hlen, hihs⟩ := classGenRule_spec hgen
  obtain ⟨hpl, hpre⟩ := ConLeche.ClassGen.prefixBinders_scoped hg hg.pre
  have htyD : ScB g.pre.length x.tyD := (hg.tyD c x hx).mono (by omega)
  obtain ⟨hfl, hfvs, -⟩ := ScB.openPis hop htyD
  have hfvS : ∀ k, k < x.nF → ∃ ty, fvs.getD k default = .fvar (g.pre.length + k) ty ∧
      ScB (g.pre.length + k) ty := by
    intro k hk
    obtain ⟨ty, hxe, hty⟩ := hfvs k _ (List.getElem?_eq_getElem (by omega))
    exact ⟨ty, by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
      Option.getD_some, hxe], hty⟩
  have hD : g.pre.length ≤ g.pre.length + x.nF := Nat.le_add_right _ _
  -- the `ih`s' parts, scoped
  have hihS : ∀ (l : Nat) (q : Nat × Nat × Nat), x.recs[l]? = some q →
      ∃ (xs idx : List Expr) (r : Name) (ih : Expr), ihs[l]? = some ih ∧
        recOf q.2.1 = some r ∧ xs.length = q.2.2 ∧
        (∀ (k : Nat) (y : Expr), xs[k]? = some y →
          ∃ ty, y = .fvar (g.pre.length + x.nF + k) ty ∧ ScB (g.pre.length + x.nF + k) ty) ∧
        (∀ a ∈ idx, ScB (g.pre.length + x.nF + q.2.2) a) ∧
        q.1 < x.nF ∧
        ScB (g.pre.length + x.nF + q.2.2) (Expr.mkAppN (.const r rlvls) (genPvars g ++ idx ++
              [Expr.mkAppN (fvs.getD q.1 default) xs])) ∧
        ih = closeLams (xs.map ConLeche.classBinder) (g.pre.length + x.nF)
            (Expr.mkAppN (.const r rlvls) (genPvars g ++ idx ++
              [Expr.mkAppN (fvs.getD q.1 default) xs])) := by
    intro l q hq
    obtain ⟨xs, idx, r, ih, hih, hparts, hr, rfl⟩ := hihs l q hq
    obtain ⟨i, t, tele⟩ := q
    obtain ⟨hi, -⟩ := ConLeche.ClassGen.recs_mem (List.mem_of_getElem? hq)
    have hw : ScB (g.pre.length + x.nF) (ws.getD i default) :=
      ScB.targetPiDomsWith_getD hws ((hg.tyN c x hx).mono (by omega)) (fun a ha => by
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
        obtain ⟨ty, hxe, hty⟩ := hfvs k _ (List.getElem?_eq_getElem hk)
        rw [hxe]; exact ScB.fvar (by omega) hty) (by omega)
    obtain ⟨hxl, hxs, hidx⟩ := ConLeche.ClassGen.ihParts_scoped hw (Nat.le_refl _) hparts
    refine ⟨xs, idx, r, _, hih, hr, hxl, hxs, hidx, hi, ?_, rfl⟩
    refine ScB.mkAppN (ScB.const _ _ _) fun b hb => ?_
    rcases List.mem_append.mp hb with hb | hb
    · rcases List.mem_append.mp hb with hb | hb
      · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
        obtain ⟨T, hT, hTs⟩ := genPvars_scoped hg k _ (List.getElem?_eq_getElem hk)
        rw [genPvars_length] at hk
        rw [hT]
        exact ScB.fvar (by omega) hTs
      · exact hidx b hb
    · simp only [List.mem_singleton] at hb
      subst hb
      obtain ⟨ty, hfe, hty⟩ := hfvS i hi
      rw [hfe]
      refine ScB.mkAppN (ScB.fvar (by omega) hty) fun b hb => ?_
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
      obtain ⟨ty', hxe, hty'⟩ := hxs k _ (List.getElem?_eq_getElem hk)
      rw [hxe]
      exact ScB.fvar (by omega) hty'
  have hihB : ∀ ih ∈ ihs, ScB (g.pre.length + x.nF) ih := by
    intro ih hmem
    obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hmem
    obtain ⟨q, hq⟩ : ∃ q, x.recs[l]? = some q := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨xs, idx, r, ih, hih, -, hxl, hxs, -, -, hcB, hihE⟩ := hihS l q hq
    rw [List.getElem?_eq_getElem hl] at hih
    obtain rfl := Option.some.inj hih
    rw [hihE]
    refine ScB.of_closeLams (fun k nd hk => ?_) (by rw [List.length_map, hxl]; exact hcB)
    rw [List.getElem?_map] at hk
    cases hxk : xs[k]? with
    | none => rw [hxk] at hk; exact nomatch hk
    | some xk =>
      rw [hxk] at hk
      obtain rfl := (Option.some.inj hk).symm
      obtain ⟨ty', hxe, hty'⟩ := hxs k xk hxk
      exact ScB.classBinder hxe hty'
  -- the whole rule, annotated
  have hnds : ∀ p ∈ g.pre ++ fvs.map ConLeche.classBinder, p.1.looseBVarsBounded 0 = true := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
      exact (hpre k _ (List.getElem?_eq_getElem hk)).2
    · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
      exact (ScB.openPis_binders hop htyD k _ (List.getElem?_eq_getElem hk)).2
  have hBS : ScB (g.pre.length + x.nF)
      (Expr.mkAppN (g.slotVar s) (fvs ++ ihs)) := by
    refine ScB.mkAppN (ScB.fvar (by omega) (ScB.sort _ _)) fun a ha => ?_
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
      obtain ⟨ty, hxe, hty⟩ := hfvs k _ (List.getElem?_eq_getElem hk)
      rw [hxe]; exact ScB.fvar (by omega) hty
    · exact hihB a ha
  have hgS := ConLeche.classGenRule_scoped hg hx hgen
  obtain ⟨nds', B', hl', he', ⟨B₀, F₀, hB₀, hwB₀, hannB⟩, hdoms⟩ :=
    annotateCore_closeLams_gen _ hnds hBS.2 (Expr.ErasedEq.rfl _) hgS.1 hann
  have hndsl : (g.pre ++ fvs.map ConLeche.classBinder).length = g.pre.length + x.nF := by
    simp [hfl]
  rw [hndsl, Nat.zero_add] at hwB₀ hannB
  have hnds'B : ∀ p ∈ nds', p.1.looseBVarsBounded 0 = true := by
    intro p hp
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
    obtain ⟨X, Fx, nd, hnd, hX, -, hannX⟩ := hdoms k _ (List.getElem?_eq_getElem hk)
    exact ConLeche.annotateCore_looseBVars Fx X hannX
      (looseBVarsBounded_of_erasedEq hX (hnds nd (List.mem_of_getElem? hnd)))
  have hB'b : B'.looseBVarsBounded 0 = true :=
    ConLeche.annotateCore_looseBVars F₀ B₀ hannB (looseBVarsBounded_of_erasedEq hB₀ hBS.2)
  obtain ⟨bs, R, hopR, hR, -⟩ := open_of_erasedEq_closeLams nds' 0 B' rhs hnds'B hB'b he'
  rw [hl', hndsl] at hopR
  obtain ⟨hfn, hlenR, hpt⟩ := annot_spine (h := g.slotVar s)
    (Or.inl ⟨g.nP + s, .sort .zero, rfl⟩) hB₀ hwB₀ hannB hR
  have hlenA : (fvs ++ ihs).length = x.nF + x.recs.length := by simp [hfl, hlen]
  refine ⟨s, bs, R, hslot, hsl, hopR, ?_, by rw [hlenR, hlenA], ?_, ?_⟩
  · exact erasedEq_fvar_inv (i := g.nP + s) (T := .sort .zero) hfn
  · intro k hk
    obtain ⟨z, hz⟩ : ∃ z, R.getAppArgs[k]? = some z :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlenR, hlenA]; omega)⟩
    have ha : (fvs ++ ihs)[k]? = some (fvs.getD k default) := by
      rw [List.getElem?_append_left (by omega), List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega)]; rfl
    obtain ⟨X, X', Fk, hXa, -, hk', hzX⟩ := hpt k _ z ha hz
    obtain ⟨ty, hfe, -⟩ := hfvS k hk
    rw [hfe] at hXa
    obtain ⟨T', rfl⟩ := annotate_erasedEq_fvar hXa hk'
    obtain ⟨T'', rfl⟩ := erasedEq_fvar_inv hzX
    exact ⟨T'', hz⟩
  · intro l q hq
    obtain ⟨xs, idx, r, ih, hih, hr, hxl, hxs, hidx, -, hcB, hihE⟩ := hihS l q hq
    have hl : l < x.recs.length := (List.getElem?_eq_some_iff.mp hq).1
    obtain ⟨z, hz⟩ : ∃ z, R.getAppArgs[x.nF + l]? = some z :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlenR, hlenA]; omega)⟩
    have ha : (fvs ++ ihs)[x.nF + l]? = some ih := by
      rw [List.getElem?_append_right (by omega), hfl, Nat.add_sub_cancel_left]; exact hih
    obtain ⟨X, X', Fk, hXa, hwX, hk', hzX⟩ := hpt (x.nF + l) _ z ha hz
    rw [hihE] at hXa
    have hxsB : ∀ p ∈ xs.map ConLeche.classBinder, p.1.looseBVarsBounded 0 = true := by
      intro p hp
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hp
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
      obtain ⟨ty', hxe, hty'⟩ := hxs k _ (List.getElem?_eq_getElem hk)
      exact (ScB.classBinder hxe hty').2
    obtain ⟨nds'', B'', hl'', he'', ⟨B₀', F₀', hB₀', hwB₀', hannB'⟩, hdoms'⟩ :=
      annotateCore_closeLams_gen _ hxsB hcB.2 hXa hwX hk'
    have hnds''B : ∀ p ∈ nds'', p.1.looseBVarsBounded 0 = true := by
      intro p hp
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
      obtain ⟨Y, Fy, nd, hnd, hY, -, hannY⟩ := hdoms' k _ (List.getElem?_eq_getElem hk)
      exact ConLeche.annotateCore_looseBVars Fy Y hannY
        (looseBVarsBounded_of_erasedEq hY (hxsB nd (List.mem_of_getElem? hnd)))
    have hB''b : B''.looseBVarsBounded 0 = true :=
      ConLeche.annotateCore_looseBVars F₀' B₀' hannB' (looseBVarsBounded_of_erasedEq hB₀' hcB.2)
    obtain ⟨bl, call, hop2, hcall, -⟩ := open_of_erasedEq_closeLams nds'' _ B'' z hnds''B hB''b
      (Expr.ErasedEq.trans hzX he'')
    rw [hl'', List.length_map, hxl] at hop2
    rw [List.length_map, hxl] at hwB₀' hannB'
    obtain ⟨hfn2, hlen2, hpt2⟩ := annot_spine (Or.inr ⟨r, rlvls, rfl⟩) hB₀' hwB₀' hannB' hcall
    have hzD : R.getAppArgs.getD (x.nF + l) default = z := by
      rw [List.getD_eq_getElem?_getD, hz]; rfl
    refine ⟨r, bl, call, hr, by rw [hzD]; exact hop2, erasedEq_const_inv hfn2, ?_, ?_⟩
    · rw [hlen2]; simp [genPvars_length]
    · intro k hk
      obtain ⟨z2, hz2⟩ : ∃ z2, call.getAppArgs[k]? = some z2 :=
        ⟨_, List.getElem?_eq_getElem (by rw [hlen2]; simp [genPvars_length]; omega)⟩
      obtain ⟨a, ha2⟩ : ∃ a, (genPvars g)[k]? = some a :=
        ⟨_, List.getElem?_eq_getElem (by rw [genPvars_length]; exact hk)⟩
      have ha3 : (genPvars g ++ idx ++ [Expr.mkAppN (fvs.getD q.1 default) xs])[k]? = some a := by
        rw [List.append_assoc, List.getElem?_append_left (by rw [genPvars_length]; exact hk)]
        exact ha2
      obtain ⟨T, rfl, -⟩ := genPvars_scoped hg k a ha2
      obtain ⟨Y, Y', Fy, hYa, -, hky, hzY⟩ := hpt2 k _ z2 ha3 hz2
      obtain ⟨T', rfl⟩ := annotate_erasedEq_fvar hYa hky
      obtain ⟨T'', rfl⟩ := erasedEq_fvar_inv hzY
      exact ⟨T'', hz2⟩

end ConLeche.Model
