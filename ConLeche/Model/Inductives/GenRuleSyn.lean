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

end ConLeche.Model
