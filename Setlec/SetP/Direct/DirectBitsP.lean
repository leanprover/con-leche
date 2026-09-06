import Setlec.SetP.Annot.BitLemmas
import Setlec.Semantics.Tower.TowerLeaf
import Setlec.Verify.InferLemmas
import Setlec.Verify.Extend.Inversions
import Setlec.Verify.InstLevels
import Setlec.Verify.BinderLoop
import Setlec.Verify.Mono
import Setlec.Verify.Subst
import Setlec.Kernel.Direct

/-!
# The direct structure's annotated Π-bits are exact (task #175 W4c, P3 module 1)

The tower leaves' folds need the annotated Π-types' codomain bits
*exactly*: the type former's parameter binders carry a nonzero bit
(their codomains end in `Sort w`, of sort `succ w`), the constructor's
and recursor's binders carry a bit that is zero exactly when the
result sort (resp. the elimination sort) evaluates to zero.  Validity
(`AnnotValidV`) is one-directional — a zero bit at an empty-domain
codomain is valid — so the content is *syntactic*: in verified mode
`inferTypeCore`'s `.forallE` clause validates `equiv (zeronessOf v)
mb.pw` against the opened body's inferred sort `v`
(`inferTypeCore_forall_inv`), and `checkConstantVal` runs that
inference on the annotated type.  This module walks the Π-prefix
(`piBits_of_infer`), pins the innermost sort per block constant, and
reads the bits off the `denoteP` reading (`stripPisAV_bits`) — the
three walks (`checkConstantVal`, `openPisAtFvars`, `denoteP`) open
the binders with the same `fvar`s, so one predicate over the opening
(`PiBitsOpen`) serves all three.
-/

namespace Setlec.Semantics
open Setlec.SetModel

open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  BinderMeta inferTypeCore ensureSortCore whnf openPisAtFvars)

variable {mode : CheckMode}

/-! ## Leaf clauses of the inference, inverted -/

theorem whnf_sort_eq {env : Env} {F d : Nat} {u : Level} {e' : Expr}
    (h : whnf mode env F d (.sort u) = .ok e') : e' = .sort u := by
  have h1 := Setlec.whnf_mono (Nat.le_add_right F 2) h
  rw [Setlec.whnf_sort] at h1
  exact (Except.ok.inj h1).symm

theorem ensureSortCore_sort_eq {env : Env} {F d : Nat} {u v : Level}
    (h : ensureSortCore mode env F d (.sort u) = .ok v) : v = u :=
  Expr.sort.inj (whnf_sort_eq (Setlec.ensureSortCore_inv h))

theorem inferTypeCore_sort_inv {env : Env} {F d : Nat} {u : Level} {t : Expr}
    (h : inferTypeCore mode env F d (.sort u) = .ok t) :
    t = .sort (.succ u) := by
  match F, h with
  | 0, h => rw [Setlec.inferTypeCore_zero] at h; exact nomatch h
  | F + 1, h =>
    rw [Setlec.inferTypeCore_succ] at h
    simp only [Setlec.inferBody, Setlec.viewM, Expr.view, pure, Except.pure,
      Bind.bind, Except.bind] at h
    exact (Except.ok.inj h).symm

theorem inferTypeCore_fvar_inv {env : Env} {F d idx : Nat} {n : Name}
    {ty t : Expr} (h : inferTypeCore mode env F d (.fvar idx n ty) = .ok t) :
    idx < d ∧ t = ty := by
  match F, h with
  | 0, h => rw [Setlec.inferTypeCore_zero] at h; exact nomatch h
  | F + 1, h =>
    rw [Setlec.inferTypeCore_succ] at h
    simp only [Setlec.inferBody, Setlec.viewM, Expr.view, pure, Except.pure,
      Bind.bind, Except.bind] at h
    split at h
    · exact ⟨‹_›, (Except.ok.inj h).symm⟩
    · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])

/-- A run on an application spine carries a run on its head. -/
theorem inferTypeCore_mkAppN_fn_inv {env : Env} {F d : Nat} :
    ∀ (as : List Expr) {f t : Expr},
      inferTypeCore mode env F d (Expr.mkAppN f as) = .ok t →
      ∃ tf, inferTypeCore mode env F d f = .ok tf
  | [], _, t, h => ⟨t, h⟩
  | a :: as, f, t, h => by
    obtain ⟨tfa, hfa⟩ := inferTypeCore_mkAppN_fn_inv as (f := .app f a) h
    obtain ⟨tf, _, _, _, _, hf, -⟩ := Setlec.inferTypeCore_app_inv' hfa
    exact ⟨tf, hf⟩

/-- **A spine into a sort**: applying a head whose type is a
Π-telescope of the spine's length ending in `Sort s` types at
`Sort s` — the sort carries no bound variables, so the per-argument
instantiations leave it alone. -/
theorem inferTypeCore_mkAppN_sort {env : Env} {F d : Nat} :
    ∀ (as : List Expr) {f ty : Expr} {bs : List (Name × Expr × BinderMeta)}
      {s : Level} {t : Expr},
      inferTypeCore mode env F d f = .ok ty →
      ty.stripPis as.length = some (bs, .sort s) →
      inferTypeCore mode env F d (Expr.mkAppN f as) = .ok t →
      t = .sort s
  | [], f, ty, bs, s, t, hf, hst, h => by
    obtain rfl : ty = t := Except.ok.inj (hf.symm.trans h)
    simp only [List.length_nil, Expr.stripPis, Option.some.injEq,
      Prod.mk.injEq] at hst
    exact hst.2
  | a :: as, f, ty, bs, s, t, hf, hst, h => by
    obtain ⟨nm, dom, body, mb, rfl⟩ :
        ∃ nm dom body mb, ty = .forallE nm dom body mb := by
      cases ty <;> first
        | exact ⟨_, _, _, _, rfl⟩
        | simp [Expr.stripPis] at hst
    obtain ⟨tfa, hfa⟩ := inferTypeCore_mkAppN_fn_inv as (f := .app f a) h
    obtain ⟨tf, n', ty', body', m', hf', hw, rfl, -⟩ :=
      Setlec.inferTypeCore_app_inv' hfa
    obtain rfl : tf = .forallE nm dom body mb :=
      Except.ok.inj (hf'.symm.trans hf)
    obtain ⟨rfl, rfl, rfl, rfl⟩ := Expr.forallE.inj (Setlec.whnf_forallE_eq hw)
    simp only [List.length_cons, Expr.stripPis, Option.map_eq_some_iff] at hst
    obtain ⟨⟨bs', body₀⟩, hst', heq⟩ := hst
    simp only [Prod.mk.injEq] at heq
    obtain ⟨-, rfl⟩ := heq
    have hsome := Expr.stripPis_instantiate1_isSome (v := a) as.length
      (e := body') 0 (by rw [hst']; rfl)
    obtain ⟨⟨bs'', body''⟩, hst''⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨hb, -⟩ := Expr.stripPis_instantiate1_eq (v := a) as.length 0
      hst' hst''
    rw [Expr.instantiate1_sort] at hb
    subst hb
    exact inferTypeCore_mkAppN_sort as hfa hst'' h

/-! ## The opening walk -/

/-- The first `n` binders of `e`, opened from depth `d` with the
inference's own `fvar`s, each codomain bit zero exactly when `z`. -/
def PiBitsOpen (φ : Name → Nat) (z : Prop) : Nat → Nat → Expr → Prop
  | 0, _, _ => True
  | n + 1, d, .forallE nm dom body mb =>
    (pwBit φ mb.pw = 0 ↔ z) ∧
      PiBitsOpen φ z n (d + 1) (body.instantiate1 (.fvar d nm dom))
  | _ + 1, _, _ => False

theorem PiBitsOpen.congr {φ : Name → Nat} {z z' : Prop} (hz : z ↔ z') :
    ∀ {n d : Nat} {e : Expr}, PiBitsOpen φ z n d e → PiBitsOpen φ z' n d e
  | 0, _, _, _ => trivial
  | _ + 1, _, .forallE _ _ _ _, h =>
    ⟨h.1.trans hz, PiBitsOpen.congr hz h.2⟩
  | _ + 1, _, .bvar _, h | _ + 1, _, .fvar _ _ _, h | _ + 1, _, .sort _, h
  | _ + 1, _, .const _ _, h | _ + 1, _, .app _ _, h | _ + 1, _, .lam _ _ _ _, h
  | _ + 1, _, .letE _ _ _ _, h | _ + 1, _, .lit _, h | _ + 1, _, .proj _ _ _, h =>
    h.elim

theorem eval_imax_eq_zero_iff (φ : Name → Nat) (l r : Level) :
    Level.eval φ (.imax l r) = 0 ↔ Level.eval φ r = 0 := by
  simp only [Level.eval]
  split
  · next h => exact ⟨fun _ => h, fun _ => rfl⟩
  · next h => exact ⟨fun h' => absurd (Nat.max_eq_zero_iff.mp h').2 h, fun h' => absurd h' h⟩

/-- **The Π-prefix walk**: in verified mode, the first `n` binders'
bits of an inferred type are exact against the innermost opened
body's inferred sort, and the whole type's sort is zero exactly when
that one is (`imax`'s zero-ness is its right argument's). -/
theorem piBits_of_infer {env : Env} (hver : mode.verified = true) :
    ∀ (n : Nat) {F d : Nat} {e t : Expr} {v₀ : Level} {fvs : List Expr}
      {opened : Expr},
      openPisAtFvars n e d = some (fvs, opened) →
      inferTypeCore mode env F d e = .ok t →
      ensureSortCore mode env F d t = .ok v₀ →
      ∃ (F' : Nat) (tb : Expr) (vb : Level),
        inferTypeCore mode env F' (d + n) opened = .ok tb ∧
        ensureSortCore mode env F' (d + n) tb = .ok vb ∧
        (∀ φ, Level.eval φ v₀ = 0 ↔ Level.eval φ vb = 0) ∧
        ∀ φ, PiBitsOpen φ (Level.eval φ vb = 0) n d e
  | 0, F, d, e, t, v₀, fvs, opened, hop, h, hens => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨-, rfl⟩ := hop
    exact ⟨F, t, v₀, h, hens, fun _ => Iff.rfl, fun _ => trivial⟩
  | n + 1, F, d, e, t, v₀, fvs, opened, hop, h, hens => by
    match e, hop, h with
    | .forallE nm dom body mb, hop, h =>
      match F, h with
      | 0, h => rw [Setlec.inferTypeCore_zero] at h; exact nomatch h
      | F + 1, h =>
        obtain ⟨tty, u, bt, v, -, -, hbt, hensb, hz, rfl⟩ :=
          Setlec.inferTypeCore_forall_inv h
        simp only [openPisAtFvars] at hop
        split at hop
        · next fvs' e' hop' =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hop
          obtain ⟨-, rfl⟩ := hop
          obtain ⟨F', tb, vb, hrun, hensb', hv, hbits⟩ :=
            piBits_of_infer hver n hop' hbt hensb
          refine ⟨F', tb, vb, ?_, ?_, ?_, ?_⟩
          · rw [show d + (n + 1) = d + 1 + n from by omega]; exact hrun
          · rw [show d + (n + 1) = d + 1 + n from by omega]; exact hensb'
          · intro φ
            rw [ensureSortCore_sort_eq hens, eval_imax_eq_zero_iff]
            exact hv φ
          · intro φ
            exact ⟨(pwBit_of_equiv_zeronessOf (hz hver) φ).trans (hv φ),
              hbits φ⟩
        · exact nomatch hop
    | .bvar _, hop, _ | .fvar _ _ _, hop, _ | .sort _, hop, _
    | .const _ _, hop, _ | .app _ _, hop, _ | .lam _ _ _ _, hop, _
    | .letE _ _ _ _, hop, _ | .lit _, hop, _ | .proj _ _ _, hop, _ =>
      simp [openPisAtFvars] at hop

/-! ## The bits, read -/

/-- The reading's Π-peel carries the syntactic bits: `denoteP` opens
with the same `fvar`s. -/
theorem stripPisAV_bits {acval : Name → (Name → Nat) → AVExpr} {env : Env}
    {φ : Name → Nat} {z : Prop} :
    ∀ (n : Nat) {d : Nat} {e : Expr} {ea : AVExpr}
      {pps : List (Nat × Nat × AVExpr)} {b : AVExpr},
      PiBitsOpen φ z n d e → denoteP acval env φ d e = some ea →
      stripPisAV n ea = some (pps, b) →
      ∀ p ∈ pps, (p.2.1 = 0 ↔ z)
  | 0, d, e, ea, pps, b, _, _, hst => by
    simp only [stripPisAV, Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, -⟩ := hst
    intro p hp
    exact absurd hp (by simp)
  | n + 1, d, e, ea, pps, b, hbits, hden, hst => by
    match e, hbits with
    | .forallE nm dom body mb, ⟨hhead, htail⟩ =>
      obtain ⟨ta, ba, -, hba, rfl⟩ := denoteP_forallE_inv hden
      simp only [stripPisAV, Option.map_eq_some_iff] at hst
      obtain ⟨⟨pps', b'⟩, hst', heq⟩ := hst
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hhead
      · exact stripPisAV_bits n htail hba hst' p hp
    | .bvar _, h | .fvar _ _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _ _, h | .letE _ _ _ _, h | .lit _, h | .proj _ _ _, h =>
      exact h.elim

/-! ## `openPisAtFvars` bookkeeping -/

theorem openPisAtFvars_length :
    ∀ (n : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {o : Expr},
      openPisAtFvars n e d = some (fvs, o) → fvs.length = n
  | 0, e, d, fvs, o, h => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; rfl
  | n + 1, e, d, fvs, o, h => by
    match e, h with
    | .forallE nm dom body mb, h =>
      simp only [openPisAtFvars] at h
      split at h
      · next fvs' e' h' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1, List.length_cons, openPisAtFvars_length n h']
      · exact nomatch h
    | .bvar _, h | .fvar _ _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _ _, h | .letE _ _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [openPisAtFvars] at h

/-- Two consecutive openings are one. -/
theorem openPisAtFvars_add :
    ∀ (n : Nat) {m : Nat} {e : Expr} {d : Nat} {fvs fvs' : List Expr}
      {o o' : Expr},
      openPisAtFvars n e d = some (fvs, o) →
      openPisAtFvars m o (d + n) = some (fvs', o') →
      openPisAtFvars (n + m) e d = some (fvs ++ fvs', o')
  | 0, m, e, d, fvs, fvs', o, o', h, h' => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simpa using h'
  | n + 1, m, e, d, fvs, fvs', o, o', h, h' => by
    match e, h with
    | .forallE nm dom body mb, h =>
      simp only [openPisAtFvars] at h
      split at h
      · next fvs₁ e₁ h₁ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have h'' := openPisAtFvars_add n h₁
          (by rw [show d + 1 + n = d + (n + 1) from by omega]; exact h')
        rw [show n + 1 + m = n + m + 1 from by omega]
        simp only [openPisAtFvars]
        rw [h'']
        rfl
      · exact nomatch h
    | .bvar _, h | .fvar _ _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _ _, h | .letE _ _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [openPisAtFvars] at h

/-- Opening a telescope whose stripped body is a sort reaches that
sort (sorts carry no bound variables). -/
theorem openPisAtFvars_of_stripPis_sort :
    ∀ (n : Nat) {e : Expr} (d : Nat) {bs : List (Name × Expr × BinderMeta)}
      {s : Level},
      e.stripPis n = some (bs, .sort s) →
      ∃ fvs, openPisAtFvars n e d = some (fvs, .sort s)
  | 0, e, d, bs, s, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨[], by rw [h.2]; rfl⟩
  | n + 1, e, d, bs, s, h => by
    match e, h with
    | .forallE nm dom body mb, h =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs', body₀⟩, hst', heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨-, rfl⟩ := heq
      have hsome := Expr.stripPis_instantiate1_isSome
        (v := .fvar d nm dom) n (e := body) 0 (by rw [hst']; rfl)
      obtain ⟨⟨bs'', body''⟩, hst''⟩ := Option.isSome_iff_exists.mp hsome
      obtain ⟨hb, -⟩ := Expr.stripPis_instantiate1_eq
        (v := .fvar d nm dom) n 0 hst' hst''
      rw [Expr.instantiate1_sort] at hb
      subst hb
      obtain ⟨fvs, hop⟩ := openPisAtFvars_of_stripPis_sort n (d + 1) hst''
      refine ⟨Expr.fvar d nm dom :: fvs, ?_⟩
      show (match openPisAtFvars n (body.instantiate1 (.fvar d nm dom)) (d + 1)
          with
        | some (fvs, e) => some (Expr.fvar d nm dom :: fvs, e)
        | none => none) = _
      rw [hop]
    | .bvar _, h | .fvar _ _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _ _, h | .letE _ _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [Expr.stripPis] at h

/-- A domain shape preserved by instantiation carries from the raw
binder to the opened variable's type. -/
theorem openPisAtFvars_dom_pred (P : Expr → Prop)
    (hP : ∀ (e v : Expr) (j : Nat), P e → P (e.instantiate1 v j)) :
    ∀ (n : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {o : Expr}
      {bs : List (Name × Expr × BinderMeta)} {body : Expr},
      openPisAtFvars n e d = some (fvs, o) →
      e.stripPis n = some (bs, body) →
      ∀ (i : Nat) (b : Name × Expr × BinderMeta) (x : Expr),
        bs[i]? = some b → fvs[i]? = some x → P b.2.1 → P x.fvarTypeD
  | 0, e, d, fvs, o, bs, body, hop, hst, i, b, x, hb, _, _ => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hst
    rw [← hst.1] at hb
    exact nomatch hb
  | n + 1, e, d, fvs, o, bs, body, hop, hst, i, b, x, hb, hx, hPb => by
    match e, hop, hst with
    | .forallE nm dom bd mb, hop, hst =>
      simp only [openPisAtFvars] at hop
      split at hop
      · next fvs₁ e₁ h₁ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        simp only [Expr.stripPis, Option.map_eq_some_iff] at hst
        obtain ⟨⟨bs', body₀⟩, hst', heq⟩ := hst
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hb hx
          subst hb; subst hx
          exact hPb
        | succ i =>
          simp only [List.getElem?_cons_succ] at hb hx
          have hsome := Expr.stripPis_instantiate1_isSome
            (v := .fvar d nm dom) n (e := bd) 0 (by rw [hst']; rfl)
          obtain ⟨⟨bs'', body''⟩, hst''⟩ := Option.isSome_iff_exists.mp hsome
          obtain ⟨-, hdoms⟩ := Expr.stripPis_instantiate1_eq
            (v := .fvar d nm dom) n 0 hst' hst''
          have hlen : bs''.length = bs'.length := by
            rw [Expr.stripPis_length n hst'', Expr.stripPis_length n hst']
          have hi : i < bs''.length := by
            rw [hlen]; exact (List.getElem?_eq_some_iff.mp hb).1
          obtain ⟨b'', hb''⟩ : ∃ b'', bs''[i]? = some b'' :=
            ⟨_, List.getElem?_eq_getElem hi⟩
          have hdom := hdoms i b b'' hb hb''
          refine openPisAtFvars_dom_pred P hP n h₁ hst'' i b'' x hb'' hx ?_
          rw [hdom, Nat.zero_add]
          exact hP _ _ _ hPb
      · exact nomatch hop
    | .bvar _, hop, _ | .fvar _ _ _, hop, _ | .sort _, hop, _
    | .const _ _, hop, _ | .app _ _, hop, _ | .lam _ _ _ _, hop, _
    | .letE _ _ _ _, hop, _ | .lit _, hop, _ | .proj _ _ _, hop, _ =>
      simp [openPisAtFvars] at hop

end Setlec.Semantics
