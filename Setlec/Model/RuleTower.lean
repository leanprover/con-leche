import Setlec.Model.TeleElim

/-!
# λ-tower machinery for the total rule equality (task #58)

`RecRulesOk` states, per fireable recursor rule, a **total equality of
function values**: the interpretation of the rule's canonical
left-hand side λ-tower (`ruleLhs`, built by `closeLamsAt` over an
opened frame) equals the interpretation of the stored rule right-hand
side, as sets.  This module holds the generic machinery on both sides
of that contract:

* the syntactic frame invariant `FrameWf` and the `closeLamsAt`
  bookkeeping (scoping, loose bvars, the abstraction/instantiation
  roundtrip, the interpretation's one-binder unfolding);
* the **producer** side (`TowerOk.out`): a caller-supplied pointwise
  spec (`TowerOk` — interp-equal domains stage by stage over fitting
  values, equal interpretations and a truthful left body at the
  bottom) yields the total equality *and* the tower's own truthful
  annotations (`AnnotOk`).  Rationale: two dependent-function graphs
  over equal domain chains are equal iff they agree on fitting inputs;
  off-domain behavior is canonical junk (`Derive/Graphs.lean`), and
  the Prop collapse is self-handling (`lam 0 _ _ = pt` on both
  sides).  Modeled installs build `TowerOk` from the checked
  `_model.iota_j` theorem, basis installs from the hand-written
  values.
* the **consumer** side (`closeLamsAt_fold`): values fitting the frame
  (`FrameFit`) beta-reduce the interpreted tower onto its instantiated
  body at the canonical extension frame (`snocFrame`), with every
  application inside a certified slot (`ChainSlots`) — everything the
  iota step's reduct annotation chain needs, at any frame, from the
  stored equality by pure `app` congruence.
-/

namespace Setlec

variable {V : Type u} [SetTheory V] {cval : ConstVal V} {env : Env}
  {φ : Name → Nat}

open SetTheory Expr

/-! ## The syntactic frame invariant -/

/-- Well-formedness of a closing frame over a body: the variables sit
at consecutive indices starting at `d`; each annotation is scoped
below its own index, free of loose bvars, and paired with a
codomain-sort annotation; and each variable is mentioned
*consistently* (same name and annotation) by the body and by every
later variable's annotation — what the abstraction/instantiation
roundtrip of `closeLamsAt` needs. -/
def FrameWf : Nat → List (Expr × BinderMeta) → Expr → Prop
  | d, [], bL => WScoped d bL ∧ bL.looseBVarsBounded 0 = true
  | d, (fv, m) :: rest, bL =>
    (∃ nm ty, fv = .fvar d nm ty ∧ WScoped d ty ∧
      ty.looseBVarsBounded 0 = true ∧ (∃ cod, m.cod = some cod) ∧
      Expr.fvarConsistent d nm ty bL ∧
      ∀ p ∈ rest, Expr.fvarConsistent d nm ty (Expr.fvarTypeD p.1)) ∧
    FrameWf (d + 1) rest bL

/-- A closed tower has bounded loose bvars: each abstraction step
introduces exactly the bvar its `λ` binds. -/
theorem FrameWf.closeLamsAt_bounded :
    ∀ {fvms : List (Expr × BinderMeta)} {d : Nat} {bL : Expr},
      FrameWf d fvms bL →
      (closeLamsAt fvms bL).looseBVarsBounded 0 = true := by
  intro fvms
  induction fvms with
  | nil =>
    intro d bL h
    exact h.2
  | cons p rest ih =>
    intro d bL h
    obtain ⟨⟨nm, ty, heq, hw, hb, -, -, -⟩, hrest⟩ := h
    obtain ⟨fv, m⟩ := p
    subst heq
    show (Expr.lam nm ty ((closeLamsAt rest bL).abstract1 d) m).looseBVarsBounded
      0 = true
    have hbody := looseBVarsBounded_abstract1 (d := d)
      (closeLamsAt rest bL) 0 (ih hrest)
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨hb, hbody⟩

/-- A closed tower is scoped at the frame base. -/
theorem FrameWf.closeLamsAt_wscoped :
    ∀ {fvms : List (Expr × BinderMeta)} {d : Nat} {bL : Expr},
      FrameWf d fvms bL → WScoped d (closeLamsAt fvms bL) := by
  intro fvms
  induction fvms with
  | nil =>
    intro d bL h
    exact h.1
  | cons p rest ih =>
    intro d bL h
    obtain ⟨⟨nm, ty, heq, hw, -, -, -, -⟩, hrest⟩ := h
    obtain ⟨fv, m⟩ := p
    subst heq
    show WScoped d (Expr.lam nm ty ((closeLamsAt rest bL).abstract1 d) m)
    simp only [WScoped]
    exact ⟨hw, WScoped.abstract1 0 (ih hrest)⟩

/-- Frame variables below the frame stay consistently mentioned by the
closed tower. -/
theorem closeLamsAt_fvarConsistent {dv : Nat} {nv : Name} {tyv : Expr} :
    ∀ {fvms : List (Expr × BinderMeta)} {d : Nat} {bL : Expr},
      dv < d → FrameWf d fvms bL →
      Expr.fvarConsistent dv nv tyv bL →
      (∀ p ∈ fvms, Expr.fvarConsistent dv nv tyv (Expr.fvarTypeD p.1)) →
      Expr.fvarConsistent dv nv tyv (closeLamsAt fvms bL) := by
  intro fvms
  induction fvms with
  | nil =>
    intro d bL _ _ hc _
    exact hc
  | cons p rest ih =>
    intro d bL hlt h hc htys
    obtain ⟨⟨nm, ty, heq, -, -, -, -, -⟩, hrest⟩ := h
    obtain ⟨fv, m⟩ := p
    subst heq
    show Expr.fvarConsistent dv nv tyv
      (Expr.lam nm ty ((closeLamsAt rest bL).abstract1 d) m)
    refine ⟨?_, ?_⟩
    · have := htys _ List.mem_cons_self
      simpa [Expr.fvarTypeD] using this
    · exact fvarConsistent_abstract1 (by omega) _ 0
        (ih (by omega) hrest hc
          (fun q hq => htys q (List.mem_cons_of_mem _ hq)))

/-- The roundtrip: re-opening the freshly closed binder restores the
inner tower. -/
theorem FrameWf.roundtrip {d : Nat} {nm : Name} {ty : Expr}
    {m : BinderMeta} {fvms : List (Expr × BinderMeta)} {bL : Expr}
    (h : FrameWf d ((.fvar d nm ty, m) :: fvms) bL) :
    ((closeLamsAt fvms bL).abstract1 d).instantiate1 (.fvar d nm ty) 0 =
      closeLamsAt fvms bL := by
  obtain ⟨⟨nm', ty', heq, -, -, -, hcb, htys⟩, hrest⟩ := h
  injection heq with _ hnm hty'
  subst hnm
  subst hty'
  exact abstract1_instantiate1 _ 0
    (closeLamsAt_fvarConsistent (by omega) hrest hcb htys)
    hrest.closeLamsAt_bounded

/-- One-binder unfolding of the closed tower's interpretation: a `λ`
over the head variable's annotation whose fibres re-enter the inner
tower at the extended frame. -/
theorem interp_closeLamsAt_cons {d : Nat} {ρ : Nat → V} {nm : Name}
    {ty : Expr} {m : BinderMeta} {cod : Level}
    {fvms : List (Expr × BinderMeta)} {bL : Expr}
    (h : FrameWf d ((.fvar d nm ty, m) :: fvms) bL)
    (hcod : m.cod = some cod) :
    interpExpr V cval env φ d ρ (closeLamsAt ((.fvar d nm ty, m) :: fvms) bL) =
      match interpExpr V cval env φ d ρ ty with
      | none => none
      | some A => some (SetTheory.lam (cod.eval φ) A fun x =>
          (interpExpr V cval env φ (d + 1) (updV V ρ d x)
            (closeLamsAt fvms bL)).getD SetTheory.empty) := by
  show interpExpr V cval env φ d ρ
    (.lam nm ty ((closeLamsAt fvms bL).abstract1 d) m) = _
  rw [interpExpr, hcod, h.roundtrip]
  rfl

/-! ## The producer side: pointwise spec ⇒ total equality + `AnnotOk` -/

/-- Caller-supplied pointwise spec of the two towers: stage by stage
(over every member of the — shared — interpreted domain) the frame
annotation and the right-hand tower's binder domain interpret to the
same set and the frame annotation is truthful; at the bottom the two
bodies interpret to the same value and the left body is truthful.
The binder metadata is *shared* by construction (`ruleLhs` copies the
right-hand side's), so no codomain-sort condition appears. -/
inductive TowerOk (cval : ConstVal V) (env : Env) (φ : Name → Nat) :
    Nat → (Nat → V) → List (Expr × BinderMeta) → Expr → Expr → Prop
  | nil {d : Nat} {ρ : Nat → V} {bL eR : Expr} {w : V} :
      interpExpr V cval env φ d ρ bL = some w →
      interpExpr V cval env φ d ρ eR = some w →
      AnnotOk V cval env φ d ρ bL →
      TowerOk cval env φ d ρ [] bL eR
  | cons {d : Nat} {ρ : Nat → V} {nm : Name} {ty : Expr} {m : BinderMeta}
      {fvms : List (Expr × BinderMeta)} {bL : Expr}
      {nmR : Name} {tyR bodyR : Expr} {A : V} :
      interpExpr V cval env φ d ρ ty = some A →
      interpExpr V cval env φ d ρ tyR = some A →
      AnnotOk V cval env φ d ρ ty →
      (∀ x, x ∈ˢ A →
        TowerOk cval env φ (d + 1) (updV V ρ d x) fvms bL
          (bodyR.instantiate1 (.fvar d nmR tyR))) →
      TowerOk cval env φ d ρ ((.fvar d nm ty, m) :: fvms) bL
        (.lam nmR tyR bodyR m)

/-- The total equality and the closed tower's truthful annotations,
from the pointwise spec: two interpreted λ-towers over pointwise
interp-equal domain chains with (pointwise) equal bodies are **equal
sets** — `lam_congr` per stage, the Prop collapse self-handling — and
the left tower inherits truthful annotations from the right one's. -/
theorem TowerOk.out :
    ∀ {d : Nat} {ρ : Nat → V} {fvms : List (Expr × BinderMeta)}
      {bL eR : Expr},
      TowerOk cval env φ d ρ fvms bL eR →
      FrameWf d fvms bL →
      AnnotOk V cval env φ d ρ eR →
      (∃ v, interpExpr V cval env φ d ρ (closeLamsAt fvms bL) = some v ∧
        interpExpr V cval env φ d ρ eR = some v) ∧
      AnnotOk V cval env φ d ρ (closeLamsAt fvms bL) := by
  intro d ρ fvms bL eR ht
  induction ht with
  | nil hbL heR hA =>
    intro _ _
    exact ⟨⟨_, hbL, heR⟩, hA⟩
  | @cons d ρ nm ty m fvms bL nmR tyR bodyR A hty htyR hAty hrec ih =>
    intro hwf hAR
    obtain ⟨⟨nm', ty', heq, hwty, hbty, ⟨cod, hcod⟩, hcb, htys⟩, hwfT⟩ := hwf
    injection heq with _ hnm hty'
    subst hnm
    subst hty'
    have hwf' : FrameWf d ((Expr.fvar d nm ty, m) :: fvms) bL :=
      ⟨⟨nm, ty, rfl, hwty, hbty, ⟨cod, hcod⟩, hcb, htys⟩, hwfT⟩
    simp only [AnnotOk] at hAR
    obtain ⟨hAtyR, -, hcondR⟩ := hAR
    -- pointwise facts of the two fibres
    have hfib : ∀ x, x ∈ˢ A →
        (∃ v, interpExpr V cval env φ (d + 1) (updV V ρ d x)
            (closeLamsAt fvms bL) = some v ∧
          interpExpr V cval env φ (d + 1) (updV V ρ d x)
            (bodyR.instantiate1 (.fvar d nmR tyR)) = some v) ∧
        AnnotOk V cval env φ (d + 1) (updV V ρ d x)
          (closeLamsAt fvms bL) := by
      intro x hx
      exact ih x hx hwfT (hcondR x A htyR hx).1
    constructor
    · -- the equality
      refine ⟨SetTheory.lam (cod.eval φ) A fun x =>
        (interpExpr V cval env φ (d + 1) (updV V ρ d x)
          (closeLamsAt fvms bL)).getD SetTheory.empty, ?_, ?_⟩
      · rw [interp_closeLamsAt_cons hwf' hcod, hty]
      · rw [interpExpr, hcod, htyR]
        refine congrArg some (lam_congr fun x hx => ?_)
        obtain ⟨⟨v, hL, hR⟩, -⟩ := hfib x hx
        rw [hL, hR]
    · -- the closed tower's truthful annotations
      show AnnotOk V cval env φ d ρ
        (.lam nm ty ((closeLamsAt fvms bL).abstract1 d) m)
      have hrt := hwf'.roundtrip
      simp only [AnnotOk]
      refine ⟨hAty, ⟨cod, hcod⟩, ?_⟩
      intro x A₀ hA₀ hx
      have hA0 : A₀ = A := by
        rw [hty] at hA₀
        exact (Option.some.inj hA₀).symm
      rw [hA0] at hx
      obtain ⟨⟨v, hL, hR⟩, hAL⟩ := hfib x hx
      refine ⟨?_, ?_⟩
      · show AnnotOk V cval env φ (d + 1) (updV V ρ d x)
          (((closeLamsAt fvms bL).abstract1 d).instantiate1
            (.fvar d nm ty) 0)
        rw [hrt]
        exact hAL
      · intro v' hv'
        have hv0 : v' = cod := by
          rw [hcod] at hv'
          exact (Option.some.inj hv').symm
        rw [hv0]
        obtain ⟨w', B, hw', hwB, hBu⟩ :=
          (hcondR x A htyR hx).2 cod hcod
        have hwv : w' = v := by
          rw [hR] at hw'
          exact (Option.some.inj hw').symm
        rw [hwv] at hwB
        refine ⟨v, B, ?_, hwB, hBu⟩
        show interpExpr V cval env φ (d + 1) (updV V ρ d x)
          (((closeLamsAt fvms bL).abstract1 d).instantiate1
            (.fvar d nm ty) 0) = some v
        rw [hrt]
        exact hL

/-! ## The consumer side: fitting values beta-reduce the tower -/

/-- The canonical frame extension: push the values onto the valuation
at consecutive indices. -/
def snocFrame (d : Nat) (ρ : Nat → V) : List V → Nat × (Nat → V)
  | [] => (d, ρ)
  | x :: xs => snocFrame (d + 1) (updV V ρ d x) xs

/-- Values fitting the frame's (progressively opened) annotations at
the canonical valuation built from the values themselves. -/
inductive FrameFit (cval : ConstVal V) (env : Env) (φ : Name → Nat) :
    Nat → (Nat → V) → List (Expr × BinderMeta) → List V → Prop
  | nil {d : Nat} {ρ : Nat → V} : FrameFit cval env φ d ρ [] []
  | cons {d : Nat} {ρ : Nat → V} {nm : Name} {ty : Expr} {m : BinderMeta}
      {fvms : List (Expr × BinderMeta)} {x : V} {xs : List V} {A : V} :
      interpExpr V cval env φ d ρ ty = some A →
      x ∈ˢ A →
      FrameFit cval env φ (d + 1) (updV V ρ d x) fvms xs →
      FrameFit cval env φ d ρ ((.fvar d nm ty, m) :: fvms) (x :: xs)

/-- Folding the interpreted closed tower over fitting values: the
result is the body's interpretation at the canonical extension frame,
and every application stays inside a certified slot.  The tower's own
truthful annotations (from `TowerOk.out`, transported) supply the
fibre packages; the Prop collapse is self-handling. -/
theorem closeLamsAt_fold :
    ∀ {fvms : List (Expr × BinderMeta)} {xs : List V} {d : Nat}
      {ρ : Nat → V} {bL : Expr},
      FrameFit cval env φ d ρ fvms xs →
      FrameWf d fvms bL →
      AnnotOk V cval env φ d ρ (closeLamsAt fvms bL) →
      ∀ {L : V}, interpExpr V cval env φ d ρ (closeLamsAt fvms bL) = some L →
      ∃ w, interpExpr V cval env φ (snocFrame (V := V) d ρ xs).1
          (snocFrame (V := V) d ρ xs).2 bL = some w ∧
        SpineFold V L xs = w ∧ ChainSlots V L xs := by
  intro fvms xs d ρ bL hfit
  induction hfit with
  | nil =>
    intro _ _ L hi
    exact ⟨L, hi, rfl, trivial⟩
  | @cons d ρ nm ty m fvms x xs A hty hx hfit ih =>
    intro hwf hA L hi
    obtain ⟨⟨nm', ty', heq, hwty, hbty, ⟨cod, hcod⟩, hcb, htys⟩, hwfT⟩ := hwf
    injection heq with _ hnm hty'
    subst hnm
    subst hty'
    have hwf' : FrameWf d ((Expr.fvar d nm ty, m) :: fvms) bL :=
      ⟨⟨nm, ty, rfl, hwty, hbty, ⟨cod, hcod⟩, hcb, htys⟩, hwfT⟩
    rw [interp_closeLamsAt_cons hwf' hcod, hty] at hi
    obtain rfl := Option.some.inj hi
    have hrt := hwf'.roundtrip
    have hA' : AnnotOk V cval env φ d ρ
        (.lam nm ty ((closeLamsAt fvms bL).abstract1 d) m) := hA
    simp only [AnnotOk] at hA'
    obtain ⟨hAty, -, hcond⟩ := hA'
    have hcond' : ∀ y (A₀ : V),
        interpExpr V cval env φ d ρ ty = some A₀ → y ∈ˢ A₀ →
        AnnotOk V cval env φ (d + 1) (updV V ρ d y)
          (closeLamsAt fvms bL) ∧
        ∀ v, m.cod = some v →
          ∃ w B, interpExpr V cval env φ (d + 1) (updV V ρ d y)
              (closeLamsAt fvms bL) = some w ∧
            w ∈ˢ B ∧ B ∈ˢ univ (v.eval φ) := by
      intro y A₀ hA₀ hy
      have h0 := hcond y A₀ hA₀ hy
      rw [hrt] at h0
      exact h0
    -- functionalized fibre packages for the beta step and the slot
    have hfibres : ∀ y, y ∈ˢ A → ∃ B,
        ((interpExpr V cval env φ (d + 1) (updV V ρ d y)
          (closeLamsAt fvms bL)).getD SetTheory.empty) ∈ˢ B ∧
        B ∈ˢ univ (cod.eval φ) := by
      intro y hy
      obtain ⟨-, hpack⟩ := hcond' y A hty hy
      obtain ⟨w, B, hw, hwB, hBu⟩ := hpack cod hcod
      rw [hw]
      exact ⟨B, hwB, hBu⟩
    obtain ⟨Bf, hBf1, hBf2⟩ := choose_fibres hfibres
    have happ : SetTheory.app
        (SetTheory.lam (cod.eval φ) A fun y =>
          (interpExpr V cval env φ (d + 1) (updV V ρ d y)
            (closeLamsAt fvms bL)).getD SetTheory.empty) x =
        (interpExpr V cval env φ (d + 1) (updV V ρ d x)
          (closeLamsAt fvms bL)).getD SetTheory.empty :=
      app_lam hx hBf1 hBf2
    obtain ⟨hAsub, hpack⟩ := hcond' x A hty hx
    obtain ⟨w0, B0, hw0, -, -⟩ := hpack cod hcod
    obtain ⟨w, hwi, hfold, hchain⟩ := ih hwfT hAsub hw0
    refine ⟨w, hwi, ?_, ?_⟩
    · rw [SpineFold_cons, happ, hw0]
      simpa using hfold
    · refine ⟨⟨cod.eval φ, A, Bf, lam_mem hBf1, hx, hBf2⟩, ?_⟩
      rw [happ, hw0]
      simpa using hchain

end Setlec
