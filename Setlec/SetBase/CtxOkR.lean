import Setlec.SetBase.Weaken
import Setlec.Verify.Leaves

/-!
# `CtxOkR`: the context correspondence for the relation family

The transpose of `Setlec/TTVerify/Claims.lean`'s `CtxOk`, with the
**slack design** of the campaign's §0 decision 1 (`HasType` →
`Infer`-up-to-`DefEq`): the relation family keeps a plain `bvar` rule,
so the correspondence cannot demand the leaf's annotation be the
context entry's *identity* — `defeqStep` opens binder congruences with
each side's own annotation, and only one of the two denotations can sit
in `Δ`.  What it demands instead is an `Infer` derivation for the
variable together with a `DefEq` between the inferred type and the
annotation's denotation; the second side of a binder congruence is then
the first plus the relation's own equality, absorbed by `DefEq.trans`
at each consumption site (the bridge's infer-claim is stated up to
`DefEq` for exactly this reason).

The plumbing is the transpose of `CtxOk.{nil, open, openWith,
weakenTop, app}`; the leaf-shifting steps consume M1
(`{Infer,DefEq}.weakenHead`, `Setlec/SetBase/Weaken.lean`) where the
typing-form `CtxOk` consumed `HasType.weakenHead` — this is the place
the mutual weakening lemma was built for.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify

/-- The context correspondence: every `fvar` leaf of `e` is in scope,
its annotation is scoped below its own variable and denotes, and the
corresponding de Bruijn variable *infers a type `DefEq` to* that
denotation. -/
def CtxOkR (μ : CheckMode) (cval : TConstVal) (env : Env)
    (φ : Name → Nat) (d : Nat) (Δ : List VExpr) (e : Expr) : Prop :=
  Δ.length = d ∧
  ∀ l ∈ e.fvarLeaves, l.1 < d ∧ Expr.fvarsBelow l.1 l.2.2 ∧
    ∃ T, denote cval env φ d l.2.2 = some T ∧
      ∃ T', Infer μ env cval φ Δ (.bvar (d - 1 - l.1)) T' ∧
        DefEq μ env cval φ Δ T' T

variable {μ : CheckMode} {cval : TConstVal} {env : Env} {φ : Name → Nat}

/-- At depth `0` the context is empty and there are no leaves to
constrain — the shape every declaration-level statement uses. -/
theorem CtxOkR.nil {e : Expr} (h : e.fvarLeaves = []) :
    CtxOkR μ cval env φ 0 [] e := by
  refine ⟨rfl, ?_⟩
  intro l hl
  rw [h] at hl
  exact nomatch hl

/-- **Opening a binder extends the context correspondence**, with the
new head typed up to `DefEq` against the annotation's denotation
(`hnew` — the slack form of `CtxOk.openWith`'s `HasType` premise).
Old leaves shift by one head insertion: their `Infer`/`DefEq`
components weaken through M1, their annotations' denotations lift
through `denote_weaken_top`. -/
theorem CtxOkR.openWith (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {d : Nat} {Δ : List VExpr} {body ty : Expr} {n : Name} {A B : VExpr}
    (hb : CtxOkR μ cval env φ d Δ body)
    (ht : CtxOkR μ cval env φ d Δ ty)
    (hty : denote cval env φ d ty = some B)
    (htyb : Expr.fvarsBelow d ty)
    (hnew : ∃ T', Infer μ env cval φ (A :: Δ) (.bvar 0) T' ∧
      DefEq μ env cval φ (A :: Δ) T' (B.liftN 1)) :
    CtxOkR μ cval env φ (d + 1) (A :: Δ)
      (body.instantiate1 (.fvar d n ty)) := by
  -- an already-present leaf: index unchanged, slot shifted by `Δ`'s
  -- new head, annotation one lift deeper, derivations weakened by M1
  have shift : ∀ l : Nat × Name × Expr, l.1 < d →
      Expr.fvarsBelow l.1 l.2.2 →
      (∃ T, denote cval env φ d l.2.2 = some T ∧
        ∃ T', Infer μ env cval φ Δ (.bvar (d - 1 - l.1)) T' ∧
          DefEq μ env cval φ Δ T' T) →
      l.1 < d + 1 ∧ Expr.fvarsBelow l.1 l.2.2 ∧
        ∃ S, denote cval env φ (d + 1) l.2.2 = some S ∧
          ∃ S', Infer μ env cval φ (A :: Δ) (.bvar (d + 1 - 1 - l.1)) S' ∧
            DefEq μ env cval φ (A :: Δ) S' S := by
    intro l hlt hfb ⟨T, hden, T', hI, hD⟩
    refine ⟨by omega, hfb, T.liftN 1, ?_, T'.liftN 1, ?_, ?_⟩
    · rw [denote_weaken_top hcl (Expr.fvarsBelow_mono (by omega) hfb),
        hden]
      rfl
    · have := hI.weakenHead hcl A
      rw [show d + 1 - 1 - l.1 = (d - 1 - l.1) + 1 from by omega]
      simpa [VExpr.lift] using this
    · exact hD.weakenHead hcl A
  refine ⟨by simp [hb.1], ?_⟩
  intro l hl
  rcases Expr.fvarLeaves_instantiate1 body 0 hl with hl' | hl'
  · obtain ⟨hlt, hfb, hpack⟩ := hb.2 l hl'
    exact shift l hlt hfb hpack
  · -- a leaf of the opened variable: the variable itself (the new head
    -- of `Δ`, at index `0`, via `hnew`) or one of its annotation's own
    -- leaves (an already-present leaf)
    rw [Expr.fvarLeaves] at hl'
    rcases List.mem_cons.mp hl' with rfl | hl''
    · obtain ⟨T', hI, hD⟩ := hnew
      refine ⟨by omega, htyb, B.liftN 1, ?_, T', ?_, hD⟩
      · rw [denote_weaken_top hcl htyb, hty]
        rfl
      · rw [show d + 1 - 1 - d = 0 from by omega]
        exact hI
    · obtain ⟨hlt, hfb, hpack⟩ := ht.2 l hl''
      exact shift l hlt hfb hpack

/-- Opening a binder with its *own* annotation: the head of the
extended context is the annotation's denotation, so the new variable's
package is the plain `bvar` rule plus `refl`. -/
theorem CtxOkR.open (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {d : Nat} {Δ : List VExpr} {body ty : Expr} {n : Name} {A : VExpr}
    (hb : CtxOkR μ cval env φ d Δ body)
    (ht : CtxOkR μ cval env φ d Δ ty)
    (hty : denote cval env φ d ty = some A)
    (htyb : Expr.fvarsBelow d ty) :
    CtxOkR μ cval env φ (d + 1) (A :: Δ)
      (body.instantiate1 (.fvar d n ty)) :=
  CtxOkR.openWith hcl hb ht hty htyb
    ⟨A.liftN 1, Infer.bvar rfl, DefEq.refl⟩

/-- Every leaf of an already-scoped expression survives one more
binder — extracted from `openWith`, which is this fact plus the new
variable's.  Transpose of `CtxOk.weakenTop`. -/
theorem CtxOkR.weakenTop (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {d : Nat} {Δ : List VExpr} {e : Expr} {A : VExpr}
    (hC : CtxOkR μ cval env φ d Δ e) :
    CtxOkR μ cval env φ (d + 1) (A :: Δ) e := by
  refine ⟨by simp [hC.1], fun l hl => ?_⟩
  obtain ⟨hlt, hfb, T, hden, T', hI, hD⟩ := hC.2 l hl
  refine ⟨by omega, hfb, T.liftN 1, ?_, T'.liftN 1, ?_, hD.weakenHead hcl A⟩
  · rw [denote_weaken_top hcl (Expr.fvarsBelow_mono (by omega) hfb), hden]
    rfl
  · have := hI.weakenHead hcl A
    rw [show d + 1 - 1 - l.1 = (d - 1 - l.1) + 1 from by omega]
    simpa [VExpr.lift] using this

/-- An application's leaves are its parts'.  Transpose of
`CtxOk.app`. -/
theorem CtxOkR.app {d : Nat} {Δ : List VExpr} {f x : Expr}
    (hf : CtxOkR μ cval env φ d Δ f) (hx : CtxOkR μ cval env φ d Δ x) :
    CtxOkR μ cval env φ d Δ (.app f x) := by
  refine ⟨hf.1, fun l hl => ?_⟩
  rw [Expr.fvarLeaves] at hl
  rcases List.mem_append.mp hl with h | h
  · exact hf.2 l h
  · exact hx.2 l h

/-- **Covered leaves inherit the correspondence.**  `CtxOkR.of_subset`
restricts along *one* expression; a pin whose leaves are scattered
over a whole opening needs the list form.  (`of_subset` is the
singleton case; it stays, because most call sites have one witness.) -/
theorem CtxOkR.of_cover {d : Nat} {Δ : List VExpr} {L : List Expr}
    {e : Expr} (hlen : Δ.length = d)
    (hL : ∀ x ∈ L, CtxOkR μ cval env φ d Δ x)
    (hsub : ∀ l ∈ e.fvarLeaves, ∃ x ∈ L, l ∈ x.fvarLeaves) :
    CtxOkR μ cval env φ d Δ e :=
  ⟨hlen, fun l hl => by
    obtain ⟨x, hx, hlx⟩ := hsub l hl
    exact (hL x hx).2 l hlx⟩

/-- `weakenTop`, iterated: a correspondence survives any number of
fresh binders pushed on the context's head. -/
theorem CtxOkR.weakenN (hcl : ∀ n ψ, VExpr.Closed (cval n ψ)) :
    ∀ (Δ₀ : List VExpr) {d : Nat} {Δ : List VExpr} {e : Expr},
      CtxOkR μ cval env φ d Δ e →
      CtxOkR μ cval env φ (d + Δ₀.length) (Δ₀ ++ Δ) e
  | [], d, Δ, e, h => h
  | A :: Δ₀, d, Δ, e, h => by
    have hrec := CtxOkR.weakenN hcl Δ₀ h
    have := CtxOkR.weakenTop (A := A) hcl hrec
    rw [show d + (A :: Δ₀).length = d + Δ₀.length + 1 from by
      simp only [List.length_cons]; omega]
    exact this

/-- **The canonical context of a telescope opening.**  Opening `k`
`∀`-binders at fresh variables extends the context by exactly the
binders' denotations, and at the extended context *both* the opened
body and every opened variable satisfy the correspondence.

This is `OpenCtxR`'s content in the form the bridge consumes it.  It
is what lets a *pin* — an expression the checker only ever inferred a
type for, whose denotation `InferClaimsR` will produce but only at
some context — be denoted at all: with `CtxOkR.of_cover`, anything
whose leaves are covered by the opening inherits the correspondence,
and `InferClaimsR`'s output denotation does not mention the context.
-/
theorem openPisAtFvars_ctxOkR (hcl : ∀ n ψ, VExpr.Closed (cval n ψ)) :
    ∀ (k : Nat) {e : Expr} {d₀ : Nat} {fvs : List Expr} {body : Expr}
      {Δ : List VExpr} {T : VExpr},
      openPisAtFvars k e d₀ = some (fvs, body) →
      CtxOkR μ cval env φ d₀ Δ e →
      denote cval env φ d₀ e = some T →
      Expr.WScoped d₀ e →
      ∃ Δ₀ : List VExpr, Δ₀.length = k ∧
        CtxOkR μ cval env φ (d₀ + k) (Δ₀ ++ Δ) body ∧
        ∀ x ∈ fvs, CtxOkR μ cval env φ (d₀ + k) (Δ₀ ++ Δ) x := by
  intro k
  induction k with
  | zero =>
    intro e d₀ fvs body Δ T hopen hC _ _
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq]
      at hopen
    obtain ⟨rfl, rfl⟩ := hopen
    exact ⟨[], rfl, by simpa using hC, fun x hx => nomatch hx⟩
  | succ n ih =>
    intro e d₀ fvs body Δ T hopen hC hT hw
    match e, hopen with
    | .forallE nm dom bodyE mb, hopen => ?_
    simp only [openPisAtFvars] at hopen
    cases h1 : openPisAtFvars n
        (bodyE.instantiate1 (.fvar d₀ nm dom)) (d₀ + 1) with
    | none => rw [h1] at hopen; exact nomatch hopen
    | some p => ?_
    rw [h1] at hopen
    simp only [Option.some.injEq, Prod.mk.injEq] at hopen
    obtain ⟨rfl, rfl⟩ := hopen
    have hw' : Expr.WScoped d₀ dom ∧ Expr.WScoped d₀ bodyE := by
      rw [Expr.WScoped] at hw; exact hw
    rw [denote_forallE] at hT
    cases hA : denote cval env φ d₀ dom with
    | none => rw [hA] at hT; exact nomatch hT
    | some A => ?_
    rw [hA] at hT
    cases hB : denote cval env φ (d₀ + 1)
        (bodyE.instantiate1 (.fvar d₀ nm dom)) with
    | none => rw [hB] at hT; exact nomatch hT
    | some B => ?_
    -- `CtxOkR.of_subset` lives downstream (`Bridge/Env.lean`); the two
    -- restrictions here are one line each, so they are taken directly
    have hCdom : CtxOkR μ cval env φ d₀ Δ dom :=
      ⟨hC.1, fun l hl => hC.2 l (by
        rw [Expr.fvarLeaves]; exact List.mem_append_left _ hl)⟩
    have hCbody : CtxOkR μ cval env φ d₀ Δ bodyE :=
      ⟨hC.1, fun l hl => hC.2 l (by
        rw [Expr.fvarLeaves]; exact List.mem_append_right _ hl)⟩
    -- the opened body, and the new variable itself, at `A :: Δ`
    have hCstep : CtxOkR μ cval env φ (d₀ + 1) (A :: Δ)
        (bodyE.instantiate1 (.fvar d₀ nm dom)) :=
      CtxOkR.open hcl hCbody hCdom hA hw'.1.fvarsBelow
    have hCfv : CtxOkR μ cval env φ (d₀ + 1) (A :: Δ)
        (.fvar d₀ nm dom) := by
      refine ⟨by simp [hC.1], fun l hl => ?_⟩
      rw [Expr.fvarLeaves] at hl
      rcases List.mem_cons.mp hl with rfl | hl'
      · refine ⟨by omega, hw'.1.fvarsBelow, A.liftN 1, ?_,
          A.liftN 1, ?_, DefEq.refl⟩
        · rw [denote_weaken_top hcl hw'.1.fvarsBelow, hA]; rfl
        · rw [show d₀ + 1 - 1 - d₀ = 0 from by omega]
          exact Infer.bvar rfl
      · exact (CtxOkR.weakenTop (A := A) hcl hCdom).2 l hl'
    have hw2 : Expr.WScoped (d₀ + 1)
        (bodyE.instantiate1 (.fvar d₀ nm dom)) :=
      Expr.WScoped.instantiate1_gen
        (show Expr.WScoped (d₀ + 1) (.fvar d₀ nm dom) from by
          rw [Expr.WScoped]; exact ⟨by omega, hw'.1⟩) 0
        (hw'.2.mono (Nat.le_succ d₀))
    obtain ⟨Δ₀, hlen, hCb, hCfvs⟩ := ih h1 hCstep hB hw2
    refine ⟨Δ₀ ++ [A], by simp [hlen], ?_, ?_⟩
    · rw [show d₀ + (n + 1) = d₀ + 1 + n from by omega,
        List.append_assoc]
      exact hCb
    · intro x hx
      rw [show d₀ + (n + 1) = d₀ + 1 + n from by omega,
        List.append_assoc]
      rcases List.mem_cons.mp hx with rfl | hx'
      · have := CtxOkR.weakenN hcl Δ₀ hCfv
        rw [hlen] at this
        exact this
      · exact hCfvs x hx'

/-- **The pinned context, per slot.**  The general form: the entries
need not agree, only each leaf's own annotation with the entry at that
leaf's slot.  Stated `_gen` from the start (the pack policy) — the
homogeneous case below is the corollary, and the div/mod
certificates' `[H2, H1, natVR, natVR]` is the reason. -/
theorem CtxOkR.pinnedCtx {d : Nat} {Δ : List VExpr} {e : Expr}
    (hlen : Δ.length = d)
    (hcl : ∀ A ∈ Δ, VExpr.Closed A)
    (hslot : ∀ l ∈ e.fvarLeaves, l.1 < d ∧
      Expr.fvarsBelow l.1 l.2.2 ∧
      denote cval env φ d l.2.2
        = some (Δ.getD (d - 1 - l.1) default)) :
    CtxOkR μ cval env φ d Δ e := by
  refine ⟨hlen, fun l hl => ?_⟩
  obtain ⟨hlt, hfb, hden⟩ := hslot l hl
  have hidx : d - 1 - l.1 < Δ.length := by rw [hlen]; omega
  have hget : Δ[d - 1 - l.1]?
      = some (Δ.getD (d - 1 - l.1) default) := by
    rw [List.getD, List.getElem?_eq_getElem hidx]
    rfl
  have hAcl : VExpr.Closed (Δ.getD (d - 1 - l.1) default) :=
    hcl _ (List.mem_of_getElem? hget)
  refine ⟨hlt, hfb, _, hden, _, ?_, DefEq.refl⟩
  have := Infer.bvar (μ := μ) (env := env) (cval := cval) (φ := φ) hget
  rwa [VExpr.liftN_eq_self_of_closed hAcl] at this

/-- **The pinned context, per slot, with the lift carried.**  The
general form: `CtxOkR` asks for `Infer`+`DefEq`, not for entry
equality, so a slot's entry need only denote *up to `Infer.bvar`'s own
`liftN`*.  `pinnedCtx` above is the corollary where every entry is
closed and the lift vanishes — correct for a context of constant
types, and **not** for a telescope whose later entries mention its
earlier variables (the div/mod certificates' hypothesis slots: a
hypothesis type mentions `x` and `y`, so its depth-`d` denotation is
its own denotation *lifted*, never itself). -/
theorem CtxOkR.pinnedCtxLift {d : Nat} {Δ : List VExpr} {e : Expr}
    (hlen : Δ.length = d)
    (hslot : ∀ l ∈ e.fvarLeaves, l.1 < d ∧
      Expr.fvarsBelow l.1 l.2.2 ∧
      denote cval env φ d l.2.2
        = some ((Δ.getD (d - 1 - l.1) default).liftN (d - l.1))) :
    CtxOkR μ cval env φ d Δ e := by
  refine ⟨hlen, fun l hl => ?_⟩
  obtain ⟨hlt, hfb, hden⟩ := hslot l hl
  have hidx : d - 1 - l.1 < Δ.length := by rw [hlen]; omega
  have hget : Δ[d - 1 - l.1]?
      = some (Δ.getD (d - 1 - l.1) default) := by
    rw [List.getD, List.getElem?_eq_getElem hidx]
    rfl
  refine ⟨hlt, hfb, _, hden, _, ?_, DefEq.refl⟩
  have hb := Infer.bvar (μ := μ) (env := env) (cval := cval) (φ := φ)
    hget
  rwa [show d - 1 - l.1 + 1 = d - l.1 from by omega] at hb

/-- **The canonical constant context** — `pinnedCtx`'s homogeneous
case: every entry is one closed valuation `A`, and every leaf carries
the same annotation denoting it. -/
theorem CtxOkR.constCtx {d : Nat} {ty : Expr} {A : VExpr}
    {e : Expr}
    (hA : VExpr.Closed A)
    (hty : denote cval env φ d ty = some A)
    (htyfb : Expr.fvarsBelow 0 ty)
    (hleaves : ∀ l ∈ e.fvarLeaves, l.1 < d ∧ l.2.2 = ty) :
    CtxOkR μ cval env φ d (List.replicate d A) e := by
  refine CtxOkR.pinnedCtx (by rw [List.length_replicate])
    (fun B hB => by
      rw [List.eq_of_mem_replicate hB]; exact hA)
    (fun l hl => ?_)
  obtain ⟨hlt, hlty⟩ := hleaves l hl
  have hfb : Expr.fvarsBelow l.1 l.2.2 := by
    rw [hlty]
    exact Expr.fvarsBelow_mono (Nat.zero_le _) htyfb
  refine ⟨hlt, hfb, ?_⟩
  rw [hlty, hty, List.getD, List.getElem?_replicate,
    if_pos (show d - 1 - l.1 < d from by omega)]
  rfl

end Setlec.SetR
