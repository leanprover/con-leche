import Setlec.SetR.Weaken
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
(`{Infer,DefEq}.weakenHead`, `Setlec/SetR/Weaken.lean`) where the
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

end Setlec.SetR
