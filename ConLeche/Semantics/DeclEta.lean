module

public import ConLeche.Semantics.DeclRun

@[expose] public section

/-!
# `declEtaStepRun` — the declaration fold's η-closure half, model-free

The fold's η half, `EtaFamiliesClosed env₂`, off the run record alone.
At every non-inductive kind the η-closure follows from
`ConstantValRun`'s `find?` freshness guard and the cons's kind
(`EtaFamiliesClosed.cons_nonind`).  The inductive kind's is the one premise
`hind`, at `DeclKindRun`'s `Ind` payload (discharged at the fold's
`DeclIndRunDispatchK`, `Model/Fold.lean`).

This module is model-free by construction: no `V`, no `SetTheory`.
-/

namespace ConLeche.Semantics

open ConLeche.Term ConLeche.Verify

/-- **The declaration fold's η-closure half, on the run record** (#161).
It reads `ConstantValRun`'s freshness guard and the kinds' cons shapes
and nothing else, so the fold takes its η half from a valuation-free
record.

The inductive kind is `DeclKindRun`'s `Ind` parameter here, so the one
premise is at whatever payload the caller instantiates
(`DeclIndRunDispatchK` at the fold). -/
theorem declEtaStepRun {F : Nat}
    {Ind : List ConstantInfo → Nat → Env → Prop}
    {env : Env} {d : Declaration} {env₂ : Env}
    (hind : ∀ {block : List ConstantInfo} {nP : Nat} {envI : Env},
      Ind block nP envI → EtaFamiliesClosed envI)
    (hE : EtaFamiliesClosed env)
    (h : DeclKindRun F Ind env d env₂) : EtaFamiliesClosed env₂ := by
  cases d with
  | defnDecl cv value hint =>
    obtain ⟨type', value', hcv, -, rfl, -, -⟩ := h
    exact EtaFamiliesClosed.cons_nonind hE
      (Option.isNone_iff_eq_none.mp hcv.1) (fun _ _ heq => nomatch heq)
  | thmDecl cv value =>
    obtain ⟨-, type', value', hcv, -, -, rfl⟩ := h
    exact EtaFamiliesClosed.cons_nonind hE
      (Option.isNone_iff_eq_none.mp hcv.1) (fun _ _ heq => nomatch heq)
  | opaqueDecl cv value =>
    obtain ⟨-, type', value', hcv, -, rfl, -⟩ := h
    exact EtaFamiliesClosed.cons_nonind hE
      (Option.isNone_iff_eq_none.mp hcv.1) (fun _ _ heq => nomatch heq)
  | axiomDecl cv =>
    rcases h with ⟨-, -, -, hf, rfl⟩ | h
    · exact EtaFamiliesClosed.cons_nonind hE (Option.isNone_iff_eq_none.mp hf)
        (fun _ _ heq => nomatch heq)
    obtain ⟨-, type', -, hcv, harm⟩ := h
    have hfresh : env.find? cv.name = none :=
      Option.isNone_iff_eq_none.mp hcv.1
    rcases harm with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ |
      ⟨-, -, -, -, -, -, -, rfl⟩
    · exact EtaFamiliesClosed.cons_nonind hE hfresh
        (fun _ _ heq => nomatch heq)
    · exact EtaFamiliesClosed.cons_nonind hE hfresh
        (fun _ _ heq => nomatch heq)
    · exact EtaFamiliesClosed.cons_nonind hE hfresh
        (fun _ _ heq => nomatch heq)
    · exact hE
  | quotDecl k cv =>
    obtain ⟨-, -, hf, rfl⟩ := h
    refine EtaFamiliesClosed.cons_nonind hE (Option.isNone_iff_eq_none.mp hf)
      fun cv' caps heq hcape => ?_
    -- the package's one former, `Quot`, carries no η capability
    cases k with
    | type =>
      injection heq with _ hc
      subst hc
      exact absurd hcape (by decide)
    | _ => exact nomatch heq
  | indDecl block nP => exact hind h

end ConLeche.Semantics
