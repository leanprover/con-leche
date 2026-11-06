module

public import ConLeche.Semantics.DeclRun

@[expose] public section

/-!
# `declEtaStepRun` — the declaration fold's η-closure half, model-free

The fold's η half, `EtaFamiliesClosed env₂`, off the run record alone.
At every non-inductive kind the η-closure follows from
`ConstantValRun`'s `find?` freshness guard and the cons's kind
(`EtaFamiliesClosed.cons_nonind`; at a pinned basis block,
`basisInstallRun_etaClosed`).  The inductive kind's is the one premise
`hind`, at `DeclRun`'s `Ind` payload (discharged at the fold's
`DeclIndRunDispatchK`, `Model/Fold.lean`).

This module is model-free by construction: no `V`, no `SetTheory`.
-/

namespace ConLeche.Semantics

open ConLeche.Term ConLeche.Verify

/-- Does every pinned basis declaration that is an eta-capable
former carry a reserved name?  Decidable, and `decide`d at each
kind — the basis blocks are literal lists. -/
def basisIndOk (l : List ConstantInfo) : Bool :=
  l.all (fun ci => match ci with
    | .indInfo _ caps => !caps.eta || reservedBasisNames.contains ci.name
    | _ => true)

/-- `basisIndOk` at one member. -/
theorem basisIndOk_mem {l : List ConstantInfo} (h : basisIndOk l = true)
    {ci : ConstantInfo} (hci : ci ∈ l) {cv : ConstantVal}
    {caps : IndCaps} (heq : ci = .indInfo cv caps)
    (hcape : caps.eta = true) :
    reservedBasisNames.contains ci.name = true := by
  have hm := List.all_eq_true.mp h ci hci
  rw [heq] at hm ⊢
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hm
  rcases hm with hm | hm
  · rw [hcape] at hm; exact nomatch hm
  · exact hm

/-- The pinned basis fold keeps the stored eta families closed: every
pinned former it stores carries a reserved name. -/
theorem basisInstallRun_etaClosed :
    ∀ (l : List ConstantInfo) {env env₂ : Env},
      BasisInstallRun env l env₂ → basisIndOk l = true →
      EtaFamiliesClosed env → EtaFamiliesClosed env₂
  | [], _, _, h, _, hE => by rw [h]; exact hE
  | ci :: rest, env, env₂, h, hok, hE => by
    obtain ⟨hfresh, htail⟩ := h
    refine basisInstallRun_etaClosed rest htail ?_ ?_
    · have := List.all_eq_true.mp hok
      exact List.all_eq_true.mpr fun x hx =>
        this x (List.mem_cons_of_mem _ hx)
    · exact EtaFamiliesClosed.cons_nonind hE
        (Option.isNone_iff_eq_none.mp hfresh)
        (fun cv caps heq hcape =>
          basisIndOk_mem hok List.mem_cons_self heq hcape)

/-- Every pinned basis block passes the former check, by computation. -/
theorem basisIndOk_decls (kind : BasisKind) :
    basisIndOk kind.decls = true := by
  cases kind <;> decide

/-- The former check reads no level-parameter name. -/
theorem basisIndOk_atBlock : ∀ (pins block : List ConstantInfo), basisIndOk pins = true →
    basisIndOk (List.zipWith (fun pin c => pin.atLps c.toConstantVal.levelParams) pins block) = true
  | [], _, _ => by simp [basisIndOk]
  | _ :: _, [], _ => by simp [basisIndOk]
  | p :: ps, c :: cs, h => by
    simp only [basisIndOk, List.all_cons, Bool.and_eq_true, List.zipWith_cons_cons] at h ⊢
    refine ⟨?_, basisIndOk_atBlock ps cs h.2⟩
    cases p <;> first | exact h.1 | rfl

/-- A quotient slot passes the former check. -/
theorem basisIndOk_quotPin (k : QuotKind) : basisIndOk [quotPin k] = true := by
  cases k <;> decide

/-- A quotient record's constant passes the former check. -/
theorem basisIndOk_quotAt (k : QuotKind) (cv : ConstantVal) :
    basisIndOk [quotAt k cv] = true :=
  basisIndOk_atBlock [quotPin k] [.axiomInfo cv] (basisIndOk_quotPin k)

/-- **The declaration fold's η-closure half, on the run record** (#161).
It reads `ConstantValRun`'s freshness guard and the kinds' cons shapes
and nothing else, so the fold takes its η half from a valuation-free
record.

The inductive kind is `DeclRun`'s `Ind` parameter here, so the one
premise is at whatever payload the caller instantiates
(`DeclIndRunDispatchK` at the fold). -/
theorem declEtaStepRun {F : Nat}
    {Ind : List ConstantInfo → Nat → Env → Prop}
    {env : Env} {d : Declaration} {env₂ : Env}
    (hind : ∀ {block : List ConstantInfo} {nP : Nat} {envI : Env},
      Ind block nP envI → EtaFamiliesClosed envI)
    (hE : EtaFamiliesClosed env)
    (h : DeclRun F Ind env d env₂) : EtaFamiliesClosed env₂ := by
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
    obtain ⟨type', -, hcv, harm⟩ := h
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
    exact basisInstallRun_etaClosed [quotAt k cv] ⟨hf, rfl⟩ (basisIndOk_quotAt k cv) hE
  | indDecl block nP =>
    simp only [DeclRun] at h
    split at h
    · exact basisInstallRun_etaClosed _ h.2
        (basisIndOk_atBlock _ _ (basisIndOk_decls _)) hE
    · exact hind h

end ConLeche.Semantics
