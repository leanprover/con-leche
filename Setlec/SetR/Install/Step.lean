import Setlec.SetR.Install.ValueKinds
import Setlec.SetR.Install.Axiom

/-!
# The per-declaration install (task #148, T5)

`declStepS` is the `checkDeclR_sound`-shaped lemma T6 consumes: a
`DeclR` derivation extends an `EnvS` to the checked environment.  It is
**pure dispatch** over `DeclR`'s six kinds — the value kinds through
`declDefnS`/`declThmS`/`declOpaqueS`, the axiom kind through
`declAxiomS`, and the two remaining kinds through the obligations
named here.

The `Nonempty` conclusion is `EnvS`'s own convention (a `Prop` carrying
a `TConstVal`, so its inhabitant is data the fold never needs to
name) — the three value kinds now conclude the *named* extension plus
its valuation agreement, and this dispatch forgets both, because v1
genuinely does not need them and the interp2 tier does; the obligations follow the house pattern of `DivModPinS` /
`StdAxiomKeyS` — stated where their consumer is, discharged where
their supplier is.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify SetTheory

universe w

variable {V : Type w} [SetTheory V]

/-- **The basis-block install obligation**: a checked basis
declaration extends the invariant.  Supplier: the basis install (the
pinned blocks' valuations and their laws — `EqLawV`, `basis_pinned`,
`empty_pinned`, the `Quot` rules). -/
def DeclBasisS (V : Type w) [SetTheory V] : Prop :=
  ∀ {env env₂ : Env} {kind : BasisKind} (_m : EnvS V env),
    DeclBasisR env kind env₂ → Nonempty (EnvS V env₂)

/-- **The modeled-inductive-block install obligation**: a checked
`indDecl` block extends the invariant.  Supplier: the block install —
the member fold, the recursor group (consuming the three iota bottoms
`indBottomPlainS`/`indBottomNestedS`/`indBottomProjS`), the capability
record (consuming `etaLawKeyS`/`unitLawKeyS`), the projection installs
and the elimination templates. -/
def DeclIndS (V : Type w) [SetTheory V] : Prop :=
  ∀ {μ : CheckMode} {F : Nat} {env env₂ : Env}
    {block : List ConstantInfo} (m : EnvS V env),
    EtaFamiliesClosed env →
    DeclIndR μ F env m.cval block env₂ →
    Nonempty (EnvS V env₂) ∧ EtaFamiliesClosed env₂

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
theorem basisInstallR_etaClosed :
    ∀ (l : List ConstantInfo) {env env₂ : Env},
      BasisInstallR env l env₂ → basisIndOk l = true →
      EtaFamiliesClosed env → EtaFamiliesClosed env₂
  | [], _, _, h, _, hE => by rw [h]; exact hE
  | ci :: rest, env, env₂, h, hok, hE => by
    obtain ⟨hfresh, htail⟩ := h
    refine basisInstallR_etaClosed rest htail ?_ ?_
    · have := List.all_eq_true.mp hok
      exact List.all_eq_true.mpr fun x hx =>
        this x (List.mem_cons_of_mem _ hx)
    · exact EtaFamiliesClosed.cons_nonind hE
        (Option.isNone_iff_eq_none.mp hfresh)
        (fun cv caps heq hcape =>
          basisIndOk_mem hok List.mem_cons_self heq hcape)

/-- Every pinned basis block passes the former check, by computation. -/
theorem basisIndOk_declsA (kind : BasisKind) :
    basisIndOk kind.declsA = true := by
  cases kind <;> decide

/-- The declaration fold's carrier: a model together with the eta
side invariant it needs one declaration later. -/
def EnvSOk (V : Type w) [SetTheory V] (env : Env) : Prop :=
  Nonempty (EnvS V env) ∧ EtaFamiliesClosed env

/-- **The per-declaration install**, by dispatch: a checked
declaration of any kind extends the invariant. -/
theorem declStepS (hdm : DivModPinS V) (hrp : ReducePinS V)
    (hstd : StdAxiomKeyS V)
    (hbas : DeclBasisS V) (hind : DeclIndS V)
    {μ : CheckMode} {F : Nat} {env env₂ : Env} {d : Declaration}
    (m : EnvS V env) (hE : EtaFamiliesClosed env)
    (h : DeclR μ F m.cval env d env₂) :
    Nonempty (EnvS V env₂) ∧ EtaFamiliesClosed env₂ := by
  cases d with
  | defnDecl cv value hint =>
    refine ⟨⟨(declDefnS hdm m h).choose⟩, ?_⟩
    obtain ⟨type', value', hcv, -, rfl, -, -⟩ := h
    exact EtaFamiliesClosed.cons_nonind hE
      (Option.isNone_iff_eq_none.mp hcv.1) (fun _ _ heq => nomatch heq)
  | thmDecl cv value =>
    refine ⟨⟨(declThmS m h).choose⟩, ?_⟩
    obtain ⟨type', value', hcv, -, -, rfl⟩ := h
    exact EtaFamiliesClosed.cons_nonind hE
      (Option.isNone_iff_eq_none.mp hcv.1) (fun _ _ heq => nomatch heq)
  | opaqueDecl cv value =>
    refine ⟨⟨(declOpaqueS hrp m h).choose⟩, ?_⟩
    obtain ⟨type', value', hcv, -, rfl, -⟩ := h
    exact EtaFamiliesClosed.cons_nonind hE
      (Option.isNone_iff_eq_none.mp hcv.1) (fun _ _ heq => nomatch heq)
  | axiomDecl cv =>
    refine ⟨declAxiomS hstd ofReduceKeyS m h, ?_⟩
    obtain ⟨type', hcv, harm⟩ := h
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
  | basisDecl kind =>
    exact ⟨hbas m h, basisInstallR_etaClosed kind.declsA h.2
      (basisIndOk_declsA kind) hE⟩
  | indDecl block => exact hind m hE h

end Setlec.SetR
