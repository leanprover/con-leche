import Setlec.Kernel.Basis
import Setlec.SetTheory.Basic

/-!
# The hand-written valuations of the basis constants

`pinnedVal` gives each basis constant its set-theoretic value, as a
function of the level assignment.  The values are `SetTheory.lam` packs
(so constant-headed application spines compute by `app_lam`) whose
domains are the interpretations of the pinned types' domains.

`EnvModel.basis_ok` (in `Interp.lean`) pins the model's valuation of any
installed basis constant to these.
-/

namespace Setlec

variable (V : Type u) [SetTheory V]

open SetTheory Name

/-- The type of constant valuations. -/
abbrev ConstVal (V : Type u) := Name → (Name → Nat) → V

def uN : Name := anonymous |>.str "u"
def u1N : Name := anonymous |>.str "u_1"
def vN : Name := anonymous |>.str "v"

/-- The value of the basis pair type former. -/
noncomputable def psigmaVal (ψ : Name → Nat) : V :=
  let u := ψ uN
  let v := ψ vN
  SetTheory.lam (Nat.max (Nat.max u (v + 1)) (Nat.max u v + 1)) (univ u) fun A =>
    SetTheory.lam (Nat.max u v + 1) (pi (v + 1) A fun _ => univ v) fun B =>
      sigmaSet (Nat.max u v) A fun x => app B x

/-- The value of the basis pair constructor (`lam` tags are the
imax-evaluations of the constructor telescope's codomain sorts). -/
noncomputable def psigmaMkVal (ψ : Name → Nat) : V :=
  let u := ψ uN
  let v := ψ vN
  let w := Nat.max u v
  SetTheory.lam (if w = 0 then 0 else Nat.max u (v + 1)) (univ u) fun A =>
    SetTheory.lam w (pi (v + 1) A fun _ => univ v) fun B =>
      SetTheory.lam w A fun a =>
        SetTheory.lam w (app B a) fun b =>
          if w = 0 then pt else spair a b

/-- The value of one basis constant (`empty` for non-basis names). -/
noncomputable def pinnedVal (n : Name) (ψ : Name → Nat) : V :=
  let u := ψ uN
  let u1 := ψ u1N
  let v := ψ vN
  if n = anonymous.str "Eq" then
    SetTheory.lam (Nat.max u 1) (univ u) fun A =>
      SetTheory.lam (Nat.max u 1) A fun x =>
        SetTheory.lam 1 A fun y => eqv x y
  else if n = (anonymous.str "Eq").str "refl" then
    SetTheory.lam 0 (univ u) fun A =>
      SetTheory.lam 0 A fun _ => pt
  else if n = (anonymous.str "Eq").str "rec" then
    -- λ α a motive refl b h. refl  (equality collapse: ⟦a⟧ = ⟦b⟧)
    SetTheory.lam (basisRecEqV u u1) (univ u) fun A =>
      SetTheory.lam (basisRecEqV2 u u1) A fun a =>
        SetTheory.lam (basisRecEqV3 u u1)
            (pi (Nat.max u1 1) A fun b => pi (u1 + 1) (eqv a b) fun _ => univ u1)
            fun M =>
          SetTheory.lam (basisRecEqV4 u u1) (app (app M a) pt) fun m =>
            SetTheory.lam (basisRecEqV5 u u1) A fun b =>
              SetTheory.lam u1 (eqv a b) fun _ => m
  else if n = anonymous.str "Nat" then omega
  else if n = (anonymous.str "Nat").str "zero" then natzero
  else if n = (anonymous.str "Nat").str "succ" then
    SetTheory.lam 1 omega natsucc
  else if n = (anonymous.str "Nat").str "rec" then
    SetTheory.lam (basisRecNatV u1) (pi (u1 + 1) omega fun _ => univ u1) fun M =>
      SetTheory.lam (basisRecNatV2 u1) (app M natzero) fun z =>
        SetTheory.lam (basisRecNatV3 u1)
            (pi (Nat.max u1 1) omega fun k =>
              pi (Nat.max u1 1) (app M k) fun _ => app M (natsucc k))
            fun s =>
          SetTheory.lam u1 omega fun t => natrec z s t
  else if n = psigmaName then psigmaVal V ψ
  else if n = psigmaMkName then psigmaMkVal V ψ
  else if n = psigmaName.str "rec" then
    -- proof-motive recursor: the result is a proof point
    SetTheory.lam (basisRecSigV u v) (univ u) fun A =>
      SetTheory.lam (basisRecSigV2 u v) (pi (v + 1) A fun _ => univ v) fun B =>
        SetTheory.lam (basisRecSigV3 u v)
            (pi 1 (sigmaSet (Nat.max u v) A fun x => app B x) fun _ => univ 0)
            fun _M =>
          SetTheory.lam (basisRecSigV4 u v)
              (pi 0 A fun a => pi 0 (app B a) fun b =>
                app _M (if Nat.max u v = 0 then pt else spair a b))
              fun _m =>
            SetTheory.lam 0 (sigmaSet (Nat.max u v) A fun x => app B x) fun _t => pt
  else if n = anonymous.str "PUnit" then unitSet
  else if n = (anonymous.str "PUnit").str "unit" then pt
  else if n = (anonymous.str "PUnit").str "rec" then
    SetTheory.lam (basisRecUnitV u u1) (pi (u1 + 1) unitSet fun _ => univ u1) fun M =>
      SetTheory.lam u1 (app M pt) fun m =>
        SetTheory.lam u1 unitSet fun _t => m
  else empty
where
  basisRecEqV (u u1 : Nat) : Nat := Nat.max u (Nat.max u1 1)
  basisRecEqV2 (u u1 : Nat) : Nat := Nat.max u (Nat.max u1 1)
  basisRecEqV3 (u u1 : Nat) : Nat := Nat.max u (Nat.max u1 1)
  basisRecEqV4 (u u1 : Nat) : Nat := Nat.max u u1
  basisRecEqV5 (_u u1 : Nat) : Nat := u1
  basisRecNatV (u1 : Nat) : Nat := Nat.max u1 1
  basisRecNatV2 (u1 : Nat) : Nat := Nat.max u1 1
  basisRecNatV3 (u1 : Nat) : Nat := u1
  basisRecSigV (_u _v : Nat) : Nat := 1
  basisRecSigV2 (_u _v : Nat) : Nat := 1
  basisRecSigV3 (_u _v : Nat) : Nat := 1
  basisRecSigV4 (_u _v : Nat) : Nat := 0
  basisRecUnitV (u u1 : Nat) : Nat := Nat.max u u1

/-- The value of the basis unit recursor (`λ M m t. m`; tags are the
imax-evaluations of the recursor telescope). -/
noncomputable def punitRecVal (ψ : Name → Nat) : V :=
  let u1 := ψ u1N
  let u := ψ uN
  let w := if u1 = 0 then 0 else Nat.max u u1
  SetTheory.lam w (pi (u1 + 1) unitSet fun _ => univ u1) fun M =>
    SetTheory.lam w (app M pt) fun m =>
      SetTheory.lam u1 unitSet fun _ => m

/-- The value of the basis equality type former (truth values of set
equality). -/
noncomputable def eqVal (ψ : Name → Nat) : V :=
  let u := ψ uN
  SetTheory.lam (Nat.max u (Nat.max u 1)) (univ u) fun A =>
    SetTheory.lam (Nat.max u 1) A fun x =>
      SetTheory.lam 1 A fun y => eqv x y

/-- The value of `Eq.refl` (a proof point under the Prop collapse). -/
noncomputable def eqReflVal (_ψ : Name → Nat) : V :=
  SetTheory.lam 0 (univ (_ψ uN)) fun _A =>
    SetTheory.lam 0 _A fun _x => pt

/-- The motive space of `Eq.rec` over a domain and a base point. -/
noncomputable def eqRecMSpace (u1 : Nat) (A a : V) : V :=
  pi (u1 + 1) A fun b => pi (u1 + 1) (eqv a b) fun _ => univ u1

/-- The value of `Eq.rec` (`λ α a motive refl b h. refl`: transport is
the identity under equality collapse). -/
noncomputable def eqRecVal (ψ : Name → Nat) : V :=
  let u := ψ uN
  let u1 := ψ u1N
  let w := if u1 = 0 then 0 else Nat.max u u1
  let s := if u1 = 0 then 0 else Nat.max u (u1 + 1)
  SetTheory.lam s (univ u) fun A =>
    SetTheory.lam s A fun a =>
      SetTheory.lam w (eqRecMSpace V u1 A a) fun M =>
        SetTheory.lam w (app (app M a) pt) fun r =>
          SetTheory.lam u1 A fun _b =>
            SetTheory.lam u1 (eqv a _b) fun _h => r

/-- The value of `PSigma'.rec` (Prop-motive only: the result is a proof
point; every lam tag is `0` because the whole telescope, from the motive
binder on, is propositional — and so are the binders before it, since
the codomain chain ends in `motive t : Prop`). -/
noncomputable def psigmaRecVal (ψ : Name → Nat) : V :=
  let u := ψ uN
  let v := ψ vN
  SetTheory.lam 0 (univ u) fun A =>
    SetTheory.lam 0 (pi (v + 1) A fun _ => univ v) fun B =>
      SetTheory.lam 0
          (pi 1 (sigmaSet (Nat.max u v) A fun x => app B x) fun _ => univ 0)
          fun M =>
        SetTheory.lam 0
            (pi 0 A fun a => pi 0 (app B a) fun b =>
              app M (if Nat.max u v = 0 then pt else spair a b)) fun _m =>
          SetTheory.lam 0 (sigmaSet (Nat.max u v) A fun x => app B x)
            fun _t => pt

/-- The value of `Nat.succ`. -/
noncomputable def natSuccVal (_ψ : Name → Nat) : V :=
  SetTheory.lam 1 omega natsucc

/-- The value of `Nat.rec` (set-theoretic recursion on omega). -/
noncomputable def natRecVal (ψ : Name → Nat) : V :=
  let u := ψ uN
  let w := if u = 0 then 0 else Nat.max 1 u
  SetTheory.lam w (pi (u + 1) omega fun _ => univ u) fun M =>
    SetTheory.lam w (app M natzero) fun z =>
      SetTheory.lam w
          (pi u omega fun n => pi u (app M n) fun _ => app M (natsucc n))
          fun s =>
        SetTheory.lam u omega fun t => natrec z s t

/-- Is this constant-info one of the basis kinds? -/
def ConstantInfo.isBasis : ConstantInfo → Bool
  | .indInfo _ | .ctorInfo _ _ _ | .recInfo _ _ _ _ _ _ => true
  | _ => false

end Setlec
