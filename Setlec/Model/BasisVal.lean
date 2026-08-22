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

/-- The value of the pair's first projection (the projection-table
entry's constant): `λ α β t. sfst t`, with the lam tags the entry
type's annotation evaluations. -/
noncomputable def pairFstVal (ψ : Name → Nat) : V :=
  let u := ψ uN
  let v := ψ vN
  let c2 := if u = 0 then 0 else Nat.max (Nat.max u v) u
  let c1 := if c2 = 0 then 0 else Nat.max (Nat.max u (v + 1)) c2
  SetTheory.lam c1 (univ u) fun A =>
    SetTheory.lam c2 (pi (v + 1) A fun _ => univ v) fun B =>
      SetTheory.lam u (sigmaSet (Nat.max u v) A fun x => SetTheory.app B x)
        fun t => sfst t

/-- The value of the pair's second projection: `λ α β t. ssnd t`. -/
noncomputable def pairSndVal (ψ : Name → Nat) : V :=
  let u := ψ uN
  let v := ψ vN
  let c2 := if v = 0 then 0 else Nat.max (Nat.max u v) v
  let c1 := if c2 = 0 then 0 else Nat.max (Nat.max u (v + 1)) c2
  SetTheory.lam c1 (univ u) fun A =>
    SetTheory.lam c2 (pi (v + 1) A fun _ => univ v) fun B =>
      SetTheory.lam v (sigmaSet (Nat.max u v) A fun x => SetTheory.app B x)
        fun t => ssnd t

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

/-- The value of `Empty.rec` (a function out of the empty set). -/
noncomputable def emptyRecVal (ψ : Name → Nat) : V :=
  SetTheory.lam (if ψ uN = 0 then 0 else Nat.max 1 (ψ uN))
    (pi (ψ uN + 1) SetTheory.empty fun _ => univ (ψ uN)) fun _M =>
    SetTheory.lam (ψ uN) SetTheory.empty fun _t => pt

/-- The interpreted relation space `α → α → Prop` over a domain. -/
noncomputable def relSpace (u : Nat) (A : V) : V :=
  pi (Nat.max u 1) A fun _ => pi 1 A fun _ => univ 0

/-- The value of the basis quotient type former. -/
noncomputable def quotVal (ψ : Name → Nat) : V :=
  let u := ψ uN
  SetTheory.lam (u + 1) (univ u) fun A =>
    SetTheory.lam (u + 1) (relSpace V u A) fun R => quotSet u A R

/-- The value of `Quot.mk` (class formation). -/
noncomputable def quotMkVal (ψ : Name → Nat) : V :=
  let u := ψ uN
  SetTheory.lam u (univ u) fun A =>
    SetTheory.lam u (relSpace V u A) fun R =>
      SetTheory.lam u A fun a => quotClass u A R a

/-- The interpreted invariance space `∀ a b, r a b → f a = f b`. -/
noncomputable def quotInvSpace (A R f : V) : V :=
  pi 0 A fun a => pi 0 A fun b =>
    pi 0 (app (app R a) b) fun _ => eqv (app f a) (app f b)

/-- The value of `Quot.lift` (the induced map on classes). -/
noncomputable def quotLiftVal (ψ : Name → Nat) : V :=
  let u := ψ uN
  let v := ψ vN
  let cq := if v = 0 then 0 else Nat.max u v
  let cr := if v = 0 then 0 else Nat.max (v + 1) (Nat.max u v)
  let ca := if cr = 0 then 0 else Nat.max (Nat.max u 1) cr
  SetTheory.lam ca (univ u) fun A =>
    SetTheory.lam cr (relSpace V u A) fun R =>
      SetTheory.lam cq (univ v) fun B =>
        SetTheory.lam cq (pi v A fun _ => B) fun f =>
          SetTheory.lam cq (quotInvSpace V A R f) fun _h =>
            SetTheory.lam v (quotSet u A R) fun q =>
              app (quotLift u v A R f) q

/-- The value of `Quot.ind` (a proof point: the motive is
propositional). -/
noncomputable def quotIndVal (ψ : Name → Nat) : V :=
  let u := ψ uN
  SetTheory.lam 0 (univ u) fun A =>
    SetTheory.lam 0 (relSpace V u A) fun R =>
      SetTheory.lam 0 (pi 1 (quotSet u A R) fun _ => univ 0) fun B =>
        SetTheory.lam 0 (pi 0 A fun a => app B (quotClass u A R a))
          fun _mk =>
        SetTheory.lam 0 (quotSet u A R) fun _q => pt

/-- The value of `Quot.sound` (a proof point: the statement is
propositional and true — related elements share their class). -/
noncomputable def quotSoundVal (ψ : Name → Nat) : V :=
  let u := ψ uN
  SetTheory.lam 0 (univ u) fun A =>
    SetTheory.lam 0 (relSpace V u A) fun R =>
      SetTheory.lam 0 A fun a =>
        SetTheory.lam 0 A fun b =>
          SetTheory.lam 0 (app (app R a) b) fun _w => pt

/-- The value of one basis constant (`empty` for non-basis names). -/
noncomputable def pinnedVal (n : Name) (ψ : Name → Nat) : V :=
  if n = eqName then eqVal V ψ
  else if n = eqReflName then eqReflVal V ψ
  else if n = eqName.str "rec" then eqRecVal V ψ
  else if n = natName then omega
  else if n = natZeroName then natzero
  else if n = natSuccName then natSuccVal V ψ
  else if n = natName.str "rec" then natRecVal V ψ
  else if n = psigmaName then psigmaVal V ψ
  else if n = psigmaMkName then psigmaMkVal V ψ
  else if n = psigmaName.str "rec" then psigmaRecVal V ψ
  else if n = punitName then unitSet
  else if n = punitUnitName then pt
  else if n = punitName.str "rec" then punitRecVal V ψ
  else if n = emptyName then SetTheory.empty
  else if n = emptyName.str "rec" then emptyRecVal V ψ
  else if n = quotName then quotVal V ψ
  else if n = quotMkName then quotMkVal V ψ
  else if n = quotLiftName then quotLiftVal V ψ
  else if n = quotIndName then quotIndVal V ψ
  else if n = quotSoundName then quotSoundVal V ψ
  else empty

/-- The pinned (annotated) declaration of one basis constant. -/
def pinnedInfo (n : Name) : ConstantInfo :=
  if n = eqName then eqA
  else if n = eqReflName then eqReflA
  else if n = eqName.str "rec" then eqRecA
  else if n = natName then natA
  else if n = natZeroName then natZeroA
  else if n = natSuccName then natSuccA
  else if n = natName.str "rec" then natRecA
  else if n = psigmaName then psigmaA
  else if n = psigmaMkName then psigmaMkA
  else if n = psigmaName.str "rec" then psigmaRecA
  else if n = punitName then punitA
  else if n = punitUnitName then punitUnitA
  else if n = punitName.str "rec" then punitRecA
  else if n = emptyName then emptyA
  else if n = emptyName.str "rec" then emptyRecA
  else if n = quotName then quotA
  else if n = quotMkName then quotMkA
  else if n = quotLiftName then quotLiftA
  else if n = quotIndName then quotIndA
  else if n = quotSoundName then quotSoundA
  else .axiomInfo ⟨n, [], .sort .zero⟩

/-- Is this constant-info one of the basis kinds? -/
def ConstantInfo.isBasis : ConstantInfo → Bool
  | .indInfo _ _ | .ctorInfo _ _ _ | .recInfo _ _ _ _ => true
  | _ => false

/-- Which names carry constructor-shaped pinned declarations. -/
theorem pinnedInfo_ctorInfo_cases {n : Name} {cv : ConstantVal} {nP nF : Nat}
    (h : pinnedInfo n = .ctorInfo cv nP nF) :
    n = eqReflName ∨ n = natZeroName ∨ n = natSuccName ∨
    n = psigmaMkName ∨ n = punitUnitName ∨ n = quotMkName := by
  delta pinnedInfo at h
  by_cases h1 : n = eqName
  · rw [if_pos h1] at h; exact nomatch h
  rw [if_neg h1] at h
  by_cases h2 : n = eqReflName
  · exact Or.inl h2
  rw [if_neg h2] at h
  by_cases h3 : n = eqName.str "rec"
  · rw [if_pos h3] at h; exact nomatch h
  rw [if_neg h3] at h
  by_cases h4 : n = natName
  · rw [if_pos h4] at h; exact nomatch h
  rw [if_neg h4] at h
  by_cases h5 : n = natZeroName
  · exact Or.inr (Or.inl h5)
  rw [if_neg h5] at h
  by_cases h6 : n = natSuccName
  · exact Or.inr (Or.inr (Or.inl h6))
  rw [if_neg h6] at h
  by_cases h7 : n = natName.str "rec"
  · rw [if_pos h7] at h; exact nomatch h
  rw [if_neg h7] at h
  by_cases h8 : n = psigmaName
  · rw [if_pos h8] at h; exact nomatch h
  rw [if_neg h8] at h
  by_cases h9 : n = psigmaMkName
  · exact Or.inr (Or.inr (Or.inr (Or.inl h9)))
  rw [if_neg h9] at h
  by_cases h10 : n = psigmaName.str "rec"
  · rw [if_pos h10] at h; exact nomatch h
  rw [if_neg h10] at h
  by_cases h11 : n = punitName
  · rw [if_pos h11] at h; exact nomatch h
  rw [if_neg h11] at h
  by_cases h12 : n = punitUnitName
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h12))))
  rw [if_neg h12] at h
  by_cases h13 : n = punitName.str "rec"
  · rw [if_pos h13] at h; exact nomatch h
  rw [if_neg h13] at h
  by_cases h14 : n = emptyName
  · rw [if_pos h14] at h; exact nomatch h
  rw [if_neg h14] at h
  by_cases h15 : n = emptyName.str "rec"
  · rw [if_pos h15] at h; exact nomatch h
  rw [if_neg h15] at h
  by_cases h16 : n = quotName
  · rw [if_pos h16] at h; exact nomatch h
  rw [if_neg h16] at h
  by_cases h17 : n = quotMkName
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h17))))
  rw [if_neg h17] at h
  by_cases h18 : n = quotLiftName
  · rw [if_pos h18] at h; exact nomatch h
  rw [if_neg h18] at h
  by_cases h19 : n = quotIndName
  · rw [if_pos h19] at h; exact nomatch h
  rw [if_neg h19] at h
  by_cases h20 : n = quotSoundName
  · rw [if_pos h20] at h; exact nomatch h
  rw [if_neg h20] at h
  exact nomatch h

/-- Which names carry recursor-shaped pinned declarations. -/
theorem pinnedInfo_recInfo_cases {n : Name} {cv : ConstantVal}
    {mI rP : Nat} {rules : List RecRule}
    (h : pinnedInfo n = .recInfo cv mI rP rules) :
    n = eqName.str "rec" ∨ n = natName.str "rec" ∨
    n = psigmaName.str "rec" ∨ n = punitName.str "rec" ∨
    n = emptyName.str "rec" ∨ n = quotLiftName ∨ n = quotIndName := by
  delta pinnedInfo at h
  by_cases h1 : n = eqName
  · rw [if_pos h1] at h; exact nomatch h
  rw [if_neg h1] at h
  by_cases h2 : n = eqReflName
  · rw [if_pos h2] at h; exact nomatch h
  rw [if_neg h2] at h
  by_cases h3 : n = eqName.str "rec"
  · exact Or.inl h3
  rw [if_neg h3] at h
  by_cases h4 : n = natName
  · rw [if_pos h4] at h; exact nomatch h
  rw [if_neg h4] at h
  by_cases h5 : n = natZeroName
  · rw [if_pos h5] at h; exact nomatch h
  rw [if_neg h5] at h
  by_cases h6 : n = natSuccName
  · rw [if_pos h6] at h; exact nomatch h
  rw [if_neg h6] at h
  by_cases h7 : n = natName.str "rec"
  · exact Or.inr (Or.inl h7)
  rw [if_neg h7] at h
  by_cases h8 : n = psigmaName
  · rw [if_pos h8] at h; exact nomatch h
  rw [if_neg h8] at h
  by_cases h9 : n = psigmaMkName
  · rw [if_pos h9] at h; exact nomatch h
  rw [if_neg h9] at h
  by_cases h10 : n = psigmaName.str "rec"
  · exact Or.inr (Or.inr (Or.inl h10))
  rw [if_neg h10] at h
  by_cases h11 : n = punitName
  · rw [if_pos h11] at h; exact nomatch h
  rw [if_neg h11] at h
  by_cases h12 : n = punitUnitName
  · rw [if_pos h12] at h; exact nomatch h
  rw [if_neg h12] at h
  by_cases h13 : n = punitName.str "rec"
  · exact Or.inr (Or.inr (Or.inr (Or.inl h13)))
  rw [if_neg h13] at h
  by_cases h14 : n = emptyName
  · rw [if_pos h14] at h; exact nomatch h
  rw [if_neg h14] at h
  by_cases h15 : n = emptyName.str "rec"
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h15))))
  rw [if_neg h15] at h
  by_cases h16 : n = quotName
  · rw [if_pos h16] at h; exact nomatch h
  rw [if_neg h16] at h
  by_cases h17 : n = quotMkName
  · rw [if_pos h17] at h; exact nomatch h
  rw [if_neg h17] at h
  by_cases h18 : n = quotLiftName
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h18)))))
  rw [if_neg h18] at h
  by_cases h19 : n = quotIndName
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h19)))))
  rw [if_neg h19] at h
  by_cases h20 : n = quotSoundName
  · rw [if_pos h20] at h; exact nomatch h
  rw [if_neg h20] at h
  exact nomatch h

end Setlec
