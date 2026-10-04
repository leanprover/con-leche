module

import ConLeche.Model.Annot.Bit
import ConLeche.Model.Annot.BitLemmas
public import ConLeche.Semantics.Tower.BlockRecTower
import ConLeche.Semantics.Kit
import ConLeche.Model.Inductives.StructRecKit
import ConLeche.Model.IndFrame
import ConLeche.Model.Inductives.BlockRecRead
import ConLeche.Semantics.BasisOk
import ConLeche.Model.Rules.Sound
import ConLeche.Model.Annot.BitInst
public import ConLeche.Model.Inductives.FixKit
import ConLeche.Model.Annot.BitRename

public section

/-!
# Reading a rule body at its opened frame

`denoteMeta` has no `.bvar` clause, so nothing with a loose bound
variable has a reading at all: a rule body is read at its OPENED form.
The opening is the check's own (`openPisAtFvars`/`instantiateList` at
`(fvsPref ++ fvsF).reverse`) — loose `bvar j` becomes `fvar (E - 1 - j)`
at a frame of `E` variables, which `denoteMeta` at depth `E` reads
straight back as `bvar j`.  So an opened reading has EXACTLY the raw
term's de Bruijn indices.

`FvarList E xs` is that opening list, taken as a PARAMETER rather than
spelled: `denoteMeta` ignores an `fvar`'s stored type, so the frames
the check builds (whose types are the rule's domains) and the ih
frame's are all instances of the same claim.  Around it: a node's own
typing (`IhTyped`), the local frame's fit (`LocalsFit`), the frame's
context (`WalkCtx`), and the capture-avoiding peel moved to the opened
frame (`instPisAtLift_instSeq`) and evaluated (`interp_peelPis_mkPisAV`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal ConstantInfo)

universe uv

/-! ## The opening list -/

/-- **A frame opening**: `xs` replaces the `E` loose bound variables of
a term by free variables, `bvar j ↦ fvar (E - 1 - j)`, which is what
`openPisAtFvars`' fvars do when `instantiateList`d in reverse
(the rule check's `(fvsPref ++ fvsF).reverse`).  The fvars' stored
TYPES are free: `denoteMeta` does not read them. -/
@[expose] def FvarList (E : Nat) (xs : List Expr) : Prop :=
  xs.length = E ∧ (∀ j, j < E → ∃ ty : Expr, xs[j]? = some (.fvar (E - 1 - j) ty)) ∧
    ∀ x ∈ xs, Expr.WScoped E x

theorem FvarList.cons {E : Nat} {xs : List Expr} (h : FvarList E xs) (ty : Expr)
    (hty : Expr.WScoped E ty) :
    FvarList (E + 1) (Expr.fvar E ty :: xs) := by
  refine ⟨by simp [h.1], fun j hj => ?_, fun x hx => ?_⟩
  · cases j with
    | zero => exact ⟨ty, by simp⟩
    | succ j =>
      obtain ⟨ty', hty'⟩ := h.2.1 j (by omega)
      refine ⟨ty', ?_⟩
      rw [show E + 1 - 1 - (j + 1) = E - 1 - j from by omega]
      simpa using hty'
  · rcases List.mem_cons.mp hx with rfl | hx'
    · simp only [Expr.WScoped]
      exact ⟨by omega, hty⟩
    · exact Expr.WScoped.mono (Nat.le_succ E) (h.2.2 x hx')

/-! ## The literal readings are lift-invariant

`BitShift.lean` has these at `liftN 1`; the abstraction inserts `nR`
binders at once, and the leaves' closedness gives every `n`. -/

theorem natLitAV_liftN_gen {za sa : AnnotTerm} {n k : Nat}
    (hz : za.liftN n k = za) (hs : sa.liftN n k = sa) :
    ∀ m : Nat, (natLitAV za sa m).liftN n k = natLitAV za sa m
  | 0 => hz
  | m + 1 => by
    show (AnnotTerm.app sa (natLitAV za sa m)).liftN n k = _
    rw [AnnotTerm.liftN_app, hs, natLitAV_liftN_gen hz hs m]
    rfl

theorem charListAV_liftN_gen {nilA consA ofNatA za sa : AnnotTerm} {n k : Nat}
    (hnil : nilA.liftN n k = nilA) (hcons : consA.liftN n k = consA)
    (hof : ofNatA.liftN n k = ofNatA) (hz : za.liftN n k = za) (hs : sa.liftN n k = sa) :
    ∀ cs : List Char,
      (charListAV nilA consA ofNatA za sa cs).liftN n k
        = charListAV nilA consA ofNatA za sa cs
  | [] => hnil
  | c :: cs => by
    show (AnnotTerm.app (.app consA (.app ofNatA (natLitAV za sa c.toNat)))
      (charListAV nilA consA ofNatA za sa cs)).liftN n k = _
    rw [AnnotTerm.liftN_app, AnnotTerm.liftN_app, AnnotTerm.liftN_app, hcons, hof,
      natLitAV_liftN_gen hz hs, charListAV_liftN_gen hnil hcons hof hz hs cs]
    rfl

variable {acval : Name → (Name → Nat) → AnnotTerm} {env : Env} {φ : Name → Nat}

theorem denoteMeta_bvar {D j : Nat} : denoteMeta acval env φ D (.bvar j) = none := by
  rw [denoteMeta] <;> simp

/-! ## The frame kit: the `nR` ih binders, dropped

`AnnotTerm.liftN nR · d` is matched by `shiftE nR d`, and at the
rule's frame that is exactly "forget the ih block". -/

variable {V : Type uv} [SetTheory V]

theorem shiftE_consList_ih {d nR : Nat} {locals ihvals : List V} {ρ' : Nat → V}
    (hloc : locals.length = d) (hih : ihvals.length = nR) :
    shiftE nR d (consList locals (consList ihvals ρ')) = consList locals ρ' := by
  funext i
  rw [shiftE]
  rcases Nat.lt_or_ge i d with hi | hi
  · rw [ite_eq_left hi, consList_getD_of_lt _ _ _ (by omega),
      consList_getD_of_lt _ _ _ (by omega)]
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + d := ⟨i - d, by omega⟩
    rw [ite_eq_right (by omega),
      show i' + d + nR = (i' + nR) + locals.length from by omega,
      consList_apply_add, ← hloc, consList_apply_add,
      show i' + nR = i' + ihvals.length from by omega, consList_apply_add]

/-- **The node's own typing**: the residue sub-term the walk has
reached was inferred by the rule stage's own run, at the checker's
CERTIFIED grade (`inferTypeCore μ` at `μ = .verified` is
`Infer … .full`, `Rules.inferTypeCore_bridge`).

The fit of a guarded call's arguments is
a fact about an OCCURRENCE — the run certified THAT node's arguments
— and a premise quantified over every expression of the call's shape
says nothing about it.  The walk that visits the occurrence carries
this hypothesis exactly as it carries `hasFvar` and `looseBVarsBounded`. -/
@[expose] def IhTyped (envT : Env) (D : Nat) (e : Expr) : Prop :=
  ∃ t : Expr, ConLeche.Rules.Infer envT .full D e t

/-! ## The frame, in the shape the reading battery wants

`FvarList E as1` is the check's own opening list — DESCENDING, because
`instantiateList` consumes `bvar 0` first.  The reading battery is
stated over the ASCENDING list `L` with `L[k] = fvar k`, through `Expr.instSeq`.
They are the same frame reversed, and these three lemmas are the
bridge. -/

/-- The opening list, reversed, is the ascending frame. -/
theorem FvarList.reverse_length {E : Nat} {as1 : List Expr} (h : FvarList E as1) :
    as1.reverse.length = E := by rw [List.length_reverse, h.1]

theorem FvarList.reverse_idx {E : Nat} {as1 : List Expr} (h : FvarList E as1) :
    ∀ (k : Nat) (x : Expr), as1.reverse[k]? = some x → ∃ ty, x = Expr.fvar k ty := by
  intro k x hx
  have hk : k < E := by
    rcases Nat.lt_or_ge k E with hk | hk
    · exact hk
    · rw [List.getElem?_eq_none (by rw [h.reverse_length]; omega)] at hx
      exact nomatch hx
  rw [List.getElem?_reverse (by rw [h.1]; omega), h.1] at hx
  obtain ⟨ty, hty⟩ := h.2.1 (E - 1 - k) (by omega)
  rw [hty] at hx
  exact ⟨ty, by rw [← Option.some.inj hx, show E - 1 - (E - 1 - k) = k from by omega]⟩

/-! ## The frame's CONTEXT, threaded with the walk

`hfit`'s discharge runs through `certs_sound`, whose conclusion is
`∀ ρ, Sat V Δa ρ → TeleFitPA …`: it needs a CONTEXT at the frame the
walk has reached — the check's `rP + nF + nR` block extended by the
`d` binders the walk opened.  It is ONE predicate, threaded with the
walk, because the residue's opening list
`as2` and the context `Δa` are INDEX-ALIGNED: `as2[j]` is the frame's
variable `D - 1 - j`, `Δa[j]` is its domain's reading at its own
depth, and `Sat`'s orientation (innermost first) is `as2`'s — so all
four obligations `ctxOk_of_openers` asks are read off one list.

The context lives at `envT`, the CONSTRUCTORS' environment, because
that is where the rule stage's `inferType` ran; the residue mentions
no block recursor (the abstraction replaced every guarded call by an
`ih` opener), which is what lets its readings live there at all. -/

/-- **The walk's context**: the residue frame's opening list `as2`,
the context `Δa` its domains read to, and a valuation satisfying it.
The last three conjuncts are the frame's HEREDITARY facts — the
annotations are closed, bounded by `envT`, and draw their own leaves
from the frame — which is what makes `CtxOk` a projection
(`WalkCtx.ctxOk`) rather than a construction at every node. -/
@[expose] def WalkCtx (V : Type uv) [SetTheory V] {envT : Env} (mT : EnvModel V envT)
    (φ : Name → Nat) (D : Nat) (ρfull : Nat → V) (Δa : List AnnotTerm) (as2 : List Expr) :
    Prop :=
  Δa.length = D ∧
  Sat V Δa ρfull ∧
  (∀ (j : Nat) (x : Expr), as2[j]? = some x →
    denoteMeta mT.acval envT φ (D - 1 - j) (Expr.fvarTypeD x) = some (Δa.getD j default)) ∧
  (∀ s, s < D → ∀ ρ : Nat → V, Sat V Δa ρ →
    WellDenotedV V (fun j => ρ (j + s + 1)) (Δa.getD s default)) ∧
  (∀ x ∈ as2, (Expr.fvarTypeD x).looseBVarsBounded 0 = true) ∧
  (∀ x ∈ as2, ConstsBound envT x) ∧
  (∀ x ∈ as2, ∀ l ∈ (Expr.fvarTypeD x).fvarLeaves, Expr.fvar l.1 l.2 ∈ as2)

/-- **Opening one binder extends the walk's context.**  The new slot
is the binder's own domain, read at the frame it was opened at; its
`Sat` obligation is the membership the binder congruences hand over
(the same one `LocalsFit.cons` consumes) and its `hokΔ` obligation is
the domain's GRADING, which the rule stage's own inference supplies
(`infer_sound` at `IhTyped.lamDom`).  Every older slot's obligation
weakens for free, because it is stated at the slot's own shifted
valuation and `Sat_tail` is the shift. -/
theorem WalkCtx.cons {envT : Env} {mT : EnvModel V envT} {φ : Name → Nat} {D : Nat}
    {ρfull : Nat → V} {Δa : List AnnotTerm} {as2 : List Expr}
    (h : WalkCtx V mT φ D ρfull Δa as2) {ty : Expr} {ta : AnnotTerm} {x : V}
    (hta : denoteMeta mT.acval envT φ D ty = some ta)
    (hlb : ty.looseBVarsBounded 0 = true) (hcb : ConstsBound envT ty)
    (hcl : ∀ l ∈ ty.fvarLeaves, Expr.fvar l.1 l.2 ∈ as2)
    (hG : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ta)
    (hx : x ∈ˢ interp V ρfull ta) :
    WalkCtx V mT φ (D + 1) (cons x ρfull) (ta :: Δa) (Expr.fvar D ty :: as2) := by
  obtain ⟨hlen, hsat, hdoms, hok, hlbs, hcbs, hcls⟩ := h
  refine ⟨by simp [hlen], Sat_cons V hsat hx, ?_, ?_, ?_, ?_, ?_⟩
  · intro j y hy
    cases j with
    | zero =>
      obtain rfl : y = Expr.fvar D ty := by simpa using hy.symm
      rw [show D + 1 - 1 - 0 = D from by omega,
        show (Expr.fvar D ty).fvarTypeD = ty from rfl]
      simpa using hta
    | succ j =>
      rw [show D + 1 - 1 - (j + 1) = D - 1 - j from by omega]
      have := hdoms j y (by simpa using hy)
      simpa using this
  · intro s hs ρ hρ
    cases s with
    | zero => exact hG _ (Sat_tail hρ)
    | succ s =>
      have heq : (fun j => ρ (j + (s + 1) + 1)) = fun j => ρ (j + s + 1 + 1) := by
        funext j; congr 1
      rw [show ((ta :: Δa).getD (s + 1) default) = Δa.getD s default from rfl, heq]
      exact hok s (by omega) (fun j => ρ (j + 1)) (Sat_tail hρ)
  · intro y hy
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact hlb
    · exact hlbs y hy'
  · intro y hy
    rcases List.mem_cons.mp hy with rfl | hy'
    · rw [constsBound_fvar]; exact hcb
    · exact hcbs y hy'
  · intro y hy l hl
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact List.mem_cons_of_mem _ (hcl l hl)
    · exact List.mem_cons_of_mem _ (hcls y hy' l hl)

/-- **`CtxOk` from the walk's context**, at any node the frame opened:
`ctxOk_of_openers` at the ASCENDING form of the opening list.  Every
one of its six inputs is a field of `WalkCtx` or of the `FvarList`;
nothing is proved per node but the leaf membership, which
`fvarLeaves_instantiateList` gives for the whole walk at once. -/
theorem WalkCtx.ctxOk {envT : Env} {mT : EnvModel V envT} {φ : Name → Nat} {D : Nat}
    {ρfull : Nat → V} {Δa : List AnnotTerm} {as2 : List Expr}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (mT.acval n ψ).liftN 1 k = mT.acval n ψ)
    (h2 : FvarList D as2) (h : WalkCtx V mT φ D ρfull Δa as2)
    {e : Expr} (hleaf : ∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2 ∈ as2) :
    CtxOk mT φ D Δa e := by
  obtain ⟨hlen, -, hdoms, hok, -, -, -⟩ := h
  have hrev : ∀ (i : Nat), i < D → as2.reverse[i]? = as2[D - 1 - i]? := by
    intro i hi
    rw [List.getElem?_reverse (by rw [h2.1]; omega), h2.1]
  refine ctxOk_of_openers hacl (fvs := as2.reverse) (n := D)
    (Aa := fun i => Δa.getD (D - 1 - i) default) hlen h2.reverse_idx ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hx
    exact h2.2.2 x (List.mem_reverse.mp hx)
  · intro i x hx
    have hi : i < D := by
      have := (List.getElem?_eq_some_iff.mp hx).1
      rw [h2.reverse_length] at this
      exact this
    rw [hrev i hi] at hx
    have := hdoms (D - 1 - i) x hx
    rw [show D - 1 - (D - 1 - i) = i from by omega] at this
    exact this
  · intro l hl
    exact List.mem_reverse.mpr (hleaf l hl)
  · intro l hl
    obtain ⟨p, hp⟩ := List.getElem?_of_mem (List.mem_reverse.mpr (hleaf l hl))
    obtain ⟨ty, hty⟩ := h2.reverse_idx p _ hp
    have hpl : p < D := by
      have := (List.getElem?_eq_some_iff.mp hp).1
      rw [h2.reverse_length] at this
      exact this
    obtain ⟨h1', -⟩ : l.1 = p ∧ l.2 = ty := by
      injection hty with a b
      exact ⟨a, b⟩
    omega
  · intro i hi
    rw [List.getD, List.getElem?_eq_getElem (by rw [hlen]; omega)]
    rfl
  · intro i hi ρ hρ
    exact hok (D - 1 - i) (by omega) ρ hρ

/-- Bulk instantiation distributes over an application spine. -/
theorem instantiateList_mkAppN :
    ∀ (as : List Expr) (f : Expr) (xs : List Expr) (k : Nat),
      (Expr.mkAppN f as).instantiateList xs k
        = Expr.mkAppN (f.instantiateList xs k) (as.map (·.instantiateList xs k))
  | [], _, _, _ => rfl
  | a :: as, f, xs, k => by
    show (Expr.mkAppN (.app f a) as).instantiateList xs k = _
    rw [instantiateList_mkAppN as (.app f a) xs k, Expr.instantiateList]
    rfl

variable {V : Type uv} [SetTheory V]

/-! ## The peel, transported to the OPENED frame

`denoteMeta_instPisAtLift_peel` (`BlockRecRead.lean`) reads an
`instPisAtLift` at bvar-CLOSED arguments — which the call's arguments
are once the rule body is opened, and are NOT before.  The check's
`instPisAtLift as … = some expected` is a fact about
the UNOPENED terms, so it has to be transported, and the per-binder
commutation that does it already exists:
`Expr.instSeq_instantiate1Lift` (`Verify/Subst.lean`) — "a
capture-avoiding substitution followed by the ambient spine is the
plain substitution at the already-instantiated argument".  Three small
lemmas turn it into the statement `instPisAtLift` needs. -/

/-! ## The peel, evaluated

`AnnotTerm.peelPis` of a `mkPisAV` tower along a spine of its own
length is the body's instantiation sequence
(`peelPis_of_piTeleAV` at `piTeleAV_mkPisAV`), and `interp_instSeq`
evaluates that at the chain — which IS `consList` of the spine's
values, since `chain` is `consN` of them and `consN` is `consList`
(`consN_eq_consList`).  So the whole peel is one `interp` equation. -/

theorem chain_eq_consList (ρ : Nat → V) (ws : List AnnotTerm) :
    chain V ρ ws = consList (ws.map (interp V ρ)) ρ :=
  consN_eq_consList _ _

end ConLeche.Model
