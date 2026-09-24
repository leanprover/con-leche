module

public import ConLeche.Model.IndFrame
import ConLeche.Model.IndSubst
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Claims
import ConLeche.Model.WellDenotedTransport

public section

/-!
# The container copy's transport (the nested design's risk 1)

DESIGN DOCUMENT 2 §2.3/§2.4 needs, for a container `C` whose stored
constructor type `E` is instantiated at the pins `Ds` (a syntactic
substitution of `C`'s parameters) and then normalised (the positivity function's normal form)
and re-checked at the block's opened frame, that

> the reading of the normalised copy at the frame equals the reading
> of `E` at the frame where `C`'s parameters take the *readings* of
> the pins.

The maintainer's question — "is it not enough to know that whnf
preserves interpretation?" — asks whether that decomposes into

* **(a) the substitution law of the reading**: reading `E[params :=
  Ds]` at `ρ` is reading `E` opened at parameter variables, at `ρ`
  extended by the pins' readings; and
* **(b) reduction preserves the reading** at the frame, certified by
  the run.

It does.  This file proves **(a)** in general — `instPisAt_denoteMeta_open`
and its two corollaries — and composes it with **(b)** taken in the
exact shape the run's claim consumers produce (`copyRead_transport`,
`copyRead_transport_defEq`).

## What (a) says, exactly

The two sides are the two ways the checker and the model see one
telescope:

* the **copy** is `Expr.instPisAt Ds E`, the parameter binders
  instantiated at the pins, read at the block's frame depth `d`;
* the **stored** side is `openPisAtFvars Ds.length E d`, the same
  binders opened at fresh variables, read at depth `d + Ds.length` —
  which is how `BlockCtorDataI.domRead` reads every stored
  constructor.

`denoteMeta` turns the opened variables into the *innermost*
de Bruijn slots (variable `d + j` becomes `.bvar (n - 1 - j)` at depth
`d + n`), so the two readings differ by exactly one
`AnnotTerm.instSeq` — outermost pin first, at descending cuts, which
is `AnnotTerm.instSeq`'s own convention (`IndFrame.lean`).  At the
values, `interp_instSeq` turns that into the valuation `chain V ρ ws`:
the frame `ρ` with the parameter slots holding the pins' readings.
That is the statement §2.4 calls `interp (E.instParams Ds) (ρ, …) =
interp E (ρ[params := ⟦Ds⟧])`.

The induction carries an accumulator `vs` of the pins already
consumed, because the copy's reading stays at depth `d` while the
opened side's depth grows with each binder; `vs = []` is the entry
point (`instPisAt_denoteMeta_pins`).

## What (b) must supply, and in what shape

`DefEqClaim`/`WhnfClaim` (`Model/Claims.lean`) deliver

```
∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ aa = interp V ρ ba
```

— an equality of readings **at every valuation that satisfies the
context `Δa`**, not at every valuation.  `copyRead_transport` takes it
in precisely that form and hands back the composite at the same
quantifier, so a consumer never sees a valuation the claim does not
cover.  See the report of lane P8 for what that costs the nested
design (the holes must range over the *family space*, which is exactly
what `Sat` gives at a hole of type `Π ı⃗, Sort w`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name BinderMeta openPisAtFvars)

universe w

variable {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → AnnotTerm}

/-! ## Two `instSeq` shape lemmas -/

/-- `instSeq` splits along an append: the left block is consumed
first, at the given cut, and the right block continues at the cut the
left block left behind. -/
theorem instSeqAV_append :
    ∀ (vs ws : List AnnotTerm) (t : Nat) (e : AnnotTerm),
      ConLeche.Model.AnnotTerm.instSeq (vs ++ ws) t e
        = ConLeche.Model.AnnotTerm.instSeq ws (t - vs.length)
            (ConLeche.Model.AnnotTerm.instSeq vs t e) := by
  intro vs
  induction vs with
  | nil => intro ws t e; simp
  | cons v vs ih =>
    intro ws t e
    rw [List.cons_append, AnnotTerm.instSeq_cons, ih, AnnotTerm.instSeq_cons,
      show t - 1 - vs.length = t - (v :: vs).length from by
        simp only [List.length_cons]; omega]

/-- The cut `vs.length - 1` and the cut `vs.length` agree one binder
in: at a non-empty block the two are the same numeral, at the empty
block `instSeq` reads no cut at all. -/
theorem instSeqAV_cut_succ (vs : List AnnotTerm) (e : AnnotTerm) :
    ConLeche.Model.AnnotTerm.instSeq vs (vs.length - 1 + 1) e
      = ConLeche.Model.AnnotTerm.instSeq vs vs.length e := by
  cases vs with
  | nil => rfl
  | cons v vs =>
    rw [show (v :: vs).length - 1 + 1 = (v :: vs).length from by
      simp only [List.length_cons]; omega]

/-! ## (a) The substitution law over a parameter telescope -/

set_option maxHeartbeats 1000000 in
/-- **The copy transport, reading half** (leg (a) of the
decomposition).  A `∀`-telescope instantiated at the pins `Ds` and
read at the frame depth `d` is the same telescope *opened* at fresh
variables and read at depth `d + Ds.length`, with the pins' readings
substituted along `AnnotTerm.instSeq`.

The accumulator `vs` holds the pins already consumed (the entry point
is `vs = []`, `instPisAt_denoteMeta_pins`); `To` is the opened side's
reading at the current stage, which the recursion propagates so that
no definedness premise has to be guessed. -/
theorem instPisAt_denoteMeta_open
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AnnotTerm) (k : Nat),
      (acval n ψ).inst y k = acval n ψ) :
    ∀ (Ds : List Expr) {Es Eo : Expr} {dss dso : List Expr} {rss rso : Expr}
      {d : Nat} {vs ws : List AnnotTerm} {To : AnnotTerm},
      Expr.instPisAt Ds Es = some (dss, rss) →
      openPisAtFvars Ds.length Eo (d + vs.length) = some (dso, rso) →
      Expr.fvarsBelow d Es →
      (∀ (j : Nat) (a : Expr), Ds[j]? = some a →
        Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true) →
      ws.length = Ds.length →
      (∀ (j : Nat) (a : Expr), Ds[j]? = some a →
        ∃ w, denoteMeta acval env φ d a = some w ∧ ws[j]? = some w) →
      denoteMeta acval env φ (d + vs.length) Eo = some To →
      denoteMeta acval env φ d Es
        = some (ConLeche.Model.AnnotTerm.instSeq vs (vs.length - 1) To) →
      ∃ Ro, denoteMeta acval env φ (d + (vs ++ ws).length) rso = some Ro ∧
        denoteMeta acval env φ d rss
          = some (ConLeche.Model.AnnotTerm.instSeq (vs ++ ws)
              ((vs ++ ws).length - 1) Ro) := by
  intro Ds
  induction Ds with
  | nil =>
    intro Es Eo dss dso rss rso d vs ws To hinst hopen _ _ hwslen _ hEo hEs
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at hinst
    obtain ⟨_, rfl⟩ := hinst
    obtain rfl : ws = [] := List.eq_nil_of_length_eq_zero (by simpa using hwslen)
    simp only [List.length_nil, openPisAtFvars, Option.some.injEq,
      Prod.mk.injEq] at hopen
    obtain ⟨_, rfl⟩ := hopen
    exact ⟨To, by simpa using hEo, by simpa using hEs⟩
  | cons a Ds ih =>
    intro Es Eo dss dso rss rso d vs ws To hinst hopen hfb hsc hwslen hwsr hEo hEs
    -- the spine's head reads
    obtain ⟨hwsa, hba⟩ := hsc 0 a rfl
    obtain ⟨w, hw, hws0⟩ := hwsr 0 a rfl
    -- hence `ws` is a cons
    obtain ⟨ws', rfl⟩ : ∃ ws', ws = w :: ws' := by
      cases ws with
      | nil => exact absurd hws0 (by simp)
      | cons w0 ws' =>
        refine ⟨ws', ?_⟩
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hws0
        rw [hws0]
    have hws'len : ws'.length = Ds.length := by
      simpa using hwslen
    rw [List.length_cons] at hopen
    match Es, hinst, hfb with
    | .forallE doms bodys ms, hinst, hfb => ?_
    match Eo, hopen, hEo with
    | .forallE domo bodyo mo, hopen, hEo => ?_
    have hfb' : Expr.fvarsBelow d doms ∧ Expr.fvarsBelow d bodys := hfb
    -- the substituted side's recursion
    rw [Expr.instPisAt] at hinst
    cases h1 : Expr.instPisAt Ds (bodys.instantiate1 a) with
    | none => rw [h1] at hinst; exact nomatch hinst
    | some p => ?_
    obtain ⟨dss', rss'⟩ := p
    rw [h1] at hinst
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hinst
    obtain ⟨_, rfl⟩ := hinst
    -- the opened side's recursion
    simp only [openPisAtFvars] at hopen
    cases h2 : openPisAtFvars Ds.length
        (bodyo.instantiate1 (.fvar (d + vs.length) domo))
        (d + vs.length + 1) with
    | none => rw [h2] at hopen; exact nomatch hopen
    | some q => ?_
    obtain ⟨dso', rso'⟩ := q
    rw [h2] at hopen
    simp only [Option.some.injEq, Prod.mk.injEq] at hopen
    obtain ⟨_, rfl⟩ := hopen
    -- the two readings, decomposed at the binder
    obtain ⟨Ao, Bo, _, hBo, rfl⟩ := denoteMeta_forallE_inv hEo
    obtain ⟨As, Bs, _, hBs, hpi⟩ := denoteMeta_forallE_inv hEs
    rw [instSeqAV_pi vs (vs.length - 1) 0 (pwBit φ mo.pw) Ao Bo (by omega),
      instSeqAV_cut_succ] at hpi
    obtain ⟨_, _, _, rfl⟩ : (0 : Nat) = 0 ∧ pwBit φ mo.pw = pwBit φ ms.pw ∧
        ConLeche.Model.AnnotTerm.instSeq vs (vs.length - 1) Ao = As ∧
        ConLeche.Model.AnnotTerm.instSeq vs vs.length Bo = Bs := by
      simpa [AnnotTerm.pi.injEq, eq_comm] using hpi
    -- one step of the substitution law
    have happ : ConLeche.Model.AnnotTerm.instSeq (vs ++ [w])
          ((vs ++ [w]).length - 1) Bo
        = (ConLeche.Model.AnnotTerm.instSeq vs vs.length Bo).inst w 0 := by
      rw [show (vs ++ [w]).length - 1 = vs.length from by
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega,
        instSeqAV_append vs [w] vs.length Bo, Nat.sub_self]
      rfl
    have hstep : denoteMeta acval env φ d (bodys.instantiate1 a)
        = some (ConLeche.Model.AnnotTerm.instSeq (vs ++ [w])
            ((vs ++ [w]).length - 1) Bo) := by
      rw [denoteMeta_beta hacl hainst (ty := doms) hfb'.2 hwsa hba hw 0, hBs,
        happ, Option.map_some]
    -- the inductive step
    have hIH := ih (Es := bodys.instantiate1 a)
      (Eo := bodyo.instantiate1 (.fvar (d + vs.length) domo))
      (d := d) (vs := vs ++ [w]) (ws := ws') (To := Bo) h1
      (by simpa [Nat.add_assoc] using h2)
      (Expr.fvarsBelow_instantiate1_gen hwsa.fvarsBelow 0 hfb'.2)
      (fun j x hx => hsc (j + 1) x (by simpa using hx))
      hws'len
      (fun j x hx => hwsr (j + 1) x (by simpa using hx))
      (by simpa [Nat.add_assoc] using hBo) hstep
    obtain ⟨Ro, hRo, hrss⟩ := hIH
    refine ⟨Ro, ?_, ?_⟩
    · simpa using hRo
    · simpa using hrss

/-- **The entry point**: the copy's reading at the frame is the stored
telescope's opened reading with the pins' readings substituted. -/
theorem instPisAt_denoteMeta_pins
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AnnotTerm) (k : Nat),
      (acval n ψ).inst y k = acval n ψ)
    {Ds : List Expr} {E : Expr} {dss dso : List Expr} {rss rso : Expr}
    {d : Nat} {ws : List AnnotTerm} {To : AnnotTerm}
    (hinst : Expr.instPisAt Ds E = some (dss, rss))
    (hopen : openPisAtFvars Ds.length E d = some (dso, rso))
    (hfb : Expr.fvarsBelow d E)
    (hsc : ∀ (j : Nat) (a : Expr), Ds[j]? = some a →
      Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true)
    (hwslen : ws.length = Ds.length)
    (hwsr : ∀ (j : Nat) (a : Expr), Ds[j]? = some a →
      ∃ w, denoteMeta acval env φ d a = some w ∧ ws[j]? = some w)
    (hE : denoteMeta acval env φ d E = some To) :
    ∃ Ro, denoteMeta acval env φ (d + ws.length) rso = some Ro ∧
      denoteMeta acval env φ d rss
        = some (ConLeche.Model.AnnotTerm.instSeq ws (ws.length - 1) Ro) := by
  have h := instPisAt_denoteMeta_open (env := env) (φ := φ) hacl hainst Ds
    (Es := E) (Eo := E) (d := d) (vs := []) (ws := ws) (To := To) hinst
    (by simpa using hopen) hfb hsc hwslen hwsr (by simpa using hE)
    (by simpa using hE)
  simpa using h

/-! ## The field telescope, domain by domain

`instPisAt_denoteMeta_pins` relates the two *residuals*; the readings
`BlockCtorDataI.domRead` consumes are the residual telescope's field
DOMAINS, one per field, read at the field's own depth
(`denoteMeta … (nP + i) x.fvarTypeD`).  Opening both residuals at
field variables propagates the relation through the telescope: each Π
binder raises `instSeq`'s cut by one (`instSeqAV_pi`), and nothing
else moves — in particular no substitution happens here, so this half
needs neither `hainst` nor a scoping premise. -/

set_option maxHeartbeats 1000000 in
/-- **The copy transport through the field telescope.**  Two
`∀`-telescopes whose readings differ by `AnnotTerm.instSeq ws t` have
field domains that differ by `AnnotTerm.instSeq ws (t + j)` at field
`j`, and residuals that differ by `AnnotTerm.instSeq ws (t + nF)`. -/
theorem openPis_denoteMeta_transport :
    ∀ (nF : Nat) {As Bs : Expr} {xs xo : List Expr} {rsb rob : Expr}
      {d n t : Nat} {ws : List AnnotTerm} {Tb : AnnotTerm},
      ws.length ≤ t + 1 →
      openPisAtFvars nF As d = some (xs, rsb) →
      openPisAtFvars nF Bs (d + n) = some (xo, rob) →
      denoteMeta acval env φ (d + n) Bs = some Tb →
      denoteMeta acval env φ d As
        = some (ConLeche.Model.AnnotTerm.instSeq ws t Tb) →
      (∃ Rb, denoteMeta acval env φ (d + n + nF) rob = some Rb ∧
        denoteMeta acval env φ (d + nF) rsb
          = some (ConLeche.Model.AnnotTerm.instSeq ws (t + nF) Rb)) ∧
      (∀ (j : Nat) (xsj xoj : Expr), xs[j]? = some xsj → xo[j]? = some xoj →
        ∃ Ad, denoteMeta acval env φ (d + n + j) xoj.fvarTypeD = some Ad ∧
          denoteMeta acval env φ (d + j) xsj.fvarTypeD
            = some (ConLeche.Model.AnnotTerm.instSeq ws (t + j) Ad)) := by
  intro nF
  induction nF with
  | zero =>
    intro As Bs xs xo rsb rob d n t ws Tb _ hos hoo hB hA
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hos hoo
    obtain ⟨rfl, rfl⟩ := hos
    obtain ⟨rfl, rfl⟩ := hoo
    refine ⟨⟨Tb, by simpa using hB, by simpa using hA⟩, ?_⟩
    intro j xsj xoj hxs _
    exact absurd hxs (by simp)
  | succ nF ih =>
    intro As Bs xs xo rsb rob d n t ws Tb hwl hos hoo hB hA
    match As, hos, hA with
    | .forallE doms bodys ms, hos, hA => ?_
    match Bs, hoo, hB with
    | .forallE domo bodyo mo, hoo, hB => ?_
    simp only [openPisAtFvars] at hos hoo
    cases h1 : openPisAtFvars nF (bodys.instantiate1 (.fvar d doms)) (d + 1) with
    | none => rw [h1] at hos; exact nomatch hos
    | some p => ?_
    obtain ⟨xs', rsb'⟩ := p
    rw [h1] at hos
    simp only [Option.some.injEq, Prod.mk.injEq] at hos
    obtain ⟨rfl, rfl⟩ := hos
    cases h2 : openPisAtFvars nF (bodyo.instantiate1 (.fvar (d + n) domo)) (d + n + 1) with
    | none => rw [h2] at hoo; exact nomatch hoo
    | some q => ?_
    obtain ⟨xo', rob'⟩ := q
    rw [h2] at hoo
    simp only [Option.some.injEq, Prod.mk.injEq] at hoo
    obtain ⟨rfl, rfl⟩ := hoo
    obtain ⟨Ao, Bo, hAo, hBo, rfl⟩ := denoteMeta_forallE_inv hB
    obtain ⟨Aa, Ba, hAa, hBa, hpi⟩ := denoteMeta_forallE_inv hA
    rw [instSeqAV_pi ws t 0 (pwBit φ mo.pw) Ao Bo hwl] at hpi
    obtain ⟨_, _, hdom, hbody⟩ :
        (0 : Nat) = 0 ∧ pwBit φ mo.pw = pwBit φ ms.pw ∧
          ConLeche.Model.AnnotTerm.instSeq ws t Ao = Aa ∧
          ConLeche.Model.AnnotTerm.instSeq ws (t + 1) Bo = Ba := by
      simpa [AnnotTerm.pi.injEq, eq_comm] using hpi
    obtain ⟨hres, hdoms⟩ := ih (As := bodys.instantiate1 (.fvar d doms))
      (Bs := bodyo.instantiate1 (.fvar (d + n) domo))
      (d := d + 1) (n := n) (t := t + 1) (ws := ws) (Tb := Bo)
      (by omega) h1 (by simpa [Nat.add_right_comm] using h2)
      (by simpa [Nat.add_right_comm] using hBo)
      (by rw [hBa, hbody])
    refine ⟨?_, ?_⟩
    · obtain ⟨Rb, hRb, hrsb⟩ := hres
      refine ⟨Rb, by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hRb, ?_⟩
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hrsb
    · intro j xsj xoj hxs hxo
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hxs hxo
        subst hxs; subst hxo
        exact ⟨Ao, by simpa [ConLeche.Expr.fvarTypeD] using hAo,
          by simpa [ConLeche.Expr.fvarTypeD, hdom] using hAa⟩
      | succ j =>
        simp only [List.getElem?_cons_succ] at hxs hxo
        obtain ⟨Ad, hAd, hAs⟩ := hdoms j xsj xoj hxs hxo
        refine ⟨Ad, ?_, ?_⟩
        · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hAd
        · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hAs

/-- **The copy transport, in `domRead` currency** — the two halves
composed.  For a container constructor telescope `E` with `Ds.length`
parameters and `nF` fields, the copy's field domains (read at the
frame, field by field) are the stored constructor's opened field
domains with the pins' readings substituted, and so is the residual.

This is the shape `blockCtorData_of` (`BlockData.lean`) could consume:
its `domRead` clause is `denoteMeta m.acval env ψ (nP + i)
x.fvarTypeD = some ((ds ψ).getD (nP + i) default).2.2`, one reading
per opened field variable, which is exactly the second conjunct's
left-hand side at `d := nP`. -/
theorem copyTele_transport
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AnnotTerm) (k : Nat),
      (acval n ψ).inst y k = acval n ψ)
    {Ds : List Expr} {E : Expr} {dss dso : List Expr} {rss rso : Expr}
    {nF : Nat} {xs xo : List Expr} {rsb rob : Expr}
    {d : Nat} {ws : List AnnotTerm} {To : AnnotTerm}
    (hinst : Expr.instPisAt Ds E = some (dss, rss))
    (hopen : openPisAtFvars Ds.length E d = some (dso, rso))
    (hfb : Expr.fvarsBelow d E)
    (hsc : ∀ (j : Nat) (a : Expr), Ds[j]? = some a →
      Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true)
    (hwslen : ws.length = Ds.length)
    (hwsr : ∀ (j : Nat) (a : Expr), Ds[j]? = some a →
      ∃ w, denoteMeta acval env φ d a = some w ∧ ws[j]? = some w)
    (hE : denoteMeta acval env φ d E = some To)
    (hos : openPisAtFvars nF rss d = some (xs, rsb))
    (hoo : openPisAtFvars nF rso (d + ws.length) = some (xo, rob)) :
    (∃ Rb, denoteMeta acval env φ (d + ws.length + nF) rob = some Rb ∧
      denoteMeta acval env φ (d + nF) rsb
        = some (ConLeche.Model.AnnotTerm.instSeq ws (ws.length - 1 + nF) Rb)) ∧
    (∀ (j : Nat) (xsj xoj : Expr), xs[j]? = some xsj → xo[j]? = some xoj →
      ∃ Ad, denoteMeta acval env φ (d + ws.length + j) xoj.fvarTypeD = some Ad ∧
        denoteMeta acval env φ (d + j) xsj.fvarTypeD
          = some (ConLeche.Model.AnnotTerm.instSeq ws (ws.length - 1 + j) Ad)) := by
  obtain ⟨Ro, hRo, hrss⟩ := instPisAt_denoteMeta_pins (env := env) (φ := φ)
    hacl hainst hinst hopen hfb hsc hwslen hwsr hE
  exact openPis_denoteMeta_transport (env := env) (φ := φ) nF
    (n := ws.length) (t := ws.length - 1) (by omega) hos hoo hRo hrss

section Values
variable {V : Type w} [SetTheory V]

/-- **The copy transport at the values** (leg (a), the form §2.4
quotes): the copy's reading interpreted at the frame `ρ` is the stored
telescope's opened reading interpreted at `ρ` with the parameter slots
holding the pins' readings — `chain V ρ ws`. -/
theorem instPisAt_interp_pins
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AnnotTerm) (k : Nat),
      (acval n ψ).inst y k = acval n ψ)
    {Ds : List Expr} {E : Expr} {dss dso : List Expr} {rss rso : Expr}
    {d : Nat} {ws : List AnnotTerm} {To Rs : AnnotTerm}
    (hinst : Expr.instPisAt Ds E = some (dss, rss))
    (hopen : openPisAtFvars Ds.length E d = some (dso, rso))
    (hfb : Expr.fvarsBelow d E)
    (hsc : ∀ (j : Nat) (a : Expr), Ds[j]? = some a →
      Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true)
    (hwslen : ws.length = Ds.length)
    (hwsr : ∀ (j : Nat) (a : Expr), Ds[j]? = some a →
      ∃ w, denoteMeta acval env φ d a = some w ∧ ws[j]? = some w)
    (hE : denoteMeta acval env φ d E = some To)
    (hRs : denoteMeta acval env φ d rss = some Rs) :
    ∃ Ro, denoteMeta acval env φ (d + ws.length) rso = some Ro ∧
      ∀ ρ : Nat → V, interp V ρ Rs = interp V (chain V ρ ws) Ro := by
  obtain ⟨Ro, hRo, hrss⟩ := instPisAt_denoteMeta_pins (env := env) (φ := φ)
    hacl hainst hinst hopen hfb hsc hwslen hwsr hE
  refine ⟨Ro, hRo, fun ρ => ?_⟩
  rw [hRs] at hrss
  obtain rfl := Option.some.inj hrss
  exact interp_instSeq ws Ro ρ

/-! ## (a) composed with (b): the transport the nested lane consumes -/

/-- **THE TRANSPORT** (DESIGN DOCUMENT 2 §2.4, risk 1).  For a
container's stored constructor telescope `E`, pins `Ds`, and a
NORMALISED copy `Dnorm` of the substituted residual, the reading of
the normalised copy at the frame equals the reading of `E` opened at
parameter variables, at the frame extended by the pins' readings —
*at every valuation the run's claim covers*.

Leg (b) enters as `hclaim`, in exactly the shape `DefEqClaim` and
`WhnfClaim` (`Model/Claims.lean`) hand out: an equality of readings at
every `ρ` with `Sat V Δa ρ`.  Nothing else about the reduction is
used, which is the answer to "is it not enough to know that whnf
preserves interpretation?" — it is. -/
theorem copyRead_transport
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AnnotTerm) (k : Nat),
      (acval n ψ).inst y k = acval n ψ)
    {Ds : List Expr} {E : Expr} {dss dso : List Expr} {rss rso : Expr}
    {d : Nat} {ws : List AnnotTerm} {To Rs An : AnnotTerm}
    {Δa : List AnnotTerm}
    (hinst : Expr.instPisAt Ds E = some (dss, rss))
    (hopen : openPisAtFvars Ds.length E d = some (dso, rso))
    (hfb : Expr.fvarsBelow d E)
    (hsc : ∀ (j : Nat) (a : Expr), Ds[j]? = some a →
      Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true)
    (hwslen : ws.length = Ds.length)
    (hwsr : ∀ (j : Nat) (a : Expr), Ds[j]? = some a →
      ∃ w, denoteMeta acval env φ d a = some w ∧ ws[j]? = some w)
    (hE : denoteMeta acval env φ d E = some To)
    (hRs : denoteMeta acval env φ d rss = some Rs)
    (hclaim : ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ An = interp V ρ Rs) :
    ∃ Ro, denoteMeta acval env φ (d + ws.length) rso = some Ro ∧
      ∀ ρ : Nat → V, Sat V Δa ρ →
        interp V ρ An = interp V (chain V ρ ws) Ro := by
  obtain ⟨Ro, hRo, hval⟩ := instPisAt_interp_pins (V := V) (env := env) (φ := φ)
    hacl hainst hinst hopen hfb hsc hwslen hwsr hE hRs
  exact ⟨Ro, hRo, fun ρ hρ => (hclaim ρ hρ).trans (hval ρ)⟩

/-- `copyRead_transport` with leg (b) read off a **recorded `isDefEq`
run** through `DefEqClaim` — the shape a normalisation stage would hand
over if it recorded the comparison of the normalised domain against the
declared one.  (None does: the install stores constructors as declared
and ties the normal form to them through `red_sound`, lane ALPHA1; see
also the lane P8 report.) -/
theorem copyRead_transport_defEq {μ : CheckMode} {m : EnvModel V env}
    {F : Nat} (hclaims : DefEqClaim μ m φ F)
    {Ds : List Expr} {E : Expr} {dss dso : List Expr} {rss rso : Expr}
    {d : Nat} {ws : List AnnotTerm} {To Rs An : AnnotTerm}
    {Δa : List AnnotTerm} {Dnorm : Expr}
    (hrun : ConLeche.isDefEqCore μ env F d Dnorm rss = .ok true)
    (hwn : Expr.WScoped d Dnorm) (hbn : Dnorm.looseBVarsBounded 0 = true)
    (hln : Expr.LeavesBounded Dnorm)
    (hws : Expr.WScoped d rss) (hbs : rss.looseBVarsBounded 0 = true)
    (hls : Expr.LeavesBounded rss)
    (hctxn : CtxOk m φ d Δa Dnorm) (hctxs : CtxOk m φ d Δa rss)
    (hAn : denoteMeta m.acval env φ d Dnorm = some An)
    (hwdn : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ An)
    (hwds : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ Rs)
    (hinst : Expr.instPisAt Ds E = some (dss, rss))
    (hopen : openPisAtFvars Ds.length E d = some (dso, rso))
    (hfb : Expr.fvarsBelow d E)
    (hsc : ∀ (j : Nat) (a : Expr), Ds[j]? = some a →
      Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true)
    (hwslen : ws.length = Ds.length)
    (hwsr : ∀ (j : Nat) (a : Expr), Ds[j]? = some a →
      ∃ w, denoteMeta m.acval env φ d a = some w ∧ ws[j]? = some w)
    (hE : denoteMeta m.acval env φ d E = some To)
    (hRs : denoteMeta m.acval env φ d rss = some Rs) :
    ∃ Ro, denoteMeta m.acval env φ (d + ws.length) rso = some Ro ∧
      ∀ ρ : Nat → V, Sat V Δa ρ →
        interp V ρ An = interp V (chain V ρ ws) Ro :=
  copyRead_transport (V := V) (acval := m.acval) m.acval_closed
    (acval_inst_self m) hinst hopen hfb hsc hwslen hwsr hE hRs
    (fun ρ hρ => hclaims hrun hwn hbn hln hws hbs hls hctxn hctxs hAn hRs
      hwdn hwds ρ hρ)

end Values

end ConLeche.Model
