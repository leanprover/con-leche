module

-- The two `public import`s are FALLBACKS, each verified by a failing
-- demotion (task #315 M7-3 session 16): demoting `NestedPremise` loses
-- the `ConLeche.SetTheory` namespace this file `open`s, and demoting
-- `NestedRestoreOpen` loses `ConLeche.mkPisB`, which the dummy
-- telescope is built with.  Everything else here is a plain import.
public import ConLeche.Model.Inductives.NestedPremise
import ConLeche.Model.Inductives.NestedCopyRead
import ConLeche.Model.Inductives.StructFrames
import ConLeche.Model.Inductives.FixData
import ConLeche.Model.Steps.Stuck
import ConLeche.Model.Annot.BitErase
import ConLeche.Verify.EraseAnnots
import ConLeche.Verify.Denote.OpenVars
public import ConLeche.Verify.Inductives.NestedRestoreOpen
import ConLeche.Verify.Inductives.NestedCopyTele
import ConLeche.Verify.Inductives.NestedCopyInstU
import ConLeche.Verify.Inductives.NestedRecCtorPin
public section

/-!
# The own pins' components, read (task #315 M7-3, DESIGN §U.73 (b), (d))

`ContainerOwnPinsSyn` (`NestedPremise.lean`) is the SYNTACTIC field
`ContainerModeled.ownPins` carries: every own pin a stored container's
mimics spell is one of the block model's recorded pins, spelled at the
instantiation the reader was asked for (`PinSyn.ownAt`).  Its consumer
(`pinCorr_of_ownPins`) wants the READING form `ContainerOwnPins`, and
`ContainerOwnPinsSyn.toRead` bridges the two modulo ONE hypothesis
`hsub` — the substitution law "the reading of a recorded component,
closed, level-instantiated and re-opened at the outer components, is
`AnnotTerm.instAll` of the recorded reading at the substituted level
assignment".

This module PROVES that law (`denoteMeta_ownAt_component`, its spine
form `denoteMetaSpine_ownAt`) and re-states the bridge with `hsub`
discharged (`ContainerOwnPinsSyn.toReadOf`).

**The route.**  A recorded component `x` stands at the block's `nP`
parameter openers, so closing it (`Expr.abstractRange x 0 nP 0`) and
re-opening it at `nP` arguments is the peel of a `∀`-tower with `nP`
binders whose domains nothing reads.  So wrap the closed component in
`nP` DUMMY binders (`dummyPis`, all `Sort 0`): the wrapped term `T` is
CLOSED, `instPis_ilp_mkPisB` (lane L-B) turns its level-instantiated
`instPis` into exactly the spelled component, `denoteMeta` on a `∀`
already reads its body opened at the binder's own variable — so `T`
reads as the tower over the component's own recorded reading — and
`instPisILP_read` (`NestedCopyRead.lean`) reads the instantiated
telescope off the closed one.  At `|Ds| = nP` the residual tower is
empty and `AnnotTerm.instAll Ds 0` is what is left.

This file sits above `NestedPremise.lean` because `instPisILP_read`
does: `NestedCopyRead.lean` reaches the premise module and not
conversely.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## The dummy telescope -/

/-- **The `n` binders nothing reads**: the wrapper that turns a CLOSED
component into a `∀`-tower `instPis` can peel.  The domains are `Sort
0` — closed, so the whole tower is closed as soon as the body is, and
`denoteMeta` plants `Expr.fvar d (.sort .zero)` for them, which is
`Verify.openFvars`' opener on the nose. -/
def dummyPis : Nat → List (Expr × ConLeche.BinderMeta)
  | 0 => []
  | n + 1 => (Expr.sort Level.zero, default) :: dummyPis n

theorem dummyPis_length : ∀ n : Nat, (dummyPis n).length = n
  | 0 => rfl
  | n + 1 => by
    show ((Expr.sort Level.zero, (default : ConLeche.BinderMeta)) :: dummyPis n).length = n + 1
    rw [List.length_cons, dummyPis_length n]

/-- **The dummy telescope under an instantiation**: the domains are
closed, so only the body moves — and it moves to the cut below the
whole telescope. -/
theorem mkPisB_dummyPis_instantiate1 (v : Expr) : ∀ (n j : Nat) (y : Expr),
    (ConLeche.mkPisB (dummyPis n) y).instantiate1 v j
      = ConLeche.mkPisB (dummyPis n) (y.instantiate1 v (j + n))
  | 0, j, y => by
    show (ConLeche.mkPisB [] y).instantiate1 v j
      = ConLeche.mkPisB [] (y.instantiate1 v (j + 0))
    rw [ConLeche.mkPisB_nil, ConLeche.mkPisB_nil, Nat.add_zero]
  | n + 1, j, y => by
    show (ConLeche.mkPisB ((Expr.sort Level.zero, (default : ConLeche.BinderMeta))
      :: dummyPis n) y).instantiate1 v j
      = ConLeche.mkPisB ((Expr.sort Level.zero, (default : ConLeche.BinderMeta))
          :: dummyPis n) (y.instantiate1 v (j + (n + 1)))
    rw [ConLeche.mkPisB_cons, ConLeche.mkPisB_cons]
    show Expr.forallE ((Expr.sort Level.zero).instantiate1 v j)
        ((ConLeche.mkPisB (dummyPis n) y).instantiate1 v (j + 1)) default = _
    rw [mkPisB_dummyPis_instantiate1 v n (j + 1) y,
      show j + 1 + n = j + (n + 1) from by omega]
    rfl

/-- The wrapper adds no free variable. -/
theorem hasFvar_mkPisB_dummyPis : ∀ (n : Nat) (y : Expr),
    (ConLeche.mkPisB (dummyPis n) y).hasFvar = y.hasFvar
  | 0, _ => rfl
  | n + 1, y => by
    show (ConLeche.mkPisB ((Expr.sort Level.zero, (default : ConLeche.BinderMeta))
      :: dummyPis n) y).hasFvar = y.hasFvar
    rw [ConLeche.mkPisB_cons]
    simp only [Expr.hasFvar, Bool.false_or]
    exact hasFvar_mkPisB_dummyPis n y

/-- The wrapper absorbs `n` loose bound variables. -/
theorem looseBVarsBounded_mkPisB_dummyPis : ∀ (n d : Nat) (y : Expr),
    y.looseBVarsBounded (d + n) = true →
      (ConLeche.mkPisB (dummyPis n) y).looseBVarsBounded d = true
  | 0, d, y, h => by
    show (ConLeche.mkPisB [] y).looseBVarsBounded d = true
    rw [ConLeche.mkPisB_nil]; simpa using h
  | n + 1, d, y, h => by
    show (ConLeche.mkPisB ((Expr.sort Level.zero, (default : ConLeche.BinderMeta))
      :: dummyPis n) y).looseBVarsBounded d = true
    rw [ConLeche.mkPisB_cons]
    simp only [Expr.looseBVarsBounded, Bool.true_and]
    exact looseBVarsBounded_mkPisB_dummyPis n (d + 1) y
      (by rw [show d + 1 + n = d + (n + 1) from by omega]; exact h)

/-- **A component closed at the parameters is `fvar`-free**:
`Expr.abstractRange e 0 k c` replaces exactly the `fvar`s with index in
`[0, k)` — and it is annotation-blind, so a leaf below the range leaves
nothing behind. -/
theorem hasFvar_abstractRange_of_leaves : ∀ (e : Expr) (k c : Nat),
    (∀ l ∈ e.fvarLeaves, l.1 < k) → (e.abstractRange 0 k c).hasFvar = false := by
  intro e
  induction e with
  | bvar i => intro _ _ _; rfl
  | sort u => intro _ _ _; rfl
  | const n us => intro _ _ _; rfl
  | lit l => intro _ _ _; rfl
  | fvar idx ty _ =>
    intro k c h
    have hlt : idx < k := h (idx, ty) (by simp [Expr.fvarLeaves])
    rw [Expr.abstractRange, if_pos (by omega)]
    rfl
  | app f a ihf iha =>
    intro k c h
    simp only [Expr.abstractRange, Expr.hasFvar, Bool.or_eq_false_iff]
    exact ⟨ihf k c fun l hl => h l (by simp [Expr.fvarLeaves, hl]),
      iha k c fun l hl => h l (by simp [Expr.fvarLeaves, hl])⟩
  | lam ty b m ihty ihb =>
    intro k c h
    simp only [Expr.abstractRange, Expr.hasFvar, Bool.or_eq_false_iff]
    exact ⟨ihty k c fun l hl => h l (by simp [Expr.fvarLeaves, hl]),
      ihb k (c + 1) fun l hl => h l (by simp [Expr.fvarLeaves, hl])⟩
  | forallE ty b m ihty ihb =>
    intro k c h
    simp only [Expr.abstractRange, Expr.hasFvar, Bool.or_eq_false_iff]
    exact ⟨ihty k c fun l hl => h l (by simp [Expr.fvarLeaves, hl]),
      ihb k (c + 1) fun l hl => h l (by simp [Expr.fvarLeaves, hl])⟩
  | letE ty v b ihty ihv ihb =>
    intro k c h
    simp only [Expr.abstractRange, Expr.hasFvar, Bool.or_eq_false_iff]
    refine ⟨⟨ihty k c fun l hl => h l (by simp [Expr.fvarLeaves, hl]),
      ihv k c fun l hl => h l (by simp [Expr.fvarLeaves, hl])⟩,
      ihb k (c + 1) fun l hl => h l (by simp [Expr.fvarLeaves, hl])⟩
  | proj s i x ih =>
    intro k c h
    simp only [Expr.abstractRange, Expr.hasFvar]
    exact ih k c fun l hl => h l (by simp [Expr.fvarLeaves, hl])

/-! ## The dummy telescope, read -/

/-- **The dummy tower reads as a tower over its body's OPENED
reading**: `denoteMeta` on a `∀` already reads the body opened at the
binder's own variable one depth up, and the dummy domains plant exactly
`Verify.openFvars`' openers, so the `n` opening steps of the walk
compose into the one `Expr.instSeq`.  The binder data are not named:
every consumer drops them. -/
theorem denoteMeta_mkPisB_dummyPis {acval : Name → (Name → Nat) → AnnotTerm}
    {φ : Name → Nat} : ∀ (n d : Nat) (y : Expr) (r : AnnotTerm),
      denoteMeta acval env φ (d + n)
          (Expr.instSeq (Verify.openFvars d n) (n - 1) y) = some r →
      ∃ pps : List (Nat × Nat × AnnotTerm), pps.length = n ∧
        denoteMeta acval env φ d (ConLeche.mkPisB (dummyPis n) y) = some (mkPisAV pps r)
  | 0, _, _, _, h => ⟨[], rfl, h⟩
  | n + 1, d, y, r, h => by
    have hop : Expr.instSeq (Verify.openFvars d (n + 1)) (n + 1 - 1) y
        = Expr.instSeq (Verify.openFvars (d + 1) n) (n - 1)
            (y.instantiate1 (Expr.fvar d (.sort .zero)) n) := by
      rw [Verify.openFvars_succ]
      rfl
    rw [hop, show d + (n + 1) = d + 1 + n from by omega] at h
    obtain ⟨pps, hlen, hpps⟩ :=
      denoteMeta_mkPisB_dummyPis n (d + 1) (y.instantiate1 (Expr.fvar d (.sort .zero)) n) r h
    refine ⟨(0, pwBit φ (default : ConLeche.BinderMeta).pw,
      .sort (Level.eval φ Level.zero)) :: pps, by rw [List.length_cons, hlen], ?_⟩
    have hbody : (ConLeche.mkPisB (dummyPis n) y).instantiate1 (Expr.fvar d (.sort .zero))
        = ConLeche.mkPisB (dummyPis n) (y.instantiate1 (Expr.fvar d (.sort .zero)) n) := by
      rw [mkPisB_dummyPis_instantiate1, Nat.zero_add]
    show denoteMeta acval env φ d (ConLeche.mkPisB
      ((Expr.sort Level.zero, (default : ConLeche.BinderMeta)) :: dummyPis n) y) = _
    rw [ConLeche.mkPisB_cons, denoteMeta_forallE, denoteMeta_sort, hbody, hpps]
    rfl

/-! ## THE SUBSTITUTION LAW -/

/-- **A RECORDED COMPONENT, SPELLED AT ANOTHER INSTANTIATION, READS AS
ITS RECORDED READING INSTANTIATED** (task #315 M7-3, DESIGN §U.73 (b),
(d)) — the law `ContainerOwnPinsSyn.toRead` carries as `hsub`.

`x` is a pin component AT THE BLOCK'S OWN PARAMETER OPENERS, which is
why it is read at depth `nP` (`hread`); `params` are those openers
(K.30's `pinsScoped`), which is what `hidx`/`hplen`/`hxlv` say.
`PinSyn.ownAt`'s spelling closes it, substitutes the level arguments
and re-opens it at the components `DsE` the reader was asked for, and
the claim is that this reads as the recorded reading with the outer
components' readings substituted — `PinCorr`'s own `AnnotTerm.instAll
Ds 0`.

The proof wraps the closed component in `nP` dummy binders so that the
re-opening becomes an `instPis` of a CLOSED type (`instPis_ilp_mkPisB`,
lane L-B) and `instPisILP_read` applies; the tower's own reading is
`denoteMeta_mkPisB_dummyPis`, whose body step is the open/close round
trip (`eraseAnnots_openAbstract`, which absorbs the annotation
mismatch between the dummy openers and the recorded ones — the
interpretation never reads an `fvar`'s annotation). -/
theorem denoteMeta_ownAt_component {env : Env} (m : EnvModel V env) {ψ : Name → Nat}
    {lps : List Name} {lvls : List Level} {nP dp : Nat}
    {params DsE : List Expr} {Ds : List AnnotTerm} {x : Expr} {rx : AnnotTerm}
    (hplen : params.length = nP)
    (hidx : ∀ j, j < nP → ∃ ty, params[j]? = some (Expr.fvar j ty))
    (hxb : x.looseBVarsBounded 0 = true)
    (hxlv : ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ params)
    (hDlen : DsE.length = nP)
    (hDs : ∀ a ∈ DsE, Expr.WScoped dp a ∧ a.looseBVarsBounded 0 = true)
    (hspine : DenoteMetaSpine m.acval env ψ dp DsE Ds)
    (hread : denoteMeta m.acval env (Level.substFn ψ lps lvls) nP x = some rx) :
    denoteMeta m.acval env ψ dp
        (Expr.instSeq DsE (DsE.length - 1)
          ((Expr.abstractRange x 0 nP 0).instantiateLevelParams lps lvls))
      = some (AnnotTerm.instAll Ds 0 rx) := by
  -- the leaves of `x` are the openers, hence below `nP`
  have hlt : ∀ l ∈ x.fvarLeaves, l.1 < nP := by
    intro l hl
    obtain ⟨i, hi⟩ := List.getElem?_of_mem (hxlv l hl)
    have hilt : i < nP := by
      have : i < params.length := by
        rcases Nat.lt_or_ge i params.length with h | h
        · exact h
        · rw [List.getElem?_eq_none h] at hi; exact nomatch hi
      omega
    obtain ⟨tyi, htyi⟩ := hidx i hilt
    rw [hi] at htyi
    have : l.1 = i := by simpa using (by simpa using htyi : l.1 = i ∧ l.2 = tyi).1
    omega
  -- the closed component, wrapped in `nP` dummy binders
  have hycl : (Expr.abstractRange x 0 nP 0).hasFvar = false :=
    hasFvar_abstractRange_of_leaves x nP 0 hlt
  have hTcl : (ConLeche.mkPisB (dummyPis nP) (Expr.abstractRange x 0 nP 0)).hasFvar = false := by
    rw [hasFvar_mkPisB_dummyPis]; exact hycl
  have hTb : (ConLeche.mkPisB (dummyPis nP) (Expr.abstractRange x 0 nP 0)).looseBVarsBounded 0
      = true :=
    looseBVarsBounded_mkPisB_dummyPis nP 0 _
      (by simpa using ConLeche.looseBVarsBounded_abstractRange x 0 nP 0 hxb)
  -- the tower's reading: its opened body is `x` up to annotations
  have hbodyRead : denoteMeta m.acval env (Level.substFn ψ lps lvls) (0 + nP)
      (Expr.instSeq (Verify.openFvars 0 nP) (nP - 1) (Expr.abstractRange x 0 nP 0))
        = some rx := by
    rw [Nat.zero_add, denoteMeta_congr_eraseAnnots (φ := Level.substFn ψ lps lvls) nP _ x
      (Expr.eraseAnnots_openAbstract x hxb (Verify.openFvars 0 nP) (Verify.openFvars_length 0 nP)
        (fun k hk => ⟨.sort .zero, by
          simpa using Verify.openFvars_getElem? (d := 0) (k := nP) (i := k) hk⟩))]
    exact hread
  obtain ⟨pps, hppsLen, hT⟩ :=
    denoteMeta_mkPisB_dummyPis (acval := m.acval) (φ := Level.substFn ψ lps lvls)
      nP 0 (Expr.abstractRange x 0 nP 0) rx hbodyRead
  obtain ⟨hbelow, hC⟩ := bvarsBelow_mkPisAV_inv
    (bvarsBelow_of_reading (m := m) (Expr.WScoped.of_not_hasFvar hTcl) hTb hT)
  rw [Nat.zero_add] at hC
  -- the syntactic step
  have hinst : Expr.instPis (Expr.instantiateLevelParams lps lvls
      (ConLeche.mkPisB (dummyPis nP) (Expr.abstractRange x 0 nP 0))) DsE
      = some (Expr.instSeq DsE (DsE.length - 1)
          (Expr.instantiateLevelParams lps lvls (Expr.abstractRange x 0 nP 0))) := by
    have h := ConLeche.instPis_ilp_mkPisB lps lvls DsE (dummyPis nP) []
      (Expr.abstractRange x 0 nP 0) (by rw [dummyPis_length, hDlen])
    simpa only [List.append_nil, List.map_nil, ConLeche.instTeleSeq, ConLeche.mkPisB,
      List.length_nil, Nat.add_zero] using h
  have hDsLen : Ds.length = nP := by rw [← hspine.length, hDlen]
  have hres := instPisILP_read m hTcl (ks := lps) (us := lvls) rfl hT hbelow hC
    (by rw [hDsLen, hppsLen]; omega) hDs hspine hinst
  have hdrop : pps.drop Ds.length = [] := by rw [hDsLen, ← hppsLen]; simp
  rw [hres, hdrop, hppsLen, hDsLen, Nat.sub_self,
    show instTeleP Ds 0 ([] : List (Nat × Nat × AnnotTerm)) = [] from
      List.eq_nil_of_length_eq_zero (by rw [instTeleP_length]; rfl)]
  rfl

/-! ## The spine, and the bridge with its law discharged -/

/-- **A PIN'S COMPONENTS, SPELLED AT ANOTHER INSTANTIATION, READ AS ITS
RECORDED READINGS INSTANTIATED** (task #315 M7-3): the list form of
`denoteMeta_ownAt_component`, which is the shape `PinSyn.ownAt` puts
the components in and `PinCorr`'s `Ds` clause wants them in. -/
theorem denoteMetaSpine_ownAt {env : Env} (m : EnvModel V env) {ψ : Name → Nat}
    {lps : List Name} {lvls : List Level} {nP dp : Nat}
    {params DsE : List Expr} {Ds : List AnnotTerm}
    (hplen : params.length = nP)
    (hidx : ∀ j, j < nP → ∃ ty, params[j]? = some (Expr.fvar j ty))
    (hDlen : DsE.length = nP)
    (hDs : ∀ a ∈ DsE, Expr.WScoped dp a ∧ a.looseBVarsBounded 0 = true)
    (hspine : DenoteMetaSpine m.acval env ψ dp DsE Ds) :
    ∀ {xs : List Expr} {rxs : List AnnotTerm},
      DenoteMetaSpine m.acval env (Level.substFn ψ lps lvls) nP xs rxs →
      (∀ x ∈ xs, x.looseBVarsBounded 0 = true) →
      (∀ x ∈ xs, ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ params) →
      DenoteMetaSpine m.acval env ψ dp
        (xs.map fun x => Expr.instSeq DsE (DsE.length - 1)
          ((Expr.abstractRange x 0 nP 0).instantiateLevelParams lps lvls))
        (rxs.map (AnnotTerm.instAll Ds 0)) := by
  intro xs rxs h
  induction h with
  | nil => intro _ _; exact .nil
  | @cons a v as vs ha _ ih =>
    intro hb hl
    rw [List.map_cons, List.map_cons]
    exact .cons (denoteMeta_ownAt_component m hplen hidx (hb a (by simp))
        (hl a (by simp)) hDlen hDs hspine ha)
      (ih (fun x hx => hb x (by simp [hx])) (fun x hx => hl x (by simp [hx])))

/-- **THE SYNTACTIC CLAUSE GIVES THE READING ONE, UNCONDITIONALLY**
(task #315 M7-3, DESIGN §U.73 (b), (d)): `ContainerOwnPinsSyn.toRead`
with its `hsub` — the substitution law — DISCHARGED by
`denoteMetaSpine_ownAt`.  What is left are facts about the block's OWN
pins and about the components the reader was asked for, all of them the
run's:

* `hscope` is K.30 (`pinsScoped`): the block's parameter openers exist
  and every recorded pin component stands at them, with no loose bound
  variable;
* `hpinDs` is `NestedStageFacts.pinDs` (`ContainerModeled`'s twin at a
  stored container): a pin's recorded components read, at the block's
  parameter depth, as its recorded readings;
* `hDsE` is what the READER's answer says about the components it was
  asked for — they are the container's parameters in number, and they
  are scoped at the depth the outer spine reads at.  It is quantified
  exactly like `ContainerOwnPins` itself, because the scoping depth
  `dp` is bound there.

`hDsE`'s scoping half is not in §U.73 (d)'s list: `instPisILP_read`
needs it (its `hDs`), and nothing in `ContainerOwnPins`' own premises
implies it. -/
theorem ContainerOwnPinsSyn.toReadOf {env : Env} {m : EnvModel V env} {d : BlockModel V}
    (hsyn : ContainerOwnPinsSyn (V := V) env d)
    (hscope : ∀ qK, qK < d.nPins →
      ∃ params : List Expr, params.length = d.nP ∧
        (∀ j, j < d.nP → ∃ ty, params[j]? = some (Expr.fvar j ty)) ∧
        ∀ x ∈ (d.pinAt qK).DsE, x.looseBVarsBounded 0 = true ∧
          ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ params)
    (hpinDs : ∀ qK, qK < d.nPins → ∀ φ : Name → Nat,
      DenoteMetaSpine m.acval env φ d.nP (d.pinAt qK).DsE ((d.pinAt qK).Ds φ))
    :
    ContainerOwnPins m d := by
  intro i cvC caps lvls DsE ps Ds ψ dp hi hfind hps hspine hsc hDlen
  have hsy := hsyn i cvC caps lvls DsE ps hi hfind (fun a ha => (hsc a ha).2) hps
  have hread : ∀ qK, qK < d.nPins →
      DenoteMetaSpine m.acval env ψ dp
        ((d.pinAt qK).DsE.map fun x =>
          Expr.instSeq DsE (DsE.length - 1)
            ((Expr.abstractRange x 0 d.nP 0).instantiateLevelParams cvC.levelParams lvls))
        (((d.pinAt qK).Ds (Level.substFn ψ cvC.levelParams lvls)).map
          (AnnotTerm.instAll Ds 0)) := by
    intro qK hqK
    obtain ⟨params, hplen, hidx, hpins⟩ := hscope qK hqK
    exact denoteMetaSpine_ownAt m hplen hidx hDlen hsc hspine
      (hpinDs qK hqK (Level.substFn ψ cvC.levelParams lvls))
      (fun x hx => (hpins x hx).1) (fun x hx => (hpins x hx).2)
  refine ⟨fun e he => ?_, fun qK hqK => ⟨_, hsy.2 qK hqK hDlen, hread qK hqK⟩⟩
  obtain ⟨qK, hqK, rfl⟩ := hsy.1 e he
  exact ⟨qK, _, hqK, rfl, hread qK hqK⟩

/-- **A CONTAINER'S OWN-PIN TABLE, READ** (task #315 WIDE, lane LE):
`ContainerOwnPinsSyn.toReadOf` at the clauses a container's record
carries for it — the components' scope (`pinDsScoped`) and their
readings (`pinDsRead`) — with the syntactic table (`ownPins`) as the
table itself.

This is what the wide identification's `hρ` is read through at EVERY
own-pin class, including the classes no field of the container names:
a pin minted inside one of the container's own copies is reachable
only through this table, and a table of expressions is only usable
once it is read. -/
theorem ContainerModeled.ownPinsRead {env : Env} {m : EnvModel V env} {ci : ContainerInfo}
    {d : BlockModel V} (C : ContainerModeled m ci d) :
    ContainerOwnPins m d :=
  C.ownPins.toReadOf C.pinDsScoped C.pinDsRead

end ConLeche.Model
