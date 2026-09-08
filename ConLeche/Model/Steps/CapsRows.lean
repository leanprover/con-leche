module

import ConLeche.Model.Steps.Stuck
import ConLeche.Model.Annot.EnvModelM
public import ConLeche.Model.Steps.TowerKit

public section

/-!
# The stored-family rows of `stuckIrrel`'s cascade (task #161, caps
tier)

`StructEtaIrrel` (`Steps/Stuck.lean`), discharged from `CapsOk`
(`Annot/EnvModelM.lean`) plus the claims.  The v1 route is two files:
`Bridge/EtaCerts.lean`'s `structEtaCertWith_stepR` (certificate run →
`DefEq.structEta`'s premises) and `Sound/Struct.lean`'s
`sndDeqStructEta` (premises → the semantic equation).  At the P
currency there is no relational way-station, so the two are one
theorem — and it is *shorter* than either, because the semantic proof
consumes only three of the rule's twenty-five premises: the family is
stored, the type former's telescope fits, and the two argument lists
are certified.  The per-field telescopes and the whole `choose_fun`
apparatus (v1's only use of choice) are **not needed at all**: they
exist to inhabit `DefEq.structEta`'s function-valued quantifiers, and
that rule is gone.

## The new sub-species: `certs_tele`

`certs_teleR` (`Bridge/Certs.lean`) turns an `iotaCerts` run into a
`Tele` derivation; the P mirror turns it into a `TeleFit`.  The
transposition is **not** clause-for-clause, and the reason is a
genuine divergence between the two fits:

* `TeleFitV` (`AnnotOkV.lean:292`) is *syntactic* — its cons peels
  `.pi A B` to `B.inst a`, exactly as `iotaCerts` peels
  `.forallE ty body` to `body.instantiate1 arg`.  The two walks
  step in lockstep, so `certs_teleR` needs no substitution lemma.
* `TeleFit` (frozen) is *semantic* — its cons peels `.pi u v A B` to
  `B` under `cons a ρ`.  The checker's walk lands on the reading of
  `body.instantiate1 arg`, which is `bodya.inst aa`; recovering `bodya`
  under `cons` from `bodya.inst aa` is a substitution metatheorem, and
  **it is false without a guard**: at `bodya = .bvar 0` the
  instantiated reading is `aa` itself, which may well be a `.pi` when
  `bodya` is not — and the checker's walk happily continues into it
  (`ty = ∀ (X : Sort 1), X` certified against `[∀ y : A, B, arg]`).

`teleFit_bvar_stuck` below is that gap, mechanized.  The guard that
closes it is `PiChain n Ta` — the reading's first `n` heads are `.pi`
nodes — and the certificate *supplies* it: `structEtaCertWith_inv`'s
`(cvT.type.stripPis cnP).isSome = true` conjunct says exactly that the
former's type is a syntactic ∀-chain of length `cnP`, and a syntactic
∀-chain reads to a `PiChain` (`piChain_of_stripPis`).  So the frozen
statement is usable; what it costs is this file's substitution
metatheorem, which has no v1 counterpart because v1's fit never needed
one.  Recorded as a finding, not a wall.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  IndCaps projFnName inferTypeCore whnf isDefEqCore)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat} {fuel : Nat}

/-! ## The ∀-chain guard -/

/-- The reading's first `n` heads are `.pi` nodes.  The guard under
which `TeleFit` can be un-instantiated (see the module docstring);
supplied at every call site by the certificate's `stripPis`
conjunct. -/
@[expose] def PiChain : Nat → AnnotTerm → Prop
  | 0, _ => True
  | n + 1, e =>
    match e with
    | .pi _ _ _ B => PiChain n B
    | _ => False

@[simp] theorem piChain_zero (e : AnnotTerm) : PiChain 0 e := trivial

@[simp] theorem piChain_succ_pi {n u v : Nat} {A B : AnnotTerm} :
    PiChain (n + 1) (.pi u v A B) = PiChain n B := rfl

/-- A ∀-chain is not a `.bvar`, and the walk cannot pretend otherwise:
this is the disequality that makes the guard load-bearing. -/
theorem piChain_succ_inv {n : Nat} {e : AnnotTerm} (h : PiChain (n + 1) e) :
    ∃ u v A B, e = .pi u v A B ∧ PiChain n B := by
  match e with
  | .pi u v A B => exact ⟨u, v, A, B, rfl, h⟩
  | .bvar _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ _
  | .letE _ _ _ | .eqE _ _ _ | .fst _ | .snd _ | .prf => exact nomatch h

/-- Substitution preserves a ∀-chain: `inst` maps `.pi` to `.pi`. -/
theorem PiChain.inst : ∀ {n : Nat} {e : AnnotTerm} (a : AnnotTerm) (k : Nat),
    PiChain n e → PiChain n (e.inst a k) := by
  intro n
  induction n with
  | zero => intro _ _ _ _; trivial
  | succ n ih =>
    intro e a k h
    obtain ⟨u, v, A, B, rfl, hB⟩ := piChain_succ_inv h
    exact ih a (k + 1) hB

/-- A ∀-chain of a list's length peels along it (task #175 W4c: the
tower typing law's residual, named without a checker run to read it
off). -/
theorem peelPis_of_piChain : ∀ (as : List AnnotTerm) {T : AnnotTerm},
    PiChain as.length T →
      ∃ rest, ConLeche.Model.AnnotTerm.peelPis T as = some rest
  | [], T, _ => ⟨T, rfl⟩
  | a :: as, T, h => by
    obtain ⟨u, v, A, B, rfl, hB⟩ := piChain_succ_inv h
    exact peelPis_of_piChain as (PiChain.inst a 0 hB)

/-! ## FINDING: the fit's un-instantiation needs the guard

`TeleFit`'s semantic cons cannot follow the checker's syntactic walk
through a `.bvar`-headed body.  The mechanized gap. -/

/-- **A `.bvar 0` body admits no fit past its own binder.**  The
checker's walk, by contrast, peels `(.bvar 0).instantiate1 a` to `a`
and keeps going — so `TeleFit` at an unguarded reading is strictly
weaker than the certificate.  (Contrast `TeleFitV`, whose cons peels
`(.bvar 0).inst a = a` and continues in step.) -/
theorem teleFit_bvar_stuck {ρ : Nat → V} {u v : Nat} {A : AnnotTerm}
    {x y : V} {ys : List V} {rest : V} :
    ¬ TeleFit V ρ (.pi u v A (.bvar 0)) (x :: y :: ys) rest := by
  rintro (_ | ⟨-, hfit⟩)
  exact nomatch hfit

/-! ## The un-instantiation metatheorem -/

/-- The empty fit pins its residual (the inversion `cases` cannot do
in place, because the fit's type index is not a variable there). -/
theorem teleFit_nil_inv {ρ : Nat → V} {T : AnnotTerm} {rest : V}
    (h : TeleFit V ρ T [] rest) : rest = interp V ρ T := by
  cases h; rfl

/-- **The fit un-instantiates, under the ∀-chain guard**: a fit of the
*substituted* reading at `ρ` is a fit of the reading itself at the
environment `inst` corresponds to.  The `.pi`-clause commutations are
`interp_inst`, `shiftE_succ_cons` and `cons_instE` — `Annot/WellDenoted.lean`'s
`WellDenoted_inst` idiom, at the fit. -/
theorem teleFit_of_inst {aa : AnnotTerm} :
    ∀ {L : List V} {E : AnnotTerm} {k : Nat} {ρ : Nat → V} {rest : V},
      PiChain L.length E →
      TeleFit V ρ (E.inst aa k) L rest →
      TeleFit V (instE k (interp V (shiftE k 0 ρ) aa) ρ) E L rest := by
  intro L
  induction L with
  | nil =>
    intro E k ρ rest _ h
    obtain rfl : rest = interp V ρ (E.inst aa k) := teleFit_nil_inv h
    rw [interp_inst]
    exact .nil
  | cons y ys ih =>
    intro E k ρ rest hpc h
    obtain ⟨u, v, A, B, rfl, hB⟩ := piChain_succ_inv hpc
    rw [AnnotTerm.inst_pi] at h
    cases h with
    | cons hmem hfit =>
      refine .cons (by rwa [interp_inst] at hmem) ?_
      have hrec := ih (E := B) (k := k + 1) (ρ := cons y ρ) hB hfit
      rw [shiftE_succ_cons] at hrec
      rw [cons_instE]
      exact hrec

/-- The outermost-binder form, the one `certs_tele` fires. -/
theorem teleFit_of_inst0 {aa : AnnotTerm} {L : List V} {E : AnnotTerm}
    {ρ : Nat → V} {rest : V} (hpc : PiChain L.length E)
    (h : TeleFit V ρ (E.inst aa) L rest) :
    TeleFit V (cons (interp V ρ aa) ρ) E L rest := by
  have := teleFit_of_inst hpc h
  rwa [shiftE_zero_zero, instE_zero] at this

/-! ## `certs_tele` — a certified spine fits the reading

`certs_teleR`'s mirror.  Two deltas beyond the substitution
metatheorem above:

* the spine's **readings are an input**, not an output.  v1's
  `InferClaimsR` *produces* a denotation; `InferClaim` consumes
  one.  Every call site already holds the readings (the subject whose
  arguments these are read, and `denoteMeta_mkAppN_inv` splits that), so
  the walk takes `DenoteMetaSpine` as a premise — which also deletes
  `DenoteSpine.det`, v1's reconciliation of two independently produced
  spines.
* the walk carries the **grading** of the running type, because
  `DefEqClaim` demands `WellDenotedV` of both comparands where
  `DefEqClaimsR` demands nothing.  It is hoisted through the `.pi`
  clause and transported across the substitution by
  `WellDenotedV_inst0` — the same two moves the literal tier's
  establishment makes. -/

/-- **A certified spine fits the type's reading.**  One step is
`InferReads` (the argument's type reads), `InferClaim` (it is
graded and the argument inhabits it) and `DefEqClaim` (it is the
domain) — the checker's own order, exactly as in `certs_teleR`. -/
theorem certs_tele {m : EnvModel V env}
    (ihd : DefEqClaim μ m φ fuel) (ihis : InferClaimIOS μ m φ fuel)
    (hexi : InferExistsIOS μ m φ fuel) :
    ∀ {d : Nat} {Δa : List AnnotTerm} (ty : Expr) (args : List Expr)
      (vs : List AnnotTerm) (Ta : AnnotTerm),
      ConLeche.iotaCertsFueled μ env fuel d false ty args = .ok true →
      PiChain args.length Ta →
      Expr.WScoped d ty → ty.looseBVarsBounded 0 = true →
      Expr.LeavesBounded ty → CtxOk m φ d Δa ty →
      denoteMeta m.acval env φ d ty = some Ta →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ Ta) →
      (∀ x ∈ args, Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ CtxOk m φ d Δa x) →
      DenoteMetaSpine m.acval env φ d args vs →
      (∀ x ∈ vs, ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ x) →
      ∀ ρ : Nat → V, Sat V Δa ρ →
        ∃ rest, TeleFit V ρ Ta (vs.map (interp V ρ)) rest := by
  intro d Δa ty args
  induction args generalizing ty with
  | nil =>
    intro vs Ta _ _ _ _ _ _ _ _ _ hsp _ ρ _
    cases hsp
    exact ⟨interp V ρ Ta, .nil⟩
  | cons a as ih =>
    intro vs Ta hc hpc hwty hbty hLbty hCty hity hokT hargs hsp hokvs
    match ty, hc, hwty, hbty, hLbty, hCty, hity with
    | .bvar _, hc, _, _, _, _, _ => exact nomatch hc
    | .fvar _ _, hc, _, _, _, _, _ => exact nomatch hc
    | .sort _, hc, _, _, _, _, _ => exact nomatch hc
    | .const _ _, hc, _, _, _, _, _ => exact nomatch hc
    | .app _ _, hc, _, _, _, _, _ => exact nomatch hc
    | .lam _ _ _, hc, _, _, _, _, _ => exact nomatch hc
    | .letE _ _ _, hc, _, _, _, _, _ => exact nomatch hc
    | .lit _, hc, _, _, _, _, _ => exact nomatch hc
    | .proj _ _ _, hc, _, _, _, _, _ => exact nomatch hc
    | .forallE dom body mb, hc, hwty, hbty, hLbty, hCty, hity => ?_
    -- the certificate's step, and the argument's frames
    obtain ⟨ta, hta, hde, hrestc⟩ := ConLeche.iotaCerts_step_inv hc
    obtain ⟨haw, hab, haLb, haC⟩ := hargs a List.mem_cons_self
    cases hsp with | @cons _ aa _ vs' haa hsp' => ?_
    -- the ∀-node's parts
    obtain ⟨hdomw, hbodyw⟩ : Expr.WScoped d dom ∧ Expr.WScoped d body := by
      simpa [Expr.WScoped] using hwty
    obtain ⟨hdomb, hbodyb⟩ :
        dom.looseBVarsBounded 0 = true ∧
          Expr.looseBVarsBounded 1 body = true := by
      simpa [Expr.looseBVarsBounded, Bool.and_eq_true] using hbty
    have hLbdom : Expr.LeavesBounded dom := fun l hl =>
      hLbty l (by simp [Expr.fvarLeaves, hl])
    have hCdom : CtxOk m φ d Δa dom :=
      hCty.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl])
    obtain ⟨doma, bodya, hdoma, hbodya, rfl⟩ := denoteMeta_forallE_inv hity
    have hpcB : PiChain as.length bodya := hpc
    -- the reading's grading, hoisted through the `.pi` clause
    have hokDom : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ doma :=
      fun ρ hρ =>
        ⟨((WellDenoted_pi V ρ 0 _ doma bodya) ▸ (hokT ρ hρ).1).1,
          ((AnnotValid_pi V ρ 0 _ doma bodya) ▸ (hokT ρ hρ).2).1⟩
    have hokBody : ∀ (ρ : Nat → V), Sat V Δa ρ →
        ∀ x, x ∈ˢ interp V ρ doma → WellDenotedV V (cons x ρ) bodya :=
      fun ρ hρ x hx =>
        ⟨((WellDenoted_pi V ρ 0 _ doma bodya) ▸ (hokT ρ hρ).1).2 x hx,
          ((AnnotValid_pi V ρ 0 _ doma bodya) ▸ (hokT ρ hρ).2).2.1 x hx⟩
    -- the argument's inferred type reads, is graded, and holds it
    obtain ⟨taa, htaa⟩ :=
      hexi hta haw hab haLb haC haa
    have hokA : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ aa :=
      hokvs aa List.mem_cons_self
    obtain ⟨hokTa, hmemA⟩ := ihis hta haw hab haLb haC haa htaa hokA
    have hwta : Expr.WScoped d ta :=
      ConLeche.inferTypeIO_WScoped m.wf fuel hta haw
    have hbta : ta.looseBVarsBounded 0 = true :=
      ConLeche.inferTypeIO_looseBVars m.wf fuel hta haw hab haLb
    have hLta : Expr.LeavesBounded ta := fun l hl =>
      haLb l (ConLeche.inferTypeIO_fvarLeaves m.wf fuel hta haw l hl)
    have hCta : CtxOk m φ d Δa ta :=
      haC.of_subset (ConLeche.inferTypeIO_fvarLeaves m.wf fuel hta haw)
    -- the certificate against the domain
    have hdeq : ∀ ρ : Nat → V, Sat V Δa ρ →
        interp V ρ taa = interp V ρ doma :=
      ihd hde hwta hbta hLta hdomw hdomb hLbdom hCta hCdom htaa hdoma
        hokTa hokDom
    -- the residual reads, by β on the reading
    have hbody' : denoteMeta m.acval env φ d (body.instantiate1 a)
        = some (bodya.inst aa) := by
      rw [denoteMeta_beta m.acval_closed (acval_inst_self m)
        (ty := dom) hbodyw.fvarsBelow haw hab haa 0, hbodya]
      rfl
    have hwbody : Expr.WScoped d (body.instantiate1 a) :=
      Expr.WScoped.instantiate1_gen haw 0 hbodyw
    have hbbody : (body.instantiate1 a).looseBVarsBounded 0 = true :=
      Expr.looseBVarsBounded_instantiate1_gen hab hbodyb
    have hLbbody : Expr.LeavesBounded (body.instantiate1 a) := by
      intro l hl
      rcases Expr.fvarLeaves_instantiate1 body 0 hl with hl' | hl'
      · exact hLbty l (by simp [Expr.fvarLeaves, hl'])
      · exact haLb l hl'
    have hCbody : CtxOk m φ d Δa (body.instantiate1 a) := by
      refine ⟨hCty.1, fun l hl => ?_⟩
      rcases Expr.fvarLeaves_instantiate1 body 0 hl with hl' | hl'
      · exact hCty.2 l (by simp [Expr.fvarLeaves, hl'])
      · exact haC.2 l hl'
    have hokBody' : ∀ ρ : Nat → V, Sat V Δa ρ →
        WellDenotedV V ρ (bodya.inst aa) := fun ρ hρ =>
      (WellDenotedV_inst0 (hokA ρ hρ)).mpr
        (hokBody ρ hρ _ ((hdeq ρ hρ) ▸ hmemA ρ hρ))
    -- the tail, and the fit
    intro ρ hρ
    obtain ⟨rest, hfit⟩ :=
      ih (body.instantiate1 a) _ _ hrestc (hpcB.inst aa 0) hwbody hbbody
        hLbbody hCbody hbody' hokBody'
        (fun x hx => hargs x (List.mem_cons_of_mem a hx)) hsp'
        (fun x hx => hokvs x (List.mem_cons_of_mem aa hx)) ρ hρ
    refine ⟨rest, .cons ((hdeq ρ hρ) ▸ hmemA ρ hρ) ?_⟩
    refine teleFit_of_inst0 (aa := aa) ?_ hfit
    rw [List.length_map, ← hsp'.length]
    exact hpcB

/-! ## The spine kit, completed

`StuckP.lean` has `DenoteMetaSpine`, its length, the inversion and the
congruence.  The η row needs four more: the two list splits, the
append, the mapped spine (`DenoteSpine.map_list`'s mirror) and the
*constructing* direction of the application inversion. -/

theorem DenoteMetaSpine.take {acval : Name → (Name → Nat) → AnnotTerm}
    {d : Nat} {as : List Expr} {vs : List AnnotTerm}
    (h : DenoteMetaSpine acval env φ d as vs) :
    ∀ n, DenoteMetaSpine acval env φ d (as.take n) (vs.take n) := by
  induction h with
  | nil => intro n; simpa using DenoteMetaSpine.nil
  | @cons a v as vs ha _ ih =>
    intro n
    cases n with
    | zero => exact DenoteMetaSpine.nil
    | succ n => exact DenoteMetaSpine.cons ha (ih n)

theorem DenoteMetaSpine.drop {acval : Name → (Name → Nat) → AnnotTerm}
    {d : Nat} {as : List Expr} {vs : List AnnotTerm}
    (h : DenoteMetaSpine acval env φ d as vs) :
    ∀ n, DenoteMetaSpine acval env φ d (as.drop n) (vs.drop n) := by
  induction h with
  | nil => intro n; simpa using DenoteMetaSpine.nil
  | @cons a v as vs ha htl ih =>
    intro n
    cases n with
    | zero => exact DenoteMetaSpine.cons ha htl
    | succ n => exact ih n

theorem DenoteMetaSpine.append {acval : Name → (Name → Nat) → AnnotTerm}
    {d : Nat} {as bs : List Expr} {vs ws : List AnnotTerm}
    (h : DenoteMetaSpine acval env φ d as vs)
    (h2 : DenoteMetaSpine acval env φ d bs ws) :
    DenoteMetaSpine acval env φ d (as ++ bs) (vs ++ ws) := by
  induction h with
  | nil => exact h2
  | cons ha _ ih => exact DenoteMetaSpine.cons ha ih

/-- A mapped spine reads pointwise (`DenoteSpine.map_list`'s mirror). -/
theorem DenoteMetaSpine.map_list {acval : Name → (Name → Nat) → AnnotTerm}
    {d : Nat} {g : Nat → Expr} {G : Nat → AnnotTerm} :
    ∀ l : List Nat, (∀ j ∈ l, denoteMeta acval env φ d (g j) = some (G j)) →
      DenoteMetaSpine acval env φ d (l.map g) (l.map G) := by
  intro l
  induction l with
  | nil => intro _; exact DenoteMetaSpine.nil
  | cons x xs ih =>
    intro h
    exact DenoteMetaSpine.cons (h x (by simp))
      (ih fun j hj => h j (by simp [hj]))

/-- **The application spine reads, constructing direction** —
`denoteMeta_mkAppN_inv`'s converse, the one the fabricated projection
spine needs. -/
theorem denoteMeta_mkAppN {acval : Name → (Name → Nat) → AnnotTerm} {d : Nat}
    {as : List Expr} {vs : List AnnotTerm}
    (h : DenoteMetaSpine acval env φ d as vs) :
    ∀ {f : Expr} {fa : AnnotTerm}, denoteMeta acval env φ d f = some fa →
      denoteMeta acval env φ d (Expr.mkAppN f as) = some (AnnotTerm.mkAppN fa vs) := by
  induction h with
  | nil => intro f fa hf; exact hf
  | cons ha _ ih =>
    intro f fa hf
    exact ih (by rw [denoteMeta_app, hf, ha]; rfl)

/-! ## From a fit to a graded application

The P currency's own tax, and the CapsP docstring's prediction made
good: a `TeleFit` plus the *type's* grading yields the applied spine's
grading and its residual membership, one `app_mem_piR` per argument
whose `v = 0` fibre premise is `AnnotValid_pi`'s third clause.  The
type's environment `σ` is kept separate from the spine's `ρ` — the fit
peels into `cons`-extensions of `σ` while the application stays at
`ρ`, which is exactly the divergence `teleFit_of_inst` had to
mediate on the other side. -/

theorem wellDenotedV_mkAppN_of_fit {ρ : Nat → V} :
    ∀ (vs : List AnnotTerm) {Ta f : AnnotTerm} {σ : Nat → V} {rest : V},
      WellDenotedV V σ Ta → WellDenotedV V ρ f →
      (∀ x ∈ vs, WellDenotedV V ρ x) →
      interp V ρ f ∈ˢ interp V σ Ta →
      TeleFit V σ Ta (vs.map (interp V ρ)) rest →
      WellDenotedV V ρ (AnnotTerm.mkAppN f vs) ∧
        interp V ρ (AnnotTerm.mkAppN f vs) ∈ˢ rest := by
  intro vs
  induction vs with
  | nil =>
    intro Ta f σ rest _ hf _ hmem hfit
    obtain rfl : rest = interp V σ Ta := teleFit_nil_inv hfit
    exact ⟨hf, hmem⟩
  | cons x xs ih =>
    intro Ta f σ rest hokT hf hoks hmem hfit
    simp only [List.map_cons] at hfit
    cases hfit with
    | @cons _ u v A B _ _ _ hx hfit' =>
      have hokA : WellDenotedV V σ A :=
        ⟨((WellDenoted_pi V σ u v A B) ▸ hokT.1).1,
          ((AnnotValid_pi V σ u v A B) ▸ hokT.2).1⟩
      have hokB : ∀ y, y ∈ˢ interp V σ A → WellDenotedV V (cons y σ) B :=
        fun y hy =>
          ⟨((WellDenoted_pi V σ u v A B) ▸ hokT.1).2 y hy,
            ((AnnotValid_pi V σ u v A B) ▸ hokT.2).2.1 y hy⟩
      have hfib : v = 0 → ∀ y, y ∈ˢ interp V σ A →
          interp V (cons y σ) B ∈ˢ (univZero : V) :=
        ((AnnotValid_pi V σ u v A B) ▸ hokT.2).2.2
      rw [interp_pi] at hmem
      have hokx : WellDenotedV V ρ x := hoks x List.mem_cons_self
      have hstep : WellDenotedV V ρ (.app f x) := by
        refine ⟨?_, ?_⟩
        · rw [WellDenoted_app]
          exact ⟨hf.1, hokx.1, v, interp V σ A,
            (fun y => interp V (cons y σ) B), hmem, hx, hfib⟩
        · rw [AnnotValid_app]; exact ⟨hf.2, hokx.2⟩
      have hmem' : interp V ρ (.app f x)
          ∈ˢ interp V (cons (interp V ρ x) σ) B := by
        rw [interp_app]
        exact app_mem_piR hmem hx hfib
      -- (`mkAppN f (x :: xs) = mkAppN (.app f x) xs` is definitional)
      exact ih (hokB _ hx) hstep
        (fun y hy => hoks y (List.mem_cons_of_mem x hy)) hmem' hfit'

/-! ## The ∀-chain guard, supplied by the certificate -/

/-- **A syntactic ∀-telescope reads to a ∀-chain.**  `stripPis n`
succeeding is exactly `PiChain n` of the reading — the certificate's
own conjunct, converted. -/
theorem piChain_of_stripPis {acval : Name → (Name → Nat) → AnnotTerm} :
    ∀ (n : Nat) {d : Nat} {e : Expr} {ea : AnnotTerm},
      (e.stripPis n).isSome = true →
      denoteMeta acval env φ d e = some ea → PiChain n ea := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _; trivial
  | succ n ih =>
    intro d e ea hs hd
    match e, hs with
    | .bvar _, hs => exact nomatch hs
    | .fvar _ _, hs => exact nomatch hs
    | .sort _, hs => exact nomatch hs
    | .const _ _, hs => exact nomatch hs
    | .app _ _, hs => exact nomatch hs
    | .lam _ _ _, hs => exact nomatch hs
    | .letE _ _ _, hs => exact nomatch hs
    | .lit _, hs => exact nomatch hs
    | .proj _ _ _, hs => exact nomatch hs
    | .forallE ty bd mb, hs =>
      obtain ⟨ta, ba, -, hba, rfl⟩ := denoteMeta_forallE_inv hd
      simp only [ConLeche.Expr.stripPis, Option.isSome_map] at hs
      exact ih (ConLeche.Expr.stripPis_instantiate1_isSome n 0 hs) hba

/-! ## The stored structure's η row

`structEtaCertWith_stepR` and `sndDeqStructEta`, fused.  What the
semantic argument actually consumes is small: the family is stored
(`EtaFamilyStored`, built from the certificate's constructor lookup and
its per-field recursor lookups), the former's telescope fits
(`certs_tele` on the `iotaCerts` conjunct), and the two argument
lists are certified (`map_interp_of_defEqListFueled` twice).  The per-field
telescopes appear only to *grade* the fabricated projection spine —
`DefEqClaim` demands `WellDenotedV` of both comparands where
`DefEqClaimsR` demands nothing — and they are consumed through
`wellDenotedV_mkAppN_of_fit`, not through any function-valued
quantification, so `choose_fun` has no counterpart here. -/

/-- **The η certificate's semantic content, at a given reduced type**
(`structEtaCertWith_stepR`'s mirror; factored out of
`structEtaIrrel_of_claims` for the iota tier's major rescue, which
holds a `structEtaCertWithFueled` run whose `tmaj` was computed by
`majorToCtor` and must not be recomputed — the same reason v1
factored its own).

The stored η law fires at the reduced type's parameter spine; the
fabricated value spine is `etaFabArgsV`, and the certificate's two
`defEqList` runs identify it with the constructor application's own
arguments. -/
theorem structEtaCertWithFueled_step {m : EnvModel V env}
    (hcaps : CapsOk m) (htower : TowerOk m φ) (hct : ConstType m φ)
    (hav : AcvalValid m)
    (ihd : DefEqClaim μ m φ fuel) (ihis : InferClaimIOS μ m φ fuel)
    (hexi : InferExistsIOS μ m φ fuel)
    {d : Nat} {Δa : List AnnotTerm} {a b wtb : Expr}
    {aa ba wtba : AnnotTerm}
    (hcw : ConLeche.structEtaCertWithFueled μ env fuel d a b wtb = .ok true)
    (hwa : Expr.WScoped d a) (hba : a.looseBVarsBounded 0 = true)
    (hLa : Expr.LeavesBounded a) (hCa : CtxOk m φ d Δa a)
    (hwb : Expr.WScoped d b) (hbb : b.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded b) (hCb : CtxOk m φ d Δa b)
    (hwr : Expr.WScoped d wtb) (hbr : wtb.looseBVarsBounded 0 = true)
    (hLr : Expr.LeavesBounded wtb) (hCr : CtxOk m φ d Δa wtb)
    (hda : denoteMeta m.acval env φ d a = some aa)
    (hdb : denoteMeta m.acval env φ d b = some ba)
    (hwtba : denoteMeta m.acval env φ d wtb = some wtba)
    (hokA : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ aa)
    (hokB : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ba)
    (hokW : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ wtba)
    (hmemBW : ∀ ρ : Nat → V, Sat V Δa ρ →
      interp V ρ ba ∈ˢ interp V ρ wtba)
    (ρ : Nat → V) (hρ : Sat V Δa ρ) :
    interp V ρ aa = interp V ρ ba := by
  obtain ⟨c, us, cvc, cnP, cnF, T, us', cvT, caps, hfna, hfc, hlena,
    hfnb, hfT, heta, hectr, hepar, hefld, hresT, hresc, hlenb, hlenus,
    hlpc, hstrip, hslots, hlev, hcertT, hprojs, hdefL1, -, hdefL2⟩ :=
    ConLeche.structEtaCertWith_inv hcw
  have hmemB := hmemBW
  -- the reduced type is the family applied to its parameters
  rw [show wtb = Expr.mkAppN wtb.getAppFn wtb.getAppArgs from
    (ConLeche.Expr.mkAppN_getApp wtb).symm, hfnb] at hwtba
  obtain ⟨vT, tsa, hvT, hspt, rfl⟩ := denoteMeta_mkAppN_inv hwtba
  rw [denoteMeta, hfT] at hvT
  dsimp only at hvT
  split at hvT
  case isFalse => exact nomatch hvT
  case isTrue =>
  obtain rfl : vT = m.acval T (Level.substFn φ cvT.levelParams us') := (Option.some.inj hvT).symm
  -- the constructor side is the constructor applied to its arguments
  rw [show a = Expr.mkAppN a.getAppFn a.getAppArgs from
    (ConLeche.Expr.mkAppN_getApp a).symm, hfna] at hda
  obtain ⟨vf, asa, hvf, hspa, rfl⟩ := denoteMeta_mkAppN_inv hda
  rw [denoteMeta, hfc] at hvf
  dsimp only at hvf
  split at hvf
  case isFalse => exact nomatch hvf
  case isTrue =>
  obtain rfl : vf = m.acval c (Level.substFn φ cvc.levelParams us) :=
    (Option.some.inj hvf).symm
  -- the two instantiations agree (`sndDeqStructEta`'s `hψ`)
  have hψc : Level.substFn φ cvc.levelParams us = (Level.substFn φ cvT.levelParams us') := by
    rw [hlpc]
    exact ConLeche.Level.substFn_congr (ConLeche.Level.isEquivList_sound hlev φ)
  -- the slot discipline (task #175 W4c): every slot is a tower entry
  -- (and there is one), or every slot is a projection function — an
  -- all-tower family with no field is the latter case, nothing being
  -- fabricated either way
  have hkind : (ConLeche.towerSlotsAll env T cnF = true ∧ 0 < cnF) ∨
      ((∀ j, j < cnF → ∃ cvp mIp rPp rulesp,
          env.find? (projFnName T j) = some (.recInfo cvp mIp rPp rulesp)) ∧
        (ConLeche.towerSlotsAll env T cnF = true → cnF = 0)) := by
    by_cases htow : ConLeche.towerSlotsAll env T cnF = true
    · by_cases h0 : 0 < cnF
      · exact .inl ⟨htow, h0⟩
      · exact .inr ⟨fun j hj => absurd hj (by omega), fun _ => by omega⟩
    · have hrec : ConLeche.recSlotsAll env T cnF = true := by
        simpa [htow] using hslots
      exact .inr ⟨fun j hj => ConLeche.recSlotsAll_slot hrec j hj,
        fun h => absurd h htow⟩
  -- the former's type: closed, so its reading at depth `0` is its
  -- reading at every depth, and all four frames are free
  have hwfT := m.wf _ (ConLeche.Semantics.Env.find?_mem hfT)
  have hnfT : (cvT.type.instantiateLevelParams cvT.levelParams us').hasFvar
      = false := by
    rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hwfT.1
  have hbdT : (cvT.type.instantiateLevelParams cvT.levelParams
      us').looseBVarsBounded 0 = true := by
    rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]
    exact hwfT.2.2.2.1
  have hTw : Expr.WScoped d
      (cvT.type.instantiateLevelParams cvT.levelParams us') :=
    ConLeche.Expr.WScoped.of_not_hasFvar hnfT
  have hTL : Expr.LeavesBounded
      (cvT.type.instantiateLevelParams cvT.levelParams us') :=
    ConLeche.Expr.LeavesBounded.of_not_hasFvar hnfT
  have hTC : CtxOk m φ d Δa
      (cvT.type.instantiateLevelParams cvT.levelParams us') :=
    ⟨hCa.1, fun l hl => by
      rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnfT] at hl
      exact nomatch hl⟩
  obtain ⟨hohT, hoT⟩ := hoist_spine tsa hokW
  obtain ⟨hohA, hoA⟩ := hoist_spine asa hokA
  -- the former's telescope fits the parameter spine (`certs_tele` on
  -- the certificate's former conjunct), at whichever law's reading
  have hfitOf : ∀ TVa : AnnotTerm,
      denoteMeta m.acval env φ 0
        (cvT.type.instantiateLevelParams cvT.levelParams us') = some TVa →
      (∀ σ : Nat → V, WellDenotedV V σ TVa) →
      ∃ rest, TeleFit V ρ TVa (tsa.map (interp V ρ)) rest := by
    intro TVa hTVa hokTVa
    have hTVd : denoteMeta m.acval env φ d
        (cvT.type.instantiateLevelParams cvT.levelParams us') = some TVa :=
      denoteMeta_depth_of_closed m.acval_closed hnfT
        (fun k => denoteMeta_closed m.acval_erase m.cval_closed
          hnfT hbdT hTVa 1 k) hTVa d
    -- the ∀-chain guard, from the certificate's `stripPis` conjunct
    have hpcT : PiChain wtb.getAppArgs.length TVa := by
      rw [hlenb]
      exact piChain_of_stripPis cnP
        (ConLeche.Expr.stripPis_instantiateLevelParams_isSome
          cvT.levelParams us' cnP hstrip) hTVd
    exact certs_tele ihd ihis hexi _ wtb.getAppArgs tsa TVa hcertT hpcT
      hTw hbdT hTL hTC hTVd (fun σ _ => hokTVa σ)
      (frame_spine hwr hbr hLr hCr) hspt hoT ρ hρ
  -- the fold form both sides are read in
  have hfold : ∀ (l : List AnnotTerm) (x : V),
      l.foldl (fun r y => SetTheory.app r (interp V ρ y)) x
        = (l.map (interp V ρ)).foldl SetTheory.app x := by
    intro l x; rw [List.foldl_map]
  -- the stuck side inhabits the family instance
  have hmemFam : interp V ρ ba
      ∈ˢ (tsa.map (interp V ρ)).foldl SetTheory.app
          (interp V ρ (m.acval T (Level.substFn φ cvT.levelParams us'))) := by
    have := hmemB ρ hρ
    rwa [interp_mkAppN, hfold] at this
  have hlenTs : (tsa.map (interp V ρ)).length = caps.etaParams := by
    rw [List.length_map, ← hspt.length, hlenb, hepar]
  -- the fabricated projection spine's subject list: it reads, and it
  -- is graded
  have hspTb : DenoteMetaSpine m.acval env φ d (wtb.getAppArgs ++ [b])
      (tsa ++ [ba]) := hspt.append (DenoteMetaSpine.cons hdb DenoteMetaSpine.nil)
  have hframeTb : ∀ x ∈ wtb.getAppArgs ++ [b],
      Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ CtxOk m φ d Δa x := by
    intro x hx
    rcases List.mem_append.mp hx with hx' | hx'
    · exact frame_spine hwr hbr hLr hCr x hx'
    · rcases List.mem_singleton.mp hx' with rfl
      exact ⟨hwb, hbb, hLb, hCb⟩
  have hokTb' : ∀ x ∈ tsa ++ [ba], ∀ σ : Nat → V, Sat V Δa σ →
      WellDenotedV V σ x := by
    intro x hx
    rcases List.mem_append.mp hx with hx' | hx'
    · exact hoT x hx'
    · rcases List.mem_singleton.mp hx' with rfl; exact hokB
  -- the parameter halves of the two certified lists, pointwise
  have htake : (asa.take cnP).map (interp V ρ) = tsa.map (interp V ρ) :=
    map_interp_of_defEqListFueled ihd hdefL1
      (fun x hx => frame_spine hwa hba hLa hCa x (List.mem_of_mem_take hx))
      (frame_spine hwr hbr hLr hCr) (hspa.take cnP) hspt
      (fun x hx => hoA x (List.mem_of_mem_take hx)) hoT ρ hρ
  rcases hkind with ⟨htow, h0⟩ | ⟨hrecs, htow0⟩
  · -- TOWER-BACKED SLOTS (task #175 W4c): the fabricated projections
    -- are `.proj T j b` nodes reading to `projAV j`, graded by each
    -- entry's typing law; the η law is the entry law's clause (C),
    -- read through slot `0`
    -- (task #175 S1: the family's slots are the table's, whose head
    -- data carries the former's level parameters; no per-slot
    -- certificate runs at a tower family)
    have hslotE : ∀ j, j < cnF → ∃ entry : ProjEntry,
        env.findProj? T j = some entry ∧
        entry.levelParams = cvT.levelParams := by
      intro j hj
      obtain ⟨entry, hfe⟩ := ConLeche.towerSlotsAll_slot htow j hj
      obtain ⟨-, -, -, ⟨cvT', capsT', hfT', hlpsT', -⟩, -⟩ :=
        htower T j entry hfe
      have hcvT' : cvT' = cvT := by
        rw [hfT] at hfT'
        exact (ConstantInfo.indInfo.inj (Option.some.inj hfT')).1.symm
      exact ⟨entry, hfe, by rw [← hlpsT', hcvT']⟩
    obtain ⟨e0, hfe0⟩ := ConLeche.towerSlotsAll_slot htow 0 h0
    obtain ⟨-, -, -, ⟨cvT', capsT', hfT', hlpsT', himp'⟩,
      -, -, -, -, -, hetaL⟩ := htower T 0 e0 hfe0
    have hcvT' : cvT' = cvT := by
      rw [hfT] at hfT'
      exact (ConstantInfo.indInfo.inj (Option.some.inj hfT')).1.symm
    have hcapsT' : capsT' = caps := by
      rw [hfT] at hfT'
      exact (ConstantInfo.indInfo.inj (Option.some.inj hfT')).2.symm
    obtain ⟨-, hctr', hpar', hfld'⟩ := himp' (by rw [hcapsT']; exact heta)
    rw [hcvT'] at hlpsT'
    rw [hcapsT'] at hctr' hpar' hfld'
    obtain ⟨TVa, hTVa, hokTVa, hlaw⟩ :=
      hetaL cvT caps hfT us' (by rw [← hlpsT']; exact hlenus)
    obtain ⟨rest, hfitT⟩ := hfitOf TVa hTVa hokTVa
    have hb := hlaw ρ (tsa.map (interp V ρ)) rest (interp V ρ ba)
      (by rw [hlenTs, hpar']) hfitT (by rw [← hlpsT']; exact hmemFam)
    -- every slot of the table carries slot `0`'s projection offset
    -- (task #210 Part A: the tagged tower of the fixpoint route)
    have hoffE : ∀ j entry, env.findProj? T j = some entry → entry.off = e0.off :=
      fun j entry hfe => ConLeche.Env.findProj?_off_eq hfe hfe0
    have hprojden : ∀ j ∈ List.range cnF,
        denoteMeta m.acval env φ d (.proj T j b) = some (projAV (j + e0.off) ba) := by
      intro j hj
      obtain ⟨entry, hfe, -⟩ := hslotE j (List.mem_range.mp hj)
      rw [← hoffE j entry hfe]
      exact denoteMeta_proj_tower hfe hdb
    have hokProj : ∀ x ∈ (List.range cnF).map (fun j => projAV (j + e0.off) ba),
        ∀ σ : Nat → V, Sat V Δa σ → WellDenotedV V σ x := by
      intro x hx σ hσ
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      obtain ⟨entry, hfe, hlpe⟩ := hslotE j (List.mem_range.mp hj)
      rw [← hoffE j entry hfe]
      obtain ⟨-, -, -, ⟨cvTj, capsTj, hfTj, -, himpj⟩, hO5j, _,
        -, -, hlawj, -⟩ := htower T j entry hfe
      have hcapsTj : capsTj = caps := by
        rw [hfT] at hfTj
        exact (ConstantInfo.indInfo.inj (Option.some.inj hfTj)).2.symm
      obtain ⟨hnpj, -, hparj, -⟩ := himpj (by rw [hcapsTj]; exact heta)
      rw [hcapsTj] at hparj
      -- the family is not a proposition (it claims η), so the guard
      -- holds at every valuation by O5
      have hgj : TowerGuardAt φ entry us' :=
        towerGuardAt_of hO5j (fun hp => by rw [hp] at hnpj; exact nomatch hnpj)
      obtain ⟨⟨Ta, hTa, hA⟩, -⟩ := hlawj us' (by rw [hlpe]; exact hlenus)
      obtain ⟨hTad, -⟩ := towerEntry_tele_at_depth hfe hTa
      have hlenVs : tsa.length = entry.numParams := by
        rw [← hspt.length, hlenb, ← hepar, hparj]
      -- the body telescope's reading is a ∀-chain of the subject
      -- list's length, so it peels along it
      have hpc : PiChain (tsa ++ [ba]).length Ta := by
        rw [List.length_append, List.length_singleton, hlenVs]
        exact piChain_of_stripPis _
          (by rw [ConLeche.projTele_stripPis]; rfl) (hTad d)
      obtain ⟨restj, hpeel⟩ := peelPis_of_piChain _ hpc
      rw [hlpe] at hA
      exact (hA hgj σ tsa ba restj hlenVs (hokW σ hσ) (hokB σ hσ) (hmemB σ hσ)
        hpeel).1
    have hframeProj : ∀ x ∈ (List.range cnF).map (fun j => Expr.proj T j b),
        Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
          Expr.LeavesBounded x ∧ CtxOk m φ d Δa x := by
      intro x hx
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
      exact ⟨by simpa [Expr.WScoped] using hwb,
        by simpa [Expr.looseBVarsBounded] using hbb,
        fun l hl => hLb l (by simpa [Expr.fvarLeaves] using hl),
        ⟨hCb.1, fun l hl => hCb.2 l (by simpa [Expr.fvarLeaves] using hl)⟩⟩
    rw [ConLeche.etaProjs, if_pos htow] at hdefL2
    have hdrop : (asa.drop cnP).map (interp V ρ)
        = ((List.range cnF).map fun j => projAV (j + e0.off) ba).map (interp V ρ) :=
      map_interp_of_defEqListFueled ihd hdefL2
        (fun x hx => frame_spine hwa hba hLa hCa x (List.mem_of_mem_drop hx))
        hframeProj (hspa.drop cnP)
        (DenoteMetaSpine.map_list _ hprojden)
        (fun x hx => hoA x (List.mem_of_mem_drop hx)) hokProj ρ hρ
    -- the constructor's arguments ARE the fabricated spine
    have hfab : asa.map (interp V ρ)
        = tsa.map (interp V ρ) ++ (List.range e0.numFields).map
            (fun j => ConLeche.SetTheory.Tower.projS (j + e0.off) (interp V ρ ba)) := by
      rw [← List.take_append_drop cnP asa, List.map_append, htake, hdrop,
        List.map_map, ← hfld', hefld]
      refine congrArg _ (List.map_congr_left fun j _ => ?_)
      rw [Function.comp_apply, projAV_interp]
    -- assemble
    rw [hb, interp_mkAppN, hfold, hfab, hψc, ← hctr', hectr, hlpsT']
  · -- PROJECTION-FUNCTION SLOTS: the stored-family law, as before
    -- the family is stored
    have hfam : ConLeche.EtaFamilyStored env T caps := by
      refine ⟨by rw [hectr]; exact hresc, ⟨cvc, ?_⟩, ?_⟩
      · rw [hectr, hepar, hefld]; exact hfc
      · intro j hj
        exact hrecs j (by rw [← hefld]; exact hj)
    -- the fabricated projections are the projection functions' spines
    have hetaP : ConLeche.etaProjs env T us' wtb.getAppArgs b cnF
        = (List.range cnF).map (fun i =>
            Expr.mkAppN (.const (projFnName T i) us') (wtb.getAppArgs ++ [b])) := by
      unfold ConLeche.etaProjs
      split
      · next h => rw [htow0 h]; simp
      · rfl
    rw [hetaP] at hdefL2
    -- the law, and its carried reading moved to the ambient depth
    obtain ⟨TVa, hTVa, hokTVa, hlaw⟩ :=
      hcaps.1 T cvT caps hfT heta hresT hfam φ us' hlenus
    obtain ⟨rest, hfitT⟩ := hfitOf TVa hTVa hokTVa
    have hb := hlaw ρ (tsa.map (interp V ρ)) rest (interp V ρ ba)
      hlenTs hfitT hmemFam
    -- each slot is a recursor, certified (the per-slot certificates
    -- ran: the family is not a tower family, task #175 S1)
    have hslotR : ∀ j ∈ List.range cnF, ∃ cvp mIp rPp rulesp,
        env.find? (projFnName T j) = some (.recInfo cvp mIp rPp rulesp) ∧
        cvp.levelParams = cvT.levelParams ∧
        (cvp.type.stripPis (wtb.getAppArgs.length + 1)).isSome = true ∧
        ConLeche.iotaCertsFueled μ env fuel d false
          (cvp.type.instantiateLevelParams cvp.levelParams us')
          (wtb.getAppArgs ++ [b]) = .ok true := by
      intro j hj
      have hcnF : 0 < cnF := Nat.lt_of_le_of_lt (Nat.zero_le j) (List.mem_range.mp hj)
      have htowF : ConLeche.towerSlotsAll env T cnF = false := by
        cases h : ConLeche.towerSlotsAll env T cnF
        · rfl
        · exact absurd (htow0 h) (by omega)
      exact ConLeche.structEtaProjCerts_inv _ (hprojs htowF) j hj
    have hprojden : ∀ j ∈ List.range cnF,
        denoteMeta m.acval env φ d
            (Expr.mkAppN (.const (projFnName T j) us') (wtb.getAppArgs ++ [b]))
          = some (AnnotTerm.mkAppN (m.acval (projFnName T j) (Level.substFn φ cvT.levelParams us')) (tsa ++ [ba])) := by
      intro j hj
      obtain ⟨cvp, mIp, rPp, rulesp, hfp, hlpj, -, -⟩ := hslotR j hj
      refine denoteMeta_mkAppN hspTb ?_
      rw [denoteMeta, hfp]
      dsimp only
      split
      · next =>
        show some (m.acval (projFnName T j)
          (Level.substFn φ cvp.levelParams us')) = _
        rw [hlpj]
      · next hne =>
        exact absurd (show us'.length = cvp.levelParams.length from by
          rw [hlpj]; exact hlenus) hne
    have hokProj : ∀ x ∈ (List.range cnF).map (fun j =>
          AnnotTerm.mkAppN (m.acval (projFnName T j) (Level.substFn φ cvT.levelParams us')) (tsa ++ [ba])),
        ∀ σ : Nat → V, Sat V Δa σ → WellDenotedV V σ x := by
      intro x hx σ hσ
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      obtain ⟨cvp, mIp, rPp, rulesp, hfp, hlpj, hstrpj, hicj⟩ := hslotR j hj
      have hlenp : us'.length = cvp.levelParams.length := by
        rw [hlpj]; exact hlenus
      obtain ⟨tpa, htpa, hoktpa, hmemp⟩ :=
        hct d (projFnName T j) _ us' hfp rfl hlenp
      -- the projection type's frames
      have hwfp := m.wf _ (ConLeche.Semantics.Env.find?_mem hfp)
      have hnfp : (cvp.type.instantiateLevelParams cvp.levelParams
          us').hasFvar = false := by
        rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hwfp.1
      have hbdp : (cvp.type.instantiateLevelParams cvp.levelParams
          us').looseBVarsBounded 0 = true := by
        rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]
        exact hwfp.2.2.2.1
      have hpcp : PiChain (wtb.getAppArgs ++ [b]).length tpa := by
        rw [List.length_append, List.length_singleton]
        exact piChain_of_stripPis _
          (ConLeche.Expr.stripPis_instantiateLevelParams_isSome
            cvp.levelParams us' _ hstrpj) htpa
      obtain ⟨restp, hfitp⟩ :=
        certs_tele ihd ihis hexi _ (wtb.getAppArgs ++ [b]) (tsa ++ [ba])
          tpa hicj hpcp (ConLeche.Expr.WScoped.of_not_hasFvar hnfp) hbdp
          (ConLeche.Expr.LeavesBounded.of_not_hasFvar hnfp)
          ⟨hCa.1, fun l hl => by
            rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnfp] at hl
            exact nomatch hl⟩
          htpa (fun τ _ => hoktpa τ) hframeTb hspTb hokTb' σ hσ
      refine (wellDenotedV_mkAppN_of_fit (tsa ++ [ba]) (hoktpa σ)
        ⟨m.acval_wellDenoted _ _ σ, hav _ _ σ⟩
        (fun x hx => hokTb' x hx σ hσ) ?_ hfitp).1
      have := hmemp σ
      dsimp only [ConLeche.ConstantInfo.toConstantVal] at this
      rwa [hlpj] at this
    have hframeProj : ∀ x ∈ (List.range cnF).map (fun i =>
          Expr.mkAppN (.const (projFnName T i) us') (wtb.getAppArgs ++ [b])),
        Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
          Expr.LeavesBounded x ∧ CtxOk m φ d Δa x := by
      intro x hx
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
      refine ⟨ConLeche.Expr.WScoped.mkAppN
          (ConLeche.Expr.WScoped.of_not_hasFvar rfl)
          (fun y hy => (hframeTb y hy).1),
        ConLeche.looseBVarsBounded_mkAppN rfl
          (fun y hy => (hframeTb y hy).2.1),
        fun l hl => ?_, ⟨hCa.1, fun l hl => ?_⟩⟩ <;>
      · rcases ConLeche.fvarLeaves_mkAppN hl with hl' | ⟨y, hy, hly⟩
        · exact absurd hl' (by simp [Expr.fvarLeaves])
        · first
          | exact (hframeTb y hy).2.2.1 l hly
          | exact (hframeTb y hy).2.2.2.2 l hly
    have hdrop : (asa.drop cnP).map (interp V ρ)
        = ((List.range cnF).map fun j =>
            AnnotTerm.mkAppN (m.acval (projFnName T j) (Level.substFn φ cvT.levelParams us')) (tsa ++ [ba])).map
          (interp V ρ) :=
      map_interp_of_defEqListFueled ihd hdefL2
        (fun x hx => frame_spine hwa hba hLa hCa x (List.mem_of_mem_drop hx))
        hframeProj (hspa.drop cnP)
        (DenoteMetaSpine.map_list _ hprojden)
        (fun x hx => hoA x (List.mem_of_mem_drop hx)) hokProj ρ hρ
    -- the constructor's arguments ARE the fabricated spine
    have hfab : asa.map (interp V ρ)
        = etaFabArgsV (fun n => interp V ρ (m.acval n (Level.substFn φ cvT.levelParams us'))) T
            (tsa.map (interp V ρ)) (interp V ρ ba) caps.etaFields := by
      rw [etaFabArgsV, projSpines, ← List.take_append_drop cnP asa,
        List.map_append, htake, hdrop, hefld, List.map_map]
      refine congrArg _ (List.map_congr_left fun j _ => ?_)
      show interp V ρ (AnnotTerm.mkAppN (m.acval (projFnName T j) (Level.substFn φ cvT.levelParams us'))
        (tsa ++ [ba])) = _
      rw [interp_mkAppN, hfold, List.map_append]
      rfl
    -- assemble
    rw [hb, interp_mkAppN, hfold, hfab, hψc, hectr]

/-- **`StructEtaIrrel`, discharged from the field.**  The wrapper's own
reduction (infer the stuck side, head-normalise, read the claims off
it) plus `structEtaCertWithFueled_step`. -/
theorem structEtaIrrel_of_claims {m : EnvModel V env}
    (hcaps : CapsOk m) (htower : TowerOk m φ) (hct : ConstType m φ)
    (hav : AcvalValid m)
    (ihw : WhnfClaim μ m φ fuel) (ihd : DefEqClaim μ m φ fuel)
    (ihis : InferClaimIOS μ m φ fuel)
    (hexi : InferExistsIOS μ m φ fuel) (hwreads : WhnfReads m μ φ fuel) :
    StructEtaIrrel μ m φ fuel := by
  intro d a b Δa h hwa hba hLa hwb hbb hLb aa ba hCa hCb hda hdb
    hokA hokB ρ hρ
  obtain ⟨tb, wtb, htb, hwtb, hcw⟩ := ConLeche.structEtaCert_inv h
  -- the stuck side's inferred type: frames, reading, membership
  have hwt : Expr.WScoped d tb :=
    ConLeche.inferTypeIO_WScoped m.wf fuel htb hwb
  have hbt : tb.looseBVarsBounded 0 = true :=
    ConLeche.inferTypeIO_looseBVars m.wf fuel htb hwb hbb hLb
  have hLt : Expr.LeavesBounded tb := fun l hl =>
    hLb l (ConLeche.inferTypeIO_fvarLeaves m.wf fuel htb hwb l hl)
  have hCt : CtxOk m φ d Δa tb :=
    hCb.of_subset (ConLeche.inferTypeIO_fvarLeaves m.wf fuel htb hwb)
  obtain ⟨tba, htba⟩ :=
    hexi htb hwb hbb hLb hCb hdb
  obtain ⟨hokTb, hmemB⟩ := ihis htb hwb hbb hLb hCb hdb htba hokB
  obtain ⟨wtba, hwtba⟩ := hwreads hwtb hwt hbt hLt
    (LeafReads.of_ctxOk hCt) htba
  obtain ⟨hokW, heqW⟩ := ihw hwtb hwt hbt hLt hCt htba hwtba hokTb
  -- the reduct's frames
  have hwr : Expr.WScoped d wtb := ConLeche.whnf_WScoped m.wf fuel hwtb hwt
  have hbr : wtb.looseBVarsBounded 0 = true :=
    ConLeche.whnf_looseBVars m.wf fuel hwtb hbt
  have hLr : Expr.LeavesBounded wtb := fun l hl =>
    hLt l (ConLeche.whnf_fvarLeaves m.wf fuel hwtb l hl)
  have hCr : CtxOk m φ d Δa wtb :=
    hCt.of_subset (ConLeche.whnf_fvarLeaves m.wf fuel hwtb)
  exact structEtaCertWithFueled_step hcaps htower hct hav ihd ihis hexi hcw
    hwa hba hLa hCa hwb hbb hLb hCb hwr hbr hLr hCr hda hdb hwtba
    hokA hokB hokW (fun σ hσ => (heqW σ hσ) ▸ hmemB σ hσ) ρ hρ

/-! ## The unit-like row (post-repair)

`structEtaIrrel_of_claims` minus the fabricated spine: both sides'
inferred types whnf to the *same* family instance (the certificate's
own `isDefEqCore` run identifies them at `interp`), the telescope
certificates build the fit, and the repaired `UnitLaw` — its
superfluous family premise deleted, the ratified fix — collapses the
two members. -/

/-- **`StructUnitIrrel`, discharged from the field.** -/
theorem structUnitIrrel_of_claims {m : EnvModel V env}
    (hcaps : CapsOk m)
    (ihw : WhnfClaim μ m φ fuel) (ihd : DefEqClaim μ m φ fuel)
    (ihis : InferClaimIOS μ m φ fuel)
    (hexi : InferExistsIOS μ m φ fuel)
    (hwreads : WhnfReads m μ φ fuel) :
    StructUnitIrrel μ m φ fuel := by
  intro d a b Δa h hwa hba hLa hwb hbb hLb aa ba hCa hCb hda hdb
    hokA hokB ρ hρ
  obtain ⟨ta, wta, T, us', cvT, caps, tb, wtb, hta, hwta, hfn, hfind,
    hunit, hres, hlenArgs, hlenUs, hstrip, htb, hwtb, hdeq, hcerts⟩ :=
    ConLeche.structUnitCert_inv h
  -- one side's chain: the reading, membership and reduction package
  -- of an inferred type, whnf'd
  have side : ∀ (x tx wtx : Expr) (xa : AnnotTerm),
      ConLeche.inferTypeIO μ env fuel d x = .ok tx →
      whnf μ env fuel d tx = .ok wtx →
      Expr.WScoped d x → x.looseBVarsBounded 0 = true →
      Expr.LeavesBounded x → CtxOk m φ d Δa x →
      denoteMeta m.acval env φ d x = some xa →
      (∀ σ : Nat → V, Sat V Δa σ → WellDenotedV V σ xa) →
      ∃ wtxa, denoteMeta m.acval env φ d wtx = some wtxa ∧
        (∀ σ : Nat → V, Sat V Δa σ → WellDenotedV V σ wtxa) ∧
        (interp V ρ xa ∈ˢ interp V ρ wtxa) ∧
        Expr.WScoped d wtx ∧ wtx.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded wtx ∧ CtxOk m φ d Δa wtx := by
    intro x tx wtx xa htx hwtx hwx hbx hLx hCx hdx hokX
    have hwt : Expr.WScoped d tx :=
      ConLeche.inferTypeIO_WScoped m.wf fuel htx hwx
    have hbt : tx.looseBVarsBounded 0 = true :=
      ConLeche.inferTypeIO_looseBVars m.wf fuel htx hwx hbx hLx
    have hLt : Expr.LeavesBounded tx := fun l hl =>
      hLx l (ConLeche.inferTypeIO_fvarLeaves m.wf fuel htx hwx l hl)
    have hCt : CtxOk m φ d Δa tx :=
      hCx.of_subset (ConLeche.inferTypeIO_fvarLeaves m.wf fuel
        htx hwx)
    obtain ⟨txa, htxa⟩ :=
      hexi htx hwx hbx hLx hCx hdx
    obtain ⟨hokTx, hmemX⟩ := ihis htx hwx hbx hLx hCx hdx htxa hokX
    obtain ⟨wtxa, hwtxa⟩ := hwreads hwtx hwt hbt hLt
      (LeafReads.of_ctxOk hCt) htxa
    obtain ⟨hokW, heqW⟩ := ihw hwtx hwt hbt hLt hCt htxa hwtxa hokTx
    refine ⟨wtxa, hwtxa, hokW, ?_,
      ConLeche.whnf_WScoped m.wf fuel hwtx hwt,
      ConLeche.whnf_looseBVars m.wf fuel hwtx hbt,
      fun l hl => hLt l (ConLeche.whnf_fvarLeaves m.wf fuel hwtx l hl),
      hCt.of_subset (ConLeche.whnf_fvarLeaves m.wf fuel hwtx)⟩
    rw [← heqW ρ hρ]
    exact hmemX ρ hρ
  obtain ⟨wtaa, hwtaa, hokWA, hmemAW, hwrA, hbrA, hLrA, hCrA⟩ :=
    side a ta wta aa hta hwta hwa hba hLa hCa hda hokA
  obtain ⟨wtba, hwtba, hokWB, hmemBW, hwrB, hbrB, hLrB, hCrB⟩ :=
    side b tb wtb ba htb hwtb hwb hbb hLb hCb hdb hokB
  -- the certificate's defeq run identifies the two family instances
  have hEq : interp V ρ wtaa = interp V ρ wtba :=
    ihd hdeq hwrA hbrA hLrA hwrB hbrB hLrB hCrA hCrB hwtaa hwtba
      hokWA hokWB ρ hρ
  -- side a's reduct is the family applied to its parameters
  rw [show wta = Expr.mkAppN wta.getAppFn wta.getAppArgs from
    (ConLeche.Expr.mkAppN_getApp wta).symm, hfn] at hwtaa
  obtain ⟨vT, tsa, hvT, hspt, rfl⟩ := denoteMeta_mkAppN_inv hwtaa
  rw [denoteMeta, hfind] at hvT
  dsimp only at hvT
  split at hvT
  case isFalse => exact nomatch hvT
  case isTrue =>
  obtain rfl : vT = m.acval T (Level.substFn φ cvT.levelParams us') :=
    (Option.some.inj hvT).symm
  -- the (repaired) unit law, and its carried reading at depth `d`
  obtain ⟨TVa, hTVa, hokTVa, hlaw⟩ :=
    hcaps.2 T cvT caps hfind hunit hres φ us' hlenUs
  have hwfT := m.wf _ (ConLeche.Semantics.Env.find?_mem hfind)
  have hnfT : (cvT.type.instantiateLevelParams cvT.levelParams
      us').hasFvar = false := by
    rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hwfT.1
  have hbdT : (cvT.type.instantiateLevelParams cvT.levelParams
      us').looseBVarsBounded 0 = true := by
    rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]
    exact hwfT.2.2.2.1
  have hTVd : denoteMeta m.acval env φ d
      (cvT.type.instantiateLevelParams cvT.levelParams us')
      = some TVa :=
    denoteMeta_depth_of_closed m.acval_closed hnfT
      (fun k => denoteMeta_closed m.acval_erase m.cval_closed
        hnfT hbdT hTVa 1 k) hTVa d
  have hTw : Expr.WScoped d
      (cvT.type.instantiateLevelParams cvT.levelParams us') :=
    ConLeche.Expr.WScoped.of_not_hasFvar hnfT
  have hTL : Expr.LeavesBounded
      (cvT.type.instantiateLevelParams cvT.levelParams us') :=
    ConLeche.Expr.LeavesBounded.of_not_hasFvar hnfT
  have hTC : CtxOk m φ d Δa
      (cvT.type.instantiateLevelParams cvT.levelParams us') :=
    ⟨hCa.1, fun l hl => by
      rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnfT] at hl
      exact nomatch hl⟩
  have hpcT : PiChain wta.getAppArgs.length TVa := by
    rw [hlenArgs]
    exact piChain_of_stripPis caps.unitParams
      (ConLeche.Expr.stripPis_instantiateLevelParams_isSome
        cvT.levelParams us' caps.unitParams hstrip) hTVd
  obtain ⟨hohT, hoT⟩ := hoist_spine tsa hokWA
  obtain ⟨rest, hfitT⟩ :=
    certs_tele ihd ihis hexi _ wta.getAppArgs tsa TVa hcerts hpcT
      hTw hbdT hTL hTC hTVd (fun σ _ => hokTVa σ)
      (frame_spine hwrA hbrA hLrA hCrA) hspt hoT ρ hρ
  -- both members, at the folded family instance
  have hfold : ∀ (l : List AnnotTerm) (x : V),
      l.foldl (fun r y => SetTheory.app r (interp V ρ y)) x
        = (l.map (interp V ρ)).foldl SetTheory.app x := by
    intro l x; rw [List.foldl_map]
  have hmx : interp V ρ aa
      ∈ˢ (tsa.map (interp V ρ)).foldl SetTheory.app
          (interp V ρ (m.acval T (Level.substFn φ cvT.levelParams
            us'))) := by
    have := hmemAW
    rwa [interp_mkAppN, hfold] at this
  have hmy : interp V ρ ba
      ∈ˢ (tsa.map (interp V ρ)).foldl SetTheory.app
          (interp V ρ (m.acval T (Level.substFn φ cvT.levelParams
            us'))) := by
    have := hEq ▸ hmemBW
    rwa [interp_mkAppN, hfold] at this
  have hlenTs : (tsa.map (interp V ρ)).length = caps.unitParams := by
    rw [List.length_map, ← hspt.length, hlenArgs]
  exact hlaw ρ (tsa.map (interp V ρ)) rest (interp V ρ aa)
    (interp V ρ ba) hlenTs hfitT hmx hmy

end ConLeche.Model
