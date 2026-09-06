import Setlec.SetP.Step2.StuckP
import Setlec.SetP.Annot.EnvS2P
import Setlec.SetP.Step2.TowerKitP

/-!
# The stored-family rows of `stuckIrrel`'s cascade (task #161, caps
tier)

`StructEtaIrrelP` (`Step2/StuckP.lean`), discharged from `CapsOkP`
(`Annot/EnvS2P.lean`) plus the claims.  The v1 route is two files:
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

## The new sub-species: `certs_teleP`

`certs_teleR` (`Bridge/Certs.lean`) turns an `iotaCerts` run into a
`Tele` derivation; the P mirror turns it into a `TeleFitP`.  The
transposition is **not** clause-for-clause, and the reason is a
genuine divergence between the two fits:

* `TeleFitV` (`AnnotOkV.lean:292`) is *syntactic* — its cons peels
  `.pi A B` to `B.inst a`, exactly as `iotaCerts` peels
  `.forallE _ ty body` to `body.instantiate1 arg`.  The two walks
  step in lockstep, so `certs_teleR` needs no substitution lemma.
* `TeleFitP` (frozen) is *semantic* — its cons peels `.pi u v A B` to
  `B` under `cons a ρ`.  The checker's walk lands on the reading of
  `body.instantiate1 arg`, which is `bodya.inst aa`; recovering `bodya`
  under `cons` from `bodya.inst aa` is a substitution metatheorem, and
  **it is false without a guard**: at `bodya = .bvar 0` the
  instantiated reading is `aa` itself, which may well be a `.pi` when
  `bodya` is not — and the checker's walk happily continues into it
  (`ty = ∀ (X : Sort 1), X` certified against `[∀ y : A, B, arg]`).

`teleFitP_bvar_stuck` below is that gap, mechanized.  The guard that
closes it is `PiChainP n Ta` — the reading's first `n` heads are `.pi`
nodes — and the certificate *supplies* it: `structEtaCertWith_inv`'s
`(cvT.type.stripPis cnP).isSome = true` conjunct says exactly that the
former's type is a syntactic ∀-chain of length `cnP`, and a syntactic
∀-chain reads to a `PiChainP` (`piChainP_of_stripPis`).  So the frozen
statement is usable; what it costs is this file's substitution
metatheorem, which has no v1 counterpart because v1's fit never needed
one.  Recorded as a finding, not a wall.
-/

namespace Setlec.SetP
open Setlec.Semantics
open Setlec.SetModel

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.Semantics (AVExpr)
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  IndCaps projFnName inferTypeCore whnf isDefEqCore)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat} {fuel : Nat}

/-! ## The ∀-chain guard -/

/-- The reading's first `n` heads are `.pi` nodes.  The guard under
which `TeleFitP` can be un-instantiated (see the module docstring);
supplied at every call site by the certificate's `stripPis`
conjunct. -/
def PiChainP : Nat → AVExpr → Prop
  | 0, _ => True
  | n + 1, e =>
    match e with
    | .pi _ _ _ B => PiChainP n B
    | _ => False

@[simp] theorem piChainP_zero (e : AVExpr) : PiChainP 0 e := trivial

@[simp] theorem piChainP_succ_pi {n u v : Nat} {A B : AVExpr} :
    PiChainP (n + 1) (.pi u v A B) = PiChainP n B := rfl

/-- A ∀-chain is not a `.bvar`, and the walk cannot pretend otherwise:
this is the disequality that makes the guard load-bearing. -/
theorem piChainP_succ_inv {n : Nat} {e : AVExpr} (h : PiChainP (n + 1) e) :
    ∃ u v A B, e = .pi u v A B ∧ PiChainP n B := by
  match e with
  | .pi u v A B => exact ⟨u, v, A, B, rfl, h⟩
  | .bvar _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ _
  | .letE _ _ _ | .eqE _ _ _ | .proj _ _ | .prf => exact nomatch h

/-- Substitution preserves a ∀-chain: `inst` maps `.pi` to `.pi`. -/
theorem PiChainP.inst : ∀ {n : Nat} {e : AVExpr} (a : AVExpr) (k : Nat),
    PiChainP n e → PiChainP n (e.inst a k) := by
  intro n
  induction n with
  | zero => intro _ _ _ _; trivial
  | succ n ih =>
    intro e a k h
    obtain ⟨u, v, A, B, rfl, hB⟩ := piChainP_succ_inv h
    exact ih a (k + 1) hB

/-- A ∀-chain of a list's length peels along it (task #175 W4c: the
tower typing law's residual, named without a checker run to read it
off). -/
theorem peelPis_of_piChainP : ∀ (as : List AVExpr) {T : AVExpr},
    PiChainP as.length T →
      ∃ rest, Setlec.SetP.AVExpr.peelPis T as = some rest
  | [], T, _ => ⟨T, rfl⟩
  | a :: as, T, h => by
    obtain ⟨u, v, A, B, rfl, hB⟩ := piChainP_succ_inv h
    exact peelPis_of_piChainP as (PiChainP.inst a 0 hB)

/-! ## FINDING: the fit's un-instantiation needs the guard

`TeleFitP`'s semantic cons cannot follow the checker's syntactic walk
through a `.bvar`-headed body.  The mechanized gap. -/

/-- **A `.bvar 0` body admits no fit past its own binder.**  The
checker's walk, by contrast, peels `(.bvar 0).instantiate1 a` to `a`
and keeps going — so `TeleFitP` at an unguarded reading is strictly
weaker than the certificate.  (Contrast `TeleFitV`, whose cons peels
`(.bvar 0).inst a = a` and continues in step.) -/
theorem teleFitP_bvar_stuck {ρ : Nat → V} {u v : Nat} {A : AVExpr}
    {x y : V} {ys : List V} {rest : V} :
    ¬ TeleFitP V ρ (.pi u v A (.bvar 0)) (x :: y :: ys) rest := by
  rintro (_ | ⟨-, hfit⟩)
  exact nomatch hfit

/-! ## The un-instantiation metatheorem -/

/-- The empty fit pins its residual (the inversion `cases` cannot do
in place, because the fit's type index is not a variable there). -/
theorem teleFitP_nil_inv {ρ : Nat → V} {T : AVExpr} {rest : V}
    (h : TeleFitP V ρ T [] rest) : rest = interp2 V ρ T := by
  cases h; rfl

/-- **The fit un-instantiates, under the ∀-chain guard**: a fit of the
*substituted* reading at `ρ` is a fit of the reading itself at the
environment `inst` corresponds to.  The `.pi`-clause commutations are
`interp2_inst`, `shiftE_succ_cons` and `cons_instE` — `Annot/Ok2.lean`'s
`AnnotOk2_inst` idiom, at the fit. -/
theorem teleFitP_of_inst {aa : AVExpr} :
    ∀ {L : List V} {E : AVExpr} {k : Nat} {ρ : Nat → V} {rest : V},
      PiChainP L.length E →
      TeleFitP V ρ (E.inst aa k) L rest →
      TeleFitP V (instE k (interp2 V (shiftE k 0 ρ) aa) ρ) E L rest := by
  intro L
  induction L with
  | nil =>
    intro E k ρ rest _ h
    obtain rfl : rest = interp2 V ρ (E.inst aa k) := teleFitP_nil_inv h
    rw [interp2_inst]
    exact .nil
  | cons y ys ih =>
    intro E k ρ rest hpc h
    obtain ⟨u, v, A, B, rfl, hB⟩ := piChainP_succ_inv hpc
    rw [AVExpr.inst_pi] at h
    cases h with
    | cons hmem hfit =>
      refine .cons (by rwa [interp2_inst] at hmem) ?_
      have hrec := ih (E := B) (k := k + 1) (ρ := cons y ρ) hB hfit
      rw [shiftE_succ_cons] at hrec
      rw [cons_instE]
      exact hrec

/-- The outermost-binder form, the one `certs_teleP` fires. -/
theorem teleFitP_of_inst0 {aa : AVExpr} {L : List V} {E : AVExpr}
    {ρ : Nat → V} {rest : V} (hpc : PiChainP L.length E)
    (h : TeleFitP V ρ (E.inst aa) L rest) :
    TeleFitP V (cons (interp2 V ρ aa) ρ) E L rest := by
  have := teleFitP_of_inst hpc h
  rwa [shiftE_zero_zero, instE_zero] at this

/-! ## `certs_teleP` — a certified spine fits the reading

`certs_teleR`'s mirror.  Two deltas beyond the substitution
metatheorem above:

* the spine's **readings are an input**, not an output.  v1's
  `InferClaimsR` *produces* a denotation; `InferClaims2P` consumes
  one.  Every call site already holds the readings (the subject whose
  arguments these are read, and `denoteP_mkAppN_inv` splits that), so
  the walk takes `DenoteSpineP` as a premise — which also deletes
  `DenoteSpine.det`, v1's reconciliation of two independently produced
  spines.
* the walk carries the **grading** of the running type, because
  `DefEqClaims2P` demands `AnnotOkP` of both comparands where
  `DefEqClaimsR` demands nothing.  It is hoisted through the `.pi`
  clause and transported across the substitution by
  `AnnotOkP_inst0` — the same two moves the literal tier's
  establishment makes. -/

/-- **A certified spine fits the type's reading.**  One step is
`InferReadsP` (the argument's type reads), `InferClaims2P` (it is
graded and the argument inhabits it) and `DefEqClaims2P` (it is the
domain) — the checker's own order, exactly as in `certs_teleR`. -/
theorem certs_teleP {m : EnvS2Core V env}
    (ihd : DefEqClaims2P μ m φ fuel) (ihis : InferClaimsIOS2P μ m φ fuel)
    (hexi : InferExistsIOSP μ m φ fuel) :
    ∀ {d : Nat} {Δa : List AVExpr} (ty : Expr) (args : List Expr)
      (vs : List AVExpr) (Ta : AVExpr),
      Setlec.iotaCertsP μ env fuel d false ty args = .ok true →
      PiChainP args.length Ta →
      Expr.WScoped d ty → ty.looseBVarsBounded 0 = true →
      Expr.LeavesBounded ty → CtxOkP m φ d Δa ty →
      denoteP m.acval env φ d ty = some Ta →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ Ta) →
      (∀ x ∈ args, Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ CtxOkP m φ d Δa x) →
      DenoteSpineP m.acval env φ d args vs →
      (∀ x ∈ vs, ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ x) →
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        ∃ rest, TeleFitP V ρ Ta (vs.map (interp2 V ρ)) rest := by
  intro d Δa ty args
  induction args generalizing ty with
  | nil =>
    intro vs Ta _ _ _ _ _ _ _ _ _ hsp _ ρ _
    cases hsp
    exact ⟨interp2 V ρ Ta, .nil⟩
  | cons a as ih =>
    intro vs Ta hc hpc hwty hbty hLbty hCty hity hokT hargs hsp hokvs
    match ty, hc, hwty, hbty, hLbty, hCty, hity with
    | .bvar _, hc, _, _, _, _, _ => exact nomatch hc
    | .fvar _ _ _, hc, _, _, _, _, _ => exact nomatch hc
    | .sort _, hc, _, _, _, _, _ => exact nomatch hc
    | .const _ _, hc, _, _, _, _, _ => exact nomatch hc
    | .app _ _, hc, _, _, _, _, _ => exact nomatch hc
    | .lam _ _ _ _, hc, _, _, _, _, _ => exact nomatch hc
    | .letE _ _ _ _, hc, _, _, _, _, _ => exact nomatch hc
    | .lit _, hc, _, _, _, _, _ => exact nomatch hc
    | .proj _ _ _, hc, _, _, _, _, _ => exact nomatch hc
    | .forallE n dom body mb, hc, hwty, hbty, hLbty, hCty, hity => ?_
    -- the certificate's step, and the argument's frames
    obtain ⟨ta, hta, hde, hrestc⟩ := Setlec.iotaCerts_step_inv hc
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
    have hCdom : CtxOkP m φ d Δa dom :=
      hCty.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl])
    obtain ⟨doma, bodya, hdoma, hbodya, rfl⟩ := denoteP_forallE_inv hity
    have hpcB : PiChainP as.length bodya := hpc
    -- the reading's grading, hoisted through the `.pi` clause
    have hokDom : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ doma :=
      fun ρ hρ =>
        ⟨((AnnotOk2_pi V ρ 0 _ doma bodya) ▸ (hokT ρ hρ).1).1,
          ((AnnotValidV_pi V ρ 0 _ doma bodya) ▸ (hokT ρ hρ).2).1⟩
    have hokBody : ∀ (ρ : Nat → V), Sat2 V Δa ρ →
        ∀ x, x ∈ˢ interp2 V ρ doma → AnnotOkP V (cons x ρ) bodya :=
      fun ρ hρ x hx =>
        ⟨((AnnotOk2_pi V ρ 0 _ doma bodya) ▸ (hokT ρ hρ).1).2 x hx,
          ((AnnotValidV_pi V ρ 0 _ doma bodya) ▸ (hokT ρ hρ).2).2.1 x hx⟩
    -- the argument's inferred type reads, is graded, and holds it
    obtain ⟨taa, htaa⟩ :=
      hexi hta haw hab haLb haC haa
    have hokA : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ aa :=
      hokvs aa List.mem_cons_self
    obtain ⟨hokTa, hmemA⟩ := ihis hta haw hab haLb haC haa htaa hokA
    have hwta : Expr.WScoped d ta :=
      Setlec.inferTypeIO_WScoped m.wf fuel hta haw
    have hbta : ta.looseBVarsBounded 0 = true :=
      Setlec.inferTypeIO_looseBVars m.wf fuel hta haw hab haLb
    have hLta : Expr.LeavesBounded ta := fun l hl =>
      haLb l (Setlec.inferTypeIO_fvarLeaves m.wf fuel hta haw l hl)
    have hCta : CtxOkP m φ d Δa ta :=
      haC.of_subset (Setlec.inferTypeIO_fvarLeaves m.wf fuel hta haw)
    -- the certificate against the domain
    have hdeq : ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ taa = interp2 V ρ doma :=
      ihd hde hwta hbta hLta hdomw hdomb hLbdom hCta hCdom htaa hdoma
        hokTa hokDom
    -- the residual reads, by β on the reading
    have hbody' : denoteP m.acval env φ d (body.instantiate1 a)
        = some (bodya.inst aa) := by
      rw [denoteP_beta m.acval_closed (acval_inst_self m)
        (n := n) (ty := dom) hbodyw.fvarsBelow haw hab haa 0, hbodya]
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
    have hCbody : CtxOkP m φ d Δa (body.instantiate1 a) := by
      refine ⟨hCty.1, fun l hl => ?_⟩
      rcases Expr.fvarLeaves_instantiate1 body 0 hl with hl' | hl'
      · exact hCty.2 l (by simp [Expr.fvarLeaves, hl'])
      · exact haC.2 l hl'
    have hokBody' : ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOkP V ρ (bodya.inst aa) := fun ρ hρ =>
      (AnnotOkP_inst0 (hokA ρ hρ)).mpr
        (hokBody ρ hρ _ ((hdeq ρ hρ) ▸ hmemA ρ hρ))
    -- the tail, and the fit
    intro ρ hρ
    obtain ⟨rest, hfit⟩ :=
      ih (body.instantiate1 a) _ _ hrestc (hpcB.inst aa 0) hwbody hbbody
        hLbbody hCbody hbody' hokBody'
        (fun x hx => hargs x (List.mem_cons_of_mem a hx)) hsp'
        (fun x hx => hokvs x (List.mem_cons_of_mem aa hx)) ρ hρ
    refine ⟨rest, .cons ((hdeq ρ hρ) ▸ hmemA ρ hρ) ?_⟩
    refine teleFitP_of_inst0 (aa := aa) ?_ hfit
    rw [List.length_map, ← hsp'.length]
    exact hpcB

/-! ## The spine kit, completed

`StuckP.lean` has `DenoteSpineP`, its length, the inversion and the
congruence.  The η row needs four more: the two list splits, the
append, the mapped spine (`DenoteSpine.map_list`'s mirror) and the
*constructing* direction of the application inversion. -/

theorem DenoteSpineP.take {acval : Name → (Name → Nat) → AVExpr}
    {d : Nat} {as : List Expr} {vs : List AVExpr}
    (h : DenoteSpineP acval env φ d as vs) :
    ∀ n, DenoteSpineP acval env φ d (as.take n) (vs.take n) := by
  induction h with
  | nil => intro n; simpa using DenoteSpineP.nil
  | @cons a v as vs ha _ ih =>
    intro n
    cases n with
    | zero => exact DenoteSpineP.nil
    | succ n => exact DenoteSpineP.cons ha (ih n)

theorem DenoteSpineP.drop {acval : Name → (Name → Nat) → AVExpr}
    {d : Nat} {as : List Expr} {vs : List AVExpr}
    (h : DenoteSpineP acval env φ d as vs) :
    ∀ n, DenoteSpineP acval env φ d (as.drop n) (vs.drop n) := by
  induction h with
  | nil => intro n; simpa using DenoteSpineP.nil
  | @cons a v as vs ha htl ih =>
    intro n
    cases n with
    | zero => exact DenoteSpineP.cons ha htl
    | succ n => exact ih n

theorem DenoteSpineP.append {acval : Name → (Name → Nat) → AVExpr}
    {d : Nat} {as bs : List Expr} {vs ws : List AVExpr}
    (h : DenoteSpineP acval env φ d as vs)
    (h2 : DenoteSpineP acval env φ d bs ws) :
    DenoteSpineP acval env φ d (as ++ bs) (vs ++ ws) := by
  induction h with
  | nil => exact h2
  | cons ha _ ih => exact DenoteSpineP.cons ha ih

/-- A mapped spine reads pointwise (`DenoteSpine.map_list`'s mirror). -/
theorem DenoteSpineP.map_list {acval : Name → (Name → Nat) → AVExpr}
    {d : Nat} {g : Nat → Expr} {G : Nat → AVExpr} :
    ∀ l : List Nat, (∀ j ∈ l, denoteP acval env φ d (g j) = some (G j)) →
      DenoteSpineP acval env φ d (l.map g) (l.map G) := by
  intro l
  induction l with
  | nil => intro _; exact DenoteSpineP.nil
  | cons x xs ih =>
    intro h
    exact DenoteSpineP.cons (h x (by simp))
      (ih fun j hj => h j (by simp [hj]))

/-- **The application spine reads, constructing direction** —
`denoteP_mkAppN_inv`'s converse, the one the fabricated projection
spine needs. -/
theorem denoteP_mkAppN {acval : Name → (Name → Nat) → AVExpr} {d : Nat}
    {as : List Expr} {vs : List AVExpr}
    (h : DenoteSpineP acval env φ d as vs) :
    ∀ {f : Expr} {fa : AVExpr}, denoteP acval env φ d f = some fa →
      denoteP acval env φ d (Expr.mkAppN f as) = some (AVExpr.mkAppN fa vs) := by
  induction h with
  | nil => intro f fa hf; exact hf
  | cons ha _ ih =>
    intro f fa hf
    exact ih (by rw [denoteP_app, hf, ha]; rfl)

/-! ## From a fit to a graded application

The P currency's own tax, and the CapsP docstring's prediction made
good: a `TeleFitP` plus the *type's* grading yields the applied spine's
grading and its residual membership, one `app_mem_piR` per argument
whose `v = 0` fibre premise is `AnnotValidV_pi`'s third clause.  The
type's environment `σ` is kept separate from the spine's `ρ` — the fit
peels into `cons`-extensions of `σ` while the application stays at
`ρ`, which is exactly the divergence `teleFitP_of_inst` had to
mediate on the other side. -/

theorem annotOkP_mkAppN_of_fit {ρ : Nat → V} :
    ∀ (vs : List AVExpr) {Ta f : AVExpr} {σ : Nat → V} {rest : V},
      AnnotOkP V σ Ta → AnnotOkP V ρ f →
      (∀ x ∈ vs, AnnotOkP V ρ x) →
      interp2 V ρ f ∈ˢ interp2 V σ Ta →
      TeleFitP V σ Ta (vs.map (interp2 V ρ)) rest →
      AnnotOkP V ρ (AVExpr.mkAppN f vs) ∧
        interp2 V ρ (AVExpr.mkAppN f vs) ∈ˢ rest := by
  intro vs
  induction vs with
  | nil =>
    intro Ta f σ rest _ hf _ hmem hfit
    obtain rfl : rest = interp2 V σ Ta := teleFitP_nil_inv hfit
    exact ⟨hf, hmem⟩
  | cons x xs ih =>
    intro Ta f σ rest hokT hf hoks hmem hfit
    simp only [List.map_cons] at hfit
    cases hfit with
    | @cons _ u v A B _ _ _ hx hfit' =>
      have hokA : AnnotOkP V σ A :=
        ⟨((AnnotOk2_pi V σ u v A B) ▸ hokT.1).1,
          ((AnnotValidV_pi V σ u v A B) ▸ hokT.2).1⟩
      have hokB : ∀ y, y ∈ˢ interp2 V σ A → AnnotOkP V (cons y σ) B :=
        fun y hy =>
          ⟨((AnnotOk2_pi V σ u v A B) ▸ hokT.1).2 y hy,
            ((AnnotValidV_pi V σ u v A B) ▸ hokT.2).2.1 y hy⟩
      have hfib : v = 0 → ∀ y, y ∈ˢ interp2 V σ A →
          interp2 V (cons y σ) B ∈ˢ (univZero : V) :=
        ((AnnotValidV_pi V σ u v A B) ▸ hokT.2).2.2
      rw [interp2_pi] at hmem
      have hokx : AnnotOkP V ρ x := hoks x List.mem_cons_self
      have hstep : AnnotOkP V ρ (.app f x) := by
        refine ⟨?_, ?_⟩
        · rw [AnnotOk2_app]
          exact ⟨hf.1, hokx.1, v, interp2 V σ A,
            (fun y => interp2 V (cons y σ) B), hmem, hx, hfib⟩
        · rw [AnnotValidV_app]; exact ⟨hf.2, hokx.2⟩
      have hmem' : interp2 V ρ (.app f x)
          ∈ˢ interp2 V (cons (interp2 V ρ x) σ) B := by
        rw [interp2_app]
        exact app_mem_piR hmem hx hfib
      -- (`mkAppN f (x :: xs) = mkAppN (.app f x) xs` is definitional)
      exact ih (hokB _ hx) hstep
        (fun y hy => hoks y (List.mem_cons_of_mem x hy)) hmem' hfit'

/-! ## The ∀-chain guard, supplied by the certificate -/

/-- **A syntactic ∀-telescope reads to a ∀-chain.**  `stripPis n`
succeeding is exactly `PiChainP n` of the reading — the certificate's
own conjunct, converted. -/
theorem piChainP_of_stripPis {acval : Name → (Name → Nat) → AVExpr} :
    ∀ (n : Nat) {d : Nat} {e : Expr} {ea : AVExpr},
      (e.stripPis n).isSome = true →
      denoteP acval env φ d e = some ea → PiChainP n ea := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _; trivial
  | succ n ih =>
    intro d e ea hs hd
    match e, hs with
    | .bvar _, hs => exact nomatch hs
    | .fvar _ _ _, hs => exact nomatch hs
    | .sort _, hs => exact nomatch hs
    | .const _ _, hs => exact nomatch hs
    | .app _ _, hs => exact nomatch hs
    | .lam _ _ _ _, hs => exact nomatch hs
    | .letE _ _ _ _, hs => exact nomatch hs
    | .lit _, hs => exact nomatch hs
    | .proj _ _ _, hs => exact nomatch hs
    | .forallE nm ty bd mb, hs =>
      obtain ⟨ta, ba, -, hba, rfl⟩ := denoteP_forallE_inv hd
      simp only [Setlec.Expr.stripPis, Option.isSome_map] at hs
      exact ih (Setlec.Expr.stripPis_instantiate1_isSome n 0 hs) hba

/-! ## The stored structure's η row

`structEtaCertWith_stepR` and `sndDeqStructEta`, fused.  What the
semantic argument actually consumes is small: the family is stored
(`EtaFamilyStored`, built from the certificate's constructor lookup and
its per-field recursor lookups), the former's telescope fits
(`certs_teleP` on the `iotaCerts` conjunct), and the two argument
lists are certified (`map_interp2_of_defEqListP` twice).  The per-field
telescopes appear only to *grade* the fabricated projection spine —
`DefEqClaims2P` demands `AnnotOkP` of both comparands where
`DefEqClaimsR` demands nothing — and they are consumed through
`annotOkP_mkAppN_of_fit`, not through any function-valued
quantification, so `choose_fun` has no counterpart here. -/

/-- **The η certificate's semantic content, at a given reduced type**
(`structEtaCertWith_stepR`'s mirror; factored out of
`structEtaIrrelP_of_claims` for the iota tier's major rescue, which
holds a `structEtaCertWithP` run whose `tmaj` was computed by
`majorToCtor` and must not be recomputed — the same reason v1
factored its own).

The stored η law fires at the reduced type's parameter spine; the
fabricated value spine is `etaFabArgs2`, and the certificate's two
`defEqList` runs identify it with the constructor application's own
arguments. -/
theorem structEtaCertWithP_step {m : EnvS2Core V env}
    (hcaps : CapsOkP m) (htower : TowerOkP m φ) (hct : ConstTypeP m φ)
    (hav : AcvalValidP m)
    (ihd : DefEqClaims2P μ m φ fuel) (ihis : InferClaimsIOS2P μ m φ fuel)
    (hexi : InferExistsIOSP μ m φ fuel)
    {d : Nat} {Δa : List AVExpr} {a b wtb : Expr}
    {aa ba wtba : AVExpr}
    (hcw : Setlec.structEtaCertWithP μ env fuel d a b wtb = .ok true)
    (hwa : Expr.WScoped d a) (hba : a.looseBVarsBounded 0 = true)
    (hLa : Expr.LeavesBounded a) (hCa : CtxOkP m φ d Δa a)
    (hwb : Expr.WScoped d b) (hbb : b.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded b) (hCb : CtxOkP m φ d Δa b)
    (hwr : Expr.WScoped d wtb) (hbr : wtb.looseBVarsBounded 0 = true)
    (hLr : Expr.LeavesBounded wtb) (hCr : CtxOkP m φ d Δa wtb)
    (hda : denoteP m.acval env φ d a = some aa)
    (hdb : denoteP m.acval env φ d b = some ba)
    (hwtba : denoteP m.acval env φ d wtb = some wtba)
    (hokA : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ aa)
    (hokB : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ba)
    (hokW : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ wtba)
    (hmemBW : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      interp2 V ρ ba ∈ˢ interp2 V ρ wtba)
    (ρ : Nat → V) (hρ : Sat2 V Δa ρ) :
    interp2 V ρ aa = interp2 V ρ ba := by
  obtain ⟨c, us, cvc, cnP, cnF, T, us', cvT, caps, hfna, hfc, hlena,
    hfnb, hfT, heta, hectr, hepar, hefld, hresT, hresc, hlenb, hlenus,
    hlpc, hstrip, hslots, hlev, hcertT, hprojs, hdefL1, -, hdefL2⟩ :=
    Setlec.structEtaCertWith_inv hcw
  have hmemB := hmemBW
  -- the reduced type is the family applied to its parameters
  rw [show wtb = Expr.mkAppN wtb.getAppFn wtb.getAppArgs from
    (Setlec.Expr.mkAppN_getApp wtb).symm, hfnb] at hwtba
  obtain ⟨vT, tsa, hvT, hspt, rfl⟩ := denoteP_mkAppN_inv hwtba
  rw [denoteP, hfT] at hvT
  dsimp only at hvT
  split at hvT
  case isFalse => exact nomatch hvT
  case isTrue =>
  obtain rfl : vT = m.acval T (Level.substFn φ cvT.levelParams us') := (Option.some.inj hvT).symm
  -- the constructor side is the constructor applied to its arguments
  rw [show a = Expr.mkAppN a.getAppFn a.getAppArgs from
    (Setlec.Expr.mkAppN_getApp a).symm, hfna] at hda
  obtain ⟨vf, asa, hvf, hspa, rfl⟩ := denoteP_mkAppN_inv hda
  rw [denoteP, hfc] at hvf
  dsimp only at hvf
  split at hvf
  case isFalse => exact nomatch hvf
  case isTrue =>
  obtain rfl : vf = m.acval c (Level.substFn φ cvc.levelParams us) :=
    (Option.some.inj hvf).symm
  -- the two instantiations agree (`sndDeqStructEta`'s `hψ`)
  have hψc : Level.substFn φ cvc.levelParams us = (Level.substFn φ cvT.levelParams us') := by
    rw [hlpc]
    exact Setlec.Level.substFn_congr (Setlec.Level.isEquivList_sound hlev φ)
  -- the slot discipline (task #175 W4c): every slot is a tower entry
  -- (and there is one), or every slot is a projection function — an
  -- all-tower family with no field is the latter case, nothing being
  -- fabricated either way
  have hkind : (Setlec.towerSlotsAll env T cnF = true ∧ 0 < cnF) ∨
      ((∀ j, j < cnF → ∃ cvp mIp rPp rulesp,
          env.find? (projFnName T j) = some (.recInfo cvp mIp rPp rulesp)) ∧
        (Setlec.towerSlotsAll env T cnF = true → cnF = 0)) := by
    by_cases htow : Setlec.towerSlotsAll env T cnF = true
    · by_cases h0 : 0 < cnF
      · exact .inl ⟨htow, h0⟩
      · exact .inr ⟨fun j hj => absurd hj (by omega), fun _ => by omega⟩
    · have hrec : Setlec.recSlotsAll env T cnF = true := by
        simpa [htow] using hslots
      exact .inr ⟨fun j hj => Setlec.recSlotsAll_slot hrec j hj,
        fun h => absurd h htow⟩
  -- the former's type: closed, so its reading at depth `0` is its
  -- reading at every depth, and all four frames are free
  have hwfT := m.wf _ (Setlec.Semantics.Env.find?_mem hfT)
  have hnfT : (cvT.type.instantiateLevelParams cvT.levelParams us').hasFvar
      = false := by
    rw [Setlec.Expr.hasFvar_instantiateLevelParams]; exact hwfT.1
  have hbdT : (cvT.type.instantiateLevelParams cvT.levelParams
      us').looseBVarsBounded 0 = true := by
    rw [Setlec.Expr.looseBVarsBounded_instantiateLevelParams]
    exact hwfT.2.2.2.1
  have hTw : Expr.WScoped d
      (cvT.type.instantiateLevelParams cvT.levelParams us') :=
    Setlec.Expr.WScoped.of_not_hasFvar hnfT
  have hTL : Expr.LeavesBounded
      (cvT.type.instantiateLevelParams cvT.levelParams us') :=
    Setlec.Expr.LeavesBounded.of_not_hasFvar hnfT
  have hTC : CtxOkP m φ d Δa
      (cvT.type.instantiateLevelParams cvT.levelParams us') :=
    ⟨hCa.1, fun l hl => by
      rw [Setlec.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnfT] at hl
      exact nomatch hl⟩
  obtain ⟨hohT, hoT⟩ := hoistP_spine tsa hokW
  obtain ⟨hohA, hoA⟩ := hoistP_spine asa hokA
  -- the former's telescope fits the parameter spine (`certs_teleP` on
  -- the certificate's former conjunct), at whichever law's reading
  have hfitOf : ∀ TVa : AVExpr,
      denoteP m.acval env φ 0
        (cvT.type.instantiateLevelParams cvT.levelParams us') = some TVa →
      (∀ σ : Nat → V, AnnotOkP V σ TVa) →
      ∃ rest, TeleFitP V ρ TVa (tsa.map (interp2 V ρ)) rest := by
    intro TVa hTVa hokTVa
    have hTVd : denoteP m.acval env φ d
        (cvT.type.instantiateLevelParams cvT.levelParams us') = some TVa :=
      denoteP_depth_of_closed m.acval_closed hnfT
        (fun k => denoteP_closed m.acval_erase m.cval_closed
          hnfT hbdT hTVa 1 k) hTVa d
    -- the ∀-chain guard, from the certificate's `stripPis` conjunct
    have hpcT : PiChainP wtb.getAppArgs.length TVa := by
      rw [hlenb]
      exact piChainP_of_stripPis cnP
        (Setlec.Expr.stripPis_instantiateLevelParams_isSome
          cvT.levelParams us' cnP hstrip) hTVd
    exact certs_teleP ihd ihis hexi _ wtb.getAppArgs tsa TVa hcertT hpcT
      hTw hbdT hTL hTC hTVd (fun σ _ => hokTVa σ)
      (frame_spineP hwr hbr hLr hCr) hspt hoT ρ hρ
  -- the fold form both sides are read in
  have hfold : ∀ (l : List AVExpr) (x : V),
      l.foldl (fun r y => SetTheory.app r (interp2 V ρ y)) x
        = (l.map (interp2 V ρ)).foldl SetTheory.app x := by
    intro l x; rw [List.foldl_map]
  -- the stuck side inhabits the family instance
  have hmemFam : interp2 V ρ ba
      ∈ˢ (tsa.map (interp2 V ρ)).foldl SetTheory.app
          (interp2 V ρ (m.acval T (Level.substFn φ cvT.levelParams us'))) := by
    have := hmemB ρ hρ
    rwa [interp2_mkAppN, hfold] at this
  have hlenTs : (tsa.map (interp2 V ρ)).length = caps.etaParams := by
    rw [List.length_map, ← hspt.length, hlenb, hepar]
  -- the fabricated projection spine's subject list: it reads, and it
  -- is graded
  have hspTb : DenoteSpineP m.acval env φ d (wtb.getAppArgs ++ [b])
      (tsa ++ [ba]) := hspt.append (DenoteSpineP.cons hdb DenoteSpineP.nil)
  have hframeTb : ∀ x ∈ wtb.getAppArgs ++ [b],
      Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ CtxOkP m φ d Δa x := by
    intro x hx
    rcases List.mem_append.mp hx with hx' | hx'
    · exact frame_spineP hwr hbr hLr hCr x hx'
    · rcases List.mem_singleton.mp hx' with rfl
      exact ⟨hwb, hbb, hLb, hCb⟩
  have hokTb' : ∀ x ∈ tsa ++ [ba], ∀ σ : Nat → V, Sat2 V Δa σ →
      AnnotOkP V σ x := by
    intro x hx
    rcases List.mem_append.mp hx with hx' | hx'
    · exact hoT x hx'
    · rcases List.mem_singleton.mp hx' with rfl; exact hokB
  -- the parameter halves of the two certified lists, pointwise
  have htake : (asa.take cnP).map (interp2 V ρ) = tsa.map (interp2 V ρ) :=
    map_interp2_of_defEqListP ihd hdefL1
      (fun x hx => frame_spineP hwa hba hLa hCa x (List.mem_of_mem_take hx))
      (frame_spineP hwr hbr hLr hCr) (hspa.take cnP) hspt
      (fun x hx => hoA x (List.mem_of_mem_take hx)) hoT ρ hρ
  rcases hkind with ⟨htow, h0⟩ | ⟨hrecs, htow0⟩
  · -- TOWER-BACKED SLOTS (task #175 W4c): the fabricated projections
    -- are `.proj T j b` nodes reading to `projAV j`, graded by each
    -- entry's typing law; the η law is the entry law's clause (C),
    -- read through slot `0`
    have hslotE : ∀ j, j < cnF → ∃ entry : ProjEntry,
        env.findProj? T j = some entry ∧ entry.tower = true ∧
        entry.levelParams = cvT.levelParams ∧
        (entry.ty.stripPis (wtb.getAppArgs.length + 1)).isSome = true := by
      intro j hj
      rcases Setlec.structEtaProjCerts_inv _ hprojs j (List.mem_range.mpr hj) with
        ⟨cvp, mIp, rPp, rulesp, hfp, -, -, -⟩ | ⟨entry, hfp, htw, hlpe, hstrpe, -⟩
      · exfalso
        obtain ⟨e, hfe, -⟩ := Setlec.towerSlotsAll_slot htow j hj
        have := Setlec.Env.findProj?_some hfe
        rw [hfp] at this
        exact nomatch this
      · exact ⟨entry, by unfold Setlec.Env.findProj?; rw [hfp], htw, hlpe, hstrpe⟩
    obtain ⟨e0, hfe0, htw0⟩ := Setlec.towerSlotsAll_slot htow 0 h0
    obtain ⟨-, -, -, -, ⟨cvT', capsT', hfT', hlpsT', -, hctr', hpar', hfld'⟩,
      -, -, -, -, -, hetaL⟩ := htower T 0 e0 hfe0 htw0
    have hcvT' : cvT' = cvT := by
      rw [hfT] at hfT'
      exact (ConstantInfo.indInfo.inj (Option.some.inj hfT')).1.symm
    have hcapsT' : capsT' = caps := by
      rw [hfT] at hfT'
      exact (ConstantInfo.indInfo.inj (Option.some.inj hfT')).2.symm
    rw [hcvT'] at hlpsT'
    rw [hcapsT'] at hctr' hpar' hfld'
    obtain ⟨TVa, hTVa, hokTVa, hlaw⟩ :=
      hetaL cvT caps hfT us' (by rw [← hlpsT']; exact hlenus)
    obtain ⟨rest, hfitT⟩ := hfitOf TVa hTVa hokTVa
    have hb := hlaw ρ (tsa.map (interp2 V ρ)) rest (interp2 V ρ ba)
      (by rw [hlenTs, hpar']) hfitT (by rw [← hlpsT']; exact hmemFam)
    have hprojden : ∀ j ∈ List.range cnF,
        denoteP m.acval env φ d (.proj T j b) = some (projAV j ba) := by
      intro j hj
      obtain ⟨entry, hfe, htw, -, -⟩ := hslotE j (List.mem_range.mp hj)
      exact denoteP_proj_tower hfe htw hdb
    have hokProj : ∀ x ∈ (List.range cnF).map (fun j => projAV j ba),
        ∀ σ : Nat → V, Sat2 V Δa σ → AnnotOkP V σ x := by
      intro x hx σ hσ
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      obtain ⟨entry, hfe, htw, hlpe, hstrpe⟩ := hslotE j (List.mem_range.mp hj)
      obtain ⟨-, -, -, -, ⟨cvTj, capsTj, hfTj, -, hetaj, -, hparj, -⟩, hO5j, _,
        -, -, hlawj, -⟩ := htower T j entry hfe htw
      have hcapsTj : capsTj = caps := by
        rw [hfT] at hfTj
        exact (ConstantInfo.indInfo.inj (Option.some.inj hfTj)).2.symm
      rw [hcapsTj] at hparj hetaj
      -- the family is not a proposition (it claims η), so the guard
      -- holds at every valuation by O5
      have hgj : TowerGuardAt φ entry us' :=
        towerGuardAt_of hO5j (fun hp => by rw [heta, hp] at hetaj; exact nomatch hetaj)
      obtain ⟨⟨Ta, hTa, hA⟩, -⟩ := hlawj us' (by rw [hlpe]; exact hlenus)
      obtain ⟨hTad, -⟩ := towerEntry_ty_at_depth hfe hTa
      -- the entry type's reading is a ∀-chain of the subject list's
      -- length, so it peels along it
      have hpc : PiChainP (tsa ++ [ba]).length Ta := by
        rw [List.length_append, List.length_singleton, ← hspt.length]
        exact piChainP_of_stripPis _
          (Setlec.Expr.stripPis_instantiateLevelParams_isSome
            entry.levelParams us' _ hstrpe) (hTad d)
      obtain ⟨restj, hpeel⟩ := peelPis_of_piChainP _ hpc
      have hlenVs : tsa.length = entry.numParams := by
        rw [← hspt.length, hlenb, ← hepar, hparj]
      rw [hlpe] at hA
      exact (hA hgj σ tsa ba restj hlenVs (hokW σ hσ) (hokB σ hσ) (hmemB σ hσ)
        hpeel).1
    have hframeProj : ∀ x ∈ (List.range cnF).map (fun j => Expr.proj T j b),
        Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
          Expr.LeavesBounded x ∧ CtxOkP m φ d Δa x := by
      intro x hx
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
      exact ⟨by simpa [Expr.WScoped] using hwb,
        by simpa [Expr.looseBVarsBounded] using hbb,
        fun l hl => hLb l (by simpa [Expr.fvarLeaves] using hl),
        ⟨hCb.1, fun l hl => hCb.2 l (by simpa [Expr.fvarLeaves] using hl)⟩⟩
    rw [Setlec.etaProjs, if_pos htow] at hdefL2
    have hdrop : (asa.drop cnP).map (interp2 V ρ)
        = ((List.range cnF).map fun j => projAV j ba).map (interp2 V ρ) :=
      map_interp2_of_defEqListP ihd hdefL2
        (fun x hx => frame_spineP hwa hba hLa hCa x (List.mem_of_mem_drop hx))
        hframeProj (hspa.drop cnP)
        (DenoteSpineP.map_list _ hprojden)
        (fun x hx => hoA x (List.mem_of_mem_drop hx)) hokProj ρ hρ
    -- the constructor's arguments ARE the fabricated spine
    have hfab : asa.map (interp2 V ρ)
        = tsa.map (interp2 V ρ) ++ (List.range e0.numFields).map
            (fun j => Setlec.SetTheory.Tower.projS j (interp2 V ρ ba)) := by
      rw [← List.take_append_drop cnP asa, List.map_append, htake, hdrop,
        List.map_map, ← hfld', hefld]
      refine congrArg _ (List.map_congr_left fun j _ => ?_)
      rw [Function.comp_apply, projAV_interp]
    -- assemble
    rw [hb, interp2_mkAppN, hfold, hfab, hψc, ← hctr', hectr, hlpsT']
  · -- PROJECTION-FUNCTION SLOTS: the stored-family law, as before
    -- the family is stored
    have hfam : Setlec.EtaFamilyStored env T caps := by
      refine ⟨by rw [hectr]; exact hresc, ⟨cvc, ?_⟩, ?_⟩
      · rw [hectr, hepar, hefld]; exact hfc
      · intro j hj
        exact hrecs j (by rw [← hefld]; exact hj)
    -- the fabricated projections are the projection functions' spines
    have hetaP : Setlec.etaProjs env T us' wtb.getAppArgs b cnF
        = (List.range cnF).map (fun i =>
            Expr.mkAppN (.const (projFnName T i) us') (wtb.getAppArgs ++ [b])) := by
      unfold Setlec.etaProjs
      split
      · next h => rw [htow0 h]; simp
      · rfl
    rw [hetaP] at hdefL2
    -- the law, and its carried reading moved to the ambient depth
    obtain ⟨TVa, hTVa, hokTVa, hlaw⟩ :=
      hcaps.1 T cvT caps hfT heta hresT hfam φ us' hlenus
    obtain ⟨rest, hfitT⟩ := hfitOf TVa hTVa hokTVa
    have hb := hlaw ρ (tsa.map (interp2 V ρ)) rest (interp2 V ρ ba)
      hlenTs hfitT hmemFam
    -- each slot is a recursor (the tower arm of the per-slot
    -- certificate is refuted by the slot discipline)
    have hslotR : ∀ j ∈ List.range cnF, ∃ cvp mIp rPp rulesp,
        env.find? (projFnName T j) = some (.recInfo cvp mIp rPp rulesp) ∧
        cvp.levelParams = cvT.levelParams ∧
        (cvp.type.stripPis (wtb.getAppArgs.length + 1)).isSome = true ∧
        Setlec.iotaCertsP μ env fuel d false
          (cvp.type.instantiateLevelParams cvp.levelParams us')
          (wtb.getAppArgs ++ [b]) = .ok true := by
      intro j hj
      rcases Setlec.structEtaProjCerts_inv _ hprojs j hj with
        ⟨cvp, mIp, rPp, rulesp, hfp, hlpj, hstrpj, hicj⟩ |
        ⟨entry, hfp, -, -, -, -⟩
      · exact ⟨cvp, mIp, rPp, rulesp, hfp, hlpj, hstrpj, hicj⟩
      · exfalso
        obtain ⟨cvp, mIp, rPp, rulesp, hfr⟩ := hrecs j (List.mem_range.mp hj)
        rw [hfp] at hfr
        exact nomatch hfr
    have hprojden : ∀ j ∈ List.range cnF,
        denoteP m.acval env φ d
            (Expr.mkAppN (.const (projFnName T j) us') (wtb.getAppArgs ++ [b]))
          = some (AVExpr.mkAppN (m.acval (projFnName T j) (Level.substFn φ cvT.levelParams us')) (tsa ++ [ba])) := by
      intro j hj
      obtain ⟨cvp, mIp, rPp, rulesp, hfp, hlpj, -, -⟩ := hslotR j hj
      refine denoteP_mkAppN hspTb ?_
      rw [denoteP, hfp]
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
          AVExpr.mkAppN (m.acval (projFnName T j) (Level.substFn φ cvT.levelParams us')) (tsa ++ [ba])),
        ∀ σ : Nat → V, Sat2 V Δa σ → AnnotOkP V σ x := by
      intro x hx σ hσ
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      obtain ⟨cvp, mIp, rPp, rulesp, hfp, hlpj, hstrpj, hicj⟩ := hslotR j hj
      have hlenp : us'.length = cvp.levelParams.length := by
        rw [hlpj]; exact hlenus
      obtain ⟨tpa, htpa, hoktpa, hmemp⟩ :=
        hct d (projFnName T j) _ us' hfp rfl hlenp
      -- the projection type's frames
      have hwfp := m.wf _ (Setlec.Semantics.Env.find?_mem hfp)
      have hnfp : (cvp.type.instantiateLevelParams cvp.levelParams
          us').hasFvar = false := by
        rw [Setlec.Expr.hasFvar_instantiateLevelParams]; exact hwfp.1
      have hbdp : (cvp.type.instantiateLevelParams cvp.levelParams
          us').looseBVarsBounded 0 = true := by
        rw [Setlec.Expr.looseBVarsBounded_instantiateLevelParams]
        exact hwfp.2.2.2.1
      have hpcp : PiChainP (wtb.getAppArgs ++ [b]).length tpa := by
        rw [List.length_append, List.length_singleton]
        exact piChainP_of_stripPis _
          (Setlec.Expr.stripPis_instantiateLevelParams_isSome
            cvp.levelParams us' _ hstrpj) htpa
      obtain ⟨restp, hfitp⟩ :=
        certs_teleP ihd ihis hexi _ (wtb.getAppArgs ++ [b]) (tsa ++ [ba])
          tpa hicj hpcp (Setlec.Expr.WScoped.of_not_hasFvar hnfp) hbdp
          (Setlec.Expr.LeavesBounded.of_not_hasFvar hnfp)
          ⟨hCa.1, fun l hl => by
            rw [Setlec.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnfp] at hl
            exact nomatch hl⟩
          htpa (fun τ _ => hoktpa τ) hframeTb hspTb hokTb' σ hσ
      refine (annotOkP_mkAppN_of_fit (tsa ++ [ba]) (hoktpa σ)
        ⟨m.acval_ok2 _ _ σ, hav _ _ σ⟩
        (fun x hx => hokTb' x hx σ hσ) ?_ hfitp).1
      have := hmemp σ
      dsimp only [Setlec.ConstantInfo.toConstantVal] at this
      rwa [hlpj] at this
    have hframeProj : ∀ x ∈ (List.range cnF).map (fun i =>
          Expr.mkAppN (.const (projFnName T i) us') (wtb.getAppArgs ++ [b])),
        Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
          Expr.LeavesBounded x ∧ CtxOkP m φ d Δa x := by
      intro x hx
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
      refine ⟨Setlec.Expr.WScoped.mkAppN
          (Setlec.Expr.WScoped.of_not_hasFvar rfl)
          (fun y hy => (hframeTb y hy).1),
        Setlec.looseBVarsBounded_mkAppN rfl
          (fun y hy => (hframeTb y hy).2.1),
        fun l hl => ?_, ⟨hCa.1, fun l hl => ?_⟩⟩ <;>
      · rcases Setlec.fvarLeaves_mkAppN hl with hl' | ⟨y, hy, hly⟩
        · exact absurd hl' (by simp [Expr.fvarLeaves])
        · first
          | exact (hframeTb y hy).2.2.1 l hly
          | exact (hframeTb y hy).2.2.2.2 l hly
    have hdrop : (asa.drop cnP).map (interp2 V ρ)
        = ((List.range cnF).map fun j =>
            AVExpr.mkAppN (m.acval (projFnName T j) (Level.substFn φ cvT.levelParams us')) (tsa ++ [ba])).map
          (interp2 V ρ) :=
      map_interp2_of_defEqListP ihd hdefL2
        (fun x hx => frame_spineP hwa hba hLa hCa x (List.mem_of_mem_drop hx))
        hframeProj (hspa.drop cnP)
        (DenoteSpineP.map_list _ hprojden)
        (fun x hx => hoA x (List.mem_of_mem_drop hx)) hokProj ρ hρ
    -- the constructor's arguments ARE the fabricated spine
    have hfab : asa.map (interp2 V ρ)
        = etaFabArgs2 (fun n => interp2 V ρ (m.acval n (Level.substFn φ cvT.levelParams us'))) T
            (tsa.map (interp2 V ρ)) (interp2 V ρ ba) caps.etaFields := by
      rw [etaFabArgs2, projSpines2, ← List.take_append_drop cnP asa,
        List.map_append, htake, hdrop, hefld, List.map_map]
      refine congrArg _ (List.map_congr_left fun j _ => ?_)
      show interp2 V ρ (AVExpr.mkAppN (m.acval (projFnName T j) (Level.substFn φ cvT.levelParams us'))
        (tsa ++ [ba])) = _
      rw [interp2_mkAppN, hfold, List.map_append]
      rfl
    -- assemble
    rw [hb, interp2_mkAppN, hfold, hfab, hψc, hectr]

/-- **`StructEtaIrrelP`, discharged from the field.**  The wrapper's own
reduction (infer the stuck side, head-normalise, read the claims off
it) plus `structEtaCertWithP_step`. -/
theorem structEtaIrrelP_of_claims {m : EnvS2Core V env}
    (hcaps : CapsOkP m) (htower : TowerOkP m φ) (hct : ConstTypeP m φ)
    (hav : AcvalValidP m)
    (ihw : WhnfClaims2P μ m φ fuel) (ihd : DefEqClaims2P μ m φ fuel)
    (ihis : InferClaimsIOS2P μ m φ fuel)
    (hexi : InferExistsIOSP μ m φ fuel) (hwreads : WhnfReadsP m μ φ fuel) :
    StructEtaIrrelP μ m φ fuel := by
  intro d a b Δa h hwa hba hLa hwb hbb hLb aa ba hCa hCb hda hdb
    hokA hokB ρ hρ
  obtain ⟨tb, wtb, htb, hwtb, hcw⟩ := Setlec.structEtaCert_inv h
  -- the stuck side's inferred type: frames, reading, membership
  have hwt : Expr.WScoped d tb :=
    Setlec.inferTypeIO_WScoped m.wf fuel htb hwb
  have hbt : tb.looseBVarsBounded 0 = true :=
    Setlec.inferTypeIO_looseBVars m.wf fuel htb hwb hbb hLb
  have hLt : Expr.LeavesBounded tb := fun l hl =>
    hLb l (Setlec.inferTypeIO_fvarLeaves m.wf fuel htb hwb l hl)
  have hCt : CtxOkP m φ d Δa tb :=
    hCb.of_subset (Setlec.inferTypeIO_fvarLeaves m.wf fuel htb hwb)
  obtain ⟨tba, htba⟩ :=
    hexi htb hwb hbb hLb hCb hdb
  obtain ⟨hokTb, hmemB⟩ := ihis htb hwb hbb hLb hCb hdb htba hokB
  obtain ⟨wtba, hwtba⟩ := hwreads hwtb hwt hbt hLt
    (LeafReadsP.of_ctxOkP hCt) htba
  obtain ⟨hokW, heqW⟩ := ihw hwtb hwt hbt hLt hCt htba hwtba hokTb
  -- the reduct's frames
  have hwr : Expr.WScoped d wtb := Setlec.whnf_WScoped m.wf fuel hwtb hwt
  have hbr : wtb.looseBVarsBounded 0 = true :=
    Setlec.whnf_looseBVars m.wf fuel hwtb hbt
  have hLr : Expr.LeavesBounded wtb := fun l hl =>
    hLt l (Setlec.whnf_fvarLeaves m.wf fuel hwtb l hl)
  have hCr : CtxOkP m φ d Δa wtb :=
    hCt.of_subset (Setlec.whnf_fvarLeaves m.wf fuel hwtb)
  exact structEtaCertWithP_step hcaps htower hct hav ihd ihis hexi hcw
    hwa hba hLa hCa hwb hbb hLb hCb hwr hbr hLr hCr hda hdb hwtba
    hokA hokB hokW (fun σ hσ => (heqW σ hσ) ▸ hmemB σ hσ) ρ hρ

/-- The frame conditions of an application's two immediate parts —
`frame_appFnP`'s one-step twin (the unit-like row peels its spine with
it). -/
theorem frame_appP {m : EnvS2Core V env} {d : Nat} {Δa : List AVExpr}
    {f x : Expr} (hw : Expr.WScoped d (.app f x))
    (hb : (Expr.app f x).looseBVarsBounded 0 = true)
    (hL : Expr.LeavesBounded (.app f x))
    (hC : CtxOkP m φ d Δa (.app f x)) :
    (Expr.WScoped d f ∧ f.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded f ∧ CtxOkP m φ d Δa f) ∧
      (Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ CtxOkP m φ d Δa x) := by
  obtain ⟨hwf, hwx⟩ : Expr.WScoped d f ∧ Expr.WScoped d x := by
    simpa [Expr.WScoped] using hw
  obtain ⟨hbf, hbx⟩ :
      f.looseBVarsBounded 0 = true ∧ x.looseBVarsBounded 0 = true := by
    simpa [Expr.looseBVarsBounded, Bool.and_eq_true] using hb
  exact ⟨⟨hwf, hbf, fun l hl => hL l (by simp [Expr.fvarLeaves, hl]),
      hC.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl])⟩,
    ⟨hwx, hbx, fun l hl => hL l (by simp [Expr.fvarLeaves, hl]),
      hC.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl])⟩⟩

/-! ## The unit-like row (post-repair)

`structEtaIrrelP_of_claims` minus the fabricated spine: both sides'
inferred types whnf to the *same* family instance (the certificate's
own `isDefEqCore` run identifies them at `interp2`), the telescope
certificates build the fit, and the repaired `UnitLawP` — its
superfluous family premise deleted, the ratified fix — collapses the
two members. -/

/-- **`StructUnitIrrelP`, discharged from the field.** -/
theorem structUnitIrrelP_of_claims {m : EnvS2Core V env}
    (hcaps : CapsOkP m)
    (ihw : WhnfClaims2P μ m φ fuel) (ihd : DefEqClaims2P μ m φ fuel)
    (ihis : InferClaimsIOS2P μ m φ fuel)
    (hexi : InferExistsIOSP μ m φ fuel)
    (hwreads : WhnfReadsP m μ φ fuel) :
    StructUnitIrrelP μ m φ fuel := by
  intro d a b Δa h hwa hba hLa hwb hbb hLb aa ba hCa hCb hda hdb
    hokA hokB ρ hρ
  obtain ⟨ta, wta, T, us', cvT, caps, tb, wtb, hta, hwta, hfn, hfind,
    hunit, hres, hlenArgs, hlenUs, hstrip, htb, hwtb, hdeq, hcerts⟩ :=
    Setlec.structUnitCert_inv h
  -- one side's chain: the reading, membership and reduction package
  -- of an inferred type, whnf'd
  have side : ∀ (x tx wtx : Expr) (xa : AVExpr),
      Setlec.inferTypeIO μ env fuel d x = .ok tx →
      whnf μ env fuel d tx = .ok wtx →
      Expr.WScoped d x → x.looseBVarsBounded 0 = true →
      Expr.LeavesBounded x → CtxOkP m φ d Δa x →
      denoteP m.acval env φ d x = some xa →
      (∀ σ : Nat → V, Sat2 V Δa σ → AnnotOkP V σ xa) →
      ∃ wtxa, denoteP m.acval env φ d wtx = some wtxa ∧
        (∀ σ : Nat → V, Sat2 V Δa σ → AnnotOkP V σ wtxa) ∧
        (interp2 V ρ xa ∈ˢ interp2 V ρ wtxa) ∧
        Expr.WScoped d wtx ∧ wtx.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded wtx ∧ CtxOkP m φ d Δa wtx := by
    intro x tx wtx xa htx hwtx hwx hbx hLx hCx hdx hokX
    have hwt : Expr.WScoped d tx :=
      Setlec.inferTypeIO_WScoped m.wf fuel htx hwx
    have hbt : tx.looseBVarsBounded 0 = true :=
      Setlec.inferTypeIO_looseBVars m.wf fuel htx hwx hbx hLx
    have hLt : Expr.LeavesBounded tx := fun l hl =>
      hLx l (Setlec.inferTypeIO_fvarLeaves m.wf fuel htx hwx l hl)
    have hCt : CtxOkP m φ d Δa tx :=
      hCx.of_subset (Setlec.inferTypeIO_fvarLeaves m.wf fuel
        htx hwx)
    obtain ⟨txa, htxa⟩ :=
      hexi htx hwx hbx hLx hCx hdx
    obtain ⟨hokTx, hmemX⟩ := ihis htx hwx hbx hLx hCx hdx htxa hokX
    obtain ⟨wtxa, hwtxa⟩ := hwreads hwtx hwt hbt hLt
      (LeafReadsP.of_ctxOkP hCt) htxa
    obtain ⟨hokW, heqW⟩ := ihw hwtx hwt hbt hLt hCt htxa hwtxa hokTx
    refine ⟨wtxa, hwtxa, hokW, ?_,
      Setlec.whnf_WScoped m.wf fuel hwtx hwt,
      Setlec.whnf_looseBVars m.wf fuel hwtx hbt,
      fun l hl => hLt l (Setlec.whnf_fvarLeaves m.wf fuel hwtx l hl),
      hCt.of_subset (Setlec.whnf_fvarLeaves m.wf fuel hwtx)⟩
    rw [← heqW ρ hρ]
    exact hmemX ρ hρ
  obtain ⟨wtaa, hwtaa, hokWA, hmemAW, hwrA, hbrA, hLrA, hCrA⟩ :=
    side a ta wta aa hta hwta hwa hba hLa hCa hda hokA
  obtain ⟨wtba, hwtba, hokWB, hmemBW, hwrB, hbrB, hLrB, hCrB⟩ :=
    side b tb wtb ba htb hwtb hwb hbb hLb hCb hdb hokB
  -- the certificate's defeq run identifies the two family instances
  have hEq : interp2 V ρ wtaa = interp2 V ρ wtba :=
    ihd hdeq hwrA hbrA hLrA hwrB hbrB hLrB hCrA hCrB hwtaa hwtba
      hokWA hokWB ρ hρ
  -- side a's reduct is the family applied to its parameters
  rw [show wta = Expr.mkAppN wta.getAppFn wta.getAppArgs from
    (Setlec.Expr.mkAppN_getApp wta).symm, hfn] at hwtaa
  obtain ⟨vT, tsa, hvT, hspt, rfl⟩ := denoteP_mkAppN_inv hwtaa
  rw [denoteP, hfind] at hvT
  dsimp only at hvT
  split at hvT
  case isFalse => exact nomatch hvT
  case isTrue =>
  obtain rfl : vT = m.acval T (Level.substFn φ cvT.levelParams us') :=
    (Option.some.inj hvT).symm
  -- the (repaired) unit law, and its carried reading at depth `d`
  obtain ⟨TVa, hTVa, hokTVa, hlaw⟩ :=
    hcaps.2 T cvT caps hfind hunit hres φ us' hlenUs
  have hwfT := m.wf _ (Setlec.Semantics.Env.find?_mem hfind)
  have hnfT : (cvT.type.instantiateLevelParams cvT.levelParams
      us').hasFvar = false := by
    rw [Setlec.Expr.hasFvar_instantiateLevelParams]; exact hwfT.1
  have hbdT : (cvT.type.instantiateLevelParams cvT.levelParams
      us').looseBVarsBounded 0 = true := by
    rw [Setlec.Expr.looseBVarsBounded_instantiateLevelParams]
    exact hwfT.2.2.2.1
  have hTVd : denoteP m.acval env φ d
      (cvT.type.instantiateLevelParams cvT.levelParams us')
      = some TVa :=
    denoteP_depth_of_closed m.acval_closed hnfT
      (fun k => denoteP_closed m.acval_erase m.cval_closed
        hnfT hbdT hTVa 1 k) hTVa d
  have hTw : Expr.WScoped d
      (cvT.type.instantiateLevelParams cvT.levelParams us') :=
    Setlec.Expr.WScoped.of_not_hasFvar hnfT
  have hTL : Expr.LeavesBounded
      (cvT.type.instantiateLevelParams cvT.levelParams us') :=
    Setlec.Expr.LeavesBounded.of_not_hasFvar hnfT
  have hTC : CtxOkP m φ d Δa
      (cvT.type.instantiateLevelParams cvT.levelParams us') :=
    ⟨hCa.1, fun l hl => by
      rw [Setlec.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnfT] at hl
      exact nomatch hl⟩
  have hpcT : PiChainP wta.getAppArgs.length TVa := by
    rw [hlenArgs]
    exact piChainP_of_stripPis caps.unitParams
      (Setlec.Expr.stripPis_instantiateLevelParams_isSome
        cvT.levelParams us' caps.unitParams hstrip) hTVd
  obtain ⟨hohT, hoT⟩ := hoistP_spine tsa hokWA
  obtain ⟨rest, hfitT⟩ :=
    certs_teleP ihd ihis hexi _ wta.getAppArgs tsa TVa hcerts hpcT
      hTw hbdT hTL hTC hTVd (fun σ _ => hokTVa σ)
      (frame_spineP hwrA hbrA hLrA hCrA) hspt hoT ρ hρ
  -- both members, at the folded family instance
  have hfold : ∀ (l : List AVExpr) (x : V),
      l.foldl (fun r y => SetTheory.app r (interp2 V ρ y)) x
        = (l.map (interp2 V ρ)).foldl SetTheory.app x := by
    intro l x; rw [List.foldl_map]
  have hmx : interp2 V ρ aa
      ∈ˢ (tsa.map (interp2 V ρ)).foldl SetTheory.app
          (interp2 V ρ (m.acval T (Level.substFn φ cvT.levelParams
            us'))) := by
    have := hmemAW
    rwa [interp2_mkAppN, hfold] at this
  have hmy : interp2 V ρ ba
      ∈ˢ (tsa.map (interp2 V ρ)).foldl SetTheory.app
          (interp2 V ρ (m.acval T (Level.substFn φ cvT.levelParams
            us'))) := by
    have := hEq ▸ hmemBW
    rwa [interp2_mkAppN, hfold] at this
  have hlenTs : (tsa.map (interp2 V ρ)).length = caps.unitParams := by
    rw [List.length_map, ← hspt.length, hlenArgs]
  exact hlaw ρ (tsa.map (interp2 V ρ)) rest (interp2 V ρ aa)
    (interp2 V ρ ba) hlenTs hfitT hmx hmy

end Setlec.SetP
