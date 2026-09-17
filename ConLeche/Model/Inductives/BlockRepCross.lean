module

public import ConLeche.Model.Inductives.BlockRecWD
public import ConLeche.Model.Inductives.MutualRecs
public import ConLeche.Model.Inductives.MutualRecData
public import ConLeche.Model.Inductives.MutualFormersKit
import ConLeche.Model.Swap
import ConLeche.Verify.Extend.Recs
import ConLeche.Kernel.Inductives.MutualInstall
public section

/-!
# The uniform block model across an environment change (task #315 U-9, M4 s4b)

The block's representation is read once, at the environment holding the
members and their constructors, and consumed at two LATER
environments: the one the `k` recursors are provisioned rule-less at
(`provisionMutualRecs`) and the one they are stored at with their
rules (a rule-list swap of the former).  This file transports the
block model — and its companions — across both, with ONE generic lemma per
structure.

The two changes are crossed uniformly by four hypotheses relating two
models `m₁ : EnvModel V env₁` and `m₂ : EnvModel V env₂`:

* `hF`, a NON-RECURSOR lookup survives (the swap moves a recursor's
  entry — it gains its rule list — and moves nothing else);
* `hres`, resolution survives;
* `hag`, the valuations agree at every stored name;
* `hde`, a successful reading at `env₁` is reproduced at `env₂`.

`hde` is stated WITHOUT a `ConstsBound` premise, and that is what keeps
the transports free of side conditions: a reading that SUCCEEDS is its
own witness that every constant it consults is stored, so the
extension crossing needs no boundedness hypothesis
(`denoteMeta_env_mono`, the `ConstsBound`-free twin of
`denoteMeta_envExtend_mono`).  The premise cannot be recovered from a
reading either: `denoteMeta` never looks at an `fvar`'s type
annotation, while `ConstsBound` demands it be bound, so
"a reading implies `ConstsBound`" is refutable
(`denoteMeta acval env φ d (.fvar 0 (.const n []))` succeeds at every
environment).  The two instances are `provision_hde` (the `k` fresh
rule-less conses) and `swap_hde` (`denoteMeta_swap`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps RecRule
  MutualBlock MutualFormerA)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The reading across an environment extension, with no `ConstsBound` -/

/-- **The monotone crossing without a boundedness premise**:
`denoteMeta_envExtend_mono`'s twin.  The original takes
`ConstsBound env₀ e` to refute the `.const` clause's unfound branch and
to feed the binder cases' `instantiate1`; a SUCCESSFUL reading refutes
that branch by itself (the clause is `none` there), and the binder
cases then need nothing.  Dropping the premise is what lets the block model's
opened readings cross with no `openPisAtFvars` detour. -/
theorem denoteMeta_env_mono {env₁ env₂ : Env}
    {acval : Name → (Name → Nat) → AnnotTerm} {φ : Name → Nat}
    (hF : FindPreserved env₁ env₂) (hG : LitGuardsMono env₁ env₂)
    (hproj : ∀ (sn : Name) (i : Nat),
      env₁.findProj? sn i = none → env₂.findProj? sn i = none) :
    ∀ (d : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta acval env₁ φ d e = some ea →
        denoteMeta acval env₂ φ d e = some ea := by
  have hmono : ∀ (sn : Name) (i : Nat) (entry : ConLeche.ProjEntry),
      env₁.findProj? sn i = some entry →
      env₂.findProj? sn i = some entry := by
    intro sn i entry h
    obtain ⟨tbl, hf0, hi, rfl⟩ := ConLeche.Env.findProj?_some h
    exact ConLeche.Env.findProj?_of_table (hF hf0) hi
  intro d e
  induction d, e using denoteMeta.induct (env := env₁) with
  | case1 d u => intro ea h; rw [denoteMeta] at h ⊢; exact h
  | case2 d idx ty => intro ea h; rw [denoteMeta] at h ⊢; exact h
  | case3 d n us ci hf hlen =>
    intro ea h
    rw [denoteMeta, hf] at h
    rw [denoteMeta, hF hf]
    exact h
  | case4 d n us ci hf hlen =>
    intro ea h
    rw [denoteMeta, hf] at h
    dsimp only at h
    rw [if_neg hlen] at h
    exact nomatch h
  | case5 d n us hf =>
    intro ea h
    rw [denoteMeta, hf] at h
    exact nomatch h
  | case6 d ty body m ihty ihbody =>
    intro ea h
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv h
    rw [denoteMeta, ihty hta, ihbody hba]
    rfl
  | case7 d ty body m ihty ihbody =>
    intro ea h
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_lam_inv h
    rw [denoteMeta, ihty hta, ihbody hba]
    rfl
  | case8 d f a ihf iha =>
    intro ea h
    obtain ⟨fa, aa, hfa, haa, rfl⟩ := denoteMeta_app_inv h
    rw [denoteMeta, ihf hfa, iha haa]
    rfl
  | case9 d ty val body =>
    intro ea h
    rw [denoteMeta] at h
    exact nomatch h
  | case10 d sn i e ihe =>
    intro ea h
    obtain ⟨ea', hea', hcase⟩ := denoteMeta_proj_inv h
    rcases hcase with ⟨entry, hfp0, rfl⟩ | ⟨hnt0, hdec⟩
    · rw [denoteMeta, ihe hea', hmono sn i entry hfp0]
      rfl
    · rw [denoteMeta, ihe hea', hproj sn i hnt0]
      exact hdec
  | case11 d n hsup =>
    intro ea h
    rw [denoteMeta, if_pos hsup] at h
    rw [denoteMeta, if_pos (hG.1 hsup)]
    exact h
  | case12 d n hsup =>
    intro ea h
    rw [denoteMeta, if_neg hsup] at h
    exact nomatch h
  | case13 d s hsup =>
    intro ea h
    obtain ⟨hnil, hcons⟩ := strLitSupported_listNames hsup
    rw [denoteMeta, if_pos hsup] at h
    rw [denoteMeta, if_pos (hG.2 hsup),
      ← levelParamsAt_congr hF hnil, ← levelParamsAt_congr hF hcons]
    exact h
  | case14 d s hsup =>
    intro ea h
    rw [denoteMeta, if_neg hsup] at h
    exact nomatch h
  | case15 d x hs hfv hc hpi hlam happ hlet hprj hnat hstr =>
    intro ea h
    cases x with
    | bvar i => rw [denoteMeta.eq_def] at h; exact nomatch h
    | sort u => exact absurd rfl (hs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n us => exact absurd rfl (hc n us)
    | forallE ty b m => exact absurd rfl (hpi ty b m)
    | lam ty b m => exact absurd rfl (hlam ty b m)
    | app f a => exact absurd rfl (happ f a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hprj sn i e)
    | lit l =>
      cases l with
      | natVal n => exact absurd rfl (hnat n)
      | strVal s => exact absurd rfl (hstr s)

/-! ## The guarded crossing: a reading that survives a PROJECTION TABLE -/

/-- **The subject has no projection at any of `Ts`** (task #315 M7-3
session 3, DESIGN §U.41): the guard that makes a reading survive an
extension whose NEW projection-table slots are all at the structures
`Ts`.  Without it `hde` is refutable across a table cons
(`hde_not_of_newTable`, `ContainerCross.lean`), which is why no
install route could discharge it: every route ends by consing its
structure-like members' tables. -/
@[expose] def ProjFree (Ts : List Name) (e : Expr) : Prop :=
  ∀ T ∈ Ts, ∀ j : Nat, ConLeche.Expr.NoProjAt T j e

omit [SetTheory V] in
/-- At no tabled structure the guard is vacuous — how the OLD,
unguarded crossings are recovered (`Ts := []`). -/
theorem ProjFree.nil (e : Expr) : ProjFree [] e := fun _ hT => nomatch hT

omit [SetTheory V] in
/-- **A RESOLVING expression is guarded at names that are not stored**:
`constsResolve` reads `find? s` at every `.proj s _` node, so a
structure the environment does not carry appears in none of them
(`Expr.noProjAt_of_constsResolve`).  This is the source of every guard
the block model's crossing needs: a block's own members are fresh at
its pre-block environment, where its opened field data resolves
(`BlockOpened`). -/
theorem ProjFree.of_constsResolve {Ts : List Name} {env : Env} {e : Expr}
    (hfresh : ∀ T ∈ Ts, env.find? T = none) (hres : e.constsResolve env = true) :
    ProjFree Ts e :=
  fun T hT _ => ConLeche.Expr.noProjAt_of_constsResolve (hfresh T hT) e hres

omit [SetTheory V] in
/-- **A STORED type is guarded where the environment's bookkeeping says
so**: the other source of the guard, for the block being installed.
Its own members are NOT fresh at the environment its subjects are read
at — they are the very structures the route is about to table — but the
install has checked that no stored piece mentions their slots
(`NoProjEnv`, `mutualNoProj` at the recursors' environment), and every
subject of the block model's readings is a stored type or an opening of
one. -/
theorem ProjFree.of_noProjEnv {Ts : List Name} {env : Env}
    (hnp : ∀ T ∈ Ts, ∀ j : Nat, NoProjEnv env T j)
    {c : ConstantInfo} (hc : c ∈ env.consts) : ProjFree Ts c.toConstantVal.type :=
  fun T hT j => (hnp T hT j).type c hc

omit [SetTheory V] in
/-- The guard is hereditary through an `fvar`'s type annotation. -/
theorem ProjFree.fvarTypeD {Ts : List Name} {e : Expr} (h : ProjFree Ts e) :
    ProjFree Ts e.fvarTypeD := by
  cases e with
  | fvar idx ty => exact fun T hT j => (ConLeche.Expr.noProjAt_fvar).mp (h T hT j)
  | _ => exact h

omit [SetTheory V] in
/-- The guard is hereditary through an application spine's arguments. -/
theorem ProjFree.getAppArgs {Ts : List Name} :
    ∀ {e : Expr}, ProjFree Ts e → ∀ a ∈ e.getAppArgs, ProjFree Ts a := by
  intro e
  induction e with
  | app f a ihf =>
    intro h b hb
    rw [ConLeche.Expr.getAppArgs, List.mem_append] at hb
    have hfa : ProjFree Ts f ∧ ProjFree Ts a :=
      ⟨fun T hT j => (ConLeche.Expr.noProjAt_app.mp (h T hT j)).1,
        fun T hT j => (ConLeche.Expr.noProjAt_app.mp (h T hT j)).2⟩
    rcases hb with hb | hb
    · exact ihf hfa.1 b hb
    · rw [List.mem_singleton.mp hb]; exact hfa.2
  | _ => intro _ b hb; simp [ConLeche.Expr.getAppArgs] at hb

omit [SetTheory V] in
/-- The guard is hereditary through an OPENING: the binders' fvar types
and the body are nodes of the telescope. -/
theorem ProjFree.openPisAtFvars {Ts : List Name} :
    ∀ (n : Nat) (e : Expr) (dp : Nat) (fvs : List Expr) (rest : Expr),
      ConLeche.openPisAtFvars n e dp = some (fvs, rest) → ProjFree Ts e →
      (∀ x ∈ fvs, ProjFree Ts x.fvarTypeD) ∧ ProjFree Ts rest := by
  intro n
  induction n with
  | zero =>
    intro e dp fvs rest hop h
    rw [ConLeche.openPisAtFvars] at hop
    simp only [Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    exact ⟨(fun _ hx => nomatch hx), h⟩
  | succ n ih =>
    intro e dp fvs rest hop h
    cases e with
    | forallE dom body m =>
      have hdom : ProjFree Ts dom := fun T hT j =>
        (ConLeche.Expr.noProjAt_forallE.mp (h T hT j)).1
      have hbody : ProjFree Ts body := fun T hT j =>
        (ConLeche.Expr.noProjAt_forallE.mp (h T hT j)).2
      have hinst : ProjFree Ts (body.instantiate1 (.fvar dp dom)) := fun T hT j =>
        ConLeche.Expr.NoProjAt.instantiate1 (v := .fvar dp dom)
          (ConLeche.Expr.noProjAt_fvar.mpr (hdom T hT j)) body 0 (hbody T hT j)
      rw [ConLeche.openPisAtFvars] at hop
      cases hrec : ConLeche.openPisAtFvars n (body.instantiate1 (.fvar dp dom)) (dp + 1) with
      | none => rw [hrec] at hop; exact nomatch hop
      | some pr =>
        obtain ⟨fvs', rest'⟩ := pr
        rw [hrec] at hop
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        obtain ⟨hfvs, hrest⟩ := ih _ _ _ _ hrec hinst
        refine ⟨fun x hx => ?_, hrest⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hdom
        · exact hfvs x hx
    | _ => simp [ConLeche.openPisAtFvars] at hop

/-- **THE GUARDED TRANSPORT** (task #315 M7-3 session 3): a successful
reading at `env₁` is the reading at `env₂` as soon as the subject is
guarded at the structures whose projection slots the extension CREATES
(`hproj`).  `denoteMeta_env_mono` is the case `Ts := []`; the guard is
what the table conses at the end of every install route need, and it is
consumed exactly where `denoteMeta_env_mono`'s proof consulted
`hproj`: the `.proj` clause's TABLE-FREE branch, which the pair decoder
answers differently from a stored entry. -/
theorem denoteMeta_env_mono_projFree {env₁ env₂ : Env} {Ts : List Name}
    {acval : Name → (Name → Nat) → AnnotTerm} {φ : Name → Nat}
    (hF : FindPreserved env₁ env₂) (hG : LitGuardsMono env₁ env₂)
    (hproj : ∀ (sn : Name) (i : Nat) (entry : ConLeche.ProjEntry),
      env₁.findProj? sn i = none → env₂.findProj? sn i = some entry → sn ∈ Ts) :
    ∀ (d : Nat) (e : Expr), ProjFree Ts e → ∀ {ea : AnnotTerm},
      denoteMeta acval env₁ φ d e = some ea →
        denoteMeta acval env₂ φ d e = some ea := by
  have hmono : ∀ (sn : Name) (i : Nat) (entry : ConLeche.ProjEntry),
      env₁.findProj? sn i = some entry →
      env₂.findProj? sn i = some entry := by
    intro sn i entry h
    obtain ⟨tbl, hf0, hi, rfl⟩ := ConLeche.Env.findProj?_some h
    exact ConLeche.Env.findProj?_of_table (hF hf0) hi
  intro d e
  induction d, e using denoteMeta.induct (env := env₁) with
  | case1 d u => intro _ ea h; rw [denoteMeta] at h ⊢; exact h
  | case2 d idx ty => intro _ ea h; rw [denoteMeta] at h ⊢; exact h
  | case3 d n us ci hf hlen =>
    intro _ ea h
    rw [denoteMeta, hf] at h
    rw [denoteMeta, hF hf]
    exact h
  | case4 d n us ci hf hlen =>
    intro _ ea h
    rw [denoteMeta, hf] at h
    dsimp only at h
    rw [if_neg hlen] at h
    exact nomatch h
  | case5 d n us hf =>
    intro _ ea h
    rw [denoteMeta, hf] at h
    exact nomatch h
  | case6 d ty body m ihty ihbody =>
    intro hg ea h
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv h
    have hty : ProjFree Ts ty := fun T hT j => (ConLeche.Expr.noProjAt_forallE.mp (hg T hT j)).1
    have hbd : ProjFree Ts (body.instantiate1 (.fvar d ty)) := fun T hT j =>
      ConLeche.Expr.NoProjAt.instantiate1 (v := .fvar d ty)
        (ConLeche.Expr.noProjAt_fvar.mpr (hty T hT j)) body 0
        (ConLeche.Expr.noProjAt_forallE.mp (hg T hT j)).2
    rw [denoteMeta, ihty hty hta, ihbody hbd hba]
    rfl
  | case7 d ty body m ihty ihbody =>
    intro hg ea h
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_lam_inv h
    have hty : ProjFree Ts ty := fun T hT j => (ConLeche.Expr.noProjAt_lam.mp (hg T hT j)).1
    have hbd : ProjFree Ts (body.instantiate1 (.fvar d ty)) := fun T hT j =>
      ConLeche.Expr.NoProjAt.instantiate1 (v := .fvar d ty)
        (ConLeche.Expr.noProjAt_fvar.mpr (hty T hT j)) body 0
        (ConLeche.Expr.noProjAt_lam.mp (hg T hT j)).2
    rw [denoteMeta, ihty hty hta, ihbody hbd hba]
    rfl
  | case8 d f a ihf iha =>
    intro hg ea h
    obtain ⟨fa, aa, hfa, haa, rfl⟩ := denoteMeta_app_inv h
    have hf' : ProjFree Ts f := fun T hT j => (ConLeche.Expr.noProjAt_app.mp (hg T hT j)).1
    have ha' : ProjFree Ts a := fun T hT j => (ConLeche.Expr.noProjAt_app.mp (hg T hT j)).2
    rw [denoteMeta, ihf hf' hfa, iha ha' haa]
    rfl
  | case9 d ty val body =>
    intro _ ea h
    rw [denoteMeta] at h
    exact nomatch h
  | case10 d sn i e ihe =>
    intro hg ea h
    obtain ⟨ea', hea', hcase⟩ := denoteMeta_proj_inv h
    have he : ProjFree Ts e := fun T hT j => (ConLeche.Expr.noProjAt_proj.mp (hg T hT j)).2
    rcases hcase with ⟨entry, hfp0, rfl⟩ | ⟨hnt0, hdec⟩
    · rw [denoteMeta, ihe he hea', hmono sn i entry hfp0]
      rfl
    · -- the TABLE-FREE branch: the guard says `sn` is not one of the
      -- structures the extension tables, so the slot stays empty
      have hnt2 : env₂.findProj? sn i = none := by
        cases hf2 : env₂.findProj? sn i with
        | none => rfl
        | some entry =>
          exact absurd ((ConLeche.Expr.noProjAt_proj.mp (hg sn (hproj sn i entry hnt0 hf2) i)).1)
            (by simp)
      rw [denoteMeta, ihe he hea', hnt2]
      exact hdec
  | case11 d n hsup =>
    intro _ ea h
    rw [denoteMeta, if_pos hsup] at h
    rw [denoteMeta, if_pos (hG.1 hsup)]
    exact h
  | case12 d n hsup =>
    intro _ ea h
    rw [denoteMeta, if_neg hsup] at h
    exact nomatch h
  | case13 d s hsup =>
    intro _ ea h
    obtain ⟨hnil, hcons⟩ := strLitSupported_listNames hsup
    rw [denoteMeta, if_pos hsup] at h
    rw [denoteMeta, if_pos (hG.2 hsup),
      ← levelParamsAt_congr hF hnil, ← levelParamsAt_congr hF hcons]
    exact h
  | case14 d s hsup =>
    intro _ ea h
    rw [denoteMeta, if_neg hsup] at h
    exact nomatch h
  | case15 d x hs hfv hc hpi hlam happ hlet hprj hnat hstr =>
    intro _ ea h
    cases x with
    | bvar i => rw [denoteMeta.eq_def] at h; exact nomatch h
    | sort u => exact absurd rfl (hs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n us => exact absurd rfl (hc n us)
    | forallE ty b m => exact absurd rfl (hpi ty b m)
    | lam ty b m => exact absurd rfl (hlam ty b m)
    | app f a => exact absurd rfl (happ f a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hprj sn i e)
    | lit l =>
      cases l with
      | natVal n => exact absurd rfl (hnat n)
      | strVal s => exact absurd rfl (hstr s)

omit [SetTheory V] in
/-- A read spine crosses whatever its entries' readings cross. -/
theorem DenoteMetaSpine.crossEnv {acval₁ acval₂ : Name → (Name → Nat) → AnnotTerm}
    {env₁ env₂ : Env} {φ : Name → Nat} {d : Nat}
    (hde : ∀ (e : Expr) {ea : AnnotTerm}, denoteMeta acval₁ env₁ φ d e = some ea →
      denoteMeta acval₂ env₂ φ d e = some ea) :
    ∀ {as : List Expr} {vs : List AnnotTerm},
      DenoteMetaSpine acval₁ env₁ φ d as vs → DenoteMetaSpine acval₂ env₂ φ d as vs
  | [], _, .nil => .nil
  | _ :: _, _ :: _, .cons ha h => .cons (hde _ ha) (DenoteMetaSpine.crossEnv hde h)

omit [SetTheory V] in
/-- **A read spine crosses, entry by entry, under the guard** (task
#315 M7-3 session 3): `DenoteMetaSpine.crossEnv` with the subjects
guarded at the extension's newly tabled structures. -/
theorem DenoteMetaSpine.crossEnvP {Ts : List Name}
    {acval₁ acval₂ : Name → (Name → Nat) → AnnotTerm}
    {env₁ env₂ : Env} {φ : Name → Nat} {d : Nat}
    (hde : ∀ (e : Expr), ProjFree Ts e → ∀ {ea : AnnotTerm},
      denoteMeta acval₁ env₁ φ d e = some ea → denoteMeta acval₂ env₂ φ d e = some ea) :
    ∀ {as : List Expr} {vs : List AnnotTerm}, (∀ e ∈ as, ProjFree Ts e) →
      DenoteMetaSpine acval₁ env₁ φ d as vs → DenoteMetaSpine acval₂ env₂ φ d as vs
  | [], _, _, .nil => .nil
  | _ :: _, _ :: _, hg, .cons ha h =>
    .cons (hde _ (hg _ List.mem_cons_self) ha)
      (DenoteMetaSpine.crossEnvP hde (fun e he => hg e (List.mem_cons_of_mem _ he)) h)

/-! ## The block model's structures across the change -/

/-- **The former's data crosses under the guard**: its one subject is
the member's stored type. -/
theorem FormerData.crossEnvP {Ts : List Name} {env₁ env₂ : Env}
    {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {cvT : ConstantVal} {nP : Nat} {resSort : Level}
    {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hde : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr), ProjFree Ts e → ∀ {ea : AnnotTerm},
      denoteMeta m₁.acval env₁ ψ dp e = some ea → denoteMeta m₂.acval env₂ ψ dp e = some ea)
    (hnpT : ProjFree Ts cvT.type)
    (h : FormerData m₁ cvT nP resSort pps) :
    FormerData m₂ cvT nP resSort pps where
  read ψ := hde ψ 0 cvT.type hnpT (h.read ψ)
  len := h.len
  bits := h.bits
  okTy := h.okTy
  below := h.below
  params := h.params

/-- The former's data crosses any change the readings cross (the
unguarded crossing, `Ts := []`). -/
theorem FormerData.crossEnv' {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {cvT : ConstantVal} {nP : Nat} {resSort : Level}
    {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hde : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta m₁.acval env₁ ψ dp e = some ea → denoteMeta m₂.acval env₂ ψ dp e = some ea)
    (h : FormerData m₁ cvT nP resSort pps) :
    FormerData m₂ cvT nP resSort pps :=
  h.crossEnvP (Ts := []) (fun ψ dp e _ {_ea} hr => hde ψ dp e hr) (ProjFree.nil _)

/-- **A constructor's data at an indexed family crosses the change**:
its type's reading and its index spine travel by `hde`, the family's
leaf inside `ctorBodyAVI` by `hag` (the family is stored: `hT`). -/
theorem CtorDataI.crossEnvP {Ts : List Name} {env₁ env₂ : Env}
    {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {T : Name} {lps : List Name} {cvC : ConstantVal} {nP nF nIdx : Nat} {resSort : Level}
    {isProp large : Bool} {idxArgs : List Expr}
    {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    {srcs : List (Option Nat)}
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → m₂.acval n = m₁.acval n)
    (hde : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr), ProjFree Ts e → ∀ {ea : AnnotTerm},
      denoteMeta m₁.acval env₁ ψ dp e = some ea → denoteMeta m₂.acval env₂ ψ dp e = some ea)
    (hT : (env₁.find? T).isSome = true)
    (hnpC : ProjFree Ts cvC.type) (hnpIdx : ∀ e ∈ idxArgs, ProjFree Ts e)
    (h : CtorDataI m₁ T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs) :
    CtorDataI m₂ T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs := by
  have hbody : ∀ (ψ : Name → Nat) (Es' : List AnnotTerm),
      ctorBodyAVI m₂ T nP nF ψ Es' = ctorBodyAVI m₁ T nP nF ψ Es' := by
    intro ψ Es'
    unfold ctorBodyAVI
    rw [hag T hT]
  refine ⟨h.resid, fun ψ => ?_, h.len, h.lenE, h.idxLen, fun ψ => ?_, h.bits,
    fun ψ ρ => ?_, h.below, h.belowE, h.params, h.srcLen, h.srcBnd, h.srcIdx, h.srcProp⟩
  · rw [hbody]
    exact hde ψ 0 cvC.type hnpC (h.read ψ)
  · exact DenoteMetaSpine.crossEnvP (fun e => hde ψ (nP + nF) e) hnpIdx (h.idxRead ψ)
  · rw [hbody]
    exact h.okTy ψ ρ

@[inherit_doc CtorDataI.crossEnvP]
theorem CtorDataI.crossEnv {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {T : Name} {lps : List Name} {cvC : ConstantVal} {nP nF nIdx : Nat} {resSort : Level}
    {isProp large : Bool} {idxArgs : List Expr}
    {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    {srcs : List (Option Nat)}
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → m₂.acval n = m₁.acval n)
    (hde : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta m₁.acval env₁ ψ dp e = some ea → denoteMeta m₂.acval env₂ ψ dp e = some ea)
    (hT : (env₁.find? T).isSome = true)
    (h : CtorDataI m₁ T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs) :
    CtorDataI m₂ T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs :=
  h.crossEnvP (Ts := []) hag (fun ψ dp e _ {_ea} hr => hde ψ dp e hr) hT (ProjFree.nil _)
    (fun e _ => ProjFree.nil e)

/-- **A block constructor's data crosses the change**: on top of
`CtorDataI.crossEnv`, the opened readings (`domRead`, `eisRead`,
`reflOpen`) travel by `hde` — no `ConstsBound` of the opened subterms
is needed, since they are read — and the recursive and reflexive
entries' target formers by `hag` (every target is stored: `hTof`). -/
theorem BlockCtorData.crossEnvP {Ts : List Name} {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {env₀ : Env} {T : Name} {Tof : Nat → Name} {nIdxOf : Nat → Nat}
    {nest : Nat → Option Nat} {pins : Nat → PinSyn} {lps : List Name}
    {cvC : ConstantVal} {nP nF nIdx : Nat} {resSort : Level} {isProp large : Bool}
    {idxArgs : List Expr} {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {Es : (Name → Nat) → List AnnotTerm} {srcs : List (Option Nat)} {ks : List RecFieldKind}
    {fvsP xFvs : List Expr} {xrest : Expr} {Eiss : (Name → Nat) → List (List AnnotTerm)}
    {tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → m₂.acval n = m₁.acval n)
    (hde : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr), ProjFree Ts e → ∀ {ea : AnnotTerm},
      denoteMeta m₁.acval env₁ ψ dp e = some ea → denoteMeta m₂.acval env₂ ψ dp e = some ea)
    (hT : (env₁.find? T).isSome = true)
    (hTof : ∀ i, i < nF → nest i = none → (env₁.find? (Tof i)).isSome = true)
    (hJ : ∀ i q, i < nF → nest i = some q → (env₁.find? (pins q).J).isSome = true)
    (hnpC : ProjFree Ts cvC.type)
    (h : BlockCtorData m₁ env₀ T Tof nIdxOf nest pins lps cvC nP nF nIdx resSort isProp large idxArgs
      ds Es srcs ks fvsP xFvs xrest Eiss tss) :
    BlockCtorData m₂ env₀ T Tof nIdxOf nest pins lps cvC nP nF nIdx resSort isProp large idxArgs
      ds Es srcs ks fvsP xFvs xrest Eiss tss :=
  by
  obtain ⟨crest, hop1, hop2⟩ := h.opens
  have hcrest : ProjFree Ts crest := (ProjFree.openPisAtFvars _ _ _ _ _ hop1 hnpC).2
  obtain ⟨hxF, hxrest⟩ := ProjFree.openPisAtFvars (Ts := Ts) _ _ _ _ _ hop2 hcrest
  have hidx : ∀ e ∈ idxArgs, ProjFree Ts e := by
    intro e he
    rw [h.idxEq] at he
    exact hxrest.getAppArgs e (List.mem_of_mem_drop he)
  have hxG : ∀ (i : Nat) (x : Expr), xFvs[i]? = some x → ProjFree Ts x.fvarTypeD :=
    fun _ x hx => hxF x (List.mem_of_getElem? hx)
  exact
  { toCtorDataI := h.toCtorDataI.crossEnvP hag hde hT hnpC hidx
    opened := h.opened
    opens := h.opens
    ksLen := h.ksLen
    xLen := h.xLen
    pLen := h.pLen
    xIdx := h.xIdx
    pIdx := h.pIdx
    idxEq := h.idxEq
    domRead := fun ψ i x hx => hde ψ (nP + i) x.fvarTypeD (hxG i x hx) (h.domRead ψ i x hx)
    eissLen := h.eissLen
    eisRead := fun ψ i x hx hn hk =>
      DenoteMetaSpine.crossEnvP (fun e => hde ψ (nP + i) e)
        (fun e he => (hxG i x hx).getAppArgs e (List.mem_of_mem_drop he))
        (h.eisRead ψ i x hx hn hk)
    eisLen := h.eisLen
    recEntry := fun ψ i hn hk hi => by
      rw [hag (Tof i) (hTof i hi hn)]
      exact h.recEntry ψ i hn hk hi
    nestEisRead := fun ψ i x q hx hq hk =>
      DenoteMetaSpine.crossEnvP (fun e => hde ψ (nP + i) e)
        (fun e he => (hxG i x hx).getAppArgs e (List.mem_of_mem_drop he))
        (h.nestEisRead ψ i x q hx hq hk)
    nestEisLen := h.nestEisLen
    nestEntry := fun ψ i q hq hk hi => by
      rw [hag (pins q).J (hJ i q hi hq)]
      exact h.nestEntry ψ i q hq hk hi
    eissParams := h.eissParams
    eissBelow := h.eissBelow
    ordNone := h.ordNone
    tssLen := h.tssLen
    tssNone := h.tssNone
    tssBits := h.tssBits
    tssPiBits := h.tssPiBits
    tssBelow := h.tssBelow
    tssParams := h.tssParams
    reflOpen := fun ψ i x hx hn hk => by
      obtain ⟨afvs, body, hop, hlenTl, hdoms, hsp⟩ := h.reflOpen ψ i x hx hn hk
      obtain ⟨hafvs, hbody⟩ := ProjFree.openPisAtFvars (Ts := Ts) _ _ _ _ _ hop (hxG i x hx)
      exact ⟨afvs, body, hop, hlenTl,
        fun k a hka =>
          hde ψ (nP + i + k) a.fvarTypeD (hafvs a (List.mem_of_getElem? hka)) (hdoms k a hka),
        DenoteMetaSpine.crossEnvP
          (fun e => hde ψ (nP + i + ((tss ψ).getD i []).length) e)
          (fun e he => hbody.getAppArgs e (List.mem_of_mem_drop he)) hsp⟩
    eisLenRefl := h.eisLenRefl
    reflEntry := fun ψ i hn hk hi => by
      rw [hag (Tof i) (hTof i hi hn)]
      exact h.reflEntry ψ i hn hk hi
    nestReflOpen := fun ψ i x q hx hq hk => by
      obtain ⟨afvs, body, hop, hlenTl, hdoms, hsp⟩ := h.nestReflOpen ψ i x q hx hq hk
      obtain ⟨hafvs, hbody⟩ := ProjFree.openPisAtFvars (Ts := Ts) _ _ _ _ _ hop (hxG i x hx)
      exact ⟨afvs, body, hop, hlenTl,
        fun k a hka =>
          hde ψ (nP + i + k) a.fvarTypeD (hafvs a (List.mem_of_getElem? hka)) (hdoms k a hka),
        DenoteMetaSpine.crossEnvP
          (fun e => hde ψ (nP + i + ((tss ψ).getD i []).length) e)
          (fun e he => hbody.getAppArgs e (List.mem_of_mem_drop he)) hsp⟩
    nestEisLenRefl := h.nestEisLenRefl
    nestReflEntry := fun ψ i q hq hk hi => by
      rw [hag (pins q).J (hJ i q hi hq)]
      exact h.nestReflEntry ψ i q hq hk hi }


/-- A block constructor's data crosses any change the readings cross
(the unguarded crossing, `Ts := []`). -/
theorem BlockCtorData.crossEnv {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {env₀ : Env} {T : Name} {Tof : Nat → Name} {nIdxOf : Nat → Nat}
    {nest : Nat → Option Nat} {pins : Nat → PinSyn} {lps : List Name}
    {cvC : ConstantVal} {nP nF nIdx : Nat} {resSort : Level} {isProp large : Bool}
    {idxArgs : List Expr} {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {Es : (Name → Nat) → List AnnotTerm} {srcs : List (Option Nat)} {ks : List RecFieldKind}
    {fvsP xFvs : List Expr} {xrest : Expr} {Eiss : (Name → Nat) → List (List AnnotTerm)}
    {tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → m₂.acval n = m₁.acval n)
    (hde : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta m₁.acval env₁ ψ dp e = some ea → denoteMeta m₂.acval env₂ ψ dp e = some ea)
    (hT : (env₁.find? T).isSome = true)
    (hTof : ∀ i, i < nF → nest i = none → (env₁.find? (Tof i)).isSome = true)
    (hJ : ∀ i q, i < nF → nest i = some q → (env₁.find? (pins q).J).isSome = true)
    (h : BlockCtorData m₁ env₀ T Tof nIdxOf nest pins lps cvC nP nF nIdx resSort isProp large idxArgs
      ds Es srcs ks fvsP xFvs xrest Eiss tss) :
    BlockCtorData m₂ env₀ T Tof nIdxOf nest pins lps cvC nP nF nIdx resSort isProp large idxArgs
      ds Es srcs ks fvsP xFvs xrest Eiss tss :=
  h.crossEnvP (Ts := []) hag (fun ψ dp e _ {_ea} hr => hde ψ dp e hr) hT hTof hJ (ProjFree.nil _)

/-- **The block's representation crosses the change**: the stored
types' readings by `hde`, the members' and constructors' lookups by
`hF` (neither is a recursor entry), the residual index arguments by
`hres`, and the leaf and constructor equations by `hag` — every name
they value is stored (`memsFound`, the constructors' own lookups).
Everything else is the block model's and moves unchanged. -/
theorem IsBlockModel.crossEnvG {Ts : List Name} {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {T : Name} {cvT cvR : ConstantVal} {mI rP : Nat} {rules : List RecRule}
    {d : BlockModel V} {mm : Nat}
    (hF : ∀ (n : Name) (ci : ConstantInfo),
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      env₁.find? n = some ci → env₂.find? n = some ci)
    (hres : ∀ e : Expr, e.constsResolve env₁ = true → e.constsResolve env₂ = true)
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → m₂.acval n = m₁.acval n)
    (hde : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr), ProjFree Ts e → ∀ {ea : AnnotTerm},
      denoteMeta m₁.acval env₁ ψ dp e = some ea → denoteMeta m₂.acval env₂ ψ dp e = some ea)
    (hnpT : ProjFree Ts cvT.type)
    (hnpCtor : ∀ (mm' j : Nat) (cA : ConstantVal × Nat), mm' < d.k →
      (d.ctorsM mm')[j]? = some cA → ProjFree Ts cA.1.type)
    (h : IsBlockModel m₁ T cvT cvR mI rP rules d mm) :
    IsBlockModel m₂ T cvT cvR mI rP rules d mm := by
  have hmem : ∀ mm', mm' < d.k → (env₁.find? (d.memberName mm')).isSome = true := by
    intro mm' hmm'
    obtain ⟨cv, caps, hf⟩ := h.memsFound mm' hmm'
    rw [hf]
    rfl
  have hTs : (env₁.find? T).isSome = true := by
    have := hmem mm h.memberLt
    rwa [h.member] at this
  exact
    { memberLt := h.memberLt
      member := h.member
      strip := h.strip
      isProp := h.isProp
      mI := h.mI
      rP := h.rP
      rules := h.rules
      former := h.former.crossEnvP hde hnpT
      ctors := by
        intro mm' j cA hmm' hj
        obtain ⟨hfind, hlps, hdata⟩ := h.ctors mm' j cA hmm' hj
        refine ⟨hF _ _ (fun _ _ _ _ hcon => nomatch hcon) hfind, hlps, ?_⟩
        have hiK : ∀ i, i < cA.2 → i < (d.ksF mm' j).length := fun i hi => by
          rw [hdata.ksLen]; exact hi
        refine hdata.crossEnvP hag hde (hmem mm' hmm') (fun i hi hn => ?_) (fun i q hi hq => ?_)
          (hnpCtor mm' j cA hmm' hj)
        · rcases Nat.lt_or_ge (d.tgts mm' j i) d.k with hc | hc
          · exact hmem _ hc
          · rw [d.nestOf_some (Nat.not_lt.mpr hc)] at hn
            exact nomatch hn
        · have hlt := h.tgtsLt mm' j i hmm' (List.getElem?_eq_some_iff.mp hj).1 (hiK i hi)
          have hnt : ¬ d.tgts mm' j i < d.k := by
            intro hc
            rw [d.nestOf_none hc] at hq
            exact nomatch hq
          have hge := Nat.not_lt.mp hnt
          have hqlt : d.tgts mm' j i - d.k < d.nPins := by omega
          rw [d.nestOf_some hnt] at hq
          obtain rfl : q = d.tgts mm' j i - d.k := (Option.some.inj hq).symm
          obtain ⟨cv, caps, hf⟩ := h.pinsFound _ hqlt
          rw [hf]
          rfl
      memsFound := by
        intro mm' hmm'
        obtain ⟨cv, caps, hf⟩ := h.memsFound mm' hmm'
        exact ⟨cv, caps, hF _ _ (fun _ _ _ _ hcon => nomatch hcon) hf⟩
      pinsFound := by
        intro q hq
        obtain ⟨cv, caps, hf⟩ := h.pinsFound q hq
        exact ⟨cv, caps, hF _ _ (fun _ _ _ _ hcon => nomatch hcon) hf⟩
      tgtsLt := h.tgtsLt
      idxRes := fun mm' j cA hmm' hj e he => hres e (h.idxRes mm' j cA hmm' hj e he)
      uParams := h.uParams
      paramsIff := h.paramsIff
      idxOk := h.idxOk
      functor := h.functor
      fibre := h.fibre
      pinShape := h.pinShape
      pinMem := h.pinMem
      pinMono := h.pinMono
      pinLeaf := by
        intro q hq ψ ρ as is hsp hi
        obtain ⟨cv, caps, hf⟩ := h.pinsFound q hq
        rw [hag (d.pinAt q).J (by rw [hf]; rfl)]
        exact h.pinLeaf q hq ψ ρ as is hsp hi
      leaf := by
        intro ψ ρ as is hsp hi
        rw [hag T hTs]
        exact h.leaf ψ ρ as is hsp hi
      ctor := by
        intro mm' j cA hmm' hj ψ ρ as fs hsp hfit
        have hfind := (h.ctors mm' j cA hmm' hj).1
        rw [hag cA.1.name (by rw [hfind]; rfl)]
        exact h.ctor mm' j cA hmm' hj ψ ρ as fs hsp hfit
      mkZero := h.mkZero
      mkInj := h.mkInj }


/-- **The block's representation crosses the change**: the guarded
crossing at an environment where the tabled structures are FRESH — the
OLD containers' half, where the constructors' guards come from their
own types' resolution (`ProjFree.of_constsResolve`).  The block being
INSTALLED takes `crossEnvG` instead: its members are stored at the
environment its subjects are read at, and the guards come from the
install's `NoProjEnv` bookkeeping (DESIGN §U.41 (f)). -/
theorem IsBlockModel.crossEnvP {Ts : List Name} {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {T : Name} {cvT cvR : ConstantVal} {mI rP : Nat} {rules : List RecRule}
    {d : BlockModel V} {mm : Nat}
    (hF : ∀ (n : Name) (ci : ConstantInfo),
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      env₁.find? n = some ci → env₂.find? n = some ci)
    (hres : ∀ e : Expr, e.constsResolve env₁ = true → e.constsResolve env₂ = true)
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → m₂.acval n = m₁.acval n)
    (hde : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr), ProjFree Ts e → ∀ {ea : AnnotTerm},
      denoteMeta m₁.acval env₁ ψ dp e = some ea → denoteMeta m₂.acval env₂ ψ dp e = some ea)
    (hfresh : ∀ T' ∈ Ts, env₁.find? T' = none) (hnpT : ProjFree Ts cvT.type)
    (h : IsBlockModel m₁ T cvT cvR mI rP rules d mm) :
    IsBlockModel m₂ T cvT cvR mI rP rules d mm :=
  h.crossEnvG hF hres hag hde hnpT (fun mm' j cA hmm' hj =>
    ProjFree.of_constsResolve hfresh
      (m₁.wf _ (ConLeche.Semantics.Env.find?_mem (h.ctors mm' j cA hmm' hj).1)).2.2.1)

/-- The block's representation crosses any change the readings cross
(the unguarded crossing, `Ts := []`). -/
theorem IsBlockModel.crossEnv {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {T : Name} {cvT cvR : ConstantVal} {mI rP : Nat} {rules : List RecRule}
    {d : BlockModel V} {mm : Nat}
    (hF : ∀ (n : Name) (ci : ConstantInfo),
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      env₁.find? n = some ci → env₂.find? n = some ci)
    (hres : ∀ e : Expr, e.constsResolve env₁ = true → e.constsResolve env₂ = true)
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → m₂.acval n = m₁.acval n)
    (hde : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta m₁.acval env₁ ψ dp e = some ea → denoteMeta m₂.acval env₂ ψ dp e = some ea)
    (h : IsBlockModel m₁ T cvT cvR mI rP rules d mm) :
    IsBlockModel m₂ T cvT cvR mI rP rules d mm :=
  h.crossEnvP (Ts := []) hF hres hag (fun ψ dp e _ {_ea} hr => hde ψ dp e hr)
    (fun _ hT' => nomatch hT') (ProjFree.nil _)

/-- **The block at every member, at the members' own constants,
crosses the change** (task #315 M7-3 session 5): `IsBlockModels.crossEnv`
keeping the `ConstantVal`s named. -/
theorem IsBlockModelsAt.crossEnv {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {d : BlockModel V} {cvTs : Nat → ConstantVal}
    (hF : ∀ (n : Name) (ci : ConstantInfo),
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      env₁.find? n = some ci → env₂.find? n = some ci)
    (hres : ∀ e : Expr, e.constsResolve env₁ = true → e.constsResolve env₂ = true)
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → m₂.acval n = m₁.acval n)
    (hde : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta m₁.acval env₁ ψ dp e = some ea → denoteMeta m₂.acval env₂ ψ dp e = some ea)
    (h : IsBlockModelsAt m₁ d cvTs) :
    IsBlockModelsAt m₂ d cvTs := by
  intro c hc
  obtain ⟨cvR, mI, rP, rules, hb⟩ := h c hc
  exact ⟨cvR, mI, rP, rules, hb.crossEnv hF hres hag hde⟩

/-- The block at every member crosses the change. -/
theorem IsBlockModels.crossEnv {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {d : BlockModel V}
    (hF : ∀ (n : Name) (ci : ConstantInfo),
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      env₁.find? n = some ci → env₂.find? n = some ci)
    (hres : ∀ e : Expr, e.constsResolve env₁ = true → e.constsResolve env₂ = true)
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → m₂.acval n = m₁.acval n)
    (hde : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta m₁.acval env₁ ψ dp e = some ea → denoteMeta m₂.acval env₂ ψ dp e = some ea)
    (h : IsBlockModels m₁ d) :
    IsBlockModels m₂ d := by
  intro c hc
  obtain ⟨cvT, cvR, mI, rP, rules, hb⟩ := h c hc
  exact ⟨cvT, cvR, mI, rP, rules, hb.crossEnv hF hres hag hde⟩

/-- The members' typing crosses the change: the member names are
stored (`hreps`), so `hag` values them alike. -/
theorem FormersTyped.crossEnv {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {d : BlockModel V} {ψ : Name → Nat}
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → m₂.acval n = m₁.acval n)
    (hreps : IsBlockModels m₁ d) (h : FormersTyped m₁ d ψ) :
    FormersTyped m₂ d ψ := by
  intro t ht ρ
  obtain ⟨cvT, cvR, mI, rP, rules, hb⟩ := hreps t ht
  obtain ⟨cv, caps, hf⟩ := hb.memsFound t ht
  rw [hag (d.memberName t) (by rw [hf]; rfl)]
  exact h t ht ρ

/-- The constructors' typing crosses the change: both the
constructor's own name and its member's are stored (`hreps`). -/
theorem CtorsTyped.crossEnv {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {d : BlockModel V} {ψ : Name → Nat}
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → m₂.acval n = m₁.acval n)
    (hreps : IsBlockModels m₁ d) (h : CtorsTyped m₁ d ψ) :
    CtorsTyped m₂ d ψ := by
  intro c hc j cA hj ρ
  obtain ⟨cvT, cvR, mI, rP, rules, hb⟩ := hreps c hc
  obtain ⟨cv, caps, hf⟩ := hb.memsFound c hc
  have hbody : ctorBodyAVI m₂ (d.memberName c) d.nP cA.2 ψ (d.esF c j ψ)
      = ctorBodyAVI m₁ (d.memberName c) d.nP cA.2 ψ (d.esF c j ψ) := by
    unfold ctorBodyAVI
    rw [hag (d.memberName c) (by rw [hf]; rfl)]
  have hfind := (hb.ctors c j cA hc hj).1
  rw [hag cA.1.name (by rw [hfind]; rfl), hbody]
  exact h c hc j cA hj ρ

/-- The pins' typing crosses the change: the pins' containers are
stored (`pinsFound`), so `hag` values them alike. -/
theorem PinsTyped.crossEnv {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {d : BlockModel V} {ψ : Name → Nat}
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → m₂.acval n = m₁.acval n)
    (hreps : IsBlockModels m₁ d) (hk : 0 < d.k) (h : PinsTyped m₁ d ψ) :
    PinsTyped m₂ d ψ := by
  intro q hq ρ
  obtain ⟨cvT, cvR, mI, rP, rules, hb⟩ := hreps 0 hk
  obtain ⟨cv, caps, hf⟩ := hb.pinsFound q hq
  rw [hag (d.pinAt q).J (by rw [hf]; rfl)]
  exact h q hq ρ

/-- A member's store fact crosses the change: the lookup by `hF` (a
member is stored as an inductive, never a recursor), its former's data
by `hde`. -/
theorem MemberStored.crossEnv {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {lps : List Name} {nP : Nat} {f : MutualFormerA} {resSort : Level}
    {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hF : ∀ (n : Name) (ci : ConstantInfo),
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      env₁.find? n = some ci → env₂.find? n = some ci)
    (hde : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta m₁.acval env₁ ψ dp e = some ea → denoteMeta m₂.acval env₂ ψ dp e = some ea)
    (h : MemberStored m₁ lps nP f resSort pps) :
    MemberStored m₂ lps nP f resSort pps where
  find := hF _ _ (fun _ _ _ _ hcon => nomatch hcon) h.find
  lps := h.lps
  strip := h.strip
  sEq := h.sEq
  data := h.data.crossEnv' hde

/-- The recursor type's reading crosses the change (its conclusion
values no name). -/
theorem MutualRecData.crossEnv {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {cvR : ConstantVal} {nP k n nIdx mm : Nat} {elimL : Level}
    {rds : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hde : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta m₁.acval env₁ ψ dp e = some ea → denoteMeta m₂.acval env₂ ψ dp e = some ea)
    (h : MutualRecData m₁ cvR nP k n nIdx mm elimL rds) :
    MutualRecData m₂ cvR nP k n nIdx mm elimL rds where
  read ψ := hde ψ 0 cvR.type (h.read ψ)
  len := h.len
  bits := h.bits
  okTy := h.okTy
  below := h.below
  params := h.params

/-! ## Instance (i): the recursors' rule-less conses -/

omit [SetTheory V] in
/-- **The provisioned recursors, as an environment extension**: every
stored lookup survives, the literal guards only grow, and no projection
table appears (`consMutualCtors_extend` at `provisionMutualRecs`). -/
theorem provisionMutualRecs_extend {b : MutualBlock} {fms : List MutualFormerA} :
    ∀ {l : List (ConstantVal × Nat)} {env : Env},
      (∀ x ∈ l, env.find? x.1.name = none) →
      (l.map (·.1.name)).Nodup →
      FindPreserved env (ConLeche.provisionMutualRecs b fms l env) ∧
      LitGuardsMono env (ConLeche.provisionMutualRecs b fms l env) ∧
      (∀ (sn : Name) (i : Nat), env.findProj? sn i = none →
        (ConLeche.provisionMutualRecs b fms l env).findProj? sn i = none)
  | [], _, _, _ => ⟨fun h => h, ⟨fun h => h, fun h => h⟩, fun _ _ h => h⟩
  | x :: rest, env, hfresh, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have hx : env.find? x.1.name = none := hfresh x List.mem_cons_self
    have hfresh' : ∀ g ∈ rest,
        (Env.mk (ConstantInfo.recInfo x.1
          (b.rulePrefix + (fms.getD x.2 default).nIdx) b.rulePrefix [] :: env.consts)).find?
            g.1.name = none := by
      intro g hg
      refine (find?_cons_of_name_ne (c := .recInfo x.1
        (b.rulePrefix + (fms.getD x.2 default).nIdx) b.rulePrefix []) (fun hh => ?_)).trans
        (hfresh g (List.mem_cons_of_mem _ hg))
      refine hnd.1 ?_
      have hnm : x.1.name = g.1.name := hh
      rw [hnm]
      exact List.mem_map_of_mem hg
    obtain ⟨hFp, hL, hP⟩ := provisionMutualRecs_extend (b := b) (fms := fms) hfresh' hnd.2
    simp only [ConLeche.provisionMutualRecs]
    refine ⟨fun h => hFp (findPreserved_cons hx h),
      ⟨fun h => hL.1 ((litGuardsMono_cons hx).1 h),
        fun h => hL.2 ((litGuardsMono_cons hx).2 h)⟩, fun sn i h => hP sn i ?_⟩
    exact ConLeche.Verify.findProj?_cons_of_base_none
      (c₀ := .recInfo x.1 (b.rulePrefix + (fms.getD x.2 default).nIdx) b.rulePrefix [])
      (fun _ hh => nomatch hh) sn i h

omit [SetTheory V] in
/-- Resolution survives any extension that preserves lookups. -/
theorem constsResolve_of_findPreserved {env env' : Env} (hF : FindPreserved env env') :
    ∀ e : Expr, e.constsResolve env = true → e.constsResolve env' = true :=
  fun e => Expr.constsResolve_of_find
    (fun n hn => by
      cases hf : env.find? n with
      | none => rw [hf] at hn; exact nomatch hn
      | some ci => rw [hF hf]; rfl)

/-- **`hde` at the provision**: the models' valuations agree at every
stored name, so the reading crosses the `k` fresh rule-less conses. -/
theorem provision_hde {b : MutualBlock} {fms : List MutualFormerA}
    {l : List (ConstantVal × Nat)} {env : Env} {m : EnvModel V env}
    {mP : EnvModel V (ConLeche.provisionMutualRecs b fms l env)}
    (hfresh : ∀ x ∈ l, env.find? x.1.name = none)
    (hnd : (l.map (·.1.name)).Nodup)
    (hag : ∀ n : Name, (env.find? n).isSome = true → mP.acval n = m.acval n) :
    ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta m.acval env ψ dp e = some ea →
        denoteMeta mP.acval (ConLeche.provisionMutualRecs b fms l env) ψ dp e = some ea := by
  obtain ⟨hFp, hG, hproj⟩ := provisionMutualRecs_extend hfresh hnd
  intro ψ dp e ea hread
  refine denoteMeta_env_mono hFp hG hproj dp e ?_
  rw [← denoteMeta_acval_congr (acval₂ := mP.acval) (fun n hn => (hag n hn).symm) dp e]
  exact hread

/-! ## Instance (ii): the recursors' store, a rule-list swap -/

omit [SetTheory V] in
/-- **`hres` at the swap**: the swap stores the same names. -/
theorem constsResolve_of_swapCongr {env₁ env₂ : Env} (hcg : ConLeche.SwapCongr env₁ env₂) :
    ∀ e : Expr, e.constsResolve env₁ = true → e.constsResolve env₂ = true := by
  intro e h
  rw [← Expr.constsResolve_congr hcg.isSomeEq e]
  exact h

/-- **`hde` at the swap**: the reading is an equation across a swap
congruence (`denoteMeta_swap`), and the two carriers share their
valuation. -/
theorem swap_hde {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    (hcg : ConLeche.SwapCongr env₁ env₂) (hac : m₂.acval = m₁.acval) :
    ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta m₁.acval env₁ ψ dp e = some ea →
        denoteMeta m₂.acval env₂ ψ dp e = some ea := by
  intro ψ dp e ea h
  rw [hac, ← denoteMeta_swap hcg ψ dp e]
  exact h

end ConLeche.Model
