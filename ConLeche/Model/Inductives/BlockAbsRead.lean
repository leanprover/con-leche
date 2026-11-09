module

import ConLeche.Model.OpenedCtx
public import ConLeche.Model.Inductives.BlockRep
import ConLeche.Model.Env.EnvModelM
import ConLeche.Model.Inductives.StructFrameKit
public import ConLeche.Model.Reading.LpDefF
import ConLeche.Model.Env.CanonCrest
import ConLeche.Model.Install
import ConLeche.Model.Inductives.DeclaredShapes
import ConLeche.Model.Inductives.BlockHoleRead
public import ConLeche.Verify.Inductives.PositivityInv

public section

/-!
# The fields with holes, read off the walk's normal form

A uniform block's datum carries its constructors' fields WITH HOLES as a
primary field (`BlockData.absFF`), chosen once — at the dummy carrier —
as the READING of the positivity walk's NORMAL FORM of the constructor
(`BlockData.nfFF`, the run's output: the stored, declared constructor
type with the members abstracted to the holes and the parameters
instantiated, each field reduced by the walk), read at `nP + k`, its
first `nF` domains (`nfFieldsRead`).  No field is classified: the flat
shape, the applied holes and the override law of these fields are the
stored field shape facts' (`DeclaredFieldShapes`), which the walk's run
produces.

`BlockAbsRead` is the reading fact at a model: the normal form reads as
the Π-tower over the datum's fields with holes ending in the component's
hole at the parameters and the result index readings, and the DECLARED
type's canonical crest reads as a Π-tower with the same body whose fields
read like the fields with holes at every frame satisfying the hole
context (`FieldsEqOn`, whnf's denotation lemma through the walk).  It
crosses every cons the stored type crosses (`BlockAbsRead.cross`); the
readings of the normal form depend on the level assignment only at the
block's level parameters (`nfFieldsRead_params`) and — the normal form
looking up no member — on the leaves only off the members
(`nfFieldsRead_agree`), so the dummy and the real carrier read them
alike.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name Level ConstantInfo ConstantVal instPisWith NestCtx
  openPisAtFvars BlockShape)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The normal form's field readings -/

/-- **The fields with holes of a normal form `N`** at a leaf assignment:
its reading at depth `D`, its first `nF` domains (`[]` where the reading
is missing). -/
@[expose] noncomputable def nfFieldsRead (acval : Name → (Name → Nat) → Term) (env : Env)
    (D nF : Nat) (N : Expr) (ψ : Name → Nat) : List Term :=
  match denote acval env ψ D N with
  | some t => ((stripPisAV nF t).map fun p => p.1).getD []
  | none => []

/-- The fields' readings at a reading of the normal form. -/
theorem nfFieldsRead_eq {acval : Name → (Name → Nat) → Term} {env : Env} {D nF : Nat}
    {N : Expr} {ψ : Name → Nat} {ab : List Term} {B : Term}
    (hr : denote acval env ψ D N = some (mkPisAV ab B)) (hl : ab.length = nF) :
    nfFieldsRead acval env D nF N ψ = ab := by
  unfold nfFieldsRead
  rw [hr]
  simp only
  rw [← hl, stripPisAV_mkPisAV]
  rfl

/-- **The fields' readings depend on the level assignment at the normal
form's footprint only.** -/
theorem nfFieldsRead_params {env : Env} (m : EnvModel V env) {ps : List Name} {D nF : Nat}
    {N : Expr} (hl : lpDefF ps N = true) {ψ₁ ψ₂ : Name → Nat} (hφ : ∀ p ∈ ps, ψ₁ p = ψ₂ p) :
    nfFieldsRead m.acval env D nF N ψ₁ = nfFieldsRead m.acval env D nF N ψ₂ := by
  unfold nfFieldsRead
  rw [denote_params_extF m hφ D N hl]

/-- **The fields' readings consult the leaves off the members only**: the
normal form mentions no member constant, and no literal-support constant
a reading consults is a member. -/
theorem nfFieldsRead_agree {acval₁ acval₂ : Name → (Name → Nat) → Term} {env : Env}
    {names : List Name} {D nF : Nat} {N : Expr}
    (hag : ∀ n, n ∉ names → acval₁ n = acval₂ n)
    (hocc : N.nestOcc names 0 0 = false)
    (hnat : ConLeche.natLitSupported env = true →
      ConLeche.natZeroName ∉ names ∧ ConLeche.natSuccName ∉ names)
    (hstr : ConLeche.strLitSupported env = true →
      ConLeche.stringOfListName ∉ names ∧ ConLeche.listNilName ∉ names ∧
        ConLeche.listConsName ∉ names ∧ ConLeche.charName ∉ names ∧
        ConLeche.charOfNatName ∉ names) (ψ : Name → Nat) :
    nfFieldsRead acval₁ env D nF N ψ = nfFieldsRead acval₂ env D nF N ψ := by
  unfold nfFieldsRead
  rw [denote_agree_of_readsAt hag _ N (Expr.readsAt_of_nestOcc hnat hstr _ hocc)]

/-- **The canonical crest consults the leaves off the members only**: it
mentions no member constant (from official's uniform check), and no
literal-support constant a reading consults is a member. -/
theorem canonCrest_read_agree {acval₁ acval₂ : Name → (Name → Nat) → Term} {env : Env}
    {names : List Name} {A : Expr}
    (hag : ∀ n, n ∉ names → acval₁ n = acval₂ n)
    (hocc : A.nestOcc names 0 0 = false)
    (hnat : ConLeche.natLitSupported env = true →
      ConLeche.natZeroName ∉ names ∧ ConLeche.natSuccName ∉ names)
    (hstr : ConLeche.strLitSupported env = true →
      ConLeche.stringOfListName ∉ names ∧ ConLeche.listNilName ∉ names ∧
        ConLeche.listConsName ∉ names ∧ ConLeche.charName ∉ names ∧
        ConLeche.charOfNatName ∉ names)
    (ψ : Name → Nat) (d : Nat) :
    denote acval₁ env ψ d A = denote acval₂ env ψ d A :=
  denote_agree_of_readsAt hag _ A (Expr.readsAt_of_nestOcc hnat hstr _ hocc)

/-- **The walk's crest is the canonical crest, up to erasure**: the kernel
puts the canonical parameter variables and holes back in with their
annotations only (`nestKeyMap`: parameters at `0 ..< nP`, holes at
`nP + t`). -/
theorem canonCrest_of_walk {ctx : NestCtx} {holes : List Expr} {cty crest : Expr}
    (hpar : ∀ (i : Nat) (x : Expr), ctx.params[i]? = some x → ∃ t, x = .fvar i t)
    (hplen : ctx.params.length = ctx.nP)
    (hholes : ∀ (t : Nat) (x : Expr), holes[t]? = some x → ∃ t', x = .fvar (ctx.nP + t) t')
    (hcrest : ConLeche.nestCrest ctx.names (ctx.lps.map .param) ctx.params holes cty
      = some crest) :
    ∃ A, ConLeche.nestCanonCrest ctx.names (ctx.lps.map .param) ctx.nP cty = some A ∧
      Expr.ErasedEq crest A := by
  unfold ConLeche.nestCrest at hcrest
  rw [hplen] at hcrest
  obtain ⟨A, hA, rfl⟩ := Option.map_eq_some_iff.mp hcrest
  refine ⟨A, hA, replaceFVars_erasedEq_idx (fun i a ha => ?_) A⟩
  unfold ConLeche.nestKeyMap at ha
  split at ha
  · obtain ⟨t, rfl⟩ := hpar i a ha
    exact ⟨t, rfl⟩
  · obtain ⟨t', rfl⟩ := hholes _ a ha
    exact ⟨t', by congr 1; omega⟩

omit [SetTheory V] in
/-- **The canonical crest names no member constant, from the positivity
stage's run** (official's uniform check `nestUniform`). -/
theorem canonOcc_of_positivity {ops : ConLeche.CheckerOps ConLeche.CheckM} {env₁ : Env}
    {find? : Name → Option ConstantInfo} {p : BlockShape}
    {posKs : List (List (List ConLeche.NestFieldKind)) × List (List Expr) × ConLeche.NestState}
    (hrun : ConLeche.PositivityRun ops env₁ find? p posKs.1 posKs.2.1 posKs.2.2)
    {d : BlockData V} {lps : List Name}
    (hnames : p.memberNames = d.memberNames) (hlps : p.lps = lps) (hnP : p.nP = d.nP)
    (hmemberCtors : ∀ c, c < d.k → p.memberCtors[c]? = some (d.ctorsM c))
    (hlpsA : ∀ (c j : Nat) (ctor : ConstantVal × Nat), (d.ctorsM c)[j]? = some ctor →
      ctor.1.levelParams = lps) :
    ∀ c, c < d.k → ∀ (j : Nat) (ctor : ConstantVal × Nat), (d.ctorsM c)[j]? = some ctor →
      ∃ A, ConLeche.nestCanonCrest d.memberNames (lps.map .param) d.nP ctor.1.type = some A ∧
        A.nestOcc d.memberNames 0 0 = false := by
  obtain ⟨cvTa0, fvsP, rest, holes, -, -, -, hall⟩ := ConLeche.checkBlockPositivity_m2 hrun
  intro c hc j ctor hcj
  obtain ⟨A, hA, hocc⟩ := hall c (d.ctorsM c) (hmemberCtors c hc) j ctor hcj
  unfold ConLeche.nestRootCanon at hA
  have hn : (p.nestCtx fvsP find?).names = d.memberNames := hnames
  have hl : (p.nestCtx fvsP find?).lps = lps := hlps
  have hP : (p.nestCtx fvsP find?).nP = d.nP := hnP
  rw [hn, hl, hP, ← hlpsA c j ctor hcj, Expr.instantiateLevelParams_self] at hA
  rw [hn] at hocc
  exact ⟨A, by rw [hlpsA c j ctor hcj] at hA; exact hA, hocc⟩

/-! ## The reading fact at a model -/

omit [SetTheory V] in
/-- Every constant bound before a cons is bound after it. -/
theorem _root_.ConLeche.Verify.ConstsBound.mono_cons {env : Env} {c₀ : ConstantInfo} :
    ∀ {e : Expr}, ConstsBound env e → ConstsBound ⟨c₀ :: env.consts, env.tables⟩ e := by
  intro e
  induction e with
  | const n us =>
    intro h
    simp only [constsBound_const, ConLeche.Env.find?, List.find?_cons] at h ⊢
    split
    · rfl
    · exact h
  | app f a ihf iha => intro h; simp only [constsBound_app] at h ⊢; exact ⟨ihf h.1, iha h.2⟩
  | lam t b iht ihb => intro h; simp only [constsBound_lam] at h ⊢; exact ⟨iht h.1, ihb h.2⟩
  | forallE t b iht ihb =>
    intro h; simp only [constsBound_forallE] at h ⊢; exact ⟨iht h.1, ihb h.2⟩
  | letE t v b iht ihv ihb =>
    intro h; simp only [constsBound_letE] at h ⊢; exact ⟨iht h.1, ihv h.2.1, ihb h.2.2⟩
  | proj s i x ih => intro h; simp only [constsBound_proj] at h ⊢; exact ih h
  | fvar i ty ih => intro h; simp only [constsBound_fvar] at h ⊢; exact ih h
  | bvar => intro _; simp
  | sort => intro _; simp
  | lit => intro _; simp

/-- **The hole context** at a level assignment: the parameters (member
`0`'s former's), then one hole per member, typed by its hole type — the
member's index tower over the parameters, lifted past the earlier holes
(a hole stands for the member's whole application to the parameters). -/
@[expose] def BlockData.holeCtx (d : BlockData V) (ψ : Name → Nat) : List Term :=
  d.params ψ ++ (List.range d.k).map fun t =>
    (mkPisAV ((d.ppsM t ψ).drop d.nP) (.sort (d.w ψ))).liftN t 0

/-- **The datum's fields with holes are the normal form's reading** at
the model, and the DECLARED constructor type's canonical crest reads as a
Π-tower with the same body whose fields read like them at every frame
satisfying the hole context: component `c`'s constructor `j` (`ctor`). -/
@[expose] def BlockAbsRead {env : Env} (m : EnvModel V env) (d : BlockData V) (lps : List Name)
    (c j : Nat) (ctor : ConstantVal × Nat) : Prop :=
  ConstsBound env (d.nfFF c j) ∧
  ∃ A, ConLeche.nestCanonCrest d.memberNames (lps.map .param) d.nP ctor.1.type = some A ∧
    ∀ ψ : Name → Nat, ∃ abD abN : List Term,
      denote m.acval env ψ (d.nP + d.k) A
        = some (mkPisAV abD (Term.mkAppN (.bvar (ctor.2 + (d.k - 1 - c))) (d.absE ψ c j))) ∧
      denote m.acval env ψ (d.nP + d.k) (d.nfFF c j)
        = some (mkPisAV abN (Term.mkAppN (.bvar (ctor.2 + (d.k - 1 - c))) (d.absE ψ c j))) ∧
      abD.length = ctor.2 ∧ abN.length = ctor.2 ∧
      abN = d.absF ψ c j ∧
      FieldsEqOn V (d.holeCtx ψ).reverse abD (d.absF ψ c j)

/-- **The reading fact crosses a cons** the stored type crosses. -/
theorem BlockAbsRead.cross {env : Env} {m : EnvModel V env} {d : BlockData V} {lps : List Name}
    {c j : Nat} {ctor : ConstantVal × Nat} (h : BlockAbsRead m d lps c j ctor)
    {c₀ : ConstantInfo} {B : (Name → Nat) → Term}
    (hfresh : env.find? c₀.name = none)
    (hcb : ConstsBound env ctor.1.type)
    (m₂ : EnvModel V ⟨c₀ :: env.consts, env.tables⟩) (hac : m₂.acval = acvalWith m.acval c₀.name B) :
    BlockAbsRead m₂ d lps c j ctor := by
  obtain ⟨hnb, A, hA, hr⟩ := h
  refine ⟨ConstsBound.mono_cons hnb, A, hA, fun ψ => ?_⟩
  obtain ⟨abD, abN, hab, habN, hl, hlN, habF, hEq⟩ := hr ψ
  refine ⟨abD, abN, ?_, ?_, hl, hlN, habF, hEq⟩
  · rw [hac]
    exact denote_cons_mono hfresh ψ _ (canonOf_constsBound hcb (.inl ⟨_, _, _, hA⟩)) hab
  · rw [hac]
    exact denote_cons_mono hfresh ψ _ hnb habN

end ConLeche.Model
