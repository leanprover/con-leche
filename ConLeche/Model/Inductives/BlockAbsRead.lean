module

public import ConLeche.Model.Inductives.BlockRep
import ConLeche.Model.Annot.EnvModelM
import ConLeche.Model.Inductives.StructRead
public import ConLeche.Model.Annot.LpDefF
import ConLeche.Model.Annot.CanonCrest
import ConLeche.Model.Inductives.StructStageFormer
import ConLeche.Model.Install
import ConLeche.Model.Inductives.StoredShapes
public import ConLeche.Model.Inductives.BlockHoleRead
import ConLeche.Model.Annot.BitRename
import ConLeche.Verify.Inductives.PositivityInv
import ConLeche.Verify.Inductives.NestScope

public section

/-!
# The fields with holes, read off the walk's normal form (lane HOLE2 stage E2; lane ALPHA1)

A uniform block's datum carries its constructors' fields WITH HOLES as a
primary field (`BlockData.absFF`), chosen once — at the dummy carrier —
as the READING of the positivity walk's NORMAL FORM of the constructor
(`BlockData.nfFF`, the run's output: the stored, declared constructor
type with the members abstracted to the holes and the parameters
instantiated, each field reduced by the walk), read at `nP + k`, its
first `nF` domains (`nfFieldsRead`).  No field is classified: the flat
shape, the applied holes and the override law of these fields are the
stored field shape facts' (`StoredFieldShapes`), which the walk's run
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
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal instPisWith NestCtx nestAbstract
  openPisAtFvars BlockParts)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The normal form's field readings -/

/-- **The fields with holes of a normal form `N`** at a leaf assignment:
its reading at depth `D`, its first `nF` domains (`[]` where the reading
is missing). -/
@[expose] noncomputable def nfFieldsRead (acval : Name → (Name → Nat) → AnnotTerm) (env : Env)
    (D nF : Nat) (N : Expr) (ψ : Name → Nat) : List AnnotTerm :=
  match denoteMeta acval env ψ D N with
  | some t => ((stripPisAV nF t).map fun p => p.1.map (·.2.2)).getD []
  | none => []

/-- The fields' readings at a reading of the normal form. -/
theorem nfFieldsRead_eq {acval : Name → (Name → Nat) → AnnotTerm} {env : Env} {D nF : Nat}
    {N : Expr} {ψ : Name → Nat} {ab : List (Nat × Nat × AnnotTerm)} {B : AnnotTerm}
    (hr : denoteMeta acval env ψ D N = some (mkPisAV ab B)) (hl : ab.length = nF) :
    nfFieldsRead acval env D nF N ψ = ab.map (·.2.2) := by
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
  rw [denoteMeta_params_extF m hφ D N hl]

/-- **The fields' readings consult the leaves off the members only**: the
normal form mentions no member constant, and no literal-support constant
a reading consults is a member. -/
theorem nfFieldsRead_agree {acval₁ acval₂ : Name → (Name → Nat) → AnnotTerm} {env : Env}
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
  rw [denoteMeta_agree_of_readsAt hag _ N (Expr.readsAt_of_nestOcc hnat hstr _ hocc)]

/-- An instantiation at arguments looking up only `P`-names keeps it. -/
theorem Expr.ReadsAt.instPisWith {P : Name → Prop} {env : Env} :
    ∀ {vs : List Expr} {e r : Expr}, (∀ v ∈ vs, Expr.ReadsAt P env v) →
      instPisWith vs e = some r → Expr.ReadsAt P env e → Expr.ReadsAt P env r
  | [], e, r, _, h, he => by
    simp only [ConLeche.instPisWith, Option.some.injEq] at h
    exact h ▸ he
  | v :: vs, e, r, hvs, h, he => by
    match e, h with
    | .forallE t b m, h =>
      have h' : ConLeche.instPisWith vs (b.instantiate1 v) = some r := h
      exact Expr.ReadsAt.instPisWith (fun x hx => hvs x (List.mem_cons_of_mem _ hx)) h'
        (Expr.ReadsAt.instantiate1 (hvs v List.mem_cons_self) b 0 he.2)

/-- **The canonical crest consults the leaves off the members only**: the
member-abstracted type mentions no member (M2′), and no literal-support
constant a reading consults is a member. -/
theorem canonCrest_read_agree {acval₁ acval₂ : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {names lps : List Name} {nP k : Nat} {e A : Expr}
    (hag : ∀ n, n ∉ names → acval₁ n = acval₂ n)
    (hocc : (canonAbs names lps nP k e).nestOcc names 0 0 = false)
    (hnat : ConLeche.natLitSupported env = true →
      ConLeche.natZeroName ∉ names ∧ ConLeche.natSuccName ∉ names)
    (hstr : ConLeche.strLitSupported env = true →
      ConLeche.stringOfListName ∉ names ∧ ConLeche.listNilName ∉ names ∧
        ConLeche.listConsName ∉ names ∧ ConLeche.charName ∉ names ∧
        ConLeche.charOfNatName ∉ names)
    (hA : instPisWith (canonParams nP) (canonAbs names lps nP k e) = some A)
    (ψ : Name → Nat) (d : Nat) :
    denoteMeta acval₁ env ψ d A = denoteMeta acval₂ env ψ d A := by
  have hR : Expr.ReadsAt (· ∉ names) env A :=
    Expr.ReadsAt.instPisWith (fun x hx => by
        obtain ⟨i, -, rfl⟩ := mem_canonParams hx
        trivial)
      hA (Expr.readsAt_of_nestOcc hnat hstr _ hocc)
  exact denoteMeta_agree_of_readsAt hag _ A hR

/-- **The walk's term is the canonical crest, up to erasure**: a stored
type member-abstracted at holes at `nP + t` and instantiated at
parameters at `0 ..< nP` — whatever their annotations — is erasure-equal
to its canonical abstraction (`canonAbs`, `canonParams`). -/
theorem canonCrest_of_walk {ctx : NestCtx} {holes : List Expr} {k : Nat} {ty crest : Expr}
    (hpar : ∀ (i : Nat) (x : Expr), ctx.params[i]? = some x → ∃ t, x = .fvar i t)
    (hplen : ctx.params.length = ctx.nP)
    (hholes : ∀ (t : Nat) (x : Expr), holes[t]? = some x → ∃ t', x = .fvar (ctx.nP + t) t')
    (hlenH : holes.length = k)
    (hcrest : instPisWith ctx.params (nestAbstract ctx holes ty) = some crest) :
    ∃ A, instPisWith (canonParams ctx.nP) (canonAbs ctx.names ctx.lps ctx.nP k ty) = some A ∧
      Expr.ErasedEq crest A := by
  have hH : Expr.ErasedEqL holes (canonHoles ctx.nP k) :=
    erasedEqL_of_fvarIdx _ _ ctx.nP hholes
      (fun t x hx => by
        have ht : t < k := by
          have := (List.getElem?_eq_some_iff.mp hx).1; rwa [canonHoles_length] at this
        rw [canonHoles_getElem? ht] at hx
        exact ⟨_, (Option.some.inj hx).symm⟩)
      (by rw [hlenH, canonHoles_length])
  have hP : Expr.ErasedEqL ctx.params (canonParams ctx.nP) :=
    erasedEqL_of_fvarIdx _ _ 0 (fun i x hx => by rw [Nat.zero_add]; exact hpar i x hx)
      (fun i x hx => ⟨.sort .zero, by rw [canonParams_getElem? hx, Nat.zero_add]⟩)
      (by rw [hplen, canonParams_length])
  exact instPisWith_erasedEq hP (nestAbstract_erasedEq rfl rfl hH ty) hcrest

omit [SetTheory V] in
/-- **M2′ at the canonical holes, from the positivity stage's run**: the
stage checked every constructor's member-abstracted type for a member
constant (`nestNoMemberConst`) at its own holes; the check does not see
the holes' annotations. -/
theorem canonOcc_of_positivity {ops : ConLeche.CheckerOps ConLeche.CheckM} {env₁ : Env}
    {find? : Name → Option ConstantInfo} {consts : List ConstantInfo} {p : BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {posKs : List (List (List ConLeche.NestFieldKind)) × List (List Expr)}
    {nst : Bool}
    (hrun : ConLeche.checkBlockPositivity ops env₁ find? consts p cvTas ctorsAs nst = .ok posKs)
    {d : BlockData V} {lps : List Name}
    (hnames : p.memberNames = d.memberNames) (hlps : p.lps = lps)
    (hk : d.k = d.memberNames.length)
    (hctorsAs : ∀ c, c < d.k → ctorsAs[c]? = some (d.ctorsM c)) :
    ∀ c, c < d.k → ∀ (j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      (canonAbs d.memberNames lps d.nP d.k cA.1.type).nestOcc d.memberNames 0 0 = false := by
  obtain ⟨cvTa0, fvsP, rest, holes, -, -, hholes, hall⟩ :=
    ConLeche.checkBlockPositivity_inv_gen hrun
  intro c hc j cA hcj
  obtain ⟨-, -, -, -, -, -, -, -, hocc⟩ := hall c (d.ctorsM c) (hctorsAs c hc) j cA hcj
  have hn : (p.nestCtx fvsP find? consts).names = d.memberNames := hnames
  rw [hn] at hocc
  rw [← hocc]
  refine nestOcc_nestAbstract_blind (by rw [hn]; rfl) (by rw [← hlps]; rfl) ?_
    (fun h hm => ?_) (fun h hm => ?_) _ _
  · rw [canonHoles_length, ConLeche.nestHoles_length hholes, hn, hk]
  · obtain ⟨mm, -, rfl⟩ := mem_canonHoles hm
    exact ⟨_, _, rfl⟩
  · obtain ⟨i, cv, caps, -, rfl⟩ := ConLeche.nestHoles_mem hholes h hm
    exact ⟨_, _, rfl⟩

/-! ## The reading fact at a model -/

omit [SetTheory V] in
/-- Every constant bound before a cons is bound after it. -/
theorem ConstsBound.mono_cons {env : Env} {c₀ : ConstantInfo} :
    ∀ {e : Expr}, ConstsBound env e → ConstsBound ⟨c₀ :: env.consts⟩ e := by
  intro e
  induction e with
  | const n us =>
    intro h
    simp only [constsBound_const, ConLeche.Env.find?, List.find?_cons] at h ⊢
    split
    · rfl
    · exact h
  | app f a ihf iha => intro h; simp only [constsBound_app] at h ⊢; exact ⟨ihf h.1, iha h.2⟩
  | lam t b m iht ihb => intro h; simp only [constsBound_lam] at h ⊢; exact ⟨iht h.1, ihb h.2⟩
  | forallE t b m iht ihb =>
    intro h; simp only [constsBound_forallE] at h ⊢; exact ⟨iht h.1, ihb h.2⟩
  | letE t v b iht ihv ihb =>
    intro h; simp only [constsBound_letE] at h ⊢; exact ⟨iht h.1, ihv h.2.1, ihb h.2.2⟩
  | proj s i x ih => intro h; simp only [constsBound_proj] at h ⊢; exact ih h
  | fvar i ty ih => intro h; simp only [constsBound_fvar] at h ⊢; exact ih h
  | bvar => intro _; simp
  | sort => intro _; simp
  | lit => intro _; simp


/-- **The hole context** at a level assignment: the parameters (member
`0`'s former's), then one hole per member, typed by the member's former
type. -/
@[expose] def BlockData.holeCtx (d : BlockData V) (ψ : Name → Nat) : List AnnotTerm :=
  d.params ψ ++ (List.range d.k).map fun t => mkPisAV (d.ppsM t ψ) (.sort (d.w ψ))

/-- **The datum's fields with holes are the normal form's reading** at
the model, and the DECLARED constructor type's canonical crest reads as a
Π-tower with the same body whose fields read like them at every frame
satisfying the hole context: component `c`'s constructor `j` (`cA`). -/
@[expose] def BlockAbsRead {env : Env} (m : EnvModel V env) (d : BlockData V) (lps : List Name)
    (c j : Nat) (cA : ConstantVal × Nat) : Prop :=
  ConstsBound env (d.nfFF c j) ∧
  ∃ A, instPisWith (canonParams d.nP) (canonAbs d.memberNames lps d.nP d.k cA.1.type) = some A ∧
    ∀ ψ : Name → Nat, ∃ abD abN : List (Nat × Nat × AnnotTerm),
      denoteMeta m.acval env ψ (d.nP + d.k) A
        = some (mkPisAV abD (AnnotTerm.mkAppN (.bvar (cA.2 + (d.k - 1 - c)))
            (paramBvarsAt d.nP (d.nP + d.k + cA.2) ++ d.absE ψ c j))) ∧
      denoteMeta m.acval env ψ (d.nP + d.k) (d.nfFF c j)
        = some (mkPisAV abN (AnnotTerm.mkAppN (.bvar (cA.2 + (d.k - 1 - c)))
            (paramBvarsAt d.nP (d.nP + d.k + cA.2) ++ d.absE ψ c j))) ∧
      abD.length = cA.2 ∧ abN.length = cA.2 ∧
      abD.map (fun x => (x.1, x.2.1)) = abN.map (fun x => (x.1, x.2.1)) ∧
      abN.map (·.2.2) = d.absF ψ c j ∧
      FieldsEqOn V (d.holeCtx ψ).reverse (abD.map (·.2.2)) (d.absF ψ c j)

/-- **The reading fact crosses a cons** the stored type crosses. -/
theorem BlockAbsRead.cross {env : Env} {m : EnvModel V env} {d : BlockData V} {lps : List Name}
    {c j : Nat} {cA : ConstantVal × Nat} (h : BlockAbsRead m d lps c j cA)
    {c₀ : ConstantInfo} {B : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? c₀.name = none) (hat : ∀ e : Expr, ConsCrossAt c₀ e)
    (hcb : ConstsBound env cA.1.type)
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩) (hac : m₂.acval = acvalWith m.acval c₀.name B) :
    BlockAbsRead m₂ d lps c j cA := by
  obtain ⟨hnb, A, hA, hr⟩ := h
  refine ⟨ConstsBound.mono_cons hnb, A, hA, fun ψ => ?_⟩
  obtain ⟨abD, abN, hab, habN, hl, hlN, hbits, habF, hEq⟩ := hr ψ
  refine ⟨abD, abN, ?_, ?_, hl, hlN, hbits, habF, hEq⟩
  · rw [hac]
    exact denoteMeta_cons_mono hfresh (hat A) ψ _ (canonCrest_constsBound hcb hA) hab
  · rw [hac]
    exact denoteMeta_cons_mono hfresh (hat _) ψ _ hnb habN

/-- **A stored constructor's field, opened and abstracted, reads as the
declared crest's field**: the concrete opening of the stored type at the
parameter variables and the fields, each field's type member-abstracted
at holes at `nP + t` (`holeAbs`), reads at `nP + k + i` as the `i`-th
field of the canonical crest's reading `abD` — whose fields read like the
fields with holes at every frame satisfying the hole context. -/
theorem blockField_holeRead {env : Env} {m : EnvModel V env} {d : BlockData V} {lps : List Name}
    {c j : Nat} {cA : ConstantVal × Nat} (hR : BlockAbsRead m d lps c j cA)
    {ctx : NestCtx} (hnames : ctx.names = d.memberNames) (hlps : ctx.lps = lps)
    (hnP : ctx.nP = d.nP) (hk : d.k = d.memberNames.length)
    {holes : List Expr} (hholes : ∀ (t : Nat) (x : Expr), holes[t]? = some x →
      ∃ ty, x = .fvar (d.nP + t) ty) (hlenH : holes.length = d.k)
    {fvsP xFvs : List Expr} {crest xrest : Expr}
    (hopP : openPisAtFvars d.nP cA.1.type 0 = some (fvsP, crest))
    (hpIdx : ∀ (i : Nat) (x : Expr), fvsP[i]? = some x → ∃ ty, x = .fvar i ty)
    (hwc : Expr.WScoped d.nP crest)
    (hopX : openPisAtFvars cA.2 crest d.nP = some (xFvs, xrest))
    (ψ : Name → Nat) :
    ∃ abD : List (AnnotTerm), abD.length = cA.2 ∧
      FieldsEqOn V (d.holeCtx ψ).reverse abD (d.absF ψ c j) ∧
      ∀ {i : Nat} {x : Expr}, xFvs[i]? = some x →
        denoteMeta m.acval env ψ (d.nP + d.k + i) (holeAbs ctx holes x.fvarTypeD)
          = some (abD.getD i default) := by
  obtain ⟨-, A, hA, hr⟩ := hR
  obtain ⟨ab, -, hab, -, hlab, -, -, -, hEq⟩ := hr ψ
  refine ⟨ab.map (·.2.2), by simp [hlab], hEq, fun {i x} hx => ?_⟩
  have hh : ∀ h ∈ holes, ∃ i ty, h = .fvar i ty := by
    intro h hm
    obtain ⟨t, ht⟩ := List.getElem?_of_mem hm
    obtain ⟨ty, rfl⟩ := hholes t h ht
    exact ⟨_, _, rfl⟩
  -- the abstracted concrete crest is the canonical one, up to erasure
  have hA₂ := nestAbstract_instPisWith (ctx := ctx) hh (instPisWith_of_openPis d.nP hopP)
  have hvars : Expr.ErasedEqL (fvsP.map (nestAbstract ctx holes)) (canonParams d.nP) := by
    refine erasedEqL_of_fvarIdx _ _ 0 (fun q y hy => ?_)
      (fun q y hy => ⟨.sort .zero, by rw [canonParams_getElem? hy, Nat.zero_add]⟩)
      (by rw [List.length_map, canonParams_length, ConLeche.Verify.openPisAtFvars_length _ hopP])
    rw [List.getElem?_map] at hy
    cases hq : fvsP[q]? with
    | none => rw [hq] at hy; exact nomatch hy
    | some z =>
      rw [hq] at hy
      obtain ⟨ty, rfl⟩ := hpIdx q z hq
      exact ⟨_, by rw [← Option.some.inj hy, Nat.zero_add]; rfl⟩
  have hHc : Expr.ErasedEqL holes (canonHoles d.nP d.k) :=
    erasedEqL_of_fvarIdx _ _ d.nP hholes
      (fun t y hy => by
        have ht : t < d.k := by
          have := (List.getElem?_eq_some_iff.mp hy).1; rwa [canonHoles_length] at this
        rw [canonHoles_getElem? ht] at hy
        exact ⟨_, (Option.some.inj hy).symm⟩)
      (by rw [hlenH, canonHoles_length])
  obtain ⟨A', hA', herased⟩ := instPisWith_erasedEq hvars
    (nestAbstract_erasedEq (ctx' := canonCtx d.memberNames lps d.nP) (by rw [hnames]; rfl)
      (by rw [hlps]; rfl) hHc cA.1.type) hA₂
  rw [show canonAbs d.memberNames lps d.nP d.k cA.1.type
      = nestAbstract (canonCtx d.memberNames lps d.nP) (canonHoles d.nP d.k) cA.1.type from rfl]
    at hA
  rw [hA] at hA'
  obtain rfl := Option.some.inj hA'
  have hhA : holeAbs ctx holes crest = nestAbstract ctx holes crest := by
    unfold holeAbs
    rw [Expr.shiftFromN_eq_self_of_fvarsBelow _ (by rw [hnP]; exact hwc.fvarsBelow)]
  have hread : denoteMeta m.acval env ψ (d.nP + d.k) (holeAbs ctx holes crest)
      = some (mkPisAV ab (AnnotTerm.mkAppN (.bvar (cA.2 + (d.k - 1 - c)))
          (paramBvarsAt d.nP (d.nP + d.k + cA.2) ++ d.absE ψ c j))) := by
    rw [hhA, denoteMeta_erasedEq herased]
    exact hab
  -- the abstracted opening, peeled
  have hopA := openPisAtFvars_holeAbs (ctx := ctx) hh cA.2 (j := 0)
    (by rw [Nat.add_zero, hnP]; exact hopX)
  rw [Nat.add_zero, hnP, hnames, ← hk] at hopA
  obtain ⟨pps, b, hst, -, -, hbind⟩ := denoteMeta_openPis cA.2 hopA hread
  rw [← hlab, stripPisAV_mkPisAV] at hst
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hst).symm
  have hxA : (xFvs.map (holeAbs ctx holes))[i]? = some (holeAbs ctx holes x) := by
    rw [List.getElem?_map, hx]; rfl
  obtain ⟨p, hp, -, hpr⟩ := hbind i _ hxA
  obtain ⟨ty, hty⟩ := ConLeche.openPisAtFvars_index _ _ _ hopX i x hx
  subst hty
  rw [holeAbs_fvar_ge ctx holes (by rw [hnP]; omega), hnames, ← hk] at hpr
  have hpr' : denoteMeta m.acval env ψ (d.nP + d.k + i) (holeAbs ctx holes ty) = some p.2.2 :=
    hpr
  show denoteMeta m.acval env ψ (d.nP + d.k + i) (holeAbs ctx holes ty) = _
  rw [hpr', List.getD_eq_getElem?_getD, List.getElem?_map, hp]
  rfl

end ConLeche.Model
