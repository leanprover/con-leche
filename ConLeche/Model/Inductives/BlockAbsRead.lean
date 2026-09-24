module

public import ConLeche.Model.Inductives.BlockRep
public import ConLeche.Model.Annot.EnvModelM
public import ConLeche.Model.Inductives.StructRead
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
# The fields with holes, read off the walked term (lane HOLE2, stage E2)

A uniform block's datum carries its constructors' fields WITH HOLES as a
primary field (`BlockData.absFF`), chosen once — at the dummy carrier —
as the READING of the term the positivity walk inspects: the stored
constructor type with the members abstracted to the canonical holes and
the parameters instantiated at the canonical variables (`canonAbs`,
`canonParams`), read at `nP + k`, its first `nF` domains
(`canonFieldsRead`).  No field is classified: the flat shape, the
applied holes and the override law of these fields are the stored field
shape facts' (`StoredFieldShapes`), which the walk's run produces.

`BlockAbsRead` is the reading fact at a model: the canonical crest reads
as the Π-tower over the datum's fields with holes ending in the
component's hole at the parameters and the result index readings.  It
crosses every cons the stored type crosses (`BlockAbsRead.cross`); the
readings depend on the level assignment only at the block's level
parameters (`canonFieldsRead_params`), and — the crest looking up no
member (M2′, `Expr.readsAt_of_nestOcc`) — on the leaves only off the
members (`canonFieldsRead_agree`), so the dummy and the real carrier
read them alike.
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

/-! ## The canonical crest's field readings -/

/-- **The fields with holes of a stored constructor `cA`** at a leaf
assignment: the canonical crest's reading at `nP + k`, its first `cA.2`
domains (`[]` where the crest or the reading is missing). -/
@[expose] noncomputable def canonFieldsRead (acval : Name → (Name → Nat) → AnnotTerm) (env : Env)
    (names lps : List Name) (nP k : Nat) (cA : ConstantVal × Nat) (ψ : Name → Nat) :
    List AnnotTerm :=
  match instPisWith (canonParams nP) (canonAbs names lps nP k cA.1.type) with
  | some A =>
    match denoteMeta acval env ψ (nP + k) A with
    | some t => ((stripPisAV cA.2 t).map fun p => p.1.map (·.2.2)).getD []
    | none => []
  | none => []

/-- The fields' readings at a reading of the crest. -/
theorem canonFieldsRead_eq {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {names lps : List Name} {nP k : Nat} {cA : ConstantVal × Nat} {ψ : Name → Nat} {A : Expr}
    {ab : List (Nat × Nat × AnnotTerm)} {B : AnnotTerm}
    (hA : instPisWith (canonParams nP) (canonAbs names lps nP k cA.1.type) = some A)
    (hr : denoteMeta acval env ψ (nP + k) A = some (mkPisAV ab B)) (hl : ab.length = cA.2) :
    canonFieldsRead acval env names lps nP k cA ψ = ab.map (·.2.2) := by
  unfold canonFieldsRead
  rw [hA]
  simp only
  rw [hr]
  simp only
  rw [← hl, stripPisAV_mkPisAV]
  rfl

omit [SetTheory V] in
/-- An instantiation at footprint-free arguments keeps the footprint. -/
theorem lpDefF_instPisWith {ps : List Name} :
    ∀ {vs : List Expr} {e r : Expr}, (∀ v ∈ vs, lpDefF ps v = true) →
      instPisWith vs e = some r → lpDefF ps e = true → lpDefF ps r = true
  | [], e, r, _, h, he => by
    simp only [ConLeche.instPisWith, Option.some.injEq] at h
    exact h ▸ he
  | v :: vs, e, r, hvs, h, he => by
    match e, h with
    | .forallE t b m, h =>
      have h' : instPisWith vs (b.instantiate1 v) = some r := h
      simp only [lpDefF, Bool.and_eq_true] at he
      exact lpDefF_instPisWith (fun x hx => hvs x (List.mem_cons_of_mem _ hx)) h'
        (lpDefF_instantiate1 (hvs v List.mem_cons_self) b 0 he.1.2)

omit [SetTheory V] in
/-- The canonical crest keeps the stored type's level footprint. -/
theorem lpDefF_canonCrest {ps names lps : List Name} {nP k : Nat} {e A : Expr}
    (he : lpDefF ps e = true)
    (hA : instPisWith (canonParams nP) (canonAbs names lps nP k e) = some A) :
    lpDefF ps A = true := by
  refine lpDefF_instPisWith (fun x hx => ?_) hA ?_
  · obtain ⟨i, -, rfl⟩ := mem_canonParams hx
    rfl
  · refine lpDefF_replaceConsts (fun c us r hr => ?_) e he
    obtain ⟨mm, -, rfl⟩ := canonAbs_repl hr
    rfl

/-- **The fields' readings depend on the level assignment at the stored
type's footprint only.** -/
theorem canonFieldsRead_params {env : Env} (m : EnvModel V env) {ps names lps : List Name}
    {nP k : Nat} {cA : ConstantVal × Nat} (hl : lpDefF ps cA.1.type = true)
    {ψ₁ ψ₂ : Name → Nat} (hφ : ∀ p ∈ ps, ψ₁ p = ψ₂ p) :
    canonFieldsRead m.acval env names lps nP k cA ψ₁
      = canonFieldsRead m.acval env names lps nP k cA ψ₂ := by
  unfold canonFieldsRead
  split
  · rename_i A hA
    rw [denoteMeta_params_extF m hφ _ A (lpDefF_canonCrest hl hA)]
  · rfl

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

/-- **The fields' readings consult the leaves off the members only**
(`canonCrest_read_agree`). -/
theorem canonFieldsRead_agree {acval₁ acval₂ : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {names lps : List Name} {nP k : Nat} {cA : ConstantVal × Nat}
    (hag : ∀ n, n ∉ names → acval₁ n = acval₂ n)
    (hocc : (canonAbs names lps nP k cA.1.type).nestOcc names 0 0 = false)
    (hnat : ConLeche.natLitSupported env = true →
      ConLeche.natZeroName ∉ names ∧ ConLeche.natSuccName ∉ names)
    (hstr : ConLeche.strLitSupported env = true →
      ConLeche.stringOfListName ∉ names ∧ ConLeche.listNilName ∉ names ∧
        ConLeche.listConsName ∉ names ∧ ConLeche.charName ∉ names ∧
        ConLeche.charOfNatName ∉ names) (ψ : Name → Nat) :
    canonFieldsRead acval₁ env names lps nP k cA ψ
      = canonFieldsRead acval₂ env names lps nP k cA ψ := by
  unfold canonFieldsRead
  split
  · rename_i A hA
    rw [canonCrest_read_agree hag hocc hnat hstr hA ψ]
  · rfl

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
    (hrun : ConLeche.checkBlockPositivity ops env₁ find? consts p cvTas ctorsAs = .ok ())
    {d : BlockData V} {lps : List Name}
    (hnames : p.memberNames = d.memberNames) (hlps : p.lps = lps)
    (hk : d.k = d.memberNames.length)
    (hctorsAs : ∀ c, c < d.k → ctorsAs[c]? = some (d.ctorsM c)) :
    ∀ c, c < d.k → ∀ (j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      (canonAbs d.memberNames lps d.nP d.k cA.1.type).nestOcc d.memberNames 0 0 = false := by
  obtain ⟨cvTa0, fvsP, rest, holes, -, -, hholes, hall⟩ := ConLeche.checkBlockPositivity_inv hrun
  intro c hc j cA hcj
  obtain ⟨-, -, -, -, -, hocc⟩ := hall c (d.ctorsM c) (hctorsAs c hc) j cA hcj
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

/-- **The datum's fields with holes are the walked term's reading** at
the model: the canonical crest of the stored constructor `cA` of
component `c` reads at `nP + k` as the Π-tower over `absF` ending in the
component's hole at the parameters and `absE`. -/
@[expose] def BlockAbsRead {env : Env} (m : EnvModel V env) (d : BlockData V) (lps : List Name)
    (c j : Nat) (cA : ConstantVal × Nat) : Prop :=
  ∃ A, instPisWith (canonParams d.nP) (canonAbs d.memberNames lps d.nP d.k cA.1.type) = some A ∧
    ∀ ψ : Name → Nat, ∃ ab : List (Nat × Nat × AnnotTerm),
      denoteMeta m.acval env ψ (d.nP + d.k) A
        = some (mkPisAV ab (AnnotTerm.mkAppN (.bvar (cA.2 + (d.k - 1 - c)))
            (paramBvarsAt d.nP (d.nP + d.k + cA.2) ++ d.absE ψ c j))) ∧
      ab.length = cA.2 ∧ ab.map (·.2.2) = d.absF ψ c j

/-- **The reading fact crosses a cons** the stored type crosses. -/
theorem BlockAbsRead.cross {env : Env} {m : EnvModel V env} {d : BlockData V} {lps : List Name}
    {c j : Nat} {cA : ConstantVal × Nat} (h : BlockAbsRead m d lps c j cA)
    {c₀ : ConstantInfo} {B : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? c₀.name = none) (hat : ∀ e : Expr, ConsCrossAt c₀ e)
    (hcb : ConstsBound env cA.1.type)
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩) (hac : m₂.acval = acvalWith m.acval c₀.name B) :
    BlockAbsRead m₂ d lps c j cA := by
  obtain ⟨A, hA, hr⟩ := h
  refine ⟨A, hA, fun ψ => ?_⟩
  obtain ⟨ab, hab, hlab, habF⟩ := hr ψ
  refine ⟨ab, ?_, hlab, habF⟩
  rw [hac]
  exact denoteMeta_cons_mono hfresh (hat A) ψ _ (canonCrest_constsBound hcb hA) hab

/-- **A stored constructor's field, opened and abstracted, reads as its
field with holes**: the concrete opening of the stored type at the
parameter variables and the fields, each field's type member-abstracted
at holes at `nP + t` (`holeAbs`), reads at `nP + k + i` as `absF`'s
`i`-th entry — the canonical crest's reading, peeled (`denoteMeta_openPis`
at the abstracted opening, `openPisAtFvars_holeAbs`). -/
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
    (ψ : Name → Nat) {i : Nat} {x : Expr} (hx : xFvs[i]? = some x) :
    denoteMeta m.acval env ψ (d.nP + d.k + i) (holeAbs ctx holes x.fvarTypeD)
      = some ((d.absF ψ c j).getD i default) := by
  obtain ⟨A, hA, hr⟩ := hR
  obtain ⟨ab, hab, hlab, habF⟩ := hr ψ
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
  rw [hpr', ← habF, List.getD_eq_getElem?_getD, List.getElem?_map, hp]
  rfl

end ConLeche.Model
