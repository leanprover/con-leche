module

public import ConLeche.Model.Inductives.WhnfContentRun
public import ConLeche.Model.Inductives.RoundTripProp
import ConLeche.Verify.Inductives.NestedFacts
import ConLeche.Verify.Inductives.NestedCtorNames

public section

/-!
# The restored constructors' stage (task #279 M-D′ D3, DESIGN §M.50)

The restored block's second stage, `env₂ = consNestedCtors ctorsR.flatten
env₁`, conses the REAL members' constructors with their types RESTORED
(`restoreNested R`: a copy at the parameters and index arguments is put
back to its container at the pin's components, K.19 stores the restore
syntactically).  Its model is a cons chain over `env₁`'s model
(`nestedFormersModel`) with, at each restored constructor `T.c`, the
leaf

    λ p⃗ f⃗, ⟦T.c⟧_aux p⃗ (ψ* f⃗)

— the AUXILIARY constructor's leaf (the scratch model's `mpAux.acval
T.c`; a real member keeps its name) applied to the parameters and to the
fields with, at every copy-recursive position, the FORWARD fold `ψ` of
the target pin transported over the field's telescope (`viaEntryAV` at
the leaf frame: no motives, minors or hypotheses) and the field itself
elsewhere.  What a cons asks (`stageNestedCtor`) is what
`stageMutualCtor` asks — the leaf closed, level-parametric, graded and
bit-valid, the restored type reading at the environment so far, graded,
and the leaf a member of that reading — and the loop
(`stageNestedCtorsGo`, `nestedCtorsModel`) carries the readings of the
pending constructors across the conses (`denoteMeta_cons_mono`) at the
names' freshness and distinctness.

The per-constructor CONTENT (the restored type's reading as the
`mkPisAV` of the aux domains with `restoreAV` at the copy positions and
the leaf's typing) is `NestedCtorLeaf`, stated here and built in
`NestedCtorLeaf.lean`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps MutualBlock AuxStored
  NestedParts ElimState)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The transport entry at the leaf frame

`viaEntryAV Ψ nF o i l tl Eis` is ψ's transport entry at a MINOR's leaf
frame (`o` motives and earlier minors, `l` hypotheses).  At a
constructor's own leaf frame there are none: `o = 0`, `l = 0`, and the
frame under the telescope values `as` is `consList as (consList fs ρp)`.
The two readers below are `interp_ihIdxAtM`/`interp_viaEntryAV` at that
frame (those take a nonempty motive block). -/

omit [SetTheory V] in
/-- The frame `as` telescope values over `fs` fields over `ρp`, shifted
past the fields at the cutoff `as.length`, keeps the first `i` fields. -/
theorem shiftE_fieldsFrame {nF i : Nat} {ρp : Nat → V} {fs : List V} (hfs : fs.length = nF)
    (as : List V) :
    shiftE (nF - i) as.length (consList as (consList fs ρp)) = consList as (consList (fs.take i) ρp) := by
  rw [shiftE_consList_len]
  congr 1
  have hsplit : consList fs ρp = consList (fs.drop i) (consList (fs.take i) ρp) := by
    rw [← consList_append, List.take_append_drop]
  rw [hsplit, show nF - i = (fs.drop i).length from by rw [List.length_drop, hfs],
    shiftE_consList]

/-- `ihIdxAtM nF 0 i 0` under `as` telescope values at the leaf frame
reads the field's expression at the field's own frame. -/
theorem interp_ihIdxAtM_leaf {nF i : Nat} {ρp : Nat → V} {fs : List V} (hfs : fs.length = nF)
    (as : List V) (E : AnnotTerm) :
    interp V (consList as (consList fs ρp)) (ihIdxAtM nF 0 i 0 as.length E)
      = interp V (consList as (consList (fs.take i) ρp)) E := by
  unfold ihIdxAtM
  rw [AnnotTerm.liftN_zero, Nat.add_zero, interp_liftN, shiftE_fieldsFrame hfs as]

omit [SetTheory V] in
/-- The leaf frame shifted past the telescope and the fields is the
parameter frame. -/
theorem shiftE_leafFrame {nF : Nat} {ρp : Nat → V} {fs : List V} (hfs : fs.length = nF)
    (as : List V) :
    shiftE (0 + nF + 0 + as.length) 0 (consList as (consList fs ρp)) = ρp := by
  rw [← consList_append, show 0 + nF + 0 + as.length = (fs ++ as).length from by
    rw [List.length_append, hfs]; omega]
  exact shiftE_consList _ _

/-- **The transport body reads at the leaf frame** (under `as` telescope
values) as `Ψ` at the parameter frame applied to the field's index
values at the field's own frame and to the field at `as`. -/
theorem interp_viaBodyAV_leaf {nF i : Nat} {ρp : Nat → V} {fs : List V} (hfs : fs.length = nF)
    (hi : i < nF) (as : List V) (Ψ : AnnotTerm) (Eis : List AnnotTerm) :
    interp V (consList as (consList fs ρp)) (viaBodyAV Ψ nF 0 i 0 as.length Eis)
      = (Eis.map (interp V (consList as (consList (fs.take i) ρp))) ++
          [as.foldl SetTheory.app (fs.getD i pt)]).foldl SetTheory.app (interp V ρp Ψ) := by
  unfold viaBodyAV
  rw [interp_mkAppN_map, List.map_append, List.map_map, List.map_singleton, interp_mkAppN_map,
    interp_bvar, interp_liftN, shiftE_leafFrame hfs]
  have hf : consList as (consList fs ρp) (nF - 1 - i + 0 + as.length) = fs.getD i pt := by
    rw [Nat.add_zero, consList_apply_add, consList_apply_lt' fs _ (by omega),
      show fs.length - 1 - (nF - 1 - i) = i from by omega]
  have hvars : (teleVarsAV as.length).map (interp V (consList as (consList fs ρp))) = as :=
    map_fieldBvars_interp rfl _
  rw [hf, hvars]
  congr 2
  apply List.map_congr_left
  intro E _
  simp only [Function.comp]
  exact interp_ihIdxAtM_leaf hfs as E

/-- **The transport entry reads at the leaf frame** as the λ-tower over
the field's telescope at the field's own frame of the transport body
(`interp_viaEntryAV` with no motives, minors or hypotheses). -/
theorem interp_viaEntryAV_leaf {b nF i : Nat} {ρp : Nat → V} {fs : List V} (hfs : fs.length = nF)
    (hi : i < nF) {tl : List (Nat × Nat × AnnotTerm)} (hbits : ∀ d ∈ tl, d.2.1 = b)
    (Ψ : AnnotTerm) (Eis : List AnnotTerm) :
    interp V (consList fs ρp) (viaEntryAV Ψ nF 0 i 0 tl Eis)
      = lamTower b (consList (fs.take i) ρp) tl fun σ' =>
          (Eis.map (interp V σ') ++
            [(Semantics.frameIdx tl.length σ').foldl SetTheory.app (fs.getD i pt)]).foldl
            SetTheory.app (interp V ρp Ψ) := by
  unfold viaEntryAV ihTeleAtR
  rw [interp_mkLamsAV_lamTower (b := b) (fun d hd => by
    obtain ⟨d', hd', he⟩ := mem_ihTeleAtGo hd
    rw [he]; exact hbits d' hd')]
  suffices h : ∀ (as : List V) (tl' : List (Nat × Nat × AnnotTerm)),
      as.length + tl'.length = tl.length →
      lamTower b (consList as (consList fs ρp)) (ihTeleAtGo nF 0 i 0 as.length tl')
          (fun σ' => interp V σ' (viaBodyAV Ψ nF 0 i 0 tl.length Eis))
        = lamTower b (consList as (consList (fs.take i) ρp)) tl' fun σ' =>
          (Eis.map (interp V σ') ++
            [(Semantics.frameIdx tl.length σ').foldl SetTheory.app (fs.getD i pt)]).foldl
            SetTheory.app (interp V ρp Ψ) by
    have := h [] tl (by simp)
    simpa only [consList_nil, List.length_nil] using this
  intro as tl' hlen
  induction tl' generalizing as with
  | nil =>
    simp only [ihTeleAtGo, lamTower]
    have hlen' : as.length = tl.length := by simpa using hlen
    rw [← hlen', interp_viaBodyAV_leaf hfs hi as Ψ Eis, frameIdx_consList' as]
  | cons d tl' ih =>
    simp only [ihTeleAtGo, lamTower]
    rw [interp_ihIdxAtM_leaf hfs as d.2.2]
    congr 1
    funext a
    have h1 : cons a (consList as (consList fs ρp)) = consList (as ++ [a]) (consList fs ρp) := by
      rw [consList_append, consList_cons, consList_nil]
    have h2 : cons a (consList as (consList (fs.take i) ρp))
        = consList (as ++ [a]) (consList (fs.take i) ρp) := by
      rw [consList_append, consList_cons, consList_nil]
    rw [h1, h2]
    have := ih (as ++ [a]) (by rw [List.length_append, List.length_singleton]; simp at hlen; omega)
    rw [List.length_append, List.length_singleton] at this
    exact this

/-- **The transport entry is typed at the leaf frame**: it inhabits the
nested product over the field's telescope (at the field's own frame) of
a body `B` from the one fact of `Ψ` — at every spine fitting the
telescope, `Ψ` at the index values and the field at the spine lands in
`B` (`viaEntry_mem` at the leaf frame). -/
theorem viaEntry_mem_leaf {b nF i : Nat} {ρp : Nat → V} {fs : List V} (hfs : fs.length = nF)
    (hi : i < nF) {tl : List (Nat × Nat × AnnotTerm)} (hbits : ∀ d ∈ tl, d.2.1 = b)
    (Ψ : AnnotTerm) (Eis : List AnnotTerm) {B : List V → V}
    (hΨ : ∀ as : List V, SpineFit (consList (fs.take i) ρp) (tl.map (·.2.2)) as →
      (Eis.map (interp V (consList as (consList (fs.take i) ρp))) ++
        [as.foldl SetTheory.app (fs.getD i pt)]).foldl SetTheory.app (interp V ρp Ψ) ∈ˢ B as) :
    interp V (consList fs ρp) (viaEntryAV Ψ nF 0 i 0 tl Eis)
      ∈ˢ piTele b (teleOfFields (consList (fs.take i) ρp) (tl.map (·.2.2))) B [] := by
  rw [interp_viaEntryAV_leaf hfs hi hbits Ψ Eis]
  refine lamTower_mem_piTele fun as hfit => ?_
  rw [List.nil_append]
  have hfit' := fitsS_teleOfFields.mp hfit
  have hlen : as.length = tl.length := by rw [hfit'.length_eq, List.length_map]
  rw [← hlen, frameIdx_consList' as]
  exact hΨ as hfit'

/-! ## What one restored constructor's cons asks -/

/-- **The content of a restored constructor** at the formers' model
`mp₁`: its leaf `A` (closed, level-parametric, graded, bit-valid), its
restored type reading at `mp₁` as `ta`, graded, and the leaf a member of
the reading.  What `stageNestedCtor` consumes; `NestedCtorLeaf.lean`
builds it from the auxiliary datum and ψ. -/
structure NestedCtorLeaf {μ : CheckMode} {env₁ : Env} (mp₁ : EnvModelM V μ env₁)
    (cvA : ConstantVal) (A ta : (Name → Nat) → AnnotTerm) : Prop where
  below : ∀ ψ : Name → Nat, Term.bvarsBelow 0 (A ψ).erase
  params : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ cvA.levelParams, ψ₁ q = ψ₂ q) → A ψ₁ = A ψ₂
  wd : ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenoted V ρ (A ψ)
  valid : ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotValid V ρ (A ψ)
  read : ∀ ψ : Name → Nat, denoteMeta mp₁.base2.acval env₁ ψ 0 cvA.type = some (ta ψ)
  okTy : ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenotedV V ρ (ta ψ)
  mem : ∀ (ψ : Name → Nat) (ρ : Nat → V), interp V ρ (A ψ) ∈ˢ interp V ρ (ta ψ)

/-! ## One constructor's cons -/

/-- **The P step at a restored constructor's cons** (`stageMutualCtor`'s
shape with the leaf and its typing given): the constructor is fresh at
the environment, its type scoped there (the pre-annotated front door's
four facts, `checkConstantValPre_typeWF`, carried up the chain), its
name unreserved and not projection-shaped, its type reads at the
environment's model, and the leaf is closed, level-parametric, graded,
bit-valid and a member of the reading.  The capability obligation is
vacuous (a constructor is consed). -/
theorem stageNestedCtor {μ : CheckMode} {env : Env} (mp : EnvModelM V μ env)
    (hE₀ : ConLeche.EtaFamiliesClosed env) {cvA : ConstantVal} {nP nF : Nat}
    (hfresh : env.find? cvA.name = none)
    (hnres : ConLeche.reservedBasisNames.contains cvA.name = false)
    (hpshape : cvA.name.isProjFnShape = false)
    (htf : cvA.type.hasFvar = false)
    (hlp : cvA.type.allLevelParamsDefined cvA.levelParams = true)
    (htr : cvA.type.constsResolve env = true)
    (hbt : cvA.type.looseBVarsBounded 0 = true)
    {A ta : (Name → Nat) → AnnotTerm}
    (hAbelow : ∀ ψ : Name → Nat, Term.bvarsBelow 0 (A ψ).erase)
    (hAparams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ cvA.levelParams, ψ₁ q = ψ₂ q) → A ψ₁ = A ψ₂)
    (hAwd : ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenoted V ρ (A ψ))
    (hAvalid : ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotValid V ρ (A ψ))
    (hread : ∀ ψ : Name → Nat, denoteMeta mp.base2.acval env ψ 0 cvA.type = some (ta ψ))
    (hok : ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenotedV V ρ (ta ψ))
    (hmem : ∀ (ψ : Name → Nat) (ρ : Nat → V), interp V ρ (A ψ) ∈ˢ interp V ρ (ta ψ)) :
    ∃ mp' : EnvModelM V μ ⟨.ctorInfo cvA nP nF :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval cvA.name A := by
  have hcb : ConstsBound env cvA.type := constsBound_of_constsResolve _ htr
  have hwfC : ConLeche.EnvWF ⟨.ctorInfo cvA nP nF :: env.consts⟩ :=
    ConLeche.EnvWF.cons mp.base2.wf (ConLeche.structConstWF htf hlp
      (Expr.constsResolve_mono htr) hbt
      (fun _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq))
  have hreadC : ∀ ψ : Name → Nat,
      denoteMeta (acvalWith mp.base2.acval cvA.name A) ⟨.ctorInfo cvA nP nF :: env.consts⟩ ψ 0
        cvA.type = some (ta ψ) := fun ψ =>
    denoteMeta_cons_mono (c₀ := .ctorInfo cvA nP nF) hfresh
      (ConsCrossAt.ofNtc fun _ h => nomatch h) ψ 0 hcb (hread ψ)
  have hnresC : ConLeche.reservedBasisNames.contains
      (ConstantInfo.ctorInfo cvA nP nF).name = false := hnres
  have hpshapeC : (ConstantInfo.ctorInfo cvA nP nF).name.isProjFnShape = false := hpshape
  refine declStep_preserves_of_ind_member_cons mp (c₀ := .ctorInfo cvA nP nF)
    (A := A) hfresh hnresC (Or.inr ⟨_, _, _, rfl⟩)
    (ConsHead.ofFresh hwfC (fun ψ => hAbelow ψ) hnresC
      (fun _ h => nomatch h)
      (fun _ _ _ _ h => nomatch h))
    (fun ψ k => AnnotTerm.liftN_eq_self _
      (Term.bvarsBelow.mono (Nat.zero_le k) (hAbelow ψ)) 1)
    hAparams hAwd hAvalid (fun ψ => ⟨_, hreadC ψ⟩) ?_ ?_ ?_
  · intro ψ ta' hta ρ
    obtain rfl := Option.some.inj ((hreadC ψ).symm.trans hta)
    exact hok ψ ρ
  · intro ψ ta' hta ρ
    obtain rfl := Option.some.inj ((hreadC ψ).symm.trans hta)
    exact hmem ψ ρ
  · -- `caps_ok`: the block claims nothing, and the cons stores a
    -- CONSTRUCTOR at the name the obligation is taken at
    intro m₂ hac
    refine capsOk_cons_native mp (c₀ := .ctorInfo cvA nP nF) (A := A)
      (T := cvA.name) hfresh (ConsCrossEnv.ofNtc fun _ h => nomatch h) hpshapeC
      (Or.inr fun _ _ h => nomatch h)
      (fun T' cvT' caps' hf _ hres hcape => hE₀ T' cvT' caps' hf hcape hres)
      m₂ hac ?_
    intro cvT' caps' hf _
    have hself := ConLeche.Env.find?_cons_self (ConstantInfo.ctorInfo cvA nP nF) env
    rw [show (ConstantInfo.ctorInfo cvA nP nF).name = cvA.name from rfl] at hself
    exact nomatch (hself.symm.trans hf)

/-! ## The loop -/

/-- The static facts of a restored constructor, off its pre-annotated
front door at the formers' environment: unreserved, not
projection-shaped, the type fvar-free, level-closed and bounded. -/
@[expose] def RestoredCtorStatic (cvA : ConstantVal) : Prop :=
  ConLeche.reservedBasisNames.contains cvA.name = false ∧
  cvA.name.isProjFnShape = false ∧
  cvA.type.hasFvar = false ∧
  cvA.type.allLevelParamsDefined cvA.levelParams = true ∧
  cvA.type.looseBVarsBounded 0 = true

/-- **The restored constructors' conses, in order** (the induction over
the remaining constructors).  Every pending constructor is fresh at the
environment, its type resolves there and reads at the environment's
model as `taOf`; each cons keeps the facts of the rest
(`denoteMeta_cons_mono`, the names distinct) and leaves every other name's
leaf untouched. -/
theorem stageNestedCtorsGo {μ : CheckMode} (Aof taOf : Nat → (Name → Nat) → AnnotTerm)
    (nPof nFof : Nat → Nat) :
    ∀ (cs : List (ConstantVal × Nat × Nat)) (k : Nat) (env : Env) (mp : EnvModelM V μ env),
      ConLeche.EtaFamiliesClosed env →
      (cs.map (·.1.name)).Nodup →
      (∀ (i : Nat) (c : ConstantVal × Nat × Nat), cs[i]? = some c →
        c.2.1 = nPof (k + i) ∧ c.2.2 = nFof (k + i) ∧ RestoredCtorStatic c.1 ∧
        (∀ ψ : Name → Nat, Term.bvarsBelow 0 (Aof (k + i) ψ).erase) ∧
        (∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ c.1.levelParams, ψ₁ q = ψ₂ q) →
          Aof (k + i) ψ₁ = Aof (k + i) ψ₂) ∧
        (∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenoted V ρ (Aof (k + i) ψ)) ∧
        (∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotValid V ρ (Aof (k + i) ψ)) ∧
        (∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenotedV V ρ (taOf (k + i) ψ)) ∧
        (∀ (ψ : Name → Nat) (ρ : Nat → V),
          interp V ρ (Aof (k + i) ψ) ∈ˢ interp V ρ (taOf (k + i) ψ))) →
      (∀ (i : Nat) (c : ConstantVal × Nat × Nat), cs[i]? = some c →
        env.find? c.1.name = none ∧ c.1.type.constsResolve env = true ∧
        ∀ ψ : Name → Nat, denoteMeta mp.base2.acval env ψ 0 c.1.type = some (taOf (k + i) ψ)) →
      ∃ mp' : EnvModelM V μ (ConLeche.consNestedCtors cs env),
        ConLeche.EtaFamiliesClosed (ConLeche.consNestedCtors cs env) ∧
        (∀ n : Name, (∀ c ∈ cs, n ≠ c.1.name) → mp'.base2.acval n = mp.base2.acval n) ∧
        (∀ (i : Nat) (c : ConstantVal × Nat × Nat), cs[i]? = some c →
          mp'.base2.acval c.1.name = Aof (k + i))
  | [], k, env, mp, hE, _, _, _ => ⟨mp, hE, fun _ _ => rfl, fun _ _ h => by simp at h⟩
  | (cvA, nP, nF) :: rest, k, env, mp, hE, hnd, hstat, hpend => by
    -- the head's facts
    obtain ⟨hnP, hnF, ⟨hnres, hpshape, htf, hlp, hbt⟩, hbelow, hparams, hwd, hvalid, hok, hmem⟩ :=
      hstat 0 (cvA, nP, nF) rfl
    obtain ⟨hfresh, htr, hread⟩ := hpend 0 (cvA, nP, nF) rfl
    simp only [Nat.add_zero] at hnP hnF hbelow hparams hwd hvalid hok hmem hread
    -- the head's cons
    obtain ⟨mpC, hacC⟩ := stageNestedCtor (nP := nP) (nF := nF) mp hE hfresh hnres hpshape htf hlp
      htr hbt hbelow hparams hwd hvalid hread hok hmem
    -- the names: the rest is fresh at the cons
    have hndR : (rest.map (·.1.name)).Nodup ∧ ∀ c ∈ rest, c.1.name ≠ cvA.name := by
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
      exact ⟨hnd.2, fun c hc h => hnd.1 ⟨c, hc, h⟩⟩
    have hE' : ConLeche.EtaFamiliesClosed ⟨.ctorInfo cvA nP nF :: env.consts⟩ :=
      EtaFamiliesClosed.ofFreshExt hE (FreshEtaExt.cons hfresh (fun _ _ heq => nomatch heq))
    -- the rest's pending facts cross the cons
    have hpend' : ∀ (i : Nat) (c : ConstantVal × Nat × Nat), rest[i]? = some c →
        (⟨.ctorInfo cvA nP nF :: env.consts⟩ : Env).find? c.1.name = none ∧
        c.1.type.constsResolve ⟨.ctorInfo cvA nP nF :: env.consts⟩ = true ∧
        ∀ ψ : Name → Nat, denoteMeta mpC.base2.acval ⟨.ctorInfo cvA nP nF :: env.consts⟩ ψ 0 c.1.type
          = some (taOf (k + 1 + i) ψ) := by
      intro i c hc
      obtain ⟨hfreshI, htrI, hreadI⟩ := hpend (i + 1) c (by simpa using hc)
      rw [show k + (i + 1) = k + 1 + i from by omega] at hreadI
      refine ⟨?_, Expr.constsResolve_mono htrI, fun ψ => ?_⟩
      · rw [ConLeche.Env.find?_cons]
        have hne : c.1.name ≠ cvA.name := hndR.2 c (List.mem_of_getElem? hc)
        simp only [show (ConstantInfo.ctorInfo cvA nP nF).name = cvA.name from rfl]
        rw [if_neg (Ne.symm hne)]
        exact hfreshI
      · rw [hacC]
        exact denoteMeta_cons_mono (c₀ := .ctorInfo cvA nP nF) hfresh
          (ConsCrossAt.ofNtc fun _ h => nomatch h) ψ 0 (constsBound_of_constsResolve _ htrI)
          (hreadI ψ)
    have hstat' : ∀ (i : Nat) (c : ConstantVal × Nat × Nat), rest[i]? = some c →
        c.2.1 = nPof (k + 1 + i) ∧ c.2.2 = nFof (k + 1 + i) ∧ RestoredCtorStatic c.1 ∧
        (∀ ψ : Name → Nat, Term.bvarsBelow 0 (Aof (k + 1 + i) ψ).erase) ∧
        (∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ c.1.levelParams, ψ₁ q = ψ₂ q) →
          Aof (k + 1 + i) ψ₁ = Aof (k + 1 + i) ψ₂) ∧
        (∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenoted V ρ (Aof (k + 1 + i) ψ)) ∧
        (∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotValid V ρ (Aof (k + 1 + i) ψ)) ∧
        (∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenotedV V ρ (taOf (k + 1 + i) ψ)) ∧
        (∀ (ψ : Name → Nat) (ρ : Nat → V),
          interp V ρ (Aof (k + 1 + i) ψ) ∈ˢ interp V ρ (taOf (k + 1 + i) ψ)) := by
      intro i c hc
      have := hstat (i + 1) c (by simpa using hc)
      rwa [show k + (i + 1) = k + 1 + i from by omega] at this
    obtain ⟨mp', hE'', hag, hleaves⟩ :=
      stageNestedCtorsGo Aof taOf nPof nFof rest (k + 1) _ mpC hE' hndR.1 hstat' hpend'
    refine ⟨mp', hE'', fun n hn => ?_, fun i c hc => ?_⟩
    · rw [hag n (fun c hc => hn c (List.mem_cons_of_mem _ hc)), hacC]
      exact acvalWith_ne (hn (cvA, nP, nF) List.mem_cons_self)
    · cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
        subst hc
        rw [hag _ (fun c hc h => hndR.2 c hc h.symm), hacC, Nat.add_zero]
        exact acvalWith_self
      | succ i =>
        simp only [List.getElem?_cons_succ] at hc
        rw [show k + (i + 1) = k + 1 + i from by omega]
        exact hleaves i c hc

/-! ## The stage, at the run -/

/-- **The model of the environment holding the restored constructors**
(M-D′ D3): from the formers' model `mp₁` of `env₁ = consNestedFormers
(stored.take p.k) env` and, at every restored constructor (position `i`
of `ctorsR.flatten`), its content `NestedCtorLeaf` — the leaf `Aof i`
and the restored type's reading `taOf i` — a model of
`env₂ = consNestedCtors ctorsR.flatten env₁` whose carrier is `mp₁`'s
off the constructors' names and `Aof i` at constructor `i`; the η
families stay closed.  The constructors' freshness, scope and names are
the restore stage's own (`restoreCtors_fresh`, `restoreCtors_pre`,
`nestedRestoredCtors_nodup`). -/
theorem nestedCtorsModel {μ : CheckMode} {F : Nat} {env envAux : Env}
    {p : NestedParts} {st : ElimState} {b : MutualBlock} {stored : List AuxStored}
    {ctorsR : List (List (ConstantVal × Nat × Nat))}
    (mp₁ : EnvModelM V μ (ConLeche.consNestedFormers (stored.take p.k) env))
    (hE₁ : ConLeche.EtaFamiliesClosed (ConLeche.consNestedFormers (stored.take p.k) env))
    (hcore : ConLeche.checkMutualCore (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env b none
      true = .ok envAux)
    (hstored : ConLeche.auxStoredAll envAux b b.k = some stored)
    (hctors : (stored.take p.k).mapM (fun a =>
        ConLeche.restoreCtors (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
          (ConLeche.consNestedFormers (stored.take p.k) env) (ConLeche.restoreTbl p st) p.lps
          a.ctors) = .ok ctorsR)
    (Aof taOf : Nat → (Name → Nat) → AnnotTerm)
    (hleaf : ∀ (i : Nat) (c : ConstantVal × Nat × Nat), ctorsR.flatten[i]? = some c →
      NestedCtorLeaf mp₁ c.1 (Aof i) (taOf i)) :
    ∃ mp₂ : EnvModelM V μ (ConLeche.consNestedCtors ctorsR.flatten
        (ConLeche.consNestedFormers (stored.take p.k) env)),
      ConLeche.EtaFamiliesClosed (ConLeche.consNestedCtors ctorsR.flatten
        (ConLeche.consNestedFormers (stored.take p.k) env)) ∧
      (∀ n : Name, (∀ c ∈ ctorsR.flatten, n ≠ c.1.name) →
        mp₂.base2.acval n = mp₁.base2.acval n) ∧
      (∀ (i : Nat) (c : ConstantVal × Nat × Nat), ctorsR.flatten[i]? = some c →
        mp₂.base2.acval c.1.name = Aof i) := by
  -- every restored constructor went through the pre-annotated front
  -- door at the formers' environment
  have hpre : ∀ c ∈ ctorsR.flatten,
      ConLeche.checkConstantValPre (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
        (ConLeche.consNestedFormers (stored.take p.k) env) c.1 = .ok c.1 := by
    intro c hc
    obtain ⟨cs, hcs, hcin⟩ := List.mem_flatten.mp hc
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hcs
    obtain ⟨hlen, hall⟩ := ConLeche.mapM_except_inv hctors
    obtain ⟨a, cs', ha, hcs', hrun⟩ := hall j (by
      have := (List.getElem?_eq_some_iff.mp hj).1
      omega)
    rw [hj] at hcs'
    obtain rfl : cs = cs' := by simpa using hcs'
    exact ConLeche.restoreCtors_pre hrun c hcin
  have hnd := ConLeche.nestedRestoredCtors_nodup hcore hstored hctors
  obtain ⟨mp₂, hE₂, hag, hleaves⟩ := stageNestedCtorsGo (μ := μ) Aof taOf
    (fun i => ((ctorsR.flatten[i]?).map (·.2.1)).getD 0)
    (fun i => ((ctorsR.flatten[i]?).map (·.2.2)).getD 0) ctorsR.flatten 0 _ mp₁ hE₁ hnd
    (fun i c hc => by
      have hL := hleaf i c hc
      obtain ⟨-, hnres, hpshape⟩ := ConLeche.checkConstantValPre_names (hpre c (List.mem_of_getElem? hc))
      obtain ⟨htf, hlp, htr, hbt⟩ :=
        ConLeche.checkConstantValPre_typeWF (hpre c (List.mem_of_getElem? hc))
      rw [Nat.zero_add]
      exact ⟨by simp [hc], by simp [hc], ⟨hnres, hpshape, htf, hlp, hbt⟩, hL.below, hL.params,
        hL.wd, hL.valid, hL.okTy, hL.mem⟩)
    (fun i c hc => by
      have hL := hleaf i c hc
      obtain ⟨-, -, htr, -⟩ :=
        ConLeche.checkConstantValPre_typeWF (hpre c (List.mem_of_getElem? hc))
      rw [Nat.zero_add]
      exact ⟨ConLeche.checkConstantValPre_fresh (hpre c (List.mem_of_getElem? hc)), htr, hL.read⟩)
  refine ⟨mp₂, hE₂, hag, fun i c hc => ?_⟩
  have := hleaves i c hc
  rwa [Nat.zero_add] at this

end ConLeche.Model
