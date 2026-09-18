module

public import ConLeche.Model.Inductives.NestedLoop
import ConLeche.Model.Inductives.NestedTransfer
import ConLeche.Verify.Inductives.NestedRestoreKit
import ConLeche.Verify.Inductives.NestedOpenSpine
public import ConLeche.Verify.Inductives.NestedRestoreOpen
public import ConLeche.Verify.Inductives.NestedRestoreTbl
import ConLeche.Verify.Inductives.NestedAuxInv
import ConLeche.Verify.Inductives.NestedInv
import ConLeche.Verify.Inductives.NestedElimInv
import ConLeche.Verify.Inductives.MutualInv
import ConLeche.Verify.Inductives.MutualGrouped
import ConLeche.Verify.EraseAnnots
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Steps.Accepted
import ConLeche.Model.Inductives.StructRows
import ConLeche.Model.Inductives.StructCtorFrames
import ConLeche.Model.Inductives.StructData
import ConLeche.Model.Inductives.StructTele
import ConLeche.Model.Inductives.StructCtorData
import ConLeche.Model.Inductives.SumRecRead
public section

/-!
# THE RESTORE READING LAW (task #315, M6 s9′)

`NestedReadLaw` (`NestedLoop.lean`) discharged: every restored
constructor's data at the prefix model (`NestedCtorRead`) from its
auxiliary twin's data at the scratch model, the door at the prefix
environment and the pins' facts (DESIGN §U.21b).

The restore touches a constructor's type at exactly the NESTED field
domains — the copy's head `aux p⃗ is` becomes the pin at the
parameter openers `J Ds is` (`restoreNested_opened`) — so the
restored constructor's opened form is the auxiliary one with, at a
nested position, the pin's components re-annotated.  Its readings at
the prefix model are then

* at an auxiliary-free position: the auxiliary reading TRANSFERRED
  from the scratch model (`nt_denoteMeta_transfer`: the piece resolves
  at the prefix environment, the two carriers agree on its names);
* at a nested position: the container's leaf at the pin's components
  lifted past the earlier fields (`nt_denoteMeta_restoredPin`) and the
  auxiliary index readings transferred;

and the two domain lists carry the SAME binder bits (the walk keeps
every binder meta: `nt_stripPisAV_denoteMeta_mkPisB`), which is what
turns the readings into the entry equalities `NestedCtorRead.dom`
demands and the pin identification `nestedIdent_of` into
`NestedCtorInput.agree`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecFieldKind RecRule
  NestedParts MutualBlock ElimState NestedPin IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The binder bits of a telescope's reading -/

/-- **A telescope's reading carries its binders' bits**: the `.pi`
entries `stripPisAV` peels off the reading of `mkPisB bs body` are
`(0, pwBit φ b.2.pw, _)`, one per binder, so two telescopes over the
same binder metas read with the same bits whatever their domains and
bodies. -/
theorem stripPisAV_denoteMeta_mkPisB {acval : Name → (Name → Nat) → AnnotTerm} {φ : Name → Nat} :
    ∀ (bs : List (Expr × BinderMeta)) {d : Nat} {body : Expr} {ea : AnnotTerm}
      {pps : List (Nat × Nat × AnnotTerm)} {b : AnnotTerm},
      denoteMeta acval env φ d (ConLeche.mkPisB bs body) = some ea →
      stripPisAV bs.length ea = some (pps, b) →
      ∀ (k : Nat) (p : Nat × Nat × AnnotTerm) (bm : Expr × BinderMeta),
        pps[k]? = some p → bs[k]? = some bm → p.1 = 0 ∧ p.2.1 = pwBit φ bm.2.pw
  | [], _, _, _, pps, _, _, hst, k, p, bm, hp, _ => by
    simp only [List.length_nil, stripPisAV, Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, -⟩ := hst
    exact absurd hp (by simp)
  | b₀ :: bs, d, body, ea, pps, b, hden, hst, k, p, bm, hp, hbm => by
    obtain ⟨ta, ba, -, hba, rfl⟩ := denoteMeta_forallE_inv hden
    simp only [List.length_cons, stripPisAV, Option.map_eq_some_iff] at hst
    obtain ⟨⟨pps', b'⟩, hst', heq⟩ := hst
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rw [ConLeche.mkPisB_instantiate1] at hba
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hp hbm
      subst hp; subst hbm
      exact ⟨rfl, rfl⟩
    | succ k =>
      simp only [List.getElem?_cons_succ] at hp hbm
      have hlen : (ConLeche.instTeleB (Expr.fvar d b₀.1) 0 bs).length = bs.length :=
        ConLeche.instTeleB_length _ _ _
      rw [← hlen] at hst'
      have hbm' : (ConLeche.instTeleB (Expr.fvar d b₀.1) 0 bs)[k]?
          = some (bm.1.instantiate1 (Expr.fvar d b₀.1) k, bm.2) := by
        rw [ConLeche.instTeleB_getElem?, hbm, Nat.zero_add]
        rfl
      exact stripPisAV_denoteMeta_mkPisB _ hba hst' k p (bm.1.instantiate1 (Expr.fvar d b₀.1) k, bm.2) hp hbm'

/-! ## The restored constructor's reading at the door -/

/-- **The restored constructor's type reads at the door** (the template
`ctorDataI_ofShapeDoor`'s per-assignment reading, at a given
residual reading): from the door's `inferTypeCore` run, the two
openings and the index arguments' readings, the type reads to the
Π-tower over SOME domain list ending in the member at the parameter
variables and those index readings, graded and bounded. -/
theorem restoredCtor_reads (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {F : Nat} {T : Name} {lps : List Name} {nP nF : Nat} {cv cvT : ConstantVal} {caps : IndCaps}
    {fvsP : List Expr} {crest : Expr} {xFvs idxArgs : List Expr} {ψ : Name → Nat}
    {Es : List AnnotTerm}
    (hfd : ConLeche.FrontDoorFacts μ F env cv cv)
    (hopC : openPisAtFvars nP cv.type 0 = some (fvsP, crest))
    (hopX : openPisAtFvars nF crest nP
      = some (xFvs, Expr.mkAppN (.const T (lps.map .param)) (fvsP ++ idxArgs)))
    (hfT : env.find? T = some (.indInfo cvT caps))
    (hlpsT : cvT.levelParams = lps)
    (hidxR : DenoteMetaSpine mp.base2.acval env ψ (nP + nF) idxArgs Es) :
    ∃ ds : List (Nat × Nat × AnnotTerm),
      denoteMeta mp.base2.acval env ψ 0 cv.type
        = some (mkPisAV ds (ctorBodyAVI mp.base2 T nP nF ψ Es)) ∧
      ds.length = nP + nF ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ (mkPisAV ds (ctorBodyAVI mp.base2 T nP nF ψ Es))) ∧
      DomsBelow 0 ds := by
  obtain ⟨stype, u, hst, -⟩ := hfd.infer
  have htf' : cv.type.hasFvar = false := hfd.noFvar
  have hbt' : cv.type.looseBVarsBounded 0 = true := hfd.bounded
  have hw : Expr.WScoped 0 cv.type := Expr.WScoped.of_not_hasFvar htf'
  have hL : Expr.LeavesBounded cv.type := Expr.LeavesBounded.of_not_hasFvar htf'
  have hnil : cv.type.fvarLeaves = [] := Expr.fvarLeaves_eq_nil_of_not_hasFvar htf'
  have hlenP : fvsP.length = nP := openPisAtFvars_length _ hopC
  have hopAll := openPisAtFvars_add nP hopC (by rw [Nat.zero_add]; exact hopX)
  have hidx := openPisAtFvars_index nP cv.type 0 hopC
  have hc := claimsAt_of hμ mp ψ F
  obtain ⟨Ta, hTa⟩ := acceptedReads_of mp.base2 ψ hst hw hbt' hL
  obtain ⟨-, -, hokT, -, -⟩ := hc.inferRow hst hw hbt' hL (CtxOk.nil hnil) hTa
  have hokT' : ∀ ρ : Nat → V, WellDenotedV V ρ Ta := fun ρ => hokT ρ (Sat_nil V ρ)
  obtain ⟨Γ, R, htele, hop'⟩ := opened_of hopAll htf' hbt' hTa hokT'
  -- the residual's spine, inverted
  obtain ⟨fa, vs, hfa, hsp, hR⟩ := denoteMeta_mkAppN_inv hop'.body
  have hfa' : fa = mp.base2.acval T ψ := by
    have hconst := denoteMeta_const (acval := mp.base2.acval) (env := env) (φ := ψ)
      (d := nP + nF) hfT
      (show (lps.map Level.param).length
        = (ConstantInfo.indInfo cvT caps).toConstantVal.levelParams.length by
        show (lps.map Level.param).length = cvT.levelParams.length
        rw [hlpsT, List.length_map])
    have hsubst : Level.substFn ψ (ConstantInfo.indInfo cvT caps).toConstantVal.levelParams
        (lps.map Level.param) = ψ := by
      show Level.substFn ψ cvT.levelParams (lps.map Level.param) = ψ
      rw [hlpsT]
      exact Level.substFn_param_self ψ _
    rw [hconst, hsubst] at hfa
    exact (Option.some.inj hfa).symm
  subst hfa'
  obtain ⟨vs₁, vs₂, rfl, hsp₁, hsp₂⟩ := DenoteMetaSpine.append_inv hsp
  have hvs₁ : vs₁ = paramBvars nP nF := by
    have := DenoteMetaSpine.unique hsp₁
      (denoteMetaSpine_indexed (acval := mp.base2.acval) (env := env) (φ := ψ) (d := nP + nF)
        fvsP 0 hidx)
    rw [this, hlenP]
    unfold paramBvars
    apply List.map_congr_left
    intro k _
    rw [Nat.zero_add]
  subst hvs₁
  have hvs₂ : vs₂ = Es := DenoteMetaSpine.unique hsp₂ hidxR
  subst vs₂
  have hR' : R = ctorBodyAVI mp.base2 T nP nF ψ Es := hR
  subst hR'
  obtain ⟨ds, hst', -⟩ := stripPisAV_of_piTeleAV htele
  obtain ⟨hTeq, hlen⟩ := stripPisAV_eq_mkPis hst'
  subst hTeq
  have hbelowAll := stripPisAV_below hst' (bvarsBelow_of_reading hw hbt' hTa)
  exact ⟨ds, hTa, hlen, hokT', hbelowAll.1⟩

/-- **The restored constructor's reading, per assignment**: the domain
list the door's reading peels at every level assignment, ending in the
member at the parameter variables and the index readings `Es`; graded,
bounded, and a function of the constructor's level parameters. -/
structure ReadSpec (mp : EnvModelM V μ env) (T : Name) (nP nF : Nat) (cv : ConstantVal)
    (Es : (Name → Nat) → List AnnotTerm) (ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)) :
    Prop where
  read : ∀ ψ : Name → Nat, denoteMeta mp.base2.acval env ψ 0 cv.type
    = some (mkPisAV (ds ψ) (ctorBodyAVI mp.base2 T nP nF ψ (Es ψ)))
  len : ∀ ψ : Name → Nat, (ds ψ).length = nP + nF
  okTy : ∀ (ψ : Name → Nat) (ρ : Nat → V),
    WellDenotedV V ρ (mkPisAV (ds ψ) (ctorBodyAVI mp.base2 T nP nF ψ (Es ψ)))
  below : ∀ ψ : Name → Nat, DomsBelow 0 (ds ψ)
  params : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ cv.levelParams, ψ₁ q = ψ₂ q) → ds ψ₁ = ds ψ₂

/-- The reading exists (`restoredCtor_reads` at every assignment, the
domain list chosen). -/
theorem readSpec_exists (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {F : Nat} {T : Name} {lps : List Name} {nP nF : Nat} {cv cvT : ConstantVal} {caps : IndCaps}
    {fvsP : List Expr} {crest : Expr} {xFvs idxArgs : List Expr}
    {Es : (Name → Nat) → List AnnotTerm}
    (hfd : ConLeche.FrontDoorFacts μ F env cv cv)
    (hopC : openPisAtFvars nP cv.type 0 = some (fvsP, crest))
    (hopX : openPisAtFvars nF crest nP
      = some (xFvs, Expr.mkAppN (.const T (lps.map .param)) (fvsP ++ idxArgs)))
    (hfT : env.find? T = some (.indInfo cvT caps))
    (hlpsT : cvT.levelParams = lps)
    (hidxR : ∀ ψ : Name → Nat, DenoteMetaSpine mp.base2.acval env ψ (nP + nF) idxArgs (Es ψ)) :
    ∃ ds : (Name → Nat) → List (Nat × Nat × AnnotTerm), ReadSpec mp T nP nF cv Es ds := by
  have hper := fun ψ => restoredCtor_reads (V := V) hμ mp hfd hopC hopX hfT hlpsT (hidxR ψ)
  have hspec : ∀ ψ, _ := fun ψ => Classical.choose_spec (hper ψ)
  refine ⟨fun ψ => Classical.choose (hper ψ), fun ψ => (hspec ψ).1, fun ψ => (hspec ψ).2.1,
    fun ψ => (hspec ψ).2.2.1, fun ψ => (hspec ψ).2.2.2, ?_⟩
  intro ψ₁ ψ₂ hφ
  have h2 := (hspec ψ₂).1
  have h1 : denoteMeta mp.base2.acval env ψ₂ 0 cv.type
      = some (mkPisAV (Classical.choose (hper ψ₁)) (ctorBodyAVI mp.base2 T nP nF ψ₁ (Es ψ₁))) := by
    rw [← denoteMeta_params_ext mp.base2 hφ 0 cv.type hfd.lpsOk]
    exact (hspec ψ₁).1
  exact (mkPisAV_inj (by rw [(hspec ψ₁).2.1, (hspec ψ₂).2.1])
    (Option.some.inj (h1.symm.trans h2))).1

/-! ## Syntactic helpers -/

/-- Two application spines compose. -/
theorem annotMkAppN_append : ∀ (as bs : List AnnotTerm) (f : AnnotTerm),
    AnnotTerm.mkAppN (AnnotTerm.mkAppN f as) bs = AnnotTerm.mkAppN f (as ++ bs)
  | [], _, _ => rfl
  | a :: as, bs, f => annotMkAppN_append as bs (.app f a)


/-- **`FieldsBoundSrc` transports along fields reading alike at every
fitting prefix.** -/
theorem fieldsBoundSrc_congr :
    ∀ (FsA FsR : List AnnotTerm) (srcs : List (Option Nat)) (ρ : Nat → V),
      FsA.length = FsR.length →
      (∀ l, l < FsA.length → ∀ fs₁ : List V, fs₁.length = l →
        SpineFit ρ (FsA.take l) fs₁ → SpineFit ρ (FsR.take l) fs₁ →
        interp V (consList fs₁ ρ) (FsA.getD l default) = interp V (consList fs₁ ρ) (FsR.getD l default)) →
      FieldsBoundSrc ρ FsA srcs → FieldsBoundSrc ρ FsR srcs
  | [], FsR, _, _, hlen, _, _ => by
    cases FsR with
    | nil => trivial
    | cons _ _ => simp at hlen
  | FA :: FsA, FsR, srcs, ρ, hlen, hag, hb => by
    cases FsR with
    | nil => simp at hlen
    | cons FR FsR =>
      cases srcs with
      | nil => trivial
      | cons s ss =>
        obtain ⟨hb1, hb2⟩ := hb
        have hhead : interp V ρ FA = interp V ρ FR :=
          hag 0 (by simp) [] rfl trivial trivial
        refine ⟨fun hs => by rw [← hhead]; exact hb1 hs, fun a ha => ?_⟩
        have haA : a ∈ˢ interp V ρ FA := by rw [hhead]; exact ha
        refine fieldsBoundSrc_congr FsA FsR ss (cons a ρ) (by simpa using hlen) ?_ (hb2 a haA)
        intro l hl fs₁ hl₁ hfA hfR
        have := hag (l + 1) (by simp; omega) (a :: fs₁) (by simp [hl₁]) ⟨haA, hfA⟩ ⟨ha, hfR⟩
        simpa using this

/-- A spine mentions a constant only through its head or an argument. -/
theorem mentionsConst_mkAppN_false {n : Name} :
    ∀ (as : List Expr) (f : Expr), f.mentionsConst n = false →
      (∀ a ∈ as, a.mentionsConst n = false) → (Expr.mkAppN f as).mentionsConst n = false
  | [], _, hf, _ => hf
  | a :: as, f, hf, has =>
    mentionsConst_mkAppN_false as (.app f a)
      (by simp only [Expr.mentionsConst, hf, has a List.mem_cons_self, Bool.or_self])
      (fun x hx => has x (List.mem_cons_of_mem _ hx))

/-- A telescope mentions a constant only through a binder or the body. -/
theorem mentionsConst_mkPisB_false {n : Name} :
    ∀ (bs : List (Expr × BinderMeta)) (body : Expr), (∀ b ∈ bs, b.1.mentionsConst n = false) →
      body.mentionsConst n = false → (ConLeche.mkPisB bs body).mentionsConst n = false
  | [], _, _, hb => hb
  | b :: bs, body, hbs, hb => by
    show (Expr.forallE b.1 (ConLeche.mkPisB bs body) b.2).mentionsConst n = false
    simp only [Expr.mentionsConst, hbs b List.mem_cons_self,
      mentionsConst_mkPisB_false bs body (fun x hx => hbs x (List.mem_cons_of_mem _ hx)) hb,
      Bool.or_self]

/-- **A binder's constant reaches an opener's annotation**: opening a
telescope at variables, a binder domain mentioning `n` yields an opener
whose annotation mentions `n` (the annotation is the domain instantiated
at the earlier openers). -/
theorem openPisAtFvars_binder_mentionsConst {n : Name} :
    ∀ (bs : List (Expr × BinderMeta)) (body : Expr) (d : Nat) (fvs : List Expr) (o : Expr),
      openPisAtFvars bs.length (ConLeche.mkPisB bs body) d = some (fvs, o) →
      ∀ (k : Nat) (b : Expr × BinderMeta), bs[k]? = some b → b.1.mentionsConst n = true →
        ∃ a ∈ fvs, a.fvarTypeD.mentionsConst n = true
  | [], _, _, _, _, _, k, b, hb, _ => absurd hb (by simp)
  | b₀ :: bs, body, d, fvs, o, hop, k, b, hb, hn => by
    simp only [List.length_cons] at hop
    replace hop : openPisAtFvars (bs.length + 1) (Expr.forallE b₀.1 (ConLeche.mkPisB bs body) b₀.2) d
      = some (fvs, o) := hop
    simp only [openPisAtFvars] at hop
    cases hop' : openPisAtFvars bs.length
        ((ConLeche.mkPisB bs body).instantiate1 (.fvar d b₀.1)) (d + 1) with
    | none => rw [hop'] at hop; exact nomatch hop
    | some pr =>
      obtain ⟨fvs', o'⟩ := pr
      rw [hop'] at hop
      simp only [Option.some.injEq, Prod.mk.injEq] at hop
      obtain ⟨rfl, rfl⟩ := hop
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
        subst hb
        exact ⟨.fvar d _, List.mem_cons_self, hn⟩
      | succ k =>
        simp only [List.getElem?_cons_succ] at hb
        rw [ConLeche.mkPisB_instantiate1] at hop'
        have hlen : (ConLeche.instTeleB (Expr.fvar d b₀.1) 0 bs).length = bs.length :=
          ConLeche.instTeleB_length _ _ _
        rw [← hlen] at hop'
        obtain ⟨a, ha, han⟩ := openPisAtFvars_binder_mentionsConst _ _ _ _ _ hop' k
          (b.1.instantiate1 (Expr.fvar d b₀.1) k, b.2)
          (by rw [ConLeche.instTeleB_getElem?, hb, Nat.zero_add]; rfl)
          (Expr.mentionsConst_instantiate1 hn)
        exact ⟨a, List.mem_cons_of_mem _ ha, han⟩

/-! ## The reading law's context -/

section Assembly

variable {F : Nat} {mp : EnvModelM V μ env} {p : NestedParts} {b : MutualBlock}
  {fms : List MutualFormerA} {f₀ : MutualFormerA} {ctorsA : List (ConstantVal × Nat)}
  {sortss : List (List Level)} {kinds : List (List (RecFieldKind × Nat))}
  {mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env)}
  {ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {W : (Name → Nat) → Nat}
  {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
  {fvsPF xFvsF : Nat → List Expr} {xrestF : Nat → Expr}
  {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
  {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
  {ctorsR : List (List (ConstantVal × Nat × Nat))}
  {dsR : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {xFvsR : Nat → Nat → List Expr}
  {pinsS : List PinSyn}

local notation "ENV₁" => (ConLeche.consMutualFormers (fms.take p.k) env)
local notation "SCR" => (ConLeche.consMutualFormers fms env)
local notation "D" => (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
  srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS)

/-- **The reading law's context**: the run's conjuncts the law reads,
the auxiliary block's formers' facts at the scratch model, the prefix
model's member facts, the restore conjunct at the prefix environment,
and the pins' facts (`NestedReadLaw`'s hypotheses, bundled). -/
structure ReadCtx (st : ElimState) (envAux : Env) (stored : List AuxStored)
    (fmsA ctorsA₀ : List ConstantVal) (mp₁' : EnvModelM V μ ENV₁) : Prop where
  hμ : μ.verifiedChecks = true
  hfA : ConLeche.nestedAnnotFormers (m := ConLeche.CheckM) (fueledOps μ F) env p.nP p.formers
    = .ok fmsA
  helim : ConLeche.elimNested env p.nP p.lps (ConLeche.nestedTypes0 p fmsA ctorsA₀) = .ok st
  hfresh : ConLeche.copiesFresh env p.k st = true
  hb : ConLeche.auxBlock p st = some b
  haux : ConLeche.checkMutualCore (m := ConLeche.CheckM) (fueledOps μ F) env b none true = .ok envAux
  hstored : ConLeche.auxStoredAll envAux b b.k = some stored
  hclosed : ConLeche.pinsClosed p.nP st.pins = true
  hformers : ConLeche.mutualFormers (m := ConLeche.CheckM) (fueledOps μ F) b.nP b.formers env true
    = .ok (SCR, fms)
  h : MutualFormersFacts V F true mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
    fvsPF xFvsF xrestF eissF tssF
  hbk : b.k = p.k + st.pins.length
  h3 : ConLeche.mutualCtorsGrouped b.ctors = true
  hnd : b.blockNames.Nodup
  hctorsA : ConLeche.checkMutualCtors (m := ConLeche.CheckM) (fueledOps μ F) SCR b fms
    (Level.isEquiv f₀.s .zero == some true) true b.ctors = .ok (ctorsA, sortss)
  hleafM' : ∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f →
    mp₁'.base2.acval f.cvTa.name = mutMemberLeaf b fms f₀ ctorsA kinds ppsF W dsF esF eissF tssF t
  hoff' : ∀ n : Name, (∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f → n ≠ f.cvTa.name) →
    mp₁'.base2.acval n = mp.base2.acval n
  hfind' : ∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f →
    (ENV₁).find? f.cvTa.name = some (.indInfo f.cvTa {}) ∧
    FormerData mp₁'.base2 f.cvTa (b.nP + f.nIdx) f₀.s (ppsF t)
  hctors : (stored.take p.k).mapM (fun a =>
      ConLeche.restoreCtors (m := ConLeche.CheckM) (fueledOps μ F) ENV₁ (ConLeche.restoreTbl p st)
        p.lps a.ctors)
    = .ok ctorsR
  PF : NestedPinFacts (V := V) (mp := mp) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
    (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF)
    (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
    (tssF := tssF) (ctorsR := ctorsR) (pinsS := pinsS) st mp₁'

variable {st : ElimState} {envAux : Env} {stored : List AuxStored} {fmsA ctorsA₀ : List ConstantVal}
  {mp₁' : EnvModelM V μ (ConLeche.consMutualFormers (fms.take p.k) env)}
  (C : ReadCtx (V := V) (μ := μ) (env := env) (F := F) (mp := mp) (p := p) (b := b) (fms := fms)
    (f₀ := f₀) (ctorsA := ctorsA) (sortss := sortss) (kinds := kinds) (mp₁ := mp₁) (ppsF := ppsF)
    (W := W) (idxF := idxF) (dsF := dsF) (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF)
    (xFvsF := xFvsF) (xrestF := xrestF) (eissF := eissF) (tssF := tssF) (ctorsR := ctorsR)
    (pinsS := pinsS) st envAux stored fmsA ctorsA₀ mp₁')
include C

/-! ### The block's shape, read off the context -/

theorem ReadCtx.hnP : b.nP = p.nP := (ConLeche.auxBlock_fields C.hb).1
theorem ReadCtx.hlps : b.lps = p.lps := (ConLeche.auxBlock_fields C.hb).2.1
theorem ReadCtx.hkle : p.k ≤ fms.length := by
  rw [C.h.lenFms, C.hbk]; exact Nat.le_add_right _ _
theorem ReadCtx.hal : ConLeche.PinsAligned p.k st :=
  ConLeche.elimNested_aligned (by
    rw [ConLeche.nestedTypes0_length, ConLeche.nestedAnnotFormers_length C.hfA]; rfl) C.helim
theorem ReadCtx.hlenA : ctorsA.length = b.ctors.length := C.h.lenA
theorem ReadCtx.hndA : (ctorsA.map (·.1.name)).Nodup := by
  rw [C.h.namesC]
  have h0 := C.hnd
  unfold ConLeche.MutualBlock.blockNames at h0
  exact (List.nodup_append.mp (List.nodup_append.mp h0).1).2.1

/-- A member `t < p.k` of the block, read at the prefix model. -/
theorem ReadCtx.memberAt (t : Nat) (ht : t < p.k) :
    fms[t]? = some (fms.getD t default) := fms_get (Nat.lt_of_lt_of_le ht C.hkle)

/-- The copy at pin `q` is the block's member `p.k + q`, under the pin's
auxiliary name. -/
theorem ReadCtx.copyName {q : Nat} {qn : NestedPin} (hq : st.pins[q]? = some qn) :
    p.k + q < fms.length ∧ (fms.getD (p.k + q) default).cvTa.name = qn.aux := by
  obtain ⟨hlenT, hal⟩ := C.hal
  obtain ⟨t, ht, htn⟩ := hal q qn hq
  have hql : q < st.pins.length := (List.getElem?_eq_some_iff.mp hq).1
  have hlt : p.k + q < fms.length := by rw [C.h.lenFms, C.hbk]; omega
  refine ⟨hlt, ?_⟩
  have hm := ConLeche.auxBlock_memberNames_eq C.hb
  have hn := C.h.names
  have h1 : (fms.map (·.cvTa.name))[p.k + q]? = some (fms.getD (p.k + q) default).cvTa.name := by
    rw [List.getElem?_map, fms_get hlt]; rfl
  rw [hn, hm, List.getElem?_map, ht] at h1
  simp only [Option.map_some, Option.some.injEq] at h1
  rw [← h1, htn]

/-- The restored constructor `(mm, j)`: its auxiliary twin, its field
count, the restore, and the door at the prefix environment. -/
theorem ReadCtx.ctorFacts {mm j : Nat} {c : ConstantVal × Nat × Nat} (hmm : mm < p.k)
    (hc : (ctorsR.getD mm [])[j]? = some c) :
    j < (b.ownCtors mm).length ∧
    ∃ cA : ConstantVal × Nat, ctorsA[b.ownOffset mm + j]? = some cA ∧ c.2.2 = cA.2 ∧ c.2.1 = b.nP ∧
      ConLeche.restoreNested (ConLeche.restoreTbl p st) cA.1.type = .ok c.1.type ∧
      ConLeche.FrontDoorFacts μ F ENV₁ c.1 c.1 ∧
      c.1 = { cA.1 with levelParams := p.lps, type := c.1.type } := by
  have hlenS : stored.length = b.k := (ConLeche.auxStoredAll_get C.hstored).1
  obtain ⟨hlenR, hposR⟩ := ConLeche.mapM_except_inv C.hctors
  have hlenT : (stored.take p.k).length = p.k := by
    rw [List.length_take, hlenS, C.hbk]; exact Nat.min_eq_left (Nat.le_add_right _ _)
  obtain ⟨a, cs, ha, hcs, hrun⟩ := hposR mm (by rw [hlenT]; exact hmm)
  rw [List.getElem?_take_of_lt hmm] at ha
  rw [List.getD_eq_getElem?_getD, hcs, Option.getD_some] at hc
  obtain ⟨hlenC, hdoor⟩ := ConLeche.restoreCtors_door hrun
  have hjl : j < a.ctors.length := by
    rw [← hlenC]; exact (List.getElem?_eq_some_iff.mp hc).1
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, a.ctors[j]? = some c₀ := ⟨_, List.getElem?_eq_getElem hjl⟩
  obtain ⟨ty, hres, hfd, h2, h1⟩ := hdoor j c₀ c hc₀ hc
  obtain ⟨hlenOwn, hallOwn⟩ :=
    ConLeche.auxStored_ctor_eq C.haux C.hformers C.hctorsA C.h3 C.hstored ha
  obtain ⟨cA, hcA, e1, e2, e3⟩ := hallOwn j c₀ hc₀
  have hty : c.1.type = ty := by rw [h1]
  refine ⟨by rw [← hlenOwn]; exact hjl, cA, hcA, by rw [h2]; exact e3, by rw [h2]; exact e2, ?_,
    ?_, ?_⟩
  · rw [hty, ← e1]; exact hres
  · rw [← h1] at hfd; exact hfd
  · rw [h1, ← e1]

/-- The constructor at `b.ownOffset mm + j` is member `mm`'s. -/
theorem ReadCtx.memJ {mm j : Nat} (hjl : j < (b.ownCtors mm).length) :
    b.ownOffset mm + j < ctorsA.length ∧ mutMemF b (b.ownOffset mm + j) = mm := by
  rcases hx : (b.ownCtors mm)[j] with ⟨J', c'⟩
  have hj' : (b.ownCtors mm)[j]? = some (J', c') := by rw [List.getElem?_eq_getElem hjl, hx]
  have hJ' := ConLeche.ownCtors_getElem?_idx C.h3 hj'
  obtain ⟨hcJ, hmemc⟩ := ConLeche.ownCtors_getElem?_ctors hj'
  subst hJ'
  refine ⟨by rw [C.hlenA]; exact (List.getElem?_eq_some_iff.mp hcJ).1, ?_⟩
  show (b.ctors.getD (b.ownOffset mm + j) default).member = mm
  rw [List.getD_eq_getElem?_getD, hcJ]
  exact hmemc

/-- Member `t`'s name and index count at the block model. -/
theorem ReadCtx.hName (t : Nat) (ht : t < p.k) :
    ((fms.take p.k).map (·.cvTa.name)).getD t .anonymous = (fms.getD t default).cvTa.name := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take_of_lt ht, C.memberAt t ht]
  rfl

theorem ReadCtx.hNIdx (t : Nat) (ht : t < p.k) :
    ((fms.take p.k).map (·.nIdx)).getD t 0 = (fms.getD t default).nIdx := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take_of_lt ht, C.memberAt t ht]
  rfl

/-- A pin's table entries: the pin map answers the abstracted pin, the
recursor map declines. -/
theorem ReadCtx.pinLookup {q : Nat} {qn : NestedPin} (hq : st.pins[q]? = some qn) :
    (ConLeche.restoreTbl p st).pins.lookup qn.aux
      = some (Expr.abstractRange qn.pin 0 p.nP 0) ∧
    (ConLeche.restoreTbl p st).recMap.lookup qn.aux = none :=
  ⟨ConLeche.restoreTbl_pins_lookup_run C.hfA C.helim C.hb C.haux hq,
    ConLeche.restoreTbl_recMap_lookup_aux' C.hfA C.helim C.hb C.haux hq⟩


/-- **The restore table's auxiliary names are absent** before the block
and at the prefix environment. -/
theorem ReadCtx.auxFree : ∀ n ∈ (ConLeche.restoreTbl p st).auxNames,
    env.find? n = none ∧ (ENV₁).find? n = none := by
  intro n hn
  obtain ⟨henv, hmem⟩ := ConLeche.rk_restoreTbl_auxNames_fresh C.hnd C.hal C.hb C.hfresh n hn
  refine ⟨henv, ?_⟩
  rw [consMutualFormers_find?_of_ne, henv]
  intro g hg heq
  apply hmem
  have : g.cvTa.name ∈ (fms.take p.k).map (·.cvTa.name) := List.mem_map_of_mem hg
  rw [List.map_take, C.h.names] at this
  rw [← heq]; exact this

/-- A member of the block's own prefix is no auxiliary name. -/
theorem ReadCtx.memberNotAux {t : Nat} (ht : t < p.k) :
    ∀ n ∈ (ConLeche.restoreTbl p st).auxNames, (fms.getD t default).cvTa.name ≠ n := by
  intro n hn heq
  have := (C.auxFree n hn).2
  rw [← heq, (C.hfind' t _ ht (C.memberAt t ht)).1] at this
  exact nomatch this

/-- A term resolving at the prefix environment mentions no auxiliary name. -/
theorem ReadCtx.auxFree_of_resolve {e : Expr} (h : e.constsResolve ENV₁ = true) :
    ∀ n ∈ (ConLeche.restoreTbl p st).auxNames, e.mentionsConst n = false :=
  fun n hn => ConLeche.rk_mentionsConst_false_of_constsResolve h (C.auxFree n hn).2

/-- A term resolving before the block mentions no auxiliary name. -/
theorem ReadCtx.auxFree_of_resolve₀ {e : Expr} (h : e.constsResolve env = true) :
    ∀ n ∈ (ConLeche.restoreTbl p st).auxNames, e.mentionsConst n = false :=
  fun n hn => ConLeche.rk_mentionsConst_false_of_constsResolve h (C.auxFree n hn).1

/-- Every pin of the table is closed over the block's parameters. -/
theorem ReadCtx.hpinB : ∀ (n : Name) (pin : Expr),
    (ConLeche.restoreTbl p st).pins.lookup n = some pin → pin.looseBVarsBounded b.nP = true := by
  intro n pin hl
  obtain ⟨q, hq, -, rfl⟩ := ConLeche.rk_restoreTbl_pins_lookup_inv hl
  rw [C.hnP]
  exact (ConLeche.rk_pinsClosed_of C.hclosed q hq).2

/-! ### The auxiliary constructor's residual, off its run -/

/-- **The auxiliary constructor's openings and residual**: the two
openings its data record, and the residual as the run's shape says —
the member at the parameter openers and the index arguments. -/
theorem ReadCtx.auxShape {J : Nat} {cA : ConstantVal × Nat} (hJ : ctorsA[J]? = some cA) :
    ∃ crest : Expr,
      openPisAtFvars b.nP cA.1.type 0 = some (fvsPF J, crest) ∧
      openPisAtFvars cA.2 crest b.nP = some (xFvsF J, xrestF J) ∧
      xrestF J = Expr.mkAppN (.const (fms.getD (mutMemF b J) default).cvTa.name (b.lps.map .param))
        (fvsPF J ++ idxF J) ∧
      (idxF J).length = (fms.getD (mutMemF b J) default).nIdx ∧
      (fvsPF J).length = b.nP ∧
      cA.1.type.hasFvar = false ∧ cA.1.type.looseBVarsBounded 0 = true := by
  have hCD := C.h.CD J cA hJ
  obtain ⟨crest, hopP, hopX⟩ := hCD.opens
  obtain ⟨-, sorts, -, hrun⟩ := C.h.runC J cA hJ
  obtain ⟨⟨ty', hfdA⟩, -, fvsP', crest', -, -, xFvs', idxArgs', hopP', -, -, hopX', -, -, -, -⟩ :=
    ConLeche.checkMutualCtorG_shape hrun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hopP.symm.trans hopP'))
  obtain ⟨rfl, hxr⟩ := Prod.mk.inj (Option.some.inj (hopX.symm.trans hopX'))
  have hlenP : (fvsPF J).length = b.nP := hCD.pLen
  have hidx : idxF J = idxArgs' := by
    rw [hCD.idxEq, hxr, Expr.getAppArgs_mkAppN,
      show (Expr.const (fms.getD (mutMemF b J) default).cvTa.name (b.lps.map .param)).getAppArgs = []
        from rfl, List.nil_append, List.drop_left' hlenP]
  exact ⟨crest, hopP, hopX, by rw [hxr, hidx], hCD.idxLen, hlenP, hfdA.noFvar, hfdA.bounded⟩

/-- The parameter openers are the variables `0 … nP-1`. -/
theorem ReadCtx.fvsPIdx {J : Nat} {cA : ConstantVal × Nat} (hJ : ctorsA[J]? = some cA) :
    ∀ k, k < b.nP → ∃ ty, (fvsPF J)[k]? = some (.fvar k ty) := by
  intro k hk
  have hCD := C.h.CD J cA hJ
  have hkl : k < (fvsPF J).length := by rw [hCD.pLen]; exact hk
  obtain ⟨x, hx⟩ : ∃ x, (fvsPF J)[k]? = some x := ⟨_, List.getElem?_eq_getElem hkl⟩
  obtain ⟨ty, rfl⟩ := hCD.pIdx k x hx
  exact ⟨ty, hx⟩


/-! ### The restored constructor, opened, field by field -/

/-- **One restored field's domain** against its auxiliary twin `x`
(the auxiliary constructor `J`'s field `i`, kinds `ks`, parameter
openers `fvsP`): at an auxiliary-free position it is the auxiliary
domain; at a finitary nested position the pin re-opened at the
parameter openers applied to the auxiliary index arguments; at a
reflexive nested position the auxiliary telescope over that. -/
@[expose] def RestoredField (p : NestedParts) (st : ElimState) (b : MutualBlock)
    (ks : List (RecFieldKind × Nat)) (fvsP : List Expr) (i : Nat) (x ty' : Expr) : Prop :=
  ((kindAt ks i = .ordinary ∨ tgtAt ks i < p.k) ∧ ty' = x.fvarTypeD) ∨
  (∃ (q : Nat) (qn : NestedPin), st.pins[q]? = some qn ∧ tgtAt ks i = p.k + q ∧
    kindAt ks i = .recursive ∧
    x.fvarTypeD = Expr.mkAppN (.const qn.aux (b.lps.map .param))
      (fvsP ++ x.fvarTypeD.getAppArgs.drop b.nP) ∧
    ty' = Expr.mkAppN (Expr.instSeq fvsP (b.nP - 1) (Expr.abstractRange qn.pin 0 p.nP 0))
      (x.fvarTypeD.getAppArgs.drop b.nP)) ∨
  (∃ (q : Nat) (qn : NestedPin) (tbs : List (Expr × BinderMeta)) (is₀ afvs is : List Expr),
    st.pins[q]? = some qn ∧ tgtAt ks i = p.k + q ∧ kindAt ks i = .reflexive ∧
    openPisAtFvars (x.fvarTypeD.piBinders).1.length x.fvarTypeD (b.nP + i)
      = some (afvs, Expr.mkAppN (.const qn.aux (b.lps.map .param)) (fvsP ++ is)) ∧
    x.fvarTypeD.stripPis (x.fvarTypeD.piBinders).1.length
      = some (tbs, Expr.mkAppN (.const qn.aux (b.lps.map .param)) (fvsP ++ is₀)) ∧
    is = is₀.map (Expr.instSeq afvs ((x.fvarTypeD.piBinders).1.length - 1)) ∧
    ty'.stripPis (x.fvarTypeD.piBinders).1.length
      = some (tbs, Expr.mkAppN (Expr.instSeq fvsP (b.nP - 1) (Expr.abstractRange qn.pin 0 p.nP 0))
          is₀))

/-- A recursive field's auxiliary domain is its target's former at the
parameter openers and its index arguments. -/
theorem ReadCtx.recShape {J : Nat} {cA : ConstantVal × Nat} (hJ : ctorsA[J]? = some cA)
    {i : Nat} {x : Expr} (hx : (xFvsF J)[i]? = some x)
    (hk : kindAt (mutKsOf kinds J) i = .recursive) :
    x.fvarTypeD = Expr.mkAppN
      (.const (mutualNameOf b.members3 (tgtAt (mutKsOf kinds J) i)) (b.lps.map .param))
      (fvsPF J ++ x.fvarTypeD.getAppArgs.drop b.nP) := by
  obtain ⟨hfn, htake, -, -, -, -⟩ := (C.h.CD J cA hJ).opened.recF i x hx hk
  have := Expr.mkAppN_getApp x.fvarTypeD
  rw [hfn, ← List.take_append_drop b.nP x.fvarTypeD.getAppArgs, htake] at this
  exact this.symm

/-- A member's former name at the block's member table. -/
theorem ReadCtx.memberName {t : Nat} (ht : t < fms.length) :
    mutualNameOf b.members3 t = (fms.getD t default).cvTa.name :=
  (C.h.memT t _ (fms_get ht)).1

/-- **The restored constructor, opened**: its auxiliary twin, the
door, the two openings at the AUXILIARY parameter openers and residual,
the residual at `stripPis`, and every field's domain against its
auxiliary twin (`RestoredField`). -/
theorem ReadCtx.restoredOpened {mm j : Nat} {c : ConstantVal × Nat × Nat} (hmm : mm < p.k)
    (hc : (ctorsR.getD mm [])[j]? = some c) :
    ∃ (cA : ConstantVal × Nat) (crestR : Expr) (xFvsRc : List Expr),
      ctorsA[b.ownOffset mm + j]? = some cA ∧ c.2.2 = cA.2 ∧ c.2.1 = b.nP ∧
      c.1.levelParams = p.lps ∧ c.1.name = cA.1.name ∧
      ConLeche.FrontDoorFacts μ F ENV₁ c.1 c.1 ∧ j < (b.ownCtors mm).length ∧
      mutMemF b (b.ownOffset mm + j) = mm ∧
      openPisAtFvars b.nP c.1.type 0 = some (fvsPF (b.ownOffset mm + j), crestR) ∧
      openPisAtFvars cA.2 crestR b.nP = some (xFvsRc, xrestF (b.ownOffset mm + j)) ∧
      xFvsRc.length = cA.2 ∧
      (∃ (cbsA cbs' : List (Expr × BinderMeta)) (es : List Expr),
        cA.1.type.stripPis (b.nP + cA.2)
          = some (cbsA, Expr.mkAppN (.const (fms.getD mm default).cvTa.name (b.lps.map .param))
              (ConLeche.structPsAt cA.2 b.nP ++ es)) ∧
        c.1.type.stripPis (b.nP + cA.2)
          = some (cbs', Expr.mkAppN (.const (fms.getD mm default).cvTa.name (b.lps.map .param))
              (ConLeche.structPsAt cA.2 b.nP ++ es)) ∧
        cbs'.map (·.2) = cbsA.map (·.2) ∧
        es.length = (fms.getD mm default).nIdx) ∧
      ∀ (i : Nat) (x : Expr), (xFvsF (b.ownOffset mm + j))[i]? = some x →
        ∃ ty', xFvsRc[i]? = some (.fvar (b.nP + i) ty') ∧
          RestoredField p st b (mutKsOf kinds (b.ownOffset mm + j)) (fvsPF (b.ownOffset mm + j)) i x ty' := by
  obtain ⟨hjl, cA, hJ, hnF, hnP1, hres, hfd, hceq⟩ := C.ctorFacts hmm hc
  obtain ⟨hJl, hmemJ⟩ := C.memJ hjl
  obtain ⟨crest, hopP, hopX, hxrEq, hlenI, hlenP, -, -⟩ := C.auxShape hJ
  rw [hmemJ] at hxrEq hlenI
  have hCD := C.h.CD (b.ownOffset mm + j) cA hJ
  have hO := hCD.opened
  have hnP := C.hnP
  have hRnP : (ConLeche.restoreTbl p st).nP = b.nP := by rw [ConLeche.restoreTbl_nP, hnP]
  have hlpsC : c.1.levelParams = p.lps := by rw [hceq]
  have hnameC : c.1.name = cA.1.name := by rw [hceq]
  -- the restored parameter opening, at the auxiliary openers
  obtain ⟨bs, bodyA, hsA, hbslen, -, -⟩ := Verify.openPisAtFvars_stripPis b.nP hopP
  have hbsl : bs.length = b.nP := Expr.stripPis_length _ hsA
  have htyA : cA.1.type = ConLeche.mkPisB bs bodyA := ConLeche.stripPis_mkPisB _ hsA
  obtain ⟨bodyR, hwalk, htyR⟩ := ConLeche.restoreNested_pis (R := ConLeche.restoreTbl p st)
    (bs := bs) (body := bodyA) (by rw [hRnP]; exact hsA)
    (by
      intro hpos
      rw [hRnP] at hpos
      cases bs with
      | nil => rw [← hbsl] at hpos; simp at hpos
      | cons b₀ bs' => exact ⟨b₀.1, ConLeche.mkPisB bs' bodyA, b₀.2, by rw [htyA]; rfl⟩)
    hres
  rw [ConLeche.mkPisB_eq_foldr] at htyR
  obtain ⟨fvs, -, -, hlaw⟩ := ConLeche.openPisAtFvars_mkPisB b.nP bs hbsl 0
  have hlawA := hlaw bodyA
  rw [← htyA, hopP] at hlawA
  simp only [Option.some.injEq, Prod.mk.injEq] at hlawA
  obtain ⟨rfl, -⟩ := hlawA
  have hopR₀ : openPisAtFvars b.nP c.1.type 0
      = some (fvsPF (b.ownOffset mm + j), Expr.instSeq (fvsPF (b.ownOffset mm + j)) (b.nP - 1) bodyR) := by
    rw [htyR]; exact hlaw bodyR
  -- the parameter openers' annotations resolve at the prefix environment
  obtain ⟨hPres, -⟩ := ConLeche.rk_openPisAtFvars_constsResolve b.nP hopR₀ hfd.resolve
  have hPfree : ∀ v ∈ fvsPF (b.ownOffset mm + j), ∀ n ∈ (ConLeche.restoreTbl p st).auxNames,
      v.mentionsConst n = false := by
    intro v hv n hn
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hv
    obtain ⟨ty, rfl⟩ := hCD.pIdx k v hk
    exact C.auxFree_of_resolve (hPres _ hv) n hn
  have hidxFree : ∀ e ∈ idxF (b.ownOffset mm + j), ∀ n ∈ (ConLeche.restoreTbl p st).auxNames,
      e.mentionsConst n = false := by
    intro e he
    have hr := hO.residRes
    rw [← hCD.idxEq] at hr
    exact C.auxFree_of_resolve₀ (hr e he)
  have hTne : ∀ n ∈ (ConLeche.restoreTbl p st).auxNames,
      (Expr.const (fms.getD mm default).cvTa.name (b.lps.map .param)).mentionsConst n = false := by
    intro n hn
    have := C.memberNotAux hmm n hn
    simp only [Expr.mentionsConst, beq_eq_false_iff_ne, ne_eq]
    exact this
  have hxrest : ∀ n ∈ (ConLeche.restoreTbl p st).auxNames,
      (xrestF (b.ownOffset mm + j)).mentionsConst n = false := by
    intro n hn
    rw [hxrEq]
    refine mentionsConst_mkAppN_false _ _ (hTne n hn) ?_
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hPfree a ha n hn
    · exact hidxFree a ha n hn
  have hxLen : (xFvsF (b.ownOffset mm + j)).length = cA.2 := hCD.xLen
  -- the fields' kinds
  have hkinds : ∀ (i : Nat) (x : Expr), (xFvsF (b.ownOffset mm + j))[i]? = some x →
      kindAt (mutKsOf kinds (b.ownOffset mm + j)) i = .ordinary ∨
      kindAt (mutKsOf kinds (b.ownOffset mm + j)) i = .recursive ∨
      kindAt (mutKsOf kinds (b.ownOffset mm + j)) i = .reflexive := by
    intro i x hx
    exact hO.kinds i (by rw [← hxLen]; exact (List.getElem?_eq_some_iff.mp hx).1)
  -- an auxiliary-mentioning field is recursive or reflexive: nothing later depends on it
  have hnodep : ∀ (i : Nat) (x : Expr), (xFvsF (b.ownOffset mm + j))[i]? = some x →
      (∃ n ∈ (ConLeche.restoreTbl p st).auxNames, x.fvarTypeD.mentionsConst n = true) →
      (∀ y ∈ (xFvsF (b.ownOffset mm + j)).drop (i + 1), y.fvarTypeD.mentionsFvar (b.nP + i) = false) ∧
        (xrestF (b.ownOffset mm + j)).mentionsFvar (b.nP + i) = false := by
    intro i x hx ⟨n, hn, hmen⟩
    rcases hkinds i x hx with hk | hk | hk
    · exact absurd hmen (by rw [C.auxFree_of_resolve₀ (hO.ord i x hx hk) n hn]; decide)
    · obtain ⟨-, -, -, -, h1, h2⟩ := hO.recF i x hx hk
      exact ⟨h1, h2⟩
    · obtain ⟨-, -, -, -, -, -, -, -, -, h1, h2⟩ := hO.reflF i x hx hk
      exact ⟨h1, h2⟩
  obtain ⟨crestR, xFvsRc, hopPR, hopXR, hlenXR, hfields⟩ :=
    ConLeche.restoreNested_opened (ConLeche.restoreTbl_keysInAux p st) hRnP C.hpinB hopP hopX hres
      hxrest hnodep
  -- the residual at `stripPis`
  obtain ⟨cbs, es, hstripA, hlenE⟩ := hCD.resid
  rw [hmemJ] at hstripA hlenE
  have hresid : ∃ (cbsA cbs' : List (Expr × BinderMeta)) (es : List Expr),
      cA.1.type.stripPis (b.nP + cA.2)
        = some (cbsA, Expr.mkAppN (.const (fms.getD mm default).cvTa.name (b.lps.map .param))
            (ConLeche.structPsAt cA.2 b.nP ++ es)) ∧
      c.1.type.stripPis (b.nP + cA.2)
        = some (cbs', Expr.mkAppN (.const (fms.getD mm default).cvTa.name (b.lps.map .param))
            (ConLeche.structPsAt cA.2 b.nP ++ es)) ∧
      cbs'.map (·.2) = cbsA.map (·.2) ∧
      es.length = (fms.getD mm default).nIdx := by
    have hopAll := openPisAtFvars_add b.nP hopP (by rw [Nat.zero_add]; exact hopX)
    have hinst := Verify.openPisAtFvars_instSeq (b.nP + cA.2) hopAll hstripA
    obtain ⟨cbs', hstripR, hmeta⟩ := ConLeche.rk_restoreNested_stripPis hRnP hstripA hres (by
      intro n hn
      refine ConLeche.mentionsConst_instSeq_false (fvsPF (b.ownOffset mm + j) ++ xFvsF (b.ownOffset mm + j))
        (b.nP + cA.2 - 1) ?_
      rw [← hinst]
      exact hxrest n hn)
    exact ⟨cbs, cbs', es, hstripA, hstripR, hmeta, hlenE⟩
  refine ⟨cA, crestR, xFvsRc, hJ, hnF, hnP1, hlpsC, hnameC, hfd, hjl, hmemJ, hopPR, hopXR,
    by rw [hlenXR, hxLen], hresid, ?_⟩
  -- the fields
  intro i x hx
  obtain ⟨ty', hxR, ha, hb, hc'⟩ := hfields i x hx
  refine ⟨ty', hxR, ?_⟩
  have hil : i < cA.2 := by rw [← hxLen]; exact (List.getElem?_eq_some_iff.mp hx).1
  have htgtLt : tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i < fms.length :=
    (C.h.ksJ _ _ hJ).2.2 i
  have hlenFms : fms.length = p.k + st.pins.length := by rw [C.h.lenFms, C.hbk]
  have hnameT := C.memberName htgtLt
  -- the target, when a pin
  have hpinOf : ¬ tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i < p.k →
      ∃ (q : Nat) (qn : NestedPin), st.pins[q]? = some qn ∧
        tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i = p.k + q ∧
        mutualNameOf b.members3 (tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i) = qn.aux := by
    intro hge
    have hql : tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i - p.k < st.pins.length := by omega
    obtain ⟨qn, hq⟩ : ∃ qn, st.pins[tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i - p.k]? = some qn :=
      ⟨_, List.getElem?_eq_getElem hql⟩
    refine ⟨_, qn, hq, by omega, ?_⟩
    rw [hnameT, ← (C.copyName hq).2, show p.k + (tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i - p.k)
      = tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i from by omega]
  rcases hkinds i x hx with hk | hk | hk
  · -- an ordinary field: auxiliary-free
    exact Or.inl ⟨Or.inl hk, ha (C.auxFree_of_resolve₀ (hO.ord i x hx hk))⟩
  · -- a recursive field
    have hshape := C.recShape hJ hx hk
    obtain ⟨-, -, -, hres', -, -⟩ := hO.recF i x hx hk
    rcases Nat.lt_or_ge (tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i) p.k with hlt | hge
    · -- a member target: auxiliary-free
      refine Or.inl ⟨Or.inr hlt, ha ?_⟩
      intro n hn
      rw [hshape]
      refine mentionsConst_mkAppN_false _ _ ?_ ?_
      · rw [hnameT]
        simp only [Expr.mentionsConst, beq_eq_false_iff_ne, ne_eq]
        exact C.memberNotAux hlt n hn
      · intro a ha'
        rcases List.mem_append.mp ha' with ha' | ha'
        · exact hPfree a ha' n hn
        · exact C.auxFree_of_resolve₀ (hres' a ha') n hn
    · -- a pin target: the pin's fire
      obtain ⟨q, qn, hq, htq, hnq⟩ := hpinOf (Nat.not_lt.mpr hge)
      rw [hnq] at hshape
      obtain ⟨hpl, hrl⟩ := C.pinLookup hq
      refine Or.inr (Or.inl ⟨q, qn, hq, htq, hk, hshape, ?_⟩)
      exact hb qn.aux (b.lps.map .param) _ _ hshape hpl hrl
  · -- a reflexive field
    obtain ⟨afvs, body, hopA, -, hares, hfn, htake, -, hres', -, -⟩ := hO.reflF i x hx hk
    have hbody : body = Expr.mkAppN
        (.const (mutualNameOf b.members3 (tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i)) (b.lps.map .param))
        (fvsPF (b.ownOffset mm + j) ++ body.getAppArgs.drop b.nP) := by
      have := Expr.mkAppN_getApp body
      rw [hfn, ← List.take_append_drop b.nP body.getAppArgs, htake] at this
      exact this.symm
    rw [hbody] at hopA
    obtain ⟨tbs, is₀, hstrip, his⟩ := ConLeche.os_openPisAtFvars_constSpine_stripPis hopA (by
      intro v hv
      obtain ⟨k, hk'⟩ := List.getElem?_of_mem hv
      obtain ⟨ty, rfl⟩ := hCD.pIdx k v hk'
      have hkl : k < (fvsPF (b.ownOffset mm + j)).length := (List.getElem?_eq_some_iff.mp hk').1
      exact ⟨k, ty, rfl, by rw [hlenP] at hkl; omega⟩)
    have hL : (x.fvarTypeD.piBinders).1.length = tbs.length := (Expr.stripPis_length _ hstrip).symm
    have hxty : x.fvarTypeD = ConLeche.mkPisB tbs _ := ConLeche.stripPis_mkPisB _ hstrip
    -- the telescope's binders mention no auxiliary name
    have htbs : ∀ bb ∈ tbs, ∀ n ∈ (ConLeche.restoreTbl p st).auxNames, bb.1.mentionsConst n = false := by
      intro bb hbb n hn
      obtain ⟨k, hk'⟩ := List.getElem?_of_mem hbb
      cases hm : bb.1.mentionsConst n with
      | false => rfl
      | true =>
        exfalso
        have hopA' := hopA
        rw [hL, hxty] at hopA'
        obtain ⟨a, ha', han⟩ := openPisAtFvars_binder_mentionsConst tbs _ _ afvs _ hopA' k bb hk' hm
        rw [C.auxFree_of_resolve₀ (hares a ha') n hn] at han
        exact Bool.false_ne_true han
    have hisFree : ∀ e ∈ is₀, ∀ n ∈ (ConLeche.restoreTbl p st).auxNames, e.mentionsConst n = false := by
      intro e he n hn
      refine ConLeche.mentionsConst_instSeq_false afvs ((x.fvarTypeD.piBinders).1.length - 1) ?_
      have hmem : Expr.instSeq afvs ((x.fvarTypeD.piBinders).1.length - 1) e ∈ body.getAppArgs.drop b.nP := by
        rw [his]; exact List.mem_map_of_mem he
      exact C.auxFree_of_resolve₀ (hres' _ hmem) n hn
    rcases Nat.lt_or_ge (tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i) p.k with hlt | hge
    · -- a member target: auxiliary-free
      refine Or.inl ⟨Or.inr hlt, ha ?_⟩
      intro n hn
      rw [hxty]
      refine mentionsConst_mkPisB_false _ _ (fun bb hbb => htbs bb hbb n hn) ?_
      refine mentionsConst_mkAppN_false _ _ ?_ ?_
      · rw [hnameT]
        simp only [Expr.mentionsConst, beq_eq_false_iff_ne, ne_eq]
        exact C.memberNotAux hlt n hn
      · intro a ha'
        rcases List.mem_append.mp ha' with ha' | ha'
        · exact hPfree a ha' n hn
        · exact hisFree a ha' n hn
    · -- a pin target: the reflexive fire
      obtain ⟨q, qn, hq, htq, hnq⟩ := hpinOf (Nat.not_lt.mpr hge)
      rw [hnq] at hopA hstrip
      obtain ⟨hpl, hrl⟩ := C.pinLookup hq
      refine Or.inr (Or.inr ⟨q, qn, tbs, is₀, afvs, _, hq, htq, hk, hopA, hstrip, his, ?_⟩)
      exact hc' _ tbs qn.aux (b.lps.map .param) _ is₀ hstrip htbs hpl hrl

/-- **THE RESTORED ABSTRACT FIELD DOMAIN AT A PIN** (task #315 PINF):
`restoredOpened` states the restore's per-field effect on the OPENED
domains, which is what the reading law wants; K.60's guard reads the
CLOSED ones — a container's stored constructor stripped, with bound
variables where the parameters and the earlier fields stand — and the
two are related only in the direction that loses the fact (an opener's
annotation can carry a mention the abstract domain does not have).

So the abstract side is proved here, directly off the walk:
`restoreNested` strips the parameter binders itself
(`restoreNested_pis`) and `restoreWalk_stripPis_pin` reads the field
telescope at the depth the field stands under. -/
theorem ReadCtx.restoredAbsPin {mm j : Nat} {c : ConstantVal × Nat × Nat}
    {cA : ConstantVal × Nat} (hmm : mm < p.k) (hc : (ctorsR.getD mm [])[j]? = some c)
    (hJ : ctorsA[b.ownOffset mm + j]? = some cA)
    {cbsA cbs' : List (Expr × BinderMeta)} {rA r' : Expr}
    (hstripA : cA.1.type.stripPis (b.nP + cA.2) = some (cbsA, rA))
    (hstripR : c.1.type.stripPis (b.nP + cA.2) = some (cbs', r'))
    {l : Nat} {domA dom' : Expr × BinderMeta}
    (hdA : cbsA[b.nP + l]? = some domA) (hdR : cbs'[b.nP + l]? = some dom')
    {n : Name} {us : List Level} {pin : Expr}
    (hfn : domA.1.getAppFn = .const n us) (hlenA : b.nP ≤ domA.1.getAppArgs.length)
    (hp : (ConLeche.restoreTbl p st).pins.lookup n = some pin)
    (hrecm : (ConLeche.restoreTbl p st).recMap.lookup n = none) :
    dom'.1 = Expr.mkAppN (pin.liftLooseBVars l 0) (domA.1.getAppArgs.drop b.nP) := by
  have hres : ConLeche.restoreNested (ConLeche.restoreTbl p st) cA.1.type = .ok c.1.type := by
    obtain ⟨-, cA', hJ', -, -, hres₀, -, -⟩ := C.ctorFacts hmm hc
    obtain rfl : cA' = cA := Option.some.inj (hJ'.symm.trans hJ)
    exact hres₀
  have hRnP : (ConLeche.restoreTbl p st).nP = b.nP := by
    rw [ConLeche.restoreTbl_nP, C.hnP]
  obtain ⟨mid, hs1, hs2⟩ := ConLeche.rk_stripPis_split b.nP cA.2 hstripA
  have hclA : cbsA.length = b.nP + cA.2 := Expr.stripPis_length _ hstripA
  have htk : (cbsA.take b.nP).length = b.nP := by rw [List.length_take, hclA]; omega
  have hs : cA.1.type.stripPis (ConLeche.restoreTbl p st).nP = some (cbsA.take b.nP, mid) := by
    rw [hRnP]; exact hs1
  have hpi : 0 < (ConLeche.restoreTbl p st).nP →
      ∃ ty bb bm, cA.1.type = Expr.forallE ty bb bm := by
    intro hlt
    rw [hRnP] at hlt
    obtain ⟨n₀, hn₀⟩ : ∃ n₀, b.nP = n₀ + 1 := ⟨b.nP - 1, by omega⟩
    rw [hn₀] at hs1
    cases hty : cA.1.type with
    | forallE ty bb bm => exact ⟨ty, bb, bm, rfl⟩
    | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _
    | lam _ _ _ | letE _ _ _ | lit _ | proj _ _ _ => rw [hty] at hs1; exact nomatch hs1
  obtain ⟨body', hw, htyR⟩ := ConLeche.restoreNested_pis hs hpi hres
  rw [ConLeche.mkPisB_eq_foldr] at htyR
  obtain ⟨mid', hr1, hr2⟩ := ConLeche.rk_stripPis_split b.nP cA.2 hstripR
  have hmk : c.1.type.stripPis b.nP = some (cbsA.take b.nP, body') := by
    rw [htyR]
    have h := ConLeche.rk_mkPisB_stripPis (cbsA.take b.nP) body'
    rw [htk] at h; exact h
  obtain rfl : mid' = body' := (Prod.mk.inj (Option.some.inj (hr1.symm.trans hmk))).2
  have hA' : (cbsA.drop b.nP)[l]? = some domA := by rw [List.getElem?_drop]; exact hdA
  have hR' : (cbs'.drop b.nP)[l]? = some dom' := by rw [List.getElem?_drop]; exact hdR
  have hkey := ConLeche.restoreWalk_stripPis_pin (ConLeche.restoreTbl_keysInAux p st)
    hw hs2 hr2 hA' hR' hfn (by rw [hRnP]; exact hlenA) hp hrecm
  rw [Nat.zero_add, hRnP] at hkey
  exact hkey

/-- **The restored constructor's syntactic record** (`restoredOpened`'s
conjuncts, named). -/
structure RestoredCtor (mm j : Nat) (c : ConstantVal × Nat × Nat) (cA : ConstantVal × Nat)
    (crestR : Expr) (xFvsRc : List Expr) : Prop where
  hmm : mm < p.k
  hJ : ctorsA[b.ownOffset mm + j]? = some cA
  hnF : c.2.2 = cA.2
  hnP1 : c.2.1 = b.nP
  hlpsC : c.1.levelParams = p.lps
  hnameC : c.1.name = cA.1.name
  hfd : ConLeche.FrontDoorFacts μ F ENV₁ c.1 c.1
  hjl : j < (b.ownCtors mm).length
  hmemJ : mutMemF b (b.ownOffset mm + j) = mm
  hopP : openPisAtFvars b.nP c.1.type 0 = some (fvsPF (b.ownOffset mm + j), crestR)
  hopX : openPisAtFvars cA.2 crestR b.nP = some (xFvsRc, xrestF (b.ownOffset mm + j))
  hlenX : xFvsRc.length = cA.2
  resid : ∃ (cbsA cbs' : List (Expr × BinderMeta)) (es : List Expr),
    cA.1.type.stripPis (b.nP + cA.2)
      = some (cbsA, Expr.mkAppN (.const (fms.getD mm default).cvTa.name (b.lps.map .param))
          (ConLeche.structPsAt cA.2 b.nP ++ es)) ∧
    c.1.type.stripPis (b.nP + cA.2)
      = some (cbs', Expr.mkAppN (.const (fms.getD mm default).cvTa.name (b.lps.map .param))
          (ConLeche.structPsAt cA.2 b.nP ++ es)) ∧
    cbs'.map (·.2) = cbsA.map (·.2) ∧
    es.length = (fms.getD mm default).nIdx
  fields : ∀ (i : Nat) (x : Expr), (xFvsF (b.ownOffset mm + j))[i]? = some x →
    ∃ ty', xFvsRc[i]? = some (.fvar (b.nP + i) ty') ∧
      RestoredField p st b (mutKsOf kinds (b.ownOffset mm + j)) (fvsPF (b.ownOffset mm + j)) i x ty'
  /-- **the ABSTRACT field domain at a pin** (task #315 PINF):
  `fields` is on the OPENED domains, which is the reading law's side;
  K.60's guard reads the closed ones and the transport between them
  runs only abstract ⟹ opened, so the pin case is carried here in the
  form `stripPis` leaves (`ReadCtx.restoredAbsPin`). -/
  absPin : ∀ (cbsA cbs' : List (Expr × BinderMeta)) (rA r' : Expr) (l : Nat)
      (domA dom' : Expr × BinderMeta) (n : Name) (us : List Level) (pin : Expr),
    cA.1.type.stripPis (b.nP + cA.2) = some (cbsA, rA) →
    c.1.type.stripPis (b.nP + cA.2) = some (cbs', r') →
    cbsA[b.nP + l]? = some domA → cbs'[b.nP + l]? = some dom' →
    domA.1.getAppFn = .const n us → b.nP ≤ domA.1.getAppArgs.length →
    (ConLeche.restoreTbl p st).pins.lookup n = some pin →
    (ConLeche.restoreTbl p st).recMap.lookup n = none →
    dom'.1 = Expr.mkAppN (pin.liftLooseBVars l 0) (domA.1.getAppArgs.drop b.nP)

theorem ReadCtx.restoredCtor {mm j : Nat} {c : ConstantVal × Nat × Nat} (hmm : mm < p.k)
    (hc : (ctorsR.getD mm [])[j]? = some c) :
    ∃ (cA : ConstantVal × Nat) (crestR : Expr) (xFvsRc : List Expr),
      RestoredCtor (μ := μ) (env := env) (F := F) (p := p) (b := b) (fms := fms)
        (ctorsA := ctorsA) (kinds := kinds) (fvsPF := fvsPF) (xFvsF := xFvsF) (xrestF := xrestF)
        (st := st) mm j c cA crestR xFvsRc := by
  obtain ⟨cA, crestR, xFvsRc, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ :=
    C.restoredOpened hmm hc
  exact ⟨cA, crestR, xFvsRc, ⟨hmm, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    fun _ _ _ _ _ _ _ _ _ _ hA hR hdA hdR hfn hlen hp hrec =>
      C.restoredAbsPin hmm hc h1 hA hR hdA hdR hfn hlen hp hrec⟩⟩

/-! ### The binder bits, shared -/

/-- **The two domain lists carry the same bits**: the restore keeps
every binder meta, and a reading's `.pi` entries are exactly the
binders' bits (`stripPisAV_denoteMeta_mkPisB`) — so at every position
the restored entry's `.1` is `0` and its `.2.1` is the auxiliary
entry's. -/
theorem ReadCtx.bitsEq {mm j : Nat} {c : ConstantVal × Nat × Nat} {cA : ConstantVal × Nat}
    {crestR : Expr} {xFvsRc : List Expr}
    (RC : RestoredCtor (μ := μ) (env := env) (F := F) (p := p) (b := b) (fms := fms)
      (ctorsA := ctorsA) (kinds := kinds) (fvsPF := fvsPF) (xFvsF := xFvsF) (xrestF := xrestF)
      (st := st) mm j c cA crestR xFvsRc)
    {dsRc : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (RS : ReadSpec mp₁' (fms.getD mm default).cvTa.name b.nP cA.2 c.1 (esF (b.ownOffset mm + j)) dsRc)
    (ψ : Name → Nat) (k : Nat) :
    ((dsRc ψ).getD k default).1 = 0 ∧ ((dsF (b.ownOffset mm + j) ψ).getD k default).1 = 0 ∧
    ((dsRc ψ).getD k default).2.1 = ((dsF (b.ownOffset mm + j) ψ).getD k default).2.1 := by
  obtain ⟨cbsA, cbs', es, hstripA, hstripR, hmeta, -⟩ := RC.resid
  have hCD := C.h.CD _ _ RC.hJ
  rw [RC.hmemJ] at hCD
  have hlenA : (dsF (b.ownOffset mm + j) ψ).length = b.nP + cA.2 := hCD.len ψ
  have hlenR : (dsRc ψ).length = b.nP + cA.2 := RS.len ψ
  have hcA : cbsA.length = b.nP + cA.2 := Expr.stripPis_length _ hstripA
  have hcR : cbs'.length = b.nP + cA.2 := Expr.stripPis_length _ hstripR
  rcases Nat.lt_or_ge k (b.nP + cA.2) with hk | hk
  · -- a binder position: both readings peel the binders' bits
    have htyA := ConLeche.stripPis_mkPisB _ hstripA
    have htyR := ConLeche.stripPis_mkPisB _ hstripR
    have hreadA := hCD.read ψ
    have hreadR := RS.read ψ
    rw [htyA] at hreadA
    rw [htyR] at hreadR
    have hstA := stripPisAV_mkPisAV (dsF (b.ownOffset mm + j) ψ)
      (ctorBodyAVI mp₁.base2 (fms.getD mm default).cvTa.name b.nP cA.2 ψ (esF (b.ownOffset mm + j) ψ))
    have hstR := stripPisAV_mkPisAV (dsRc ψ)
      (ctorBodyAVI mp₁'.base2 (fms.getD mm default).cvTa.name b.nP cA.2 ψ (esF (b.ownOffset mm + j) ψ))
    rw [hlenA, ← hcA] at hstA
    rw [hlenR, ← hcR] at hstR
    obtain ⟨pA, hpA⟩ : ∃ pA, (dsF (b.ownOffset mm + j) ψ)[k]? = some pA :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨pR, hpR⟩ : ∃ pR, (dsRc ψ)[k]? = some pR := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨bmA, hbmA⟩ : ∃ bmA, cbsA[k]? = some bmA := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨bmR, hbmR⟩ : ∃ bmR, cbs'[k]? = some bmR := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨hA1, hA2⟩ := stripPisAV_denoteMeta_mkPisB cbsA hreadA hstA k pA bmA hpA hbmA
    obtain ⟨hR1, hR2⟩ := stripPisAV_denoteMeta_mkPisB cbs' hreadR hstR k pR bmR hpR hbmR
    have hm : bmR.2 = bmA.2 := by
      have h1 := congrArg (fun l => l[k]?) hmeta
      simp only [List.getElem?_map, hbmA, hbmR, Option.map_some, Option.some.injEq] at h1
      exact h1
    simp only [List.getD_eq_getElem?_getD, hpA, hpR, Option.getD_some]
    exact ⟨hR1, hA1, by rw [hR2, hA2, hm]⟩
  · -- beyond the telescope: the defaults
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega),
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    exact ⟨rfl, rfl, rfl⟩

/-! ### The transfer from the scratch model to the prefix model -/

/-- The members' names are pairwise distinct. -/
theorem ReadCtx.hndNames : (fms.map (·.cvTa.name)).Nodup := by
  rw [C.h.names]
  have h0 := C.hnd
  unfold ConLeche.MutualBlock.blockNames at h0
  exact (List.nodup_append.mp (List.nodup_append.mp h0).1).1

/-- The prefix environment is preserved by the scratch one. -/
theorem ReadCtx.hF : FindPreserved ENV₁ SCR :=
  nt_findPreserved_take p.k (fun f hf => by
      obtain ⟨t, ht⟩ := List.getElem?_of_mem hf
      exact C.h.fresh t f ht) C.hndNames

/-- The two carriers agree on the prefix environment's names. -/
theorem ReadCtx.hag : ∀ n : Name, ((ENV₁).find? n).isSome = true →
    mp₁'.base2.acval n = mp₁.base2.acval n := by
  intro n hn
  cases hf : (ENV₁).find? n with
  | none => rw [hf] at hn; exact nomatch hn
  | some ci =>
    rcases nt_consMutualFormers_find?_cases hf with henv | ⟨f, hf', hfn⟩
    · have hne : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f → n ≠ f.cvTa.name := by
        intro t f hft heq
        have := C.h.fresh t f hft
        rw [← heq, henv] at this
        exact nomatch this
      rw [C.hoff' n (fun t f _ hft => hne t f hft), C.h.off n hne]
    · obtain ⟨t, ht⟩ := List.getElem?_of_mem hf'
      have htk : t < p.k := by
        have := (List.getElem?_eq_some_iff.mp ht).1
        rw [List.length_take] at this
        omega
      rw [List.getElem?_take_of_lt htk] at ht
      rw [← hfn, C.hleafM' t f htk ht, C.h.leaf t f ht]

/-- **The transfer**: a term resolving at the prefix environment reads
at the scratch model as at the prefix model. -/
theorem ReadCtx.transfer (ψ : Name → Nat) (d : Nat) (e : Expr) (hres : e.constsResolve ENV₁ = true) :
    denoteMeta mp₁.base2.acval SCR ψ d e = denoteMeta mp₁'.base2.acval ENV₁ ψ d e :=
  nt_denoteMeta_transfer C.hF (nt_findProj?_take p.k) C.hag d e hres

theorem ReadCtx.transferSpine (ψ : Name → Nat) (d : Nat) {as : List Expr} {vs : List AnnotTerm}
    (hres : ∀ a ∈ as, a.constsResolve ENV₁ = true) :
    DenoteMetaSpine mp₁.base2.acval SCR ψ d as vs ↔ DenoteMetaSpine mp₁'.base2.acval ENV₁ ψ d as vs :=
  nt_denoteMetaSpine_transfer C.hF (nt_findProj?_take p.k) C.hag d hres

/-- The auxiliary constructor's index arguments read at the prefix model. -/
theorem ReadCtx.idxRead {J : Nat} {cA : ConstantVal × Nat} (hJ : ctorsA[J]? = some cA) (ψ : Name → Nat) :
    DenoteMetaSpine mp₁'.base2.acval ENV₁ ψ (b.nP + cA.2) (idxF J) (esF J ψ) := by
  have hCD := C.h.CD J cA hJ
  refine (C.transferSpine ψ _ ?_).mp (hCD.idxRead ψ)
  intro e he
  have hr := hCD.opened.residRes
  rw [← hCD.idxEq] at hr
  exact constsResolve_consMutualFormers (hr e he)

/-! ### The pin's reading at the prefix model -/

/-- **A pin, re-opened at parameter openers, reads as the container's
leaf at the lifted components** at every depth past the parameters:
the pins' facts (`pinRec`, `pinψ`, `pinDs`), the group's stored
container and `pinsClosed`, through `nt_denoteMeta_restoredPin`. -/
theorem ReadCtx.pinRead {q : Nat} {qn : NestedPin} (hq : st.pins[q]? = some qn)
    {fvsP : List Expr} (hlenP : fvsP.length = b.nP)
    (hidx : ∀ k, k < b.nP → ∃ ty, fvsP[k]? = some (.fvar k ty)) (ψ : Name → Nat) (i : Nat) :
    denoteMeta mp₁'.base2.acval ENV₁ ψ (b.nP + i)
        (Expr.instSeq fvsP (b.nP - 1) (Expr.abstractRange qn.pin 0 p.nP 0))
      = some (AnnotTerm.mkAppN (mp₁'.base2.acval ((D).pinAt q).J (((D).pinAt q).ψJ ψ))
          ((((D).pinAt q).Ds ψ).map (·.liftN i 0))) := by
  have hql : q < pinsS.length := by
    rw [C.PF.pinsLen]; exact (List.getElem?_eq_some_iff.mp hq).1
  obtain ⟨hJ, hpin⟩ := C.PF.pinRec q qn hq
  obtain ⟨q₀, kJ, i', dJ, hqe, hi', G⟩ := C.PF.groups dsR xFvsR q hql
  obtain ⟨cv, caps, hf⟩ := G.found hi'
  rw [← hqe] at hf
  obtain ⟨hlen, hψ⟩ := C.PF.pinψ q hql cv caps hf
  have hfv : (Expr.abstractRange qn.pin 0 p.nP 0).hasFvar = false := by
    have := List.all_eq_true.mp C.hclosed qn (List.mem_of_getElem? hq)
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
    exact this.1
  have hnP := C.hnP
  have hf' : (ENV₁).find? (pinsS.getD q default).J = some (.indInfo cv caps) := hf
  rw [hpin] at hfv ⊢
  rw [← hnP] at hfv ⊢
  show denoteMeta mp₁'.base2.acval ENV₁ ψ (b.nP + i)
      (Expr.instSeq fvsP (b.nP - 1) (Expr.abstractRange
        (Expr.mkAppN (.const qn.container (pinsS.getD q default).lvls)
          (pinsS.getD q default).DsE) 0 b.nP 0))
    = some (AnnotTerm.mkAppN (mp₁'.base2.acval (pinsS.getD q default).J ((pinsS.getD q default).ψJ ψ))
        (((pinsS.getD q default).Ds ψ).map (·.liftN i 0)))
  rw [hψ ψ, hJ]
  rw [hJ] at hf'
  exact nt_denoteMeta_restoredPin mp₁'.base2 hlenP hidx hfv hf' hlen (C.PF.pinDs q hql ψ)

/-! ### The entries' readings -/

section Entries

variable {mm j : Nat} {c : ConstantVal × Nat × Nat} {cA : ConstantVal × Nat}
  {crestR : Expr} {xFvsRc : List Expr}
  (RC : RestoredCtor (μ := μ) (env := env) (F := F) (p := p) (b := b) (fms := fms)
    (ctorsA := ctorsA) (kinds := kinds) (fvsPF := fvsPF) (xFvsF := xFvsF) (xrestF := xrestF)
    (st := st) mm j c cA crestR xFvsRc)
  {dsRc : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  (RS : ReadSpec mp₁' (fms.getD mm default).cvTa.name b.nP cA.2 c.1 (esF (b.ownOffset mm + j)) dsRc)
include RC RS

omit C in
/-- The restored constructor's opened record at the prefix model. -/
theorem ReadCtx.openedR (ψ : Name → Nat) :
    Opened mp₁'.base2 ψ (b.nP + cA.2) c.1.type (fvsPF (b.ownOffset mm + j) ++ xFvsRc)
      (xrestF (b.ownOffset mm + j)) (((dsRc ψ).map (·.2.2)).reverse)
      (ctorBodyAVI mp₁'.base2 (fms.getD mm default).cvTa.name b.nP cA.2 ψ (esF (b.ownOffset mm + j) ψ)) :=
  opened_of_peel (openPisAtFvars_add b.nP RC.hopP (by rw [Nat.zero_add]; exact RC.hopX))
    RC.hfd.noFvar RC.hfd.bounded (RS.read ψ) (RS.len ψ) (RS.okTy ψ)

/-- A restored opener's annotation reads to the restored entry. -/
theorem ReadCtx.entryR (ψ : Name → Nat) {k : Nat} {x : Expr}
    (hx : (fvsPF (b.ownOffset mm + j) ++ xFvsRc)[k]? = some x) :
    denoteMeta mp₁'.base2.acval ENV₁ ψ k x.fvarTypeD = some ((dsRc ψ).getD k default).2.2 := by
  have hO := ReadCtx.openedR RC RS ψ
  have hk : k < b.nP + cA.2 := by
    have := (List.getElem?_eq_some_iff.mp hx).1
    rw [List.length_append, (C.h.CD _ _ RC.hJ).pLen, RC.hlenX] at this
    exact this
  have hlen : (dsRc ψ).length = b.nP + cA.2 := RS.len ψ
  obtain ⟨pk, hpk⟩ : ∃ pk, (dsRc ψ)[k]? = some pk := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  rw [hO.doms k x hx, getD_reverse_of_peel hlen hk hpk, List.getD_eq_getElem?_getD, hpk]
  rfl

omit RS in
/-- The auxiliary constructor's opened record at the scratch model. -/
theorem ReadCtx.openedA (ψ : Name → Nat) :
    Opened mp₁.base2 ψ (b.nP + cA.2) cA.1.type (fvsPF (b.ownOffset mm + j) ++ xFvsF (b.ownOffset mm + j))
      (xrestF (b.ownOffset mm + j)) (((dsF (b.ownOffset mm + j) ψ).map (·.2.2)).reverse)
      (ctorBodyAVI mp₁.base2 (fms.getD mm default).cvTa.name b.nP cA.2 ψ (esF (b.ownOffset mm + j) ψ)) := by
  obtain ⟨crest, hopP, hopX, -, -, -, hcl, hb⟩ := C.auxShape RC.hJ
  have hCD := C.h.CD _ _ RC.hJ
  rw [RC.hmemJ] at hCD
  exact opened_of_peel (openPisAtFvars_add b.nP hopP (by rw [Nat.zero_add]; exact hopX)) hcl hb
    (hCD.read ψ) (hCD.len ψ) (hCD.okTy ψ)

omit RS in
/-- An auxiliary opener's annotation reads to the auxiliary entry. -/
theorem ReadCtx.entryA (ψ : Name → Nat) {k : Nat} {x : Expr}
    (hx : (fvsPF (b.ownOffset mm + j) ++ xFvsF (b.ownOffset mm + j))[k]? = some x) :
    denoteMeta mp₁.base2.acval SCR ψ k x.fvarTypeD
      = some ((dsF (b.ownOffset mm + j) ψ).getD k default).2.2 := by
  have hO := C.openedA RC ψ
  have hCD := C.h.CD _ _ RC.hJ
  have hk : k < b.nP + cA.2 := by
    have := (List.getElem?_eq_some_iff.mp hx).1
    rw [List.length_append, hCD.pLen, hCD.xLen] at this
    exact this
  have hlen : (dsF (b.ownOffset mm + j) ψ).length = b.nP + cA.2 := hCD.len ψ
  obtain ⟨pk, hpk⟩ : ∃ pk, (dsF (b.ownOffset mm + j) ψ)[k]? = some pk :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  rw [hO.doms k x hx, getD_reverse_of_peel hlen hk hpk, List.getD_eq_getElem?_getD, hpk]
  rfl

omit [SetTheory V] C RS in
/-- The restored openers' annotations resolve at the prefix environment. -/
theorem ReadCtx.openersResolve :
    ∀ x ∈ fvsPF (b.ownOffset mm + j) ++ xFvsRc, x.fvarTypeD.constsResolve ENV₁ = true := by
  obtain ⟨h1, hcrest⟩ := ConLeche.rk_openPisAtFvars_constsResolve b.nP RC.hopP RC.hfd.resolve
  obtain ⟨h2, -⟩ := ConLeche.rk_openPisAtFvars_constsResolve cA.2 RC.hopX hcrest
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact h1 x hx
  · exact h2 x hx

/-- **An auxiliary-free position reads alike**: an opener whose
annotation is the auxiliary opener's reads, at the prefix model, to the
auxiliary entry. -/
theorem ReadCtx.entryEq (ψ : Name → Nat) {k : Nat} {x x' : Expr}
    (hx : (fvsPF (b.ownOffset mm + j) ++ xFvsF (b.ownOffset mm + j))[k]? = some x)
    (hx' : (fvsPF (b.ownOffset mm + j) ++ xFvsRc)[k]? = some x')
    (heq : x'.fvarTypeD = x.fvarTypeD) :
    ((dsRc ψ).getD k default).2.2 = ((dsF (b.ownOffset mm + j) ψ).getD k default).2.2 := by
  have hR := C.entryR RC RS ψ hx'
  have hA := C.entryA RC ψ hx
  rw [← heq, C.transfer ψ k _ (ReadCtx.openersResolve RC x' (List.mem_of_getElem? hx'))] at hA
  exact Option.some.inj (hR.symm.trans hA)

/-- A parameter position reads alike. -/
theorem ReadCtx.paramEq (ψ : Name → Nat) {k : Nat} (hk : k < b.nP) :
    ((dsRc ψ).getD k default).2.2 = ((dsF (b.ownOffset mm + j) ψ).getD k default).2.2 := by
  have hCD := C.h.CD _ _ RC.hJ
  have hkl : k < (fvsPF (b.ownOffset mm + j)).length := by rw [hCD.pLen]; exact hk
  obtain ⟨x, hx⟩ : ∃ x, (fvsPF (b.ownOffset mm + j))[k]? = some x := ⟨_, List.getElem?_eq_getElem hkl⟩
  exact C.entryEq RC RS ψ (by rw [List.getElem?_append_left hkl]; exact hx)
    (by rw [List.getElem?_append_left hkl]; exact hx) rfl

/-- A field position with the auxiliary domain reads alike. -/
theorem ReadCtx.fieldEqA (ψ : Name → Nat) {i : Nat} {x ty' : Expr}
    (hx : (xFvsF (b.ownOffset mm + j))[i]? = some x)
    (hx' : xFvsRc[i]? = some (.fvar (b.nP + i) ty')) (heq : ty' = x.fvarTypeD) :
    ((dsRc ψ).getD (b.nP + i) default).2.2 = ((dsF (b.ownOffset mm + j) ψ).getD (b.nP + i) default).2.2 := by
  have hCD := C.h.CD _ _ RC.hJ
  refine C.entryEq RC RS ψ (x := x) (x' := .fvar (b.nP + i) ty') ?_ ?_ heq
  · rw [List.getElem?_append_right (by rw [hCD.pLen]; exact Nat.le_add_right _ _), hCD.pLen,
      Nat.add_sub_cancel_left]
    exact hx
  · rw [List.getElem?_append_right (by rw [hCD.pLen]; exact Nat.le_add_right _ _), hCD.pLen,
      Nat.add_sub_cancel_left]
    exact hx'

/-- **A finitary nested field's entry**: the container's leaf at the
pin's lifted components and the auxiliary index readings, which read
the pin's index arguments at the prefix model. -/
theorem ReadCtx.fieldEqB (ψ : Name → Nat) {i q : Nat} {qn : NestedPin} {x ty' : Expr}
    (hx : (xFvsF (b.ownOffset mm + j))[i]? = some x)
    (hx' : xFvsRc[i]? = some (.fvar (b.nP + i) ty'))
    (hq : st.pins[q]? = some qn)
    (hk : kindAt (mutKsOf kinds (b.ownOffset mm + j)) i = .recursive)
    (hty : ty' = Expr.mkAppN (Expr.instSeq (fvsPF (b.ownOffset mm + j)) (b.nP - 1)
      (Expr.abstractRange qn.pin 0 p.nP 0)) (x.fvarTypeD.getAppArgs.drop b.nP)) :
    DenoteMetaSpine mp₁'.base2.acval ENV₁ ψ (b.nP + i) (x.fvarTypeD.getAppArgs.drop b.nP)
      ((eissF (b.ownOffset mm + j) ψ).getD i []) ∧
    ((dsRc ψ).getD (b.nP + i) default).2.2
      = AnnotTerm.mkAppN (mp₁'.base2.acval ((D).pinAt q).J (((D).pinAt q).ψJ ψ))
          ((((D).pinAt q).Ds ψ).map (·.liftN i 0) ++ (eissF (b.ownOffset mm + j) ψ).getD i []) := by
  have hCD := C.h.CD _ _ RC.hJ
  obtain ⟨-, -, -, hres, -, -⟩ := hCD.opened.recF i x hx hk
  have hsp : DenoteMetaSpine mp₁'.base2.acval ENV₁ ψ (b.nP + i) (x.fvarTypeD.getAppArgs.drop b.nP)
      ((eissF (b.ownOffset mm + j) ψ).getD i []) :=
    (C.transferSpine ψ _ (fun a ha => constsResolve_consMutualFormers (hres a ha))).mp
      (hCD.eisRead ψ i x hx hk)
  refine ⟨hsp, ?_⟩
  have hR := C.entryR RC RS ψ (k := b.nP + i) (x := .fvar (b.nP + i) ty') (by
    rw [List.getElem?_append_right (by rw [hCD.pLen]; exact Nat.le_add_right _ _), hCD.pLen,
      Nat.add_sub_cancel_left]
    exact hx')
  have hread : denoteMeta mp₁'.base2.acval ENV₁ ψ (b.nP + i) ty'
      = some (AnnotTerm.mkAppN (mp₁'.base2.acval ((D).pinAt q).J (((D).pinAt q).ψJ ψ))
          ((((D).pinAt q).Ds ψ).map (·.liftN i 0) ++ (eissF (b.ownOffset mm + j) ψ).getD i [])) := by
    rw [hty, ← annotMkAppN_append]
    exact denoteMeta_mkAppN hsp (C.pinRead hq hCD.pLen (C.fvsPIdx RC.hJ) ψ i)
  exact Option.some.inj (hR.symm.trans hread)


/-- The parameter prefixes are equal. -/
theorem ReadCtx.takeEq (ψ : Name → Nat) :
    (dsRc ψ).take b.nP = (dsF (b.ownOffset mm + j) ψ).take b.nP := by
  have hCD := C.h.CD _ _ RC.hJ
  have hlenA : (dsF (b.ownOffset mm + j) ψ).length = b.nP + cA.2 := hCD.len ψ
  have hlenR : (dsRc ψ).length = b.nP + cA.2 := RS.len ψ
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_take, List.getElem?_take]
  split
  · rename_i hk
    obtain ⟨pA, hpA⟩ : ∃ pA, (dsF (b.ownOffset mm + j) ψ)[k]? = some pA :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨pR, hpR⟩ : ∃ pR, (dsRc ψ)[k]? = some pR := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨h1, h2, h3⟩ := C.bitsEq RC RS ψ k
    have h4 := C.paramEq RC RS ψ hk
    simp only [List.getD_eq_getElem?_getD, hpA, hpR, Option.getD_some] at h1 h2 h3 h4
    rw [hpA, hpR]
    exact congrArg some (Prod.ext (h1.trans h2.symm) (Prod.ext h3 h4))
  · rfl

/-- **The restored constructor's data** (`CtorDataI` at the restored
domains, the prefix model): the door's reading and grading, the
auxiliary constructor's index/source facts, the bits shared with the
auxiliary domains, and the sources' bound transported along the
agreement at fitting prefixes. -/
theorem ReadCtx.ctorDataI_of
    (hagree : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((dsF (b.ownOffset mm + j) ψ).take b.nP).map (·.2.2)).reverse ρ →
      ∀ l, l < cA.2 → ∀ fs₁ : List V, fs₁.length = l →
        SpineFit ρ ((((dsF (b.ownOffset mm + j) ψ).drop b.nP).map (·.2.2)).take l) fs₁ →
        SpineFit ρ ((((dsRc ψ).drop b.nP).map (·.2.2)).take l) fs₁ →
        interp V (consList fs₁ ρ) ((dsF (b.ownOffset mm + j) ψ).getD (b.nP + l) default).2.2
          = interp V (consList fs₁ ρ) ((dsRc ψ).getD (b.nP + l) default).2.2) :
    CtorDataI mp₁'.base2 (fms.getD mm default).cvTa.name b.lps c.1 b.nP cA.2
      (fms.getD mm default).nIdx f₀.s (Level.isEquiv f₀.s .zero == some true) b.large
      (idxF (b.ownOffset mm + j)) dsRc (esF (b.ownOffset mm + j)) (srcsF (b.ownOffset mm + j)) := by
  have hCD := C.h.CD _ _ RC.hJ
  rw [RC.hmemJ] at hCD
  have hsEq : ∀ ψ : Name → Nat, (fms.getD mm default).s.eval ψ = f₀.s.eval ψ :=
    C.h.sEq mm _ (C.memberAt mm RC.hmm)
  have hlenA : ∀ ψ, (dsF (b.ownOffset mm + j) ψ).length = b.nP + cA.2 := hCD.len
  have hlenR : ∀ ψ, (dsRc ψ).length = b.nP + cA.2 := RS.len
  obtain ⟨-, cbs', es, -, hstripR, -, hlenE⟩ := RC.resid
  refine ⟨⟨cbs', es, hstripR, hlenE⟩, RS.read, RS.len, hCD.lenE, hCD.idxLen, C.idxRead RC.hJ,
    ?_, RS.okTy, RS.below, hCD.belowE, ?_, hCD.srcLen, hCD.srcBnd, hCD.srcIdx, ?_⟩
  · -- the bits: the auxiliary's, shared
    intro ψ d hd
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hd
    obtain ⟨-, -, h3⟩ := C.bitsEq RC RS ψ k
    have hkl : k < b.nP + cA.2 := by rw [← hlenR ψ]; exact (List.getElem?_eq_some_iff.mp hk).1
    obtain ⟨dA, hdA⟩ : ∃ dA, (dsF (b.ownOffset mm + j) ψ)[k]? = some dA :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlenA]; exact hkl)⟩
    simp only [List.getD_eq_getElem?_getD, hk, hdA, Option.getD_some] at h3
    rw [h3, ← hsEq ψ]
    exact hCD.bits ψ dA (List.mem_of_getElem? hdA)
  · -- level dependence
    intro ψ₁ ψ₂ hφ
    have hφ' : ∀ q ∈ cA.1.levelParams, ψ₁ q = ψ₂ q := by
      rw [RC.hlpsC, ← C.hlps] at hφ
      rw [C.h.lpsC _ _ RC.hJ]; exact hφ
    exact ⟨RS.params ψ₁ ψ₂ hφ, (hCD.params ψ₁ ψ₂ hφ').2⟩
  · -- the sources' bound, transported
    intro hl ψ hw ρ hρ
    rw [C.takeEq RC RS ψ] at hρ
    have hA := hCD.srcProp hl ψ (by rw [hsEq]; exact hw) ρ hρ
    refine fieldsBoundSrc_congr _ _ _ ρ (by
        rw [List.length_map, List.length_drop, List.length_map, List.length_drop, hlenA, hlenR])
      ?_ hA
    intro l hl' fs₁ hl₁ hfA hfR
    rw [List.length_map, List.length_drop, hlenA, Nat.add_sub_cancel_left] at hl'
    rw [fieldsGetD _ _ _ (by rw [hlenA]; omega), fieldsGetD _ _ _ (by rw [hlenR]; omega)]
    exact hagree ψ ρ hρ l hl' fs₁ hl₁ hfA hfR

/-- **The loop's per-constructor input** at the restored data, from the
door, the data at the restored domains, the auxiliary constructor's
term-level facts at the auxiliary domains (the member's leaf being the
same at both models), the agreement at fitting prefixes, and the fold
and chain facts as `mutualCtorsStage` instantiates them. -/
theorem ReadCtx.input_of
    (hagree : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((dsF (b.ownOffset mm + j) ψ).take b.nP).map (·.2.2)).reverse ρ →
      ∀ l, l < cA.2 → ∀ fs₁ : List V, fs₁.length = l →
        SpineFit ρ ((((dsF (b.ownOffset mm + j) ψ).drop b.nP).map (·.2.2)).take l) fs₁ →
        SpineFit ρ ((((dsRc ψ).drop b.nP).map (·.2.2)).take l) fs₁ →
        interp V (consList fs₁ ρ) ((dsF (b.ownOffset mm + j) ψ).getD (b.nP + l) default).2.2
          = interp V (consList fs₁ ρ) ((dsRc ψ).getD (b.nP + l) default).2.2) :
    NestedCtorInput mp₁' F (fms.getD mm default).cvTa.name b.lps b.nP cA.2
      (fms.getD mm default).nIdx j mm f₀.s (Level.isEquiv f₀.s .zero == some true) b.large c.1
      W (fun ψ => f₀.s.eval ψ) (blkIdss b ppsF)
      (fun ψ => (mutFss b.nP ctorsA.length dsF ψ).drop (b.ownOffset mm))
      (fun ψ => (blkEss b ctorsA ppsF W esF ψ).drop (b.ownOffset mm)) (ppsF mm)
      (dsF (b.ownOffset mm + j)) dsRc (esF (b.ownOffset mm + j)) (idxF (b.ownOffset mm + j))
      (srcsF (b.ownOffset mm + j)) := by
  have h := C.h
  have hμ := C.hμ
  have hCD := h.CD _ _ RC.hJ
  rw [RC.hmemJ] at hCD
  have hJl : b.ownOffset mm + j < ctorsA.length := (List.getElem?_eq_some_iff.mp RC.hJ).1
  have hft := C.memberAt mm RC.hmm
  have hsEq : ∀ ψ : Name → Nat, (fms.getD mm default).s.eval ψ = f₀.s.eval ψ := h.sEq mm _ hft
  have hleaf : mp₁'.base2.acval (fms.getD mm default).cvTa.name
      = mp₁.base2.acval (fms.getD mm default).cvTa.name := by
    rw [C.hleafM' mm _ RC.hmm hft, h.leaf mm _ hft]
  have hbody : ∀ (ψ : Name → Nat) (Es : List AnnotTerm),
      ctorBodyAVI mp₁'.base2 (fms.getD mm default).cvTa.name b.nP cA.2 ψ Es
        = ctorBodyAVI mp₁.base2 (fms.getD mm default).cvTa.name b.nP cA.2 ψ Es := by
    intro ψ Es; unfold ctorBodyAVI; rw [hleaf]
  have hle : b.ownOffset mm ≤ b.ownOffset mm + j := Nat.le_add_right _ _
  refine
    { door := RC.hfd, lpsC := by rw [RC.hlpsC, C.hlps]
      Tfound := by rw [(C.hfind' mm _ RC.hmm hft).1]; rfl
      idxRes := ?_, wEq := fun _ => rfl, CD := C.ctorDataI_of RC RS hagree
      lenA := hCD.len, okTyA := fun ψ ρ => by rw [hbody]; exact hCD.okTy ψ ρ
      bitsA := fun ψ d hd => by rw [← hsEq]; exact hCD.bits ψ d hd
      belowA := hCD.below
      paramsA := fun ψ₁ ψ₂ hφ => (hCD.params ψ₁ ψ₂ (by rw [h.lpsC _ _ RC.hJ]; exact hφ)).1
      lenR := fun ψ => by rw [RS.len, hCD.len], takeR := C.takeEq RC RS
      bitsR := fun ψ i => (C.bitsEq RC RS ψ i).2.2, agree := hagree
      fold := ?_, FsJ := ?_, EsJ := ?_, FssParams := ?_, FssBelow := ?_
      frameIff := ?_, FssOkP := ?_ }
  · -- the index arguments resolve at the prefix environment
    intro e he
    have hr := hCD.opened.residRes
    rw [← hCD.idxEq] at hr
    exact constsResolve_consMutualFormers (hr e he)
  · -- the fold, at the auxiliary block's fibre
    intro ψ ρ hρ bs hsp
    have := h.fold hμ RC.hJ ψ ρ (by rw [RC.hmemJ]; exact hρ) bs hsp
    rw [RC.hmemJ] at this
    rw [hbody]
    exact this
  · intro ψ
    rw [List.getElem?_drop]
    show ((List.range ctorsA.length).map _)[b.ownOffset mm + j]? = _
    rw [List.getElem?_map, List.getElem?_range hJl]
    rfl
  · intro ψ
    rw [List.getElem?_drop]
    have hgd := blkEss_getD (b := b) (ppsF := ppsF) (W := W) (esF := esF) (ψ := ψ) hJl
    rw [List.getD_eq_getElem?_getD] at hgd
    rw [List.getElem?_eq_getElem (show b.ownOffset mm + j < (blkEss b ctorsA ppsF W esF ψ).length from
      by rw [blkEss_length]; exact hJl)] at hgd ⊢
    rw [Option.getD_some] at hgd
    rw [hgd, mutNFOf_eq RC.hJ, RC.hmemJ]
  · intro ψ₁ ψ₂ hφ
    refine ⟨((h.FD₀ 0 f₀ h.first).params ψ₁ ψ₂ (by rw [h.lps 0 f₀ h.first]; exact hφ)).2, ?_⟩
    show (mutFss _ _ _ _).drop _ = (mutFss _ _ _ _).drop _
    congr 1
    unfold mutFss
    exact List.map_congr_left (fun J hJ => by
      rw [(h.CDpar J (List.mem_range.mp hJ) ψ₁ ψ₂ hφ).1])
  · intro ψ Fs hFs
    obtain ⟨J, hJ, rfl⟩ := List.mem_map.mp (show Fs ∈ (List.range ctorsA.length).map
      (fun J => ((dsF J ψ).drop b.nP).map (·.2.2)) from List.mem_of_mem_drop hFs)
    have hh := (DomsBelow.drop b.nP
      ((h.CD J _ (ctorsA_get (List.mem_range.mp hJ))).below ψ)).fields
    rwa [Nat.zero_add] at hh
  · intro ψ ρ
    have := (h.framesJ hμ hJl).1 ψ ρ
    rw [RC.hmemJ] at this
    exact this
  · intro ψ ρ hρ
    exact ⟨fun Fs hFs => (h.fssOkP hμ hJl ψ ρ hρ).1 Fs (List.mem_of_mem_drop hFs),
      fun Fs hFs => (h.fssOkP hμ hJl ψ ρ hρ).2 Fs (List.mem_of_mem_drop hFs)⟩


/-- **A plain position's entry is the auxiliary's** (the whole triple):
a field that is not a nested recursive/reflexive one is auxiliary-free,
its restored domain is the auxiliary domain, and the bits are shared. -/
theorem ReadCtx.plainEntry (ψ : Name → Nat) {i : Nat} (hi : i < cA.2)
    (hpl : (D).nestOf mm j i = none ∨
      (rsOf (kindsOf (mutKsOf kinds (b.ownOffset mm + j)))).getD i false = false) :
    (dsRc ψ).getD (b.nP + i) default = (dsF (b.ownOffset mm + j) ψ).getD (b.nP + i) default := by
  have hCD := C.h.CD _ _ RC.hJ
  have hil : i < (xFvsF (b.ownOffset mm + j)).length := by rw [hCD.xLen]; exact hi
  obtain ⟨x, hx⟩ : ∃ x, (xFvsF (b.ownOffset mm + j))[i]? = some x := ⟨_, List.getElem?_eq_getElem hil⟩
  obtain ⟨ty', hx', hF⟩ := RC.fields i x hx
  have hksl : (mutKsOf kinds (b.ownOffset mm + j)).length = cA.2 := (C.h.ksJ _ _ RC.hJ).1
  have hkl : i < (kindsOf (mutKsOf kinds (b.ownOffset mm + j))).length := by
    rw [kindsOf_length, hksl]; exact hi
  -- a nested recursive/reflexive field is excluded by `hpl`
  have hnotNest : ∀ q, ¬ (tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i = p.k + q ∧
      (kindAt (mutKsOf kinds (b.ownOffset mm + j)) i = .recursive ∨
        kindAt (mutKsOf kinds (b.ownOffset mm + j)) i = .reflexive)) := by
    rintro q ⟨htq, hk⟩
    have hnt : ¬ (D).tgts mm j i < p.k := by
      show ¬ tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i < p.k
      omega
    have hr : (rsOf (kindsOf (mutKsOf kinds (b.ownOffset mm + j)))).getD i false = true :=
      (rsOf_getD_iff hkl).mpr (by rw [kindsOf_getD']; exact hk)
    rcases hpl with hpl | hpl
    · rw [(D).nestOf_some hnt] at hpl; exact nomatch hpl
    · rw [hr] at hpl; exact Bool.false_ne_true hpl.symm
  have h22 : ((dsRc ψ).getD (b.nP + i) default).2.2
      = ((dsF (b.ownOffset mm + j) ψ).getD (b.nP + i) default).2.2 := by
    rcases hF with ⟨-, heq⟩ | ⟨q, qn, -, htq, hk, -, -⟩ | ⟨q, qn, -, -, -, -, -, htq, hk, -, -, -, -⟩
    · exact C.fieldEqA RC RS ψ hx hx' heq
    · exact absurd ⟨htq, Or.inl hk⟩ (hnotNest q)
    · exact absurd ⟨htq, Or.inr hk⟩ (hnotNest q)
  obtain ⟨h1, h2, h3⟩ := C.bitsEq RC RS ψ (b.nP + i)
  exact Prod.ext (h1.trans h2.symm) (Prod.ext h3 h22)

/-- The domain facts (`NestedCtorRead.dom`). -/
theorem ReadCtx.dom_of (ψ : Name → Nat) :
    (dsRc ψ).length = (dsF (b.ownOffset mm + j) ψ).length ∧
    (dsRc ψ).take b.nP = (dsF (b.ownOffset mm + j) ψ).take b.nP ∧
    (∀ i, ((D).nestOf mm j i = none ∨
        (rsOf (kindsOf (mutKsOf kinds (b.ownOffset mm + j)))).getD i false = false) →
      (dsRc ψ).getD (b.nP + i) default = (dsF (b.ownOffset mm + j) ψ).getD (b.nP + i) default) := by
  have hCD := C.h.CD _ _ RC.hJ
  refine ⟨by rw [RS.len, hCD.len], C.takeEq RC RS ψ, ?_⟩
  intro i hpl
  rcases Nat.lt_or_ge i cA.2 with hi | hi
  · exact C.plainEntry RC RS ψ hi hpl
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [RS.len]; omega),
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hCD.len]; omega)]


/-! ### The nested finitary and the member-target clauses -/

omit RS in
/-- The target of a field, when a pin: the pin's record and index count. -/
theorem ReadCtx.pinTarget {i q : Nat} (hq : (D).nestOf mm j i = some q) :
    q < pinsS.length ∧ ∃ qn : NestedPin, st.pins[q]? = some qn ∧
      tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i = p.k + q ∧
      mutualNIdxOf b.members3 (tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i) = ((D).pinAt q).nIdx := by
  have htgt : tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i < fms.length := (C.h.ksJ _ _ RC.hJ).2.2 i
  have hlenFms : fms.length = p.k + st.pins.length := by rw [C.h.lenFms, C.hbk]
  have hnt : ¬ (D).tgts mm j i < p.k := by
    intro hlt
    rw [(D).nestOf_none hlt] at hq
    exact nomatch hq
  rw [(D).nestOf_some hnt] at hq
  have hqe : q = tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i - p.k := (Option.some.inj hq).symm
  have hnt' : ¬ tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i < p.k := hnt
  have hql : q < st.pins.length := by omega
  obtain ⟨qn, hqn⟩ : ∃ qn, st.pins[q]? = some qn := ⟨_, List.getElem?_eq_getElem hql⟩
  refine ⟨by rw [C.PF.pinsLen]; exact hql, qn, hqn, by omega, ?_⟩
  have hft := fms_get htgt
  rw [(C.h.memT _ _ hft).2, show tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i = p.k + q from by omega]
  exact C.PF.pinNIdx q (by rw [C.PF.pinsLen]; exact hql)

/-- **A nested finitary field's clauses**: the index arguments read at
the prefix model, with the pin's index count, and the entry is the
container's leaf at the lifted components. -/
theorem ReadCtx.nestClauses (ψ : Name → Nat) {i q : Nat} {x : Expr}
    (hx : xFvsRc[i]? = some x) (hq : (D).nestOf mm j i = some q)
    (hk : (kindsOf (mutKsOf kinds (b.ownOffset mm + j))).getD i .ordinary = .recursive) :
    DenoteMetaSpine mp₁'.base2.acval ENV₁ ψ (b.nP + i) (x.fvarTypeD.getAppArgs.drop ((D).pinAt q).nPJ)
      ((eissF (b.ownOffset mm + j) ψ).getD i []) ∧
    ((eissF (b.ownOffset mm + j) ψ).getD i []).length = ((D).pinAt q).nIdx ∧
    ((dsRc ψ).getD (b.nP + i) default).2.2
      = AnnotTerm.mkAppN (mp₁'.base2.acval ((D).pinAt q).J (((D).pinAt q).ψJ ψ))
          ((((D).pinAt q).Ds ψ).map (·.liftN i 0) ++ (eissF (b.ownOffset mm + j) ψ).getD i []) := by
  have hCD := C.h.CD _ _ RC.hJ
  have hi : i < cA.2 := by rw [← RC.hlenX]; exact (List.getElem?_eq_some_iff.mp hx).1
  have hil : i < (xFvsF (b.ownOffset mm + j)).length := by rw [hCD.xLen]; exact hi
  obtain ⟨xA, hxA⟩ : ∃ xA, (xFvsF (b.ownOffset mm + j))[i]? = some xA := ⟨_, List.getElem?_eq_getElem hil⟩
  obtain ⟨ty', hx', hF⟩ := RC.fields i xA hxA
  obtain rfl : x = .fvar (b.nP + i) ty' := Option.some.inj (hx.symm.trans hx')
  rw [kindsOf_getD'] at hk
  obtain ⟨hql, qn, hqn, htq, hnIdx⟩ := C.pinTarget RC hq
  rcases hF with ⟨hA, -⟩ | ⟨q', qn', hqn', htq', -, hshape, hty⟩ | ⟨q', qn', -, -, -, -, -, -, hk', -, -, -, -⟩
  · exfalso
    rcases hA with hA | hA
    · rw [hA] at hk; exact nomatch hk
    · omega
  · have hqq : q' = q := by omega
    subst q'
    obtain rfl := Option.some.inj (hqn.symm.trans hqn')
    obtain ⟨hsp, hentry⟩ := C.fieldEqB RC RS ψ hxA hx' hqn hk hty
    obtain ⟨-, -, hlenArgs, -, -, -⟩ := hCD.opened.recF i xA hxA hk
    -- the pin's argument count
    have hnPJ : (Expr.instSeq (fvsPF (b.ownOffset mm + j)) (b.nP - 1)
        (Expr.abstractRange qn.pin 0 p.nP 0)).getAppArgs.length = ((D).pinAt q).nPJ := by
      obtain ⟨hJ', hpin⟩ := C.PF.pinRec q qn hqn
      obtain ⟨q₀, kJ, i', dJ, hqe, hi', G⟩ := C.PF.groups dsR xFvsR q hql
      have hDsE : (pinsS.getD q default).DsE.length = ((D).pinAt q).nPJ := by
        rw [(C.PF.pinDs q hql ψ).length]
        show ((pinsS.getD q default).Ds ψ).length = (pinsS.getD q default).nPJ
        rw [hqe] at hql ⊢
        rw [show ((pinsS.getD (q₀ + i') default).Ds ψ).length = (((D).pinAt (q₀ + i')).Ds ψ).length from rfl,
          G.pinDsLen i' hi' ψ, ← G.pinNP i' hi']
        rfl
      rw [hpin, ← C.hnP]
      rw [ConLeche.rk_restoredPin_getAppArgs_length hCD.pLen (C.fvsPIdx RC.hJ)
        (nt_pin_bounded (C.PF.pinDs q hql ψ))]
      exact hDsE
    refine ⟨?_, ?_, hentry⟩
    · show DenoteMetaSpine _ _ _ _ (ty'.getAppArgs.drop ((D).pinAt q).nPJ) _
      rw [hty, Expr.getAppArgs_mkAppN, List.drop_left' hnPJ]
      exact hsp
    · rw [hCD.eisLen ψ i hk hi, hnIdx]
  · rw [hk'] at hk; exact nomatch hk

/-- **A member-target field's clauses**: the auxiliary domain, read at
the prefix model — a recursive field's index readings, count and entry
at the TARGET member's former; a reflexive field's opening, count and
entry — the auxiliary's, transferred, with the member's leaf the same
at both models. -/
theorem ReadCtx.memberClauses (ψ : Name → Nat) {i : Nat} {x : Expr}
    (hx : xFvsRc[i]? = some x) (hn : (D).nestOf mm j i = none) :
    ((kindsOf (mutKsOf kinds (b.ownOffset mm + j))).getD i .ordinary = .recursive →
      DenoteMetaSpine mp₁'.base2.acval ENV₁ ψ (b.nP + i) (x.fvarTypeD.getAppArgs.drop b.nP)
        ((eissF (b.ownOffset mm + j) ψ).getD i []) ∧
      ((eissF (b.ownOffset mm + j) ψ).getD i []).length = (D).nIdxAt ((D).tgts mm j i) ∧
      ((dsRc ψ).getD (b.nP + i) default).2.2
        = AnnotTerm.mkAppN (mp₁'.base2.acval ((D).memberName ((D).tgts mm j i)) ψ)
            (paramBvarsAt b.nP (b.nP + i) ++ (eissF (b.ownOffset mm + j) ψ).getD i [])) ∧
    ((kindsOf (mutKsOf kinds (b.ownOffset mm + j))).getD i .ordinary = .reflexive →
      (∃ afvs body,
        openPisAtFvars ((tssF (b.ownOffset mm + j) ψ).getD i []).length x.fvarTypeD (b.nP + i)
          = some (afvs, body) ∧
        ((tssF (b.ownOffset mm + j) ψ).getD i []).length = (x.fvarTypeD.piBinders).1.length ∧
        (∀ k a, afvs[k]? = some a →
          denoteMeta mp₁'.base2.acval ENV₁ ψ (b.nP + i + k) a.fvarTypeD
            = some (((tssF (b.ownOffset mm + j) ψ).getD i []).getD k default).2.2) ∧
        DenoteMetaSpine mp₁'.base2.acval ENV₁ ψ
          (b.nP + i + ((tssF (b.ownOffset mm + j) ψ).getD i []).length)
          (body.getAppArgs.drop b.nP) ((eissF (b.ownOffset mm + j) ψ).getD i [])) ∧
      ((eissF (b.ownOffset mm + j) ψ).getD i []).length = (D).nIdxAt ((D).tgts mm j i) ∧
      ((dsRc ψ).getD (b.nP + i) default).2.2
        = mkPisAV ((tssF (b.ownOffset mm + j) ψ).getD i [])
            (AnnotTerm.mkAppN (mp₁'.base2.acval ((D).memberName ((D).tgts mm j i)) ψ)
              (paramBvarsAt b.nP (b.nP + i + ((tssF (b.ownOffset mm + j) ψ).getD i []).length)
                ++ (eissF (b.ownOffset mm + j) ψ).getD i []))) := by
  have hCD := C.h.CD _ _ RC.hJ
  have hi : i < cA.2 := by rw [← RC.hlenX]; exact (List.getElem?_eq_some_iff.mp hx).1
  have hil : i < (xFvsF (b.ownOffset mm + j)).length := by rw [hCD.xLen]; exact hi
  obtain ⟨xA, hxA⟩ : ∃ xA, (xFvsF (b.ownOffset mm + j))[i]? = some xA := ⟨_, List.getElem?_eq_getElem hil⟩
  obtain ⟨ty', hx', hF⟩ := RC.fields i xA hxA
  obtain rfl : x = .fvar (b.nP + i) ty' := Option.some.inj (hx.symm.trans hx')
  -- the target is a member
  have hlt : (D).tgts mm j i < p.k := by
    rcases Nat.lt_or_ge ((D).tgts mm j i) p.k with h | h
    · exact h
    · rw [(D).nestOf_some (Nat.not_lt.mpr h)] at hn; exact nomatch hn
  have hlt' : tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i < p.k := hlt
  have htl : tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i < fms.length :=
    Nat.lt_of_lt_of_le hlt' C.hkle
  have hft := fms_get htl
  have hName : (D).memberName ((D).tgts mm j i)
      = mutualNameOf b.members3 (tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i) := by
    show ((fms.take p.k).map (·.cvTa.name)).getD (tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i) .anonymous = _
    rw [C.hName _ hlt', (C.h.memT _ _ hft).1]
  have hNIdx : (D).nIdxAt ((D).tgts mm j i)
      = mutualNIdxOf b.members3 (tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i) := by
    show ((fms.take p.k).map (·.nIdx)).getD (tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i) 0 = _
    rw [C.hNIdx _ hlt', (C.h.memT _ _ hft).2]
  have hleaf : mp₁'.base2.acval ((D).memberName ((D).tgts mm j i))
      = mp₁.base2.acval (mutualNameOf b.members3 (tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i)) := by
    rw [hName, (C.h.memT _ _ hft).1, C.hleafM' _ _ hlt' hft, C.h.leaf _ _ hft]
  -- the domain is the auxiliary's
  have heq : ty' = xA.fvarTypeD := by
    rcases hF with ⟨-, heq⟩ | ⟨q', qn', -, htq', -, -, -⟩ | ⟨q', qn', -, -, -, -, -, htq', -, -, -, -, -⟩
    · exact heq
    · omega
    · omega
  have h22 := C.fieldEqA RC RS ψ hxA hx' heq
  have hxt : (Expr.fvar (b.nP + i) ty').fvarTypeD = xA.fvarTypeD := heq
  rw [hxt]
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · rw [kindsOf_getD'] at hk
    obtain ⟨-, -, -, hres, -, -⟩ := hCD.opened.recF i xA hxA hk
    refine ⟨(C.transferSpine ψ _ (fun a ha => constsResolve_consMutualFormers (hres a ha))).mp
      (hCD.eisRead ψ i xA hxA hk), by rw [hCD.eisLen ψ i hk hi, hNIdx], ?_⟩
    rw [h22, hCD.recEntry ψ i hk hi, hleaf]
  · rw [kindsOf_getD'] at hk
    obtain ⟨afvs, body, hopA, hLen, hdoms, hsp⟩ := hCD.reflOpen ψ i xA hxA hk
    obtain ⟨afvs', body', hopA', -, hares, -, -, -, hres, -, -⟩ := hCD.opened.reflF i xA hxA hk
    rw [hLen] at hopA
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hopA.symm.trans hopA'))
    rw [← hLen] at hopA
    refine ⟨⟨afvs, body, hopA, hLen, fun k a ha => ?_, ?_⟩,
      by rw [hCD.eisLenRefl ψ i hk hi, hNIdx], ?_⟩
    · rw [← C.transfer ψ _ _ (constsResolve_consMutualFormers (hares a (List.mem_of_getElem? ha)))]
      exact hdoms k a ha
    · exact (C.transferSpine ψ _ (fun e he => constsResolve_consMutualFormers (hres e he))).mp hsp
    · rw [h22, hCD.reflEntry ψ i hk hi, hleaf]

/-- The `agree` input at a finitary nested position. -/
theorem ReadCtx.hnest_of (ψ : Name → Nat) {l q : Nat} (hl : l < cA.2)
    (hq : (D).nestOf mm j l = some q)
    (hk : (kindsOf (mutKsOf kinds (b.ownOffset mm + j))).getD l .ordinary = .recursive) :
    ((dsRc ψ).getD (b.nP + l) default).2.2
      = AnnotTerm.mkAppN (mp₁'.base2.acval ((D).pinAt q).J (((D).pinAt q).ψJ ψ))
          ((((D).pinAt q).Ds ψ).map (·.liftN l 0) ++ (eissF (b.ownOffset mm + j) ψ).getD l []) ∧
    ((eissF (b.ownOffset mm + j) ψ).getD l []).length = ((D).pinAt q).nIdx := by
  have hll : l < xFvsRc.length := by rw [RC.hlenX]; exact hl
  obtain ⟨x, hx⟩ : ∃ x, xFvsRc[l]? = some x := ⟨_, List.getElem?_eq_getElem hll⟩
  obtain ⟨-, h2, h3⟩ := C.nestClauses RC RS ψ hx hq hk
  exact ⟨h3, h2⟩


/-! ### The block model's constructor data -/

omit RS in
/-- The block model's names at member `mm`. -/
theorem ReadCtx.dName : (D).memberName mm = (fms.getD mm default).cvTa.name := C.hName mm RC.hmm
omit RS in
theorem ReadCtx.dNIdx : (D).nIdxAt mm = (fms.getD mm default).nIdx := C.hNIdx mm RC.hmm

omit RS in
/-- A restored field is a variable at its position. -/
theorem ReadCtx.xIdx_of {k : Nat} {x : Expr} (hx : xFvsRc[k]? = some x) :
    ∃ ty, x = Expr.fvar (b.nP + k) ty := by
  have hCD := C.h.CD _ _ RC.hJ
  have hkl : k < (xFvsF (b.ownOffset mm + j)).length := by
    rw [hCD.xLen, ← RC.hlenX]; exact (List.getElem?_eq_some_iff.mp hx).1
  obtain ⟨xA, hxA⟩ : ∃ xA, (xFvsF (b.ownOffset mm + j))[k]? = some xA := ⟨_, List.getElem?_eq_getElem hkl⟩
  obtain ⟨ty', hx', -⟩ := RC.fields k xA hxA
  exact ⟨ty', Option.some.inj (hx.symm.trans hx')⟩

/-- **The block model's constructor data at the restored constructor**
(`BlockCtorFacts`' third conjunct, at the prefix model), from the
restored `CtorDataI`, the opened form (`hopened`, lane O), the plain
and finitary nested clauses, and the reflexive nested clauses
(`hreflC`, lane R). -/
theorem ReadCtx.blockCtorData_of
    (hagree : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((dsF (b.ownOffset mm + j) ψ).take b.nP).map (·.2.2)).reverse ρ →
      ∀ l, l < cA.2 → ∀ fs₁ : List V, fs₁.length = l →
        SpineFit ρ ((((dsF (b.ownOffset mm + j) ψ).drop b.nP).map (·.2.2)).take l) fs₁ →
        SpineFit ρ ((((dsRc ψ).drop b.nP).map (·.2.2)).take l) fs₁ →
        interp V (consList fs₁ ρ) ((dsF (b.ownOffset mm + j) ψ).getD (b.nP + l) default).2.2
          = interp V (consList fs₁ ρ) ((dsRc ψ).getD (b.nP + l) default).2.2)
    (hopened : BlockOpened env (fun i => (D).memberName ((D).tgts mm j i))
      (fun i => (D).nIdxAt ((D).tgts mm j i)) (fun i => (D).nestOf mm j i) (D).pinAt b.lps b.nP cA.2
      (kindsOf (mutKsOf kinds (b.ownOffset mm + j))) (fvsPF (b.ownOffset mm + j)) xFvsRc
      (xrestF (b.ownOffset mm + j)))
    (hreflC : ∀ (ψ : Name → Nat) (i q : Nat) (x : Expr), xFvsRc[i]? = some x →
      (D).nestOf mm j i = some q →
      (kindsOf (mutKsOf kinds (b.ownOffset mm + j))).getD i .ordinary = .reflexive →
      (∃ afvs body,
        openPisAtFvars ((tssF (b.ownOffset mm + j) ψ).getD i []).length x.fvarTypeD (b.nP + i)
          = some (afvs, body) ∧
        ((tssF (b.ownOffset mm + j) ψ).getD i []).length = (x.fvarTypeD.piBinders).1.length ∧
        (∀ k a, afvs[k]? = some a →
          denoteMeta mp₁'.base2.acval ENV₁ ψ (b.nP + i + k) a.fvarTypeD
            = some (((tssF (b.ownOffset mm + j) ψ).getD i []).getD k default).2.2) ∧
        DenoteMetaSpine mp₁'.base2.acval ENV₁ ψ
          (b.nP + i + ((tssF (b.ownOffset mm + j) ψ).getD i []).length)
          (body.getAppArgs.drop ((D).pinAt q).nPJ) ((eissF (b.ownOffset mm + j) ψ).getD i [])) ∧
      ((eissF (b.ownOffset mm + j) ψ).getD i []).length = ((D).pinAt q).nIdx ∧
      ((dsRc ψ).getD (b.nP + i) default).2.2
        = mkPisAV ((tssF (b.ownOffset mm + j) ψ).getD i [])
            (AnnotTerm.mkAppN (mp₁'.base2.acval ((D).pinAt q).J (((D).pinAt q).ψJ ψ))
              ((((D).pinAt q).Ds ψ).map
                  (·.liftN (i + ((tssF (b.ownOffset mm + j) ψ).getD i []).length) 0)
                ++ (eissF (b.ownOffset mm + j) ψ).getD i []))) :
    BlockCtorData mp₁'.base2 env (fms.getD mm default).cvTa.name
      (fun i => (D).memberName ((D).tgts mm j i)) (fun i => (D).nIdxAt ((D).tgts mm j i))
      (fun i => (D).nestOf mm j i) (D).pinAt b.lps c.1 b.nP cA.2 (fms.getD mm default).nIdx f₀.s
      (Level.isEquiv f₀.s .zero == some true) b.large (idxF (b.ownOffset mm + j)) dsRc
      (esF (b.ownOffset mm + j)) (srcsF (b.ownOffset mm + j))
      (kindsOf (mutKsOf kinds (b.ownOffset mm + j))) (fvsPF (b.ownOffset mm + j)) xFvsRc
      (xrestF (b.ownOffset mm + j)) (eissF (b.ownOffset mm + j)) (tssF (b.ownOffset mm + j)) := by
  have hCD := C.h.CD _ _ RC.hJ
  rw [RC.hmemJ] at hCD
  have hsEq : ∀ ψ : Name → Nat, (fms.getD mm default).s.eval ψ = f₀.s.eval ψ :=
    C.h.sEq mm _ (C.memberAt mm RC.hmm)
  have hlpsA : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ c.1.levelParams, ψ₁ q = ψ₂ q) →
      ∀ q ∈ cA.1.levelParams, ψ₁ q = ψ₂ q := by
    intro ψ₁ ψ₂ hφ
    rw [RC.hlpsC, ← C.hlps] at hφ
    rw [C.h.lpsC _ _ RC.hJ]; exact hφ
  have hxAt : ∀ (i : Nat), i < cA.2 → ∃ x, xFvsRc[i]? = some x :=
    fun i hi => ⟨_, List.getElem?_eq_getElem (by rw [RC.hlenX]; exact hi)⟩
  have hpos : ∀ (i : Nat) (x : Expr), xFvsRc[i]? = some x →
      (fvsPF (b.ownOffset mm + j) ++ xFvsRc)[b.nP + i]? = some x := by
    intro i x hx
    rw [List.getElem?_append_right (by rw [hCD.pLen]; exact Nat.le_add_right _ _), hCD.pLen,
      Nat.add_sub_cancel_left]
    exact hx
  refine
    { toCtorDataI := C.ctorDataI_of RC RS hagree
      opened := hopened, opens := ⟨crestR, RC.hopP, RC.hopX⟩
      ksLen := by rw [kindsOf_length]; exact (C.h.ksJ _ _ RC.hJ).1
      xLen := RC.hlenX, pLen := hCD.pLen, xIdx := fun k x hx => C.xIdx_of RC hx
      pIdx := hCD.pIdx, idxEq := hCD.idxEq
      domRead := fun ψ i x hx => C.entryR RC RS ψ (hpos i x hx)
      eissLen := hCD.eissLen
      eisRead := fun ψ i x hx hn hk => ((C.memberClauses RC RS ψ hx hn).1 hk).1
      eisLen := fun ψ i hn hk hi => ?_
      recEntry := fun ψ i hn hk hi => ?_
      nestEisRead := fun ψ i x q hx hq hk => (C.nestClauses RC RS ψ hx hq hk).1
      nestEisLen := fun ψ i q hq hk hi => ?_
      nestEntry := fun ψ i q hq hk hi => ?_
      eissParams := fun ψ₁ ψ₂ hφ => hCD.eissParams ψ₁ ψ₂ (hlpsA ψ₁ ψ₂ hφ)
      eissBelow := hCD.eissBelow
      ordNone := fun ψ i h₁ h₂ =>
        hCD.ordNone ψ i (by rwa [kindsOf_getD'] at h₁) (by rwa [kindsOf_getD'] at h₂)
      tssLen := hCD.tssLen
      tssNone := fun ψ i hk => hCD.tssNone ψ i (by rwa [kindsOf_getD'] at hk)
      tssBits := fun ψ i d hd => by rw [← hsEq]; exact hCD.tssBits ψ i d hd
      tssPiBits := hCD.tssPiBits, tssBelow := hCD.tssBelow
      tssParams := fun ψ₁ ψ₂ hφ => hCD.tssParams ψ₁ ψ₂ (hlpsA ψ₁ ψ₂ hφ)
      reflOpen := fun ψ i x hx hn hk => ((C.memberClauses RC RS ψ hx hn).2 hk).1
      eisLenRefl := fun ψ i hn hk hi => ?_
      reflEntry := fun ψ i hn hk hi => ?_
      nestReflOpen := fun ψ i x q hx hq hk => (hreflC ψ i q x hx hq hk).1
      nestEisLenRefl := fun ψ i q hq hk hi => ?_
      nestReflEntry := fun ψ i q hq hk hi => ?_ }
  · obtain ⟨x, hx⟩ := hxAt i hi
    exact ((C.memberClauses RC RS ψ hx hn).1 hk).2.1
  · obtain ⟨x, hx⟩ := hxAt i hi
    exact ((C.memberClauses RC RS ψ hx hn).1 hk).2.2
  · obtain ⟨x, hx⟩ := hxAt i hi
    exact (C.nestClauses RC RS ψ hx hq hk).2.1
  · obtain ⟨x, hx⟩ := hxAt i hi
    exact (C.nestClauses RC RS ψ hx hq hk).2.2
  · obtain ⟨x, hx⟩ := hxAt i hi
    exact ((C.memberClauses RC RS ψ hx hn).2 hk).2.1
  · obtain ⟨x, hx⟩ := hxAt i hi
    exact ((C.memberClauses RC RS ψ hx hn).2 hk).2.2
  · obtain ⟨x, hx⟩ := hxAt i hi
    exact (hreflC ψ i q x hx hq hk).2.1
  · obtain ⟨x, hx⟩ := hxAt i hi
    exact (hreflC ψ i q x hx hq hk).2.2


omit RS in
/-- **The reading exists at a restored constructor**: the door, the
openings at the auxiliary residual (the member at the parameter
openers and the index arguments), the member found at the prefix
environment, the index arguments read there. -/
theorem ReadCtx.readSpec_of :
    ∃ dsRc : (Name → Nat) → List (Nat × Nat × AnnotTerm),
      ReadSpec mp₁' (fms.getD mm default).cvTa.name b.nP cA.2 c.1 (esF (b.ownOffset mm + j)) dsRc := by
  obtain ⟨-, -, -, hxrEq, -, -, -, -⟩ := C.auxShape RC.hJ
  rw [RC.hmemJ] at hxrEq
  have hopX := RC.hopX
  rw [hxrEq] at hopX
  exact readSpec_exists C.hμ mp₁' RC.hfd RC.hopP hopX (C.hfind' mm _ RC.hmm (C.memberAt mm RC.hmm)).1
    (C.h.lps mm _ (C.memberAt mm RC.hmm)) (C.idxRead RC.hJ)

end Entries

/-! ### The pin identification at the restored entries -/

/-- **The two domain lists read alike at every fitting prefix** (the
`agree` input of `NestedCtorInput`): `nestedDomAgree_of`
(`NestedCore.lean`) at the loop's own model — the theorem is stated
there because the RECURSORS' stage spends it too, at the restored
constructors' model (`NestedTailIn.domAgree`). -/
theorem ReadCtx.agree_of {mm j : Nat} {cA : ConstantVal × Nat}
    (hJ : ctorsA[b.ownOffset mm + j]? = some cA)
    (hmemJ : mutMemF b (b.ownOffset mm + j) = mm)
    (hlenR : ∀ ψ : Name → Nat, (dsR mm j ψ).length = b.nP + cA.2)
    (hokR : ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenotedV V ρ (mkPisAV (dsR mm j ψ)
      (ctorBodyAVI mp₁'.base2 (fms.getD mm default).cvTa.name b.nP cA.2 ψ
        (esF (b.ownOffset mm + j) ψ))))
    (htake : ∀ ψ : Name → Nat, (dsR mm j ψ).take b.nP = (dsF (b.ownOffset mm + j) ψ).take b.nP)
    (hplain : ∀ (ψ : Name → Nat) (l : Nat), l < cA.2 →
      ((D).nestOf mm j l = none ∨
        (rsOf (kindsOf (mutKsOf kinds (b.ownOffset mm + j)))).getD l false = false) →
      (dsR mm j ψ).getD (b.nP + l) default = (dsF (b.ownOffset mm + j) ψ).getD (b.nP + l) default)
    (hnest : ∀ (ψ : Name → Nat) (l q : Nat), l < cA.2 → (D).nestOf mm j l = some q →
      (kindsOf (mutKsOf kinds (b.ownOffset mm + j))).getD l .ordinary = .recursive →
      ((dsR mm j ψ).getD (b.nP + l) default).2.2
        = AnnotTerm.mkAppN (mp₁'.base2.acval ((D).pinAt q).J (((D).pinAt q).ψJ ψ))
            ((((D).pinAt q).Ds ψ).map (·.liftN l 0) ++ (eissF (b.ownOffset mm + j) ψ).getD l []) ∧
      ((eissF (b.ownOffset mm + j) ψ).getD l []).length = ((D).pinAt q).nIdx)
    (hnestRefl : ∀ (ψ : Name → Nat) (l q : Nat), l < cA.2 → (D).nestOf mm j l = some q →
      (kindsOf (mutKsOf kinds (b.ownOffset mm + j))).getD l .ordinary = .reflexive →
      ((dsR mm j ψ).getD (b.nP + l) default).2.2
        = mkPisAV ((tssF (b.ownOffset mm + j) ψ).getD l [])
          (AnnotTerm.mkAppN (mp₁'.base2.acval ((D).pinAt q).J (((D).pinAt q).ψJ ψ))
            ((((D).pinAt q).Ds ψ).map
                (·.liftN (l + ((tssF (b.ownOffset mm + j) ψ).getD l []).length) 0)
              ++ (eissF (b.ownOffset mm + j) ψ).getD l [])) ∧
      ((eissF (b.ownOffset mm + j) ψ).getD l []).length = ((D).pinAt q).nIdx) :
    ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((dsF (b.ownOffset mm + j) ψ).take b.nP).map (·.2.2)).reverse ρ →
      ∀ l, l < cA.2 → ∀ fs₁ : List V, fs₁.length = l →
        SpineFit ρ ((((dsF (b.ownOffset mm + j) ψ).drop b.nP).map (·.2.2)).take l) fs₁ →
        SpineFit ρ ((((dsR mm j ψ).drop b.nP).map (·.2.2)).take l) fs₁ →
        interp V (consList fs₁ ρ) ((dsF (b.ownOffset mm + j) ψ).getD (b.nP + l) default).2.2
          = interp V (consList fs₁ ρ) ((dsR mm j ψ).getD (b.nP + l) default).2.2 :=
  nestedDomAgree_of C.hμ C.h C.h3 (by rw [C.hbk, C.PF.pinsLen]) mp₁'.base2
    (fun q hq => C.PF.groups dsR xFvsR q hq) hJ hmemJ hlenR (fun ψ ρ => (hokR ψ ρ).1) htake
    hplain hnest hnestRefl

/-! ### The per-constructor law -/

/-- **`NestedCtorRead` at one restored constructor**, from its record,
its reading, the opened form (lane O) and the reflexive nested entries
(lane R): the identification `agree_of` at the entries, then the
three components. -/
theorem ReadCtx.nestedCtorRead_of {mm j : Nat} {c : ConstantVal × Nat × Nat} {cA : ConstantVal × Nat}
    {crestR : Expr}
    (RC : RestoredCtor (μ := μ) (env := env) (F := F) (p := p) (b := b) (fms := fms)
      (ctorsA := ctorsA) (kinds := kinds) (fvsPF := fvsPF) (xFvsF := xFvsF) (xrestF := xrestF)
      (st := st) mm j c cA crestR (xFvsR mm j))
    (RS : ReadSpec mp₁' (fms.getD mm default).cvTa.name b.nP cA.2 c.1 (esF (b.ownOffset mm + j))
      (dsR mm j))
    (hopened : BlockOpened env (fun i => (D).memberName ((D).tgts mm j i))
      (fun i => (D).nIdxAt ((D).tgts mm j i)) (fun i => (D).nestOf mm j i) (D).pinAt b.lps b.nP cA.2
      (kindsOf (mutKsOf kinds (b.ownOffset mm + j))) (fvsPF (b.ownOffset mm + j)) (xFvsR mm j)
      (xrestF (b.ownOffset mm + j)))
    (hreflC : ∀ (ψ : Name → Nat) (i q : Nat) (x : Expr), (xFvsR mm j)[i]? = some x →
      (D).nestOf mm j i = some q →
      (kindsOf (mutKsOf kinds (b.ownOffset mm + j))).getD i .ordinary = .reflexive →
      (∃ afvs body,
        openPisAtFvars ((tssF (b.ownOffset mm + j) ψ).getD i []).length x.fvarTypeD (b.nP + i)
          = some (afvs, body) ∧
        ((tssF (b.ownOffset mm + j) ψ).getD i []).length = (x.fvarTypeD.piBinders).1.length ∧
        (∀ k a, afvs[k]? = some a →
          denoteMeta mp₁'.base2.acval ENV₁ ψ (b.nP + i + k) a.fvarTypeD
            = some (((tssF (b.ownOffset mm + j) ψ).getD i []).getD k default).2.2) ∧
        DenoteMetaSpine mp₁'.base2.acval ENV₁ ψ
          (b.nP + i + ((tssF (b.ownOffset mm + j) ψ).getD i []).length)
          (body.getAppArgs.drop ((D).pinAt q).nPJ) ((eissF (b.ownOffset mm + j) ψ).getD i [])) ∧
      ((eissF (b.ownOffset mm + j) ψ).getD i []).length = ((D).pinAt q).nIdx ∧
      ((dsR mm j ψ).getD (b.nP + i) default).2.2
        = mkPisAV ((tssF (b.ownOffset mm + j) ψ).getD i [])
            (AnnotTerm.mkAppN (mp₁'.base2.acval ((D).pinAt q).J (((D).pinAt q).ψJ ψ))
              ((((D).pinAt q).Ds ψ).map
                  (·.liftN (i + ((tssF (b.ownOffset mm + j) ψ).getD i []).length) 0)
                ++ (eissF (b.ownOffset mm + j) ψ).getD i []))) :
    NestedCtorRead (V := V) (F := F) (p := p) (b := b) (fms := fms) (f₀ := f₀)
      (ctorsA := ctorsA) (kinds := kinds) (env := env) (ppsF := ppsF) (W := W)
      (idxF := idxF) (dsF := dsF) (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF)
      (xrestF := xrestF) (eissF := eissF) (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR)
      (xFvsR := xFvsR) (pinsS := pinsS) mp₁' mm j c := by
  have hxAt : ∀ (i : Nat), i < cA.2 → ∃ x, (xFvsR mm j)[i]? = some x :=
    fun i hi => ⟨_, List.getElem?_eq_getElem (by rw [RC.hlenX]; exact hi)⟩
  have hagree := C.agree_of RC.hJ RC.hmemJ RS.len RS.okTy (C.takeEq RC RS)
    (fun ψ l hl hpl => C.plainEntry RC RS ψ hl hpl)
    (fun ψ l q hl hq hk => C.hnest_of RC RS ψ hl hq hk)
    (fun ψ l q hl hq hk => by
      obtain ⟨x, hx⟩ := hxAt l hl
      exact ⟨(hreflC ψ l q x hx hq hk).2.2, (hreflC ψ l q x hx hq hk).2.1⟩)
  have hdata := C.blockCtorData_of RC RS hagree hopened hreflC
  have hinput := C.input_of RC RS hagree
  have hName : (D).memberName mm = (fms.getD mm default).cvTa.name := C.dName RC
  have hNIdx : (D).nIdxAt mm = (fms.getD mm default).nIdx := C.dNIdx RC
  refine ⟨?_, ?_, fun ψ => ?_, ?_, ?_, ?_⟩
  · rw [RC.hnF]; exact hinput
  · rw [RC.hnF]
    show BlockCtorData mp₁'.base2 env ((D).memberName mm) _ _ _ _ b.lps c.1 b.nP cA.2 ((D).nIdxAt mm) f₀.s
      (Level.isEquiv f₀.s .zero == some true) b.large (idxF (b.ownOffset mm + j)) (dsR mm j)
      (esF (b.ownOffset mm + j)) (srcsF (b.ownOffset mm + j))
      (kindsOf (mutKsOf kinds (b.ownOffset mm + j))) (fvsPF (b.ownOffset mm + j)) (xFvsR mm j)
      (xrestF (b.ownOffset mm + j)) (eissF (b.ownOffset mm + j)) (tssF (b.ownOffset mm + j))
    rw [hName, hNIdx]
    exact hdata
  · exact C.dom_of RC RS ψ
  · -- **the nested field's parameter arguments**: `RestoredField`'s own
    -- pin case, before `BlockOpened.nestF` drops it (task #315 PINF)
    intro l x pin q hx hpinE hn hk
    have hCD := C.h.CD (b.ownOffset mm + j) cA RC.hJ
    have hlenP : (fvsPF (b.ownOffset mm + j)).length = b.nP := hCD.pLen
    have hidxP := C.fvsPIdx RC.hJ
    have hk' : kindAt (mutKsOf kinds (b.ownOffset mm + j)) l = .recursive := by
      rw [← kindsOf_getD']; exact hk
    have htg : tgtAt (mutKsOf kinds (b.ownOffset mm + j)) l = p.k + q := by
      rcases Nat.lt_or_ge (tgtAt (mutKsOf kinds (b.ownOffset mm + j)) l) p.k with h | h
      · rw [(D).nestOf_none h] at hn; exact nomatch hn
      · rw [(D).nestOf_some (Nat.not_lt.mpr h)] at hn
        have h2 : tgtAt (mutKsOf kinds (b.ownOffset mm + j)) l - p.k = q := Option.some.inj hn
        omega
    have hil : l < cA.2 := by rw [← RC.hlenX]; exact (List.getElem?_eq_some_iff.mp hx).1
    obtain ⟨x₀, hx₀⟩ : ∃ y, (xFvsF (b.ownOffset mm + j))[l]? = some y :=
      ⟨_, List.getElem?_eq_getElem (by rw [hCD.xLen]; exact hil)⟩
    obtain ⟨ty', hxR, hRF⟩ := RC.fields l x₀ hx₀
    obtain rfl : x = Expr.fvar (b.nP + l) ty' := Option.some.inj (hx.symm.trans hxR)
    unfold RestoredField at hRF
    rcases hRF with ⟨hA, -⟩ | ⟨q', qn, hq', htg', -, -, hty⟩ |
        ⟨-, -, -, -, -, -, -, -, hkr, -, -, -, -⟩
    · exfalso
      rcases hA with h | h
      · rw [hk'] at h; exact nomatch h
      · omega
    · have hqq : q' = q := by omega
      subst hqq
      have hql : q' < pinsS.length := by
        rw [C.PF.pinsLen]; exact (List.getElem?_eq_some_iff.mp hq').1
      obtain ⟨hJn, hpin⟩ := C.PF.pinRec q' qn hq'
      obtain rfl : pin = qn.pin := by
        rw [hpinE, hpin]
        show Expr.mkAppN (Expr.const (pinsS.getD q' default).J (pinsS.getD q' default).lvls)
            (pinsS.getD q' default).DsE
          = Expr.mkAppN (Expr.const qn.container (pinsS.getD q' default).lvls)
            (pinsS.getD q' default).DsE
        rw [hJn]
      have hDs := C.PF.pinDs q' hql (fun _ => 0)
      have hbnd : (Expr.mkAppN (.const qn.container (pinsS.getD q' default).lvls)
          (pinsS.getD q' default).DsE).looseBVarsBounded 0 = true := nt_pin_bounded hDs
      obtain ⟨q₀, kJ, i', dJ, hqe, hi', G⟩ := C.PF.groups dsR xFvsR q' hql
      have hnp : (pinsS.getD q' default).nPJ = dJ.nP := by rw [hqe]; exact G.pinNP i' hi'
      have hdl : ((pinsS.getD q' default).Ds (fun _ => 0)).length = dJ.nP := by
        rw [hqe]; exact G.pinDsLen i' hi' (fun _ => 0)
      have hDsLen : (pinsS.getD q' default).DsE.length = (pinsS.getD q' default).nPJ := by
        rw [hDs.length, hdl, hnp]
      have hPargs : (Expr.instSeq (fvsPF (b.ownOffset mm + j)) (b.nP - 1)
          (Expr.abstractRange qn.pin 0 p.nP 0)).getAppArgs.length
            = (pinsS.getD q' default).nPJ := by
        rw [hpin, ← C.hnP, ← hDsLen]
        exact ConLeche.rk_restoredPin_getAppArgs_length hlenP hidxP hbnd
      show ty'.getAppArgs.take (pinsS.getD q' default).nPJ
        = (Expr.instSeq (fvsPF (b.ownOffset mm + j)) (b.nP - 1)
            (Expr.abstractRange qn.pin 0 p.nP 0)).getAppArgs
      rw [hty, Expr.getAppArgs_mkAppN, List.take_left' hPargs]
    · rw [hk'] at hkr; exact nomatch hkr
  · -- **the nested field's ABSTRACT parameter arguments**: the same
    -- pin case read one step earlier, where `stripPis` leaves the
    -- domain (task #315 PINF, `ReadCtx.restoredAbsPin`)
    intro l bs r dom pin q hstripR hdom hpinE hn hk
    have hCD := C.h.CD (b.ownOffset mm + j) cA RC.hJ
    have hk' : kindAt (mutKsOf kinds (b.ownOffset mm + j)) l = .recursive := by
      rw [← kindsOf_getD']; exact hk
    have htg : tgtAt (mutKsOf kinds (b.ownOffset mm + j)) l = p.k + q := by
      rcases Nat.lt_or_ge (tgtAt (mutKsOf kinds (b.ownOffset mm + j)) l) p.k with h | h
      · rw [(D).nestOf_none h] at hn; exact nomatch hn
      · rw [(D).nestOf_some (Nat.not_lt.mpr h)] at hn
        have h2 : tgtAt (mutKsOf kinds (b.ownOffset mm + j)) l - p.k = q := Option.some.inj hn
        omega
    obtain ⟨cbsA, cbs', es, hstripA, hstripR₀, -, -⟩ := RC.resid
    -- the two `stripPis` calls are the same call
    have hnF : c.2.2 = cA.2 := RC.hnF
    have hbsEq : bs = cbs' := by
      have h := hstripR
      rw [hnF] at h
      exact (Prod.mk.inj (Option.some.inj (h.symm.trans hstripR₀))).1
    -- the field index is in range
    have hclR : bs.length = b.nP + cA.2 := by
      rw [hbsEq]; exact Expr.stripPis_length _ hstripR₀
    have hDnP : (D).nP = b.nP := rfl
    have hlF : l < cA.2 := by
      have hin := (List.getElem?_eq_some_iff.mp hdom).1
      rw [hclR, hDnP] at hin
      omega
    have hclA : cbsA.length = b.nP + cA.2 := Expr.stripPis_length _ hstripA
    obtain ⟨domA, hdomA⟩ : ∃ domA, cbsA[b.nP + l]? = some domA :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    -- the auxiliary field, opened: its head is the mimic
    obtain ⟨x₀, hx₀⟩ : ∃ y, (xFvsF (b.ownOffset mm + j))[l]? = some y :=
      ⟨_, List.getElem?_eq_getElem (by rw [hCD.xLen]; exact hlF)⟩
    obtain ⟨ty', hxR, hRF⟩ := RC.fields l x₀ hx₀
    unfold RestoredField at hRF
    rcases hRF with ⟨hA, -⟩ | ⟨q', qn, hq', htg', -, hxdom, -⟩ |
        ⟨-, -, -, -, -, -, -, -, hkr, -, -, -, -⟩
    · exfalso
      rcases hA with h | h
      · rw [hk'] at h; exact nomatch h
      · omega
    · have hqq : q' = q := by omega
      subst hqq
      obtain ⟨hJn, hpin⟩ := C.PF.pinRec q' qn hq'
      obtain ⟨hpl, hrl⟩ := C.pinLookup hq'
      have hql : q' < pinsS.length := by
        rw [C.PF.pinsLen]; exact (List.getElem?_eq_some_iff.mp hq').1
      obtain rfl : pin = qn.pin := by
        rw [hpinE, hpin]
        show Expr.mkAppN (Expr.const (pinsS.getD q' default).J (pinsS.getD q' default).lvls)
            (pinsS.getD q' default).DsE
          = Expr.mkAppN (Expr.const qn.container (pinsS.getD q' default).lvls)
            (pinsS.getD q' default).DsE
        rw [hJn]
      -- the two openings of the AUXILIARY constructor, and the bridge
      obtain ⟨crestA, hopPA, hopXA⟩ := hCD.opens
      obtain ⟨bodyA, hopAll⟩ : ∃ bodyA, openPisAtFvars (b.nP + cA.2) cA.1.type 0
          = some (fvsPF (b.ownOffset mm + j) ++ xFvsF (b.ownOffset mm + j), bodyA) :=
        ⟨_, openPisAtFvars_add b.nP hopPA (by rw [Nat.zero_add]; exact hopXA)⟩
      obtain ⟨residA, hsplitA⟩ : ∃ residA, cA.1.type.stripPis (b.nP + cA.2)
          = some (cbsA.take b.nP ++ cbsA.drop b.nP, residA) :=
        ⟨_, by rw [List.take_append_drop]; exact hstripA⟩
      have htkA : (cbsA.take b.nP).length = b.nP := by rw [List.length_take, hclA]; omega
      have hdropA : (cbsA.drop b.nP)[l]? = some domA := by
        rw [List.getElem?_drop]; exact hdomA
      have hfnOp : x₀.fvarTypeD.getAppFn = Expr.const qn.aux (b.lps.map .param) := by
        rw [hxdom, Expr.getAppFn_mkAppN]; rfl
      have hfnA : domA.1.getAppFn = Expr.const qn.aux (b.lps.map .param) :=
        ConLeche.os_field_domain_head b.nP cA.2 l hopAll hsplitA hCD.pLen htkA hx₀ hdropA hfnOp
      have hargsA : x₀.fvarTypeD.getAppArgs
          = domA.1.getAppArgs.map (Expr.instSeq (fvsPF (b.ownOffset mm + j)
              ++ (xFvsF (b.ownOffset mm + j)).take l) (b.nP + l - 1) ·) :=
        ConLeche.os_field_domain_args b.nP cA.2 l hopAll hsplitA hCD.pLen htkA hx₀ hdropA
      have hlenA : b.nP ≤ domA.1.getAppArgs.length := by
        have h1 : x₀.fvarTypeD.getAppArgs.length = domA.1.getAppArgs.length := by
          rw [hargsA, List.length_map]
        have h2 := congrArg Expr.getAppArgs hxdom
        rw [Expr.getAppArgs_mkAppN] at h2
        simp only [show (Expr.const qn.aux (b.lps.map Level.param)).getAppArgs = [] from rfl,
          List.nil_append] at h2
        have h5 := congrArg List.length h2
        rw [List.length_append, hCD.pLen, List.length_drop] at h5
        omega
      -- the abstract restored domain, and its spine
      have habs := RC.absPin cbsA bs _ r l domA dom qn.aux (b.lps.map .param) _
        hstripA (by rw [hnF] at hstripR; exact hstripR) hdomA hdom hfnA hlenA hpl hrl
      -- the pin's own arity
      have hDs := C.PF.pinDs q' hql (fun _ => 0)
      obtain ⟨q₀, kJ, i', dJ, hqe, hi', G⟩ := C.PF.groups dsR xFvsR q' hql
      have hnp : (pinsS.getD q' default).nPJ = dJ.nP := by rw [hqe]; exact G.pinNP i' hi'
      have hdl : ((pinsS.getD q' default).Ds (fun _ => 0)).length = dJ.nP := by
        rw [hqe]; exact G.pinDsLen i' hi' (fun _ => 0)
      have hDsLen : (pinsS.getD q' default).DsE.length = (pinsS.getD q' default).nPJ := by
        rw [hDs.length, hdl, hnp]
      have hPargs : ((Expr.abstractRange qn.pin 0 p.nP 0).liftLooseBVars l 0).getAppArgs.length
          = (pinsS.getD q' default).nPJ := by
        rw [ConLeche.getAppArgs_length_liftLooseBVars, ConLeche.getAppArgs_length_abstractRange,
          hpin, Expr.getAppArgs_mkAppN]
        show ((Expr.const qn.container (pinsS.getD q' default).lvls).getAppArgs
          ++ (pinsS.getD q' default).DsE).length = _
        rw [show (Expr.const qn.container (pinsS.getD q' default).lvls).getAppArgs = [] from rfl,
          List.nil_append]
        exact hDsLen
      refine ⟨l, ?_⟩
      show dom.1.getAppArgs.take (pinsS.getD q' default).nPJ = _
      rw [habs, Expr.getAppArgs_mkAppN, List.take_left' hPargs]
    · rw [hk'] at hkr; exact nomatch hkr
  · -- the front door's own `.proj`-slot fact, at the members' prefix
    -- environment (task #315 PINF)
    exact RC.hfd.slots

end Assembly

end ConLeche.Model
