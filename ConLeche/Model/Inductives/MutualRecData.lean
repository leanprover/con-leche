module

public import ConLeche.Model.Inductives.MutualRecRead
public import ConLeche.Model.Inductives.MutualData
import ConLeche.Verify.Inductives.MutualInv
import ConLeche.Model.Inductives.StructRows
import ConLeche.Model.Inductives.StructFrames
import ConLeche.Model.Steps.BitLevels
import ConLeche.Model.Annot.BitConsCross
import ConLeche.Semantics.ConstsBound
import ConLeche.Semantics.Install
import ConLeche.Model.Install
public section

/-!
# The mutual recursor stage's readings, from the run (task #278, M2.5a)

`FixRecData.lean` at a mutual block: member `mm`'s generated recursor
type (`mutualRecTy`, checked by `checkMutualRecTy`) read off the run —
the READING half, the stored recursor type's binder data
(`mutualRdsAV`) and its reading package (`MutualRecData`).

`SumRecData` does NOT fit: its `len`/`read` are the ONE-motive shape
(`nP + n + nIdx + 2` binders, core `recConcAV n nIdx`), while a mutual
member's recursor carries `k` motives (`nP + k + n + nIdx + 1` binders,
core `mutualConcAV k n nIdx mm`) — the two coincide only at `k = 1`.
`MutualRecData` is the same six clauses at that shape, with
`SumRecData.cross`'s cons-crossing lemma repeated.

No cross-member parameter identification is needed for the READING:
`mutualRecTy` takes the parameter Πs from former `0` and the index Πs
from member `mm`, and the data names exactly those (`ppsOf 0`,
`ipsOf mm`).

The READING-FROM-THE-RUN half, in the order the stage needs it:

* `MutualFormerFacts` / `formerReadsM_of` — the members' reading
  premises (`FormerReadsM`) from their `FormerData`s and their stored
  records;
* `blockCtorRead_of` — ONE constructor's reading premise
  (`MutualCtorRead`) from its uniform datum (`BlockCtorData`) and the
  classified kinds: the datum's recursive positions are `recIdxOf` of
  its kinds and it names the fields' TARGETS directly (`Tof`,
  `nIdxOfT`), where the recursor's member table names them through
  `moti` — `htgt` is that the two agree.  `mutualRecFieldsOf_eq` is
  the same step for the generated constructor's `recFields`, which
  pairs the positions with their targets;
* `mutualRecData_of` — the stored recursor type's reading package and
  its universe, the kernel's own sort inference through the claims'
  sort row.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The stored recursor type's data -/

/-- Member `mm`'s generated recursor type's binder data at the block. -/
@[expose] def mutualRdsAV {env : Env} (m : EnvModel V env) (k nP : Nat) (ℓ : Level)
    (Lof : Nat → (Name → Nat) → AnnotTerm) (nIdxOf : Nat → Nat)
    (ppsOf ipsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (cds : (Name → Nat) → List CtorDatumR) (mots : Nat → Nat) (tgts : Nat → Nat → Nat)
    (mm : Nat) (ψ : Name → Nat) : List (Nat × Nat × AnnotTerm) :=
  mutualRecDataAV m ψ ((List.range k).map fun t => Lof t ψ) nP ((List.range k).map nIdxOf) ℓ
    (ppsOf 0 ψ) ((List.range k).map fun t => ipsOf t ψ) (cds ψ) mots tgts mm

/-- **Member `mm`'s generated recursor type's reading, peeled**
(`SumRecData` at `k` motives): the same six clauses, at the `k`-motive
length `nP + k + n + nIdx + 1` and the `k`-motive core
`mutualConcAV k n nIdx mm`.  At `k = 1` the two shapes agree
(`recConcAV_eq_mutualConcAV`); for `k > 1` they do not, so this is its
own record. -/
structure MutualRecData {env : Env} (m : EnvModel V env) (cvR : ConstantVal)
    (nP k n nIdx mm : Nat) (elimL : Level)
    (rds : (Name → Nat) → List (Nat × Nat × AnnotTerm)) : Prop where
  read : ∀ ψ : Name → Nat, denoteMeta m.acval env ψ 0 cvR.type
    = some (mkPisAV (rds ψ) (mutualConcAV k n nIdx mm))
  len : ∀ ψ : Name → Nat, (rds ψ).length = nP + k + n + nIdx + 1
  bits : ∀ (ψ : Name → Nat) (d : Nat × Nat × AnnotTerm), d ∈ rds ψ →
    (elimL.eval ψ = 0 ↔ d.2.1 = 0)
  okTy : ∀ (ψ : Name → Nat) (ρ : Nat → V),
    WellDenotedV V ρ (mkPisAV (rds ψ) (mutualConcAV k n nIdx mm))
  below : ∀ ψ : Name → Nat, DomsBelow 0 (rds ψ)
  params : ∀ ψ₁ ψ₂ : Name → Nat, (∀ p ∈ cvR.levelParams, ψ₁ p = ψ₂ p) →
    rds ψ₁ = rds ψ₂

/-- The data crosses a cons whose slot does not mention the stored
recursor (`SumRecData.cross`). -/
theorem MutualRecData.cross {m : EnvModel V env} {cvR : ConstantVal}
    {nP k n nIdx mm : Nat} {elimL : Level}
    {rds : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (h : MutualRecData m cvR nP k n nIdx mm elimL rds)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? c₀.name = none) (hat : ConsCrossAt c₀ cvR.type)
    (hcb : ConstsBound env cvR.type)
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval c₀.name A) :
    MutualRecData m₂ cvR nP k n nIdx mm elimL rds where
  read ψ := by
    rw [hac]
    exact denoteMeta_cons_mono hfresh hat ψ 0 hcb (h.read ψ)
  len := h.len
  bits := h.bits
  okTy := h.okTy
  below := h.below
  params := h.params

/-! ## The recursive positions of a mutual constructor -/

/-- A `filterMap` whose function is a guarded `some` is a filter and a
map. -/
theorem filterMap_if_eq {α β : Type} (p : α → Bool) (g : α → β) :
    ∀ l : List α, l.filterMap (fun a => if p a then some (g a) else none)
      = (l.filter p).map g
  | [] => rfl
  | a :: l => by
    cases h : p a with
    | true => simp [h, filterMap_if_eq p g l]
    | false => simp [h, filterMap_if_eq p g l]

omit [SetTheory V] in
/-- **The generated constructor's recursive fields are the datum's
recursive positions, re-paired with their targets**: `mutualRecFieldsOf`
walks the kinds with their targets, `recIdxOf` the kinds alone. -/
theorem mutualRecFieldsOf_eq (ks : List (RecFieldKind × Nat)) :
    ConLeche.mutualRecFieldsOf ks
      = (ConLeche.recIdxOf (kindsOf ks)).map fun i => (i, tgtAt ks i) := by
  unfold ConLeche.mutualRecFieldsOf ConLeche.recIdxOf
  rw [kindsOf_length, ← filterMap_if_eq
    (fun i => (kindsOf ks).getD i RecFieldKind.ordinary == RecFieldKind.recursive ||
      (kindsOf ks).getD i RecFieldKind.ordinary == RecFieldKind.reflexive)
    (fun i => (i, tgtAt ks i))]
  congr 1
  funext i
  by_cases hi : i < ks.length
  · rw [show ks.getD i (RecFieldKind.ordinary, 0) = (kindAt ks i, tgtAt ks i) from rfl,
      kindsOf_getD hi]
    cases hk : kindAt ks i <;> simp
  · have h1 : ks.getD i (RecFieldKind.ordinary, 0) = (.ordinary, 0) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    have h2 : (kindsOf ks).getD i RecFieldKind.ordinary = .ordinary := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [kindsOf_length]; omega)]
      rfl
    rw [h1, h2]
    simp

/-! ## The members' reading premises -/

/-- **What the stage knows about one member after the formers' stage**:
its former is stored at the block's level parameters with the
generators' type, its telescope ends in its result sort, and its
parameter/index data are its `FormerData`. -/
structure MutualFormerFacts {env : Env} (m : EnvModel V env) (lps : List Name) (nP : Nat)
    (f : ConLeche.MutualFormer) (cvTa : ConstantVal) (s : Level)
    (pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)) : Prop where
  find : ∃ caps : IndCaps, env.find? f.name = some (.indInfo cvTa caps)
  tty : cvTa.type = f.tty
  lps : cvTa.levelParams = lps
  strip : ∃ bs : List (Expr × BinderMeta),
    cvTa.type.stripPis (nP + f.nIdx) = some (bs, Expr.sort s)
  data : FormerData m cvTa (nP + f.nIdx) s pps

/-- **The members' reading premises**, from their facts: the leaf is
the stored former's value, the parameter block the telescope's first
`nP` entries and the index block the rest. -/
theorem formerReadsM_of {m : EnvModel V env} {lps : List Name} {nP : Nat}
    {Tname : Nat → Name} {nIdxOf : Nat → Nat}
    {cvTaOf : Nat → ConstantVal} {sOf : Nat → Level}
    {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {formers : List ConLeche.MutualFormer}
    (hT : ∀ t, t < formers.length → Tname t = (formers.getD t default).name)
    (hI : ∀ t, t < formers.length → nIdxOf t = (formers.getD t default).nIdx)
    (hf : ∀ t, t < formers.length →
      MutualFormerFacts m lps nP (formers.getD t default) (cvTaOf t) (sOf t) (ppsOf t))
    (ψ : Name → Nat) :
    FormerReadsM m ψ lps nP (fun t => m.acval (Tname t) ψ) nIdxOf
      (fun t => (ppsOf t ψ).take nP) (fun t => (ppsOf t ψ).drop nP) formers := by
  intro t ht
  obtain ⟨⟨caps, hfind⟩, htty, hlps, ⟨bs, hstrip⟩, hD⟩ := hf t ht
  obtain ⟨hCf, -, -, hCb, -⟩ := m.wf _ (ConLeche.Semantics.Env.find?_mem hfind)
  simp only [ConstantInfo.toConstantVal] at hCf hCb
  have hname : Tname t = (formers.getD t default).name := hT t ht
  have hidx : nIdxOf t = (formers.getD t default).nIdx := hI t ht
  have hstripS : ((formers.getD t default).tty.stripPis
      (nP + (formers.getD t default).nIdx)).isSome = true := by
    rw [← htty, hstrip]; rfl
  refine ⟨⟨.indInfo (cvTaOf t) caps, hfind, hlps⟩, by show m.acval (Tname t) ψ = _; rw [hname],
    hidx, by rw [← htty]; exact hCf, by rw [← htty]; exact hCb, ?_, hstripS,
    ⟨ppsOf t ψ, (sOf t).eval ψ, by rw [← htty]; exact hD.read ψ, by rw [hD.len ψ], rfl, rfl⟩⟩
  obtain ⟨⟨tbs, itele⟩, hq⟩ := Option.isSome_iff_exists.mp
    (ConLeche.stripPis_isSome_of_le (Nat.le_add_right _ _) hstripS)
  exact ⟨tbs, itele, hq⟩

/-! ## The constructors' reading premises -/

/-- **One constructor's reading premise, from the uniform datum**
(`fixCtorReadsR_of` at ONE position with a per-field TARGET member).
The datum names the fields' targets directly (`Tof`, `nIdxOfT`); the
recursor's member table names them through `moti`, and `htgt` is what
the earlier stages know: at a recursive position the two agree. -/
theorem blockCtorRead_of {m : EnvModel V env} {env₀ : Env} {T : Name} {Tof : Nat → Name}
    {nIdxOfT : Nat → Nat} {lps : List Name} {cA : ConstantVal × Nat} {nP nIdx : Nat}
    {resSort : Level} {isProp large : Bool} {idxArgs : List Expr}
    {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    {srcs : List (Option Nat)} {ks : List RecFieldKind} {fvsP xFvs : List Expr} {xrest : Expr}
    {Eiss : (Name → Nat) → List (List AnnotTerm)}
    {tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (ψ : Name → Nat)
    (hf : env.find? cA.1.name = some (.ctorInfo cA.1 nP cA.2)) (hlps : cA.1.levelParams = lps)
    (hD : BlockCtorData m env₀ T Tof nIdxOfT lps cA.1 nP cA.2 nIdx resSort isProp large idxArgs
      ds Es srcs ks fvsP xFvs xrest Eiss tss)
    {Tname : Nat → Name} {nIdxOf : Nat → Nat} {mot : Nat} {moti : Nat → Nat}
    (hT : Tname mot = T) (hI : nIdxOf mot = nIdx)
    (htgt : ∀ i ∈ ConLeche.recIdxOf ks, Tname (moti i) = Tof i ∧ nIdxOf (moti i) = nIdxOfT i) :
    MutualCtorRead m ψ lps nP Tname nIdxOf mot moti
      ⟨cA.1.name, cA.2, cA.1.type, mot, (ConLeche.recIdxOf ks).map fun i => (i, moti i)⟩
      (cA.1.name, cA.2, ds ψ, Es ψ, ConLeche.recIdxOf ks, Eiss ψ, tss ψ) := by
  obtain ⟨hCf, -, -, hCb, -⟩ := m.wf _ (ConLeche.Semantics.Env.find?_mem hf)
  simp only [ConstantInfo.toConstantVal] at hCf hCb
  have hksLen := hD.ksLen
  -- a recursive position is a field
  have hmemF : ∀ i, i ∈ ConLeche.recIdxOf ks →
      i < cA.2 ∧ (ks.getD i .ordinary = .recursive ∨ ks.getD i .ordinary = .reflexive) := by
    intro i hi
    obtain ⟨hlt, hk⟩ := mem_recIdxOf.mp hi
    rw [hksLen] at hlt
    exact ⟨hlt, hk⟩
  -- the opening
  obtain ⟨crest, hopP, hopX⟩ := hD.opens
  have hopAll : openPisAtFvars (nP + cA.2) cA.1.type 0 = some (fvsP ++ xFvs, xrest) :=
    openPisAtFvars_add nP hopP (by rw [Nat.zero_add]; exact hopX)
  obtain ⟨cbs, es, hst, -⟩ := hD.resid
  have hlenAll : (fvsP ++ xFvs).length = nP + cA.2 := by
    rw [List.length_append, hD.pLen, hD.xLen]
  have hidxAll := (opening_vars_at hopAll).2.1
  have hxAt : ∀ (i' : Nat), i' < cA.2 → ∀ x, xFvs[i']? = some x →
      (fvsP ++ xFvs)[nP + i']? = some x := by
    intro i' hi' x hx
    rw [List.getElem?_append_right (by rw [hD.pLen]; omega), hD.pLen, Nat.add_sub_cancel_left]
    exact hx
  have hfvL : ∀ (i' : Nat), ∀ a ∈ (fvsP ++ xFvs).take (nP + i'),
      ∃ (k : Nat) (ty : Expr), a = Expr.fvar k ty := by
    intro i' a ha
    obtain ⟨q, hq⟩ := List.getElem?_of_mem (List.mem_of_mem_take ha)
    obtain ⟨ty, rfl⟩ := hidxAll q a hq
    exact ⟨_, ty, rfl⟩
  have hbGet : ∀ (i' : Nat), i' < cA.2 → ∃ b, cbs[nP + i']? = some b ∧
      cbs.getD (nP + i') default = b := by
    intro i' hi'
    have hlt : nP + i' < cbs.length := by rw [ConLeche.Expr.stripPis_length _ hst]; omega
    exact ⟨_, List.getElem?_eq_getElem hlt, by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl⟩
  have hpb : ∀ (i' : Nat), i' < cA.2 → ∀ x, xFvs[i']? = some x →
      ∀ b, cbs[nP + i']? = some b →
        (x.fvarTypeD.piBinders).1.length = (b.1.piBinders).1.length ∧
        (x.fvarTypeD.piBinders).2.getAppArgs.length
          = (b.1.piBinders).2.getAppArgs.length := by
    intro i' hi' x hx b hb
    have hty := openPisAtFvars_fvarTypeD (nP + cA.2) hopAll hst (nP + i') b x hb
      (hxAt i' hi' x hx)
    have hlenTake : ((fvsP ++ xFvs).take (nP + i')).length = nP + i' := by
      rw [List.length_take, hlenAll]
      omega
    obtain ⟨h1, h2⟩ := Expr.piBinders_instSeq ((fvsP ++ xFvs).take (nP + i'))
      (nP + i' - 1) b.1 (hfvL i') (by rw [hlenTake]; omega)
    rw [hty]
    refine ⟨h1, ?_⟩
    rw [h2, Expr.getAppArgs_instSeq_fvars _ _ _ (hfvL i'), List.length_map]
  refine ⟨rfl, rfl, rfl, rfl, ⟨_, hf, hlps⟩, hCf, hCb, by rw [hT, hI]; exact hD.resid,
    by rw [hT]; exact hD.read ψ, hD.len ψ, by rw [hI]; exact hD.lenE ψ, rfl, ?_,
    recIdxOf_pairwise _, hD.eissLen ψ, ?_, hD.tssLen ψ, ?_, ?_, ?_, ?_⟩
  · exact fun i' hi' => (hmemF i' hi').1
  · -- the index readings' count, at the field's TARGET member
    intro i' hi'
    obtain ⟨hlt, hk⟩ := hmemF i' hi'
    rw [(htgt i' hi').2]
    rcases hk with hk | hk
    · exact hD.eisLen ψ i' hk hlt
    · exact hD.eisLenRefl ψ i' hk hlt
  · -- the telescope's length: the raw binder type's own `∀`-binders
    intro i' hi'
    obtain ⟨hlt, hk⟩ := hmemF i' hi'
    obtain ⟨x, hx⟩ : ∃ x, xFvs[i']? = some x :=
      ⟨_, List.getElem?_eq_getElem (by rw [hD.xLen]; exact hlt)⟩
    obtain ⟨b, hb, hbd⟩ := hbGet i' hlt
    have hteleEq : ConLeche.structFieldTeleOf cA.1.type nP cA.2 i' = (b.1.piBinders).1 := by
      unfold ConLeche.structFieldTeleOf
      rw [hst]
      simp only [List.getD_eq_getElem?_getD, hb, Option.getD_some]
    rw [hteleEq, ← (hpb i' hlt x hx b hb).1]
    rcases hk with hk | hk
    · obtain ⟨hfn, -, -, -, -, -⟩ := hD.opened.recF i' x hx hk
      rw [Expr.piBinders_nil_of_getAppFn_const hfn,
        hD.tssNone ψ i' (fun h => by rw [hk] at h; exact nomatch h)]
      rfl
    · obtain ⟨afvs, body, -, hlenTl, -, -⟩ := hD.reflOpen ψ i' x hx hk
      rw [hlenTl]
  · -- a field's domain reads to its entry
    intro i' hi' fvs o hop x hx
    obtain ⟨hlt, -⟩ := hmemF i' hi'
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj (hop.symm.trans hopAll))
    rw [List.getElem?_append_right (by rw [hD.pLen]; omega), hD.pLen,
      Nat.add_sub_cancel_left] at hx
    exact hD.domRead ψ i' x hx
  · -- the domain's argument count, under the field's own telescope
    intro i' hi' cbs' body' hst'
    obtain ⟨hlt, hk⟩ := hmemF i' hi'
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj (hst'.symm.trans hst))
    obtain ⟨x, hx⟩ : ∃ x, xFvs[i']? = some x :=
      ⟨_, List.getElem?_eq_getElem (by rw [hD.xLen]; exact hlt)⟩
    obtain ⟨b, hb, hbd⟩ := hbGet i' hlt
    rw [hbd, ← (hpb i' hlt x hx b hb).2, (htgt i' hi').2]
    rcases hk with hk | hk
    · obtain ⟨hfn, -, hlenA, -, -, -⟩ := hD.opened.recF i' x hx hk
      rw [Expr.piBinders_nil_body (Expr.piBinders_nil_of_getAppFn_const hfn)]
      exact hlenA
    · obtain ⟨afvs, body, hop, -, -, -, -, hlenA, -, -, -⟩ := hD.opened.reflF i' x hx hk
      have hbody := openPisAtFvars_instSeq (x.fvarTypeD.piBinders).1.length hop
        (Expr.stripPis_piBinders x.fvarTypeD)
      have hfvA : ∀ a ∈ afvs, ∃ (k : Nat) (ty : Expr), a = Expr.fvar k ty := by
        intro a ha
        obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
        obtain ⟨ty, rfl⟩ := (opening_vars_at hop).2.1 q a hq
        exact ⟨_, ty, rfl⟩
      rw [hbody, Expr.getAppArgs_instSeq_fvars _ _ _ hfvA, List.length_map] at hlenA
      exact hlenA
  · -- a field's entry, at the field's TARGET member
    intro i' hi'
    obtain ⟨hlt, hk⟩ := hmemF i' hi'
    rw [(htgt i' hi').1]
    rcases hk with hk | hk
    · rw [hD.tssNone ψ i' (fun h => by rw [hk] at h; exact nomatch h),
        hD.recEntry ψ i' hk hlt]
      rfl
    · exact hD.reflEntry ψ i' hk hlt

/-! ## The stored recursor type's data, from the run -/

/-- **Member `mm`'s recursor data**, read off the generated type, and
its universe: the kernel's sort inference at the pre-recursor
environment, through the claims' sort row. -/
theorem mutualRecData_of (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {F : Nat} {b : ConLeche.MutualBlock} {formers4 : List ConLeche.MutualFormer}
    {ctors4 : List ConLeche.MutualCtor4}
    {mm : Nat} {streamRec : Option ConstantVal} {cvRa : ConstantVal}
    (hRec : ConLeche.checkMutualRecTy (ConLeche.fueledOps μ F) env b formers4 ctors4 mm streamRec
      = .ok cvRa)
    {Tname : Nat → Name} {nIdxOf : Nat → Nat} {mots : Nat → Nat} {tgts : Nat → Nat → Nat}
    {Lof : Nat → (Name → Nat) → AnnotTerm}
    {ppsOf ipsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {cds : (Name → Nat) → List CtorDatumR}
    (hformers : ∀ ψ : Name → Nat, FormerReadsM mp.base2 ψ b.lps b.nP (fun t => Lof t ψ) nIdxOf
      (fun t => ppsOf t ψ) (fun t => ipsOf t ψ) formers4)
    (hctors : ∀ ψ : Name → Nat,
      MutualCtorReadsM mp.base2 ψ b.lps b.nP Tname nIdxOf mots tgts ctors4 (cds ψ))
    (hmots : ∀ J, J < ctors4.length → mots J < formers4.length)
    (hfT : ∀ q : Nat, ∃ ci : ConstantInfo,
      env.find? (Tname q) = some ci ∧ ci.toConstantVal.levelParams = b.lps)
    (hmm : mm < formers4.length) :
    MutualRecData mp.base2 cvRa b.nP formers4.length ctors4.length (nIdxOf mm) mm b.elimLevel
        (mutualRdsAV mp.base2 formers4.length b.nP b.elimLevel Lof nIdxOf ppsOf ipsOf cds mots
          tgts mm) ∧
      ∃ u : Level, ∀ (ψ : Name → Nat) (ρ : Nat → V),
        interp V ρ (mkPisAV (mutualRdsAV mp.base2 formers4.length b.nP b.elimLevel Lof nIdxOf
            ppsOf ipsOf cds mots tgts mm ψ)
          (mutualConcAV formers4.length ctors4.length (nIdxOf mm) mm)) ∈ˢ
          (univ (u.eval ψ) : V) := by
  obtain ⟨recTy, sty, u, hgen, htp, -, hbt, hRf, hsty, hens, -, rfl⟩ :=
    ConLeche.checkMutualRecTy_shape hRec
  have h0lt : 0 < formers4.length := by omega
  -- the reading
  have hread : ∀ ψ : Name → Nat, denoteMeta mp.base2.acval env ψ 0 recTy
      = some (mkPisAV (mutualRdsAV mp.base2 formers4.length b.nP b.elimLevel Lof nIdxOf ppsOf
          ipsOf cds mots tgts mm ψ)
        (mutualConcAV formers4.length ctors4.length (nIdxOf mm) mm)) := fun ψ =>
    denoteMeta_mutualRecTy (hformers ψ) (hctors ψ) hmots hfT hgen
  -- the parameter and index blocks' lengths
  have hp : ∀ ψ : Name → Nat, (ppsOf 0 ψ).length = b.nP := by
    intro ψ
    obtain ⟨ppsAll, w, -, hlenP, hpps, -⟩ := ((hformers ψ) 0 h0lt).read
    rw [show ppsOf 0 ψ = (fun t => ppsOf t ψ) 0 from rfl, hpps, List.length_take, hlenP]
    omega
  have hi : ∀ ψ : Name → Nat, (ipsOf mm ψ).length = nIdxOf mm := by
    intro ψ
    obtain ⟨ppsAll, w, -, hlenP, -, hips⟩ := ((hformers ψ) mm hmm).read
    rw [show ipsOf mm ψ = (fun t => ipsOf t ψ) mm from rfl, hips, List.length_drop, hlenP,
      ((hformers ψ) mm hmm).idxCount]
    omega
  have hlenC : ∀ ψ : Name → Nat, (cds ψ).length = ctors4.length :=
    fun ψ => (hctors ψ).length_eq
  have hlen : ∀ ψ : Name → Nat,
      (mutualRdsAV mp.base2 formers4.length b.nP b.elimLevel Lof nIdxOf ppsOf ipsOf cds mots
        tgts mm ψ).length
        = b.nP + formers4.length + ctors4.length + nIdxOf mm + 1 := by
    intro ψ
    unfold mutualRdsAV
    rw [mutualRecDataAV_length (hp ψ), List.length_map, List.length_range, hlenC ψ,
      getD_range_map _ _ _ hmm [], hi ψ]
  have hw : Expr.WScoped 0 recTy := Expr.WScoped.of_not_hasFvar hRf
  have hL : Expr.LeavesBounded recTy := Expr.LeavesBounded.of_not_hasFvar hRf
  have hnil : recTy.fvarLeaves = [] := Expr.fvarLeaves_eq_nil_of_not_hasFvar hRf
  refine ⟨⟨hread, hlen, ?_, ?_, ?_, ?_⟩, u, fun ψ ρ => ?_⟩
  · intro ψ d hd
    unfold mutualRdsAV at hd
    rw [mem_mutualRecDataAV hd, pwBit_eq_zero_iff, ConLeche.PropWhen.zeronessOf_sound,
      beq_iff_eq]
  · intro ψ ρ
    have hc := claimsAt_of hμ mp ψ F
    obtain ⟨-, -, hokT, -, -⟩ := hc.inferRow hsty hw hbt hL (CtxOk.nil hnil) (hread ψ)
    exact hokT ρ (Sat_nil V ρ)
  · intro ψ
    have hst := stripPisAV_mkPisAV (mutualRdsAV mp.base2 formers4.length b.nP b.elimLevel Lof
      nIdxOf ppsOf ipsOf cds mots tgts mm ψ)
      (mutualConcAV formers4.length ctors4.length (nIdxOf mm) mm)
    exact (stripPisAV_below hst (bvarsBelow_of_reading hw hbt (hread ψ))).1
  · intro ψ₁ ψ₂ hφ
    have h2 := hread ψ₂
    have h1 : denoteMeta mp.base2.acval env ψ₂ 0 recTy
        = some (mkPisAV (mutualRdsAV mp.base2 formers4.length b.nP b.elimLevel Lof nIdxOf ppsOf
            ipsOf cds mots tgts mm ψ₁)
          (mutualConcAV formers4.length ctors4.length (nIdxOf mm) mm)) := by
      rw [← denoteMeta_params_ext mp.base2 hφ 0 recTy htp]
      exact hread ψ₁
    exact (mkPisAV_inj (by rw [hlen ψ₁, hlen ψ₂]) (Option.some.inj (h1.symm.trans h2))).1
  · have hc := claimsAt_of hμ mp ψ F
    exact (hc.sortRow hsty hens hw hbt hL (CtxOk.nil hnil) (hread ψ) ρ (Sat_nil V ρ)).2

end ConLeche.Model
