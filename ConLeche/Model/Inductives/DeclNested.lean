module

public import ConLeche.Model.Inductives.DeclMutual
public import ConLeche.Semantics.Inductives.DeclNested
import ConLeche.Verify.Inductives.NestedFacts
import ConLeche.Verify.Extend.Inversions
public section

/-!
# The nested install, assembled (task #279, model lane)

`declNested`: the P carrier survives the nested install's run
(`DeclNestedRun`, `ConLeche/Semantics/Inductives/DeclNested.lean`).
The proof is staged along the run relation, and what is here is its
first stage:

**The auxiliary block's model** (`nestedAuxModel`).  The elimination's
auxiliary block `b` is an ordinary mutual block checked by
`checkMutualCore … b none` in a SCRATCH environment `envAux`, so
task #278's `declMutualCore` models it — at a `MutualParts` whose
`toBlock` is `b` (`auxParts`), and with the three recursor-name facts
the core theorem takes as hypotheses discharged from the nested run
itself: for a REAL member `T` its restored recursor `T.rec` went
through `checkConstantVal` at the restored environment
(`restoreRecTys`, post-check (b)), which is a fresh, unreserved,
non-projection name carried back to the pre-block environment through
the formers' and constructors' conses; for a COPY, its recursor is
free by the kernel's `copiesFresh` conjunct, unreserved because its
FORMER's name — which `mutualFormers` checked — is unreserved and the
reserved list closes under `.rec` (`reserved_of_str_rec`), and never
projection-shaped under `.str "rec"`.  The result is the model
`mpAux : EnvModelM V μ envAux` together with the block's
representations at it (`MutualBlockReps`, task #279 M-B′ step 3c (c):
ONE datum for the scratch block — every member and copy real, the
pins the parameter variables — and each member's `IndRep` at it, with
`fibre`/`leaf`/`ctor`/`mkInj` and, through M-A′, the recursors'
`recRead`/`rulesRead`), which the later stages read.

The stages that follow (DESIGN §M.10): the copy ↔ container-family map
over `st.pins` with the one `elimNested` lemma (a copy's constructor
fields are the container's at the pin), the fold spellings `ψ`/`ψ⁻¹`
(M-B′), the round trips (M-C′), the restored leaves with `T`'s honest
representation (M-D′), and the assembly into `declNested` (M-E).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps
  MutualParts MutualBlock MutualFormerA MutualFormer MutualCtor MutualCtor4 BinderMeta RecRule
  NestedParts ElimState AuxType AuxStored)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## The auxiliary block as a `MutualParts` -/

/-- A block record dressed as a recognised mutual block, so that
`declMutualCore` — whose text is over `p.toBlock` — applies to it: the
members carry the formers with dummy recursor records (the core theorem
never reads them). -/
def auxParts (b : MutualBlock) : MutualParts :=
  ⟨b.formers.map fun q => ⟨q.1, q.2, default, 0, 0, []⟩, b.ctors, b.nP, b.lps, b.large, b.elim,
    false⟩

/-- The dressing is invisible to `toBlock`. -/
theorem auxParts_toBlock (b : MutualBlock) : (auxParts b).toBlock = b := by
  cases b with
  | mk formers ctors nP lps large elim =>
    simp [auxParts, MutualParts.toBlock, List.map_map, Function.comp_def]

/-! ## The block's own types, as the elimination takes them -/

/-- The block's own types as `elimNested` takes them (the run relation's
spelling): member `mIdx`'s former with its own constructors. -/
theorem nestedTypes0_getElem? (p : NestedParts) (t : Nat) :
    (p.formers.zipIdx.map fun ((cv, _), mIdx) =>
        (⟨cv.name, cv.type,
          (p.ctors.filter (fun (c : MutualCtor) => c.member == mIdx)).map
            fun (c : MutualCtor) => (c.cv.name, c.cv.type, c.nF)⟩ : AuxType))[t]?
      = (p.formers[t]?).map fun (cv, _) =>
        (⟨cv.name, cv.type,
          (p.ctors.filter (fun (c : MutualCtor) => c.member == t)).map
            fun (c : MutualCtor) => (c.cv.name, c.cv.type, c.nF)⟩ : AuxType) := by
  rw [List.getElem?_map, List.getElem?_zipIdx]
  cases p.formers[t]? with
  | none => rfl
  | some q => simp

/-- The block's own types are as many as its formers. -/
theorem nestedTypes0_length (p : NestedParts) :
    (p.formers.zipIdx.map fun ((cv, _), mIdx) =>
        (⟨cv.name, cv.type,
          (p.ctors.filter (fun (c : MutualCtor) => c.member == mIdx)).map
            fun (c : MutualCtor) => (c.cv.name, c.cv.type, c.nF)⟩ : AuxType)).length = p.k := by
  simp [NestedParts.k]

/-! ## The auxiliary block's model -/

/-- **The three recursor-name facts of the scratch block**, read off the
run (see the module docstring): fresh before the block, unreserved, not
projection-shaped. -/
theorem nestedRecNameFacts {F : Nat} {env envAux : Env}
    {p : NestedParts} {st₀ st : ElimState} {b : MutualBlock} {stored : List AuxStored}
    {ctorsR : List (List (ConstantVal × Nat × Nat))} {cvRms : List ConstantVal}
    {pinsA : List (ConLeche.NestedPin × Expr)}
    (helim : ConLeche.elimNested env p.nP p.lps
      (p.formers.zipIdx.map fun ((cv, _), mIdx) =>
        (⟨cv.name, cv.type,
          (p.ctors.filter (fun (c : MutualCtor) => c.member == mIdx)).map
            fun (c : MutualCtor) => (c.cv.name, c.cv.type, c.nF)⟩ : AuxType)) = .ok st₀)
    (hremint : ConLeche.nestedRemint (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env p st₀
      = .ok (st, pinsA))
    (hfresh : ConLeche.copiesFresh env p.k st = true)
    (hb : ConLeche.auxBlock p st = some b)
    (hcore : ConLeche.checkMutualCore (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env b none
      true = .ok envAux)
    (hstored : ConLeche.auxStoredAll envAux b b.k = some stored)
    (hrm : ConLeche.restoreRecTys (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
        (ConLeche.consNestedCtors ctorsR.flatten
          (ConLeche.consNestedFormers (stored.take p.k) env))
        (ConLeche.restoreTbl p st) p.lps
        ((List.range p.k).map fun mIdx => ((p.formers.getD mIdx default).1.name.str "rec"))
        (stored.take p.k) = .ok cvRms) :
    ∀ t, t < b.k →
      env.find? (b.recName t) = none ∧
      ConLeche.reservedBasisNames.contains (b.recName t) = false ∧
      (b.recName t).isProjFnShape = false := by
  have hrun : DeclMutualCoreRun μ F env b none true envAux := declMutualCoreRun_of hcore
  -- the block's shape
  have hk : b.k = st.types.length := ConLeche.auxBlock_k hb
  obtain ⟨hpins, -, hlenT, -, -⟩ := ConLeche.nestedRemint_inv hremint
  have hlenSt : st.types.length = p.k + st.pins.length := by
    have := ConLeche.elimNested_length helim
    rw [nestedTypes0_length] at this
    rw [hlenT, hpins]; exact this
  obtain ⟨hstoredLen, -⟩ := ConLeche.auxStoredAll_inv hstored
  have hkp : p.k ≤ b.k := by omega
  -- the formers' checks in the scratch run: every auxiliary former's
  -- name went through a front door at the pre-block environment
  -- (`FormerFront`, either grade — K.10)
  have hformerName : ∀ t, t < b.k → ∀ ty, st.types[t]? = some ty →
      ConLeche.reservedBasisNames.contains ty.name = false := by
    obtain ⟨env₁, fms, f₀, tq₀, ctorsA, sortss, kinds, formers4, ctors4, cvRas, rulesOf,
      -, -, -, -, hformers, -, -, -, -, -, -, -, -, -, -, -⟩ := hrun
    obtain ⟨hchecks, -⟩ := ConLeche.mutualFormers_inv hformers
    obtain ⟨hlenFms, hposF⟩ := ConLeche.mutualFormerChecks_front hchecks
    intro t ht ty hty
    obtain ⟨-, -, -, -, -, hall, -⟩ := ConLeche.auxBlock_inv hb
    obtain ⟨nIdx, -, hf⟩ := hall t ty hty
    have htf : t < fms.length := by
      rw [hlenFms]; exact ht
    obtain ⟨f, hft⟩ : ∃ f, fms[t]? = some f := ⟨_, List.getElem?_eq_getElem htf⟩
    obtain ⟨cv, bs, hl, hff, -⟩ := hposF t f hft
    rw [hf] at hl
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hl)
    exact hff.nres
  intro t ht
  obtain ⟨ty, hty⟩ : ∃ ty, st.types[t]? = some ty :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hrecName : b.recName t = ty.name.str "rec" := ConLeche.auxBlock_recName hb hty
  rw [hrecName]
  rcases Nat.lt_or_ge t p.k with htk | htk
  · -- a REAL member: its restored recursor went through `checkConstantVal`
    have hname : ty.name = (p.formers.getD t default).1.name := by
      have h1 := ConLeche.elimNested_name_lt helim (t := t) (by rw [nestedTypes0_length]; exact htk)
      rw [← ConLeche.nestedRemint_name hremint, hty, nestedTypes0_getElem?] at h1
      obtain ⟨q, hq⟩ : ∃ q, p.formers[t]? = some q :=
        ⟨_, List.getElem?_eq_getElem (by simpa [NestedParts.k] using htk)⟩
      rw [hq] at h1
      simp only [Option.map_some, Option.some.injEq] at h1
      rw [h1, List.getD_eq_getElem?_getD, hq]
      rfl
    obtain ⟨hlenR, hallR⟩ := ConLeche.restoreRecTys_inv hrm
    obtain ⟨a, ha⟩ : ∃ a, (stored.take p.k)[t]? = some a :=
      ⟨_, List.getElem?_eq_getElem (by rw [List.length_take_of_le (by omega)]; exact htk)⟩
    obtain ⟨tyR, cvA, -, hccv, -⟩ := hallR t a ha
    obtain ⟨hfind, hres, hsh, -⟩ := ConLeche.checkConstantVal_inv hccv
    have hnm : (((List.range p.k).map fun mIdx =>
        ((p.formers.getD mIdx default).1.name.str "rec")).drop t).headD a.cvRa.name
          = ty.name.str "rec" := by
      rw [List.headD_eq_head?_getD, List.head?_drop, List.getElem?_map,
        List.getElem?_range htk, hname]
      rfl
    simp only [hnm] at hfind hres hsh
    exact ⟨ConLeche.consNestedFormers_find?_none (ConLeche.consNestedCtors_find?_none hfind),
      hres, hsh⟩
  · -- a COPY: free by `copiesFresh`, unreserved through its former
    have hmem : ty ∈ st.types.drop p.k := by
      refine List.mem_of_getElem? (i := t - p.k) ?_
      rw [List.getElem?_drop, Nat.add_sub_cancel' htk]
      exact hty
    obtain ⟨-, hfreeRec, -⟩ := ConLeche.copiesFresh_inv hfresh ty hmem
    refine ⟨hfreeRec, ?_, ConLeche.isProjFnShape_str_rec _⟩
    cases hc : ConLeche.reservedBasisNames.contains (ty.name.str "rec") with
    | false => rfl
    | true =>
      have := ConLeche.reserved_of_str_rec hc
      rw [hformerName t ht ty hty] at this
      exact nomatch this

/-- **The auxiliary block's model**: the scratch environment of a
nested run carries the P invariant.  `declMutualCore` at the auxiliary
block, its recursor-name facts read off the run (see the module
docstring). -/
theorem nestedAuxModel (hμ : μ.verifiedChecks = true) {F : Nat} {env envAux : Env}
    {p : NestedParts} {st₀ st : ElimState} {b : MutualBlock} {stored : List AuxStored}
    {ctorsR : List (List (ConstantVal × Nat × Nat))} {cvRms : List ConstantVal}
    {pinsA : List (ConLeche.NestedPin × Expr)}
    (mp : EnvModelM V μ env) (hE : ConLeche.EtaFamiliesClosed env)
    (helim : ConLeche.elimNested env p.nP p.lps
      (p.formers.zipIdx.map fun ((cv, _), mIdx) =>
        (⟨cv.name, cv.type,
          (p.ctors.filter (fun (c : MutualCtor) => c.member == mIdx)).map
            fun (c : MutualCtor) => (c.cv.name, c.cv.type, c.nF)⟩ : AuxType)) = .ok st₀)
    (hremint : ConLeche.nestedRemint (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env p st₀
      = .ok (st, pinsA))
    (hfresh : ConLeche.copiesFresh env p.k st = true)
    (hb : ConLeche.auxBlock p st = some b)
    (hcore : ConLeche.checkMutualCore (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env b none
      true = .ok envAux)
    (hstored : ConLeche.auxStoredAll envAux b b.k = some stored)
    (hrm : ConLeche.restoreRecTys (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
        (ConLeche.consNestedCtors ctorsR.flatten
          (ConLeche.consNestedFormers (stored.take p.k) env))
        (ConLeche.restoreTbl p st) p.lps
        ((List.range p.k).map fun mIdx => ((p.formers.getD mIdx default).1.name.str "rec"))
        (stored.take p.k) = .ok cvRms) :
    ∃ (mpAux : EnvModelM V μ envAux) (d : IndRepData V), MutualBlockReps mpAux.base2 b d := by
  have hrun : DeclMutualCoreRun μ F env b none true envAux := declMutualCoreRun_of hcore
  have hfacts := nestedRecNameFacts helim hremint hfresh hb hcore hstored hrm
  -- `declMutualCore` at the dressed block
  have hq : (auxParts b).toBlock = b := auxParts_toBlock b
  obtain ⟨mpAux, d, hreps⟩ := declMutualCore (p := auxParts b) hμ mp hE (by rw [hq]; exact hrun)
    (fun t ht => by rw [hq] at ht ⊢; exact (hfacts t ht).1)
    (fun t ht => by rw [hq] at ht ⊢; exact (hfacts t ht).2.1)
    (fun t ht => by rw [hq] at ht ⊢; exact (hfacts t ht).2.2)
  rw [hq] at hreps
  exact ⟨mpAux, d, hreps⟩

/-! ## The stored formers are the checked ones (K.10, DESIGN §M.25 piece 3)

`nestedCopyFormerType_eq` identifies a copy's stored FORMER with the
checked one `fms[i]`, consed by `consMutualFormers`; what the model
reads is `envAux.find?`, three stages later.  The stages after the
formers' conses are fresh extensions by non-formers (`FreshEtaExt`), and
a fresh extension preserves every lookup it does not shadow. -/

/-- A fresh extension keeps every existing lookup. -/
theorem FreshEtaExt.find?_some {env env' : Env} (h : FreshEtaExt env env') {n : Name}
    {c : ConstantInfo} (hf : env.find? n = some c) : env'.find? n = some c := by
  obtain ⟨new, hc, hfresh, -⟩ := h
  rw [find?_append_of_new_none hc, hf]
  rw [List.find?_eq_none]
  intro c' hc' hn
  have hn' : c'.name = n := beq_iff_eq.mp hn
  have := hfresh c' hc'
  rw [hn', hf] at this
  exact nomatch this

/-- **Every checked former is stored at the scratch environment** as
the mutual install consed it (with the empty capability record): from
the run's formers stage, the block's name discipline, and the three
later stages' fresh extensions (the recursors' names fresh at the
pre-block environment, as the nested run supplies them). -/
theorem auxFormers_stored {F : Nat} {env envAux : Env} {b : MutualBlock} {auxRoute : Bool}
    (hrun : DeclMutualCoreRun μ F env b none auxRoute envAux)
    (hfreshRec : ∀ t, t < b.k → env.find? (b.recName t) = none) :
    ∃ fms : List MutualFormerA,
      ConLeche.mutualFormers (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) b.nP b.formers env
        auxRoute = .ok (ConLeche.consMutualFormers fms env, fms) ∧
      fms.length = b.k ∧
      (∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
        ∃ (cv : ConstantVal) (bs : List (Expr × BinderMeta)),
          b.formers[t]? = some (cv, f.nIdx) ∧ ConLeche.FormerFront μ F env cv f.cvTa ∧
          f.cvTa.type.stripPis (b.nP + f.nIdx) = some (bs, .sort f.s)) ∧
      ∀ f ∈ fms, envAux.find? f.cvTa.name = some (.indInfo f.cvTa {}) := by
  obtain ⟨env₁, fms, f₀, tq₀, ctorsA, sortss, kinds, formers4, ctors4, cvRas, rulesOf, hNodup,
    -, -, -, hformers, -, -, -, -, hctors, -, -, -, hrectys, -, htbl⟩ := hrun
  obtain ⟨hchecks, rfl⟩ := ConLeche.mutualFormers_inv hformers
  obtain ⟨hlenFms, hposF⟩ := ConLeche.mutualFormerChecks_front hchecks
  have hkF : fms.length = b.k := hlenFms
  -- the checked members carry the declared names
  have hnamesF : fms.map (·.cvTa.name) = b.memberNames := by
    refine List.ext_getElem? fun t => ?_
    rw [List.getElem?_map]
    cases hft : fms[t]? with
    | none =>
      have hn : b.formers[t]? = none := by
        rw [List.getElem?_eq_none_iff] at hft ⊢
        exact (by rw [← hkF]; exact hft : b.k ≤ t)
      simp [ConLeche.MutualBlock.memberNames, List.getElem?_map, hn]
    | some f =>
      obtain ⟨cv, bs, hl, hff, -⟩ := hposF t f hft
      simp [ConLeche.MutualBlock.memberNames, List.getElem?_map, hl, hff.name]
  have hNd := hNodup
  unfold ConLeche.MutualBlock.blockNames at hNd
  obtain ⟨hNd₁, hNdRec, hdisj⟩ := List.nodup_append.mp hNd
  obtain ⟨hNdM, hNdC, hdisjMC⟩ := List.nodup_append.mp hNd₁
  have hndF : (fms.map (·.cvTa.name)).Nodup := by rw [hnamesF]; exact hNdM
  -- the constructors' checked names are the declared ones
  obtain ⟨hlenA, -, hallC⟩ := ConLeche.checkMutualCtors_inv hctors
  have hctorNames : ∀ cA ∈ ctorsA, cA.1.name ∈ b.ctors.map (·.cv.name) := by
    intro cA hcA
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hcA
    have hjl : j < b.ctors.length := by rw [← hlenA]; exact (List.getElem?_eq_some_iff.mp hj).1
    obtain ⟨c, hc⟩ : ∃ c, b.ctors[j]? = some c := ⟨_, List.getElem?_eq_getElem hjl⟩
    obtain ⟨-, sorts, -, hrunJ⟩ := hallC j c cA hc hj
    obtain ⟨⟨ty', hccv⟩, -, -⟩ := ConLeche.checkMutualCtor_shape hrunJ
    have hn : cA.1.name = c.cv.name := (ConLeche.FormerFront.of_checkConstantVal hccv).name
    rw [hn]
    exact List.mem_map_of_mem (List.mem_of_getElem? hc)
  -- the recursors' names are fresh where they are stored
  have hfreshR : ∀ q ∈ cvRas.zipIdx,
      (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env)).find?
        (Prod.fst q).name = none := by
    intro q hq
    have hget : cvRas[q.2]? = some q.1 := List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using hq)
    obtain ⟨hlenR, hallR⟩ := ConLeche.checkMutualRecTys_inv hrectys
    have hqk : q.2 < b.k := by
      have := (List.getElem?_eq_some_iff.mp hget).1
      rw [hlenR] at this; exact this
    obtain ⟨cvRa, hget', hrunR⟩ := hallR q.2 hqk
    obtain rfl : q.1 = cvRa := Option.some.inj (hget.symm.trans hget')
    obtain ⟨recTy, -, -, -, -, -, -, -, -, -, -, hqeq⟩ := ConLeche.checkMutualRecTy_shape hrunR
    rw [hqeq]
    show (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env)).find?
      (b.recName q.2) = none
    have hrecMem : b.recName q.2 ∈ (List.range b.k).map b.recName :=
      List.mem_map_of_mem (List.mem_range.mpr hqk)
    rw [consMutualCtors_find?_of_ne, consMutualFormers_find?_of_ne]
    · exact hfreshRec q.2 hqk
    · intro g hg hh
      refine hdisj _ (List.mem_append.mpr (Or.inl ?_)) _ hrecMem hh
      rw [← hnamesF]
      exact List.mem_map_of_mem hg
    · intro c hc hh
      exact hdisj _ (List.mem_append.mpr (Or.inr (hctorNames c hc))) _ hrecMem hh
  -- the three later stages are fresh extensions
  have hx : FreshEtaExt (ConLeche.consMutualFormers fms env) envAux :=
    (consMutualCtors_freshExt (nP := b.nP) (checkMutualCtors_fresh hctors)).trans
      ((storeMutualRecs_freshExt hfreshR).trans (mutualTables_freshExt htbl))
  refine ⟨fms, hformers, hkF, hposF, fun f hf => ?_⟩
  exact FreshEtaExt.find?_some hx (consMutualFormers_find?_self hf hndF)

/-- **The auxiliary model of a nested run**: the scratch environment the
run's `checkMutualCore` produced carries the P invariant. -/
theorem declNestedRun_auxModel (hμ : μ.verifiedChecks = true) {F : Nat} {env envOut : Env}
    {p : NestedParts} (mp : EnvModelM V μ env) (hE : ConLeche.EtaFamiliesClosed env)
    (h : DeclNestedRun μ F env p envOut) :
    ∃ (st : ElimState) (b : MutualBlock) (envAux : Env),
      ConLeche.auxBlock p st = some b ∧
      ConLeche.checkMutualCore (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env b none true
        = .ok envAux ∧
      ∃ (mpAux : EnvModelM V μ envAux) (d : IndRepData V), MutualBlockReps mpAux.base2 b d := by
  obtain ⟨-, -, st, b, envAux, stored, ctorsR, cvRms, cvRns, rulesM, rulesN, st₀, a₀, fvsA, order,
    pinsA, helim, hremint, -, hfresh, -, hb, hcore, hstored, -, -, -, -, -, hrm, -⟩ := h
  exact ⟨st, b, envAux, hb, hcore,
    nestedAuxModel hμ mp hE helim hremint hfresh hb hcore hstored hrm⟩

end ConLeche.Model
