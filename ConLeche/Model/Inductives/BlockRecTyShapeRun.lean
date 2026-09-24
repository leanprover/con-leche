module

import ConLeche.Verify.Inductives.RecStage
public import ConLeche.Model.Inductives.BlockRecTyping
public import ConLeche.Model.Inductives.BlockRecMem
import ConLeche.Model.Inductives.BlockRecPreRun
public import ConLeche.Model.Inductives.BlockRecRule

public section

/-!
# The recursor type's binder SHAPE, at the run

`BlockRecTyShape` (`Model/Inductives/BlockRecTyping.lean`) is what the
recursor model reads off the stored recursor types: the arity, the
parameters, the eliminated member's index telescope and the major.
This file produces it from the recursor stage's run and the members'
own former data.

It is a LEAF module and it has to be: it consumes `prefixDoms_spineFit`
(`BlockRecPreRun`) and `recStage_tyPis`/`recStage_tyAt`
(`BlockRecMem`, which `BlockRecPreRun` sits above), so it can be an
addition to neither.

**What the check actually pins**, and what each clause is therefore
bounded by (`checkBlockRecTys`, `Kernel/Inductives/BlockInstall.lean`):

* `nP ≤ rP` and `mI = rP + nIdx_m` are the stage's own two `unless`es
  — clauses 1 and 2, arithmetic once the member's index count is
  identified with `nIdx_m` (`FormerData.len`);
* the first `nP` binder DOMAINS are compared BINDER BY BINDER with the
  member's own opened former telescope — clause 3, and it is an `↔`
  between FITS (never a syntactic equality: the two spellings are only
  ever certified defeq).  BOTH directions are paid the same way, which
  is why the clause is an `↔` and clause 4 is not:
  `prefixDoms_spineFit` is symmetric in its two openings (it takes the
  comparison as an `Or`, so the swapped call is the same hop with the
  disjunct on the other side), and the member-to-member parameter
  agreement (`paramsIff`) is an `↔` already;
* the binders `nP … rP-1` and the INDEX binders are never looked
  inside at all.  Clause 4 therefore does not read them: it reads the
  MAJOR, whose domain is `T_m p⃗ ı⃗` on the nose, so its reading is a
  spine against the member's FORMER — a λ-tower — and the spine's
  grading carries the fit (`spineFit_of_major_grading`).  The tower's
  binder numeral is `w ψ + 1`, never zero, so this survives a
  `Prop`-valued block;
* the MAJOR's syntactic pin is clause 6, read off the opening's own
  fvars (`interp_of_major_reading`).

The OPPOSITE direction of clause 4 is not produced: nothing in the run
ties the recursor's index binders to the member's telescope except the
per-argument `isDefEq` inside `checkConstantVal`'s inference of the
major's domain, and no consumer needs it (stage (b'')'s converse,
`blockRecIdxConv_run`, is what the model reads instead).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo openPisAtFvars)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## 1. Kit -/

/-- A closed leaf's interpretation does not read the frame. -/
theorem acval_interp_closed {env : Env} (m : EnvModel V env) (n : Name)
    (ψ : Name → Nat) (ρ ρ' : Nat → V) :
    interp V ρ (m.acval n ψ) = interp V ρ' (m.acval n ψ) :=
  interp_closed V (by rw [m.acval_erase]; exact m.cval_closed n ψ) ρ ρ'

/-! ## 2. The member-side run facts

Five statements about the members, all of them the block install's
own: the shape agreement (`d.nP`, `d.k`), the per-member former data
(`BlockFormerFacts.fdOf` at the CONSTRUCTORS' environment, which is
where the recursor stage runs), the member record's name and index
count, the leaf's λ-TOWER shape (`blockLeafZ`, whose binder numeral is
`w ψ + 1` — never zero, which is why the index clause survives a
`Prop`-valued block), and official's parameter agreement
(`BlockFormerFacts.paramsIff`).

It is a bundle and not five premises because every clause below needs
two or three of them, and it has exactly one consumer, the shape's
producer. -/
@[expose] def BlockMembersRun {envC : Env} (mo : EnvModel V envC) (d : BlockData V)
    (q : ConLeche.BlockShape) (cvTas : List ConstantVal) : Prop :=
  d.nP = q.nP ∧ d.k = q.members.length ∧
  cvTas.length = d.k ∧
  (∀ (m : Nat) (cvTb : ConstantVal), cvTas[m]? = some cvTb →
    d.memberName m = cvTb.name ∧ cvTb.levelParams = q.lps ∧
    (∃ caps, envC.find? cvTb.name = some (.indInfo cvTb caps)) ∧
    cvTb.type.hasFvar = false ∧ cvTb.type.looseBVarsBounded 0 = true ∧
    FormerData mo cvTb (d.nP + d.nIdxAt m) d.resSort (d.ppsM m)) ∧
  (∀ (m : Nat) (ms : ConLeche.MemberShape), q.members[m]? = some ms →
    d.memberName m = ms.cvT.name ∧ d.nIdxAt m = ms.nIdx) ∧
  (∀ (m : Nat) (ψ : Name → Nat), m < d.k →
    ∃ B, mo.acval (d.memberName m) ψ = mkLamsC (d.w ψ + 1) (d.ppsM m ψ) B) ∧
  (∀ m, m < d.k → ∀ (ψ : Name → Nat) (ρ : Nat → V),
    Sat V (((d.ppsM m ψ).take d.nP).map (·.2.2)).reverse ρ ↔ Sat V (d.params ψ).reverse ρ)

section Run

variable {envC : Env} {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
  {d : BlockData V}

/-! ## 3. The MAJOR's reading, and the arity

One theorem, because the major's reading is what identifies the
recursor's member and the arity is what its position is read at. -/

/-- **The recursor's arity and its MAJOR's reading, at the run.**

The major's domain is pinned syntactically (`checkBlockRecTys`'s last
`unless`): the member's constant at the block's level parameters,
applied to the opening's first `nP` fvars and to its index fvars.  A
fvar reads to the bvar its position names, so the reading is the
member's leaf applied to `paramBvarsAt nP mI ++ teleVarsAV nIdx` —
which is exactly what `interp_of_major_reading` and
`spineFit_of_major_grading` are stated against. -/
theorem blockRecMajor_run (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    (h : ConLeche.RecStageOk μ F envC p cvTas ctorsAs rs)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) (ψ : Name → Nat) :
    d.nP ≤ p.toBlockShape.rulePrefixAt c ∧
    p.toBlockShape.recTgtAt c < d.k ∧
    p.toBlockShape.majorIdxAt c
      = p.toBlockShape.rulePrefixAt c + d.nIdxAt (p.toBlockShape.recTgtAt c) ∧
    (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
      = p.toBlockShape.majorIdxAt c + 1 ∧
    ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).getD
        (p.toBlockShape.majorIdxAt c) default).2.2
      = AnnotTerm.mkAppN
          (mpC.base2.acval (d.memberName (p.toBlockShape.recTgtAt c)) ψ)
          (paramBvarsAt d.nP (p.toBlockShape.majorIdxAt c)
            ++ teleVarsAV (d.nIdxAt (p.toBlockShape.recTgtAt c))) := by
  obtain ⟨hnPq, hkq, -, hcvF, hmsF, -, -⟩ := hmr
  obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.recStage_tyAt h hr
  have hms := TE.hms
  have hcvTa := TE.hcvTa
  have hnPle := TE.nP_le
  have hmI := TE.hmI
  have hop := TE.hopen
  have hopT := TE.hopenT
  have htfl := TE.htfvs
  have hdeq := TE.hparams
  have hmaj0 := TE.hmaj
  have hfn := TE.hmajFn
  have hargl := TE.hmajLen
  have hargP := TE.hmajParams
  have hargI := TE.hmajIdx
  obtain ⟨fvsL, conclL, hopL, hread, hmk, hlenRds, hbits, hbind, hconclRead, hwdTy⟩ :=
    recStage_tyPis hμ mpC h hr ψ
  have hfvE : fvsL = TE.fvs := by
    have hq := Option.some.inj (hopL.symm.trans hop)
    exact congrArg Prod.fst hq
  rw [hfvE] at hbind
  obtain ⟨hnameMs, hnIdxMs⟩ := hmsF _ _ hms
  obtain ⟨hnameCv, hlpsE, ⟨caps, hfind⟩, -, -, -⟩ := hcvF _ _ hcvTa
  have hmemk : p.toBlockShape.recTgtAt c < d.k := by
    rw [hkq]
    exact (List.getElem?_eq_some_iff.mp hms).1
  have hnPle' : d.nP ≤ p.toBlockShape.rulePrefixAt c := by rw [hnPq]; exact hnPle
  have hmI' : p.toBlockShape.majorIdxAt c
      = p.toBlockShape.rulePrefixAt c + d.nIdxAt (p.toBlockShape.recTgtAt c) := by
    rw [hnIdxMs]; exact hmI
  -- the major's TYPE, reassembled from the pin
  have hmajTy : Expr.fvarTypeD TE.maj
      = Expr.mkAppN (.const TE.ms.cvT.name (p.toBlockShape.lps.map .param))
        (TE.fvs.take p.nP
          ++ (TE.fvs.drop (p.toBlockShape.rulePrefixAt c)).take TE.ms.nIdx) := by
    conv => lhs; rw [← ConLeche.Expr.mkAppN_getApp (Expr.fvarTypeD TE.maj)]
    rw [hfn, ← hargP, ← hargI, List.take_append_drop]
  -- the head
  have hnameEq : TE.ms.cvT.name = TE.cvTa.name := by rw [← hnameMs, hnameCv]
  have hconst : denoteMeta mpC.base2.acval envC ψ (p.toBlockShape.majorIdxAt c)
      (.const TE.ms.cvT.name (p.toBlockShape.lps.map .param))
      = some (mpC.base2.acval (d.memberName (p.toBlockShape.recTgtAt c)) ψ) := by
    rw [denoteMeta_const (ci := .indInfo TE.cvTa caps) (by rw [hnameEq]; exact hfind)
      (by rw [show (ConstantInfo.indInfo TE.cvTa caps).toConstantVal = TE.cvTa from rfl, hlpsE,
        List.length_map])]
    rw [show (ConstantInfo.indInfo TE.cvTa caps).toConstantVal = TE.cvTa from rfl, hlpsE,
      Level.substFn_param_self, hnameMs]
  -- the two argument spines
  have hlenFvs : TE.fvs.length = p.toBlockShape.majorIdxAt c + 1 :=
    ConLeche.Verify.openPisAtFvars_length _ hop
  have hidxFvs := ConLeche.openPisAtFvars_index _ _ _ hop
  have hlenTake : (TE.fvs.take p.nP).length = p.nP := by
    rw [List.length_take, hlenFvs]; omega
  have hidxTake : ∀ (k : Nat) (x : Expr), (TE.fvs.take p.nP)[k]? = some x →
      ∃ ty, x = Expr.fvar k ty := by
    intro k x hx
    have hk : k < p.nP := by
      have := (List.getElem?_eq_some_iff.mp hx).1
      rw [hlenTake] at this; exact this
    rw [List.getElem?_take, if_pos hk] at hx
    obtain ⟨ty, hty⟩ := hidxFvs k x hx
    exact ⟨ty, by rw [hty, Nat.zero_add]⟩
  have hspP := denoteMetaSpine_params (acval := mpC.base2.acval) (env := envC) (φ := ψ)
    (p.toBlockShape.majorIdxAt c) hlenTake hidxTake
  have hlenI : ((TE.fvs.drop (p.toBlockShape.rulePrefixAt c)).take TE.ms.nIdx).length = TE.ms.nIdx := by
    rw [List.length_take, List.length_drop, hlenFvs]; omega
  have hidxI : ∀ (k : Nat) (x : Expr),
      ((TE.fvs.drop (p.toBlockShape.rulePrefixAt c)).take TE.ms.nIdx)[k]? = some x →
      ∃ ty, x = Expr.fvar (p.toBlockShape.rulePrefixAt c + k) ty := by
    intro k x hx
    have hk : k < TE.ms.nIdx := by
      have := (List.getElem?_eq_some_iff.mp hx).1
      rw [hlenI] at this; exact this
    rw [List.getElem?_take, if_pos hk, List.getElem?_drop] at hx
    obtain ⟨ty, hty⟩ := hidxFvs _ x hx
    exact ⟨ty, by rw [hty, Nat.zero_add]⟩
  have hspI0 := denoteMetaSpine_fvars (acval := mpC.base2.acval) (env := envC) (φ := ψ)
    (p.toBlockShape.majorIdxAt c) ((TE.fvs.drop (p.toBlockShape.rulePrefixAt c)).take TE.ms.nIdx)
    (p.toBlockShape.rulePrefixAt c) hidxI
  rw [hlenI] at hspI0
  have hteleE : ((List.range TE.ms.nIdx).map fun k =>
        (AnnotTerm.bvar (p.toBlockShape.majorIdxAt c - 1
          - (p.toBlockShape.rulePrefixAt c + k))))
      = teleVarsAV TE.ms.nIdx := by
    rw [teleVarsAV]
    refine List.map_congr_left fun k hk => ?_
    have hk' : k < TE.ms.nIdx := by simpa using hk
    rw [hmI]
    congr 1
    omega
  rw [hteleE] at hspI0
  -- the reading, and its position in the binder data
  have hreadMaj : denoteMeta mpC.base2.acval envC ψ (p.toBlockShape.majorIdxAt c)
      (Expr.fvarTypeD TE.maj)
      = some (AnnotTerm.mkAppN
          (mpC.base2.acval (d.memberName (p.toBlockShape.recTgtAt c)) ψ)
          (paramBvarsAt p.nP (p.toBlockShape.majorIdxAt c) ++ teleVarsAV TE.ms.nIdx)) := by
    rw [hmajTy, denoteMeta_mkAppN_of _ hconst (DenoteMetaSpine.append hspP hspI0)]
  obtain ⟨pd, hpd, -, hreadB⟩ := hbind _ TE.maj hmaj0
  refine ⟨hnPle', hmemk, hmI', hlenRds, ?_⟩
  rw [List.getD_eq_getElem?_getD, hpd, Option.getD_some, hnPq, hnIdxMs,
    ← Option.some.inj (hreadB.symm.trans hreadMaj)]

/-! ## 4. The INDEX clause's payable half, at the run

The recursor's own index binders are never inspected by the check, so
nothing here reads them: what carries the fit is the MAJOR, whose
domain is the member's FORMER applied to the prefix and index binders.
The former is a λ-tower whose binder numeral is `w ψ + 1` — **never
zero**, so this clause survives a `Prop`-valued block, where the
rule contract's own fit conjunct is refutable. -/

/-- **The eliminated member's index fit, at the run** — clause 4 of
the shape.  Bounded by the prefix's fit, because the grading it uses
is the recursor type's own and is available only along a fitting
spine. -/
theorem blockRecIdxFit_run (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    (h : ConLeche.RecStageOk μ F envC p cvTas ctorsAs rs)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) (ψ : Name → Nat) (ρ : Nat → V) :
    ∀ xs is : List V, xs.length = p.toBlockShape.rulePrefixAt c →
      SpineFit ρ (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map
        (·.2.2)).take (p.toBlockShape.rulePrefixAt c)) xs →
      SpineFit (consList xs ρ)
        ((((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map (·.2.2)).drop
          (p.toBlockShape.rulePrefixAt c)).take
            (d.IdsM (p.toBlockShape.recTgtAt c) ψ).length) is →
      SpineFit (consList (xs.take d.nP) ρ)
        (d.IdsM (p.toBlockShape.recTgtAt c) ψ) is := by
  intro xs is hxl hpref hidx
  obtain ⟨hnPle, hmemk, hmI, hlenRds, hmajRead⟩ := blockRecMajor_run hμ mpC h hmr hr ψ
  obtain ⟨hnPq, hkq, hlenCv, hcvF, hmsF, hlamF, -⟩ := hmr
  obtain ⟨-, -, -, -, hmk, -, -, -, -, hwdTy⟩ := recStage_tyPis hμ mpC h hr ψ
  obtain ⟨cvTa, hcvTa⟩ : ∃ cvTa, cvTas[p.toBlockShape.recTgtAt c]? = some cvTa :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlenCv]; exact hmemk)⟩
  obtain ⟨-, -, -, -, -, hFD⟩ := hcvF _ _ hcvTa
  obtain ⟨B, hB⟩ := hlamF (p.toBlockShape.recTgtAt c) ψ hmemk
  -- the member's telescope: `nP` parameters, then its own indices
  have hppsLen : (d.ppsM (p.toBlockShape.recTgtAt c) ψ).length
      = d.nP + d.nIdxAt (p.toBlockShape.recTgtAt c) := hFD.len ψ
  have hIdsLen : (d.IdsM (p.toBlockShape.recTgtAt c) ψ).length
      = d.nIdxAt (p.toBlockShape.recTgtAt c) := by
    rw [BlockData.IdsM, List.length_map, List.length_drop, hppsLen]; omega
  rw [hIdsLen] at hidx
  -- the two spine lengths
  have hDlen : ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map (·.2.2)).length
      = p.toBlockShape.rulePrefixAt c + d.nIdxAt (p.toBlockShape.recTgtAt c) + 1 := by
    rw [List.length_map, hlenRds, hmI]
  have hisl : is.length = d.nIdxAt (p.toBlockShape.recTgtAt c) := by
    rw [hidx.length_eq, List.length_take, List.length_drop, hDlen]; omega
  -- the frame's fit past the prefix and the indices
  have happ : SpineFit ρ
      (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map (·.2.2)).take
        (p.toBlockShape.majorIdxAt c)) (xs ++ is) := by
    rw [hmI, take_add_eq_append]
    exact SpineFit.append hpref hidx
  -- the major's domain is GRADED there
  have hgetD : ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map
        (·.2.2)).getD (p.toBlockShape.majorIdxAt c) default
      = ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).getD
        (p.toBlockShape.majorIdxAt c) default).2.2 := by
    obtain ⟨pd, hpd⟩ : ∃ pd,
        (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c)[
          p.toBlockShape.majorIdxAt c]? = some pd :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlenRds]; omega)⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hpd,
      List.getD_eq_getElem?_getD, hpd]
    rfl
  have hwd : WellDenotedV V (consList (xs ++ is) ρ)
      (AnnotTerm.mkAppN
        (mpC.base2.acval (d.memberName (p.toBlockShape.recTgtAt c)) ψ)
        (paramBvarsAt d.nP (p.toBlockShape.majorIdxAt c)
          ++ teleVarsAV (d.nIdxAt (p.toBlockShape.recTgtAt c)))) := by
    have happ' : SpineFit ρ
        ((((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).take
          (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length).map
            (·.2.2)).take (p.toBlockShape.majorIdxAt c)) (xs ++ is) := by
      rw [List.take_length]; exact happ
    have hg := prefixDoms_graded_of_tower (V := V)
      (rds := blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c)
      (cc := blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ c)
      (rP := (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length)
      (Nat.le_refl _) (fun ρ' => by rw [← hmk]; exact hwdTy ρ')
      (l := p.toBlockShape.majorIdxAt c) (by rw [hlenRds]; omega) happ'
    rw [List.take_length, hgetD, hmajRead] at hg
    exact hg
  rw [hmI] at hwd
  -- the FORMER's λ-tower, and the fit it carries
  have hsplitD : ((d.ppsM (p.toBlockShape.recTgtAt c) ψ).take
        (d.nP + d.nIdxAt (p.toBlockShape.recTgtAt c))).map (·.2.2)
      = ((d.ppsM (p.toBlockShape.recTgtAt c) ψ).take d.nP).map (·.2.2)
        ++ d.IdsM (p.toBlockShape.recTgtAt c) ψ := by
    rw [← hppsLen, List.take_length, BlockData.IdsM, ← List.map_append,
      List.take_append_drop]
  exact (spineFit_of_major_grading (V := V) (u := d.w ψ + 1) (Nat.succ_ne_zero _)
    (nm := d.memberName (p.toBlockShape.recTgtAt c)) (B := B)
    (Params := ((d.ppsM (p.toBlockShape.recTgtAt c) ψ).take d.nP).map (·.2.2))
    (Ids := d.IdsM (p.toBlockShape.recTgtAt c) ψ)
    hxl hisl hnPle
    (by rw [List.length_map, List.length_take, hppsLen]; omega)
    (Nat.le_of_eq hppsLen.symm)
    hsplitD
    (by rw [← hB]; exact acval_interp_closed mpC.base2 _ ψ _ ρ) hwd.1).2

/-! ## 5. The PARAMETER clause, at the run

`checkBlockRecTys` compares the recursor's first `nP` binder domains
BINDER BY BINDER with the ELIMINATED member's own opened former
telescope — never with the block's, and never syntactically: it is an
`isDefEq` per position.  So the clause is an `↔` between FITS
(`prefixDoms_spineFit`, the certified hop, called once each way),
composed with the members' own parameter agreement
(`BlockFormerFacts.paramsIff`, itself an `↔`) between the eliminated
member's telescope and the block's `d.params`.

**A clause is stated in the direction(s) that have producers.**  This
one has both, which is what separates it from the index clause: the
hop takes its comparison as an `Or` of the two `isDefEq` orientations
and proves the transfer either way, so swapping its two openings costs
nothing. -/

/-- **The block's parameter telescope fits, at the run, IN BOTH
DIRECTIONS** — clause 3 of the shape. -/
theorem blockRecParams_run (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    (h : ConLeche.RecStageOk μ F envC p cvTas ctorsAs rs)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) (ψ : Name → Nat) (ρ : Nat → V) :
    ∀ xs : List V,
      SpineFit ρ (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map
        (·.2.2)).take d.nP) xs ↔ SpineFit ρ (d.params ψ) xs := by
  intro xs
  obtain ⟨hnPle, hmemk, hmI, hlenRds, -⟩ := blockRecMajor_run hμ mpC h hmr hr ψ
  obtain ⟨hnPq, hkq, hlenCv, hcvF, -, -, hparIff⟩ := hmr
  obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.recStage_tyAt h hr
  have hms := TE.hms
  have hcvTa := TE.hcvTa
  have hop := TE.hopen
  have hopT := TE.hopenT
  have htfl := TE.htfvs
  have hdeq := TE.hparams
  obtain ⟨fvsL, conclL, hopL, hread, hmk, -, -, hbind, -, hwdTy⟩ :=
    recStage_tyPis hμ mpC h hr ψ
  have hfvE : fvsL = TE.fvs := congrArg Prod.fst (Option.some.inj (hopL.symm.trans hop))
  rw [hfvE] at hbind
  obtain ⟨-, -, -, hfvT, hbndT, hFD⟩ := hcvF _ _ hcvTa
  have hppsLen : (d.ppsM (p.toBlockShape.recTgtAt c) ψ).length
      = d.nP + d.nIdxAt (p.toBlockShape.recTgtAt c) := hFD.len ψ
  -- the two openings, at the block's parameter count
  obtain ⟨hwA, hbA⟩ := recStage_tyClosed h hr
  obtain ⟨fvsA, fvs', oA, hopA, -, hfvsplit⟩ :=
    openPisAtFvars_split (e := r.1.type) (d := 0) p.nP
      (by rw [show p.nP + (p.toBlockShape.majorIdxAt c + 1 - p.nP)
            = p.toBlockShape.majorIdxAt c + 1 from by omega]
          exact hop)
  have hlenA : fvsA.length = p.nP := ConLeche.Verify.openPisAtFvars_length _ hopA
  have hfvsA : TE.fvs.take p.nP = fvsA := by
    rw [hfvsplit, List.take_append_of_le_length (Nat.le_of_eq hlenA.symm),
      List.take_of_length_le (Nat.le_of_eq hlenA)]
  -- the two domain lists, their readings and their gradings
  have hDomA : ∀ l, l < p.nP →
      ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map (·.2.2)).getD l default
        = (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).take p.nP).map
            (·.2.2)).getD l default := by
    intro l hl
    rw [List.map_take, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take, if_pos hl]
  have hdA : ∀ (i : Nat) (x : Expr), fvsA[i]? = some x →
      denoteMeta mpC.base2.acval envC ψ i (Expr.fvarTypeD x)
        = some ((((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).take p.nP).map
            (·.2.2)).getD i default) := by
    intro i x hx
    have hi : i < p.nP := by
      have := (List.getElem?_eq_some_iff.mp hx).1
      rw [hlenA] at this; exact this
    have hx' : TE.fvs[i]? = some x := by
      rw [← hfvsA, List.getElem?_take, if_pos hi] at hx
      exact hx
    obtain ⟨pd, hpd, -, hreadD⟩ := hbind i x hx'
    rw [hreadD, List.map_take, List.getD_eq_getElem?_getD, List.getElem?_take,
      if_pos hi, List.getElem?_map, hpd]
    rfl
  have hokA : ∀ i, i < p.nP → ∀ (ρ' : Nat → V) (ys : List V),
      SpineFit ρ' ((((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).take
        p.nP).map (·.2.2)).take i) ys →
      WellDenotedV V (consList ys ρ')
        ((((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).take p.nP).map
          (·.2.2)).getD i default) :=
    fun i hi ρ' ys hys => prefixDoms_graded_of_tower (V := V)
      (cc := blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ c)
      (by rw [hlenRds]; omega) (fun ρ'' => by rw [← hmk]; exact hwdTy ρ'') hi hys
  -- the member's side
  obtain ⟨ppsT, bT, hstT, -, hlenT, hbindT⟩ :=
    denoteMeta_openPis (acval := mpC.base2.acval) (env := envC) (φ := ψ) p.nP hopT (hFD.read ψ)
  have hppsT : ppsT = (d.ppsM (p.toBlockShape.recTgtAt c) ψ).take p.nP := by
    have := stripPisAV_mkPisAV_take p.nP (d.ppsM (p.toBlockShape.recTgtAt c) ψ)
      (.sort (d.resSort.eval ψ)) (by rw [hppsLen, hnPq]; omega)
    rw [this] at hstT
    exact congrArg Prod.fst (Option.some.inj hstT.symm)
  have hdB : ∀ (i : Nat) (x : Expr), TE.tfvs[i]? = some x →
      denoteMeta mpC.base2.acval envC ψ i (Expr.fvarTypeD x)
        = some ((((d.ppsM (p.toBlockShape.recTgtAt c) ψ).take d.nP).map (·.2.2)).getD i
            default) := by
    intro i x hx
    obtain ⟨pd, hpd, -, hreadD⟩ := hbindT i x hx
    rw [Nat.zero_add] at hreadD
    rw [hreadD, hnPq, ← hppsT, List.getD_eq_getElem?_getD, List.getElem?_map, hpd]
    rfl
  have hokB : ∀ i, i < p.nP → ∀ (ρ' : Nat → V) (ys : List V),
      SpineFit ρ' ((((d.ppsM (p.toBlockShape.recTgtAt c) ψ).take d.nP).map (·.2.2)).take i) ys →
      WellDenotedV V (consList ys ρ')
        ((((d.ppsM (p.toBlockShape.recTgtAt c) ψ).take d.nP).map (·.2.2)).getD i default) := by
    intro i hi ρ' ys hys
    rw [hnPq] at hys ⊢
    exact prefixDoms_graded_of_tower (V := V) (cc := .sort (d.resSort.eval ψ))
      (by rw [hppsLen, hnPq]; omega) (fun ρ'' => hFD.okTy ψ ρ'') hi hys
  -- the two telescopes' lengths, shared by the two directions
  obtain ⟨cvT0, hcvT0⟩ : ∃ cvT0, cvTas[0]? = some cvT0 :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlenCv]; omega)⟩
  obtain ⟨-, -, -, -, -, hFD0⟩ := hcvF _ _ hcvT0
  have hlenPD : (d.params ψ).length = d.nP := by
    rw [BlockData.params, List.length_map, List.length_take, hFD0.len ψ]; omega
  have hlenT : ((((d.ppsM (p.toBlockShape.recTgtAt c) ψ).take d.nP).map (·.2.2))).length
      = d.nP := by
    rw [List.length_map, List.length_take, hppsLen]; omega
  -- **the certified hop**, in both directions: `prefixDoms_spineFit` is
  -- symmetric in its two openings (the comparison travels as an `Or`),
  -- and the members' own parameter agreement is an `↔` already
  constructor
  · intro hfit
    have hfitA : SpineFit ρ (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).take
        p.nP).map (·.2.2)) xs := by
      rw [hnPq] at hfit
      rw [List.map_take]
      exact hfit
    have hfitB := prefixDoms_spineFit (V := V) hμ mpC hopA hopT hwA
      (Expr.WScoped.of_not_hasFvar hfvT) hbA hbndT
      (by rw [List.length_map, List.length_take, hlenRds]; omega)
      (by rw [List.length_map, List.length_take, hppsLen, hnPq]; omega)
      hdA hdB hokA hokB
      (fun l hl => Or.inr (by
        rw [← hfvsA]
        exact hdeq l hl))
      hfitA
    have hsat : Sat V ((((d.ppsM (p.toBlockShape.recTgtAt c) ψ).take d.nP).map
        (·.2.2)).reverse) (consList xs ρ) := by
      simpa using sat_of_spineFit (Sat_nil V ρ) hfitB
    exact spineFit_of_sat_consList (by rw [hfitB.length_eq, hlenT, hlenPD])
      ((hparIff _ hmemk ψ _).mp hsat)
  · intro hfit
    have hsat : Sat V (d.params ψ).reverse (consList xs ρ) := by
      simpa using sat_of_spineFit (Sat_nil V ρ) hfit
    have hfitB : SpineFit ρ (((d.ppsM (p.toBlockShape.recTgtAt c) ψ).take d.nP).map (·.2.2)) xs :=
      spineFit_of_sat_consList (by rw [hfit.length_eq, hlenPD, hlenT])
        ((hparIff _ hmemk ψ _).mpr hsat)
    have hfitA := prefixDoms_spineFit (V := V) hμ mpC hopT hopA
      (Expr.WScoped.of_not_hasFvar hfvT) hwA hbndT hbA
      (by rw [List.length_map, List.length_take, hppsLen, hnPq]; omega)
      (by rw [List.length_map, List.length_take, hlenRds]; omega)
      hdB hdA hokB hokA
      (fun l hl => Or.inl (by
        rw [← hfvsA]
        exact hdeq l hl))
      hfitB
    rw [hnPq, ← List.map_take]
    exact hfitA

/-! ## 6. THE SHAPE, at the run -/

/-- **`BlockRecTyShape` FROM THE RUN.**

Its five clauses, in order: the two the stage's own `unless`es pin
(`nP ≤ rP`, the binder count), the parameters as an `↔` between FITS
(`blockRecParams_run`), the eliminated member's index fit
(`blockRecIdxFit_run`) and the MAJOR's reading folded into
applications (`interp_of_major_reading`).

The index clause's OPPOSITE direction is not among them and is not
produced here: nothing in the run ties the recursor's index binders to
the member's telescope. -/
theorem blockRecTyShape_run (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    (h : ConLeche.RecStageOk μ F envC p cvTas ctorsAs rs)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    {K : Nat} (hK : rs.length = K) (ψ : Name → Nat) (ρ : Nat → V) :
    BlockRecTyShape V mpC.base2 d ψ K p.toBlockShape.rulePrefixAt
      p.toBlockShape.recTgtAt
      (fun c => blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c) ρ := by
  intro c hc
  obtain ⟨r, hr⟩ : ∃ r, rs[c]? = some r :=
    ⟨_, List.getElem?_eq_getElem (by rw [hK]; exact hc)⟩
  obtain ⟨hnPle, hmemk, hmI, hlenRds, hmajRead⟩ := blockRecMajor_run hμ mpC h hmr hr ψ
  have hpar := blockRecParams_run hμ mpC h hmr hr ψ ρ
  have hidxF := blockRecIdxFit_run hμ mpC h hmr hr ψ ρ
  obtain ⟨hnPq, hkq, hlenCv, hcvF, -, -, -⟩ := hmr
  obtain ⟨cvTa, hcvTa⟩ : ∃ cvTa, cvTas[p.toBlockShape.recTgtAt c]? = some cvTa :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlenCv]; exact hmemk)⟩
  obtain ⟨-, -, -, -, -, hFD⟩ := hcvF _ _ hcvTa
  have hIdsLen : (d.IdsM (p.toBlockShape.recTgtAt c) ψ).length
      = d.nIdxAt (p.toBlockShape.recTgtAt c) := by
    rw [BlockData.IdsM, List.length_map, List.length_drop, hFD.len ψ]; omega
  have hDlen : ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map (·.2.2)).length
      = p.toBlockShape.rulePrefixAt c + d.nIdxAt (p.toBlockShape.recTgtAt c) + 1 := by
    rw [List.length_map, hlenRds, hmI]
  refine ⟨hnPle, by rw [hDlen, hIdsLen], hpar, hidxF, ?_⟩
  -- the MAJOR clause, from the one syntactic reading
  intro xs is hxl hisl
  rw [hIdsLen] at hisl
  have hgetMaj : (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map
        (·.2.2)).drop (p.toBlockShape.rulePrefixAt c)).getD
        (d.nIdxAt (p.toBlockShape.recTgtAt c)) default
      = AnnotTerm.mkAppN
          (mpC.base2.acval (d.memberName (p.toBlockShape.recTgtAt c)) ψ)
          (paramBvarsAt d.nP (p.toBlockShape.majorIdxAt c)
            ++ teleVarsAV (d.nIdxAt (p.toBlockShape.recTgtAt c))) := by
    obtain ⟨pd, hpd⟩ : ∃ pd,
        (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c)[
          p.toBlockShape.majorIdxAt c]? = some pd :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlenRds]; omega)⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_map,
      show p.toBlockShape.rulePrefixAt c + d.nIdxAt (p.toBlockShape.recTgtAt c)
        = p.toBlockShape.majorIdxAt c from hmI.symm, hpd, Option.map_some,
      Option.getD_some, ← hmajRead, List.getD_eq_getElem?_getD, hpd]
    rfl
  rw [hIdsLen, hgetMaj, ← consList_append, hmI]
  exact interp_of_major_reading (mo := mpC.base2) hxl hisl hnPle
    (fun ρ₁ ρ₂ => acval_interp_closed mpC.base2 _ ψ ρ₁ ρ₂)

/-! ## 7. The `ih` KEY's block facts (`hkey` half A)

One `ih` key's reading (`blockKitIhKey_run`, `BlockKitIhRun.lean`)
splits in two with very different provenances:

* **(A) the KEY's block facts** — the field is in range, it is
  RECURSIVE or REFLEXIVE, it targets the callee's member, and the
  callee's class is in range.  These are decided by `blockIhKeys`'
  own filter and by the block's tables, and they are proved here;
* **(B) `eisA`/`fapA`/`BlockRuleConclAt` and the DOMAIN equation** —
  ONE reading of the generated `blockIhPis` opener, delivered by
  `blockRuleHopener_of` (`BlockRecOpenerRead.lean`) and
  `blockRuleHconcl_of` — which is why they form the single premise
  `hihOpen` rather than several premises about one term.

The keys are the CHECK's own list (`BlockInstall.lean`'s
`ihKeys := blockIhKeys rP rPs recTgts ks`), so nothing here is
quantified over an arbitrary key list; and the block-table bridges are
premises because they are `rfl` at `blockDataOf` and this module may
not name that record. -/

section Keys

/-- **`hihOpen` half A's MEMBER arity**: the index telescope a member
contributes has that member's index count — the last of the fused
premise's four lengths, and the one that ties the field's readings to
the CALLEE's telescope (the key's own fact, `blockIhKey_block_facts`). -/
theorem blockMembers_IdsM_length {envC : Env} {mo : EnvModel V envC} {d : BlockData V}
    {q : ConLeche.BlockShape} {cvTas : List ConstantVal}
    (hmr : BlockMembersRun mo d q cvTas) {mm : Nat} (hmm : mm < d.k) (ψ : Name → Nat) :
    (d.IdsM mm ψ).length = d.nIdxAt mm := by
  obtain ⟨-, -, hlenCv, hcvF, -, -, -⟩ := hmr
  obtain ⟨cvTb, hcvTa⟩ : ∃ cvTb, cvTas[mm]? = some cvTb :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlenCv]; exact hmm)⟩
  obtain ⟨-, -, -, -, -, hFD⟩ := hcvF _ _ hcvTa
  rw [BlockData.IdsM, List.length_map, List.length_drop, hFD.len ψ]
  omega

end Keys

/-! ## 8. The `ih` LEVEL, at the opener's CONCLUSION (the fused
opener reading's last syntactic step)

One key's reading (`blockKitIhKey_run`) states its `BlockRuleConclAt`
conjunct at `ih` level `l = 0`, and it has to: `blockRecCa_value`
reads that conclusion at the frame the field TELESCOPE's values sit
on, and the domain equation carries the `liftN r 0` that cancels the
`r` earlier openers' values (`blockGraphIhF_run`).  The RUN peels
the callee's stored type at the generated opener's own level `l = r`
(`blockRuleHconcl_of`, `BlockRecOpenerRead.lean`), because that is
where `blockIhPis` puts the `r`-th key's binder.

The two peels are ONE fact.  Each of the spine's three stretches is
its `l = 0` self lifted at the telescope's cut
(`paramBvarsAt_shift`, `ihIdxAtM_shift`, `fieldApp_shift`, all
`BlockRecRule.lean`), and the peel follows a lift of its whole spine
(`peelPis_liftN_inv`) — so the `l = r` conclusion IS the `l = 0`
conclusion lifted, which is what `mkPisAV_ihTeleAtR_shift` then needs
to move the `liftN` out of the tower. -/

/-! ## `WalkCtx` at the rule's opened frame

`interp_blockResidue`'s `hW` is the walk's ENTRY context, and the rule
frame is the one `ctxOk_blockFrame` (`BlockRecTyping.lean`) already
describes: three openings at the offsets `0`, `rP` and `rP + nF`, the
context `ihdoms.reverse ++ (pdoms ++ fdoms).reverse`, and a valuation
`consList ihvals (consList (xs ++ fs) ρ₀)`.

**`WalkCtx` is `CtxOk`'s inputs, re-indexed.**  `ctxOk_blockFrame`
reads the openers ASCENDING (opener `i` at depth `i`, context slot
`D - 1 - i`); `WalkCtx` carries the opening LIST, which the walk
conses onto, so it reads them DESCENDING (`as2 = L.reverse`, slot `j`
at depth `D - 1 - j`).  The two are the same statement under
`List.getElem?_reverse`, and `D - 1 - (D - 1 - j) = j` below `D` is
the whole of the translation.

What `WalkCtx` asks beyond `CtxOk` is the frame's three HEREDITARY
facts — the openers' annotations are `looseBVarsBounded 0`, bounded by
`envT`, and draw their own leaves from the frame again, all stated
over the opener list. -/

/-- **`WalkCtx` at the rule stage's opened frame** — `hW` at the
entry, from exactly `residueOk_blockFrame`'s inputs plus the frame's
three hereditary facts.

No `w` hypothesis anywhere: the evidence is the two `SpineFit`s and
the openers' readings, never a membership in the carrier. -/
theorem walkCtx_blockFrame {envT : Env} {mT : EnvModel V envT} {ψ : Name → Nat}
    {rP nF nR : Nat} {recTy crest ihTele : Expr}
    {fvsPref fvsF fvsIh : List Expr} {o₁ o₂ o₃ : Expr}
    (h₁ : openPisAtFvars rP recTy 0 = some (fvsPref, o₁))
    (h₂ : openPisAtFvars nF crest rP = some (fvsF, o₂))
    (h₃ : openPisAtFvars nR ihTele (rP + nF) = some (fvsIh, o₃))
    {pdoms fdoms ihdoms : List AnnotTerm}
    (hp : pdoms.length = rP) (hf : fdoms.length = nF) (hidx : ihdoms.length = nR)
    (hdoms : ∀ (i : Nat) (x : Expr), (fvsPref ++ fvsF ++ fvsIh)[i]? = some x →
      denoteMeta mT.acval envT ψ i (Expr.fvarTypeD x)
        = some ((ihdoms.reverse ++ (pdoms ++ fdoms).reverse).getD
            (rP + nF + nR - 1 - i) default))
    (hokΔ : ∀ i, i < rP + nF + nR →
      ∀ ρ : Nat → V, Sat V (ihdoms.reverse ++ (pdoms ++ fdoms).reverse) ρ →
        WellDenotedV V (fun j => ρ (j + (rP + nF + nR - 1 - i) + 1))
          ((ihdoms.reverse ++ (pdoms ++ fdoms).reverse).getD (rP + nF + nR - 1 - i) default))
    (hlbF : ∀ x ∈ fvsPref ++ fvsF ++ fvsIh, (Expr.fvarTypeD x).looseBVarsBounded 0 = true)
    (hcbF : ∀ x ∈ fvsPref ++ fvsF ++ fvsIh, ConstsBound envT x)
    (hclF : ∀ x ∈ fvsPref ++ fvsF ++ fvsIh, ∀ l ∈ (Expr.fvarTypeD x).fvarLeaves,
      Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF ++ fvsIh)
    {ρ₀ : Nat → V} {xs fs ihvals : List V}
    (hsp : SpineFit ρ₀ (pdoms ++ fdoms) (xs ++ fs))
    (hih : SpineFit (consList (xs ++ fs) ρ₀) ihdoms ihvals) :
    WalkCtx V mT ψ (rP + nF + nR) (consList ihvals (consList (xs ++ fs) ρ₀))
      (ihdoms.reverse ++ (pdoms ++ fdoms).reverse) (fvsPref ++ fvsF ++ fvsIh).reverse := by
  have hlenL : (fvsPref ++ fvsF ++ fvsIh).length = rP + nF + nR := by
    rw [List.length_append, List.length_append, openPisAtFvars_length rP h₁,
      openPisAtFvars_length nF h₂, openPisAtFvars_length nR h₃]
  refine ⟨sat_blockFrame_length hp hf hidx, sat_blockFrame hsp hih, ?_, ?_, ?_, ?_, ?_⟩
  · intro j x hx
    have hj : j < rP + nF + nR := by
      have := (List.getElem?_eq_some_iff.mp hx).1
      rw [List.length_reverse, hlenL] at this
      exact this
    rw [List.getElem?_reverse (by rw [hlenL]; exact hj), hlenL] at hx
    have h := hdoms _ x hx
    rwa [show rP + nF + nR - 1 - (rP + nF + nR - 1 - j) = j from by omega] at h
  · intro s hs ρ hρ
    have h := hokΔ (rP + nF + nR - 1 - s) (by omega) ρ hρ
    rwa [show rP + nF + nR - 1 - (rP + nF + nR - 1 - s) = s from by omega] at h
  · exact fun x hx => hlbF x (List.mem_reverse.mp hx)
  · exact fun x hx => hcbF x (List.mem_reverse.mp hx)
  · exact fun x hx l hl => List.mem_reverse.mpr (hclF x (List.mem_reverse.mp hx) l hl)

/-! ## `IhSpineFold` at the run — `ihSpineFold_blockRec`, composed

`ihSpineFold_blockRec` (`BlockRecRule.lean`) carries fifteen premises.
Eleven of them have producers in the tree; this theorem applies them,
and what is left is the four that are about the BLOCK rather than
about the rule's walk.

| premise | producer |
|---|---|
| `hacl`/`hainst`/`hcl` | `EnvModel`'s own fields (`blockRuleHainst`, `blockRuleHcl`) |
| `hfld` | the constructors' stage, MOVED to the consed environment (`fieldReadAt_mono`) |
| `hnofv` | `blockRuleHnofv_of` at the frame's telescope and index data |
| `hi` | the field bound `hfld` already carries |
| `hfit` | `blockRuleHfit_run` — H3′ composed |

**The two environments are named, and they stay apart.**  The field
readings the CONSTRUCTORS' stage produces are at `envT`; the fold
reads the guarded call's arguments at the CONSED environment, where
the rule's recursors live.  `hfld` is therefore stated at `mT` and
transported for `ihSpineFold_blockRec`'s own use — `blockRuleHfit_run`
wants the `envT` form, so the premise is stated once and used at both.

`hcallee` and `hihv` stay premises: the first is a fact about the
block's LEAF valuation (`blockRuleHcallee_of`), the second the
identification of the caller's `ihvals` with the design's ih terms,
and both are the assembly's to pick — this module sits below the
file that fixes either. -/

/-! ## The BODY EQUATION at the run

`BlockRuleResidueB`'s fourth conjunct (`BlockRecData.lean`) asks for
`interp_blockResidue`'s own conclusion at the tower's CORE — the rule
body's reading against the residue's at the `ih` values — and NOT for
the applied form: the β-reduction to `mkAppN Ra (x⃗ ++ f⃗)` is paid on
the model side by `blockRuleHRa_tower_run`.  This is that conclusion
with the two rule-side premises discharged.

`interp_blockResidue` has nineteen premises.  Two of them carry
content — `hspine` (the guarded call's fold) and `hW` (the walk's entry
context); the rest are the environment facts, the frame's three openings and the run-level peel
of the check's own witnesses (`abstractIh`, the scope guards, the two
readings and `IhTyped`), every one of which the rule record
(`RuleRun`) carries.  So the theorem below takes the peel's rows verbatim and
builds the two content premises itself.

**The frame, once.**  `F = rP + nF` is forced by `hF`/`hrP`, so the
walk's entry depth `F + nR` IS the frame's `rP + nF + nR`, which is
where `walkCtx_blockFrame` concludes and where the check's three
openings sit.  `as2` is the opening list itself (`hsx` is
reflexivity); the fold travels with any extension of it. -/

end Run

end ConLeche.Model
