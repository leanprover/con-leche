module

public import ConLeche.Model.Inductives.BlockRecTyping
public import ConLeche.Model.Inductives.BlockRecMem
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockFieldRead

public section

/-!
# The recursor type's binder SHAPE, at the run (task #315, M5M-rule)

`BlockRecTyShape` (`Model/Inductives/BlockRecTyping.lean`) is what the
three regimes read off the stored recursor types: the arity, the
parameters, the eliminated member's index telescope and the major.
Every clause of it was a premise; this file is its PRODUCER, from the
recursor stage's run and the members' own former data.

It is a LEAF module and it has to be: it consumes `prefixDoms_spineFit`
(`BlockRecPreRun`) and `checkBlockRecK_tyPis`/`checkBlockRecK_tyMajor`
(`BlockRecMem`, which `BlockRecPreRun` sits above), so it can be an
addition to neither.

**What the check actually pins**, and what each clause is therefore
bounded by (`checkBlockRecTys`, `Kernel/Inductives/BlockInstall.lean`):

* `nP ≤ rP` and `mI = rP + nIdx_m` are the stage's own two `unless`es
  — clauses 1 and 2, arithmetic once the member's index count is
  identified with `nIdx_m` (`FormerData.len`);
* the first `nP` binder DOMAINS are compared BINDER BY BINDER with the
  member's own opened former telescope — clause 3, and it is an
  implication between FITS because the two spellings are never
  compared, only certified defeq: `prefixDoms_spineFit` is the hop,
  and the member-to-member parameter agreement (`paramsIff`) carries
  it from the ELIMINATED member's telescope to the block's;
* the binders `nP … rP-1` and the INDEX binders are never looked
  inside at all.  Clause 4 therefore does not read them: it reads the
  MAJOR, whose domain is `T_m p⃗ ı⃗` on the nose, so its reading is a
  spine against the member's FORMER — a λ-tower — and the spine's
  grading carries the fit (`spineFit_of_major_grading`).  The tower's
  binder numeral is `w ψ + 1`, never zero, so this survives a
  `Prop`-valued block;
* the MAJOR's syntactic pin is clause 6, read off the opening's own
  fvars (`interp_of_major_reading`).

The OPPOSITE direction of clause 4 (`BlockRecTyJoin`) is NOT produced
here and cannot be: nothing in the run ties the recursor's index
binders to the member's telescope except the per-argument `isDefEq`
inside `checkConstantVal`'s inference of the major's domain.
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

/-- **`Sat` at a CONSED frame is the spine's own fit** — the converse
of `sat_of_spineFit` at the frame the spine builds.  `spineFit_of_sat`
recovers a frame and a spine by its own construction; at
`consList xs ρ` with the lengths matching, those two ARE `ρ` and
`xs`. -/
theorem spineFit_of_sat_consList {Ds : List AnnotTerm} {ρ : Nat → V} {xs : List V}
    (hlen : xs.length = Ds.length) (h : Sat V Ds.reverse (consList xs ρ)) :
    SpineFit ρ Ds xs := by
  have h' : Sat V (Ds.reverse ++ []) (consList xs ρ) := by simpa using h
  have hsp := spineFit_of_sat (Ds := Ds) (Δ₀ := []) h'
  have hfr : (fun j => consList xs ρ (j + Ds.length)) = ρ := by
    funext j
    rw [← hlen]
    exact consList_apply_add xs ρ j
  have hys : (List.range Ds.length).reverse.map (consList xs ρ) = xs := by
    rw [← frameIdx_eq_reverse_map, ← hlen]
    exact frameIdx_consList' xs ρ
  rwa [hfr, hys] at hsp

/-- A list's `take n` and `drop n`'s `take m` reassemble its
`take (n + m)`. -/
theorem take_add_eq_append {α : Type u} :
    ∀ (l : List α) (n m : Nat), l.take (n + m) = l.take n ++ (l.drop n).take m
  | [], _, _ => by simp
  | _ :: _, 0, _ => by simp
  | a :: l, n + 1, m => by
    rw [show n + 1 + m = (n + m) + 1 from by omega, List.take_succ_cons,
      List.take_succ_cons, List.drop_succ_cons, take_add_eq_append l n m,
      List.cons_append]

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
two or three of them, and the audit's lesson about bundles
(one per consumer) cuts the other way here: there is ONE consumer, the
shape's producer. -/
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
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
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
  obtain ⟨ms, cvTa, fvs, tfvs, concl, to, maj, hms, hcvTa, hnPle, hmI, hop, hopT, htfl,
    hdeq, hmaj0, hfn, hargl, hargP, hargI⟩ := checkBlockRecK_tyMajor h hr
  obtain ⟨fvsL, conclL, hopL, hread, hmk, hlenRds, hbits, hbind, hconclRead, hwdTy⟩ :=
    checkBlockRecK_tyPis hμ mpC h hr ψ
  have hfvE : fvsL = fvs := by
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
  have hmajTy : Expr.fvarTypeD maj
      = Expr.mkAppN (.const ms.cvT.name (p.toBlockShape.lps.map .param))
        (fvs.take p.nP
          ++ (fvs.drop (p.toBlockShape.rulePrefixAt c)).take ms.nIdx) := by
    conv => lhs; rw [← ConLeche.Expr.mkAppN_getApp (Expr.fvarTypeD maj)]
    rw [hfn, ← hargP, ← hargI, List.take_append_drop]
  -- the head
  have hnameEq : ms.cvT.name = cvTa.name := by rw [← hnameMs, hnameCv]
  have hconst : denoteMeta mpC.base2.acval envC ψ (p.toBlockShape.majorIdxAt c)
      (.const ms.cvT.name (p.toBlockShape.lps.map .param))
      = some (mpC.base2.acval (d.memberName (p.toBlockShape.recTgtAt c)) ψ) := by
    rw [denoteMeta_const (ci := .indInfo cvTa caps) (by rw [hnameEq]; exact hfind)
      (by rw [show (ConstantInfo.indInfo cvTa caps).toConstantVal = cvTa from rfl, hlpsE,
        List.length_map])]
    rw [show (ConstantInfo.indInfo cvTa caps).toConstantVal = cvTa from rfl, hlpsE,
      Level.substFn_param_self, hnameMs]
  -- the two argument spines
  have hlenFvs : fvs.length = p.toBlockShape.majorIdxAt c + 1 :=
    ConLeche.Verify.openPisAtFvars_length _ hop
  have hidxFvs := ConLeche.openPisAtFvars_index _ _ _ hop
  have hlenTake : (fvs.take p.nP).length = p.nP := by
    rw [List.length_take, hlenFvs]; omega
  have hidxTake : ∀ (k : Nat) (x : Expr), (fvs.take p.nP)[k]? = some x →
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
  have hlenI : ((fvs.drop (p.toBlockShape.rulePrefixAt c)).take ms.nIdx).length = ms.nIdx := by
    rw [List.length_take, List.length_drop, hlenFvs]; omega
  have hidxI : ∀ (k : Nat) (x : Expr),
      ((fvs.drop (p.toBlockShape.rulePrefixAt c)).take ms.nIdx)[k]? = some x →
      ∃ ty, x = Expr.fvar (p.toBlockShape.rulePrefixAt c + k) ty := by
    intro k x hx
    have hk : k < ms.nIdx := by
      have := (List.getElem?_eq_some_iff.mp hx).1
      rw [hlenI] at this; exact this
    rw [List.getElem?_take, if_pos hk, List.getElem?_drop] at hx
    obtain ⟨ty, hty⟩ := hidxFvs _ x hx
    exact ⟨ty, by rw [hty, Nat.zero_add]⟩
  have hspI0 := denoteMetaSpine_fvars (acval := mpC.base2.acval) (env := envC) (φ := ψ)
    (p.toBlockShape.majorIdxAt c) ((fvs.drop (p.toBlockShape.rulePrefixAt c)).take ms.nIdx)
    (p.toBlockShape.rulePrefixAt c) hidxI
  rw [hlenI] at hspI0
  have hteleE : ((List.range ms.nIdx).map fun k =>
        (AnnotTerm.bvar (p.toBlockShape.majorIdxAt c - 1
          - (p.toBlockShape.rulePrefixAt c + k))))
      = teleVarsAV ms.nIdx := by
    rw [teleVarsAV]
    refine List.map_congr_left fun k hk => ?_
    have hk' : k < ms.nIdx := by simpa using hk
    rw [hmI]
    congr 1
    omega
  rw [hteleE] at hspI0
  -- the reading, and its position in the binder data
  have hreadMaj : denoteMeta mpC.base2.acval envC ψ (p.toBlockShape.majorIdxAt c)
      (Expr.fvarTypeD maj)
      = some (AnnotTerm.mkAppN
          (mpC.base2.acval (d.memberName (p.toBlockShape.recTgtAt c)) ψ)
          (paramBvarsAt p.nP (p.toBlockShape.majorIdxAt c) ++ teleVarsAV ms.nIdx)) := by
    rw [hmajTy, denoteMeta_mkAppN_of _ hconst (DenoteMetaSpine.append hspP hspI0)]
  obtain ⟨pd, hpd, -, hreadB⟩ := hbind _ maj hmaj0
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
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
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
  obtain ⟨-, -, -, -, hmk, -, -, -, -, hwdTy⟩ := checkBlockRecK_tyPis hμ mpC h hr ψ
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
`isDefEq` per position.  So the clause is an implication between FITS
(`prefixDoms_spineFit`, the certified hop), followed by the members'
own parameter agreement (`BlockFormerFacts.paramsIff`) from the
eliminated member's telescope to the block's `d.params`. -/

/-- **The block's parameter telescope fits, at the run** — clause 3 of
the shape. -/
theorem blockRecParams_run (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) (ψ : Name → Nat) (ρ : Nat → V) :
    ∀ xs : List V,
      SpineFit ρ (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map
        (·.2.2)).take d.nP) xs → SpineFit ρ (d.params ψ) xs := by
  intro xs hfit
  obtain ⟨hnPle, hmemk, hmI, hlenRds, -⟩ := blockRecMajor_run hμ mpC h hmr hr ψ
  obtain ⟨hnPq, hkq, hlenCv, hcvF, -, -, hparIff⟩ := hmr
  obtain ⟨ms, cvTa, fvs, tfvs, concl, to, maj, hms, hcvTa, -, -, hop, hopT, htfl,
    hdeq, -, -, -, -, -⟩ := checkBlockRecK_tyMajor h hr
  obtain ⟨fvsL, conclL, hopL, hread, hmk, -, -, hbind, -, hwdTy⟩ :=
    checkBlockRecK_tyPis hμ mpC h hr ψ
  have hfvE : fvsL = fvs := congrArg Prod.fst (Option.some.inj (hopL.symm.trans hop))
  rw [hfvE] at hbind
  obtain ⟨-, -, -, hfvT, hbndT, hFD⟩ := hcvF _ _ hcvTa
  have hppsLen : (d.ppsM (p.toBlockShape.recTgtAt c) ψ).length
      = d.nP + d.nIdxAt (p.toBlockShape.recTgtAt c) := hFD.len ψ
  -- the two openings, at the block's parameter count
  obtain ⟨hwA, hbA⟩ := checkBlockRecK_tyClosed h hr
  obtain ⟨fvsA, fvs', oA, hopA, -, hfvsplit⟩ :=
    openPisAtFvars_split (e := r.1.type) (d := 0) p.nP
      (by rw [show p.nP + (p.toBlockShape.majorIdxAt c + 1 - p.nP)
            = p.toBlockShape.majorIdxAt c + 1 from by omega]
          exact hop)
  have hlenA : fvsA.length = p.nP := ConLeche.Verify.openPisAtFvars_length _ hopA
  have hfvsA : fvs.take p.nP = fvsA := by
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
    have hx' : fvs[i]? = some x := by
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
  have hdB : ∀ (i : Nat) (x : Expr), tfvs[i]? = some x →
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
  -- **the certified hop**
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
  -- the members' own parameter agreement
  have hxl : xs.length = d.nP := by
    rw [hfitB.length_eq, List.length_map, List.length_take, hppsLen]; omega
  have hsat : Sat V ((((d.ppsM (p.toBlockShape.recTgtAt c) ψ).take d.nP).map
      (·.2.2)).reverse) (consList xs ρ) := by
    simpa using sat_of_spineFit (Sat_nil V ρ) hfitB
  refine spineFit_of_sat_consList ?_ ((hparIff _ hmemk ψ _).mp hsat)
  obtain ⟨cvT0, hcvT0⟩ : ∃ cvT0, cvTas[0]? = some cvT0 :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlenCv]; omega)⟩
  obtain ⟨-, -, -, -, -, hFD0⟩ := hcvF _ _ hcvT0
  rw [hxl, BlockData.params, List.length_map, List.length_take, hFD0.len ψ]
  omega

/-! ## 6. THE SHAPE, at the run -/

/-- **`BlockRecTyShape` FROM THE RUN** — the recursor-type lane's
premise, discharged.

Its five clauses, in order: the two the stage's own `unless`es pin
(`nP ≤ rP`, the binder count), the parameters as an implication
between FITS (`blockRecParams_run`), the eliminated member's index fit
(`blockRecIdxFit_run`) and the MAJOR's reading folded into
applications (`interp_of_major_reading`).

`BlockRecTyJoin` — the index clause's OPPOSITE direction — is NOT
among them and is not produced here: nothing in the run ties the
recursor's index binders to the member's telescope. -/
theorem blockRecTyShape_run (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
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

/-! ## 7. The `ih` KEY's block facts (task #315, `hkey` half A)

`blockIndRegime_run`'s `hihOpen` (`BlockRecPreRun.lean`) splits in two
with very different provenances:

* **(A) the KEY's block facts** — the field is in range, it is
  RECURSIVE or REFLEXIVE, it targets the callee's member, and the
  callee's class is in range.  These are decided by `blockIhKeys`'
  own filter and by the block's tables, and they are proved here;
* **(B) `eisA`/`fapA`/`BlockRuleConclAt` and the DOMAIN equation** —
  ONE reading of the generated `blockIhPis` opener.  They are NOT
  proved here; they are the half `blockRuleHopener_of`
  (`BlockRecOpenerRead.lean`) and `blockRuleHconcl_of` deliver, which
  is why `hihDom`/`hihBits`/`hkey` are now the single premise
  `hihOpen` rather than three premises about one term.

The keys are the CHECK's own list (`BlockInstall.lean`'s
`ihKeys := blockIhKeys rP rPs recTgts ks`), so nothing here is
quantified over an arbitrary key list; and the block-table bridges are
premises because they are `rfl` at `blockDataOf` and this module may
not name that record. -/

section Keys

open ConLeche (BlockFieldKind blockIhKeys blockTgtsOf)

/-- A key at a position is a member of the key list. -/
theorem mem_blockIhKeys_getD {rP : Nat} {rPs recTgts : List Nat}
    {ks : List BlockFieldKind} {r i c' : Nat}
    (hkey : (blockIhKeys rP rPs recTgts ks).getD r (0, 0) = (i, c'))
    (hr : r < (blockIhKeys rP rPs recTgts ks).length) :
    (i, c') ∈ blockIhKeys rP rPs recTgts ks := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr, Option.getD_some] at hkey
  exact hkey ▸ List.getElem_mem hr

/-- **A key's field is RECURSIVE or REFLEXIVE and in range** —
`pairIdxOf_blockIhKeys_kind`, at membership rather than at a
`pairIdxOf?` (the regime reads its keys off a POSITION, not off a
lookup). -/
theorem mem_blockIhKeys_kind {rP : Nat} {rPs recTgts : List Nat}
    {ks : List BlockFieldKind} {i c' : Nat}
    (hmem : (i, c') ∈ blockIhKeys rP rPs recTgts ks) :
    i < ks.length ∧
      ((ks.map BlockFieldKind.toRec).getD i .ordinary = .recursive ∨
        (ks.map BlockFieldKind.toRec).getD i .ordinary = .reflexive) := by
  simp only [ConLeche.blockIhKeys, List.mem_flatMap, List.mem_filterMap,
    List.mem_range] at hmem
  obtain ⟨i', hi', c'', -, hite⟩ := hmem
  have hiEq : i' = i := by
    split at hite
    · exact (Prod.mk.inj (Option.some.inj hite)).1
    · exact nomatch hite
  subst hiEq
  exact mem_blockRecIdxOf hi'

/-- **A key's callee shares the rule's prefix and is the field's
target** — `pairIdxOf_blockIhKeys_rP`, at membership. -/
theorem mem_blockIhKeys_rP {rP : Nat} {rPs recTgts : List Nat}
    {ks : List BlockFieldKind} {i c' : Nat}
    (hmem : (i, c') ∈ blockIhKeys rP rPs recTgts ks) :
    c' < recTgts.length ∧ rPs.getD c' 0 = rP ∧
      (ks.getD i .ordinary).tgt? = some (recTgts.getD c' recTgts.length) := by
  simp only [ConLeche.blockIhKeys, List.mem_flatMap, List.mem_filterMap,
    List.mem_range] at hmem
  obtain ⟨i', -, c'', hc'', hite⟩ := hmem
  split at hite
  · rename_i hcond
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hite)
    simp only [Bool.and_eq_true] at hcond
    exact ⟨hc'', by simpa using hcond.2, by simpa using hcond.1⟩
  · exact nomatch hite

omit [SetTheory V] in
/-- **`hkey`'s half A, at the run.**  Everything the KEY decides,
read against the block's own tables. -/
theorem blockIhKey_block_facts {d : BlockData V} {ψ : Name → Nat}
    {K mm j r i c' rP : Nat} {mem : Nat → Nat}
    {rPs recTgts : List Nat} {ks : List BlockFieldKind} {cA : ConstantVal × Nat}
    (hcj : (d.ctorsM mm)[j]? = some cA)
    (hksF : d.ksF mm j = ks.map BlockFieldKind.toRec)
    (hksLen : ks.length = cA.2)
    (hFssLen : ((d.Fss mm ψ).getD j []).length = cA.2)
    (htgtsF : ∀ l, d.tgts mm j l = (blockTgtsOf ks).getD l 0)
    (hrecTgtsLen : recTgts.length = K)
    (hrecTgts : ∀ q, q < K → recTgts.getD q K = mem q)
    (hkey : (blockIhKeys rP rPs recTgts ks).getD r (0, 0) = (i, c'))
    (hr : r < (blockIhKeys rP rPs recTgts ks).length) :
    c' < K ∧
      i < ((d.Fss mm ψ).getD j []).length ∧
      ((d.rss mm).getD j []).getD i false = true ∧
      d.tgts mm j i = mem c' ∧
      rPs.getD c' 0 = rP := by
  have hmem := mem_blockIhKeys_getD hkey hr
  obtain ⟨hiL, hkind⟩ := mem_blockIhKeys_kind hmem
  obtain ⟨hc'L, hrPs, htgt⟩ := mem_blockIhKeys_rP hmem
  have hc'K : c' < K := by rw [← hrecTgtsLen]; exact hc'L
  have hjl : j < (d.ctorsM mm).length := (List.getElem?_eq_some_iff.mp hcj).1
  have hiF : i < ((d.Fss mm ψ).getD j []).length := by rw [hFssLen, ← hksLen]; exact hiL
  refine ⟨hc'K, hiF, ?_, ?_, hrPs⟩
  · have hrss : (d.rss mm).getD j [] = rsOf (d.ksF mm j) := rssOfK_getD hjl
    rw [hrss, rsOf_getD (by rw [hksF, List.length_map]; exact hiL), hksF,
      getD_map_toRec]
    refine decide_eq_true ?_
    rcases hkind with hk | hk <;> rw [getD_map_toRec] at hk
    · exact Or.inl hk
    · exact Or.inr hk
  · -- the target: the kind's `tgt?` and `blockTgtsOf` are one answer
    rw [htgtsF i, getD_blockTgtsOf]
    rw [hrecTgtsLen, hrecTgts c' hc'K] at htgt
    cases hq : ks.getD i .ordinary with
    | recursive t =>
      rw [hq] at htgt
      exact Option.some.inj htgt
    | reflexive t =>
      rw [hq] at htgt
      exact Option.some.inj htgt
    | ordinary => rw [hq] at htgt; exact nomatch htgt
    | negative => rw [hq] at htgt; exact nomatch htgt
    | unsupported => rw [hq] at htgt; exact nomatch htgt

end Keys

end Run

end ConLeche.Model
