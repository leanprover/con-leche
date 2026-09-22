module

public import ConLeche.Model.Inductives.BlockRecPreRun

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
  (∀ (m : Nat) (cvTb : ConstantVal), cvTas[m]? = some cvTb →
    d.memberName m = cvTb.name ∧ cvTb.levelParams = q.lps ∧
    (∃ caps, envC.find? cvTb.name = some (.indInfo cvTb caps)) ∧
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
  obtain ⟨hnPq, hkq, hcvF, hmsF, -, -⟩ := hmr
  obtain ⟨ms, cvTa, fvs, tfvs, concl, to, maj, hms, hcvTa, hnPle, hmI, hop, hopT, htfl,
    hdeq, hmaj0, hfn, hargl, hargP, hargI⟩ := checkBlockRecK_tyMajor h hr
  obtain ⟨fvsL, conclL, hopL, hread, hmk, hlenRds, hbits, hbind, hconclRead, hwdTy⟩ :=
    checkBlockRecK_tyPis hμ mpC h hr ψ
  have hfvE : fvsL = fvs := by
    have hq := Option.some.inj (hopL.symm.trans hop)
    exact congrArg Prod.fst hq
  rw [hfvE] at hbind
  obtain ⟨hnameMs, hnIdxMs⟩ := hmsF _ _ hms
  obtain ⟨hnameCv, hlpsE, ⟨caps, hfind⟩, -⟩ := hcvF _ _ hcvTa
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

end Run

end ConLeche.Model
