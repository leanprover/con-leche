module

public import ConLeche.Model.Inductives.NestHomeCalls
public import ConLeche.Model.Inductives.NestHomeWalk
import ConLeche.Verify.Inductives.RecCheckRun
import ConLeche.Verify.Inductives.RecHomeRun

public section

/-!
# A hot layer's classes at the walk's nodes (PRIMREC / NESTHOME)

`homeFacts_of`: at a family on the route (`targetRouteOf`) and a hot
layer `n` of its call graph (`targetHot`), the recursor check's run and
the home table the positivity stage computed give the layer's
`HomeFacts` — the classes matched (`homeMatch`) to entries the walk
derived (`homeTable_good`), the consistency checks read at the walk's
context (the checks read only the block's names, `homeLeafKey_congr`),
and the layer's classes carrying the matched entries' normal forms as
their K.53 source (`targetRecRun_homeNfs`, `targetHomeOf_some`).
-/

namespace ConLeche.Model

open ConLeche

section Facts

variable {μ : CheckMode} {F : Nat} {fe : FEnv} {p : BlockShape} {nested : Bool}
  {block : List ConstantInfo} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}

/-- The classes the recursor check matched against the table. -/
@[expose] def homeCls (out : List (ConstantVal × TargetMajor × List Expr)) : List HomeClass :=
  (out.map (·.2.1)).map (·.homeClass)

/-- The recursor check's matching. -/
@[expose] def homeR (p : BlockShape) (aux : NestNodes)
    (out : List (ConstantVal × TargetMajor × List Expr)) : List (Option HomeReach) :=
  (homeCls out).map (homeMatch (p.nestCtx [] (fun _ => none) []) aux.homes)

theorem homeCls_getD {c : Nat} (hc : c < out.length) :
    (homeCls out).getD c default = (tgtMajor out c).homeClass := by
  simp only [homeCls, tgtMajor, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hc, Option.map_some, Option.getD_some]

theorem homeR_getD {aux : NestNodes} {c : Nat} (hc : c < out.length) :
    (homeR p aux out).getD c none =
      homeMatch (p.nestCtx [] (fun _ => none) []) aux.homes (tgtMajor out c).homeClass := by
  simp only [homeR, homeCls, tgtMajor, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hc, Option.map_some, Option.getD_some]

theorem homeR_length {aux : NestNodes} : (homeR p aux out).length = out.length := by
  simp [homeR, homeCls]

theorem tgtRs_length' : (tgtRs out).length = out.length := by simp [tgtRs]

theorem homeCls_length : (homeCls out).length = out.length := by simp [homeCls]

/-- **A hot layer's facts** (see the module docstring). -/
theorem homeFacts_of (R : TargetRecRun μ F fe p nested block cvTas ctorsAs out)
    (hroute : targetRouteOf p (out.map (·.2.1)) = true) {n : Nat}
    (hhot : targetHot p (out.map (·.2.1)) n = true)
    {envI : Env} {ctxW : NestCtx} {holes : List Expr} {ns : List PosTree}
    {ctorsAsW : List (List (ConstantVal × Nat))}
    (W : HomeWalk F envI ctxW holes ns ctorsAsW) (hholes : nestHoles ctxW = some holes)
    (hparams : ∀ x ∈ ctxW.params, ∃ i ty, x = .fvar i ty ∧ i < ctxW.nP)
    (hnames : ctxW.names = p.memberNames) (hnP : ctxW.nP = p.nP) (hlps : ctxW.lps = p.lps)
    {m : Nat}
    (htab : homeTableAt (fueledOps .verified F) envI ctxW holes ctorsAsW m = .ok R.aux.homes) :
    HomeFacts F envI ctxW holes ns ctorsAsW (homeCls out) (homeR p R.aux out) out
      (fun c => (graphRank (targetGraphOf p)).getD c 0 = n) := by
  have hH := targetRecRun_home R hroute hhot
  obtain ⟨hcov, hcons, hpair, hhn⟩ := targetHomeOf_some hH
  have hc0n : (p.nestCtx [] (fun _ => none) []).names = ctxW.names := by
    rw [hnames]; rfl
  have hc0p : (p.nestCtx [] (fun _ => none) []).nP = ctxW.nP := by rw [hnP]; rfl
  have hc0l : (p.nestCtx [] (fun _ => none) []).lps = ctxW.lps := by rw [hlps]; rfl
  have hRb := homeRb_congr hc0n hc0p hc0l
  have hLK := homeLeafKey_congr hc0n hc0p hc0l
  have hRe := homeReachable_congr hc0n hc0p hc0l
  have hgoodT := homeTable_good W htab
  have hlenO : (tgtRs out).length = out.length := tgtRs_length'
  refine {
    W := W, hholes := hholes, hparams := hparams
    hgood := fun c r hr => ?_
    hlen := by simp [homeCls, tgtRs]
    hind := fun c hc => by rw [homeCls_getD (hlenO ▸ hc)]; rfl
    hlvls := fun c hc => by rw [homeCls_getD (hlenO ▸ hc)]; rfl
    hds := fun c hc => by rw [homeCls_getD (hlenO ▸ hc)]; rfl
    hmember := fun c hc => by rw [homeCls_getD (hlenO ▸ hc)]; rfl
    hctorsM := fun c hc _ => by rw [homeCls_getD (hlenO ▸ hc)]; rfl
    hS := fun c hc hSc => ?_
    hcons := fun a r hr hexp e he l hl c hc hSc k hk => ?_
    hpair := fun a c ha hc hSa hSc hmo hi hl hd ra rc hra hrc => ?_
    hnfs := fun c hc hSc r hr => ?_ }
  · -- the matched entry, good
    have hcl : c < out.length := homeR_length (p := p) (aux := R.aux) ▸ getD_none_lt hr
    rw [homeR_getD hcl] at hr
    obtain ⟨e, he, hnfsE, hctE, hcase⟩ := homeMatch_some hr
    obtain ⟨hrun, hkey⟩ := hgoodT e he
    refine ⟨by rw [homeCls_length]; exact hcl, ?_, ?_⟩
    · rw [homeCls_getD hcl, hnfsE, ← hctE]
      rcases hcase with ⟨t, -, -, hek, hrk⟩ | ⟨a, -, hek, hrk, hind, hlv, -, -⟩
      · rw [hrk]; rw [hek] at hrun
        simpa only [homeEntryNfs] using hrun
      · rw [hrk, ← hind, ← hlv]; rw [hek] at hrun; exact hrun
    · rw [homeCls_getD hcl]
      rcases hcase with ⟨t, hmt, hem, hek, hrk⟩ | ⟨a, hmo, hek, hrk, hind, hlv, hnpc, hdsE⟩
      · rw [hrk]
        rw [hek] at hkey
        obtain ⟨t', hem', ht', hct'⟩ := hkey
        rw [hem] at hem'
        obtain rfl := Option.some.inj hem'
        exact ⟨t, hmt, ht', by rw [← hctE]; exact hct'⟩
      · rw [hrk]
        rw [hek] at hkey
        obtain ⟨-, hcont, hmates, -, u, hu, hanc, hds, hlvu, hgrp⟩ := hkey
        refine ⟨hmo, ?_, ?_, ?_, u, hu, hanc, hds, ?_, ?_⟩
        · rw [← hind, ← hnpc, ← hctE]; exact hcont
        · rw [← hind]; exact hmates
        · rw [← hRb]; exact hdsE
        · rw [hlvu, hlv]
        · rw [hgrp, hind]
  · -- covered
    have hcl : c < out.length := hlenO ▸ hc
    have hhc := hcov c (by simpa using hcl)
      (by rw [targetHots_getD (by simpa using hcl), hSc]; exact hhot)
    obtain ⟨hreach, r, hr, hexp⟩ := homeCovered_true hhc
    refine ⟨by rw [← hRe]; exact hreach, r, hr, hexp⟩
  · -- consistent
    have hlenR : (homeR p R.aux out).length = (homeCls out).length := by
      simp [homeR, homeCls]
    rw [← hLK] at hk
    exact homeConsistent_true hlenR hcons a r hr hexp e he l hl c
      (by rw [homeCls_length]; exact hlenO ▸ hc)
      (show (targetHots _ _).getD _ _ = true by
        rw [targetHots_getD (by simpa using hlenO ▸ hc), hSc]; exact hhot) k hk
  · -- one key per instance
    exact homePairConsistent_true hpair a c (by simpa using hlenO ▸ ha)
      (by simpa using hlenO ▸ hc)
      (show (targetHots _ _).getD _ _ = true by
        rw [targetHots_getD (by simpa using hlenO ▸ ha), hSa]; exact hhot)
      (show (targetHots _ _).getD _ _ = true by
        rw [targetHots_getD (by simpa using hlenO ▸ hc), hSc]; exact hhot) hmo hi hl hd ra rc hra hrc
  · -- the K.53 source
    have hcl : c < out.length := hlenO ▸ hc
    have hh := targetRecRun_homeNfs R c hcl
    rw [hhn] at hh
    have hcr : c < (out.map (·.2.1)).length := by simpa using hcl
    have hval : ∀ {β : Type} (f : Nat → Option β),
        ((List.range (out.map (·.2.1)).length).map f).getD c none = f c := by
      intro β f
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hcr, Option.map_some,
        Option.getD_some]
    rw [hval, targetHots_getD hcr, hSc, hhot] at hh
    simp only [if_true] at hh
    have hr' := hr
    simp only [homeR, homeCls] at hr'
    rw [hr', Option.map_some] at hh
    show targetClassNfs (out.getD c default).2.1 = _
    unfold targetClassNfs
    rw [hh]

end Facts

end ConLeche.Model
