module

import ConLeche.Model.Cover
public import ConLeche.Model.Inductives.BlockRep
import ConLeche.Model.Inductives.BlockStageRec
import ConLeche.Verify.Extend.Inversions
import ConLeche.Verify.ExceptBind
import ConLeche.Verify.InferLemmas
import ConLeche.Model.Annot.CanonCrest

public section

/-!
# Coverage across the uniform block install

The glue `declBlock` uses to carry `LfpCover` (`Model/Cover.lean`)
through the uniform install: a stage that conses a LIST of fresh,
non-table constants on top of the environment, with a carrier that
keeps every old name's leaf, keeps coverage (`lfpCover_append`); the
kernel's cons functions' constant lists (`consBlockInds_consts`,
`consBlockCtors_consts`, `consBlockRecsT_consts`); and the block's own
constructor ownership at its constructors' environment
(`blockLfpOwn`), from the constructor check's result head
(`checkSumCtor_shape`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.Verify
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockShape)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## An environment extended by a list of constants -/

theorem find?_append (new : List ConstantInfo) (env : Env) (n : Name) :
    Env.find? ⟨new ++ env.consts⟩ n = (new.find? (·.name == n)).or (env.find? n) := by
  simp only [Env.find?, List.find?_append]

theorem find?_append_none {new : List ConstantInfo} {n : Name}
    (h : ∀ c ∈ new, c.name ≠ n) : new.find? (·.name == n) = none := by
  rw [List.find?_eq_none]
  intro c hc
  simpa using h c hc

theorem find?_append_of_fresh {new : List ConstantInfo} {env : Env}
    (hfresh : ∀ c ∈ new, env.find? c.name = none) {n : Name} {ci : ConstantInfo}
    (h : env.find? n = some ci) : Env.find? ⟨new ++ env.consts⟩ n = some ci := by
  rw [find?_append, find?_append_none (fun c hc hh => by
    have := hfresh c hc; rw [hh, h] at this; exact nomatch this)]
  exact h

theorem findProj?_append_none {new : List ConstantInfo} {env : Env}
    (hntc : ∀ c ∈ new, ∀ tbl, c ≠ .projInfo tbl) (sn : Name) (i : Nat)
    (h : env.findProj? sn i = none) : Env.findProj? ⟨new ++ env.consts⟩ sn i = none := by
  induction new with
  | nil => exact h
  | cons c rest ih =>
    exact findProj?_cons_of_base_none (env := ⟨rest ++ env.consts⟩)
      (hntc c List.mem_cons_self) sn i
      (ih fun c' hc' => hntc c' (List.mem_cons_of_mem _ hc'))

/-- **Coverage across a stage that conses a list of non-table constants**
on top of the environment, keeping every lookup, at a carrier that
keeps every old name's leaf: the carrier rebuilt with the input's
recorded list (the clauses re-read through the monotone crossing), and
coverage carried to an exemption list that holds the new inductives. -/
theorem lfpCover_append {env env' : Env} {new : List ConstantInfo} (mp : EnvModelM V μ env)
    (mpX : EnvModelM V μ env') {ex ex' : List Name}
    (henv : env'.consts = new ++ env.consts)
    (hfwd : ∀ n ci, env.find? n = some ci → env'.find? n = some ci)
    (hntc : ∀ c ∈ new, ∀ tbl, c ≠ .projInfo tbl)
    (hag : ∀ n, (env.find? n).isSome = true → mpX.base2.acval n = mp.base2.acval n)
    (hex : ∀ n ∈ ex, n ∈ ex')
    (hex' : ∀ n ∈ ex', n ∈ ex ∨ env.find? n = none)
    (hind : ∀ c ∈ new, ∀ cv caps, c = .indInfo cv caps → c.name ∈ ex')
    (hhead : ∀ c ∈ new, ∀ C, (ctorEntry C c).isSome = true →
      C ∈ ex ∨ env.find? C = none ∨
        ∃ cv caps, env.find? C = some (.indInfo cv caps) ∧ caps.all = []) :
    ∃ mk : EnvModelM V μ env', mk.base2 = mpX.base2 ∧ mk.lfpBlocks = mp.lfpBlocks ∧
      (LfpCover mp ex → LfpCover mk ex') := by
  obtain ⟨cs⟩ := env'
  simp only at henv
  subst henv
  have hbound := ConLeche.Semantics.envWF_constsBound mp.base2.wf
  have hden : ∀ (ψ : Name → Nat) (d : Nat) (e : Expr), ConstsBound env e →
      ∀ {ea : AnnotTerm}, denoteMeta mp.base2.acval env ψ d e = some ea →
        denoteMeta mpX.base2.acval ⟨new ++ env.consts⟩ ψ d e = some ea := by
    intro ψ d e hcb ea h
    refine denoteMeta_envExtend_mono (fun hf => hfwd _ _ hf)
      ⟨natLitSupported_mono_of_keep hfwd, strLitSupported_mono_of_keep hfwd⟩
      (findProj?_append_none hntc) d e hcb ?_
    rw [denoteMeta_acval_congr (env := env) hag]
    exact h
  have hok := mp.lfp_ok_transport (acval' := mpX.base2.acval)
    (fun n ci hf _ => hfwd n ci hf) (fun n _ hf _ => hag n (by rw [hf]; rfl))
    (fun _ _ _ hf ψ _ hta =>
      hden ψ 0 _ (hbound _ (ConLeche.Semantics.Env.find?_mem hf)).1 hta)
    (fun _ _ _ _ hf ψ _ hta =>
      hden ψ 0 _ (hbound _ (ConLeche.Semantics.Env.find?_mem hf)).1 hta)
    (fun _ _ _ _ hf _ _ _ hA ψ _ hta =>
      hden ψ _ _ (canonCrest_constsBound
        (hbound _ (ConLeche.Semantics.Env.find?_mem hf)).1 hA) hta)
  refine ⟨{ mpX with lfpBlocks := mp.lfpBlocks, lfp_ok := hok }, rfl, rfl, fun hc => ?_⟩
  refine hc.ext rfl hfwd ?_ hex' ?_
  · intro n cv caps hf hn _
    rw [find?_append] at hf
    cases hnew : new.find? (·.name == n) with
    | some c =>
      rw [hnew] at hf
      obtain rfl := Option.some.inj hf
      have hmem := List.mem_of_find?_eq_some hnew
      have hname : (ConstantInfo.indInfo cv caps).name = n := by
        simpa using List.find?_some hnew
      exact absurd (hname ▸ hind _ hmem cv caps rfl) hn
    | none =>
      rw [hnew] at hf
      exact ⟨hf, fun h' => hn (hex n h')⟩
  · intro C hC hCex hall
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hC
    refine nestContainer_congr (by rw [hfwd _ _ hci, hci]) fun n => ?_
    simp only [ctorLook]
    cases hn : env.find? n with
    | some c => rw [hfwd _ _ hn]
    | none =>
      rw [find?_append, hn, Option.or_none]
      cases hnew : new.find? (·.name == n) with
      | none => rfl
      | some c =>
        have hmem := List.mem_of_find?_eq_some hnew
        simp only [Option.bind_some, Option.bind_none]
        cases hent : ctorEntry C c with
        | none => rfl
        | some _ =>
          rcases hhead c hmem C (by rw [hent]; rfl) with h' | h' | ⟨cv, caps, hf, hnil⟩
          · exact absurd h' hCex
          · rw [h'] at hci; exact nomatch hci
          · exact absurd hnil (hall cv caps hf)

/-! ## The kernel's cons functions, as lists -/

theorem consSumCtors_consts (nP : Nat) :
    ∀ (cs : List (ConstantVal × Nat)) (env : Env),
      (ConLeche.consSumCtors nP cs env).consts
        = (cs.map fun c => ConstantInfo.ctorInfo c.1 nP c.2).reverse ++ env.consts
  | [], _ => rfl
  | c :: cs, env => by
    rw [show ConLeche.consSumCtors nP (c :: cs) env
      = ConLeche.consSumCtors nP cs ⟨.ctorInfo c.1 nP c.2 :: env.consts⟩ from rfl,
      consSumCtors_consts nP cs]
    simp

theorem consBlockCtors_consts (nP : Nat) :
    ∀ (L : List (List (ConstantVal × Nat))) (env : Env),
      (ConLeche.consBlockCtors nP L env).consts
        = (L.flatten.map fun c => ConstantInfo.ctorInfo c.1 nP c.2).reverse ++ env.consts
  | [], _ => rfl
  | l :: L, env => by
    rw [show ConLeche.consBlockCtors nP (l :: L) env
      = ConLeche.consBlockCtors nP L (ConLeche.consSumCtors nP l env) from rfl,
      consBlockCtors_consts nP L, consSumCtors_consts]
    simp

theorem consBlockInds_consts {p₁ : BlockShape} {isRec : Bool} :
    ∀ (cvs : List ConstantVal) (i : Nat) (env : Env), ∃ new : List ConstantInfo,
      (ConLeche.consBlockInds p₁ isRec cvs i env).consts = new ++ env.consts ∧
      ∀ c ∈ new, ∃ cv ∈ cvs, ∃ j, c = .indInfo cv (ConLeche.blockCapsAt p₁ j isRec)
  | [], _, _ => ⟨[], rfl, fun _ h => nomatch h⟩
  | cv :: rest, i, env => by
    obtain ⟨new, hnew, hall⟩ := consBlockInds_consts (p₁ := p₁) (isRec := isRec) rest (i + 1)
      ⟨.indInfo cv (ConLeche.blockCapsAt p₁ i isRec) :: env.consts⟩
    refine ⟨new ++ [.indInfo cv (ConLeche.blockCapsAt p₁ i isRec)], ?_, fun c hc => ?_⟩
    · show (ConLeche.consBlockInds p₁ isRec rest (i + 1) _).consts = _
      rw [hnew]; simp
    · rcases List.mem_append.mp hc with h | h
      · obtain ⟨cv', hcv', j, rfl⟩ := hall c h
        exact ⟨cv', List.mem_cons_of_mem _ hcv', j, rfl⟩
      · rw [List.mem_singleton.mp h]
        exact ⟨cv, List.mem_cons_self, i, rfl⟩


/-- The recursors' cons at the majors (`consBlockRecsT`), as a list. -/
theorem consBlockRecsT_consts {find? : Name → Option ConstantInfo} {res : Expr → Bool}
    {q : BlockShape} :
    ∀ (m : Nat) (out : List (ConstantVal × ConLeche.TargetMajor × List Expr))
      (env : Env), ∃ new : List ConstantInfo,
      (ConLeche.consBlockRecsT find? res q m out env).consts = new ++ env.consts ∧
      ∀ c ∈ new, ∃ o ∈ out, ∃ mI rP rules, c = .recInfo o.1 mI rP rules
  | _, [], _ => ⟨[], rfl, fun _ h => nomatch h⟩
  | m, o :: rest, env => by
    obtain ⟨cv, M, rhss⟩ := o
    obtain ⟨new, hnew, hall⟩ := consBlockRecsT_consts (find? := find?) (res := res) (q := q)
      (m + 1) rest ⟨.recInfo cv (q.majorIdxAt m) (q.rulePrefixAt m)
        (ConLeche.tgtStoredRules find? res cv (q.majorIdxAt m) (q.rulePrefixAt m) M rhss)
          :: env.consts⟩
    refine ⟨new ++ [.recInfo cv (q.majorIdxAt m) (q.rulePrefixAt m)
        (ConLeche.tgtStoredRules find? res cv (q.majorIdxAt m) (q.rulePrefixAt m) M rhss)],
      ?_, fun c hc => ?_⟩
    · show (ConLeche.consBlockRecsT find? res q (m + 1) rest _).consts = _
      rw [hnew]; simp
    · rcases List.mem_append.mp hc with h | h
      · obtain ⟨r', hr', rest'⟩ := hall c h
        exact ⟨r', List.mem_cons_of_mem _ hr', rest'⟩
      · rw [List.mem_singleton.mp h]
        exact ⟨_, List.mem_cons_self, _, _, _, rfl⟩

/-- A name absent above the cons at the majors was absent below it. -/
theorem find?_none_consBlockRecsT {find? : Name → Option ConstantInfo} {res : Expr → Bool}
    {q : BlockShape} :
    ∀ {m : Nat} {out : List (ConstantVal × ConLeche.TargetMajor × List Expr)} {env : Env}
      {n : Name}, (ConLeche.consBlockRecsT find? res q m out env).find? n = none →
      env.find? n = none
  | _, [], _, _, h => h
  | m, (cv, M, rhss) :: rest, env, n, h => by
    have h' := find?_none_consBlockRecsT (m := m + 1) (out := rest) h
    rw [ConLeche.Env.find?_cons] at h'
    split at h'
    · exact nomatch h'
    · exact h'

/-! ## The block's own constructor ownership -/

theorem getAppFn_mkAppN_const (n : Name) (us : List Level) (args : List Expr) :
    (Expr.mkAppN (.const n us) args).getAppFn = .const n us := by
  rw [ConLeche.Expr.getAppFn_mkAppN]; rfl

/-- A former's check leaves its level parameters distinct. -/
theorem checkBlockTele_nodup {env : Env} {nP : Nat} {ms : ConLeche.MemberShape} {F : Nat}
    {r : ConstantVal × Level}
    (h : ConLeche.checkBlockTele (ConLeche.fueledOps μ F) env nP ms = .ok r) :
    ms.cvT.levelParams.Nodup := by
  unfold ConLeche.checkBlockTele at h
  obtain ⟨cv, hcv, -⟩ := exceptBind_ok h
  exact nodup_of_nameNodup (ConLeche.checkConstantVal_inv hcv).2.2.2.1

theorem blockCapsAt_all (p : BlockShape) (mi : Nat) (isRec : Bool) :
    (ConLeche.blockCapsAt p mi isRec).all = p.memberNames := by
  unfold ConLeche.blockCapsAt; split <;> rfl

theorem blockCapsAt_nparams (p : BlockShape) (mi : Nat) (isRec : Bool) :
    (ConLeche.blockCapsAt p mi isRec).nparams = p.nP := by
  unfold ConLeche.blockCapsAt; split <;> rfl

theorem blockCapsAt_ctors (p : BlockShape) (mi : Nat) (isRec : Bool) :
    (ConLeche.blockCapsAt p mi isRec).ctors = (p.members.getD mi default).ctors.map (·.1.name) := by
  unfold ConLeche.blockCapsAt
  split
  · next h => rw [h]; rfl
  · rfl

/-- The stored constructors' names, member by member, are the
recogniser's. -/
theorem ctorsAs_names_getD :
    ∀ {ctorsAs : List (List (ConstantVal × Nat))} {members : List ConLeche.MemberShape},
    ctorsAs.map (·.map (fun cA => (cA.1.name, cA.2)))
      = members.map (fun ms => ms.ctors.map (fun c => (c.1.name, c.2))) →
    ∀ (m : Nat),
    (ctorsAs.getD m []).map (·.1.name) = (members.getD m default).ctors.map (·.1.name)
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => nomatch h
  | _ :: _, [], h, _ => nomatch h
  | cs :: C, ms :: M, h, m => by
    simp only [List.map_cons, List.cons.injEq] at h
    cases m with
    | zero =>
      have h1 := congrArg (List.map Prod.fst) h.1
      simpa [List.map_map, Function.comp_def] using h1
    | succ m => exact ctorsAs_names_getD h.2 m

omit [SetTheory V] in
/-- **The block's constructor ownership at its constructors'
environment**: every member's recorded constructor names
(`IndCaps.ctors`, the member's constructors in order) look up the
constructors the block stored, each concluding in its member (the heads
are the check's, `checkSumCtor_shape`). -/
theorem blockLfpOwn {envC : Env} {d : BlockData V}
    {ctorsAs : List (List (ConstantVal × Nat))} {lps : List Name}
    (hctorsM : ∀ c, d.ctorsM c = ctorsAs.getD c [])
    (hhead : ∀ m, m < d.k → ∀ cA ∈ ctorsAs.getD m [], ∃ bs body us,
      cA.1.type.stripPis (d.nP + cA.2) = some (bs, body) ∧
      body.getAppFn = .const (d.memberName m) us)
    (hfindT : ∀ m, m < d.k → ∃ cv caps, envC.find? (d.memberName m) = some (.indInfo cv caps) ∧
      caps.nparams = d.nP ∧ cv.levelParams = lps ∧
      caps.ctors = (ctorsAs.getD m []).map (·.1.name))
    (hlps : lps.Nodup)
    (hparams : ∀ ψ, (d.params ψ).length = d.nP)
    (hfindC : ∀ c, c < d.k → ∀ (j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      envC.find? cA.1.name = some (.ctorInfo cA.1 d.nP cA.2))
    (hshape : ∀ m, m < d.k → ∀ cA ∈ ctorsAs.getD m [], ∃ bs args,
      cA.1.type.stripPis (d.nP + cA.2)
        = some (bs, Expr.mkAppN (.const (d.memberName m) (cA.1.levelParams.map .param)) args) ∧
      ∀ ψ, args.length = d.nP + (d.IdsM m ψ).length) :
    LfpOwn envC d.toLfp := by
  -- a member's recorded constructors, looked up
  have hentry : ∀ c, c < d.k → ∀ caps : ConLeche.IndCaps,
      caps.ctors = (ctorsAs.getD c []).map (·.1.name) →
      caps.ctors.filterMap (ctorLook envC.find? (d.memberName c))
        = (ctorsAs.getD c []).map fun cA => (cA.1, d.nP, cA.2) := by
    intro c hc caps hcs
    rw [hcs, List.filterMap_map]
    have hall : ∀ a ∈ ctorsAs.getD c [],
        ((ctorLook envC.find? (d.memberName c)) ∘ fun cA => cA.1.name) a
          = some (a.1, d.nP, a.2) := by
      intro a ha
      obtain ⟨bs, body, us, hs, hg⟩ := hhead c hc a ha
      have ha' : a ∈ d.ctorsM c := by rw [hctorsM]; exact ha
      obtain ⟨j, hj⟩ := List.getElem?_of_mem ha'
      show (envC.find? a.1.name).bind (ctorEntry (d.memberName c)) = _
      rw [hfindC c hc j a hj, Option.bind_some]
      exact ctorEntry_self rfl hs hg
    generalize ctorsAs.getD c [] = l at hall
    induction l with
    | nil => rfl
    | cons a l ih =>
      rw [List.filterMap_cons, hall a List.mem_cons_self, List.map_cons,
        ih fun a' ha' => hall a' (List.mem_cons_of_mem _ ha')]
  have hnc : ∀ c, c < d.k → ∃ cv caps, envC.find? (d.memberName c) = some (.indInfo cv caps) ∧
      caps.nparams = d.nP ∧ cv.levelParams = lps ∧
      ConLeche.nestContainer (envCtx envC) (d.memberName c)
        = nestPick caps ((ctorsAs.getD c []).map fun cA => (cA.1, d.nP, cA.2)) := by
    intro c hc
    obtain ⟨cv, caps, hf, hnp, hl, hcs⟩ := hfindT c hc
    refine ⟨cv, caps, hf, hnp, hl, ?_⟩
    rw [nestContainer_eq]
    show (match envC.find? (d.memberName c) with
      | some (.indInfo _ caps) =>
        nestPick caps (caps.ctors.filterMap (ctorLook envC.find? (d.memberName c)))
      | _ => none) = _
    rw [hf]
    show nestPick caps (caps.ctors.filterMap (ctorLook envC.find? (d.memberName c))) = _
    rw [hentry c hc caps hcs]
  have hpick : ∀ (caps : ConLeche.IndCaps) (l : List (ConstantVal × Nat)), l ≠ [] →
      nestPick caps (l.map fun cA => (cA.1, d.nP, cA.2)) = some (d.nP, l) := by
    intro caps l hl
    obtain ⟨a, l', rfl⟩ := List.exists_cons_of_ne_nil hl
    simp [nestPick, List.map_map, Function.comp_def]
  refine ⟨fun c hc => ?_, fun c hc nP' hL => ?_, fun c hc => ?_, fun c hc j hj => ?_⟩
  · obtain ⟨cv, caps, -, hnp, -, hN⟩ := hnc c hc
    show ∃ nP' L, ConLeche.nestContainer (envCtx envC) (d.memberName c) = some (nP', L) ∧ _
    rw [hN]
    by_cases hl : ctorsAs.getD c [] = []
    · refine ⟨caps.nparams, [], by rw [hl]; rfl, ?_, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
      show 0 = (d.ctorsM c).length
      rw [hctorsM, hl]; rfl
    · refine ⟨d.nP, ctorsAs.getD c [], hpick caps _ hl, by
        show _ = (d.ctorsM c).length; rw [hctorsM], fun j hj => ?_⟩
      have hj' : (d.ctorsM c)[j]? = some (ctorsAs.getD c [])[j] := by
        rw [hctorsM]; exact List.getElem?_eq_getElem hj
      show envC.find? ((d.ctorsM c).getD j default).1.name = _
      rw [List.getD_eq_getElem?_getD, hj', Option.getD_some]
      exact hfindC c hc j _ hj'
  · obtain ⟨cv, caps, hf, hnp, hl, hN⟩ := hnc c hc
    have hLc : ConLeche.nestContainer (envCtx envC) (d.memberName c) = some (nP', []) := hL
    rw [hN] at hLc
    have hnil : ctorsAs.getD c [] = [] := by
      by_cases hne : ctorsAs.getD c [] = []
      · exact hne
      · rw [hpick caps _ hne] at hLc
        simp only [Option.some.injEq, Prod.mk.injEq] at hLc
        exact absurd hLc.2 hne
    rw [hnil] at hLc
    obtain rfl : caps.nparams = nP' := by
      simp only [List.map_nil, nestPick, Option.some.injEq, Prod.mk.injEq] at hLc
      exact hLc.1
    refine ⟨cv, caps, hf, hl ▸ hlps, fun ψ => by rw [hnp]; exact hparams ψ, fun mm hmm => ?_⟩
    obtain ⟨cvm, capsm, hfm, -, hlm, -⟩ := hfindT mm hmm
    exact ⟨cvm, capsm, hfm, by rw [hlm, hl]⟩
  · obtain ⟨cv, caps, hf, -, hl, -⟩ := hfindT c hc
    exact ⟨cv, caps, hf, hl ▸ hlps⟩
  · have hj' : j < (d.ctorsM c).length := hj
    have hget : (d.ctorsM c)[j]? = some (d.ctorsM c)[j] := List.getElem?_eq_getElem hj'
    refine ⟨(d.ctorsM c)[j].1, d.nP, (d.ctorsM c)[j].2, ?_, ?_⟩
    · show envC.find? ((d.ctorsM c).getD j default).1.name = _
      rw [List.getD_eq_getElem?_getD, hget, Option.getD_some]
      exact hfindC c hc j _ hget
    · have hmem : (d.ctorsM c)[j] ∈ ctorsAs.getD c [] := by
        rw [← hctorsM]; exact List.getElem_mem hj'
      exact hshape c hc _ hmem

end ConLeche.Model
