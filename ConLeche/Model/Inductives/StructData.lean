module

import ConLeche.Model.Inductives.BlockData
public import ConLeche.Model.Inductives.StructLaws
import ConLeche.Model.Inductives.StructRows
import ConLeche.Verify.InstLevels
public import ConLeche.Verify.Inductives.FormerFront
import ConLeche.Semantics.Tower.TowerWire
public section

/-!
# The direct block's stage data (task #175 W4c, P3 module 6, part 1)

The readings the leaves are built over, packaged per stored constant:
`FormerData` (the type former's Π-peel, its bits, gradings, bounds,
the parameter binders' universes and level dependence) and — later in
the file — the constructor's.
Each is derived once from the stage's run (`formerData_of`) and
crossed to the later stage environments (`FormerData.cross`), where
the readings survive because the block's constants are stored and
the head's slot mentions none of them.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## Kit -/

theorem mkPisAV_inj :
    ∀ {pps₁ pps₂ : List (Nat × Nat × AnnotTerm)} {b₁ b₂ : AnnotTerm},
      pps₁.length = pps₂.length → mkPisAV pps₁ b₁ = mkPisAV pps₂ b₂ →
      pps₁ = pps₂ ∧ b₁ = b₂
  | [], [], _, _, _, h => ⟨rfl, h⟩
  | [], _ :: _, _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, _, hlen, _ => by simp at hlen
  | d₁ :: pps₁, d₂ :: pps₂, b₁, b₂, hlen, h => by
    simp only [mkPisAV, AnnotTerm.pi.injEq] at h
    obtain ⟨hu, hv, hA, hB⟩ := h
    obtain ⟨rfl, rfl⟩ := mkPisAV_inj (by simpa using hlen) hB
    refine ⟨?_, rfl⟩
    congr 1
    exact Prod.ext hu (Prod.ext hv hA)

/-- A `.pi` context is a successful peel, with the peel's domains
reversed. -/
theorem stripPisAV_of_piTeleAV :
    ∀ {k : Nat} {T : AnnotTerm} {Γ : List AnnotTerm} {R : AnnotTerm},
      PiTeleAV k T Γ R →
      ∃ pps : List (Nat × Nat × AnnotTerm),
        stripPisAV k T = some (pps, R) ∧ (pps.map (·.2.2)).reverse = Γ := by
  intro k T Γ R h
  induction h with
  | nil => exact ⟨[], rfl, rfl⟩
  | @cons k u v A B R Γ' _ ih =>
    obtain ⟨pps, hst, hΓ⟩ := ih
    refine ⟨(u, v, A) :: pps, ?_, ?_⟩
    · simp only [stripPisAV, hst, Option.map_some]
    · simp [hΓ]

theorem DomsBelow.drop {k : Nat} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} (j : Nat), DomsBelow k ds →
      DomsBelow (k + j) (ds.drop j)
  | _, 0, h => by simpa using h
  | [], _ + 1, _ => trivial
  | _ :: ds, j + 1, h => by
    rw [List.drop_succ_cons, show k + (j + 1) = k + 1 + j from by omega]
    exact DomsBelow.drop (k := k + 1) (ds := ds) j h.2

omit [SetTheory V] in
/-- Evaluating a list of levels commutes with indexing. -/
theorem getD_map_eval (f : Name → Nat) (us : List Level) {i : Nat}
    (hi : i < us.length) :
    (us.map (Level.eval f)).getD i 0 = Level.eval f (us.getD i .zero) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_eq_getElem hi]
  rfl

/-! ## The domains' universes, walked -/

/-- **The telescope's domains land in their own universes**, binder by
binder: at a frame satisfying the earlier domains, the next domain's
reading is graded and lies in `univ (ws k)` whenever the binder's
inferred sort evaluates below `ws k` — the sort claim at the context
opened by the earlier binders. -/
theorem teleLevels_walk (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    (ψ : Name → Nat) :
    ∀ (n : Nat) (ws : Nat → Nat) {d : Nat} {e : Expr} {fvs : List Expr}
      {o : Expr} {Δ : List AnnotTerm} {tl : List (Nat × Nat × AnnotTerm)},
      ConLeche.openPisAtFvars n e d = some (fvs, o) → tl.length = n →
      CtxOk mp.base2 ψ d Δ e → Expr.WScoped d e →
      e.looseBVarsBounded 0 = true → Expr.LeavesBounded e →
      (∀ k a, fvs[k]? = some a →
        denoteMeta mp.base2.acval env ψ (d + k) a.fvarTypeD
          = some (tl.getD k default).2.2) →
      (∀ k a, fvs[k]? = some a → ∃ (F : Nat) (t : Expr) (u : Level),
        ConLeche.inferTypeCore μ env F (d + k) a.fvarTypeD = .ok t ∧
        ConLeche.ensureSortCore μ env F (d + k) t = .ok u ∧
        Level.eval ψ u ≤ ws k) →
      ∀ k, k < n → ∀ ρ : Nat → V,
        Sat V (((tl.take k).map (·.2.2)).reverse ++ Δ) ρ →
        WellDenotedV V ρ (tl.getD k default).2.2 ∧
          interp V ρ (tl.getD k default).2.2 ∈ˢ (univ (ws k) : V)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, k, hk, _, _ =>
    absurd hk (Nat.not_lt_zero k)
  | n + 1, ws, d, e, fvs, o, Δ, tl, hop, hlen, hC, hws, hb, hL, hread, hinf,
      k, hk, ρ, hρ => by
    match e, hop, hws, hb with
    | .forallE ty body mb, hop, hws, hb =>
      simp only [ConLeche.openPisAtFvars] at hop
      split at hop
      · next fvs' o' hop' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        cases tl with
        | nil => exact absurd hlen (by simp)
        | cons t0 tl' =>
        have hlen' : tl'.length = n := by simpa using hlen
        have hws2 : Expr.WScoped d ty ∧ Expr.WScoped d body := by
          simp only [Expr.WScoped] at hws; exact hws
        -- the first domain's frame conditions
        have hbty : ty.looseBVarsBounded 0 = true := by
          simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb; exact hb.1
        have hbb : body.looseBVarsBounded 1 = true := by
          simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb; exact hb.2
        have hLty : Expr.LeavesBounded ty := fun l hl =>
          hL l (by rw [Expr.fvarLeaves]; exact List.mem_append_left _ hl)
        have hLbody : Expr.LeavesBounded body := fun l hl =>
          hL l (by rw [Expr.fvarLeaves]; exact List.mem_append_right _ hl)
        -- the first domain's row
        have hread0 : denoteMeta mp.base2.acval env ψ d ty = some t0.2.2 := by
          have := hread 0 _ rfl
          simpa [Expr.fvarTypeD] using this
        obtain ⟨F, t, u, hi, hens, hle⟩ := hinf 0 _ rfl
        simp only [Nat.add_zero, Expr.fvarTypeD] at hi hens
        have hCty := hC.forallE_ty
        have hrow := (claimsAt_of hμ mp ψ F).sortRow hi hens hws2.1 hbty hLty hCty
          hread0
        cases k with
        | zero =>
          simp only [List.take_zero, List.map_nil, List.reverse_nil,
            List.nil_append] at hρ
          exact ⟨(hrow ρ hρ).1, univ_mono hle _ (hrow ρ hρ).2⟩
        | succ k =>
          -- open the binder, walk on
          have hC' : CtxOk mp.base2 ψ (d + 1) (t0.2.2 :: Δ)
              (body.instantiate1 (.fvar d ty)) :=
            CtxOk.open hC.forallE_body hCty hread0 fun ρ hρ => (hrow ρ hρ).1
          obtain ⟨hws', hb', hL'⟩ := frame_open2 hws2.1 hbty hws2.2 hbb hLty hLbody
          have hread' : ∀ k a, fvs'[k]? = some a →
              denoteMeta mp.base2.acval env ψ (d + 1 + k) a.fvarTypeD
                = some (tl'.getD k default).2.2 := by
            intro k a hk
            have := hread (k + 1) a (by simpa using hk)
            rwa [show d + (k + 1) = d + 1 + k from by omega] at this
          have hinf' : ∀ k a, fvs'[k]? = some a → ∃ (F : Nat) (t : Expr) (u : Level),
              ConLeche.inferTypeCore μ env F (d + 1 + k) a.fvarTypeD = .ok t ∧
              ConLeche.ensureSortCore μ env F (d + 1 + k) t = .ok u ∧
              Level.eval ψ u ≤ ws (k + 1) := by
            intro k a hk
            obtain ⟨F, t, u, h1, h2, h3⟩ := hinf (k + 1) a (by simpa using hk)
            rw [show d + (k + 1) = d + 1 + k from by omega] at h1 h2
            exact ⟨F, t, u, h1, h2, h3⟩
          have hρ' : Sat V (((tl'.take k).map (·.2.2)).reverse ++ (t0.2.2 :: Δ)) ρ := by
            simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc]
              using hρ
          have := teleLevels_walk hμ mp ψ n (fun k => ws (k + 1)) hop' hlen' hC'
            hws' hb' hL' hread' hinf' k (by omega) ρ hρ'
          simpa using this
      · exact nomatch hop
    | .bvar _, hop, _, _ | .fvar _ _, hop, _, _ | .sort _, hop, _, _
    | .const _ _, hop, _, _ | .app _ _, hop, _, _ | .lam _ _ _, hop, _, _
    | .letE _ _ _, hop, _, _ | .lit _, hop, _, _ | .proj _ _ _, hop, _, _ =>
      simp [ConLeche.openPisAtFvars] at hop

/-! ## The former's data -/


/-- The former's data, from EITHER front door's facts (`FormerFront`,
task #279 K.10) and the checked telescope shape: the reading and its
grading come from INFERENCE at depth 0 (`acceptedReads_of`,
`ClaimsAt.inferRow`), never from the annotation pass. -/
theorem formerData_of_front (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {F : Nat} {cvT cvTa : ConstantVal} {nP : Nat} {resSort : Level}
    {bs : List (Expr × ConLeche.BinderMeta)}
    (hff : ConLeche.FormerFront μ F env cvT cvTa)
    (hstrip : cvTa.type.stripPis nP = some (bs, .sort resSort)) :
    ∃ (pps : (Name → Nat) → List (Nat × Nat × AnnotTerm))
      (lvls : (Name → Nat) → List Nat),
      FormerData mp.base2 cvTa nP resSort pps lvls := by
  obtain ⟨stype, u, hst, hens⟩ := hff.infer
  have htf' := hff.noFvar
  have hbt' := hff.bounded
  have htp' := hff.lpsOk
  have hw : Expr.WScoped 0 cvTa.type := Expr.WScoped.of_not_hasFvar htf'
  have hL : Expr.LeavesBounded cvTa.type := Expr.LeavesBounded.of_not_hasFvar htf'
  have hnil : cvTa.type.fvarLeaves = [] :=
    Expr.fvarLeaves_eq_nil_of_not_hasFvar htf'
  obtain ⟨fvs, hop⟩ := openPisAtFvars_of_stripPis_sort nP 0 hstrip
  have hlenF : fvs.length = nP := openPisAtFvars_length nP hop
  -- the bits: the opened body is `Sort resSort`, of sort `succ resSort`
  obtain ⟨F', tb, vb, hib, hensb, -, hbits⟩ :=
    piBits_of_infer hμ nP hop hst hens
  obtain rfl := inferTypeCore_sort_inv hib
  obtain rfl := ensureSortCore_sort_eq hensb
  -- the parameter binders' own sorts, one per binder
  obtain ⟨us, hlenUs, hus⟩ := piLevels_of_infer nP hop hst hens
  -- per assignment: the reading, its peel, its grading, its universes
  have hper : ∀ ψ : Name → Nat, ∃ pps : List (Nat × Nat × AnnotTerm),
      denoteMeta mp.base2.acval env ψ 0 cvTa.type
        = some (mkPisAV pps (.sort (resSort.eval ψ))) ∧
      pps.length = nP ∧
      (∀ d ∈ pps, d.2.1 ≠ 0) ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ (mkPisAV pps (.sort (resSort.eval ψ)))) ∧
      DomsBelow 0 pps ∧
      (∀ i, i < nP → ∀ ρ : Nat → V,
        Sat V (((pps.take i).map (·.2.2)).reverse) ρ →
        interp V ρ ((pps.getD i default).2.2)
          ∈ˢ (univ (Level.eval ψ (us.getD i .zero)) : V)) := by
    intro ψ
    have hc := claimsAt_of hμ mp ψ F
    obtain ⟨Ta, hTa⟩ := acceptedReads_of mp.base2 ψ hst hw hbt' hL
    obtain ⟨-, -, hokT, -, -⟩ := hc.inferRow hst hw hbt' hL (CtxOk.nil hnil) hTa
    have hokT' : ∀ ρ : Nat → V, WellDenotedV V ρ Ta := fun ρ =>
      hokT ρ (Sat_nil V ρ)
    obtain ⟨Γ, R, htele, hop'⟩ := opened_of hop htf' hbt' hTa hokT'
    have hR : R = .sort (resSort.eval ψ) := by
      have := hop'.body
      rw [denoteMeta_sort] at this
      exact (Option.some.inj this).symm
    subst hR
    obtain ⟨pps, hst', hΓ⟩ := stripPisAV_of_piTeleAV htele
    obtain ⟨hTeq, hlen⟩ := stripPisAV_eq_mkPis hst'
    subst hTeq
    refine ⟨pps, hTa, hlen, ?_, hokT', ?_, ?_⟩
    · intro d hd
      have := stripPisAV_bits nP (hbits ψ) hTa hst' d hd
      simp only [Level.eval, Nat.succ_ne_zero, iff_false] at this
      exact this
    · exact (stripPisAV_below hst' (bvarsBelow_of_reading hw hbt' hTa)).1
    · -- the domains' universes: the sort rows along the opening
      have hread : ∀ k a, fvs[k]? = some a →
          denoteMeta mp.base2.acval env ψ (0 + k) a.fvarTypeD
            = some (pps.getD k default).2.2 := by
        intro k a hk
        have hkn : k < nP := by
          have := (List.getElem?_eq_some_iff.mp hk).1
          omega
        have hp : pps[k]? = some (pps.getD k default) := by
          rw [List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem (l := pps) (i := k) (by omega)]
          rfl
        have := hop'.doms k a hk
        rw [← hΓ, getD_reverse_of_peel hlen hkn hp] at this
        simpa using this
      have hinf : ∀ k a, fvs[k]? = some a → ∃ (F : Nat) (t : Expr) (u : Level),
          ConLeche.inferTypeCore μ env F (0 + k) a.fvarTypeD = .ok t ∧
          ConLeche.ensureSortCore μ env F (0 + k) t = .ok u ∧
          Level.eval ψ u ≤ Level.eval ψ (us.getD k .zero) := by
        intro k a hk
        obtain ⟨F'', t', h1, h2, -⟩ := hus k a hk
        exact ⟨F'', t', us.getD k .zero, h1, h2, Nat.le_refl _⟩
      intro i hi ρ hρ
      exact (teleLevels_walk hμ mp ψ nP (fun k => Level.eval ψ (us.getD k .zero))
        hop hlen (CtxOk.nil hnil) hw hbt' hL hread hinf i hi ρ
        (by simpa using hρ)).2
  -- The binders' sorts above are the checker's own levels, and
  -- nothing here says they mention only the block's parameters — so
  -- the universes are recorded at the assignment RESTRICTED to those.
  -- The readings do not tell the two assignments apart (`params`), so
  -- the membership at ψ is the membership at its restriction.
  have hrestr : ∀ ψ : Name → Nat, ∀ p ∈ cvTa.levelParams,
      ψ p = (fun q => if q ∈ cvTa.levelParams then ψ q else 0) p := by
    intro ψ p hp; simp only [hp, if_pos]
  have hparams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ p ∈ cvTa.levelParams, ψ₁ p = ψ₂ p) →
      Classical.choose (hper ψ₁) = Classical.choose (hper ψ₂) ∧
        resSort.eval ψ₁ = resSort.eval ψ₂ := by
    intro ψ₁ ψ₂ hφ
    have h2 := (Classical.choose_spec (hper ψ₂)).1
    have h1 : denoteMeta mp.base2.acval env ψ₂ 0 cvTa.type
        = some (mkPisAV (Classical.choose (hper ψ₁))
          (.sort (resSort.eval ψ₁))) := by
      rw [← denoteMeta_params_ext mp.base2 hφ 0 cvTa.type htp']
      exact (Classical.choose_spec (hper ψ₁)).1
    obtain ⟨hp, hb⟩ := mkPisAV_inj
      (by rw [(Classical.choose_spec (hper ψ₁)).2.1,
        (Classical.choose_spec (hper ψ₂)).2.1])
      (Option.some.inj (h1.symm.trans h2))
    exact ⟨hp, AnnotTerm.sort.inj hb⟩
  refine ⟨fun ψ => Classical.choose (hper ψ),
    fun ψ => us.map (Level.eval (fun q => if q ∈ cvTa.levelParams then ψ q else 0)),
    ?_, ?_, ?_, ?_, ?_, hparams, ?_, ?_, ?_⟩
  · exact fun ψ => (Classical.choose_spec (hper ψ)).1
  · exact fun ψ => (Classical.choose_spec (hper ψ)).2.1
  · exact fun ψ => (Classical.choose_spec (hper ψ)).2.2.1
  · exact fun ψ => (Classical.choose_spec (hper ψ)).2.2.2.1
  · exact fun ψ => (Classical.choose_spec (hper ψ)).2.2.2.2.1
  · exact fun ψ => by rw [List.length_map]; exact hlenUs
  · intro ψ i hi ρ hρ
    have he := (hparams ψ _ (hrestr ψ)).1
    rw [getD_map_eval _ us (by omega), he]
    exact (Classical.choose_spec
      (hper (fun q => if q ∈ cvTa.levelParams then ψ q else 0))).2.2.2.2.2 i hi ρ
      (by rw [← he]; exact hρ)
  · intro ψ₁ ψ₂ hφ
    have hfun : (fun q => if q ∈ cvTa.levelParams then ψ₁ q else 0)
        = (fun q => if q ∈ cvTa.levelParams then ψ₂ q else 0) := by
      funext q
      by_cases h : q ∈ cvTa.levelParams
      · simp only [h, if_pos, hφ q h]
      · simp only [h, if_false]
    rw [hfun]

/-- The former's data, from its `checkConstantVal` run at the
pre-block environment and the annotated telescope shape. -/
theorem formerData_of (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {F : Nat} {cvT cvTa : ConstantVal} {nP : Nat} {resSort : Level}
    {bs : List (Expr × ConLeche.BinderMeta)}
    (hccv : ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env cvT = .ok cvTa)
    (hstrip : cvTa.type.stripPis nP = some (bs, .sort resSort)) :
    ∃ (pps : (Name → Nat) → List (Nat × Nat × AnnotTerm))
      (lvls : (Name → Nat) → List Nat),
      FormerData mp.base2 cvTa nP resSort pps lvls :=
  formerData_of_front hμ mp (ConLeche.FormerFront.of_checkConstantVal hccv) hstrip

/-- The former's data crosses a cons whose slot does not mention the
stored type (any block cons after the former's). -/
theorem FormerData.cross {m : EnvModel V env} {cvT : ConstantVal}
    {nP : Nat} {resSort : Level}
    {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {lvls : (Name → Nat) → List Nat}
    (h : FormerData m cvT nP resSort pps lvls)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? c₀.name = none) (hat : ConsCrossAt c₀ cvT.type)
    (hcb : ConstsBound env cvT.type)
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval c₀.name A) :
    FormerData m₂ cvT nP resSort pps lvls where
  read ψ := by
    rw [hac]
    exact denoteMeta_cons_mono hfresh hat ψ 0 hcb (h.read ψ)
  len := h.len
  bits := h.bits
  okTy := h.okTy
  below := h.below
  params := h.params
  lvlsLen := h.lvlsLen
  lvl := h.lvl
  lvlsParams := h.lvlsParams

end ConLeche.Model
