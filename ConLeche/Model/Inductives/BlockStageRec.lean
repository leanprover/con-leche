module

public import ConLeche.Model.Inductives.BlockRep
public import ConLeche.Model.Swap
public import ConLeche.Model.Inductives.StructCaps
public import ConLeche.Verify.Inductives.BlockWF
public section

/-!
# The recursor stage's discharge, Model tier (task #315, milestone M5)

The stage conses the block's `k` recursors — each with its rules —
onto the CONSTRUCTORS' environment, and the P carrier has to survive
it.  At `k = 1` that is one `declStep_preserves_of_ind_rec_cons`; at
`k ≥ 2` it cannot be, for the reason `envWF_consBlockRecs`
(`Verify/Inductives/BlockWF.lean`) records: a rule of `rec_0` may name
`rec_1`, so it reads only where all `k` recursors stand, and no
intermediate environment is well-formed.

The route here is the one the group rule-list swap already paved:

1. **the `k` RULE-LESS conses** (`envModelM_consBlockRecsBare`): a
   rule-less `recInfo` owes nothing about rules, so each cons is an
   ordinary `declStep_preserves_of_ind_rec_cons` and the whole chain is
   an induction over the recursor list;
2. **the rules, attached in one step** (`EnvModelM.swapP`,
   `Model/Swap.lean`): `consBlockRecsBare` and `consBlockRecs` cons the
   same constants in the same order, differing only in the `rules`
   field, which is exactly `SwapShList`
   (`swapShList_consBlockRecs`).  The swap takes `EnvWF`,
   `RecCtorsStored`, `BasisPinnedTT`, `ProjOkT` and `RecRules` at the
   stored environment as hypotheses — the first is
   `envWF_consBlockRecs` and the last is the ι content this lane's
   consumer supplies.

`blockRecStaged_of` is the proposition `Model/Inductives/DeclBlock.lean`
consumes, stated literally.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  IndCaps RecRule BlockShape consBlockRecs consBlockRecsBare)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## The `k` recursors' names -/

/-- The recursor stage's stored tuple: the checked constant, its
rules' right-hand sides, its target member's index count and that
member's constructors. -/
abbrev RecDatum := ConstantVal × List Expr × Nat × List (ConstantVal × Nat)

/-- `consBlockRecsBare`'s argument list, off the stage's own. -/
@[expose] def bareOf (rs : List RecDatum) : List (ConstantVal × Nat) :=
  rs.map fun r => (r.1, r.2.2.1)

theorem bareOf_map_name (rs : List RecDatum) :
    (bareOf rs).map (·.1.name) = rs.map (·.1.name) := by
  simp [bareOf]

theorem mem_bareOf {rs : List RecDatum} {x : ConstantVal × Nat} (h : x ∈ bareOf rs) :
    ∃ r ∈ rs, x.1 = r.1 := by
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
  exact ⟨r, hr, rfl⟩

/-! ## `CapsOk` at a rule-less recursor cons

A block recursor is `isProjFnShape`-free (`checkConstantVal`'s own
rejection), so it can complete no η family's projection slot, and it
is not an `indInfo`, so it is no family's former either; the whole
capability row therefore crosses with nothing supplied.  It is
`capsOk_cons_native` at `T := c₀.name`, whose two branches are then
both refuted by the head's KIND. -/
theorem capsOk_cons_recFresh {env : Env} (mp : EnvModelM V μ env)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    {cvR : ConstantVal} {mI rP : Nat} {rules : List RecRule}
    (hfresh : env.find? c₀.name = none)
    (hkind : c₀ = .recInfo cvR mI rP rules)
    (hpshape : c₀.name.isProjFnShape = false)
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith mp.base2.acval c₀.name A) :
    CapsOk m₂ := by
  refine capsOk_cons_native (T := c₀.name) mp hfresh
    (ConsCrossEnv.ofNtc (fun tbl h => by rw [hkind] at h; exact nomatch h))
    hpshape (Or.inr (fun cv caps h => by rw [hkind] at h; exact nomatch h))
    ?_ m₂ hac ?_
  · -- no stored family's capability constructor is this recursor
    intro T' cvT' caps' hf hne hres hcape hfam hh
    obtain ⟨-, ⟨cvC, hfC⟩, -⟩ := hfam
    rw [hh, ConLeche.Env.find?_cons_self, hkind] at hfC
    exact nomatch hfC
  · -- the head is not an `indInfo`, so it is no family's former
    intro cvT caps hf _
    rw [ConLeche.Env.find?_cons_self, hkind] at hf
    exact nomatch hf

/-! ## The `k` rule-less conses -/

/-- **The `k` RULE-LESS recursors' cons, P tier.**  Each head is a
`recInfo` with NO rules, so the whole `EnvModelM` bill is the ordinary
one (`declStep_preserves_of_ind_rec_cons`) with `caps_ok` free
(`capsOk_cons_recFresh`) and `rec_rules` free (`recRules_cons_fresh`
at an empty rule list); the chain is then an induction over the
recursor list.

The target valuation `acv` is given up front rather than built by
iterated `acvalWith`: every hypothesis is then a statement about
`acv r.1.name`, and the induction never has to shift a positional
index.  `hagree` is what ties it to the prefix's valuation off the
`k` names. -/
theorem envModelM_consBlockRecsBare {q : BlockShape}
    {acv : Name → (Name → Nat) → AnnotTerm} :
    ∀ {m : Nat} {ls : List (ConstantVal × Nat)} {env : Env} (mp : EnvModelM V μ env),
      (ls.map (·.1.name)).Nodup →
      (∀ r ∈ ls, env.find? r.1.name = none) →
      (∀ r ∈ ls, ConLeche.reservedBasisNames.contains r.1.name = false) →
      (∀ r ∈ ls, r.1.name.isProjFnShape = false) →
      (∀ r ∈ ls,
        r.1.type.hasFvar = false ∧
        r.1.type.allLevelParamsDefined r.1.levelParams = true ∧
        r.1.type.constsResolve env = true ∧
        r.1.type.looseBVarsBounded 0 = true) →
      (∀ n : Name, (∀ r ∈ ls, n ≠ r.1.name) → acv n = mp.base2.acval n) →
      (∀ r ∈ ls, ∀ ψ : Name → Nat, Term.Closed ((acv r.1.name ψ).erase)) →
      (∀ r ∈ ls, ∀ (ψ : Name → Nat) (k : Nat),
        (acv r.1.name ψ).liftN 1 k = acv r.1.name ψ) →
      (∀ r ∈ ls, ∀ ψ₁ ψ₂ : Name → Nat,
        (∀ p ∈ r.1.levelParams, ψ₁ p = ψ₂ p) → acv r.1.name ψ₁ = acv r.1.name ψ₂) →
      (∀ r ∈ ls, ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenoted V ρ (acv r.1.name ψ)) →
      (∀ r ∈ ls, ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotValid V ρ (acv r.1.name ψ)) →
      (∀ r ∈ ls, ∀ ψ : Name → Nat, ∃ ta : AnnotTerm,
        denoteMeta mp.base2.acval env ψ 0 r.1.type = some ta ∧
        (∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧
        (∀ ρ : Nat → V, interp V ρ (acv r.1.name ψ) ∈ˢ interp V ρ ta)) →
      ∃ mp' : EnvModelM V μ (consBlockRecsBare q m ls env), mp'.base2.acval = acv
  | _, [], env, mp, _, _, _, _, _, hag, _, _, _, _, _, _ =>
    ⟨mp, by funext n; exact (hag n (fun _ h => nomatch h)).symm⟩
  | m, r0 :: rest, env, mp, hnd, hfr, hnres, hpsh, hty, hag, hcl, hlift, hpar, hok, hval, hrd => by
    -- the head
    have hmem0 : r0 ∈ r0 :: rest := List.mem_cons_self
    have hfresh : env.find? r0.1.name = none := hfr r0 hmem0
    rw [List.map_cons, List.nodup_cons] at hnd
    have hnrr : ∀ r ∈ rest, r.1.name ≠ r0.1.name := fun r hr hh =>
      hnd.1 (List.mem_map.mpr ⟨r, hr, hh⟩)
    obtain ⟨h1, h2, h3, h4⟩ := hty r0 hmem0
    have hcb : ConstsBound env r0.1.type := constsBound_of_constsResolve _ h3
    have hcross : ∀ e : Expr,
        ConsCrossAt (.recInfo r0.1 (q.majorIdxAt m) (q.rulePrefixAt m) []) e :=
      fun _ => ConsCrossAt.ofNtc (fun _ h => nomatch h)
    have hreadUp : ∀ ψ : Name → Nat, ∃ ta : AnnotTerm,
        denoteMeta (acvalWith mp.base2.acval r0.1.name (acv r0.1.name))
            ⟨.recInfo r0.1 (q.majorIdxAt m) (q.rulePrefixAt m) [] :: env.consts⟩ ψ 0
            r0.1.type = some ta ∧
          (∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧
          (∀ ρ : Nat → V, interp V ρ (acv r0.1.name ψ) ∈ˢ interp V ρ ta) := by
      intro ψ
      obtain ⟨ta, hta, hokta, hmemta⟩ := hrd r0 hmem0 ψ
      exact ⟨ta, denoteMeta_cons_mono hfresh (hcross _) ψ 0 hcb hta, hokta, hmemta⟩
    -- the cons
    obtain ⟨mp₁, hac₁⟩ :=
      declStep_preserves_of_ind_rec_cons (A := acv r0.1.name)
        (c₀ := .recInfo r0.1 (q.majorIdxAt m) (q.rulePrefixAt m) []) mp hfresh (hnres r0 hmem0)
        ⟨r0.1, q.majorIdxAt m, q.rulePrefixAt m, [], rfl⟩
        (ConsHead.ofFresh
          (ConLeche.EnvWF.cons mp.base2.wf
            (ConLeche.structConstWF h1 h2 (Expr.constsResolve_mono h3) h4
              (fun _ _ _ heq => nomatch heq)
              (fun _ _ _ rules heq r hr => by
                injection heq with _ _ _ e4
                subst e4
                exact nomatch hr)))
          (fun ψ => hcl r0 hmem0 ψ) (hnres r0 hmem0)
          (fun _ h => nomatch h)
          (fun _ _ _ rules heq r hr => by
            injection heq with _ _ _ e4
            subst e4
            exact nomatch hr))
        (fun ψ k => hlift r0 hmem0 ψ k) (fun ψ₁ ψ₂ h => hpar r0 hmem0 ψ₁ ψ₂ h)
        (fun ψ ρ => hok r0 hmem0 ψ ρ) (fun ψ ρ => hval r0 hmem0 ψ ρ)
        (fun ψ => (hreadUp ψ).imp fun _ h => h.1)
        (fun ψ ta hta ρ => by
          obtain ⟨ta', hta', hokta, -⟩ := hreadUp ψ
          obtain rfl := Option.some.inj (hta'.symm.trans hta)
          exact hokta ρ)
        (fun ψ ta hta ρ => by
          obtain ⟨ta', hta', -, hmemta⟩ := hreadUp ψ
          obtain rfl := Option.some.inj (hta'.symm.trans hta)
          exact hmemta ρ)
        (fun m₂ hac =>
          capsOk_cons_recFresh (c₀ := .recInfo r0.1 (q.majorIdxAt m) (q.rulePrefixAt m) [])
            mp hfresh rfl (hpsh r0 hmem0) m₂ hac)
        (fun m₂ hac φ =>
          recRules_cons_fresh (c₀ := .recInfo r0.1 (q.majorIdxAt m) (q.rulePrefixAt m) [])
            mp hfresh (ConsCrossEnv.ofNtc (fun _ h => nomatch h))
            (fun _ _ _ _ heq => by injection heq with _ _ _ e4; exact e4.symm) m₂ hac φ)
    -- the tail
    show ∃ mp' : EnvModelM V μ (consBlockRecsBare q (m + 1) rest
        ⟨.recInfo r0.1 (q.majorIdxAt m) (q.rulePrefixAt m) [] :: env.consts⟩),
      mp'.base2.acval = acv
    refine envModelM_consBlockRecsBare mp₁ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact hnd.2
    · intro r hr
      rw [ConLeche.Env.find?_cons, if_neg (fun hh => hnrr r hr hh.symm)]
      exact hfr r (List.mem_cons_of_mem _ hr)
    · exact fun r hr => hnres r (List.mem_cons_of_mem _ hr)
    · exact fun r hr => hpsh r (List.mem_cons_of_mem _ hr)
    · intro r hr
      obtain ⟨g1, g2, g3, g4⟩ := hty r (List.mem_cons_of_mem _ hr)
      exact ⟨g1, g2, Expr.constsResolve_mono g3, g4⟩
    · intro n hn
      rw [hac₁]
      show acv n = acvalWith mp.base2.acval r0.1.name (acv r0.1.name) n
      by_cases hh : n = r0.1.name
      · rw [hh]
        exact acvalWith_self.symm
      · rw [acvalWith_ne hh]
        exact hag n (fun r hr => by
          rcases List.mem_cons.mp hr with rfl | hr'
          · exact hh
          · exact hn r hr')
    · exact fun r hr => hcl r (List.mem_cons_of_mem _ hr)
    · exact fun r hr => hlift r (List.mem_cons_of_mem _ hr)
    · exact fun r hr => hpar r (List.mem_cons_of_mem _ hr)
    · exact fun r hr => hok r (List.mem_cons_of_mem _ hr)
    · exact fun r hr => hval r (List.mem_cons_of_mem _ hr)
    · intro r hr ψ
      obtain ⟨ta, hta, hokta, hmemta⟩ := hrd r (List.mem_cons_of_mem _ hr) ψ
      refine ⟨ta, ?_, hokta, hmemta⟩
      rw [hac₁]
      exact denoteMeta_cons_mono hfresh (hcross _) ψ 0
        (constsBound_of_constsResolve _ (hty r (List.mem_cons_of_mem _ hr)).2.2.1) hta

/-! ## The rules, attached in one step

`consBlockRecsBare` and `consBlockRecs` cons the SAME constants in the
SAME order — the first with empty rule lists, the second with
`sumRules`' — which is exactly `SwapPairSh` at every position. -/

/-- The two recursor conses are a shape-level rule-list swap. -/
theorem swapShList_consBlockRecs {find? : Name → Option ConstantInfo}
    {q : BlockShape} {nP : Nat} :
    ∀ {m : Nat} {rs : List RecDatum} {envA envB : Env},
      ConLeche.SwapShList envA.consts envB.consts →
      ConLeche.SwapShList (consBlockRecsBare q m (bareOf rs) envA).consts
        (consBlockRecs find? q nP m rs envB).consts
  | _, [], _, _, h => h
  | m, (cvRa, rhss, nIdx, ctorsA) :: rest, envA, envB, h => by
    simp only [bareOf, List.map_cons, consBlockRecsBare, consBlockRecs]
    exact swapShList_consBlockRecs (q := q) (nP := nP)
      (rs := rest) (envA := ⟨_ :: envA.consts⟩) (envB := ⟨_ :: envB.consts⟩)
      (ConLeche.SwapShList.cons
        (Or.inr ⟨cvRa, q.majorIdxAt m, q.rulePrefixAt m, _, rfl, rfl⟩) h)

/-- **The three non-`EnvWF` syntactic facts across a rule-list swap** —
`swapEnvFacts`'s other three arms, off the head facts a
`RecCtorsStored` needs and nothing else (the `EnvWF` arm is the one
that consumes the rules' own syntax, and at the block it is
`envWF_consBlockRecs`). -/
theorem recSwapFacts3 {envSelf env₃ : Env} {cval : TConstVal}
    (hctorsS : ConLeche.RecCtorsStored envSelf)
    (hbpS : BasisPinnedTT envSelf cval) (hprojS : ProjOkT envSelf)
    (hswR : ConLeche.SwapShList envSelf.consts env₃.consts)
    (hnresR : SwapNResS envSelf env₃)
    (hnew : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      env₃.find? n = some (.recInfo cv mI rP rules) →
      envSelf.find? n = some (.recInfo cv mI rP []) → cv.name = n →
      ∀ r ∈ rules,
        (∃ cvj cnP cnF,
          envSelf.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF)) ∧
        (r.k = true → ConLeche.recRuleKOf envSelf.find? r.ctor = true) ∧
        (r.eta = true → ConLeche.recRuleEtaOf envSelf.find? n r.ctor = true)) :
    ConLeche.RecCtorsStored env₃ ∧ BasisPinnedTT env₃ cval ∧ ProjOkT env₃ := by
  have hcg : ConLeche.SwapCongr envSelf env₃ := ConLeche.SwapShList.congr hswR
  have hcorr := ConLeche.swapSh_find?_corr hswR
  have hsame : ∀ (n : Name) (ci : ConstantInfo),
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      (env₃.find? n = some ci ↔ envSelf.find? n = some ci) :=
    fun n ci hnr =>
      ⟨fun h => hcg.findDown n ci h hnr, fun h => hcg.findUp n ci h hnr⟩
  have hkeep : ∀ (m : Name) (ci : ConstantInfo),
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      envSelf.find? m = some ci → env₃.find? m = some ci :=
    fun m ci hnr hfc => hcg.findUp m ci hfc hnr
  refine ⟨?_, ?_, ?_⟩
  · -- `RecCtorsStored`
    intro n cv mI rP rules hf r hr
    rcases hcorr n with heq | ⟨cv', mI', rP', rules', h₀, h₃, hn'⟩
    · have hfS : envSelf.find? n = some (.recInfo cv mI rP rules) := by
        rw [← heq]; exact hf
      obtain ⟨⟨cvj, cnP, cnF, hfc⟩, hk, he⟩ := hctorsS n cv mI rP rules hfS r hr
      exact ⟨⟨cvj, cnP, cnF, hkeep _ _
          (fun _ _ _ _ hcon => ConstantInfo.noConfusion hcon) hfc⟩,
        fun hb => ConLeche.recRuleKOf_mono hkeep (hk hb),
        fun hb => ConLeche.recRuleEtaOf_mono hkeep (he hb)⟩
    · obtain ⟨e1, e2, e3, -⟩ :=
        ConstantInfo.recInfo.inj (Option.some.inj (h₃.symm.trans hf))
      obtain ⟨⟨cvj, cnP, cnF, hfc⟩, hk, he⟩ :=
        hnew n cv mI rP rules hf (by rw [← e1, ← e2, ← e3]; exact h₀)
          (by rw [← e1]; exact hn') r hr
      exact ⟨⟨cvj, cnP, cnF, hkeep _ _
          (fun _ _ _ _ hcon => ConstantInfo.noConfusion hcon) hfc⟩,
        fun hb => ConLeche.recRuleKOf_mono hkeep (hk hb),
        fun hb => ConLeche.recRuleEtaOf_mono hkeep (he hb)⟩
  · -- `BasisPinnedTT`: a genuinely swapped entry is never reserved
    intro n ci hf hres
    have hf₀ : envSelf.find? n = some ci := by
      rcases hcorr n with heq | ⟨cv, mI, rP, rules, h₀, h₃, -⟩
      · rw [← heq]; exact hf
      · rcases hnresR n cv mI rP rules h₀ h₃ with rfl | hnr
        · rw [h₃] at hf
          obtain rfl := Option.some.inj hf
          exact h₀
        · rw [hnr] at hres
          exact nomatch hres
    exact hbpS n ci hf₀ hres
  · -- `ProjOkT`: projection tables are untouched
    intro n tbl hf i hi
    exact ConLeche.TowerHead.mono (fun n ci hnr hf' => (hsame n ci hnr).mpr hf')
      (hprojS n tbl ((hsame _ _
        (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf) i hi)

end ConLeche.Model
