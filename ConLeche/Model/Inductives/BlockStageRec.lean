module

public import ConLeche.Model.Annot.EnvModelM
public import ConLeche.Model.Annot.BitConsCross
public import ConLeche.Semantics.IndBlockFacts
import ConLeche.Model.Swap
import ConLeche.Model.Inductives.StructFrameKit
public import ConLeche.Verify.Inductives.BlockWF
public section

/-!
# The recursor stage's discharge, Model tier (task #315)

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
   `envWF_consBlockRecs` and the last is the ι content the caller
   supplies.

`blockRecStaged_of` is the proposition `Model/Inductives/DeclBlock.lean`
consumes, stated literally.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  IndCaps RecRule BlockShape consBlockRecs consBlockRecsBare consBlockRecsR)

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
theorem swapShList_consBlockRecsR {R : Nat → RecDatum → List RecRule}
    {q : BlockShape} :
    ∀ {m : Nat} {rs : List RecDatum} {envA envB : Env},
      ConLeche.SwapShList envA.consts envB.consts →
      ConLeche.SwapShList (consBlockRecsBare q m (bareOf rs) envA).consts
        (consBlockRecsR R q m rs envB).consts
  | _, [], _, _, h => h
  | m, (cvRa, rhss, nIdx, ctorsA) :: rest, envA, envB, h => by
    simp only [bareOf, List.map_cons, consBlockRecsBare, consBlockRecsR]
    exact swapShList_consBlockRecsR (R := R) (q := q)
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

/-! ## The names the conses do not touch -/

/-- A name that is none of the `k` recursors' is found as it was. -/
theorem find?_consBlockRecsBare_of_ne {q : BlockShape} {n : Name} :
    ∀ {m : Nat} {ls : List (ConstantVal × Nat)} {env : Env},
      (∀ r ∈ ls, n ≠ r.1.name) →
      (consBlockRecsBare q m ls env).find? n = env.find? n
  | _, [], _, _ => rfl
  | m, r0 :: rest, env, hne => by
    rw [consBlockRecsBare,
      find?_consBlockRecsBare_of_ne (fun r hr => hne r (List.mem_cons_of_mem _ hr)),
      ConLeche.Env.find?_cons,
      if_neg (fun h => hne r0 List.mem_cons_self h.symm)]

/-! (A name that is none of the `k` recursors' is found as it was:
`find?_consBlockRecsR_of_ne`, `Verify/Inductives/BlockWF.lean`, where
the literal guards' crossing needs it too.) -/

/-! ## The stage's cons, whole -/

/-- **The `k` recursors' cons with their rules, P tier.**  The two
phases composed: the rule-less chain, then the rule-list swap.  The
`rec_rules` row (`hrecP`) is the ι content the caller supplies; every
other row is discharged here. -/
theorem envModelM_consBlockRecsR {R : Nat → RecDatum → List RecRule} {q : BlockShape} {rs : List RecDatum}
    {envC : Env} {acv : Name → (Name → Nat) → AnnotTerm} (mpC : EnvModelM V μ envC)
    (hnd : (rs.map (·.1.name)).Nodup)
    (hfr : ∀ r ∈ rs, envC.find? r.1.name = none)
    (hnres : ∀ r ∈ rs, ConLeche.reservedBasisNames.contains r.1.name = false)
    (hpsh : ∀ r ∈ rs, r.1.name.isProjFnShape = false)
    (hty : ∀ r ∈ rs,
      r.1.type.hasFvar = false ∧
      r.1.type.allLevelParamsDefined r.1.levelParams = true ∧
      r.1.type.constsResolve envC = true ∧
      r.1.type.looseBVarsBounded 0 = true)
    (hag : ∀ n : Name, (∀ r ∈ rs, n ≠ r.1.name) → acv n = mpC.base2.acval n)
    (hcl : ∀ r ∈ rs, ∀ ψ : Name → Nat, Term.Closed ((acv r.1.name ψ).erase))
    (hlift : ∀ r ∈ rs, ∀ (ψ : Name → Nat) (k : Nat),
      (acv r.1.name ψ).liftN 1 k = acv r.1.name ψ)
    (hpar : ∀ r ∈ rs, ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ r.1.levelParams, ψ₁ p = ψ₂ p) → acv r.1.name ψ₁ = acv r.1.name ψ₂)
    (hok : ∀ r ∈ rs, ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenoted V ρ (acv r.1.name ψ))
    (hval : ∀ r ∈ rs, ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotValid V ρ (acv r.1.name ψ))
    (hrd : ∀ r ∈ rs, ∀ ψ : Name → Nat, ∃ ta : AnnotTerm,
      denoteMeta mpC.base2.acval envC ψ 0 r.1.type = some ta ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧
      (∀ ρ : Nat → V, interp V ρ (acv r.1.name ψ) ∈ˢ interp V ρ ta))
    (hwf₃ : ConLeche.EnvWF (consBlockRecsR R q 0 rs envC))
    (hnew : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      (consBlockRecsR R q 0 rs envC).find? n
        = some (.recInfo cv mI rP rules) →
      (consBlockRecsBare q 0 (bareOf rs) envC).find? n = some (.recInfo cv mI rP []) →
      cv.name = n →
      ∀ r ∈ rules,
        (∃ cvj cnP cnF, (consBlockRecsBare q 0 (bareOf rs) envC).find? (RecRule.ctor r)
          = some (.ctorInfo cvj cnP cnF)) ∧
        (r.k = true →
          ConLeche.recRuleKOf (consBlockRecsBare q 0 (bareOf rs) envC).find? r.ctor = true) ∧
        (r.eta = true →
          ConLeche.recRuleEtaOf (consBlockRecsBare q 0 (bareOf rs) envC).find? n r.ctor = true))
    (hrecP : ∀ m₃ : EnvModel V (consBlockRecsR R q 0 rs envC),
      m₃.acval = acv → ∀ φ : Name → Nat, RecRules m₃ φ) :
    ∃ mp' : EnvModelM V μ (consBlockRecsR R q 0 rs envC),
      mp'.base2.acval = acv := by
  -- phase 1: the `k` rule-less conses
  have hmemB : ∀ x ∈ bareOf rs, ∃ r ∈ rs, x.1 = r.1 := fun x hx => mem_bareOf hx
  obtain ⟨mpB, hacB⟩ :=
    envModelM_consBlockRecsBare (q := q) (acv := acv) (m := 0) (ls := bareOf rs) mpC
      (by rw [bareOf_map_name]; exact hnd)
      (fun x hx => by obtain ⟨r, hr, he⟩ := hmemB x hx; rw [he]; exact hfr r hr)
      (fun x hx => by obtain ⟨r, hr, he⟩ := hmemB x hx; rw [he]; exact hnres r hr)
      (fun x hx => by obtain ⟨r, hr, he⟩ := hmemB x hx; rw [he]; exact hpsh r hr)
      (fun x hx => by obtain ⟨r, hr, he⟩ := hmemB x hx; rw [he]; exact hty r hr)
      (fun n hn => hag n (fun r hr => hn (r.1, r.2.2.1) (List.mem_map_of_mem hr)))
      (fun x hx => by obtain ⟨r, hr, he⟩ := hmemB x hx; rw [he]; exact hcl r hr)
      (fun x hx => by obtain ⟨r, hr, he⟩ := hmemB x hx; rw [he]; exact hlift r hr)
      (fun x hx => by obtain ⟨r, hr, he⟩ := hmemB x hx; rw [he]; exact hpar r hr)
      (fun x hx => by obtain ⟨r, hr, he⟩ := hmemB x hx; rw [he]; exact hok r hr)
      (fun x hx => by obtain ⟨r, hr, he⟩ := hmemB x hx; rw [he]; exact hval r hr)
      (fun x hx => by obtain ⟨r, hr, he⟩ := hmemB x hx; rw [he]; exact hrd r hr)
  -- phase 2: the rules, attached by the swap
  have hswR : ConLeche.SwapShList (consBlockRecsBare q 0 (bareOf rs) envC).consts
      (consBlockRecsR R q 0 rs envC).consts :=
    swapShList_consBlockRecsR (ConLeche.SwapShList.of_eq envC.consts)
  have hnresS : SwapNResS (consBlockRecsBare q 0 (bareOf rs) envC)
      (consBlockRecsR R q 0 rs envC) := by
    intro n cv mI rP rules h₀ h₃
    by_cases hres : ConLeche.reservedBasisNames.contains n = true
    · refine Or.inl ?_
      have hne : ∀ r ∈ rs, n ≠ r.1.name := by
        intro r hr h
        rw [h, hnres r hr] at hres
        exact nomatch hres
      rw [find?_consBlockRecsR_of_ne hne] at h₃
      rw [find?_consBlockRecsBare_of_ne
        (fun x hx => by obtain ⟨r, hr, he⟩ := hmemB x hx; rw [he]; exact hne r hr)] at h₀
      rw [h₀] at h₃
      obtain ⟨-, -, -, e4⟩ := ConstantInfo.recInfo.inj (Option.some.inj h₃)
      exact e4.symm
    · exact Or.inr (Bool.not_eq_true _ ▸ hres)
  obtain ⟨hctors₃, hbp₃, hproj₃⟩ :=
    recSwapFacts3 mpB.base2.rec_ctors mpB.base2.basis_pinned mpB.base2.proj_ok
      hswR hnresS hnew
  obtain ⟨mp₃, hac₃, -⟩ :=
    EnvModelM.swapP mpB hswR hwf₃ hctors₃ hbp₃ hproj₃
      (fun m₃ hac φ => hrecP m₃ (by rw [hac, hacB]) φ)
  exact ⟨mp₃, by rw [hac₃, hacB]⟩

/-! ## What the cons leaves alone

The four conjuncts `BlockRecStaged` carries beyond the carrier itself.
`findProj?` is EQUAL across the cons (a recursor's name is not
`isProjFnShape`, so it can be no structure's table), and so is the
`Nat`-literal guard (the three slots are reserved names, and a block
recursor's is not).  The `String` guard is the one that is only
MONOTONE, and it is the recursor stage's NAME check that makes it
congruent too (`ConLeche.strLitSupported_consBlockRecsR`). -/

/-- A name found in the constructors' environment is found unchanged
after the recursors. -/
theorem find?_consBlockRecsR_keep {R : Nat → RecDatum → List RecRule} {q : BlockShape} {rs : List RecDatum}
    {envC : Env} (hfr : ∀ r ∈ rs, envC.find? r.1.name = none) :
    ∀ (n : Name) (c : ConstantInfo), envC.find? n = some c →
      (consBlockRecsR R q 0 rs envC).find? n = some c := by
  intro n c hf
  rw [find?_consBlockRecsR_of_ne (fun r hr hh => by rw [hh, hfr r hr] at hf; exact nomatch hf)]
  exact hf

/-- The recursors' cons stores no projection table. -/
theorem findProj?_consBlockRecsR {R : Nat → RecDatum → List RecRule} {q : BlockShape} {rs : List RecDatum}
    {envC : Env} (hpsh : ∀ r ∈ rs, r.1.name.isProjFnShape = false) (sn : Name) (i : Nat) :
    (consBlockRecsR R q 0 rs envC).findProj? sn i = envC.findProj? sn i := by
  unfold ConLeche.Env.findProj?
  rw [find?_consBlockRecsR_of_ne (fun r hr hh => by
    have hsh : (ConLeche.projTableName sn).isProjFnShape = true := rfl
    rw [hh, hpsh r hr] at hsh
    exact nomatch hsh)]

/-- The RULE-LESS cons stores no projection table either — the bare
environment is where the stage annotates a rule's right-hand side, so
its empty slots are `envC`'s. -/
theorem findProj?_consBlockRecsBare {q : BlockShape} :
    ∀ {m : Nat} {ls : List (ConstantVal × Nat)} {env : Env},
      (∀ r ∈ ls, r.1.name.isProjFnShape = false) → ∀ (sn : Name) (i : Nat),
      (consBlockRecsBare q m ls env).findProj? sn i = env.findProj? sn i := by
  intro m ls env hpsh sn i
  unfold ConLeche.Env.findProj?
  rw [find?_consBlockRecsBare_of_ne (fun r hr hh => by
    have hsh : (ConLeche.projTableName sn).isProjFnShape = true := rfl
    rw [hh, hpsh r hr] at hsh
    exact nomatch hsh)]

/-- **`NoProjEnv` across the recursors' cons.**  A `.proj T i` node can
enter only through a recursor's stored TYPE or one of its rules'
right-hand sides; both are premises, and both come from
`annotateCore_noProjAt` at the environment the stage annotates in
(`Verify/ProjSlots.lean` — the slot `(T, i)` is empty there because the
members' projection tables are consed AFTER the recursors). -/
theorem noProjEnv_consBlockRecsR {R : Nat → RecDatum → List RecRule}
    {q : BlockShape} {T : Name} {i : Nat} :
    ∀ {m : Nat} {rs : List RecDatum} {env : Env},
      NoProjEnv env T i →
      (∀ r ∈ rs, Expr.NoProjAt T i r.1.type) →
      (∀ (j : Nat) (r : RecDatum), rs[j]? = some r → ∀ rl ∈ R (m + j) r,
        Expr.NoProjAt T i (RecRule.rhs rl) ∧
        ∀ lvls pins, RecRule.fire rl = .nested lvls pins → ∀ pin ∈ pins, Expr.NoProjAt T i pin) →
      NoProjEnv (consBlockRecsR R q m rs env) T i
  | _, [], _, h, _, _ => h
  | m, r0 :: rest, env, h, hT, hR => by
    have hhead : NoProjHead (.recInfo r0.1 (q.majorIdxAt m) (q.rulePrefixAt m) (R m r0)) T i := by
      refine ⟨hT _ List.mem_cons_self, (fun _ _ _ hcon => nomatch hcon), ?_,
        (fun _ hcon => nomatch hcon)⟩
      intro cv mI rP rules heq rl hrl
      injection heq with _ _ _ e4
      subst e4
      exact hR 0 r0 rfl rl hrl
    show NoProjEnv (consBlockRecsR R q (m + 1) rest ⟨_ :: env.consts⟩) T i
    exact noProjEnv_consBlockRecsR (h.cons hhead)
      (fun r hr => hT r (List.mem_cons_of_mem _ hr))
      (fun j r hr rl hrl => hR (j + 1) r (by simpa using hr) rl
        (by rw [show m + (j + 1) = m + 1 + j by omega]; exact hrl))

/-! ## The stage's stored rules, inverted

`blockRecStaged_of`'s `hnew` — the `RecCtorsStored` head facts of the
stored rules — is not a run fact but a consequence of `sumRules`' own
construction, once the cons is inverted.  That inversion is the only
place this file looks INSIDE `consBlockRecs`. -/

/-- **The recursors' cons, inverted**: a constant found above the `k`
recursors is one of them, with its rules `sumRules`', or was stored
below. -/
theorem find?_consBlockRecsR_inv {R : Nat → RecDatum → List RecRule}
    {q : BlockShape} :
    ∀ {m : Nat} {rs : List RecDatum} {env : Env} {n : Name} {ci : ConstantInfo},
      (consBlockRecsR R q m rs env).find? n = some ci →
      env.find? n = some ci ∨
      ∃ (j : Nat) (r : RecDatum), rs[j]? = some r ∧ n = r.1.name ∧
        ci = .recInfo r.1 (q.majorIdxAt (m + j)) (q.rulePrefixAt (m + j)) (R (m + j) r)
  | _, [], _, _, _, h => Or.inl h
  | m, r0 :: rest, env, n, ci, h => by
    rw [consBlockRecsR] at h
    rcases find?_consBlockRecsR_inv h with h' | ⟨j, r, hr, hn, hci⟩
    · rw [ConLeche.Env.find?_cons] at h'
      split at h'
      next heq =>
        refine Or.inr ⟨0, r0, rfl, heq.symm, ?_⟩
        rw [Nat.add_zero]
        exact (Option.some.inj h').symm
      next => exact Or.inl h'
    · refine Or.inr ⟨j + 1, r, hr, hn, ?_⟩
      rw [show m + (j + 1) = m + 1 + j from by omega]
      exact hci

/-- A name found in the constructors' environment is found unchanged
after the RULE-LESS recursors. -/
theorem find?_consBlockRecsBare_keep {q : BlockShape} {rs : List RecDatum} {envC : Env}
    (hfr : ∀ r ∈ rs, envC.find? r.1.name = none) :
    ∀ (n : Name) (c : ConstantInfo), envC.find? n = some c →
      (consBlockRecsBare q 0 (bareOf rs) envC).find? n = some c := by
  intro n c hf
  rw [find?_consBlockRecsBare_of_ne (fun x hx hh => by
    obtain ⟨r, hr, he⟩ := mem_bareOf hx
    rw [hh, he, hfr r hr] at hf
    exact nomatch hf)]
  exact hf

/-- **`hnew`, discharged.**  The stored rules' constructors are the
block's own — stored in the constructors' environment, hence in the
bare-`k` one — and their two rescue bits are `recRuleBits`' reading of
that same environment, which `recRuleKOf_mono`/`recRuleEtaOf_mono`
carry up. -/
theorem recCtorsHead_consBlockRecsR {R : Nat → RecDatum → List RecRule} {q : BlockShape} {rs : List RecDatum}
    {envC : Env} {nPc : Nat → Nat} {fireOf : Nat → RecDatum → ConLeche.RecRuleFire}
    (hshape : ConLeche.RecRulesShape envC.find? R rs nPc fireOf)
    (hfr : ∀ r ∈ rs, envC.find? r.1.name = none)
    (hctorsIn : ∀ r ∈ rs, ∀ cA ∈ r.2.2.2,
      ∃ cvj cnP cnF, envC.find? cA.1.name = some (.ctorInfo cvj cnP cnF)) :
    ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      (consBlockRecsR R q 0 rs envC).find? n
        = some (.recInfo cv mI rP rules) →
      (consBlockRecsBare q 0 (bareOf rs) envC).find? n = some (.recInfo cv mI rP []) →
      cv.name = n →
      ∀ r ∈ rules,
        (∃ cvj cnP cnF, (consBlockRecsBare q 0 (bareOf rs) envC).find? (RecRule.ctor r)
          = some (.ctorInfo cvj cnP cnF)) ∧
        (r.k = true →
          ConLeche.recRuleKOf (consBlockRecsBare q 0 (bareOf rs) envC).find? r.ctor = true) ∧
        (r.eta = true →
          ConLeche.recRuleEtaOf (consBlockRecsBare q 0 (bareOf rs) envC).find? n r.ctor
            = true) := by
  have hkeepB := find?_consBlockRecsBare_keep (q := q) hfr
  have hkeepB' : ∀ (n : Name) (ci : ConstantInfo),
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      envC.find? n = some ci → (consBlockRecsBare q 0 (bareOf rs) envC).find? n = some ci :=
    fun n ci _ hf => hkeepB n ci hf
  intro n cv mI rP rules hf hfB hname rl hrl
  rcases find?_consBlockRecsR_inv hf with hbelow | ⟨j, r0, hr0, rfl, hci⟩
  · -- stored below the recursors: the bare environment finds the same
    -- record, so the rule list is empty and there is nothing to prove
    exfalso
    rw [hkeepB n _ hbelow] at hfB
    obtain ⟨-, -, -, e4⟩ := ConstantInfo.recInfo.inj (Option.some.inj hfB)
    rw [e4] at hrl
    exact nomatch hrl
  · obtain ⟨-, -, -, rfl⟩ := ConstantInfo.recInfo.inj hci
    rw [Nat.zero_add] at hrl
    obtain ⟨i, cA, rhs, hi, -, rfl⟩ := hshape j r0 hr0 rl hrl
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨cvj, cnP, cnF, hfc⟩ := hctorsIn r0 (List.mem_of_getElem? hr0) cA (List.mem_of_getElem? hi)
      exact ⟨cvj, cnP, cnF, hkeepB _ _ hfc⟩
    · intro hb
      exact ConLeche.recRuleKOf_mono hkeepB' hb
    · intro hb
      exact ConLeche.recRuleEtaOf_mono hkeepB' hb

/-! ## The stage's proposition -/

/-- **`BlockRecStaged`, discharged.**

The carrier at the recursors' environment, with the four facts the
tables' stage and the final assembly read off it: the valuation is the
constructors' own off the `k` new names; every stored lookup survives;
every reading of a constructor-environment subject survives; and a slot
no stored piece mentioned is still mentioned by none.

Two premises beyond the cons's own are worth naming.  `hresRec` is
the recursor stage's own NAME check
(`ConLeche.recStage_reserved`): without it the
`String`-literal guard is monotone but not congruent — nothing else
would forbid a recursor from being named `List.cons` at a block that
declares `List` — and conjunct 3's EQUATION (as opposed to its
monotone half, `denoteMeta_consBlockRecsR_mono`, which needs nothing)
is then refutable.  With it both guards are untouched
(`ConLeche.natLitSupported_consBlockRecsR` /
`strLitSupported_consBlockRecsR`).
`hnoTy`/`hnoRhs` are the `.proj`-freedom of the stage's two stored
pieces; they are `annotateCore_noProjAt` at the bare-`k` environment,
whose `findProj?` is `envC`'s (`findProj?_consBlockRecsR`). -/
theorem blockRecStaged_of {R : Nat → RecDatum → List RecRule} {q : BlockShape} {rs : List RecDatum}
    {envC : Env} {acv : Name → (Name → Nat) → AnnotTerm} (mpC : EnvModelM V μ envC)
    (hnd : (rs.map (·.1.name)).Nodup)
    (hfr : ∀ r ∈ rs, envC.find? r.1.name = none)
    (hnres : ∀ r ∈ rs, ConLeche.reservedBasisNames.contains r.1.name = false)
    (hpsh : ∀ r ∈ rs, r.1.name.isProjFnShape = false)
    (hty : ∀ r ∈ rs,
      r.1.type.hasFvar = false ∧
      r.1.type.allLevelParamsDefined r.1.levelParams = true ∧
      r.1.type.constsResolve envC = true ∧
      r.1.type.looseBVarsBounded 0 = true)
    (hag : ∀ n : Name, (∀ r ∈ rs, n ≠ r.1.name) → acv n = mpC.base2.acval n)
    (hcl : ∀ r ∈ rs, ∀ ψ : Name → Nat, Term.Closed ((acv r.1.name ψ).erase))
    (hlift : ∀ r ∈ rs, ∀ (ψ : Name → Nat) (k : Nat),
      (acv r.1.name ψ).liftN 1 k = acv r.1.name ψ)
    (hpar : ∀ r ∈ rs, ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ r.1.levelParams, ψ₁ p = ψ₂ p) → acv r.1.name ψ₁ = acv r.1.name ψ₂)
    (hok : ∀ r ∈ rs, ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenoted V ρ (acv r.1.name ψ))
    (hval : ∀ r ∈ rs, ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotValid V ρ (acv r.1.name ψ))
    (hrd : ∀ r ∈ rs, ∀ ψ : Name → Nat, ∃ ta : AnnotTerm,
      denoteMeta mpC.base2.acval envC ψ 0 r.1.type = some ta ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧
      (∀ ρ : Nat → V, interp V ρ (acv r.1.name ψ) ∈ˢ interp V ρ ta))
    (hrhs : ∀ r ∈ rs, ∀ rhs ∈ r.2.1,
      rhs.hasFvar = false ∧
      rhs.allLevelParamsDefined r.1.levelParams = true ∧
      rhs.constsResolve (consBlockRecsBare q 0 (bareOf rs) envC) = true ∧
      rhs.looseBVarsBounded 0 = true)
    (hctorsIn : ∀ r ∈ rs, ∀ cA ∈ r.2.2.2,
      ∃ cvj cnP cnF, envC.find? cA.1.name = some (.ctorInfo cvj cnP cnF))
    {nPc : Nat → Nat} {fireOf : Nat → RecDatum → ConLeche.RecRuleFire}
    (hshape : ConLeche.RecRulesShape envC.find? R rs nPc fireOf)
    -- a `.nested` firing's pins: `EnvWF`'s clause, and no projection at an
    -- empty slot (vacuous at member majors, whose rules never fire `.nested`)
    (hnest : ∀ (j : Nat) (r : RecDatum), rs[j]? = some r → ∀ lvls pins,
      fireOf j r = .nested lvls pins →
        q.rulePrefixAt j ≤ q.majorIdxAt j ∧
        (∀ l ∈ lvls, l.allParamsDefined r.1.levelParams = true) ∧
        (∀ pin ∈ pins, pin.hasFvar = false ∧
          pin.allLevelParamsDefined r.1.levelParams = true ∧
          pin.constsResolve envC = true ∧
          pin.looseBVarsBounded (q.rulePrefixAt j) = true ∧
          ∀ (T : Name) (i : Nat), envC.findProj? T i = none → Expr.NoProjAt T i pin) ∧
        ∃ pre dom body bm D,
          r.1.type.stripPis (q.majorIdxAt j) = some (pre, .forallE dom body bm) ∧
          dom.getAppFn = .const D lvls ∧
          dom.getAppArgs =
            pins.map (Expr.liftLooseBVars (q.majorIdxAt j - q.rulePrefixAt j) 0) ++
              (List.range (q.majorIdxAt j - q.rulePrefixAt j)).map
                (fun i => Expr.bvar (q.majorIdxAt j - q.rulePrefixAt j - 1 - i)))
    (hrecP : ∀ m₃ : EnvModel V (consBlockRecsR R q 0 rs envC),
      m₃.acval = acv → ∀ φ : Name → Nat, RecRules m₃ φ)
    (hresRec : ∀ r ∈ rs, ConLeche.reservedRecName r.1.name = false)
    (hnoTy : ∀ r ∈ rs, ∀ (T : Name) (i : Nat), envC.findProj? T i = none →
      Expr.NoProjAt T i r.1.type)
    (hnoRhs : ∀ r ∈ rs, ∀ rhs ∈ r.2.1, ∀ (T : Name) (i : Nat),
      envC.findProj? T i = none → Expr.NoProjAt T i rhs) :
    ∃ mp' : EnvModelM V μ (consBlockRecsR R q 0 rs envC),
      (∀ n : Name, (envC.find? n).isSome = true →
        mp'.base2.acval n = mpC.base2.acval n) ∧
      (∀ (n : Name) (c : ConstantInfo), envC.find? n = some c →
        (consBlockRecsR R q 0 rs envC).find? n = some c) ∧
      (∀ (ψ : Name → Nat) (d : Nat) (e : Expr), ConstsBound envC e →
        denoteMeta mp'.base2.acval (consBlockRecsR R q 0 rs envC) ψ d e
          = denoteMeta mpC.base2.acval envC ψ d e) ∧
      (∀ (T : Name) (i : Nat), envC.findProj? T i = none →
        NoProjEnv envC T i →
        NoProjEnv (consBlockRecsR R q 0 rs envC) T i) := by
  have hkeep := find?_consBlockRecsR_keep (R := R) (q := q) hfr
  have hne : ∀ n : Name, (envC.find? n).isSome = true → ∀ r ∈ rs, n ≠ r.1.name := by
    intro n hn r hr hh
    rw [hh, hfr r hr] at hn
    exact nomatch hn
  obtain ⟨mp', hac'⟩ :=
    envModelM_consBlockRecsR mpC hnd hfr hnres hpsh hty hag hcl hlift hpar hok hval hrd
      (ConLeche.envWF_consBlockRecsR mpC.base2.wf
        (fun r hr => ⟨(hty r hr).1, (hty r hr).2.1, (hty r hr).2.2.1, (hty r hr).2.2.2,
          fun rhs hrhs' => hrhs r hr rhs hrhs'⟩)
        (fun j r hr rl hrl => by
          obtain ⟨i, cA, rhs, -, hrhs', rfl⟩ := hshape j r hr rl hrl
          refine ⟨List.mem_of_getElem? hrhs', fun lvls pins hf => ?_⟩
          obtain ⟨n1, n2, n3, n4⟩ := hnest j r hr lvls pins hf
          exact ⟨n1, n2, fun pin hpin =>
            ⟨(n3 pin hpin).1, (n3 pin hpin).2.1, (n3 pin hpin).2.2.1,
              (n3 pin hpin).2.2.2.1⟩, n4⟩))
      (recCtorsHead_consBlockRecsR (R := R) hshape hfr hctorsIn) hrecP
  refine ⟨mp', fun n hn => by rw [hac']; exact hag n (hne n hn), hkeep, ?_, ?_⟩
  · -- the readings of the constructors' environment survive, verbatim
    intro ψ d e hcb
    rw [hac',
      ← denoteMeta_envExtend (acval := acv) (φ := ψ) (fun {n} {ci} h => hkeep n ci h)
        ⟨(ConLeche.natLitSupported_consBlockRecsR hresRec).symm,
          (ConLeche.strLitSupported_consBlockRecsR hresRec).symm⟩
        (fun sn i h => by rw [findProj?_consBlockRecsR hpsh]; exact h) d e hcb]
    exact denoteMeta_acval_congr
      (fun n hn => hag n (hne n hn)) d e
  · -- the untouched slots
    intro T i hslot hnp
    refine noProjEnv_consBlockRecsR hnp (fun r hr => hnoTy r hr T i hslot) ?_
    intro j r hr rl hrl
    rw [Nat.zero_add] at hrl
    obtain ⟨i', cA, rhs, -, hrhs', rfl⟩ := hshape j r hr rl hrl
    refine ⟨hnoRhs r (List.mem_of_getElem? hr) rhs (List.mem_of_getElem? hrhs') T i hslot,
      fun lvls pins hf pin hpin => ?_⟩
    obtain ⟨-, -, n3, -⟩ := hnest j r hr lvls pins hf
    exact (n3 pin hpin).2.2.2.2 T i hslot

/-! ## The `String` guard, monotonically

`strLitSupported` is not congruent under the cons — nothing forbids a
recursor NAME from being one of the seven string-support names — but it
is MONOTONE, because every guard is false at an absent slot and a
present one is carried over verbatim.  That is enough for conjunct 3's
monotone half. -/

/-- A slot guard that fails at an absent name survives a lookup-preserving
extension. -/
theorem guardOk_mono {envA envB : Env} {n : Name} {f : Option ConstantInfo → Bool}
    (hnone : f none = false)
    (hkeep : ∀ (n : Name) (c : ConstantInfo), envA.find? n = some c → envB.find? n = some c)
    (h : f (envA.find? n) = true) : f (envB.find? n) = true := by
  cases hf : envA.find? n with
  | none => rw [hf, hnone] at h; exact nomatch h
  | some ci => rw [hkeep n ci hf]; rw [hf] at h; exact h

/-- The `Nat`-literal guard is monotone. -/
theorem natLitSupported_mono_of_keep {envA envB : Env}
    (hkeep : ∀ (n : Name) (c : ConstantInfo), envA.find? n = some c → envB.find? n = some c)
    (h : ConLeche.natLitSupported envA = true) : ConLeche.natLitSupported envB = true := by
  unfold ConLeche.natLitSupported at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  exact ⟨⟨guardOk_mono rfl hkeep h.1.1, guardOk_mono rfl hkeep h.1.2⟩,
    guardOk_mono rfl hkeep h.2⟩

/-- The `String`-literal guard is monotone. -/
theorem strLitSupported_mono_of_keep {envA envB : Env}
    (hkeep : ∀ (n : Name) (c : ConstantInfo), envA.find? n = some c → envB.find? n = some c)
    (h : ConLeche.strLitSupported envA = true) : ConLeche.strLitSupported envB = true := by
  unfold ConLeche.strLitSupported at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  exact ⟨⟨⟨⟨⟨⟨⟨natLitSupported_mono_of_keep hkeep h.1.1.1.1.1.1.1,
    guardOk_mono rfl hkeep h.1.1.1.1.1.1.2⟩,
    guardOk_mono rfl hkeep h.1.1.1.1.1.2⟩,
    guardOk_mono rfl hkeep h.1.1.1.1.2⟩,
    guardOk_mono rfl hkeep h.1.1.1.2⟩,
    guardOk_mono rfl hkeep h.1.1.2⟩,
    guardOk_mono rfl hkeep h.1.2⟩,
    guardOk_mono rfl hkeep h.2⟩

/-- **Conjunct 3's monotone half, unconditionally** — the form the tree
uses everywhere else (`denoteMeta_cons_fresh_mono`): a SUCCESSFUL
reading at the constructors' environment is reproduced verbatim at the
recursors'.  The equation `blockRecStaged_of` states needs the NAME
check (`hresRec`); this does not. -/
theorem denoteMeta_consBlockRecsR_mono {R : Nat → RecDatum → List RecRule} {q : BlockShape} {rs : List RecDatum}
    {envC : Env} {acv acvC : Name → (Name → Nat) → AnnotTerm}
    (hfr : ∀ r ∈ rs, envC.find? r.1.name = none)
    (hpsh : ∀ r ∈ rs, r.1.name.isProjFnShape = false)
    (hag : ∀ n : Name, (∀ r ∈ rs, n ≠ r.1.name) → acv n = acvC n)
    (ψ : Name → Nat) (d : Nat) (e : Expr) (hcb : ConstsBound envC e) {ea : AnnotTerm}
    (h : denoteMeta acvC envC ψ d e = some ea) :
    denoteMeta acv (consBlockRecsR R q 0 rs envC) ψ d e = some ea := by
  have hkeep := find?_consBlockRecsR_keep (R := R) (q := q) hfr
  have hne : ∀ n : Name, (envC.find? n).isSome = true → ∀ r ∈ rs, n ≠ r.1.name := by
    intro n hn r hr hh
    rw [hh, hfr r hr] at hn
    exact nomatch hn
  refine denoteMeta_envExtend_mono (acval := acv) (φ := ψ)
    (fun {n} {ci} hf => hkeep n ci hf)
    ⟨natLitSupported_mono_of_keep hkeep, strLitSupported_mono_of_keep hkeep⟩
    (fun sn i hs => by rw [findProj?_consBlockRecsR hpsh]; exact hs) d e hcb ?_
  rw [denoteMeta_acval_congr (φ := ψ) (fun n hn => hag n (hne n hn)) d e]
  exact h

end ConLeche.Model
