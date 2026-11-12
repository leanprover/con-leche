module

public import ConLeche.Model.Env.EnvModelM
public import ConLeche.Verify.Denote.ConstsBound
import ConLeche.Verify.Denote.EnvExtend
import ConLeche.Verify.Denote.OpenVars
public import ConLeche.Semantics.IndBlockFacts
import ConLeche.Model.Swap
import ConLeche.Model.Inductives.StructFrameKit
public import ConLeche.Verify.Inductives.BlockWF
public section

/-!
# The recursor stage's discharge, Model tier

The stage conses the block's `k` recursors — each with its rules —
onto the CONSTRUCTORS' environment, and the P carrier has to survive
it.  At `k = 1` that is one `declStep_preserves_of_ind_rec_cons`; at
`k ≥ 2` it cannot be, for the reason `envWF_consBlockRecs`
(`Verify/Inductives/BlockWF.lean`) records: a rule of `rec_0` may name
`rec_1`, so it reads only where all `k` recursors stand, and no
intermediate environment is well-formed.

The route here has two phases:

1. **the `k` RULE-LESS conses** (`envModelM_consBlockRecsBare`): a
   rule-less `recInfo` owes nothing about rules, so each cons is an
   ordinary `declStep_preserves_of_ind_rec_cons` and the whole chain is
   an induction over the recursor list;
2. **the rules, attached in one step** (`EnvModelM.swapP`,
   `Model/Swap.lean`): `consBlockRecsBare` and `consBlockRecs` cons the
   same constants in the same order, differing only in the `rules`
   field, which is exactly `SwapShList`
   (`swapShList_consBlockRecsR`).  The swap takes `EnvWF`,
   `RecCtorsStored`, `BasisPinnedTT`, `ProjOkT` and `RecRules` at the
   stored environment as hypotheses — the first is
   `envWF_consBlockRecs` and the last is the ι content the caller
   supplies.

`blockRecStaged_of` is the proposition `BlockRecAssembly.lean`
consumes, stated literally.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  IndCaps RecRule BlockShape consBlockRecs consBlockRecsBare consBlockRecsR)

universe w

variable {V : Type w} [SetTheory V]

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

/-! ## The `k` rule-less conses -/

/-- **The `k` RULE-LESS recursors' cons, P tier.**  Each head is a
`recInfo` with NO rules, so the whole `EnvModelM` bill is the ordinary
one (`declStep_preserves_of_ind_rec_cons`) with `rec_rules` free
(`recRules_cons_fresh` at an empty rule list); the chain is then an induction over the
recursor list.

The target valuation `acv` is given up front rather than built by
iterated `acvalWith`: every hypothesis is then a statement about
`acv r.1.name`, and the induction never has to shift a positional
index.  `hagree` is what ties it to the prefix's valuation off the
`k` names. -/
theorem envModelM_consBlockRecsBare {q : BlockShape}
    {acv : Name → (Name → Nat) → Term} :
    ∀ {m : Nat} {ls : List (ConstantVal × Nat)} {env : Env} (mp : EnvModelM V env),
      (ls.map (·.1.name)).Nodup →
      (∀ r ∈ ls, env.find? r.1.name = none) →
      (∀ r ∈ ls, ConLeche.reservedBasisNames.contains r.1.name = false) →
      (∀ r ∈ ls, natOpName r.1.name = false) →
      (∀ r ∈ ls,
        r.1.type.hasFvar = false ∧
        r.1.type.allLevelParamsDefined r.1.levelParams = true ∧
        r.1.type.constsResolve env = true ∧
        r.1.type.looseBVarsBounded 0 = true ∧ LitShapeAt r.1) →
      -- the stage's step (`recStage_bareCons_envWF`)
      (∀ r ∈ ls, ∀ (m' : Nat) {env' : Env}, ConLeche.EnvWF env' →
        r.1.type.constsResolve env' = true →
        ConLeche.EnvWF ⟨.recInfo r.1 (q.majorIdxAt m') (q.rulePrefixAt m') false [] :: env'.consts,
          env'.tables⟩) →
      (∀ n : Name, (∀ r ∈ ls, n ≠ r.1.name) → acv n = mp.base2.acval n) →
      (∀ r ∈ ls, ∀ ψ : Name → Nat, Term.Closed (acv r.1.name ψ)) →
      (∀ r ∈ ls, ∀ ψ₁ ψ₂ : Name → Nat,
        (∀ p ∈ r.1.levelParams, ψ₁ p = ψ₂ p) → acv r.1.name ψ₁ = acv r.1.name ψ₂) →
      (∀ r ∈ ls, ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenoted V ρ (acv r.1.name ψ)) →
      (∀ r ∈ ls, ∀ ψ : Name → Nat, ∃ ta : Term,
        denote mp.base2.acval env ψ 0 r.1.type = some ta ∧
        (∀ ρ : Nat → V, WellDenotedTy V ρ ta) ∧
        (∀ ρ : Nat → V, interp V ρ (acv r.1.name ψ) ∈ˢ interp V ρ ta)) →
      ∃ mp' : EnvModelM V (consBlockRecsBare q m ls env), mp'.base2.acval = acv
  | _, [], env, mp, _, _, _, _, _, _, hag, _, _, _, _ =>
    ⟨mp, by funext n; exact (hag n (fun _ h => nomatch h)).symm⟩
  | m, r0 :: rest, env, mp, hnd, hfr, hnres, hop, hty, hwfOf, hag, hcl, hpar, hok, hrd => by
    -- the head
    have hmem0 : r0 ∈ r0 :: rest := List.mem_cons_self
    have hfresh : env.find? r0.1.name = none := hfr r0 hmem0
    rw [List.map_cons, List.nodup_cons] at hnd
    have hnrr : ∀ r ∈ rest, r.1.name ≠ r0.1.name := fun r hr hh =>
      hnd.1 (List.mem_map.mpr ⟨r, hr, hh⟩)
    obtain ⟨-, -, h3, -, -⟩ := hty r0 hmem0
    have hcb : ConstsBound env r0.1.type := constsBound_of_constsResolve _ h3
    have hreadUp : ∀ ψ : Name → Nat, ∃ ta : Term,
        denote (acvalWith mp.base2.acval r0.1.name (acv r0.1.name))
            ⟨.recInfo r0.1 (q.majorIdxAt m) (q.rulePrefixAt m) false [] :: env.consts, env.tables⟩ ψ 0
            r0.1.type = some ta ∧
          (∀ ρ : Nat → V, WellDenotedTy V ρ ta) ∧
          (∀ ρ : Nat → V, interp V ρ (acv r0.1.name ψ) ∈ˢ interp V ρ ta) := by
      intro ψ
      obtain ⟨ta, hta, hokta, hmemta⟩ := hrd r0 hmem0 ψ
      exact ⟨ta, denote_cons_mono (c₀ := .recInfo r0.1 (q.majorIdxAt m) (q.rulePrefixAt m) false [])
        hfresh ψ 0 hcb hta, hokta, hmemta⟩
    -- the cons
    obtain ⟨mp₁, hac₁⟩ :=
      declStep_preserves_of_ind_rec_cons (A := acv r0.1.name)
        (c₀ := .recInfo r0.1 (q.majorIdxAt m) (q.rulePrefixAt m) false []) mp hfresh (hnres r0 hmem0) (hop r0 hmem0)
        ⟨r0.1, q.majorIdxAt m, q.rulePrefixAt m, false, [], rfl⟩
        (ConsHead.ofFresh
          (hwfOf r0 hmem0 m mp.base2.wf h3)
          (fun ψ => hcl r0 hmem0 ψ) (hnres r0 hmem0)
          (fun _ _ _ _ rules heq r hr => by
            injection heq with _ _ _ _ e4
            subst e4
            exact nomatch hr))
        (fun ψ₁ ψ₂ h => hpar r0 hmem0 ψ₁ ψ₂ h)
        (fun ψ ρ => hok r0 hmem0 ψ ρ)
        (fun ψ => (hreadUp ψ).imp fun _ h => h.1)
        (fun ψ ta hta ρ => by
          obtain ⟨ta', hta', hokta, -⟩ := hreadUp ψ
          obtain rfl := Option.some.inj (hta'.symm.trans hta)
          exact hokta ρ)
        (fun ψ ta hta ρ => by
          obtain ⟨ta', hta', -, hmemta⟩ := hreadUp ψ
          obtain rfl := Option.some.inj (hta'.symm.trans hta)
          exact hmemta ρ)
        (fun m₂ hac φ =>
          recRules_cons_fresh (c₀ := .recInfo r0.1 (q.majorIdxAt m) (q.rulePrefixAt m) false [])
            mp hfresh
            (fun _ _ _ _ _ heq => by injection heq with _ _ _ _ e4; exact e4.symm) m₂ hac φ)
    -- the tail
    show ∃ mp' : EnvModelM V (consBlockRecsBare q (m + 1) rest
        ⟨.recInfo r0.1 (q.majorIdxAt m) (q.rulePrefixAt m) false [] :: env.consts, env.tables⟩),
      mp'.base2.acval = acv
    refine envModelM_consBlockRecsBare mp₁ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact hnd.2
    · intro r hr
      rw [ConLeche.Env.find?_cons, ite_eq_right (fun hh => hnrr r hr hh.symm)]
      exact hfr r (List.mem_cons_of_mem _ hr)
    · exact fun r hr => hnres r (List.mem_cons_of_mem _ hr)
    · exact fun r hr => hop r (List.mem_cons_of_mem _ hr)
    · intro r hr
      obtain ⟨g1, g2, g3, g4, g5⟩ := hty r (List.mem_cons_of_mem _ hr)
      exact ⟨g1, g2, Expr.constsResolve_mono g3, g4, g5⟩
    · exact fun r hr => hwfOf r (List.mem_cons_of_mem _ hr)
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
    · exact fun r hr => hpar r (List.mem_cons_of_mem _ hr)
    · exact fun r hr => hok r (List.mem_cons_of_mem _ hr)
    · intro r hr ψ
      obtain ⟨ta, hta, hokta, hmemta⟩ := hrd r (List.mem_cons_of_mem _ hr) ψ
      refine ⟨ta, ?_, hokta, hmemta⟩
      rw [hac₁]
      exact denote_cons_mono hfresh ψ 0
        (constsBound_of_constsResolve _ (hty r (List.mem_cons_of_mem _ hr)).2.2.1) hta

/-! ## The rules, attached in one step

`consBlockRecsBare` and `consBlockRecs` cons the SAME constants in the
SAME order — the first with empty rule lists, the second with
`sumRules`' — which is exactly `SwapPairSh` at every position. -/

/-- The two recursor conses are a shape-level rule-list swap. -/
theorem swapShList_consBlockRecsR {R : Nat → RecDatum → Bool × List RecRule}
    {q : BlockShape} :
    ∀ {m : Nat} {rs : List RecDatum} {envA envB : Env},
      ConLeche.SwapShList envA.consts envB.consts →
      ConLeche.SwapShList (consBlockRecsBare q m (bareOf rs) envA).consts
        (consBlockRecsR R q m rs envB).consts
  | _, [], _, _, h => h
  | m, (cvRa, rhss, nIdx, ctorList) :: rest, envA, envB, h => by
    simp only [bareOf, List.map_cons, consBlockRecsBare, consBlockRecsR]
    exact swapShList_consBlockRecsR (R := R) (q := q)
      (rs := rest) (envA := ⟨_ :: envA.consts, envA.tables⟩) (envB := ⟨_ :: envB.consts, envB.tables⟩)
      (ConLeche.SwapShList.cons
        (Or.inr ⟨cvRa, q.majorIdxAt m, q.rulePrefixAt m, _, _, rfl, rfl⟩) h)

/-- **The three non-`EnvWF` syntactic facts across a rule-list swap**,
off the head facts a `RecCtorsStored` needs and nothing else (the `EnvWF` arm is the one
that consumes the rules' own syntax, and at the block it is
`envWF_consBlockRecs`). -/
theorem recSwapFacts3 {envSelf env₃ : Env} {cval : (Name → (Name → Nat) → Term)}
    (hctorsS : ConLeche.RecCtorsStored envSelf)
    (hbpS : BasisPinnedTT envSelf cval) (hprojS : ProjOkT envSelf)
    (hswR : ConLeche.SwapShList envSelf.consts env₃.consts)
    (htabR : env₃.tables = envSelf.tables)
    (hnresR : SwapNResS envSelf env₃)
    (hnew : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat) (isK : Bool) (rules : List RecRule),
      env₃.find? n = some (.recInfo cv mI rP isK rules) →
      envSelf.find? n = some (.recInfo cv mI rP false []) → cv.name = n →
      ∀ r ∈ rules,
        (∃ cvj cnP cnF iT,
          envSelf.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF iT))) :
    ConLeche.RecCtorsStored env₃ ∧ BasisPinnedTT env₃ cval ∧ ProjOkT env₃ := by
  have hcg : ConLeche.SwapCongr envSelf env₃ := ConLeche.SwapShList.congrEnv hswR htabR
  have hcorr := ConLeche.swapSh_find?_corrEnv hswR
  have hsame : ∀ (n : Name) (ci : ConstantInfo),
      (∀ cv mI rP isK rules, ci ≠ .recInfo cv mI rP isK rules) →
      (env₃.find? n = some ci ↔ envSelf.find? n = some ci) :=
    fun n ci hnr =>
      ⟨fun h => hcg.findDown n ci h hnr, fun h => hcg.findUp n ci h hnr⟩
  have hkeep : ∀ (m : Name) (ci : ConstantInfo),
      (∀ cv mI rP isK rules, ci ≠ .recInfo cv mI rP isK rules) →
      envSelf.find? m = some ci → env₃.find? m = some ci :=
    fun m ci hnr hfc => hcg.findUp m ci hfc hnr
  refine ⟨?_, ?_, ?_⟩
  · -- `RecCtorsStored`
    intro n cv mI rP isK rules hf r hr
    rcases hcorr n with heq | ⟨cv', mI', rP', isK', rules', h₀, h₃, hn'⟩
    · have hfS : envSelf.find? n = some (.recInfo cv mI rP isK rules) := by
        rw [← heq]; exact hf
      obtain ⟨cvj, cnP, cnF, iT, hfc⟩ := hctorsS n cv mI rP isK rules hfS r hr
      exact ⟨cvj, cnP, cnF, iT, hkeep _ _
          (fun _ _ _ _ _ hcon => ConstantInfo.noConfusion hcon) hfc⟩
    · obtain ⟨e1, e2, e3, -⟩ :=
        ConstantInfo.recInfo.inj (Option.some.inj (h₃.symm.trans hf))
      obtain ⟨cvj, cnP, cnF, iT, hfc⟩ :=
        hnew n cv mI rP isK rules hf (by rw [← e1, ← e2, ← e3]; exact h₀)
          (by rw [← e1]; exact hn') r hr
      exact ⟨cvj, cnP, cnF, iT, hkeep _ _
          (fun _ _ _ _ _ hcon => ConstantInfo.noConfusion hcon) hfc⟩
  · -- `BasisPinnedTT`: a genuinely swapped entry is never reserved
    intro n ci hf hres
    have hf₀ : envSelf.find? n = some ci := by
      rcases hcorr n with heq | ⟨cv, mI, rP, isK, rules, h₀, h₃, -⟩
      · rw [← heq]; exact hf
      · rcases hnresR n cv mI rP isK rules h₀ h₃ with ⟨rfl, rfl⟩ | hnr
        · rw [h₃] at hf
          obtain rfl := Option.some.inj hf
          exact h₀
        · rw [hnr] at hres
          exact nomatch hres
    exact (let hp := hbpS n ci hf₀ hres
     ⟨hp.1, hp.2.1.mono (fun x cvj cnP cnF iT hx => by
        rcases hcorr x with heq | ⟨cv, mI, rP, isK, rules, h₀, h₃, -⟩
        · rw [← heq]; exact hx
        · rw [h₃] at hx; exact nomatch hx), hp.2.2⟩)
  · -- `ProjOkT`: projection tables are untouched
    intro n tbl hf
    exact ConLeche.TableHead.mono (fun n ci hnr hf' => (hsame n ci hnr).mpr hf')
      (hprojS n tbl ((hcg.tableEq n).trans hf))

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
      ite_eq_right (fun h => hne r0 List.mem_cons_self h.symm)]

/-! (A name that is none of the `k` recursors' is found as it was:
`find?_consBlockRecsR_of_ne`, `Verify/Inductives/BlockWF.lean`, where
the literal guards' crossing needs it too.) -/

/-! ## What the cons leaves alone

The three conjuncts `blockRecStaged_of` states beyond the carrier itself.
`findProj?` is EQUAL across the cons (the cons stores no table, and a
stored table's structure is no fresh name), and so is the
`Nat`-literal guard (the three slots are reserved names, and a block
recursor's is not).  The `String` guard is the one that is only
MONOTONE, and it is the recursor stage's NAME check that makes it
congruent too (`ConLeche.strLitSupported_consBlockRecsR`). -/

/-- A name found in the constructors' environment is found unchanged
after the recursors. -/
theorem find?_consBlockRecsR_keep {R : Nat → RecDatum → Bool × List RecRule} {q : BlockShape} {rs : List RecDatum}
    {envC : Env} (hfr : ∀ r ∈ rs, envC.find? r.1.name = none) :
    ∀ (n : Name) (c : ConstantInfo), envC.find? n = some c →
      (consBlockRecsR R q 0 rs envC).find? n = some c := by
  intro n c hf
  rw [find?_consBlockRecsR_of_ne (fun r hr hh => by rw [hh, hfr r hr] at hf; exact nomatch hf)]
  exact hf

/-- The recursors' cons stores no projection table. -/
theorem findProj?_consBlockRecsR {R : Nat → RecDatum → Bool × List RecRule} {q : BlockShape} {rs : List RecDatum}
    {envC : Env} (hwf : ConLeche.EnvWF envC) (hfr : ∀ r ∈ rs, envC.find? r.1.name = none)
    (sn : Name) (i : Nat) :
    (consBlockRecsR R q 0 rs envC).findProj? sn i = envC.findProj? sn i :=
  hwf.findProj?_extend (fun n hn => by
      cases h : envC.find? n with
      | none => rw [h] at hn; exact nomatch hn
      | some c => rw [find?_consBlockRecsR_keep (R := R) (q := q) hfr n c h]; rfl)
    (ConLeche.consBlockRecsR_tables R q 0 rs envC) sn i

/-! ## The stage's stored rules, inverted

`blockRecStaged_of`'s `hnew` — the `RecCtorsStored` head facts of the
stored rules — is not a run fact but a consequence of `sumRules`' own
construction, once the cons is inverted.  That inversion is the only
place this file looks INSIDE `consBlockRecs`. -/

/-- **The recursors' cons, inverted**: a constant found above the `k`
recursors is one of them, with its rules `sumRules`', or was stored
below. -/
theorem find?_consBlockRecsR_inv {R : Nat → RecDatum → Bool × List RecRule}
    {q : BlockShape} :
    ∀ {m : Nat} {rs : List RecDatum} {env : Env} {n : Name} {ci : ConstantInfo},
      (consBlockRecsR R q m rs env).find? n = some ci →
      env.find? n = some ci ∨
      ∃ (j : Nat) (r : RecDatum), rs[j]? = some r ∧ n = r.1.name ∧
        ci = .recInfo r.1 (q.majorIdxAt (m + j)) (q.rulePrefixAt (m + j)) (R (m + j) r).1 (R (m + j) r).2
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
block's own — stored in the constructors' environment, hence in the bare one. -/
theorem recCtorsHead_consBlockRecsR {R : Nat → RecDatum → Bool × List RecRule} {q : BlockShape} {rs : List RecDatum}
    {envC : Env} {fireOf : Nat → RecDatum → ConLeche.RecRuleFire}
    (hshape : ConLeche.RecRulesShape R rs fireOf)
    (hfr : ∀ r ∈ rs, envC.find? r.1.name = none)
    (hctorsIn : ∀ r ∈ rs, ∀ ctor ∈ r.2.2.2,
      ∃ cvj cnP cnF iT, envC.find? ctor.1.name = some (.ctorInfo cvj cnP cnF iT)) :
    ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat) (isK : Bool) (rules : List RecRule),
      (consBlockRecsR R q 0 rs envC).find? n
        = some (.recInfo cv mI rP isK rules) →
      (consBlockRecsBare q 0 (bareOf rs) envC).find? n = some (.recInfo cv mI rP false []) →
      cv.name = n →
      ∀ r ∈ rules,
        (∃ cvj cnP cnF iT, (consBlockRecsBare q 0 (bareOf rs) envC).find? (RecRule.ctor r)
          = some (.ctorInfo cvj cnP cnF iT)) := by
  have hkeepB := find?_consBlockRecsBare_keep (q := q) hfr
  intro n cv mI rP isK rules hf hfB hname rl hrl
  rcases find?_consBlockRecsR_inv hf with hbelow | ⟨j, r0, hr0, rfl, hci⟩
  · -- stored below the recursors: the bare environment finds the same
    -- record, so the rule list is empty and there is nothing to prove
    exfalso
    rw [hkeepB n _ hbelow] at hfB
    obtain ⟨-, -, -, -, e4⟩ := ConstantInfo.recInfo.inj (Option.some.inj hfB)
    rw [e4] at hrl
    exact nomatch hrl
  · obtain ⟨-, -, -, -, rfl⟩ := ConstantInfo.recInfo.inj hci
    rw [Nat.zero_add] at hrl
    obtain ⟨i, ctor, rhs, hi, -, rfl⟩ := hshape j r0 hr0 rl hrl
    obtain ⟨cvj, cnP, cnF, iT, hfc⟩ := hctorsIn r0 (List.mem_of_getElem? hr0) ctor (List.mem_of_getElem? hi)
    exact ⟨cvj, cnP, cnF, iT, hkeepB _ _ hfc⟩

/-! ## The stage's cons, whole, and its proposition

Both theorems are stated over the recursors' own facts (the section's
variables): their names fresh, distinct, unreserved and not
projection-shaped, their stored types closed and resolving, and the
post-cons valuation `acv` — the constructors' off the new names, closed,
level-local and graded, inhabiting the types' readings. -/

section Staged

variable {R : Nat → RecDatum → Bool × List RecRule} {q : BlockShape} {rs : List RecDatum}
  {envC : Env} {acv : Name → (Name → Nat) → Term} (mpC : EnvModelM V envC)
  (hnd : (rs.map (·.1.name)).Nodup)
  (hfr : ∀ r ∈ rs, envC.find? r.1.name = none)
  (hnres : ∀ r ∈ rs, ConLeche.reservedBasisNames.contains r.1.name = false)
  (hop : ∀ r ∈ rs, natOpName r.1.name = false)
  (hty : ∀ r ∈ rs,
    r.1.type.hasFvar = false ∧
    r.1.type.allLevelParamsDefined r.1.levelParams = true ∧
    r.1.type.constsResolve envC = true ∧
    r.1.type.looseBVarsBounded 0 = true ∧ LitShapeAt r.1)
  (hag : ∀ n : Name, (∀ r ∈ rs, n ≠ r.1.name) → acv n = mpC.base2.acval n)
  (hcl : ∀ r ∈ rs, ∀ ψ : Name → Nat, Term.Closed (acv r.1.name ψ))
  (hpar : ∀ r ∈ rs, ∀ ψ₁ ψ₂ : Name → Nat,
    (∀ p ∈ r.1.levelParams, ψ₁ p = ψ₂ p) → acv r.1.name ψ₁ = acv r.1.name ψ₂)
  (hok : ∀ r ∈ rs, ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenoted V ρ (acv r.1.name ψ))
  (hrd : ∀ r ∈ rs, ∀ ψ : Name → Nat, ∃ ta : Term,
    denote mpC.base2.acval envC ψ 0 r.1.type = some ta ∧
    (∀ ρ : Nat → V, WellDenotedTy V ρ ta) ∧
    (∀ ρ : Nat → V, interp V ρ (acv r.1.name ψ) ∈ˢ interp V ρ ta))

include mpC hnd hfr hnres hop hty hag hcl hpar hok hrd

/-- **The `k` recursors' cons with their rules, P tier.**  The two
phases composed: the rule-less chain, then the rule-list swap.  The
`rec_rules` row (`hrecP`) is the ι content the caller supplies; every
other row is discharged here. -/
theorem envModelM_consBlockRecsR
    (hwfOf : ∀ r ∈ rs, ∀ (m' : Nat) {env' : Env}, ConLeche.EnvWF env' →
      r.1.type.constsResolve env' = true →
      ConLeche.EnvWF ⟨.recInfo r.1 (q.majorIdxAt m') (q.rulePrefixAt m') false [] :: env'.consts,
        env'.tables⟩)
    (hwf₃ : ConLeche.EnvWF (consBlockRecsR R q 0 rs envC))
    (hnew : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat) (isK : Bool) (rules : List RecRule),
      (consBlockRecsR R q 0 rs envC).find? n
        = some (.recInfo cv mI rP isK rules) →
      (consBlockRecsBare q 0 (bareOf rs) envC).find? n = some (.recInfo cv mI rP false []) →
      cv.name = n →
      ∀ r ∈ rules,
        (∃ cvj cnP cnF iT, (consBlockRecsBare q 0 (bareOf rs) envC).find? (RecRule.ctor r)
          = some (.ctorInfo cvj cnP cnF iT)))
    (hrecP : ∀ m₃ : EnvModel V (consBlockRecsR R q 0 rs envC),
      m₃.acval = acv → ∀ φ : Name → Nat, RecRules m₃ φ) :
    ∃ mp' : EnvModelM V (consBlockRecsR R q 0 rs envC),
      mp'.base2.acval = acv := by
  -- phase 1: the `k` rule-less conses
  have hmemB : ∀ x ∈ bareOf rs, ∃ r ∈ rs, x.1 = r.1 := fun x hx => mem_bareOf hx
  obtain ⟨mpB, hacB⟩ :=
    envModelM_consBlockRecsBare (q := q) (acv := acv) (m := 0) (ls := bareOf rs) mpC
      (by rw [bareOf_map_name]; exact hnd)
      (fun x hx => by obtain ⟨r, hr, he⟩ := hmemB x hx; rw [he]; exact hfr r hr)
      (fun x hx => by obtain ⟨r, hr, he⟩ := hmemB x hx; rw [he]; exact hnres r hr)
      (fun x hx => by obtain ⟨r, hr, he⟩ := hmemB x hx; rw [he]; exact hop r hr)
      (fun x hx => by obtain ⟨r, hr, he⟩ := hmemB x hx; rw [he]; exact hty r hr)
      (fun x hx => by obtain ⟨r, hr, he⟩ := hmemB x hx; rw [he]; exact hwfOf r hr)
      (fun n hn => hag n (fun r hr => hn (r.1, r.2.2.1) (List.mem_map_of_mem hr)))
      (fun x hx => by obtain ⟨r, hr, he⟩ := hmemB x hx; rw [he]; exact hcl r hr)
      (fun x hx => by obtain ⟨r, hr, he⟩ := hmemB x hx; rw [he]; exact hpar r hr)
      (fun x hx => by obtain ⟨r, hr, he⟩ := hmemB x hx; rw [he]; exact hok r hr)
      (fun x hx => by obtain ⟨r, hr, he⟩ := hmemB x hx; rw [he]; exact hrd r hr)
  -- phase 2: the rules, attached by the swap
  have hswR : ConLeche.SwapShList (consBlockRecsBare q 0 (bareOf rs) envC).consts
      (consBlockRecsR R q 0 rs envC).consts :=
    swapShList_consBlockRecsR (ConLeche.SwapShList.of_eq envC.consts)
  have hnresS : SwapNResS (consBlockRecsBare q 0 (bareOf rs) envC)
      (consBlockRecsR R q 0 rs envC) := by
    intro n cv mI rP isK rules h₀ h₃
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
      obtain ⟨-, -, -, e3, e4⟩ := ConstantInfo.recInfo.inj (Option.some.inj h₃)
      exact ⟨e3.symm, e4.symm⟩
    · exact Or.inr (Bool.not_eq_true _ ▸ hres)
  have htabR : (consBlockRecsR R q 0 rs envC).tables
      = (consBlockRecsBare q 0 (bareOf rs) envC).tables := by
    rw [ConLeche.consBlockRecsR_tables, ConLeche.consBlockRecsBare_tables]
  obtain ⟨hctors₃, hbp₃, hproj₃⟩ :=
    recSwapFacts3 mpB.base2.rec_ctors mpB.base2.basis_pinned mpB.base2.proj_ok
      hswR htabR hnresS hnew
  obtain ⟨mp₃, hac₃, -⟩ :=
    EnvModelM.swapP mpB hswR htabR hwf₃ hctors₃ hbp₃ hproj₃
      (fun m₃ hac φ => hrecP m₃ (by rw [hac, hacB]) φ)
  exact ⟨mp₃, by rw [hac₃, hacB]⟩

/-- **The recursors' stage, discharged.**

The carrier at the recursors' environment, with the three facts the
tables' stage and the final assembly read off it: the valuation is the
constructors' own off the `k` new names; every stored lookup survives;
and every reading of a constructor-environment subject survives.

One premise beyond the cons's own is worth naming.  `hresRec` is
the recursor stage's own NAME check
(`ConLeche.recStage_reserved`): without it the
`String`-literal guard is monotone but not congruent — nothing else
would forbid a recursor from being named `List.cons` at a block that
declares `List` — and conjunct 3's EQUATION (as opposed to its
monotone half, `denote_consBlockRecsR_mono`, which needs nothing)
is then refutable.  With it both guards are untouched
(`ConLeche.natLitSupported_consBlockRecsR` /
`strLitSupported_consBlockRecsR`). -/
theorem blockRecStaged_of
    -- the stage's steps and its result, well formed (`recStage_bareCons_envWF`,
    -- `recStage_envWF_consR`)
    (hwfOf : ∀ r ∈ rs, ∀ (m' : Nat) {env' : Env}, ConLeche.EnvWF env' →
      r.1.type.constsResolve env' = true →
      ConLeche.EnvWF ⟨.recInfo r.1 (q.majorIdxAt m') (q.rulePrefixAt m') false [] :: env'.consts,
        env'.tables⟩)
    (hwf₃ : ConLeche.EnvWF (consBlockRecsR R q 0 rs envC))
    (hctorsIn : ∀ r ∈ rs, ∀ ctor ∈ r.2.2.2,
      ∃ cvj cnP cnF iT, envC.find? ctor.1.name = some (.ctorInfo cvj cnP cnF iT))
    {fireOf : Nat → RecDatum → ConLeche.RecRuleFire}
    (hshape : ConLeche.RecRulesShape R rs fireOf)
    (hrecP : ∀ m₃ : EnvModel V (consBlockRecsR R q 0 rs envC),
      m₃.acval = acv → ∀ φ : Name → Nat, RecRules m₃ φ)
    (hresRec : ∀ r ∈ rs, ConLeche.reservedRecName r.1.name = false) :
    ∃ mp' : EnvModelM V (consBlockRecsR R q 0 rs envC),
      (∀ n : Name, (envC.find? n).isSome = true →
        mp'.base2.acval n = mpC.base2.acval n) ∧
      (∀ (n : Name) (c : ConstantInfo), envC.find? n = some c →
        (consBlockRecsR R q 0 rs envC).find? n = some c) ∧
      (∀ (ψ : Name → Nat) (d : Nat) (e : Expr), ConstsBound envC e →
        denote mp'.base2.acval (consBlockRecsR R q 0 rs envC) ψ d e
          = denote mpC.base2.acval envC ψ d e) := by
  have hkeep := find?_consBlockRecsR_keep (R := R) (q := q) hfr
  have hne : ∀ n : Name, (envC.find? n).isSome = true → ∀ r ∈ rs, n ≠ r.1.name := by
    intro n hn r hr hh
    rw [hh, hfr r hr] at hn
    exact nomatch hn
  obtain ⟨mp', hac'⟩ :=
    envModelM_consBlockRecsR mpC hnd hfr hnres hop hty hag hcl hpar hok hrd
      hwfOf hwf₃
      (recCtorsHead_consBlockRecsR (R := R) hshape hfr hctorsIn) hrecP
  refine ⟨mp', fun n hn => by rw [hac']; exact hag n (hne n hn), hkeep, ?_⟩
  · -- the readings of the constructors' environment survive, verbatim
    intro ψ d e hcb
    rw [hac',
      ← denote_envExtend (acval := acv) (φ := ψ) (fun {n} {ci} h => hkeep n ci h)
        ⟨(ConLeche.natLitSupported_consBlockRecsR hresRec).symm,
          (ConLeche.strLitSupported_consBlockRecsR hresRec).symm⟩
        (findProj?_consBlockRecsR mpC.base2.wf hfr) d e hcb]
    exact denote_acval_congr
      (fun n hn => hag n (hne n hn)) d e

end Staged

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
uses everywhere else (`denote_cons_mono`): a SUCCESSFUL
reading at the constructors' environment is reproduced verbatim at the
recursors'.  The equation `blockRecStaged_of` states needs the NAME
check (`hresRec`); this does not. -/
theorem denote_consBlockRecsR_mono {R : Nat → RecDatum → Bool × List RecRule} {q : BlockShape} {rs : List RecDatum}
    {envC : Env} {acv acvC : Name → (Name → Nat) → Term}
    (hfr : ∀ r ∈ rs, envC.find? r.1.name = none)
    (hag : ∀ n : Name, (∀ r ∈ rs, n ≠ r.1.name) → acv n = acvC n)
    (ψ : Name → Nat) (d : Nat) (e : Expr) (hcb : ConstsBound envC e) {ea : Term}
    (h : denote acvC envC ψ d e = some ea) :
    denote acv (consBlockRecsR R q 0 rs envC) ψ d e = some ea := by
  have hkeep := find?_consBlockRecsR_keep (R := R) (q := q) hfr
  have hne : ∀ n : Name, (envC.find? n).isSome = true → ∀ r ∈ rs, n ≠ r.1.name := by
    intro n hn r hr hh
    rw [hh, hfr r hr] at hn
    exact nomatch hn
  refine denote_envExtend_mono (acval := acv) (φ := ψ)
    (fun {n} {ci} hf => hkeep n ci hf)
    ⟨natLitSupported_mono_of_keep hkeep, strLitSupported_mono_of_keep hkeep⟩
    (findProj?_mono_of_tables (fun {n} {ci} hf => hkeep n ci hf)
      (ConLeche.consBlockRecsR_tables R q 0 rs envC)) d e hcb ?_
  rw [denote_acval_congr (φ := ψ) (fun n hn => hag n (hne n hn)) d e]
  exact h

end ConLeche.Model
