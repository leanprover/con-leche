module

public import ConLeche.Model.Inductives.TowerCons
public import ConLeche.Verify.Inductives.MutualInv
import ConLeche.Verify.Inductives.MutualWF
import ConLeche.Verify.ProjSlots
import ConLeche.Verify.Inductives.FixRec
import ConLeche.Verify.Inductives.StructRec
import ConLeche.Model.Inductives.MutualFormersKit
import ConLeche.Model.Inductives.MutualRuleRead

public section

/-!
# The mutual block's `.proj` and name bookkeeping (task #315 U-10)

The RUN-LEVEL facts the projection-table stage of a mutual block asks
for, stated over the kernel's stage equations
(`ConLeche/Semantics/Inductives/DeclMutual.lean`'s `DeclMutualRun`) and
needing NO model beyond `EnvWF` and `ProjOkT` of the PRE-BLOCK
environment:

* `mutualNoProj` — **no stored piece mentions a member's
  projections** at the recursors' environment.  The member is not
  stored before the block (`mutualMemberNames`), so nothing stored
  there mentions its projections (`noProjEnv_of_fresh`, with
  `findProj?_none_of_indFresh` for the empty slot); the block's own
  pieces are either READ at an environment where the slot is still
  empty (the members' types resolve at the pre-block environment, the
  constructors' are `annotateCore`d at the formers' environment) or
  GENERATED from those (the recursor types and the rules' right-hand
  sides, through the same `struct*` pieces the fixpoint route uses —
  `Verify/Inductives/FixRec.lean`'s `NoProjAt` kit at `k` motives).
* `mutualMemberNames` / `mutualMemberNames_eq` — the members' names:
  fresh, not a projection function's, unreserved, and the block's
  recursor name at the member is the member's `.rec`; as a list, the
  checked formers' names ARE the block record's `memberNames`.
* `mutualCtorNames` — the constructors' names: not a projection
  function's, unreserved.

`ConLeche/Model/Inductives/FixStageTable.lean` runs the same argument
on the fixpoint route (one member, the table's freshness in place of
`ProjOkT`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecRule ProjEntry ProjTable
  PropWhen BinderMeta CheckMode fueledOps MutualBlock MutualFormerA MutualFormer MutualCtor
  MutualCtor4 RecFieldKind)

/-! ## The empty slot across the block's conses -/

/-- **An unstored structure has no projection table**: a stored table's
entries carry their structure as a STORED inductive (`ProjOkT`), so a
name the environment does not hold has an empty slot at every field. -/
theorem findProj?_none_of_indFresh {env : Env} (hproj : ConLeche.ProjOkT env) {T : Name}
    (hT : env.find? T = none) (i : Nat) : env.findProj? T i = none := by
  cases hf : env.findProj? T i with
  | none => rfl
  | some entry =>
    exfalso
    obtain ⟨-, -, -, -, ⟨cvT, caps, hfind, -⟩, -⟩ := hproj.towerHead hf
    have hsn : entry.structName = T := by
      have hf' := hf
      unfold ConLeche.Env.findProj? at hf'
      cases hfn : env.find? (ConLeche.projTableName T) with
      | none => rw [hfn] at hf'; exact nomatch hf'
      | some ci =>
        cases ci with
        | projInfo tbl =>
          have hname : (ConstantInfo.projInfo tbl).name = ConLeche.projTableName T :=
            eq_of_beq (by simpa using List.find?_some hfn)
          rw [hfn] at hf'
          have hf'' : (if i < tbl.numFields then some (tbl.entry i) else none) = some entry := hf'
          by_cases hlt : i < tbl.numFields
          · rw [if_pos hlt] at hf''
            obtain rfl := Option.some.inj hf''
            show tbl.structName = T
            simp only [ConstantInfo.name, ConstantInfo.toConstantVal,
              ConLeche.projTableName] at hname
            simpa using hname
          · rw [if_neg hlt] at hf''
            exact nomatch hf''
        | _ => rw [hfn] at hf'; exact nomatch hf'
    rw [hsn, hT] at hfind
    exact nomatch hfind

/-- An empty projection slot survives a cons that is not a table. -/
theorem findProj?_none_cons {env : Env} {c₀ : ConstantInfo} {T : Name} {i : Nat}
    (hnt : ∀ tbl, c₀ ≠ .projInfo tbl) (h : env.findProj? T i = none) :
    (⟨c₀ :: env.consts⟩ : Env).findProj? T i = none := by
  have h' : (⟨c₀ :: env.consts⟩ : Env).find? (ConLeche.projTableName T)
      = if c₀.name = ConLeche.projTableName T then some c₀
        else env.find? (ConLeche.projTableName T) := ConLeche.Env.find?_cons
  unfold ConLeche.Env.findProj? at h ⊢
  rw [h']
  by_cases hname : c₀.name = ConLeche.projTableName T
  · rw [if_pos hname]
    cases c₀ with
    | projInfo tbl => exact absurd rfl (hnt tbl)
    | _ => rfl
  · rw [if_neg hname]
    exact h

/-- An empty projection slot survives the members' conses. -/
theorem findProj?_none_consMutualFormers {T : Name} {i : Nat} :
    ∀ {fms : List MutualFormerA} {env₀ : Env}, env₀.findProj? T i = none →
      (ConLeche.consMutualFormers fms env₀).findProj? T i = none
  | [], _, h => h
  | _ :: _, _, h => by
    simp only [ConLeche.consMutualFormers]
    exact findProj?_none_consMutualFormers
      (findProj?_none_cons (fun _ hh => ConstantInfo.noConfusion hh) h)

/-! ## `NoProjEnv` across the block's conses -/

/-- `NoProjEnv` across the members' conses. -/
theorem noProjEnv_consMutualFormers {T : Name} {i : Nat} :
    ∀ {fms : List MutualFormerA} {env₀ : Env}, NoProjEnv env₀ T i →
      (∀ f ∈ fms, Expr.NoProjAt T i f.cvTa.type) →
      NoProjEnv (ConLeche.consMutualFormers fms env₀) T i
  | [], _, h, _ => h
  | f :: rest, env₀, h, hall => by
    simp only [ConLeche.consMutualFormers]
    refine noProjEnv_consMutualFormers (h.cons (c₀ := .indInfo f.cvTa {})
      (NoProjHead.ofType (hall f List.mem_cons_self) (fun _ _ _ hh => nomatch hh)
        (fun _ _ _ _ hh => nomatch hh) (fun _ hh => nomatch hh)))
      (fun f' hf' => hall f' (List.mem_cons_of_mem _ hf'))

/-- `NoProjEnv` across the constructors' conses. -/
theorem noProjEnv_consMutualCtors {T : Name} {i nP : Nat} :
    ∀ {ctorsA : List (ConstantVal × Nat)} {env₀ : Env}, NoProjEnv env₀ T i →
      (∀ cA ∈ ctorsA, Expr.NoProjAt T i cA.1.type) →
      NoProjEnv (ConLeche.consMutualCtors nP ctorsA env₀) T i
  | [], _, h, _ => h
  | cA :: rest, env₀, h, hall => by
    simp only [ConLeche.consMutualCtors]
    refine noProjEnv_consMutualCtors (h.cons (c₀ := .ctorInfo cA.1 nP cA.2)
      (NoProjHead.ofType (hall cA List.mem_cons_self) (fun _ _ _ hh => nomatch hh)
        (fun _ _ _ _ hh => nomatch hh) (fun _ hh => nomatch hh)))
      (fun c' hc' => hall c' (List.mem_cons_of_mem _ hc'))

/-- **The stored rules of a mutual recursor, shaped**: every one of
them carries a right-hand side of the input list, and none fires
`.nested` (the mode is `.plain` or `.inert` by construction). -/
theorem mutualRules_shape {find? : Name → Option ConstantInfo} {recName : Name}
    {nP mI rP : Nat} {recTy : Expr} :
    ∀ {l : List (MutualCtor × Expr)} {r : RecRule},
      r ∈ ConLeche.mutualRules find? recName nP mI rP recTy l →
      (∃ p ∈ l, RecRule.rhs r = p.2) ∧
        ∀ lvls pins, RecRule.fire r = .nested lvls pins → False
  | [], r, hr => by simp only [ConLeche.mutualRules] at hr; exact absurd hr List.not_mem_nil
  | (c, rhs) :: rest, r, hr => by
    simp only [ConLeche.mutualRules, List.mem_cons] at hr
    rcases hr with rfl | hr
    · refine ⟨⟨(c, rhs), List.mem_cons_self, rfl⟩, ?_⟩
      intro lvls pins hfire
      simp only [ConLeche.recRuleBits] at hfire
      split at hfire <;> exact nomatch hfire
    · obtain ⟨⟨p, hp, hrhs⟩, hnest⟩ := mutualRules_shape hr
      exact ⟨⟨p, List.mem_cons_of_mem _ hp, hrhs⟩, hnest⟩

/-- `NoProjEnv` across the recursors' group store. -/
theorem noProjEnv_storeMutualRecs {T : Name} {i : Nat} {envR : Env} {b : MutualBlock}
    {fms : List MutualFormerA} {rulesOf : List (List (MutualCtor × Expr))} :
    ∀ {l : List (ConstantVal × Nat)} {env₀ : Env}, NoProjEnv env₀ T i →
      (∀ x ∈ l, Expr.NoProjAt T i x.1.type ∧
        ∀ r ∈ ConLeche.mutualRules envR.find? x.1.name b.nP
            (b.rulePrefix + (fms.getD x.2 default).nIdx) b.rulePrefix x.1.type
            (rulesOf.getD x.2 []),
          Expr.NoProjAt T i (RecRule.rhs r)) →
      NoProjEnv (ConLeche.storeMutualRecs envR b fms rulesOf l env₀) T i
  | [], _, h, _ => h
  | (cvRa, mIdx) :: rest, env₀, h, hall => by
    simp only [ConLeche.storeMutualRecs]
    refine noProjEnv_storeMutualRecs (h.cons ⟨(hall _ List.mem_cons_self).1,
      (fun _ _ _ hh => nomatch hh), ?_, (fun _ hh => nomatch hh)⟩)
      (fun x hx => hall x (List.mem_cons_of_mem _ hx))
    intro cv mI rP rules heq r hr
    injection heq with _ _ _ hrules
    rw [← hrules] at hr
    exact ⟨(hall _ List.mem_cons_self).2 r hr,
      fun lvls pins hfire pin _ => absurd hfire (fun hh =>
        (mutualRules_shape hr).2 lvls pins hh)⟩

/-! ## The generated terms carry no new `.proj` node

The generated recursor types and rules are built from the members' and
constructors' own types through the SAME pieces the fixpoint route
uses (`structFamI`, `structPsAt`, `structCtorSpineAt`,
`structFieldTeleOf`/`structFieldIdxOf`, `structTeleAt`/`structIdxAt`),
so these are `Verify/Inductives/FixRec.lean`'s lemmas at `k` motives. -/

section NoProj

variable {T : Name} {i : Nat}

/-- The recursors' leading spine mentions no projection. -/
theorem noProjAt_mutualRecPrefixAt (nP k n nF e : Nat) :
    ∀ a ∈ ConLeche.mutualRecPrefixAt nP k n nF e, Expr.NoProjAt T i a := by
  intro a ha
  simp only [ConLeche.mutualRecPrefixAt, List.mem_append, List.mem_map] at ha
  rcases ha with (ha | ⟨q, -, rfl⟩) | ⟨q, -, rfl⟩
  · exact ConLeche.Expr.NoProjAt.structPsAt _ _ a ha
  · simp
  · simp

/-- A recursive field's inductive hypothesis mentions no projection its
telescope and index expressions do not. -/
theorem noProjAt_mutualIhApp {recOf : Nat → Name} {rlvls : List Level} {pw : PropWhen}
    {nP k n nF j m' : Nat} {tele : List (Expr × BinderMeta)} {idx : List Expr}
    (ht : ∀ d ∈ tele, Expr.NoProjAt T i d.1) (hidx : ∀ e ∈ idx, Expr.NoProjAt T i e) :
    Expr.NoProjAt T i (ConLeche.mutualIhApp recOf rlvls pw nP k n nF j m' tele idx) := by
  unfold ConLeche.mutualIhApp
  refine ConLeche.Expr.NoProjAt.mkLamsOf (ConLeche.Expr.NoProjAt.structTeleAt ht) ?_
  refine ConLeche.Expr.NoProjAt.mkAppN (by simp) ?_
  intro a ha
  simp only [List.mem_append, List.mem_singleton, List.mem_map] at ha
  rcases ha with (ha | ⟨e, he, rfl⟩) | rfl
  · exact noProjAt_mutualRecPrefixAt _ _ _ _ _ a ha
  · exact ConLeche.Expr.NoProjAt.structIdxAt (hidx e he)
  · exact ConLeche.Expr.NoProjAt.mkAppN (by simp) (ConLeche.Expr.NoProjAt.structTeleVars _)

/-- A rule's body mentions no projection the constructor's field
telescopes and index expressions do not. -/
theorem noProjAt_mutualRuleBody {recOf : Nat → Name} {rlvls : List Level} {pw : PropWhen}
    {nP k n nF J : Nat} {recFields : List (Nat × Nat)}
    {teleOf : Nat → List (Expr × BinderMeta)} {idxOf : Nat → List Expr}
    (ht : ∀ q, ∀ d ∈ teleOf q, Expr.NoProjAt T i d.1)
    (hidx : ∀ q, ∀ e ∈ idxOf q, Expr.NoProjAt T i e) :
    Expr.NoProjAt T i
      (ConLeche.mutualRuleBody recOf rlvls pw nP k n nF J recFields teleOf idxOf) := by
  unfold ConLeche.mutualRuleBody
  refine ConLeche.Expr.NoProjAt.mkAppN (by simp) ?_
  intro a ha
  simp only [List.mem_append, List.mem_map] at ha
  rcases ha with ⟨q, -, rfl⟩ | ⟨q, -, rfl⟩
  · simp
  · obtain ⟨qi, qm⟩ := q
    exact noProjAt_mutualIhApp (ht qi) (hidx qi)

/-- A minor premise's `ih` binders mention no projection the field
telescopes and index expressions do not. -/
theorem noProjAt_mutualIhPis {nF o : Nat} {pw : PropWhen}
    {teleOf : Nat → List (Expr × BinderMeta)} {idxOf : Nat → List Expr}
    (ht : ∀ q, ∀ d ∈ teleOf q, Expr.NoProjAt T i d.1)
    (hidx : ∀ q, ∀ e ∈ idxOf q, Expr.NoProjAt T i e) :
    ∀ {is : List (Nat × Nat)} {l : Nat} {body : Expr}, Expr.NoProjAt T i body →
      Expr.NoProjAt T i (ConLeche.mutualIhPis nF o pw teleOf idxOf is l body)
  | [], _, _, hb => hb
  | (q, m') :: is, l, body, hb => by
    simp only [ConLeche.mutualIhPis, ConLeche.Expr.noProjAt_forallE]
    refine ⟨ConLeche.Expr.NoProjAt.mkPisOf (ConLeche.Expr.NoProjAt.structTeleAt (ht q)) ?_,
      noProjAt_mutualIhPis ht hidx hb⟩
    refine ConLeche.Expr.NoProjAt.mkAppN (by simp) ?_
    intro a ha
    simp only [List.mem_append, List.mem_singleton, List.mem_map] at ha
    rcases ha with ⟨e, he, rfl⟩ | rfl
    · exact ConLeche.Expr.NoProjAt.structIdxAt (hidx q e he)
    · exact ConLeche.Expr.NoProjAt.mkAppN (by simp) (ConLeche.Expr.NoProjAt.structTeleVars _)

/-- A minor premise mentions no projection its constructor's type does
not. -/
theorem noProjAt_mutualMinorTy {lps : List Name} {nP o : Nat} {pw : PropWhen}
    {c : MutualCtor4} {mty : Expr}
    (h : ConLeche.mutualMinorTy lps nP o pw c = some mty)
    (hC : Expr.NoProjAt T i c.cty) : Expr.NoProjAt T i mty := by
  unfold ConLeche.mutualMinorTy at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨q, hq, r, hr, hm⟩ := h
  have hcrest : Expr.NoProjAt T i q.2 := ConLeche.Expr.NoProjAt.stripPis nP hq hC
  refine ConLeche.Expr.NoProjAt.replacePisPw c.nF hm hcrest.liftLooseBVars ?_
  refine noProjAt_mutualIhPis (fun _ => ConLeche.Expr.NoProjAt.structFieldTeleOf hC)
    (fun _ => ConLeche.Expr.NoProjAt.structFieldIdxOf hC) ?_
  refine ConLeche.Expr.NoProjAt.liftLooseBVars ?_
  refine ConLeche.Expr.NoProjAt.mkAppN (by simp) ?_
  intro a ha
  simp only [List.mem_append, List.mem_singleton, List.mem_map] at ha
  rcases ha with ⟨e, he, rfl⟩ | rfl
  · exact (ConLeche.Expr.NoProjAt.getAppArgs
      (ConLeche.Expr.NoProjAt.stripPis c.nF hr hcrest) e
      (List.mem_of_mem_drop he)).liftLooseBVars
  · exact ConLeche.Expr.NoProjAt.structCtorSpineAt _ _ _ _ _

/-- The minor premises' `∀`-telescope. -/
theorem noProjAt_mutualMinorsPis {lps : List Name} {nP : Nat} {pw : PropWhen} :
    ∀ {cs : List MutualCtor4} {o : Nat} {body mins : Expr},
      ConLeche.mutualMinorsPis lps nP pw cs o body = some mins →
      (∀ c ∈ cs, Expr.NoProjAt T i c.cty) → Expr.NoProjAt T i body → Expr.NoProjAt T i mins
  | [], _, body, mins, h, _, hb => by rw [mutualMinorsPis_nil h]; exact hb
  | c :: cs, o, body, mins, h, hcs, hb => by
    obtain ⟨mty, rest, hmty, hrest, rfl⟩ := mutualMinorsPis_cons h
    rw [ConLeche.Expr.noProjAt_forallE]
    exact ⟨noProjAt_mutualMinorTy hmty (hcs _ List.mem_cons_self),
      noProjAt_mutualMinorsPis hrest (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')) hb⟩

/-- The minor premises' `λ`-telescope. -/
theorem noProjAt_mutualMinorsLams {lps : List Name} {nP : Nat} {pw : PropWhen} :
    ∀ {cs : List MutualCtor4} {o : Nat} {body mins : Expr},
      ConLeche.mutualMinorsLams lps nP pw cs o body = some mins →
      (∀ c ∈ cs, Expr.NoProjAt T i c.cty) → Expr.NoProjAt T i body → Expr.NoProjAt T i mins
  | [], _, body, mins, h, _, hb => by rw [mutualMinorsLams_nil h]; exact hb
  | c :: cs, o, body, mins, h, hcs, hb => by
    obtain ⟨mty, rest, hmty, hrest, rfl⟩ := mutualMinorsLams_cons h
    rw [ConLeche.Expr.noProjAt_lam]
    exact ⟨noProjAt_mutualMinorTy hmty (hcs _ List.mem_cons_self),
      noProjAt_mutualMinorsLams hrest (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')) hb⟩

/-- A motive's type mentions no projection its member's type does not. -/
theorem noProjAt_mutualMotiveTy {lps : List Name} {nP : Nat} {ℓ : Level} {q : Nat}
    {f : MutualFormer} {mty : Expr}
    (h : ConLeche.mutualMotiveTy lps nP ℓ q f = some mty)
    (hT : Expr.NoProjAt T i f.tty) : Expr.NoProjAt T i mty := by
  unfold ConLeche.mutualMotiveTy at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨r, hr, hm⟩ := h
  refine ConLeche.Expr.NoProjAt.replacePisPw f.nIdx hm
    (ConLeche.Expr.NoProjAt.stripPis nP hr hT).liftLooseBVars ?_
  simp only [ConLeche.Expr.noProjAt_forallE, ConLeche.Expr.noProjAt_sort, and_true]
  exact ConLeche.Expr.NoProjAt.structFamI _ _ _ _ _ _

/-- The motives' `∀`-telescope. -/
theorem noProjAt_mutualMotivesPis {lps : List Name} {nP : Nat} {ℓ : Level} {pw : PropWhen} :
    ∀ {fs : List MutualFormer} {q : Nat} {body mots : Expr},
      ConLeche.mutualMotivesPis lps nP ℓ pw fs q body = some mots →
      (∀ f ∈ fs, Expr.NoProjAt T i f.tty) → Expr.NoProjAt T i body → Expr.NoProjAt T i mots
  | [], _, body, mots, h, _, hb => by rw [mutualMotivesPis_nil h]; exact hb
  | f :: fs, q, body, mots, h, hfs, hb => by
    obtain ⟨mty, rest, hmty, hrest, rfl⟩ := mutualMotivesPis_cons h
    rw [ConLeche.Expr.noProjAt_forallE]
    exact ⟨noProjAt_mutualMotiveTy hmty (hfs _ List.mem_cons_self),
      noProjAt_mutualMotivesPis hrest (fun f' hf' => hfs f' (List.mem_cons_of_mem _ hf')) hb⟩

/-- The motives' `λ`-telescope. -/
theorem noProjAt_mutualMotivesLams {lps : List Name} {nP : Nat} {ℓ : Level} {pw : PropWhen} :
    ∀ {fs : List MutualFormer} {q : Nat} {body mots : Expr},
      ConLeche.mutualMotivesLams lps nP ℓ pw fs q body = some mots →
      (∀ f ∈ fs, Expr.NoProjAt T i f.tty) → Expr.NoProjAt T i body → Expr.NoProjAt T i mots
  | [], _, body, mots, h, _, hb => by rw [mutualMotivesLams_nil h]; exact hb
  | f :: fs, q, body, mots, h, hfs, hb => by
    obtain ⟨mty, rest, hmty, hrest, rfl⟩ := mutualMotivesLams_cons h
    rw [ConLeche.Expr.noProjAt_lam]
    exact ⟨noProjAt_mutualMotiveTy hmty (hfs _ List.mem_cons_self),
      noProjAt_mutualMotivesLams hrest (fun f' hf' => hfs f' (List.mem_cons_of_mem _ hf')) hb⟩

/-- **The generated recursor type of a mutual member has no `.proj`
node** the members' and constructors' types do not have. -/
theorem noProjAt_mutualRecTy {lps : List Name} {elim : Name} {large : Bool} {nP mm : Nat}
    {formers : List MutualFormer} {ctors : List MutualCtor4} {recTy : Expr}
    (h : ConLeche.mutualRecTy lps elim large nP formers ctors mm = some recTy)
    (hT : ∀ f ∈ formers, Expr.NoProjAt T i f.tty)
    (hC : ∀ c ∈ ctors, Expr.NoProjAt T i c.cty) : Expr.NoProjAt T i recTy := by
  obtain ⟨f, f₀, tbs, itele, major, minors, motives, hf, hf₀, hs, hmaj, hmin, hmot, hr⟩ :=
    mutualRecTy_unfold h
  have hTf : Expr.NoProjAt T i f.tty := hT _ (List.mem_of_getElem? hf)
  have hTf₀ : Expr.NoProjAt T i f₀.tty := hT _ (List.mem_of_getElem? hf₀)
  have hI : Expr.NoProjAt T i itele := ConLeche.Expr.NoProjAt.stripPis nP hs hTf
  refine ConLeche.Expr.NoProjAt.replacePisPw nP hr hTf₀ ?_
  refine noProjAt_mutualMotivesPis hmot hT ?_
  refine noProjAt_mutualMinorsPis hmin hC ?_
  refine ConLeche.Expr.NoProjAt.replacePisPw f.nIdx hmaj hI.liftLooseBVars ?_
  simp only [ConLeche.Expr.noProjAt_forallE]
  refine ⟨ConLeche.Expr.NoProjAt.structFamI _ _ _ _ _ _,
    ConLeche.Expr.NoProjAt.mkAppN (by simp) ?_⟩
  intro a ha
  rcases List.mem_append.mp ha with h' | h'
  · exact ConLeche.Expr.NoProjAt.structPsAt _ _ a h'
  · rcases List.mem_singleton.mp h' with rfl; simp

/-- **The generated rules of a mutual block have no `.proj` node** the
members' and constructors' types do not have. -/
theorem noProjAt_mutualRecRhs {lps : List Name} {elim : Name} {large : Bool} {nP J : Nat}
    {formers : List MutualFormer} {ctors : List MutualCtor4}
    {recOf : Nat → Name} {rlvls : List Level} {rhs : Expr}
    (h : ConLeche.mutualRecRhs lps elim large nP formers ctors recOf rlvls J = some rhs)
    (hT : ∀ f ∈ formers, Expr.NoProjAt T i f.tty)
    (hC : ∀ c ∈ ctors, Expr.NoProjAt T i c.cty) : Expr.NoProjAt T i rhs := by
  obtain ⟨c, f₀, cbs, crest0, inner, minors, motives, hJc, hf0, hsC, hinner, hmin, hmot, hr⟩ :=
    mutualRecRhs_unfold h
  have hcty : Expr.NoProjAt T i c.cty := hC _ (List.mem_of_getElem? hJc)
  have hTf₀ : Expr.NoProjAt T i f₀.tty := hT _ (List.mem_of_getElem? hf0)
  have hcrest : Expr.NoProjAt T i crest0 := ConLeche.Expr.NoProjAt.stripPis nP hsC hcty
  have hinnerP : Expr.NoProjAt T i inner :=
    ConLeche.Expr.NoProjAt.pisToLamsPw c.nF hinner hcrest.liftLooseBVars
      (noProjAt_mutualRuleBody (fun _ => ConLeche.Expr.NoProjAt.structFieldTeleOf hcty)
        (fun _ => ConLeche.Expr.NoProjAt.structFieldIdxOf hcty))
  refine ConLeche.Expr.NoProjAt.pisToLamsPw nP hr hTf₀ ?_
  exact noProjAt_mutualMotivesLams hmot hT (noProjAt_mutualMinorsLams hmin hC hinnerP)

end NoProj

/-! ## The generators' data, read off `mutualGenData` -/

/-- A member of a `zipWith` is its function at members of the two
lists. -/
theorem mem_zipWith_of {α β γ : Type} {g : α → β → γ} :
    ∀ {l₁ : List α} {l₂ : List β} {c : γ}, c ∈ List.zipWith g l₁ l₂ →
      ∃ a ∈ l₁, ∃ b ∈ l₂, c = g a b
  | [], _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: as, b :: bs, c, h => by
    simp only [List.zipWith_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨a, List.mem_cons_self, b, List.mem_cons_self, rfl⟩
    · obtain ⟨a', ha', b', hb', rfl⟩ := mem_zipWith_of h
      exact ⟨a', List.mem_cons_of_mem _ ha', b', List.mem_cons_of_mem _ hb', rfl⟩

/-- The generated formers' types are the checked members' types. -/
theorem mutualGenData_formers {b : MutualBlock} {fms : List MutualFormerA}
    {ctorsA : List (ConstantVal × Nat)} {kinds : List (List (RecFieldKind × Nat))}
    {formers4 : List MutualFormer} {ctors4 : List MutualCtor4}
    (hgd : ConLeche.mutualGenData b fms ctorsA kinds = (formers4, ctors4))
    {f : MutualFormer} (hf : f ∈ formers4) :
    ∃ f' ∈ fms, f.tty = f'.cvTa.type := by
  simp only [ConLeche.mutualGenData, Prod.mk.injEq] at hgd
  obtain ⟨rfl, -⟩ := hgd
  obtain ⟨f', hf', rfl⟩ := List.mem_map.mp hf
  exact ⟨f', hf', rfl⟩

/-- The generated constructors' types are the annotated constructors'
types. -/
theorem mutualGenData_ctors {b : MutualBlock} {fms : List MutualFormerA}
    {ctorsA : List (ConstantVal × Nat)} {kinds : List (List (RecFieldKind × Nat))}
    {formers4 : List MutualFormer} {ctors4 : List MutualCtor4}
    (hgd : ConLeche.mutualGenData b fms ctorsA kinds = (formers4, ctors4))
    {c : MutualCtor4} (hc : c ∈ ctors4) :
    ∃ cA ∈ ctorsA, c.cty = cA.1.type := by
  simp only [ConLeche.mutualGenData, Prod.mk.injEq] at hgd
  obtain ⟨-, rfl⟩ := hgd
  obtain ⟨p, hp, ks, -, rfl⟩ := mem_zipWith_of hc
  exact ⟨p.2, (List.of_mem_zip hp).2, rfl⟩

/-! ## The members' and constructors' names -/

/-- The formers' stage, positionally, with everything the name and
`.proj` bookkeeping reads off it: the member's name is the declared
one's, it is fresh, unreserved and not a projection function's, and
its checked type resolves at the PRE-BLOCK environment. -/
theorem mutualFormers_nameFacts {μ : CheckMode} {F : Nat} {env : Env} {b : MutualBlock}
    {fms : List MutualFormerA}
    (hformers : ConLeche.mutualFormers (m := ConLeche.CheckM) (fueledOps μ F) b.nP b.formers env
      = .ok (ConLeche.consMutualFormers fms env, fms)) :
    fms.length = b.formers.length ∧
    ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      b.formers[t]? = some ((b.formers.getD t default).1, f.nIdx) ∧
      (b.formers.getD t default).1.name = f.cvTa.name ∧
      env.find? f.cvTa.name = none ∧ f.cvTa.name.isProjFnShape = false ∧
      ConLeche.reservedBasisNames.contains f.cvTa.name = false ∧
      f.cvTa.type.constsResolve env = true := by
  obtain ⟨hlen, hpos⟩ := mutualFormerChecks_pos (ConLeche.mutualFormers_inv hformers).1
  refine ⟨hlen, ?_⟩
  intro t f hf
  obtain ⟨cvD, cvC, -, hl, hccv, hnm, -, -⟩ := hpos t f hf
  obtain ⟨hfind, hres, hproj, -, -, -, ty, -, -, -, -, htr, -, -, hty⟩ :=
    ConLeche.checkConstantVal_inv hccv
  have hname : f.cvTa.name = cvC.name := by rw [hty]
  have hD : (b.formers.getD t default).1 = cvD := by
    rw [List.getD_eq_getElem?_getD, hl]; rfl
  have hnameD : (b.formers.getD t default).1.name = f.cvTa.name := by
    rw [hD, hname, hnm]
  refine ⟨by rw [hD]; exact hl, hnameD, ?_, ?_, ?_, ?_⟩
  · rw [hname]; exact hfind
  · rw [hname]; exact hproj
  · rw [hname]; exact hres
  · rw [show f.cvTa.type = ty from by rw [hty]]; exact htr

/-- The members' names: fresh before the block, not a projection function's, unreserved,
and the block's recursor name at the member is the member's `.rec`. -/
theorem mutualMemberNames {μ : CheckMode} {F : Nat} {env : Env} {b : MutualBlock}
    {fms : List MutualFormerA}
    (hformers : ConLeche.mutualFormers (m := ConLeche.CheckM) (fueledOps μ F) b.nP b.formers env
      = .ok (ConLeche.consMutualFormers fms env, fms)) :
    ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      env.find? f.cvTa.name = none ∧ f.cvTa.name.isProjFnShape = false ∧
      ConLeche.reservedBasisNames.contains f.cvTa.name = false ∧
      b.recName t = f.cvTa.name.str "rec" := by
  intro t f hf
  obtain ⟨-, hpos⟩ := mutualFormers_nameFacts hformers
  obtain ⟨-, hnameD, hfind, hproj, hres, -⟩ := hpos t f hf
  exact ⟨hfind, hproj, hres, by simp only [ConLeche.MutualBlock.recName, hnameD]⟩

/-- **The members' names, as a list**: the checked formers' names are
the block record's `memberNames`, positionally. -/
theorem mutualMemberNames_eq {μ : CheckMode} {F : Nat} {env : Env} {b : MutualBlock}
    {fms : List MutualFormerA}
    (hformers : ConLeche.mutualFormers (m := ConLeche.CheckM) (fueledOps μ F) b.nP b.formers env
      = .ok (ConLeche.consMutualFormers fms env, fms)) :
    fms.map (·.cvTa.name) = b.memberNames := by
  obtain ⟨hlen, hpos⟩ := mutualFormers_nameFacts hformers
  refine List.ext_getElem? fun t => ?_
  simp only [ConLeche.MutualBlock.memberNames, List.getElem?_map]
  cases hf : fms[t]? with
  | none =>
    have ht : fms.length ≤ t := by
      rw [List.getElem?_eq_none_iff] at hf; exact hf
    rw [List.getElem?_eq_none (by omega)]
    rfl
  | some f =>
    obtain ⟨hl, hnameD, -, -, -, -⟩ := hpos t f hf
    rw [hl]
    simp only [Option.map_some]
    exact congrArg some hnameD.symm

/-- The constructors' names: not a projection function's, unreserved. -/
theorem mutualCtorNames {μ : CheckMode} {F : Nat} {env : Env} {b : MutualBlock}
    {fms : List MutualFormerA} {isProp : Bool} {ctorsA : List (ConstantVal × Nat)}
    {sortss : List (List Level)}
    (hctors : ConLeche.checkMutualCtors (m := ConLeche.CheckM) (fueledOps μ F) env b fms isProp
      b.ctors = .ok (ctorsA, sortss)) :
    ∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA →
      cA.1.name.isProjFnShape = false ∧ ConLeche.reservedBasisNames.contains cA.1.name = false := by
  intro J cA hJ
  obtain ⟨hlen, -, hall⟩ := ConLeche.checkMutualCtors_inv hctors
  have hJlt : J < b.ctors.length := by
    rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hJ).1
  obtain ⟨-, sorts, -, hrun⟩ := hall J _ cA (List.getElem?_eq_getElem hJlt) hJ
  obtain ⟨⟨ty', hccv⟩, -, -⟩ := ConLeche.checkMutualCtor_shape hrun
  obtain ⟨-, hres, hproj, -, -, -, ty, -, -, -, -, -, -, -, hty⟩ :=
    ConLeche.checkConstantVal_inv hccv
  have hname : cA.1.name = b.ctors[J].cv.name := by rw [hty]
  exact ⟨by rw [hname]; exact hproj, by rw [hname]; exact hres⟩

/-! ## The block's `.proj` bookkeeping -/

/-- **No stored piece mentions a member's projections** at the recursors' environment. -/
theorem mutualNoProj {μ : CheckMode} {F : Nat} {env : Env} (hwf : ConLeche.EnvWF env)
    (hproj : ConLeche.ProjOkT env) {b : MutualBlock}
    {streamRecs : Option (List (ConstantVal × List RecRule))} {fms : List MutualFormerA}
    {f₀ : MutualFormerA} {ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)}
    {kinds : List (List (RecFieldKind × Nat))} {formers4 : List MutualFormer}
    {ctors4 : List MutualCtor4} {cvRas : List ConstantVal}
    {rulesOf : List (List (MutualCtor × Expr))}
    (hformers : ConLeche.mutualFormers (m := ConLeche.CheckM) (fueledOps μ F) b.nP b.formers env
      = .ok (ConLeche.consMutualFormers fms env, fms))
    (hctors : ConLeche.checkMutualCtors (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.consMutualFormers fms env) b fms (Level.isEquiv f₀.s .zero == some true) b.ctors
      = .ok (ctorsA, sortss))
    (hgd : ConLeche.mutualGenData b fms ctorsA kinds = (formers4, ctors4))
    (hrectys : ConLeche.checkMutualRecTys (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env)) b formers4 ctors4
      streamRecs b.k = .ok cvRas)
    (hrules : ConLeche.checkMutualAllRules (m := ConLeche.CheckM)
      (ConLeche.provisionMutualRecs b fms cvRas.zipIdx
        (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env)))
      b formers4 ctors4 streamRecs b.k = .ok rulesOf) :
    ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f → ∀ j : Nat,
      NoProjEnv (ConLeche.storeMutualRecs
        (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env)) b fms rulesOf
        cvRas.zipIdx (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env)))
        f.cvTa.name j := by
  intro t f hft j
  obtain ⟨-, hposF⟩ := mutualFormers_nameFacts hformers
  have hfresh : env.find? f.cvTa.name = none := (hposF t f hft).2.2.1
  -- the members' types resolve at the pre-block environment
  have hnpT : ∀ f' ∈ fms, Expr.NoProjAt f.cvTa.name j f'.cvTa.type := by
    intro f' hf'
    obtain ⟨t', hf''⟩ := List.getElem?_of_mem hf'
    exact ConLeche.Expr.noProjAt_of_constsResolve hfresh _ (hposF t' f' hf'').2.2.2.2.2
  have h0 : NoProjEnv env f.cvTa.name j := noProjEnv_of_fresh hwf hfresh j
  have h1 : NoProjEnv (ConLeche.consMutualFormers fms env) f.cvTa.name j :=
    noProjEnv_consMutualFormers h0 hnpT
  -- the member's slot is still empty at the formers' environment
  have hslot : (ConLeche.consMutualFormers fms env).findProj? f.cvTa.name j = none :=
    findProj?_none_consMutualFormers (findProj?_none_of_indFresh hproj hfresh j)
  -- the constructors' types are annotated there
  have hnpC : ∀ cA ∈ ctorsA, Expr.NoProjAt f.cvTa.name j cA.1.type := by
    intro cA hcA
    obtain ⟨J, hJ⟩ := List.getElem?_of_mem hcA
    obtain ⟨hlenC, -, hallC⟩ := ConLeche.checkMutualCtors_inv hctors
    have hJlt : J < b.ctors.length := by
      rw [← hlenC]; exact (List.getElem?_eq_some_iff.mp hJ).1
    obtain ⟨-, sorts, -, hrun⟩ := hallC J _ cA (List.getElem?_eq_getElem hJlt) hJ
    obtain ⟨⟨ty', hccv⟩, -, -⟩ := ConLeche.checkMutualCtor_shape hrun
    obtain ⟨-, -, -, -, -, hnfv, ty, -, -, hann, -, -, -, -, hty⟩ :=
      ConLeche.checkConstantVal_inv hccv
    rw [show cA.1.type = ty from by rw [hty]]
    exact ConLeche.annotateCore_noProjAt μ hann hnfv hslot
  have h2 : NoProjEnv (ConLeche.consMutualCtors b.nP ctorsA
      (ConLeche.consMutualFormers fms env)) f.cvTa.name j :=
    noProjEnv_consMutualCtors h1 hnpC
  -- the generators' data
  have hnpF4 : ∀ f' ∈ formers4, Expr.NoProjAt f.cvTa.name j f'.tty := by
    intro f' hf'
    obtain ⟨f'', hf'', hty⟩ := mutualGenData_formers hgd hf'
    rw [hty]; exact hnpT f'' hf''
  have hnpC4 : ∀ c' ∈ ctors4, Expr.NoProjAt f.cvTa.name j c'.cty := by
    intro c' hc'
    obtain ⟨cA, hcA, hty⟩ := mutualGenData_ctors hgd hc'
    rw [hty]; exact hnpC cA hcA
  -- the recursors' store
  obtain ⟨hlenR, hallR⟩ := ConLeche.checkMutualRecTys_inv hrectys
  obtain ⟨hlenU, hallU⟩ := ConLeche.checkMutualAllRules_inv hrules
  refine noProjEnv_storeMutualRecs h2 fun x hx => ?_
  have hget : cvRas[x.2]? = some x.1 :=
    List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using hx)
  have hlt : x.2 < b.k := by
    have h := (List.getElem?_eq_some_iff.mp hget).1
    rw [hlenR] at h; exact h
  obtain ⟨cvRa, hget', hrun⟩ := hallR x.2 hlt
  obtain rfl : cvRa = x.1 := by rw [hget'] at hget; exact Option.some.inj hget
  obtain ⟨recTy, sty, u, hgenR, -, -, -, -, -, -, -, hcv⟩ :=
    ConLeche.checkMutualRecTy_shape hrun
  have htype : x.1.type = recTy := by rw [hcv]
  refine ⟨by rw [htype]; exact noProjAt_mutualRecTy hgenR hnpF4 hnpC4, ?_⟩
  intro r hr
  obtain ⟨⟨p, hp, hrhs⟩, -⟩ := mutualRules_shape hr
  rw [hrhs]
  obtain ⟨rules, hgetR, hrunU⟩ := hallU x.2 hlt
  have hd : rulesOf.getD x.2 [] = rules := by
    rw [List.getD_eq_getElem?_getD, hgetR]; rfl
  rw [hd] at hp
  obtain ⟨-, hlenRules, hallRules⟩ := ConLeche.checkMutualMemberRules_inv hrunU
  obtain ⟨n, hn⟩ := List.getElem?_of_mem hp
  have hnlt : n < (b.ownCtors x.2).length := by
    rw [← hlenRules]; exact (List.getElem?_eq_some_iff.mp hn).1
  obtain ⟨J, c, rhs', -, hgetn, hgen, -, -, -, -⟩ := hallRules n hnlt
  obtain rfl : p = (c, rhs') := by rw [hn] at hgetn; exact Option.some.inj hgetn
  exact noProjAt_mutualRecRhs hgen hnpF4 hnpC4

end ConLeche.Model
