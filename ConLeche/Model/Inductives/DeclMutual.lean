module

public import ConLeche.Model.Inductives.MutualStageFormer
public import ConLeche.Model.Inductives.MutualStageCtor
public import ConLeche.Model.Inductives.MutualStageRec
public import ConLeche.Model.Inductives.MutualStageTable
public import ConLeche.Model.Inductives.MutualRuleOk
public import ConLeche.Model.Inductives.MutualRuleRead
public import ConLeche.Model.Inductives.MutualRecPre2
public import ConLeche.Semantics.Inductives.DeclMutual
import ConLeche.Verify.Inductives.MutualInv
public section

/-!
# The mutual install, assembled (task #278, M2.5f)

`declMutual`: the P carrier survives the mutual install's run
(`DeclMutualRun`).  The stages are `DeclNative.lean`'s twins —
`stageMutualFormers` (the `k` members' conses, member `t`'s leaf the
fibre `mutualTyAVI … t` of the ONE auxiliary family), the constructor
loop (`stageMutualCtors`, constructor `J` at its GLOBAL block
position), `stageMutualRecs` (the `k` recursors, provisioned rule-less
and stored as a group) and `stageMutualTables` (the structure-like
members' projection tables).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps
  MutualParts MutualBlock MutualFormerA MutualFormer MutualCtor MutualCtor4 BinderMeta RecRule)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## The representation clause's obligations -/

/-- **The #280 representation-clause obligations the mutual recursor
stage leaves open** — exactly `stageMutualRecsProvision`'s `hreps` (a
rule-less recursor cons claims its block's representation) and
`stageMutualRecsStore`'s `hreps` (the group store keeps the clause
across the swap), stated about the block's data alone.

The clause as `inductives` carries it (`IndRep`) is SINGLE-FAMILY —
its major index is `nP + 1 + n + nIdx`, one motive — so a mutual
member's recursor cannot satisfy it; the member view (`k` motives,
member `m`'s own rules, the leaf at the tagged tuple) is its own task,
and until it lands this is `declMutual`'s one hypothesis. -/
@[expose] def MutualRepsOk (V : Type w) [SetTheory V] (μ : CheckMode) (b : MutualBlock) : Prop :=
  ∀ (fms : List MutualFormerA) (cvRas : List ConstantVal)
    (rulesOf : List (List (MutualCtor × Expr))) (env₂ : Env) (mp₂ : EnvModelM V μ env₂)
    (prts : MutualRecParts) (env₀ : Env) (m₀ : EnvModel V env₀),
    prts.LeafHyp V m₀ → cvRas.length = prts.k → prts.nP = b.nP → prts.n = b.n →
    -- (i) the provision: member `t`'s recursor, consed RULE-LESS
    (∀ (env' : Env) (mp' : EnvModelM V μ env') (t : Nat), t < prts.k →
      env'.find? (cvRas.getD t default).name = none →
      ∀ m₂ : EnvModel V ⟨.recInfo (cvRas.getD t default)
          (b.rulePrefix + (fms.getD t default).nIdx) b.rulePrefix [] :: env'.consts⟩,
        m₂.acval = acvalWith mp'.base2.acval (cvRas.getD t default).name (prts.leaf m₀ t) →
        IndRepsHead env' (.recInfo (cvRas.getD t default)
          (b.rulePrefix + (fms.getD t default).nIdx) b.rulePrefix []) m₂) ∧
    -- (ii) the swap: the `k` recursors stored as a group
    (∀ (acv : Name → (Name → Nat) → AnnotTerm),
      (∀ t, t < prts.k → ∀ ψ : Name → Nat,
        acv (cvRas.getD t default).name ψ = prts.leaf m₀ t ψ) →
      (∀ n : Name, (∀ t, t < prts.k → n ≠ (cvRas.getD t default).name) →
        acv n = mp₂.base2.acval n) →
      ∀ m₃ : EnvModel V (ConLeche.storeMutualRecs env₂ b fms rulesOf cvRas.zipIdx env₂),
        m₃.acval = acv → IndReps m₃)

/-! ## Kit: the formers' conses and their checks, positionally -/

/-- A lookup past the formers' conses of other names. -/
theorem consMutualFormers_find?_of_ne :
    ∀ {fms : List MutualFormerA} {env : Env} {n : Name},
      (∀ g ∈ fms, g.cvTa.name ≠ n) →
      (ConLeche.consMutualFormers fms env).find? n = env.find? n
  | [], _, _, _ => rfl
  | g :: gs, env, n, hne => by
    show (ConLeche.consMutualFormers gs ⟨.indInfo g.cvTa {} :: env.consts⟩).find? n = _
    rw [consMutualFormers_find?_of_ne (fun x hx => hne x (List.mem_cons_of_mem _ hx))]
    exact find?_cons_of_name_ne (c := .indInfo g.cvTa {}) (hne g List.mem_cons_self)

/-- **Every consed former is found at its own name** with the block's
empty capability record. -/
theorem consMutualFormers_find?_self :
    ∀ {fms : List MutualFormerA} {env : Env} {f : MutualFormerA},
      f ∈ fms → (fms.map (·.cvTa.name)).Nodup →
      (ConLeche.consMutualFormers fms env).find? f.cvTa.name = some (.indInfo f.cvTa {})
  | [], _, _, hf, _ => nomatch hf
  | g :: gs, env, f, hf, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hf with rfl | hf'
    · show (ConLeche.consMutualFormers gs
        ⟨.indInfo f.cvTa {} :: env.consts⟩).find? f.cvTa.name = _
      rw [consMutualFormers_find?_of_ne (fun x hx hh => hnd.1 (by
        rw [← hh]; exact List.mem_map_of_mem hx))]
      exact ConLeche.Env.find?_cons_self _ _
    · show (ConLeche.consMutualFormers gs
        ⟨.indInfo g.cvTa {} :: env.consts⟩).find? f.cvTa.name = _
      exact consMutualFormers_find?_self hf' hnd.2

/-- **The formers' checks, positionally**: the `t`-th checked former is
the `t`-th declared one's constant check at the PRE-BLOCK environment
(its name and level parameters the declared constant's), and its
annotated type is the telescope ending in its result sort. -/
theorem mutualFormerChecks_pos {F nP : Nat} :
    ∀ {l : List (ConstantVal × Nat)} {env : Env} {fms : List MutualFormerA},
      ConLeche.mutualFormerChecks (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env nP l
        = .ok fms →
      fms.length = l.length ∧
      ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
        ∃ (cv cv' : ConstantVal) (bs : List (Expr × BinderMeta)),
          l[t]? = some (cv, f.nIdx) ∧
          ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env cv' = .ok f.cvTa ∧
          cv'.name = cv.name ∧ cv'.levelParams = cv.levelParams ∧
          f.cvTa.type.stripPis (nP + f.nIdx) = some (bs, .sort f.s)
  | [], _, _, h => by
    obtain rfl := ConLeche.mutualFormerChecks_nil_inv h
    exact ⟨rfl, fun t f hf => nomatch hf⟩
  | (cv, nIdx) :: rest, env, fms, h => by
    obtain ⟨cvTa₀, cvTa, s, bs, fs, hccv₀, htele, hstrip, hrest, rfl⟩ :=
      ConLeche.mutualFormerChecks_inv h
    obtain ⟨hlen, hall⟩ := mutualFormerChecks_pos hrest
    refine ⟨by simp [hlen], ?_⟩
    intro t f hf
    cases t with
    | zero =>
      obtain rfl := Option.some.inj hf
      rcases ConLeche.checkSumTele_shape htele with ⟨rfl, -⟩ | ⟨ty, hccv⟩
      · exact ⟨cv, cv, bs, rfl, hccv₀, rfl, rfl, hstrip⟩
      · exact ⟨cv, { cv with type := ty }, bs, rfl, hccv, rfl, rfl, hstrip⟩
    | succ t =>
      simp only [List.getElem?_cons_succ] at hf ⊢
      exact hall t f hf

/-- **The cross-member checks, at every member**: the result sort is
the first former's and the parameter domains are compared there. -/
theorem mutualCrossChecks_all {F nP : Nat} {env : Env} {f₀ : MutualFormerA}
    {doms₀ : List Expr} :
    ∀ {l : List MutualFormerA},
      ConLeche.mutualCrossChecks (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env nP f₀ doms₀ l
        = .ok () →
      ∀ f ∈ l, Level.isEquiv f.s f₀.s = some true ∧
        ∃ tq : List Expr × Expr, ConLeche.openPisAtFvars nP f.cvTa.type 0 = some tq ∧
          ConLeche.mutualDomsOk (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env tq.1 doms₀ nP
            = .ok ()
  | [], _, f, hf => nomatch hf
  | g :: gs, h, f, hf => by
    obtain ⟨heq, tq, htq, hdoms, hrest⟩ := ConLeche.mutualCrossChecks_inv h
    rcases List.mem_cons.mp hf with rfl | hf'
    · exact ⟨heq, tq, htq, hdoms⟩
    · exact mutualCrossChecks_all hrest f hf'

/-- The former's data at a level the result sort evaluates like. -/
theorem FormerData.congr_sort {env : Env} {m : EnvModel V env} {cvT : ConstantVal} {nP : Nat}
    {s s' : Level} {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {lvls : (Name → Nat) → List Nat}
    (h : FormerData m cvT nP s pps lvls) (hs : ∀ ψ : Name → Nat, s.eval ψ = s'.eval ψ) :
    FormerData m cvT nP s' pps lvls where
  read ψ := by rw [← hs ψ]; exact h.read ψ
  len := h.len
  bits := h.bits
  okTy ψ ρ := by rw [← hs ψ]; exact h.okTy ψ ρ
  below := h.below
  params ψ₁ ψ₂ hφ := ⟨(h.params ψ₁ ψ₂ hφ).1, by rw [← hs ψ₁, ← hs ψ₂]; exact (h.params ψ₁ ψ₂ hφ).2⟩
  lvlsLen := h.lvlsLen
  lvl := h.lvl
  lvlsParams := h.lvlsParams

/-! ## Kit: the block's member table -/

/-- The members, by position, with an offset. -/
theorem members3_find?_go :
    ∀ (l : List (ConstantVal × Nat)) (o t : Nat), o ≤ t → t < o + l.length →
      ((l.zipIdx o).map fun q => (q.1.1.name, q.2, q.1.2)).find? (fun x => x.2.1 == t)
        = some ((l.getD (t - o) default).1.name, t, (l.getD (t - o) default).2)
  | [], o, t, h1, h2 => by simp at h2; omega
  | a :: l, o, t, h1, h2 => by
    rw [List.zipIdx_cons, List.map_cons, List.find?_cons]
    split
    · next hb =>
      have hot : o = t := by simpa using hb
      subst hot
      simp
    · next hb =>
      have hne : ¬ o = t := by simpa using hb
      have hlt : o + 1 ≤ t := by omega
      rw [members3_find?_go l (o + 1) t hlt (by simp at h2 ⊢; omega)]
      have ht : t - o = (t - (o + 1)) + 1 := by omega
      rw [ht]
      simp

/-- **The block's member table, positionally**. -/
theorem members3_find? {b : MutualBlock} {t : Nat} (ht : t < b.k) :
    b.members3.find? (fun x => x.2.1 == t)
      = some ((b.formers.getD t default).1.name, t, (b.formers.getD t default).2) := by
  have h := members3_find?_go b.formers 0 t (Nat.zero_le _)
    (by simpa [ConLeche.MutualBlock.k] using ht)
  simp only [Nat.sub_zero] at h
  simpa [ConLeche.MutualBlock.members3] using h

theorem mutualNameOf_members3 {b : MutualBlock} {t : Nat} (ht : t < b.k) :
    mutualNameOf b.members3 t = (b.formers.getD t default).1.name := by
  unfold mutualNameOf
  rw [members3_find? ht]
  rfl

theorem mutualNIdxOf_members3 {b : MutualBlock} {t : Nat} (ht : t < b.k) :
    mutualNIdxOf b.members3 t = (b.formers.getD t default).2 := by
  unfold mutualNIdxOf
  rw [members3_find? ht]
  rfl

/-- Official's positivity walk names a MEMBER of the block, or nothing. -/
theorem mutualPositivity_tgt (members : List (Name × Nat × Nat)) (lps : List Name) (nP o : Nat) :
    ∀ (e : Expr) (kk : Nat),
      (ConLeche.mutualPositivity members lps nP o e kk).2 = 0 ∨
        ∃ x ∈ members, x.2.1 = (ConLeche.mutualPositivity members lps nP o e kk).2 := by
  intro e
  induction e with
  | forallE d b bm ihd ihb =>
    intro kk
    rw [ConLeche.mutualPositivity]
    split
    · exact Or.inl rfl
    · exact ihb (kk + 1)
  | _ =>
    intro kk
    rw [ConLeche.mutualPositivity]
    · split
      · exact Or.inl rfl
      · split <;> try exact Or.inl rfl
        split <;> try exact Or.inl rfl
        split <;> try exact Or.inl rfl
        rename_i _ _ _ _ _ _ _ _ hq _
        exact Or.inr ⟨_, List.mem_of_find?_eq_some hq, rfl⟩
    · intro d' b' bm' hh
      exact Expr.noConfusion hh

/-- **A classified field's target is a MEMBER of the block** (or the
harmless `0`): the classification's only source of a target is
official's positivity walk, and that walk reads the member table. -/
theorem mutualCtorKinds_tgt {members : List (Name × Nat × Nat)} {lps : List Name} {nP : Nat}
    {c : ConstantVal × Nat} {ks : List (RecFieldKind × Nat)}
    (h : ConLeche.mutualCtorKinds members lps nP c = some ks) :
    ∀ i, tgtAt ks i = 0 ∨ ∃ x ∈ members, x.2.1 = tgtAt ks i := by
  unfold ConLeche.mutualCtorKinds at h
  split at h
  · next cbs cbody hst =>
    split at h
    · obtain rfl := Option.some.inj h
      intro i
      simp only [tgtAt]
      by_cases hi : i < c.2
      · rw [List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_getElem (by simpa using hi)]
        simp only [List.getElem_range, Option.map_some, Option.getD_some]
        split
        · exact Or.inl rfl
        · rcases hpos : ConLeche.mutualPositivity members lps nP i
            ((cbs.getD (nP + i) default).1) 0 with ⟨kind, m'⟩
          have hm := mutualPositivity_tgt members lps nP i ((cbs.getD (nP + i) default).1) 0
          rw [hpos] at hm
          cases kind
          · exact hm
          · show (if ConLeche.structUsedLater c.1.type nP i = true then
                  (RecFieldKind.unsupported, 0) else (RecFieldKind.recursive, m')).2 = 0 ∨
              ∃ x ∈ members, x.2.1 = (if ConLeche.structUsedLater c.1.type nP i = true then
                  (RecFieldKind.unsupported, 0) else (RecFieldKind.recursive, m')).2
            split
            · exact Or.inl rfl
            · exact hm
          · show (if ConLeche.structUsedLater c.1.type nP i = true then
                  (RecFieldKind.unsupported, 0) else (RecFieldKind.reflexive, m')).2 = 0 ∨
              ∃ x ∈ members, x.2.1 = (if ConLeche.structUsedLater c.1.type nP i = true then
                  (RecFieldKind.unsupported, 0) else (RecFieldKind.reflexive, m')).2
            split
            · exact Or.inl rfl
            · exact hm
          · exact hm
          · exact hm
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hi)]
        exact Or.inl rfl
    · obtain rfl := Option.some.inj h
      intro i
      simp only [tgtAt]
      by_cases hi : i < c.2
      · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_map,
          List.getElem?_eq_getElem (by simpa using hi)]
        exact Or.inl rfl
      · rw [List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hi)]
        exact Or.inl rfl
  · exact nomatch h

end ConLeche.Model
