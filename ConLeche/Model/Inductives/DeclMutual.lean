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

/-- A successful `mapM` in `Option`, positionally. -/
theorem mapM_option_getElem? {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r →
      ∀ (i : Nat) (a : α), l[i]? = some a → ∃ b, r[i]? = some b ∧ f a = some b
  | [], r, h, i, a, ha => by simp at ha
  | a₀ :: l, r, h, i, a, ha => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨b₀, hb₀, bs, hbs, rfl⟩ := h
    cases i with
    | zero =>
      obtain rfl := Option.some.inj ha
      exact ⟨b₀, rfl, hb₀⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at ha ⊢
      exact mapM_option_getElem? hbs i a ha

/-- **The kinds re-checked on the annotated constructors**, inverted. -/
theorem mutualFieldsOk_inv {env₀ : Env} {members : List (Name × Nat × Nat)} {lps : List Name}
    {nP : Nat} {ctorsA : List (ConstantVal × Nat)} {kinds : List (List (RecFieldKind × Nat))}
    (h : ConLeche.mutualFieldsOk env₀ members lps nP ctorsA kinds = true) :
    ctorsA.length = kinds.length ∧
    ∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA →
      ∃ ks : List (RecFieldKind × Nat), kinds[J]? = some ks ∧ ks.length = cA.2 ∧
        ConLeche.mutualOpenedOk env₀ members lps nP cA.1.type cA.2 ks = true := by
  unfold ConLeche.mutualFieldsOk at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hlen, hall⟩ := h
  refine ⟨hlen, fun J cA hJ => ?_⟩
  have hJl : J < ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
  have hthis := hall J hJl
  rw [hJ] at hthis
  cases hk : kinds[J]? with
  | none => rw [hk] at hthis; exact nomatch hthis
  | some ks =>
    rw [hk] at hthis
    simp only [Bool.and_eq_true, beq_iff_eq] at hthis
    exact ⟨ks, rfl, hthis.1, hthis.2⟩

/-! ## Kit: the formers' conses as an extension the readings cross -/

/-- **The formers' conses, as an environment extension**: every stored
lookup survives, the literal guards only grow, and no projection table
appears. -/
theorem consMutualFormers_extend :
    ∀ {fms : List MutualFormerA} {env : Env},
      (∀ f ∈ fms, env.find? f.cvTa.name = none) →
      (fms.map (·.cvTa.name)).Nodup →
      FindPreserved env (ConLeche.consMutualFormers fms env) ∧
      LitGuardsMono env (ConLeche.consMutualFormers fms env) ∧
      (∀ (sn : Name) (i : Nat), env.findProj? sn i = none →
        (ConLeche.consMutualFormers fms env).findProj? sn i = none)
  | [], _, _, _ => ⟨fun h => h, ⟨fun h => h, fun h => h⟩, fun _ _ h => h⟩
  | f :: fs, env, hfresh, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have hf : env.find? f.cvTa.name = none := hfresh f List.mem_cons_self
    have hfresh' : ∀ g ∈ fs,
        (Env.mk (ConstantInfo.indInfo f.cvTa {} :: env.consts)).find? g.cvTa.name = none := by
      intro g hg
      refine (find?_cons_of_name_ne (c := .indInfo f.cvTa {}) (fun hh => ?_)).trans
        (hfresh g (List.mem_cons_of_mem _ hg))
      refine hnd.1 ?_
      have : f.cvTa.name = g.cvTa.name := hh
      rw [this]
      exact List.mem_map_of_mem hg
    obtain ⟨hF, hL, hP⟩ := consMutualFormers_extend hfresh' hnd.2
    refine ⟨fun h => hF (findPreserved_cons hf h), ⟨fun h => hL.1 ((litGuardsMono_cons hf).1 h),
      fun h => hL.2 ((litGuardsMono_cons hf).2 h)⟩, fun sn i h => hP sn i ?_⟩
    exact ConLeche.Verify.findProj?_cons_of_base_none
      (c₀ := .indInfo f.cvTa {}) (fun _ hh => nomatch hh) sn i h

/-- The former's data crosses the whole formers' loop: its type
resolves before the block, so neither the new constants nor the new
leaves are read. -/
theorem FormerData.crossEnv {env env' : Env} {m : EnvModel V env} {m' : EnvModel V env'}
    {cvT : ConstantVal} {nP : Nat} {resSort : Level}
    {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {lvls : (Name → Nat) → List Nat}
    (h : FormerData m cvT nP resSort pps lvls)
    (hcb : ConstsBound env cvT.type)
    (hF : FindPreserved env env') (hG : LitGuardsMono env env')
    (hproj : ∀ (sn : Name) (i : Nat), env.findProj? sn i = none → env'.findProj? sn i = none)
    (hag : ∀ n : Name, (env.find? n).isSome = true → m.acval n = m'.acval n) :
    FormerData m' cvT nP resSort pps lvls where
  read ψ := by
    refine denoteMeta_envExtend_mono hF hG hproj 0 cvT.type hcb ?_
    rw [← denoteMeta_acval_congr hag]
    exact h.read ψ
  len := h.len
  bits := h.bits
  okTy := h.okTy
  below := h.below
  params := h.params
  lvlsLen := h.lvlsLen
  lvl := h.lvl
  lvlsParams := h.lvlsParams

/-! ## Kit: the formers' loop at an ARBITRARY leaf

The constructors' data can only be READ at the environment holding all
`k` formers (their types mention the members), while the block's chains
— and hence the real member leaves — are built from that reading.  The
fixpoint route breaks the same circle with its dummy former
(`stageSumFormer` at the empty chain list); `MutualStageFormer.lean`'s
step is specialised to the fibre leaf, so the chain-free first pass
needs the step and the loop at an arbitrary closed leaf.  Everything
else — `MemberConsOk`, the block's empty capability record, the
freshness carried by the block's `Nodup` — is that file's. -/

set_option maxHeartbeats 1600000 in
/-- **The P step at one member's cons with an arbitrary closed leaf.** -/
theorem stageMemberConsG (mp : EnvModelM V μ env) (hE₀ : ConLeche.EtaFamiliesClosed env)
    {cvTa : ConstantVal} (hok : MemberConsOk env cvTa)
    {nP : Nat} {resSort : Level}
    {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {lvls : (Name → Nat) → List Nat}
    (hFD : FormerData mp.base2 cvTa nP resSort pps lvls)
    {A : (Name → Nat) → AnnotTerm}
    (hAbelow : ∀ ψ : Name → Nat, Term.bvarsBelow 0 (A ψ).erase)
    (hAparams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ cvTa.levelParams, ψ₁ q = ψ₂ q) → A ψ₁ = A ψ₂)
    (hAok : ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenotedV V ρ (A ψ))
    (hAmem : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      interp V ρ (A ψ) ∈ˢ interp V ρ (mkPisAV (pps ψ) (.sort (resSort.eval ψ)))) :
    ∃ mp' : EnvModelM V μ ⟨.indInfo cvTa {} :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval cvTa.name A := by
  have hfresh : env.find? cvTa.name = none := hok.fresh
  have hcb : ConstsBound env cvTa.type := constsBound_of_constsResolve _ hok.resolve
  have hicw : ConLeche.IndCapsWF (.indInfo cvTa {}) :=
    ConLeche.IndCapsWF.of_caps (fun hu => absurd hu (by decide)) (fun he => absurd he (by decide))
  have hwfI : ConLeche.EnvWF ⟨.indInfo cvTa {} :: env.consts⟩ :=
    ConLeche.EnvWF.cons mp.base2.wf (ConLeche.structConstWF hok.noFvar hok.lpsOk
      (Expr.constsResolve_mono hok.resolve) hok.bounded
      (fun _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
      (by intro tbl hh; exact ConstantInfo.noConfusion hh) hicw)
  have hreadI : ∀ ψ : Name → Nat,
      denoteMeta (acvalWith mp.base2.acval cvTa.name A)
        ⟨.indInfo cvTa {} :: env.consts⟩ ψ 0 cvTa.type
        = some (mkPisAV (pps ψ) (.sort (resSort.eval ψ))) := fun ψ =>
    denoteMeta_cons_mono (c₀ := .indInfo cvTa {}) hfresh
      (ConsCrossAt.ofNtc fun _ h => nomatch h) ψ 0 hcb (hFD.read ψ)
  have hnresI : ConLeche.reservedBasisNames.contains
      (ConstantInfo.indInfo cvTa {}).name = false := hok.nres
  have hpshapeI : (ConstantInfo.indInfo cvTa {}).name.isProjFnShape = false := hok.pshape
  refine declStep_preserves_of_ind_member_cons mp (c₀ := .indInfo cvTa {})
    (A := A) hfresh hnresI (Or.inl ⟨_, _, rfl⟩)
    (ConsHead.ofFresh hwfI (fun ψ => hAbelow ψ) hnresI
      (fun _ h => nomatch h)
      (fun _ _ _ _ h => nomatch h))
    (fun ψ k => AnnotTerm.liftN_eq_self _
      (Term.bvarsBelow.mono (Nat.zero_le k) (hAbelow ψ)) 1)
    hAparams (fun ψ ρ => (hAok ψ ρ).1) (fun ψ ρ => (hAok ψ ρ).2)
    (fun ψ => ⟨_, hreadI ψ⟩) ?_ ?_ ?_
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hreadI ψ).symm.trans hta)
    exact hFD.okTy ψ ρ
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hreadI ψ).symm.trans hta)
    exact hAmem ψ ρ
  · intro m₂ hac
    refine capsOk_cons_native mp (c₀ := .indInfo cvTa {})
      (A := A) (T := cvTa.name) hfresh
      (ConsCrossEnv.ofNtc fun _ h => nomatch h) hpshapeI
      (Or.inl ⟨cvTa, {}, rfl, rfl⟩)
      (fun T' cvT' caps' hf _ hres hcape => hE₀ T' cvT' caps' hf hcape hres)
      m₂ hac ?_
    intro cvT' caps' hf _
    have hself := ConLeche.Env.find?_cons_self (ConstantInfo.indInfo cvTa {}) env
    obtain ⟨rfl, rfl⟩ :=
      ConstantInfo.indInfo.inj (Option.some.inj (hself.symm.trans hf))
    exact ⟨fun he _ => absurd he (by decide), fun hu => absurd hu (by decide)⟩

set_option maxHeartbeats 1600000 in
/-- **The formers' loop at an arbitrary leaf** (`stageMutualFormersGo`
with the fibre leaf abstracted; `idxs i` is the block position of the
loop's `i`-th member). -/
theorem stageMembersGoG {nP : Nat} {resSort : Level} {lps : List Name}
    {Aof : Nat → (Name → Nat) → AnnotTerm}
    {ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {lvlsF : Nat → (Name → Nat) → List Nat}
    (hAbelow : ∀ (t : Nat) (ψ : Name → Nat), Term.bvarsBelow 0 (Aof t ψ).erase)
    (hAparams : ∀ (t : Nat) (ψ₁ ψ₂ : Name → Nat), (∀ q ∈ lps, ψ₁ q = ψ₂ q) →
      Aof t ψ₁ = Aof t ψ₂)
    (hAok : ∀ (t : Nat) (ψ : Name → Nat) (ρ : Nat → V), WellDenotedV V ρ (Aof t ψ))
    (hAmem : ∀ (t : Nat) (ψ : Name → Nat) (ρ : Nat → V),
      interp V ρ (Aof t ψ) ∈ˢ interp V ρ (mkPisAV (ppsF t ψ) (.sort (resSort.eval ψ)))) :
    ∀ (fs : List MutualFormerA) (idxs : Nat → Nat) (env' : Env) (mp' : EnvModelM V μ env'),
      ConLeche.EtaFamiliesClosed env' →
      (∀ f ∈ fs, MemberConsOk env' f.cvTa) →
      (fs.map (fun f => f.cvTa.name)).Nodup →
      (∀ (i : Nat) (f : MutualFormerA), fs[i]? = some f →
        f.cvTa.levelParams = lps ∧
        FormerData mp'.base2 f.cvTa (nP + f.nIdx) resSort (ppsF (idxs i)) (lvlsF (idxs i))) →
      ∃ mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fs env'),
        (∀ (i : Nat) (f : MutualFormerA), fs[i]? = some f →
          mp₁.base2.acval f.cvTa.name = Aof (idxs i)) ∧
        (∀ n : Name,
          (∀ (i : Nat) (f : MutualFormerA), fs[i]? = some f → n ≠ f.cvTa.name) →
          mp₁.base2.acval n = mp'.base2.acval n) := by
  intro fs
  induction fs with
  | nil =>
    intro idxs env' mp' _ _ _ _
    exact ⟨mp', fun i f hf => by simp at hf, fun _ _ => rfl⟩
  | cons f₁ rest ih =>
    intro idxs env' mp' hE hcons hnd hmem
    obtain ⟨cvTa, nIdx, s⟩ := f₁
    obtain ⟨hlps₀, hFD₀⟩ := hmem 0 ⟨cvTa, nIdx, s⟩ rfl
    have hok₀ : MemberConsOk env' cvTa := hcons ⟨cvTa, nIdx, s⟩ List.mem_cons_self
    have hfresh : env'.find? cvTa.name = none := hok₀.fresh
    have hcb₀ : ConstsBound env' cvTa.type := constsBound_of_constsResolve _ hok₀.resolve
    rw [List.map_cons, List.nodup_cons] at hnd
    have hne₀ : ∀ (i : Nat) (f : MutualFormerA), rest[i]? = some f → cvTa.name ≠ f.cvTa.name := by
      intro i f hf hh
      exact hnd.1 (hh ▸ List.mem_map_of_mem (List.mem_of_getElem? hf))
    obtain ⟨mpI, hacI⟩ := stageMemberConsG mp' hE hok₀ hFD₀ (hAbelow (idxs 0))
      (fun ψ₁ ψ₂ hφ => hAparams (idxs 0) ψ₁ ψ₂ (by rw [← hlps₀]; exact hφ))
      (hAok (idxs 0)) (hAmem (idxs 0))
    have hE' : ConLeche.EtaFamiliesClosed ⟨.indInfo cvTa {} :: env'.consts⟩ :=
      ConLeche.EtaFamiliesClosed.cons_nonind hE hfresh (fun cv'' caps heq he => by
        obtain ⟨-, rfl⟩ := ConstantInfo.indInfo.inj heq
        exact absurd he (by decide))
    obtain ⟨mp₁, hpos, hoff⟩ := ih (fun i => idxs (i + 1)) _ mpI hE' (by
      intro f hf
      refine (hcons f (List.mem_cons_of_mem _ hf)).cons (c₀ := .indInfo cvTa {}) ?_
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hf
      exact hne₀ i f hi) hnd.2 (by
      intro i f hf
      obtain ⟨hlps, hFD⟩ := hmem (i + 1) f (by simpa using hf)
      have hcb : ConstsBound env' f.cvTa.type :=
        constsBound_of_constsResolve _ (hcons f (List.mem_cons_of_mem _
          (List.mem_of_getElem? hf))).resolve
      exact ⟨hlps,
        hFD.cross (c₀ := .indInfo cvTa {}) hfresh
          (ConsCrossAt.ofNtc fun _ h => nomatch h) hcb mpI.base2 hacI⟩)
    refine ⟨mp₁, ?_, ?_⟩
    · intro i f hf
      cases i with
      | zero =>
        obtain rfl : f = ⟨cvTa, nIdx, s⟩ := Option.some.inj hf.symm
        show mp₁.base2.acval cvTa.name = _
        rw [hoff cvTa.name hne₀, hacI, acvalWith_self]
      | succ i =>
        have hf' : rest[i]? = some f := by simpa using hf
        exact hpos i f hf'
    · intro n hn
      rw [hoff n (fun i f hf => hn (i + 1) f (by simpa using hf)), hacI,
        acvalWith_ne (hn 0 ⟨cvTa, nIdx, s⟩ rfl)]

/-- **The formers' loop at an arbitrary leaf**, over the stage's run. -/
theorem stageMembersG {F nP : Nat} {resSort : Level} {lps : List Name}
    {Aof : Nat → (Name → Nat) → AnnotTerm}
    {ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {lvlsF : Nat → (Name → Nat) → List Nat}
    (hAbelow : ∀ (t : Nat) (ψ : Name → Nat), Term.bvarsBelow 0 (Aof t ψ).erase)
    (hAparams : ∀ (t : Nat) (ψ₁ ψ₂ : Name → Nat), (∀ q ∈ lps, ψ₁ q = ψ₂ q) →
      Aof t ψ₁ = Aof t ψ₂)
    (hAok : ∀ (t : Nat) (ψ : Name → Nat) (ρ : Nat → V), WellDenotedV V ρ (Aof t ψ))
    (hAmem : ∀ (t : Nat) (ψ : Name → Nat) (ρ : Nat → V),
      interp V ρ (Aof t ψ) ∈ˢ interp V ρ (mkPisAV (ppsF t ψ) (.sort (resSort.eval ψ))))
    {formers : List (ConstantVal × Nat)} {env₁ : Env} {fms : List MutualFormerA}
    (mp : EnvModelM V μ env) (hE : ConLeche.EtaFamiliesClosed env)
    (hrun : ConLeche.mutualFormers (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) nP formers env
      = .ok (env₁, fms))
    (hnd : (fms.map (fun f => f.cvTa.name)).Nodup)
    (hmem : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      f.cvTa.levelParams = lps ∧
      FormerData mp.base2 f.cvTa (nP + f.nIdx) resSort (ppsF t) (lvlsF t)) :
    ∃ mp₁ : EnvModelM V μ env₁,
      (∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
        mp₁.base2.acval f.cvTa.name = Aof t) ∧
      (∀ n : Name, (∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f → n ≠ f.cvTa.name) →
        mp₁.base2.acval n = mp.base2.acval n) := by
  obtain ⟨hchecks, rfl⟩ := ConLeche.mutualFormers_inv hrun
  exact stageMembersGoG hAbelow hAparams hAok hAmem fms (fun i => i) env mp hE
    (fun f hf => MemberConsOk.ofCheck (ConLeche.mutualFormerChecks_checked hchecks f hf).choose_spec)
    hnd hmem

/-! ## Kit: a member's index telescope, from its former's data alone -/

omit [SetTheory V] in
/-- The reversed telescope, dropped to its first `i` binders. -/
theorem drop_reverse_map_eq {ds : List (Nat × Nat × AnnotTerm)} {k i : Nat}
    (hlen : ds.length = k) (_hi : i ≤ k) :
    ((ds.map (·.2.2)).reverse).drop (k - i) = ((ds.take i).map (·.2.2)).reverse := by
  rw [reverse_map_take_drop ds i]
  have hl : (((ds.drop i).map (·.2.2)).reverse).length = k - i := by simp [hlen]
  rw [← hl, List.drop_left]

/-- **A member's index telescope is graded and bounded**, from its
former's binder data alone: the binders' universes are `FormerData`'s
`lvls` (M2.3c) and the walk is `idxOk_of`'s, with those levels in
place of the checker's sort rows — the mutual install runs no
index-telescope sort check of its own, so this is where `TagOk` comes
from. -/
theorem formerIdxOk {env : Env} {m : EnvModel V env} {cvT : ConstantVal} {nP nIdx : Nat}
    {resSort : Level} {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {lvls : (Name → Nat) → List Nat}
    (hFD : FormerData m cvT (nP + nIdx) resSort pps lvls)
    {u : Nat} {ψ : Name → Nat} (hu : ∀ j, j < nIdx → (lvls ψ).getD (nP + j) 0 ≤ u)
    (ρp : Nat → V) (hρp : Sat V (((pps ψ).take nP).map (·.2.2)).reverse ρp) :
    IdxOk u ρp (((pps ψ).drop nP).map (·.2.2)) ∧
      FieldsValid ρp (((pps ψ).drop nP).map (·.2.2)) := by
  have hst := stripPisAV_mkPisAV (pps ψ) (.sort (resSort.eval ψ))
  rw [hFD.len ψ] at hst
  have htele := piTeleAV_of_stripPisAV hst
  obtain ⟨okΓ, -⟩ := piTeleAV_graded (V := V) htele (Δ₀ := []) (fun ρ _ => hFD.okTy ψ ρ)
  simp only [List.append_nil] at okΓ
  have hΓ : (((pps ψ).map (·.2.2)).reverse).length = nP + nIdx := by simp [hFD.len ψ]
  have hbnd : ∀ j, j < nIdx → ∀ ρ : Nat → V,
      Sat V ((((pps ψ).map (·.2.2)).reverse).drop (nP + nIdx - (nP + j))) ρ →
      interp V ρ ((((pps ψ).map (·.2.2)).reverse).getD (nP + nIdx - 1 - (nP + j)) default)
        ∈ˢ (univ u : V) := by
    intro j hj ρ hρ
    have hi : nP + j < nP + nIdx := by omega
    have hget : (pps ψ)[nP + j]? = some ((pps ψ).getD (nP + j) default) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hFD.len ψ]; omega)]; rfl
    rw [getD_reverse_of_peel (hFD.len ψ) hi hget]
    refine univ_mono (hu j hj) _ (hFD.lvl ψ (nP + j) hi ρ ?_)
    rw [drop_reverse_map_eq (hFD.len ψ) (by omega)] at hρ
    exact hρ
  have hρp' : Sat V ((((pps ψ).map (·.2.2)).reverse).drop (nP + nIdx - (nP + 0))) ρp := by
    rw [Nat.add_zero, drop_reverse_map_eq (hFD.len ψ) (by omega)]
    exact hρp
  have hok := fieldsOkB_of_frame rfl hΓ okΓ (fun j hj ρ hρ _ => hbnd j hj ρ hρ) 0
    (Nat.zero_le _) ρp hρp'
  have hbd := fieldsBound_of_frame rfl hΓ hbnd 0 (Nat.zero_le _) ρp hρp'
  have hvd := fieldsValid_of_frame rfl hΓ okΓ 0 (Nat.zero_le _) ρp hρp'
  rw [fieldsFrom_eq_drop (hFD.len ψ)] at hok hbd hvd
  exact ⟨⟨hok, hbd⟩, hvd⟩

end ConLeche.Model
