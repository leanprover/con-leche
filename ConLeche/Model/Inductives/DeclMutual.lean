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

**The order, and why it is not the fixpoint route's.**  A mutual
constructor's type mentions the members, so its data can only be READ
at the environment holding all `k` formers; but the block's chains —
and hence the members' real leaves — are built from that reading.  The
fixpoint route breaks the circle with a dummy former; here the
CHAIN-FREE FIRST PASS does it (`stageMembersG` at the sum route's
chain-free towers), and the two readings are identified off the
recursive and reflexive slots (`mutualCtorDataI_ident`), which is
exactly where the X-chains are the shadow of the real ones.  The
cross-member parameter identification (`paramFrames` at
`mutualDomsOk`'s rows) also lives at that first carrier: without it no
member's index telescope can be graded at another member's parameter
frame, and the tag is the union of all of them.

**What the tail still owes** (the `sorry`): `stageMutualRecs` and
`stageMutualTables`.  For the first, the pieces in order are the
members' and constructors' readings at the constructors' carrier
(`formerReadsM_of`, `mutualCtorReadsM_of`, `mutualRecData_of`), the
`MutualRecParts` bundle, its `LeafHyp` (`MutualFrameOkM` at every
parameter frame, `auxFixPre_of` and `auxRecLeafFacts` for the
auxiliary recursor, and the stored type's typing), `mutualRuleOk` and
`denoteMeta_mutualRecRhs` for the rules, and `mutualRecRuleLaw` with
`ruleFires_of`.  For the second, `MutualTableOk` at every member.
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

/-! ## Kit: the λ-tower congruence over its domains

The block's members are consed with their OWN parameter telescopes,
while the generated recursor type takes its parameter Πs from member
`0`; the checker identifies the two only by `isDefEq`
(`mutualCrossChecks`' `mutualDomsOk`), so the leaves are identified
semantically — a λ-tower congruence over `mkLamsAV` under the
pointwise `interp` equality of the domains (`mkLamsC` re-bits every
binder, so only the domains matter). -/

/-- Two λ-towers' binder data agree hereditarily: equal bits, and
domains that interpret alike at every frame the tower reaches. -/
@[expose] def LamDomsAgree (V : Type w) [SetTheory V] (ρ : Nat → V) :
    List (Nat × AnnotTerm) → List (Nat × AnnotTerm) → Prop
  | [], [] => True
  | d :: ds, d' :: ds' => d.1 = d'.1 ∧ interp V ρ d.2 = interp V ρ d'.2 ∧
      ∀ x, x ∈ˢ interp V ρ d.2 → LamDomsAgree V (cons x ρ) ds ds'
  | _, _ => False

/-- **The λ-tower congruence**: two towers whose leading binder data
agree and whose trailing data and body are shared interpret alike. -/
theorem mkLamsAV_congr_doms {rest : List (Nat × AnnotTerm)} {b : AnnotTerm} :
    ∀ {ds ds' : List (Nat × AnnotTerm)} {ρ : Nat → V},
      LamDomsAgree V ρ ds ds' →
      interp V ρ (mkLamsAV (ds ++ rest) b) = interp V ρ (mkLamsAV (ds' ++ rest) b) := by
  intro ds
  induction ds with
  | nil =>
    intro ds' ρ h
    match ds' with
    | [] => rfl
    | _ :: _ => exact h.elim
  | cons d ds ih =>
    intro ds' ρ h
    match ds' with
    | [] => exact h.elim
    | d' :: ds' =>
      obtain ⟨hbit, hdom, hrest⟩ := h
      show (lamR d.1 (interp V ρ d.2) fun x => interp V (cons x ρ) (mkLamsAV (ds ++ rest) b))
        = (lamR d'.1 (interp V ρ d'.2) fun x => interp V (cons x ρ) (mkLamsAV (ds' ++ rest) b))
      rw [hbit, hdom]
      exact lamR_congr fun x hx => ih (hrest x (by rw [hdom]; exact hx))

/-- The agreement, from the binder-by-binder rows `paramFrames`
yields: the two telescopes have the same length and their `i`-th
entries interpret alike under every spine fitting the earlier ones. -/
theorem lamDomsAgree_of_rows {mb : Nat} :
    ∀ {L L' : List AnnotTerm} {ρ : Nat → V},
      L.length = L'.length →
      (∀ i, i < L.length → ∀ as : List V, SpineFit ρ (L.take i) as →
        interp V (consList as ρ) (L.getD i default)
          = interp V (consList as ρ) (L'.getD i default)) →
      LamDomsAgree V ρ (L.map fun A => (mb, A)) (L'.map fun A => (mb, A)) := by
  intro L
  induction L with
  | nil =>
    intro L' ρ hlen _
    match L' with
    | [] => trivial
    | _ :: _ => simp at hlen
  | cons A L ih =>
    intro L' ρ hlen hrow
    match L' with
    | [] => simp at hlen
    | A' :: L' =>
      refine ⟨rfl, ?_, fun x hx => ?_⟩
      · exact hrow 0 (by simp) [] trivial
      · refine ih (by simpa using hlen) ?_
        intro i hi as hsp
        exact hrow (i + 1) (by simp only [List.length_cons]; omega) (x :: as) ⟨hx, hsp⟩

/-- A reversed context's tail is the reverse of the telescope's head. -/
theorem reverse_drop_eq {L : List AnnotTerm} {n i : Nat}
    (hlen : L.length = n) (hi : i ≤ n) :
    L.reverse.drop (n - i) = (L.take i).reverse := by
  rw [List.drop_reverse, hlen, show n - (n - i) = i from by omega]

/-- A reversed context's `i`-th entry from the top is the telescope's
`i`-th from the bottom. -/
theorem reverse_getD_eq {L : List AnnotTerm} {n i : Nat}
    (hlen : L.length = n) (hi : i < n) :
    L.reverse.getD (n - 1 - i) default = L.getD i default := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_reverse (by omega), hlen, show n - 1 - (n - 1 - i) = i from by omega]

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

/-- Every entry of the member table carries a member's index. -/
theorem members3_mem_lt {b : MutualBlock} {x : Name × Nat × Nat} (h : x ∈ b.members3) :
    x.2.1 < b.k := by
  unfold ConLeche.MutualBlock.members3 at h
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
  obtain ⟨⟨cv, nIdx⟩, mIdx⟩ := q
  have hget : b.formers[mIdx]? = some (cv, nIdx) :=
    List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using hq)
  show mIdx < b.formers.length
  exact (List.getElem?_eq_some_iff.mp hget).1

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

/-- **The constructors' conses, as an environment extension.** -/
theorem consMutualCtors_extend {nP : Nat} :
    ∀ {ctorsA : List (ConstantVal × Nat)} {env : Env},
      (∀ c ∈ ctorsA, env.find? c.1.name = none) →
      (ctorsA.map (·.1.name)).Nodup →
      FindPreserved env (ConLeche.consMutualCtors nP ctorsA env) ∧
      LitGuardsMono env (ConLeche.consMutualCtors nP ctorsA env) ∧
      (∀ (sn : Name) (i : Nat), env.findProj? sn i = none →
        (ConLeche.consMutualCtors nP ctorsA env).findProj? sn i = none)
  | [], _, _, _ => ⟨fun h => h, ⟨fun h => h, fun h => h⟩, fun _ _ h => h⟩
  | c :: cs, env, hfresh, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have hc : env.find? c.1.name = none := hfresh c List.mem_cons_self
    have hfresh' : ∀ g ∈ cs,
        (Env.mk (ConstantInfo.ctorInfo c.1 nP c.2 :: env.consts)).find? g.1.name = none := by
      intro g hg
      refine (find?_cons_of_name_ne (c := .ctorInfo c.1 nP c.2) (fun hh => ?_)).trans
        (hfresh g (List.mem_cons_of_mem _ hg))
      refine hnd.1 ?_
      have hnm : c.1.name = g.1.name := hh
      rw [hnm]
      exact List.mem_map_of_mem hg
    obtain ⟨hF, hL, hP⟩ := consMutualCtors_extend hfresh' hnd.2
    refine ⟨fun h => hF (findPreserved_cons hc h), ⟨fun h => hL.1 ((litGuardsMono_cons hc).1 h),
      fun h => hL.2 ((litGuardsMono_cons hc).2 h)⟩, fun sn i h => hP sn i ?_⟩
    exact ConLeche.Verify.findProj?_cons_of_base_none
      (c₀ := .ctorInfo c.1 nP c.2) (fun _ hh => nomatch hh) sn i h

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
loop's `i`-th member).  The leaf's four facts are per member, beside
its binder data. -/
theorem stageMembersGoG {nP : Nat} {resSort : Level} {lps : List Name}
    {Aof : Nat → (Name → Nat) → AnnotTerm}
    {ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {lvlsF : Nat → (Name → Nat) → List Nat} :
    ∀ (fs : List MutualFormerA) (idxs : Nat → Nat) (env' : Env) (mp' : EnvModelM V μ env'),
      ConLeche.EtaFamiliesClosed env' →
      (∀ f ∈ fs, MemberConsOk env' f.cvTa) →
      (fs.map (fun f => f.cvTa.name)).Nodup →
      (∀ (i : Nat) (f : MutualFormerA), fs[i]? = some f →
        f.cvTa.levelParams = lps ∧
        FormerData mp'.base2 f.cvTa (nP + f.nIdx) resSort (ppsF (idxs i)) (lvlsF (idxs i)) ∧
        (∀ ψ : Name → Nat, Term.bvarsBelow 0 (Aof (idxs i) ψ).erase) ∧
        (∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ lps, ψ₁ q = ψ₂ q) →
          Aof (idxs i) ψ₁ = Aof (idxs i) ψ₂) ∧
        (∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenotedV V ρ (Aof (idxs i) ψ)) ∧
        (∀ (ψ : Name → Nat) (ρ : Nat → V), interp V ρ (Aof (idxs i) ψ)
          ∈ˢ interp V ρ (mkPisAV (ppsF (idxs i) ψ) (.sort (resSort.eval ψ))))) →
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
    obtain ⟨hlps₀, hFD₀, hbel₀, hpar₀, hok₀', hmem₀'⟩ := hmem 0 ⟨cvTa, nIdx, s⟩ rfl
    have hok₀ : MemberConsOk env' cvTa := hcons ⟨cvTa, nIdx, s⟩ List.mem_cons_self
    have hfresh : env'.find? cvTa.name = none := hok₀.fresh
    rw [List.map_cons, List.nodup_cons] at hnd
    have hne₀ : ∀ (i : Nat) (f : MutualFormerA), rest[i]? = some f → cvTa.name ≠ f.cvTa.name := by
      intro i f hf hh
      exact hnd.1 (hh ▸ List.mem_map_of_mem (List.mem_of_getElem? hf))
    obtain ⟨mpI, hacI⟩ := stageMemberConsG mp' hE hok₀ hFD₀ hbel₀
      (fun ψ₁ ψ₂ hφ => hpar₀ ψ₁ ψ₂ (by rw [← hlps₀]; exact hφ)) hok₀' hmem₀'
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
      obtain ⟨hlps, hFD, hb, hp, ho, hm⟩ := hmem (i + 1) f (by simpa using hf)
      have hcb : ConstsBound env' f.cvTa.type :=
        constsBound_of_constsResolve _ (hcons f (List.mem_cons_of_mem _
          (List.mem_of_getElem? hf))).resolve
      exact ⟨hlps,
        hFD.cross (c₀ := .indInfo cvTa {}) hfresh
          (ConsCrossAt.ofNtc fun _ h => nomatch h) hcb mpI.base2 hacI, hb, hp, ho, hm⟩)
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
    {formers : List (ConstantVal × Nat)} {env₁ : Env} {fms : List MutualFormerA}
    (mp : EnvModelM V μ env) (hE : ConLeche.EtaFamiliesClosed env)
    (hrun : ConLeche.mutualFormers (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) nP formers env
      = .ok (env₁, fms))
    (hnd : (fms.map (fun f => f.cvTa.name)).Nodup)
    (hmem : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      f.cvTa.levelParams = lps ∧
      FormerData mp.base2 f.cvTa (nP + f.nIdx) resSort (ppsF t) (lvlsF t) ∧
      (∀ ψ : Name → Nat, Term.bvarsBelow 0 (Aof t ψ).erase) ∧
      (∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ lps, ψ₁ q = ψ₂ q) → Aof t ψ₁ = Aof t ψ₂) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenotedV V ρ (Aof t ψ)) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V), interp V ρ (Aof t ψ)
        ∈ˢ interp V ρ (mkPisAV (ppsF t ψ) (.sort (resSort.eval ψ))))) :
    ∃ mp₁ : EnvModelM V μ env₁,
      (∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
        mp₁.base2.acval f.cvTa.name = Aof t) ∧
      (∀ n : Name, (∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f → n ≠ f.cvTa.name) →
        mp₁.base2.acval n = mp.base2.acval n) := by
  obtain ⟨hchecks, rfl⟩ := ConLeche.mutualFormers_inv hrun
  exact stageMembersGoG fms (fun i => i) env mp hE
    (fun f hf => MemberConsOk.ofCheck (ConLeche.mutualFormerChecks_checked hchecks f hf).choose_spec)
    hnd hmem

/-! ## Kit: the readings that do not move -/

/-- **`denoteMeta_acvalWith_unmentioned` at two carriers agreeing off a
block**: a term whose constants all resolve in the pre-block
environment — literal spines included, which is what `constsResolve`'s
literal clauses give — reads the same under any two carriers that agree
there. -/
theorem denoteMeta_congr_of_resolve {acval₁ acval₂ : Name → (Name → Nat) → AnnotTerm}
    {env₀ env : Env} {φ : Name → Nat}
    (hag : ∀ n : Name, (env₀.find? n).isSome = true → acval₁ n = acval₂ n) :
    ∀ (d : Nat) (e : Expr), Expr.constsResolve env₀ e = true →
      denoteMeta acval₁ env φ d e = denoteMeta acval₂ env φ d e := by
  intro d e
  induction d, e using denoteMeta.induct (env := env) with
  | case1 d u => intro _; rw [denoteMeta, denoteMeta]
  | case2 d idx ty => intro _; rw [denoteMeta, denoteMeta]
  | case3 d n us ci hf hlen =>
    intro hcr
    rw [denoteMeta, denoteMeta, hf]
    dsimp only
    rw [if_pos hlen, if_pos hlen, hag n (by simpa [Expr.constsResolve] using hcr)]
  | case4 d n us ci hf hlen =>
    intro _
    rw [denoteMeta, denoteMeta, hf]
    dsimp only
    rw [if_neg hlen, if_neg hlen]
  | case5 d n us hf => intro _; rw [denoteMeta, denoteMeta, hf]
  | case6 d ty body m ihty ihbody =>
    intro hcr
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
    rw [denoteMeta, denoteMeta, ihty hcr.1,
      ihbody (Expr.constsResolve_instantiate1 hcr.1 0 hcr.2)]
  | case7 d ty body m ihty ihbody =>
    intro hcr
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
    rw [denoteMeta, denoteMeta, ihty hcr.1,
      ihbody (Expr.constsResolve_instantiate1 hcr.1 0 hcr.2)]
  | case8 d f a ihf iha =>
    intro hcr
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
    rw [denoteMeta, denoteMeta, ihf hcr.1, iha hcr.2]
  | case9 d ty val body =>
    intro _
    rw [denoteMeta, denoteMeta]
  | case10 d sn i e ihe =>
    intro hcr
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
    rw [denoteMeta, denoteMeta, ihe hcr.2]
  | case11 d n hsup =>
    intro hcr
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
    rw [denoteMeta, denoteMeta, if_pos hsup, if_pos hsup,
      hag ConLeche.natZeroName hcr.1.2, hag ConLeche.natSuccName hcr.2]
  | case12 d n hsup =>
    intro _
    rw [denoteMeta, denoteMeta, if_neg hsup, if_neg hsup]
  | case13 d s hsup =>
    intro hcr
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hZ⟩, hS⟩, -⟩, hO⟩, -⟩, hN⟩, hC⟩, hH⟩, hF⟩ := hcr
    rw [denoteMeta, denoteMeta, if_pos hsup, if_pos hsup,
      hag ConLeche.stringOfListName hO, hag ConLeche.listNilName hN,
      hag ConLeche.listConsName hC, hag ConLeche.charName hH,
      hag ConLeche.charOfNatName hF, hag ConLeche.natZeroName hZ,
      hag ConLeche.natSuccName hS]
  | case14 d s hsup =>
    intro _
    rw [denoteMeta, denoteMeta, if_neg hsup, if_neg hsup]
  | case15 d x hs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro _
    cases x with
    | bvar i => rw [denoteMeta.eq_def, denoteMeta.eq_def]
    | sort u => exact absurd rfl (hs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n us => exact absurd rfl (hc n us)
    | forallE ty b m => exact absurd rfl (hpi ty b m)
    | lam ty b m => exact absurd rfl (hlam ty b m)
    | app f a => exact absurd rfl (happ f a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal n => exact absurd rfl (hnat n)
      | strVal s => exact absurd rfl (hstr s)

set_option maxHeartbeats 1600000 in
/-- **A mutual constructor's data at two carriers agreeing off the
block** (`fixCtorDataI_ident` at `k` members): the openings and the
residual's index arguments are syntactic, and the index readings, the
recursive slots' index expressions, the reflexive telescopes and the
ORDINARY fields' domains all read expressions that resolve BEFORE the
block, so they do not move.  What moves is exactly the recursive and
reflexive entries — the members' leaves. -/
theorem mutualCtorDataI_ident {env₀ : Env} {m₁ m₂ : EnvModel V env}
    (hag : ∀ n : Name, (env₀.find? n).isSome = true → m₁.acval n = m₂.acval n)
    {members : List (Name × Nat × Nat)} {T : Name} {lps : List Name} {cvC : ConstantVal}
    {nP nF nIdx : Nat} {resSort : Level} {isProp large : Bool}
    {idx₁ idx₂ : List Expr}
    {ds₁ ds₂ : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {Es₁ Es₂ : (Name → Nat) → List AnnotTerm} {srcs₁ srcs₂ : List (Option Nat)}
    {ks : List (RecFieldKind × Nat)}
    {fvsP₁ fvsP₂ xFvs₁ xFvs₂ : List Expr} {xrest₁ xrest₂ : Expr}
    {Eiss₁ Eiss₂ : (Name → Nat) → List (List AnnotTerm)}
    {tss₁ tss₂ : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (h₁ : MutualCtorDataI m₁ env₀ members T lps cvC nP nF nIdx resSort isProp large idx₁ ds₁ Es₁
      srcs₁ ks fvsP₁ xFvs₁ xrest₁ Eiss₁ tss₁)
    (h₂ : MutualCtorDataI m₂ env₀ members T lps cvC nP nF nIdx resSort isProp large idx₂ ds₂ Es₂
      srcs₂ ks fvsP₂ xFvs₂ xrest₂ Eiss₂ tss₂) :
    idx₁ = idx₂ ∧ fvsP₁ = fvsP₂ ∧ xFvs₁ = xFvs₂ ∧ xrest₁ = xrest₂ ∧
    (∀ ψ : Name → Nat, Es₁ ψ = Es₂ ψ) ∧ (∀ ψ : Name → Nat, Eiss₁ ψ = Eiss₂ ψ) ∧
    (∀ ψ : Name → Nat, tss₁ ψ = tss₂ ψ) ∧
    ∀ (ψ : Name → Nat) (i : Nat), i < nF → kindAt ks i ≠ .recursive → kindAt ks i ≠ .reflexive →
      ((ds₁ ψ).getD (nP + i) default).2.2 = ((ds₂ ψ).getD (nP + i) default).2.2 := by
  have hcg : ∀ (ψ : Name → Nat) (d : Nat) (e : Expr), Expr.constsResolve env₀ e = true →
      denoteMeta m₁.acval env ψ d e = denoteMeta m₂.acval env ψ d e :=
    fun ψ => denoteMeta_congr_of_resolve (φ := ψ) hag
  obtain ⟨crest₁, hopP₁, hopX₁⟩ := h₁.opens
  obtain ⟨crest₂, hopP₂, hopX₂⟩ := h₂.opens
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hopP₁.symm.trans hopP₂))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hopX₁.symm.trans hopX₂))
  have hidx : idx₁ = idx₂ := by rw [h₁.idxEq, h₂.idxEq]
  subst hidx
  -- a reflexive field's opening is the same at both carriers
  have hrefl : ∀ (ψ : Name → Nat) (i : Nat) (x : Expr), xFvs₁[i]? = some x →
      kindAt ks i = .reflexive →
      ((tss₁ ψ).getD i []).length = ((tss₂ ψ).getD i []).length ∧
      ∃ afvs body,
        ConLeche.openPisAtFvars ((tss₁ ψ).getD i []).length x.fvarTypeD (nP + i)
          = some (afvs, body) ∧
        (∀ k a, afvs[k]? = some a →
          ((tss₁ ψ).getD i []).getD k default = ((tss₂ ψ).getD i []).getD k default) ∧
        DenoteMetaSpine m₁.acval env ψ (nP + i + ((tss₁ ψ).getD i []).length)
          (body.getAppArgs.drop nP) ((Eiss₁ ψ).getD i []) ∧
        DenoteMetaSpine m₂.acval env ψ (nP + i + ((tss₁ ψ).getD i []).length)
          (body.getAppArgs.drop nP) ((Eiss₂ ψ).getD i []) ∧
        (∀ e ∈ body.getAppArgs.drop nP, Expr.constsResolve env₀ e = true) := by
    intro ψ i x hx hk
    obtain ⟨afvs, body, hop₁, hlen₁, hdoms₁, hsp₁⟩ := h₁.reflOpen ψ i x hx hk
    obtain ⟨afvs₂, body₂, hop₂, hlen₂, hdoms₂, hsp₂⟩ := h₂.reflOpen ψ i x hx hk
    have hlen : ((tss₁ ψ).getD i []).length = ((tss₂ ψ).getD i []).length := by
      rw [hlen₁, hlen₂]
    rw [← hlen] at hop₂ hsp₂
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hop₁.symm.trans hop₂))
    obtain ⟨afvs', body', hop', -, hresA, -, -, -, hresB, -, -⟩ := h₁.opened.reflF i x hx hk
    rw [← hlen₁] at hop'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hop₁.symm.trans hop'))
    refine ⟨hlen, afvs, body, hop₁, fun k a hka => ?_, hsp₁, hsp₂, hresB⟩
    have hd₁ := hdoms₁ k a hka
    have hd₂ := hdoms₂ k a hka
    rw [hcg ψ (nP + i + k) _ (hresA a (List.mem_of_getElem? hka))] at hd₁
    have h22 := Option.some.inj (hd₁.symm.trans hd₂)
    have hlenA := openPisAtFvars_length _ hop₁
    have hkA : k < afvs.length := (List.getElem?_eq_some_iff.mp hka).1
    have hB₁ := h₁.tssBits ψ i
    have hB₂ := h₂.tssBits ψ i
    have hP₁ := h₁.tssPiBits ψ i
    have hP₂ := h₂.tssPiBits ψ i
    generalize hL₁ : (tss₁ ψ).getD i [] = L₁ at hlen hlenA hB₁ hP₁ h22 ⊢
    generalize hL₂ : (tss₂ ψ).getD i [] = L₂ at hlen hB₂ hP₂ h22 ⊢
    have hk₁ : k < L₁.length := by rw [← hlenA]; exact hkA
    have hk₂ : k < L₂.length := by rw [← hlen]; exact hk₁
    have hm₁ : L₁.getD k default ∈ L₁ := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk₁]; exact List.getElem_mem hk₁
    have hm₂ : L₂.getD k default ∈ L₂ := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk₂]; exact List.getElem_mem hk₂
    obtain ⟨hb₁, hle₁⟩ := hP₁ _ hm₁
    obtain ⟨hb₂, hle₂⟩ := hP₂ _ hm₂
    have hz := (hB₁ _ hm₁).trans (hB₂ _ hm₂).symm
    have h21 : (L₁.getD k default).2.1 = (L₂.getD k default).2.1 := by
      rcases Nat.lt_or_ge (L₁.getD k default).2.1 1 with hlt | hge
      · have h0 : (L₁.getD k default).2.1 = 0 := by omega
        rw [h0, (hz.mp h0).symm]
      · have h1 : (L₁.getD k default).2.1 = 1 := by omega
        have hne : (L₂.getD k default).2.1 ≠ 0 := fun h0 => by
          have := hz.mpr h0; omega
        omega
    exact Prod.ext (hb₁.trans hb₂.symm) (Prod.ext h21 h22)
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro ψ
    have hres : ∀ a ∈ idx₁, Expr.constsResolve env₀ a = true := by
      rw [h₁.idxEq]; exact h₁.opened.residRes
    exact DenoteMetaSpine.unique
      (DenoteMetaSpine.congr (h₁.idxRead ψ) (fun a ha => hcg ψ (nP + nF) a (hres a ha)))
      (h₂.idxRead ψ)
  · intro ψ
    have hl₁ := h₁.eissLen ψ
    have hl₂ := h₂.eissLen ψ
    apply List.ext_getElem?
    intro i
    rcases Nat.lt_or_ge i nF with hi | hi
    · have hx : xFvs₁[i]? = some (xFvs₁[i]'(by rw [h₁.xLen]; exact hi)) :=
        List.getElem?_eq_getElem _
      have hD : (Eiss₁ ψ).getD i [] = (Eiss₂ ψ).getD i [] := by
        rcases h₁.opened.kinds i hi with hk | hk | hk
        · rw [h₁.ordNone ψ i (by rw [hk]; exact nofun) (by rw [hk]; exact nofun),
            h₂.ordNone ψ i (by rw [hk]; exact nofun) (by rw [hk]; exact nofun)]
        · have hr₁ := h₁.eisRead ψ i _ hx hk
          have hr₂ := h₂.eisRead ψ i _ hx hk
          obtain ⟨-, -, -, hres, -, -⟩ := h₁.opened.recF i _ hx hk
          exact DenoteMetaSpine.unique
            (DenoteMetaSpine.congr hr₁ (fun a ha => hcg ψ (nP + i) a (hres a ha))) hr₂
        · obtain ⟨-, afvs, body, -, -, hr₁, hr₂, hres⟩ := hrefl ψ i _ hx hk
          exact DenoteMetaSpine.unique
            (DenoteMetaSpine.congr hr₁ (fun a ha => hcg ψ _ a (hres a ha))) hr₂
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
      congr 1
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hD
      exact hD
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  · intro ψ
    have hl₁ := h₁.tssLen ψ
    have hl₂ := h₂.tssLen ψ
    apply List.ext_getElem?
    intro i
    rcases Nat.lt_or_ge i nF with hi | hi
    · have hx : xFvs₁[i]? = some (xFvs₁[i]'(by rw [h₁.xLen]; exact hi)) :=
        List.getElem?_eq_getElem _
      have hD : (tss₁ ψ).getD i [] = (tss₂ ψ).getD i [] := by
        by_cases hk : kindAt ks i = .reflexive
        · obtain ⟨hlen, afvs, body, hop, hdoms, -, -, -⟩ := hrefl ψ i _ hx hk
          have hlenA := openPisAtFvars_length _ hop
          generalize hL₁ : (tss₁ ψ).getD i [] = L₁ at hlen hlenA hdoms ⊢
          generalize hL₂ : (tss₂ ψ).getD i [] = L₂ at hlen hdoms ⊢
          apply List.ext_getElem
          · exact hlen
          · intro k hk₁ hk₂
            obtain ⟨a, ha⟩ : ∃ a, afvs[k]? = some a :=
              ⟨_, List.getElem?_eq_getElem (by rw [hlenA]; exact hk₁)⟩
            have hh := hdoms k a ha
            rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem hk₁, List.getElem?_eq_getElem hk₂, Option.getD_some,
              Option.getD_some] at hh
            exact hh
        · rw [h₁.tssNone ψ i hk, h₂.tssNone ψ i hk]
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
      congr 1
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hD
      exact hD
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  · intro ψ i hi hnr hnf
    have hx : xFvs₁[i]? = some (xFvs₁[i]'(by rw [h₁.xLen]; exact hi)) :=
      List.getElem?_eq_getElem _
    have hk : kindAt ks i = .ordinary := by
      rcases h₁.opened.kinds i hi with hk | hk | hk
      · exact hk
      · exact absurd hk hnr
      · exact absurd hk hnf
    have hd₁ := h₁.domRead ψ i _ hx
    have hd₂ := h₂.domRead ψ i _ hx
    rw [hcg ψ (nP + i) _ (h₁.opened.ord i _ hx hk)] at hd₁
    exact Option.some.inj (hd₁.symm.trans hd₂)

/-! ## Kit: the opened guard travels to the formers' environment

The kernel re-checks the opened constructor form at the PRE-BLOCK
environment (`mutualFieldsOk env …`) but CHECKS the constructor at the
formers' environment, and `MutualStageCtor.lean`'s stage ties the two
into one `env₀`.  The guard is a conjunction of `constsResolve env₀`
facts, so it travels along the formers' conses. -/

theorem constsResolve_consMutualFormers : ∀ {fms : List MutualFormerA} {env : Env} {e : Expr},
    Expr.constsResolve env e = true →
    Expr.constsResolve (ConLeche.consMutualFormers fms env) e = true
  | [], _, _, h => h
  | f :: fs, env, e, h => by
    show Expr.constsResolve
      (ConLeche.consMutualFormers fs ⟨.indInfo f.cvTa {} :: env.consts⟩) e = true
    exact constsResolve_consMutualFormers (Expr.constsResolve_mono h)

omit [SetTheory V] in
/-- The opened-form guard travels to a larger environment. -/
theorem MutualOpened.mono {env₀ env₀' : Env} {members : List (Name × Nat × Nat)}
    {lps : List Name} {nP nF : Nat} {ks : List (RecFieldKind × Nat)}
    {fvsP xFvs : List Expr} {xrest : Expr}
    (hm : ∀ e : Expr, Expr.constsResolve env₀ e = true → Expr.constsResolve env₀' e = true)
    (h : MutualOpened env₀ members lps nP nF ks fvsP xFvs xrest) :
    MutualOpened env₀' members lps nP nF ks fvsP xFvs xrest where
  residRes e he := hm e (h.residRes e he)
  ord i x hx hk := hm _ (h.ord i x hx hk)
  recF i x hx hk := by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h.recF i x hx hk
    exact ⟨h1, h2, h3, fun e he => hm e (h4 e he), h5, h6⟩
  reflF i x hx hk := by
    obtain ⟨afvs, body, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h.reflF i x hx hk
    exact ⟨afvs, body, h1, h2, fun a ha => hm _ (h3 a ha), h4, h5, h6,
      fun e he => hm e (h7 e he), h8, h9⟩
  kinds := h.kinds

/-- … and so does a constructor's data: its `env₀` is the guard's. -/
theorem MutualCtorDataI.monoEnv₀ {m : EnvModel V env} {env₀ env₀' : Env}
    {members : List (Name × Nat × Nat)} {T : Name} {lps : List Name} {cvC : ConstantVal}
    {nP nF nIdx : Nat} {resSort : Level} {isProp large : Bool} {idxArgs : List Expr}
    {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    {srcs : List (Option Nat)} {ks : List (RecFieldKind × Nat)} {fvsP xFvs : List Expr}
    {xrest : Expr} {Eiss : (Name → Nat) → List (List AnnotTerm)}
    {tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (hm : ∀ e : Expr, Expr.constsResolve env₀ e = true → Expr.constsResolve env₀' e = true)
    (h : MutualCtorDataI m env₀ members T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es
      srcs ks fvsP xFvs xrest Eiss tss) :
    MutualCtorDataI m env₀' members T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es
      srcs ks fvsP xFvs xrest Eiss tss :=
  { h with opened := h.opened.mono hm }

/-! ## Kit: `FieldsBelow`, positionally -/

/-- A field chain is bounded when its entries are. -/
theorem fieldsBelow_of_getD : ∀ (L : List AnnotTerm) (K : Nat),
    (∀ i, i < L.length → Term.bvarsBelow (K + i) (L.getD i default).erase) → FieldsBelow K L
  | [], _, _ => trivial
  | F :: L, K, h => by
    refine ⟨by simpa using h 0 (by simp), ?_⟩
    refine fieldsBelow_of_getD L (K + 1) fun i hi => ?_
    have hh := h (i + 1) (by simp; omega)
    simpa [show K + 1 + i = K + (i + 1) from by omega] using hh

/-- … and conversely. -/
theorem getD_of_fieldsBelow : ∀ (L : List AnnotTerm) (K : Nat), FieldsBelow K L →
    ∀ i, i < L.length → Term.bvarsBelow (K + i) (L.getD i default).erase
  | [], _, _, i, hi => by simp at hi
  | F :: L, K, h, i, hi => by
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have hh := getD_of_fieldsBelow L (K + 1) h.2 i (by simp at hi ⊢; omega)
      simpa [show K + 1 + i = K + (i + 1) from by omega] using hh

omit [SetTheory V] in
/-- The shadow chain only reads the ORDINARY slots. -/
theorem shadowFs_congr {nP nF : Nat} {ks : List RecFieldKind} {Fs₁ Fs₂ : List AnnotTerm}
    (h : ∀ i, i < nF → ¬ recAt nP ks (nP + i) →
      Fs₁.getD i default = Fs₂.getD i default) :
    shadowFs nP ks nF Fs₁ = shadowFs nP ks nF Fs₂ := by
  refine List.ext_getElem? fun i => ?_
  by_cases hi : i < nF
  · rw [shadowFs_getElem? hi, shadowFs_getElem? hi]
    by_cases hr : recAt nP ks (nP + i)
    · rw [if_pos hr, if_pos hr]
    · rw [if_neg hr, if_neg hr, h i hi hr]
  · rw [List.getElem?_eq_none (by rw [shadowFs_length]; omega),
      List.getElem?_eq_none (by rw [shadowFs_length]; omega)]

/-- The shadow chain is bounded where the real one is: the shadowed
slots carry `Sort 0`. -/
theorem shadowFs_below {nP nF : Nat} {ks : List RecFieldKind} {Fs : List AnnotTerm}
    (hlen : Fs.length = nF) (h : FieldsBelow nP Fs) :
    FieldsBelow nP (shadowFs nP ks nF Fs) := by
  refine fieldsBelow_of_getD _ nP fun i hi => ?_
  have hi' : i < nF := by rw [shadowFs_length] at hi; exact hi
  rw [shadowFs_getD hi']
  split
  · exact trivial
  · exact getD_of_fieldsBelow Fs nP h i (by omega)

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

/-! ## The assembly -/

set_option maxHeartbeats 25600000 in
/-- A bounded binder list stays bounded when truncated. -/
theorem domsBelow_take : ∀ {ds : List (Nat × Nat × AnnotTerm)} {k n : Nat},
    DomsBelow k ds → DomsBelow k (ds.take n)
  | [], _, _, _ => by rw [List.take_nil]; trivial
  | _ :: _, _, 0, _ => trivial
  | _ :: ds, _, n + 1, h => ⟨h.1, domsBelow_take (ds := ds) (n := n) h.2⟩

/-! ## Kit: the auxiliary family's body is valid at the BARE parameter
frame

`auxBodyAV_validV` (`MutualStageFormer.lean`) asks for an index spine
`SpineFit ρp (auxIds W Idss) [z]`, which it uses only for the frame
shift of `fixBody_validV`'s application arm; the fixpoint body's own
validity needs the index data and the chains alone.  The recursor's
frame theorem (`MutualFrameOkM.auxValid`) wants it at the parameter
frame, where NO tag element is available — the block's tag can be
empty (a member with an uninhabited index domain) — so the spine-free
form is the one the stage needs. -/
theorem fixBodyAVI_validV {u w nIdx : Nat} {ρp : Nat → V} {Ids : List AnnotTerm}
    {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
    {Eiss : List (List (List AnnotTerm))} {Fss Ess : List (List AnnotTerm)}
    (hI : IdxOk u ρp Ids) (hIV : FieldsValid ρp Ids)
    (hchains : ∀ X, X ∈ˢ lfpFamSpace V w (idxSet u ρp Ids) → ∀ t, t ∈ˢ idxSet u ρp Ids →
      SumFieldsValid (cons t (cons X ρp)) (chainsXI u Ids nIdx rss tlss Eiss Fss Ess)) :
    AnnotValid V ρp (fixBodyAVI u w Ids nIdx rss tlss Eiss Fss Ess) := by
  unfold fixBodyAVI
  refine mkAppN_validV (by simp) ?_
  intro a ha
  simp only [List.mem_cons] at ha
  rcases ha with rfl | rfl | h
  · exact towerBodyAV_validV hIV
  · unfold fixFunAVI
    rw [AnnotValid_lam]
    refine ⟨?_, fun X hX => ?_⟩
    · unfold famTyAV
      rw [AnnotValid_pi]
      exact ⟨towerBodyAV_validV hIV, fun _ _ => trivial, fun h => absurd h (Nat.succ_ne_zero _)⟩
    · rw [(famTyAV_facts hI).1] at hX
      rw [AnnotValid_lam]
      have hsh1 : shiftE 1 0 (cons X ρp) = ρp := by
        rw [show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
      refine ⟨?_, fun t ht => ?_⟩
      · rw [AnnotValid_liftN, hsh1]; exact towerBodyAV_validV hIV
      · rw [interp_liftN, hsh1, (idxTyAV_facts hI).1] at ht
        exact sumBodyAV_validV (hchains X hX t ht)
  · exact nomatch h

/-- **The P carrier survives a mutual install.** -/
theorem declMutual (hμ : μ.verifiedChecks = true) {F : Nat} {env env₂ : Env}
    {block : List ConstantInfo} {nPd : Nat} {p : MutualParts} (mp : EnvModelM V μ env)
    (hE : ConLeche.EtaFamiliesClosed env) (hdp : ConLeche.mutualParts? nPd block = some p)
    (h : ConLeche.Semantics.DeclMutualRun μ F env p env₂)
    (hreps : MutualRepsOk V μ p.toBlock) : Nonempty (EnvModelM V μ env₂) := by
  obtain ⟨hpin, b, streamRecs, env₁, fms, f₀, tq₀, ctorsA, sortss, kinds, formers4, ctors4,
    cvRas, rulesOf, rfl, rfl, hNodup, hlpsAll, hmemLt, hgrouped, hformers, hf0, htq0, hcross,
    hlarge, hctors, hkinds, hfo, hgd, hrectys, hrules, htbl⟩ := h
  -- the recogniser settled the pin; the install threw on it
  have hpinOk : ConLeche.mutualRecPinOk p = true := by
    rw [← ConLeche.mutualParts?_recPinned hdp]; exact hpin
  -- stage 1, split: the checks at the PRE-BLOCK environment, the conses after
  obtain ⟨hchecks, rfl⟩ := ConLeche.mutualFormers_inv hformers
  obtain ⟨hlenFms, hposF⟩ := mutualFormerChecks_pos hchecks
  -- the checked members carry the declared names and level parameters
  have hnamesF : fms.map (·.cvTa.name) = p.toBlock.memberNames := by
    refine List.ext_getElem? fun t => ?_
    rw [List.getElem?_map]
    cases hft : fms[t]? with
    | none =>
      have hn : p.toBlock.formers[t]? = none := by
        rw [List.getElem?_eq_none_iff] at hft ⊢; omega
      simp [ConLeche.MutualBlock.memberNames, List.getElem?_map, hn]
    | some f =>
      obtain ⟨cv, cv', bs, hl, hccv, hn1, -, -⟩ := hposF t f hft
      obtain ⟨-, -, -, -, -, -, _, _, _, -, -, -, -, -, hty⟩ :=
        ConLeche.checkConstantVal_inv hccv
      simp [ConLeche.MutualBlock.memberNames, List.getElem?_map, hl, hty, hn1]
  -- the block's names are distinct
  have hndM : (p.toBlock.formers.map (·.1.name)).Nodup := by
    have h0 := hNodup
    unfold ConLeche.MutualBlock.blockNames ConLeche.MutualBlock.memberNames at h0
    exact (List.nodup_append.mp (List.nodup_append.mp h0).1).1
  have hndC : (p.toBlock.ctors.map (·.cv.name)).Nodup := by
    have h0 := hNodup
    unfold ConLeche.MutualBlock.blockNames at h0
    exact (List.nodup_append.mp (List.nodup_append.mp h0).1).2.1
  have hndF : (fms.map (·.cvTa.name)).Nodup := by
    rw [hnamesF]; exact hndM
  -- every member carries the block's level parameters and is fresh
  -- before the block
  have hlpsF : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      f.cvTa.levelParams = p.toBlock.lps := by
    intro t f hft
    obtain ⟨cv, cv', bs, hl, hccv, -, hl2, -⟩ := hposF t f hft
    obtain ⟨-, -, -, -, -, -, _, _, _, -, -, -, -, -, hty⟩ :=
      ConLeche.checkConstantVal_inv hccv
    have hall : (p.toBlock.formers.all fun f => f.1.levelParams == p.toBlock.lps) = true := by
      simpa using (Bool.and_eq_true _ _ |>.mp hlpsAll).1
    have := List.all_eq_true.mp hall (cv, f.nIdx) (List.mem_of_getElem? hl)
    rw [hty]
    show cv'.levelParams = _
    rw [hl2]
    simpa using this
  have hfreshF : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      env.find? f.cvTa.name = none := by
    intro t f hft
    obtain ⟨cv, cv', bs, hl, hccv, -, -, -⟩ := hposF t f hft
    obtain ⟨hfind, -, -, -, -, -, _, _, _, -, -, -, -, -, hty⟩ :=
      ConLeche.checkConstantVal_inv hccv
    rw [hty]; exact hfind
  -- every member's telescope, from its check
  have hstripF : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      ∃ bs : List (Expr × BinderMeta),
        f.cvTa.type.stripPis (p.toBlock.nP + f.nIdx) = some (bs, .sort f.s) := by
    intro t f hft
    obtain ⟨cv, cv', bs, -, -, -, -, hstrip⟩ := hposF t f hft
    exact ⟨bs, hstrip⟩
  -- the members' binder data, at the pre-block carrier
  have hFDex : ∀ t : Nat, ∃ (pps : (Name → Nat) → List (Nat × Nat × AnnotTerm))
      (lvls : (Name → Nat) → List Nat),
      (∀ f : MutualFormerA, fms[t]? = some f →
        FormerData mp.base2 f.cvTa (p.toBlock.nP + f.nIdx) f.s pps lvls) ∧
      (fms[t]? = none → ∀ ψ : Name → Nat, pps ψ = []) := by
    intro t
    cases hft : fms[t]? with
    | none =>
      refine ⟨fun _ => [], fun _ => [], ?_, ?_⟩
      · intro f hf
        exact nomatch hf
      · intro _ _
        rfl
    | some f =>
      obtain ⟨cv, cv', bs, -, hccv, -, -, hstrip⟩ := hposF t f hft
      obtain ⟨pps, lvls, hFD⟩ := formerData_of hμ mp hccv hstrip
      exact ⟨pps, lvls, (fun f' hf' => by obtain rfl := Option.some.inj hf'; exact hFD),
        fun hn => nomatch hn⟩
  let ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm) := fun t => (hFDex t).choose
  let lvlsF : Nat → (Name → Nat) → List Nat := fun t => (hFDex t).choose_spec.choose
  have hFDF : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      FormerData mp.base2 f.cvTa (p.toBlock.nP + f.nIdx) f.s (ppsF t) (lvlsF t) :=
    fun t => (hFDex t).choose_spec.choose_spec.1
  have hppsNone : ∀ t : Nat, fms[t]? = none → ∀ ψ : Name → Nat, ppsF t ψ = [] :=
    fun t => (hFDex t).choose_spec.choose_spec.2
  -- every member is stored at the formers' environment with the
  -- block's EMPTY capability record
  have hfindF : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      (ConLeche.consMutualFormers fms env).find? f.cvTa.name
        = some (.indInfo f.cvTa {}) :=
    fun t f hf => consMutualFormers_find?_self (List.mem_of_getElem? hf) hndF
  -- the cross-member checks: one result sort for the whole block
  have hcrossAll := mutualCrossChecks_all hcross
  have hsEq : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      ∀ ψ : Name → Nat, f.s.eval ψ = f₀.s.eval ψ := fun t f hf ψ =>
    Level.isEquiv_sound (hcrossAll f (List.mem_of_getElem? hf)).1 ψ
  have hFD : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      FormerData mp.base2 f.cvTa (p.toBlock.nP + f.nIdx) f₀.s (ppsF t) (lvlsF t) :=
    fun t f hf => FormerData.congr_sort (hFDF t f hf) (hsEq t f hf)
  -- **the chain-free first pass**: the members consed with the sum
  -- route's chain-free towers.  The constructors' types mention the
  -- members, so their data can only be read at the environment holding
  -- all `k` formers; the block's chains are read there, and the real
  -- member leaves are built from them
  have hmem₀ : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      f.cvTa.levelParams = p.toBlock.lps ∧
      FormerData mp.base2 f.cvTa (p.toBlock.nP + f.nIdx) f₀.s (ppsF t) (lvlsF t) ∧
      (∀ ψ : Name → Nat,
        Term.bvarsBelow 0 (sumTyAV (f₀.s.eval ψ) (ppsF t ψ) ([] : List (List AnnotTerm))).erase) ∧
      (∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ p.toBlock.lps, ψ₁ q = ψ₂ q) →
        sumTyAV (f₀.s.eval ψ₁) (ppsF t ψ₁) [] = sumTyAV (f₀.s.eval ψ₂) (ppsF t ψ₂) []) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V),
        WellDenotedV V ρ (sumTyAV (f₀.s.eval ψ) (ppsF t ψ) [])) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V),
        interp V ρ (sumTyAV (f₀.s.eval ψ) (ppsF t ψ) [])
          ∈ˢ interp V ρ (mkPisAV (ppsF t ψ) (.sort (f₀.s.eval ψ)))) := by
    intro t f hft
    have hFDt := hFD t f hft
    have hwalk := formerWalksS (V := V) hFDt (Fss := fun _ => [])
      (fun ψ ρ _ => ⟨(fun Fs hFs => nomatch hFs), (fun Fs hFs => nomatch hFs)⟩)
    refine ⟨hlpsF t f hft, hFDt, ?_, ?_, ?_, ?_⟩
    · intro ψ
      exact sumTyAV_below (hFDt.below ψ) (fun Fs hFs => nomatch hFs)
    · intro ψ₁ ψ₂ hφ
      obtain ⟨hp, hw⟩ := hFDt.params ψ₁ ψ₂ (by rw [hlpsF t f hft]; exact hφ)
      show sumTyAV _ _ _ = sumTyAV _ _ _
      rw [hp, hw]
    · exact fun ψ ρ => sumTyAV_wellDenotedV (hwalk ψ ρ).1 (hwalk ψ ρ).2
    · exact fun ψ ρ => sumTyAV_mem (hwalk ψ ρ).1
  obtain ⟨mp₀, hleaf₀, hoff₀⟩ := stageMembersG mp hE hformers hndF hmem₀
  -- the block's readers: the member table, the constructors' members
  -- and the classified kinds
  have hk0 : 0 < fms.length := by
    have := (List.getElem?_eq_some_iff.mp hf0).1; omega
  have hfmGet : ∀ t : Nat, t < fms.length → fms[t]? = some (fms.getD t default) := by
    intro t ht
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]; rfl
  have hmemT : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      mutualNameOf p.toBlock.members3 t = f.cvTa.name ∧
      mutualNIdxOf p.toBlock.members3 t = f.nIdx := by
    intro t f hft
    obtain ⟨cv, cv', bs, hl, hccv, hn1, -, -⟩ := hposF t f hft
    obtain ⟨-, -, -, -, -, -, _, _, _, -, -, -, -, -, hty⟩ := ConLeche.checkConstantVal_inv hccv
    have htk : t < p.toBlock.k := by
      show t < p.toBlock.formers.length
      exact (List.getElem?_eq_some_iff.mp hl).1
    have hgetD : p.toBlock.formers.getD t default = (cv, f.nIdx) := by
      rw [List.getD_eq_getElem?_getD, hl]; rfl
    rw [mutualNameOf_members3 htk, mutualNIdxOf_members3 htk, hgetD]
    exact ⟨by rw [hty]; exact hn1.symm, rfl⟩
  -- the constructors, positionally, and their classified kinds
  obtain ⟨hlenA, hlenS, hallC⟩ := ConLeche.checkMutualCtors_inv hctors
  obtain ⟨hkindsM, -, -, hlenK⟩ := ConLeche.classifyMutualKinds_inv hkinds
  obtain ⟨hlenAK, hfoJ⟩ := mutualFieldsOk_inv hfo
  have hctorGet : ∀ (J : Nat), J < ctorsA.length →
      p.toBlock.ctors[J]? = some (p.toBlock.ctors.getD J default) := by
    intro J hJ
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [← hlenA]; exact hJ)]; rfl
  have hmotLt : ∀ (J : Nat), J < ctorsA.length →
      (p.toBlock.ctors.getD J default).member < fms.length := by
    intro J hJ
    have hall : (p.toBlock.ctors.all fun c => decide (c.member < p.toBlock.k)) = true := hmemLt
    have := List.all_eq_true.mp hall (p.toBlock.ctors.getD J default)
      (List.mem_of_getElem? (hctorGet J hJ))
    simp only [decide_eq_true_eq] at this
    show _ < fms.length
    rw [hlenFms]
    exact this
  have hrunC : ∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA →
      cA.2 = (p.toBlock.ctors.getD J default).nF ∧
      ∃ sorts : List Level, sortss[J]? = some sorts ∧
        ConLeche.checkMutualCtor (ConLeche.fueledOps μ F) (ConLeche.consMutualFormers fms env)
          p.toBlock.memberNames
          (fms.getD (p.toBlock.ctors.getD J default).member default).cvTa.name p.toBlock.lps
          p.toBlock.nP (fms.getD (p.toBlock.ctors.getD J default).member default).nIdx
          (fms.getD (p.toBlock.ctors.getD J default).member default).s
          (Level.isEquiv f₀.s Level.zero == some true) p.toBlock.large
          (p.toBlock.ctors.getD J default).cv cA.2
          (fms.getD (p.toBlock.ctors.getD J default).member default).cvTa = .ok (cA.1, sorts) := by
    intro J cA hJ
    have hJl : J < ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
    obtain ⟨hnF, sorts, hsj, hrun⟩ := hallC J _ cA (hctorGet J hJl) hJ
    exact ⟨hnF, sorts, hsj, by rw [hnF]; exact hrun⟩
  -- the kinds: classified on the stored constructors, re-checked in
  -- the opened form, and their targets are members of the block
  have hksJ : ∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA →
      (kinds.getD J []).length = cA.2 ∧
      ConLeche.mutualOpenedOk env p.toBlock.members3 p.toBlock.lps p.toBlock.nP cA.1.type cA.2
        (kinds.getD J []) = true ∧
      ∀ i, tgtAt (kinds.getD J []) i < fms.length := by
    intro J cA hJ
    obtain ⟨ks, hks, hlenks, hopened⟩ := hfoJ J cA hJ
    have hksD : kinds.getD J [] = ks := by rw [List.getD_eq_getElem?_getD, hks]; rfl
    obtain ⟨ks', hks', hkJ⟩ := mapM_option_getElem? hkindsM J cA hJ
    obtain rfl := Option.some.inj (hks.symm.trans hks')
    refine ⟨by rw [hksD]; exact hlenks, by rw [hksD]; exact hopened, fun i => ?_⟩
    rw [hksD]
    rcases mutualCtorKinds_tgt hkJ i with h0 | ⟨x, hx, hxe⟩
    · rw [h0]; exact hk0
    · rw [← hxe, hlenFms]; exact members3_mem_lt hx
  -- the members' data at the formers' carrier: their types resolve
  -- before the block, so they cross the loop untouched
  have hagree₀ : ∀ n : Name, (env.find? n).isSome = true →
      mp.base2.acval n = mp₀.base2.acval n := by
    intro n hn
    refine (hoff₀ n (fun t f hft hh => ?_)).symm
    rw [hh, hfreshF t f hft] at hn
    exact nomatch hn
  obtain ⟨hFP, hLG, hPJ⟩ := consMutualFormers_extend (fms := fms) (env := env)
    (fun f hf => by obtain ⟨t, ht⟩ := List.getElem?_of_mem hf; exact hfreshF t f ht) hndF
  have hcbF : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      ConstsBound env f.cvTa.type := by
    intro t f hft
    obtain ⟨cv, cv', bs, -, hccv, -, -, -⟩ := hposF t f hft
    obtain ⟨-, -, -, -, -, -, _, _, _, -, -, htr, -, -, hty⟩ := ConLeche.checkConstantVal_inv hccv
    exact constsBound_of_constsResolve _ (by rw [hty]; exact htr)
  have hFD₁ : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      FormerData mp₀.base2 f.cvTa (p.toBlock.nP + f.nIdx) f₀.s (ppsF t) (lvlsF t) :=
    fun t f hft => FormerData.crossEnv (hFD t f hft) (hcbF t f hft) hFP hLG hPJ hagree₀
  -- **the constructors' data**, at the formers' carrier
  have hCDexAt : ∀ mpX : EnvModelM V μ (ConLeche.consMutualFormers fms env),
      ∀ J : Nat, ∃ (idxF : List Expr)
      (dsF : (Name → Nat) → List (Nat × Nat × AnnotTerm))
      (esF : (Name → Nat) → List AnnotTerm) (srcsF : List (Option Nat))
      (fvsPF xFvsF : List Expr) (xrestF : Expr)
      (eissF : (Name → Nat) → List (List AnnotTerm))
      (tssF : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))),
      ∀ cA : ConstantVal × Nat, ctorsA[J]? = some cA →
        MutualCtorDataI mpX.base2 env p.toBlock.members3
          (fms.getD (p.toBlock.ctors.getD J default).member default).cvTa.name
          p.toBlock.lps cA.1 p.toBlock.nP cA.2
          (fms.getD (p.toBlock.ctors.getD J default).member default).nIdx
          (fms.getD (p.toBlock.ctors.getD J default).member default).s
          (Level.isEquiv f₀.s Level.zero == some true) p.toBlock.large
          idxF dsF esF srcsF (kinds.getD J []) fvsPF xFvsF xrestF eissF tssF := by
    intro mpX J
    cases hJ : ctorsA[J]? with
    | none =>
      exact ⟨[], fun _ => [], fun _ => [], [], [], [], default, fun _ => [], fun _ => [],
        fun cA hcA => nomatch hcA⟩
    | some cA =>
      have hJl : J < ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
      obtain ⟨hnF, sorts, hsj, hrun⟩ := hrunC J cA hJ
      obtain ⟨hlenks, hopened, htgt⟩ := hksJ J cA hJ
      have hmt : (p.toBlock.ctors.getD J default).member < fms.length := hmotLt J hJl
      have hmtG := hfmGet _ hmt
      obtain ⟨bsT, hstripT⟩ := hstripF _ _ hmtG
      have hfM : ∀ i, i < cA.2 →
          (kindAt (kinds.getD J []) i = .recursive ∨
            kindAt (kinds.getD J []) i = .reflexive) →
          ∃ (ci : ConstantInfo) (bs' : List (Expr × BinderMeta)) (s' : Level),
            (ConLeche.consMutualFormers fms env).find?
              (mutualNameOf p.toBlock.members3 (tgtAt (kinds.getD J []) i)) = some ci ∧
            ci.toConstantVal.levelParams = p.toBlock.lps ∧
            ci.toConstantVal.type.stripPis (p.toBlock.nP +
                mutualNIdxOf p.toBlock.members3 (tgtAt (kinds.getD J []) i))
              = some (bs', .sort s') ∧
            ∀ ψ : Name → Nat,
              s'.eval ψ
                = (fms.getD (p.toBlock.ctors.getD J default).member default).s.eval ψ := by
        intro i hi _
        have ht := htgt i
        have htG := hfmGet _ ht
        obtain ⟨hnm, hni⟩ := hmemT _ _ htG
        obtain ⟨bs', hs'⟩ := hstripF _ _ htG
        refine ⟨.indInfo (fms.getD (tgtAt (kinds.getD J []) i) default).cvTa {}, bs', _,
          by rw [hnm]; exact hfindF _ _ htG, hlpsF _ _ htG, by rw [hni]; exact hs', fun ψ => ?_⟩
        rw [hsEq _ _ htG ψ, hsEq _ _ hmtG ψ]
      obtain ⟨idxF, dsF, esF, srcsF, fvsPF, xFvsF, xrestF, eissF, tssF, hD⟩ :=
        mutualCtorData_of hμ mpX hrun (hfindF _ _ hmtG) (hlpsF _ _ hmtG) hstripT
          hlenks hfM hopened
      exact ⟨idxF, dsF, esF, srcsF, fvsPF, xFvsF, xrestF, eissF, tssF, fun cA' hcA' => by
        obtain rfl := Option.some.inj hcA'; exact hD⟩
  -- **the cross-member parameter identification** (`mutualCrossChecks`'
  -- `isDefEq`, semantically): every member's parameter frame is the
  -- first member's
  have hopened₀ : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      ∃ tq : List Expr × Expr, ConLeche.openPisAtFvars p.toBlock.nP f.cvTa.type 0 = some tq ∧
        ConLeche.mutualDomsOk (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
          (ConLeche.consMutualFormers fms env) tq.1 (tq₀.1.map Expr.fvarTypeD) p.toBlock.nP
          = .ok () := fun t f hft => (hcrossAll f (List.mem_of_getElem? hft)).2
  have hOpenedAt : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      ∀ (ψ : Name → Nat) (tfvs : List Expr) (trest : Expr),
        ConLeche.openPisAtFvars p.toBlock.nP f.cvTa.type 0 = some (tfvs, trest) →
        Opened mp₀.base2 ψ p.toBlock.nP f.cvTa.type tfvs trest
          ((((ppsF t ψ).take p.toBlock.nP).map (·.2.2)).reverse)
          (mkPisAV ((ppsF t ψ).drop p.toBlock.nP) (.sort (f₀.s.eval ψ))) := by
    intro t f hft ψ tfvs trest hop
    have hFDt := hFD₁ t f hft
    obtain ⟨hTf, -, -, hTb, -⟩ :=
      mp₀.base2.wf _ (ConLeche.Semantics.Env.find?_mem (hfindF t f hft))
    simp only [ConstantInfo.toConstantVal] at hTf hTb
    obtain ⟨Γt, Rt, hteleT, hT⟩ := opened_of hop hTf hTb (hFDt.read ψ) (hFDt.okTy ψ)
    obtain ⟨pps', hst', hΓt⟩ := stripPisAV_of_piTeleAV hteleT
    have hst'' := stripPisAV_mkPisAV_take p.toBlock.nP (ppsF t ψ)
      (AnnotTerm.sort (f₀.s.eval ψ)) (by rw [hFDt.len ψ]; omega)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hst'.symm.trans hst''))
    subst hΓt
    exact hT
  have hframeM : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      ∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat V (((ppsF t ψ).take p.toBlock.nP).map (·.2.2)).reverse ρ ↔
          Sat V (((ppsF 0 ψ).take p.toBlock.nP).map (·.2.2)).reverse ρ := by
    intro t f hft ψ ρ
    obtain ⟨tq, hopT, hdoms⟩ := hopened₀ t f hft
    have hpins := ConLeche.mutualDomsOk_inv hdoms
    have hT := hOpenedAt 0 f₀ hf0 ψ tq₀.1 tq₀.2 (by cases tq₀; exact htq0)
    have hC := hOpenedAt t f hft ψ tq.1 tq.2 (by cases tq; exact hopT)
    have hpf := paramFrames (nF := 0) (claimsAt_of hμ mp₀ ψ F) hT hC (fun i hi => by
      obtain ⟨a, b, ha, hb, hdeq⟩ := hpins i hi
      rw [List.getElem?_map] at hb
      obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.mp hb
      exact ⟨a, b', ha, hb', hdeq⟩)
    have h := (hpf p.toBlock.nP (Nat.le_refl _)).1 ρ
    rw [Nat.add_zero, Nat.sub_self, List.drop_zero, List.drop_zero] at h
    exact h
  -- **the parameter DOMAINS**, pointwise (`paramFrames`' second
  -- component): member `t`'s `i`-th parameter binder and member `0`'s
  -- interpret alike under every frame satisfying the earlier ones —
  -- what identifies the two members' leaves (`hleafM`)
  have hdomM : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      ∀ (ψ : Name → Nat) (i : Nat), i < p.toBlock.nP → ∀ ρ : Nat → V,
        Sat V (((((ppsF t ψ).take p.toBlock.nP).map (·.2.2)).take i).reverse) ρ →
        interp V ρ ((((ppsF t ψ).take p.toBlock.nP).map (·.2.2)).getD i default)
          = interp V ρ ((((ppsF 0 ψ).take p.toBlock.nP).map (·.2.2)).getD i default) := by
    intro t f hft ψ i hi ρ hρ
    obtain ⟨tq, hopT, hdoms⟩ := hopened₀ t f hft
    have hpins := ConLeche.mutualDomsOk_inv hdoms
    have hT := hOpenedAt 0 f₀ hf0 ψ tq₀.1 tq₀.2 (by cases tq₀; exact htq0)
    have hC := hOpenedAt t f hft ψ tq.1 tq.2 (by cases tq; exact hopT)
    have hpf := paramFrames (nF := 0) (claimsAt_of hμ mp₀ ψ F) hT hC (fun j hj => by
      obtain ⟨a, b, ha, hb, hdeq⟩ := hpins j hj
      rw [List.getElem?_map] at hb
      obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.mp hb
      exact ⟨a, b', ha, hb', hdeq⟩)
    have hlenT : ((((ppsF t ψ).take p.toBlock.nP).map (·.2.2))).length = p.toBlock.nP := by
      rw [List.length_map, List.length_take, (hFD₁ t f hft).len ψ]; omega
    have hlen0 : ((((ppsF 0 ψ).take p.toBlock.nP).map (·.2.2))).length = p.toBlock.nP := by
      rw [List.length_map, List.length_take, (hFD₁ 0 f₀ hf0).len ψ]; omega
    have h := (hpf i (Nat.le_of_lt hi)).2 hi ρ (by
      rw [Nat.add_zero, reverse_drop_eq hlenT (Nat.le_of_lt hi)]
      exact hρ)
    rw [Nat.add_zero, reverse_getD_eq hlenT hi, reverse_getD_eq hlen0 hi] at h
    exact h
  -- **the block's index telescopes and the tag's universe**: the tag
  -- is the tagged union of the members' index towers, and its universe
  -- is the join of the binders' own (`FormerData`'s `lvls`)
  have hframeAll : ∀ (t t' : Nat) (f f' : MutualFormerA), fms[t]? = some f → fms[t']? = some f' →
      ∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat V (((ppsF t ψ).take p.toBlock.nP).map (·.2.2)).reverse ρ →
        Sat V (((ppsF t' ψ).take p.toBlock.nP).map (·.2.2)).reverse ρ :=
    fun t t' f f' hft hft' ψ ρ h => (hframeM t' f' hft' ψ ρ).mpr ((hframeM t f hft ψ ρ).mp h)
  let Wf : (Name → Nat) → Nat := fun ψ =>
    1 + ((List.range fms.length).map fun q => (lvlsF q ψ).foldl max 0).foldl max 0
  let Idssf : (Name → Nat) → List (List AnnotTerm) := fun ψ =>
    (List.range fms.length).map fun q => ((ppsF q ψ).drop p.toBlock.nP).map (·.2.2)
  have hIdssGet : ∀ (ψ : Name → Nat) (t : Nat), t < fms.length →
      (Idssf ψ)[t]? = some (((ppsF t ψ).drop p.toBlock.nP).map (·.2.2)) := by
    intro ψ t ht
    show ((List.range fms.length).map _)[t]? = _
    rw [List.getElem?_map, List.getElem?_range ht]
    rfl
  have hIdssLen : ∀ ψ : Name → Nat, (Idssf ψ).length = fms.length := by
    intro ψ; show ((List.range fms.length).map _).length = _; simp
  have hWge : ∀ (ψ : Name → Nat) (t j : Nat), t < fms.length →
      (lvlsF t ψ).getD j 0 ≤ Wf ψ := by
    intro ψ t j ht
    have h1 : (lvlsF t ψ).getD j 0 ≤ (lvlsF t ψ).foldl max 0 := by
      by_cases hj : j < (lvlsF t ψ).length
      · refine le_foldl_max _ _ _ ?_
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
        exact List.getElem_mem hj
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        exact Nat.zero_le _
    have h2 : (lvlsF t ψ).foldl max 0
        ≤ ((List.range fms.length).map fun q => (lvlsF q ψ).foldl max 0).foldl max 0 :=
      le_foldl_max _ _ _ (List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩)
    show _ ≤ 1 + _
    omega
  have hIdxAll : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      ∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat V (((ppsF t ψ).take p.toBlock.nP).map (·.2.2)).reverse ρ →
        TagOk (Wf ψ) ρ (Idssf ψ) ∧ ∀ Ids ∈ Idssf ψ, FieldsValid ρ Ids := by
    intro t f hft ψ ρ hρ
    have hpair : ∀ Ids ∈ Idssf ψ, IdxOk (Wf ψ) ρ Ids ∧ FieldsValid ρ Ids := by
      intro Ids hIds
      obtain ⟨t', ht', rfl⟩ := List.mem_map.mp (show Ids ∈ (List.range fms.length).map
        (fun q => ((ppsF q ψ).drop p.toBlock.nP).map (·.2.2)) from hIds)
      have ht'l : t' < fms.length := List.mem_range.mp ht'
      exact formerIdxOk (hFD₁ t' _ (hfmGet t' ht'l))
        (fun j _ => hWge ψ t' (p.toBlock.nP + j) ht'l) ρ
        (hframeAll t t' f _ hft (hfmGet t' ht'l) ψ ρ hρ)
    exact ⟨⟨show 1 + _ ≠ 0 by omega, fun Ids hIds => (hpair Ids hIds).1⟩,
      fun Ids hIds => (hpair Ids hIds).2⟩
  -- the constructors' data and the block's chain lists
  have hCDex : ∀ J : Nat, _ := hCDexAt mp₀
  let idxF : Nat → List Expr := fun J => (hCDex J).choose
  let dsF₀ : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm) := fun J =>
    (hCDex J).choose_spec.choose
  let esF₀ : Nat → (Name → Nat) → List AnnotTerm := fun J =>
    (hCDex J).choose_spec.choose_spec.choose
  let srcsF₀ : Nat → List (Option Nat) := fun J =>
    (hCDex J).choose_spec.choose_spec.choose_spec.choose
  let fvsPF₀ : Nat → List Expr := fun J =>
    (hCDex J).choose_spec.choose_spec.choose_spec.choose_spec.choose
  let xFvsF₀ : Nat → List Expr := fun J =>
    (hCDex J).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let xrestF₀ : Nat → Expr := fun J =>
    (hCDex J).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let eissF₀ : Nat → (Name → Nat) → List (List AnnotTerm) := fun J =>
    (hCDex J).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let tssF₀ : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)) := fun J =>
    (hCDex J).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  have hCD₀ : ∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA →
      MutualCtorDataI mp₀.base2 env p.toBlock.members3
        (fms.getD (p.toBlock.ctors.getD J default).member default).cvTa.name
        p.toBlock.lps cA.1 p.toBlock.nP cA.2
        (fms.getD (p.toBlock.ctors.getD J default).member default).nIdx
        (fms.getD (p.toBlock.ctors.getD J default).member default).s
        (Level.isEquiv f₀.s Level.zero == some true) p.toBlock.large
        (idxF J) (dsF₀ J) (esF₀ J) (srcsF₀ J) (kinds.getD J []) (fvsPF₀ J) (xFvsF₀ J)
        (xrestF₀ J) (eissF₀ J) (tssF₀ J) := fun J =>
    (hCDex J).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
  -- the block's chain lists (`MutualChains.lean`'s spellings)
  let ksF : Nat → List (RecFieldKind × Nat) := fun J => kinds.getD J []
  let nFs : Nat → Nat := fun J => (ctorsA.getD J default).2
  let memF : Nat → Nat := fun J => (p.toBlock.ctors.getD J default).member
  let rssf : List (List Bool) := mutRss ctorsA.length ksF
  let Fss0f : (Name → Nat) → List (List AnnotTerm) := fun ψ =>
    mutFss0 p.toBlock.nP ctorsA.length dsF₀ ksF nFs ψ
  let tlssf : (Name → Nat) → List (List (List (Nat × Nat × AnnotTerm))) := fun ψ =>
    mutTlss ctorsA.length tssF₀ ψ
  let Essf : (Name → Nat) → List (List AnnotTerm) := fun ψ =>
    mutEss' (n := ctorsA.length) (Wf ψ) (Idssf ψ) memF nFs esF₀ ψ
  let Eissf : (Name → Nat) → List (List (List AnnotTerm)) := fun ψ =>
    mutEiss' (n := ctorsA.length) (Wf ψ) (Idssf ψ) ksF nFs tssF₀ eissF₀ ψ
  have hcAGet : ∀ J : Nat, J < ctorsA.length → ctorsA[J]? = some (ctorsA.getD J default) := by
    intro J hJ
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hJ]; rfl
  -- **the block's chain facts**, at every member's parameter frame
  have hChainJ : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      ∀ (ψ : Name → Nat) (ρp : Nat → V),
        Sat V (((ppsF t ψ).take p.toBlock.nP).map (·.2.2)).reverse ρp →
        ∀ J : Nat, J < ctorsA.length →
          ChainFacts (Wf ψ) (f₀.s.eval ψ) p.toBlock.nP (nFs J) ρp
              (auxIds (Wf ψ) (Idssf ψ)) (kindsOf (ksF J)) ((tlssf ψ).getD J [])
              ((Fss0f ψ).getD J []) ((Eissf ψ).getD J []) ((Essf ψ).getD J []) ∧
            ChainValidFacts p.toBlock.nP (nFs J) ρp (kindsOf (ksF J)) ((tlssf ψ).getD J [])
              ((Fss0f ψ).getD J []) ((Eissf ψ).getD J []) ((Essf ψ).getD J []) := by
    intro t f hft ψ ρp hρ J hJl
    have hJ : ctorsA[J]? = some (ctorsA.getD J default) := hcAGet J hJl
    have hmt : memF J < fms.length := hmotLt J hJl
    have hmtG := hfmGet _ hmt
    have hD := hCD₀ J _ hJ
    obtain ⟨hnF, sorts, hsj, hrun⟩ := hrunC J _ hJ
    have hFDm := FormerData.congr_sort (hFD₁ _ _ hmtG) (fun ψ' => (hsEq _ _ hmtG ψ').symm)
    have hleafTm : ∀ ψ' : Name → Nat, ∃ B,
        mp₀.base2.acval (fms.getD (memF J) default).cvTa.name ψ'
          = mkLamsC ((fms.getD (memF J) default).s.eval ψ' + 1) (ppsF (memF J) ψ') B := by
      intro ψ'
      refine ⟨sumBodyAV (f₀.s.eval ψ') [], ?_⟩
      rw [hsEq _ _ hmtG ψ', hleaf₀ _ _ hmtG]
      rfl
    have hPropJ : (Level.isEquiv f₀.s Level.zero == some true) = true →
        ∀ ψ' : Name → Nat, Level.eval ψ' (fms.getD (memF J) default).s
          = Level.eval ψ' Level.zero := by
      intro hp ψ'
      rw [hsEq _ _ hmtG ψ']
      exact Level.isEquiv_sound (beq_iff_eq.mp hp) ψ'
    have hρJ : Sat V (((ppsF (memF J) ψ).take p.toBlock.nP).map (·.2.2)).reverse ρp :=
      hframeAll t (memF J) f _ hft hmtG ψ ρp hρ
    obtain ⟨hTagJ, hVJ⟩ := hIdxAll t f hft ψ ρp hρ
    have hTgtJ : ∀ i, i < (ctorsA.getD J default).2 →
        (kindAt (ksF J) i = .recursive ∨ kindAt (ksF J) i = .reflexive) →
        ∃ (ppsT : List (Nat × Nat × AnnotTerm)) (B : AnnotTerm),
          ppsT.length = p.toBlock.nP
            + mutualNIdxOf p.toBlock.members3 (tgtAt (ksF J) i) ∧
          mp₀.base2.acval (mutualNameOf p.toBlock.members3 (tgtAt (ksF J) i)) ψ
            = mkLamsC ((fms.getD (memF J) default).s.eval ψ + 1) ppsT B ∧
          (Idssf ψ)[tgtAt (ksF J) i]? = some ((ppsT.drop p.toBlock.nP).map (·.2.2)) := by
      intro i hi _
      obtain ⟨-, -, htgt⟩ := hksJ J _ hJ
      have htl := htgt i
      have htG := hfmGet _ htl
      obtain ⟨hnm, hni⟩ := hmemT _ _ htG
      refine ⟨ppsF (tgtAt (ksF J) i) ψ, sumBodyAV (f₀.s.eval ψ) [], ?_, ?_, hIdssGet ψ _ htl⟩
      · rw [hni]; exact (hFD₁ _ _ htG).len ψ
      · rw [hnm, hsEq _ _ hmtG ψ, hleaf₀ _ _ htG]
        rfl
    have hC := mutualChainFacts_at hμ mp₀ hrun (hfindF _ _ hmtG) hPropJ hFDm hleafTm hD ψ ρp
      hρJ hTagJ (hIdssGet ψ _ hmt) hTgtJ
    have hCV := mutualChainValidFacts_at (W := Wf ψ) hμ mp₀ hrun (hfindF _ _ hmtG) hPropJ hFDm
      hleafTm hD ψ ρp hρJ hVJ (hIdssGet ψ _ hmt)
      (fun i hi _ => by
        obtain ⟨-, -, htgt⟩ := hksJ J _ hJ
        exact ⟨_, hIdssGet ψ _ (htgt i)⟩)
    have hEL : (eissF₀ J ψ).length = nFs J := hD.eissLen ψ
    have hgetT : (tlssf ψ).getD J [] = tssF₀ J ψ := mutTlss_getD hJl
    have hgetF : (Fss0f ψ).getD J []
        = shadowFs p.toBlock.nP (kindsOf (ksF J)) (nFs J)
            (((dsF₀ J ψ).drop p.toBlock.nP).map (·.2.2)) := mutFss0_getD hJl
    have hgetE : (Essf ψ).getD J []
        = [tagTupleAV (Wf ψ) (memF J) (nFs J) (Idssf ψ) (esF₀ J ψ)] := mutEss'_getD hJl
    have hgetI : (Eissf ψ).getD J []
        = (List.range (nFs J)).map fun i =>
            [tagTupleAV (Wf ψ) (tgtAt (ksF J) i) (i + ((tssF₀ J ψ).getD i []).length)
              (Idssf ψ) ((eissF₀ J ψ).getD i [])] := mutEiss'_getDJ hJl hEL
    rw [hgetT, hgetF, hgetE, hgetI, hsEq _ _ hmtG ψ] at *
    exact ⟨hC, hCV⟩
  -- **`MemberChainsOk`**, at every member
  have hXAll : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      ∀ (ψ : Name → Nat) (ρp : Nat → V),
        Sat V (((ppsF t ψ).take p.toBlock.nP).map (·.2.2)).reverse ρp →
        XChainsOk (Wf ψ) (f₀.s.eval ψ) ρp (auxIds (Wf ψ) (Idssf ψ)) rssf (tlssf ψ) (Eissf ψ)
            (Fss0f ψ) (Essf ψ) ∧
          ∀ X, X ∈ˢ lfpFamSpace V (f₀.s.eval ψ) (idxSet (Wf ψ) ρp (auxIds (Wf ψ) (Idssf ψ))) →
            ∀ τ, τ ∈ˢ idxSet (Wf ψ) ρp (auxIds (Wf ψ) (Idssf ψ)) →
              SumFieldsValid (cons τ (cons X ρp))
                (chainsXI (Wf ψ) (auxIds (Wf ψ) (Idssf ψ))
                  (auxIds (Wf ψ) (Idssf ψ)).length rssf (tlssf ψ) (Eissf ψ) (Fss0f ψ)
                  (Essf ψ)) := by
    intro t f hft ψ ρp hρ
    obtain ⟨hTagJ, hVJ⟩ := hIdxAll t f hft ψ ρp hρ
    have hFs₀ : ∀ J : Nat, J < ctorsA.length → ((Fss0f ψ).getD J []).length = nFs J := by
      intro J hJ
      rw [mutFss0_getD hJ]
      exact shadowFs_length
    exact xChainsOk_of (V := V) (u := Wf ψ) (w := f₀.s.eval ψ)
      (nP := p.toBlock.nP) (n := ctorsA.length) (Ids := auxIds (Wf ψ) (Idssf ψ))
      (ksF := fun J => kindsOf (ksF J)) (rss := rssf) (tlss := tlssf ψ) (Eiss := Eissf ψ)
      (Fss := Fss0f ψ) (Ess := Essf ψ)
      (auxIds_idxOk hTagJ) (auxIds_fieldsValid hVJ)
      (by show ((List.range ctorsA.length).map _).length = _; simp)
      (fun J hJ => mutRss_getD hJ)
      (fun J hJ => by rw [hFs₀ J hJ]; exact (hChainJ t f hft ψ ρp hρ J hJ).1)
      (fun J hJ => by rw [hFs₀ J hJ]; exact (hChainJ t f hft ψ ρp hρ J hJ).2)
  have hMCO : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      MemberChainsOk V p.toBlock.nP t f₀.s Wf Idssf rssf tlssf Eissf Fss0f Essf (ppsF t) := by
    intro t f hft
    have hlt : t < fms.length := (List.getElem?_eq_some_iff.mp hft).1
    refine ⟨fun ψ => hIdssGet ψ t hlt, fun ψ ρp hρ => ?_⟩
    obtain ⟨hTagJ, hVJ⟩ := hIdxAll t f hft ψ ρp hρ
    obtain ⟨hX, hvalid⟩ := hXAll t f hft ψ ρp hρ
    exact ⟨hTagJ, hVJ, hX.hok, hvalid⟩
  -- the level-parameter dependence of the block's data
  have hlpsC : ∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA →
      cA.1.levelParams = p.toBlock.lps := by
    intro J cA hJ
    have hJl : J < ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
    obtain ⟨-, sorts, -, hrun⟩ := hrunC J cA hJ
    obtain ⟨⟨ty', hccv⟩, -, -⟩ := ConLeche.checkMutualCtor_shape hrun
    obtain ⟨-, -, -, -, -, -, _, _, _, -, -, -, -, -, hty⟩ := ConLeche.checkConstantVal_inv hccv
    have hall : (p.toBlock.ctors.all fun c => c.cv.levelParams == p.toBlock.lps) = true := by
      simpa using (Bool.and_eq_true _ _ |>.mp hlpsAll).2
    have hthis := List.all_eq_true.mp hall _ (List.mem_of_getElem? (hctorGet J hJl))
    rw [hty]
    simpa using hthis
  have hCDparams : ∀ J : Nat, J < ctorsA.length → ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ q ∈ p.toBlock.lps, ψ₁ q = ψ₂ q) →
      dsF₀ J ψ₁ = dsF₀ J ψ₂ ∧ esF₀ J ψ₁ = esF₀ J ψ₂ ∧ eissF₀ J ψ₁ = eissF₀ J ψ₂ ∧
        tssF₀ J ψ₁ = tssF₀ J ψ₂ := by
    intro J hJl ψ₁ ψ₂ hφ
    have hJ := hcAGet J hJl
    have hD := hCD₀ J _ hJ
    have hφ' : ∀ q ∈ (ctorsA.getD J default).1.levelParams, ψ₁ q = ψ₂ q := by
      rw [hlpsC J _ hJ]; exact hφ
    obtain ⟨h1, h2⟩ := hD.params ψ₁ ψ₂ hφ'
    exact ⟨h1, h2, hD.eissParams ψ₁ ψ₂ hφ', hD.tssParams ψ₁ ψ₂ hφ'⟩
  have hppsPar : ∀ t : Nat, t < fms.length → ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ q ∈ p.toBlock.lps, ψ₁ q = ψ₂ q) →
      ppsF t ψ₁ = ppsF t ψ₂ ∧ lvlsF t ψ₁ = lvlsF t ψ₂ := by
    intro t ht ψ₁ ψ₂ hφ
    have hft := hfmGet t ht
    have hφ' : ∀ q ∈ (fms.getD t default).cvTa.levelParams, ψ₁ q = ψ₂ q := by
      rw [hlpsF t _ hft]; exact hφ
    exact ⟨((hFD t _ hft).params ψ₁ ψ₂ hφ').1, (hFD t _ hft).lvlsParams ψ₁ ψ₂ hφ'⟩
  have hParams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ p.toBlock.lps, ψ₁ q = ψ₂ q) →
      Wf ψ₁ = Wf ψ₂ ∧ Idssf ψ₁ = Idssf ψ₂ ∧ tlssf ψ₁ = tlssf ψ₂ ∧ Eissf ψ₁ = Eissf ψ₂ ∧
        Fss0f ψ₁ = Fss0f ψ₂ ∧ Essf ψ₁ = Essf ψ₂ := by
    intro ψ₁ ψ₂ hφ
    have hW : Wf ψ₁ = Wf ψ₂ := by
      show 1 + ((List.range fms.length).map _).foldl max 0
        = 1 + ((List.range fms.length).map _).foldl max 0
      rw [List.map_congr_left (fun q hq => by
        rw [(hppsPar q (List.mem_range.mp hq) ψ₁ ψ₂ hφ).2])]
    have hI : Idssf ψ₁ = Idssf ψ₂ := by
      show (List.range fms.length).map _ = (List.range fms.length).map _
      exact List.map_congr_left (fun q hq => by
        rw [(hppsPar q (List.mem_range.mp hq) ψ₁ ψ₂ hφ).1])
    have hds : mutFss0 p.toBlock.nP ctorsA.length dsF₀ ksF nFs ψ₁
        = mutFss0 p.toBlock.nP ctorsA.length dsF₀ ksF nFs ψ₂ := by
      unfold mutFss0
      exact List.map_congr_left (fun J hJ => by
        rw [(hCDparams J (List.mem_range.mp hJ) ψ₁ ψ₂ hφ).1])
    have htl : mutTlss ctorsA.length tssF₀ ψ₁ = mutTlss ctorsA.length tssF₀ ψ₂ := by
      unfold mutTlss
      exact List.map_congr_left (fun J hJ => by
        rw [(hCDparams J (List.mem_range.mp hJ) ψ₁ ψ₂ hφ).2.2.2])
    have hes : mutEss0 ctorsA.length esF₀ ψ₁ = mutEss0 ctorsA.length esF₀ ψ₂ := by
      unfold mutEss0
      exact List.map_congr_left (fun J hJ => by
        rw [(hCDparams J (List.mem_range.mp hJ) ψ₁ ψ₂ hφ).2.1])
    have hei : mutEiss0 ctorsA.length eissF₀ ψ₁ = mutEiss0 ctorsA.length eissF₀ ψ₂ := by
      unfold mutEiss0
      exact List.map_congr_left (fun J hJ => by
        rw [(hCDparams J (List.mem_range.mp hJ) ψ₁ ψ₂ hφ).2.2.1])
    refine ⟨hW, hI, htl, ?_, hds, ?_⟩
    · show mutEiss' _ _ _ _ _ _ _ = mutEiss' _ _ _ _ _ _ _
      unfold mutEiss'
      rw [hW, hI, htl, hei]
    · show mutEss' _ _ _ _ _ _ = mutEss' _ _ _ _ _ _
      unfold mutEss'
      rw [hW, hI, hes]
  -- the block's data is bounded at the parameters
  have hIdsBelow : ∀ ψ : Name → Nat, ∀ Ids ∈ Idssf ψ, FieldsBelow p.toBlock.nP Ids := by
    intro ψ Ids hIds
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (show Ids ∈ (List.range fms.length).map
      (fun q => ((ppsF q ψ).drop p.toBlock.nP).map (·.2.2)) from hIds)
    have hql : q < fms.length := List.mem_range.mp hq
    have hh := (DomsBelow.drop p.toBlock.nP ((hFD q _ (hfmGet q hql)).below ψ)).fields
    rwa [Nat.zero_add] at hh
  have hchainBelow : ∀ ψ : Name → Nat, ∀ chain ∈ chainsXI (Wf ψ) (auxIds (Wf ψ) (Idssf ψ)) 1
      rssf (tlssf ψ) (Eissf ψ) (Fss0f ψ) (Essf ψ), FieldsBelow (p.toBlock.nP + 2) chain := by
    intro ψ
    refine chainsXI_below_of (u := Wf ψ) (nP := p.toBlock.nP) (nIdx := 1)
      (n := ctorsA.length) (Ids := auxIds (Wf ψ) (Idssf ψ)) (rss := rssf) (tlss := tlssf ψ)
      (Eiss := Eissf ψ) (Fss := Fss0f ψ) (Ess := Essf ψ)
      (show FieldsBelow p.toBlock.nP (auxIds (Wf ψ) (Idssf ψ)) from
        ⟨tagTyAV_below (hIdsBelow ψ), trivial⟩)
      (by show ((List.range ctorsA.length).map _).length = _; simp) ?_ ?_ ?_ ?_ ?_
    · intro J hJ i
      rw [mutTlss_getD hJ]
      exact (hCD₀ J _ (hcAGet J hJ)).tssBelow ψ i
    · intro J hJ i E hE
      have hEL : (eissF₀ J ψ).length = nFs J := (hCD₀ J _ (hcAGet J hJ)).eissLen ψ
      rw [mutTlss_getD hJ]
      by_cases hi : i < nFs J
      · rw [mutEiss'_getD hJ hi hEL, List.mem_singleton] at hE
        subst hE
        have hb := tagTupleAV_belowM (nP := p.toBlock.nP) (W := Wf ψ)
          (m := tgtAt (ksF J) i)
          (d := i + ((tssF₀ J ψ).getD i []).length) (hIdsBelow ψ) (fun E hE => by
            have hh := (hCD₀ J _ (hcAGet J hJ)).eissBelow ψ i E hE
            rwa [show p.toBlock.nP + i + ((tssF₀ J ψ).getD i []).length
              = p.toBlock.nP + (i + ((tssF₀ J ψ).getD i []).length) from by omega] at hh)
        rwa [show p.toBlock.nP + (i + ((tssF₀ J ψ).getD i []).length)
          = p.toBlock.nP + i + ((tssF₀ J ψ).getD i []).length from by omega] at hb
      · rw [mutEiss'_getDJ hJ hEL, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hi)] at hE
        exact nomatch hE
    · intro J hJ
      rw [mutFss0_getD hJ]
      refine shadowFs_below (show (((dsF₀ J ψ).drop p.toBlock.nP).map (·.2.2)).length = nFs J from
        by rw [List.length_map, List.length_drop, (hCD₀ J _ (hcAGet J hJ)).len ψ]
           show p.toBlock.nP + nFs J - p.toBlock.nP = nFs J
           omega) ?_
      have hh := (DomsBelow.drop p.toBlock.nP ((hCD₀ J _ (hcAGet J hJ)).below ψ)).fields
      rwa [Nat.zero_add] at hh
    · intro J hJ
      rw [mutEss'_getD hJ]
      rfl
    · intro J hJ E hE
      rw [mutEss'_getD hJ, List.mem_singleton] at hE
      subst hE
      rw [mutFss0_getD hJ, shadowFs_length]
      exact tagTupleAV_belowM (nP := p.toBlock.nP) (W := Wf ψ) (m := memF J) (d := nFs J)
        (hIdsBelow ψ) (fun E hE => (hCD₀ J _ (hcAGet J hJ)).belowE ψ E hE)
  -- **the formers' stage**: the members consed with their fibre leaves
  obtain ⟨mp₁, hleaf₁, hoff₁⟩ := stageMutualFormers hParams hIdsBelow hchainBelow mp hE hformers
    hndF (fun t f hft => ⟨hlpsF t f hft, hFD t f hft, hMCO t f hft⟩)
  have hagree₁ : ∀ n : Name, (env.find? n).isSome = true →
      mp₀.base2.acval n = mp₁.base2.acval n := by
    intro n hn
    have h0 := hoff₀ n (fun t f hft hh => by rw [hh, hfreshF t f hft] at hn; exact nomatch hn)
    have h1 := hoff₁ n (fun t f hft hh => by rw [hh, hfreshF t f hft] at hn; exact nomatch hn)
    rw [h0, h1]
  -- the constructors' data at the MEMBER LEAVES, identified with the
  -- chain-free pass's off the recursive and reflexive slots
  have hCDex₁ : ∀ J : Nat, _ := hCDexAt mp₁
  let idxF₁ : Nat → List Expr := fun J => (hCDex₁ J).choose
  let dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm) := fun J =>
    (hCDex₁ J).choose_spec.choose
  let esF : Nat → (Name → Nat) → List AnnotTerm := fun J =>
    (hCDex₁ J).choose_spec.choose_spec.choose
  let srcsF : Nat → List (Option Nat) := fun J =>
    (hCDex₁ J).choose_spec.choose_spec.choose_spec.choose
  let fvsPF : Nat → List Expr := fun J =>
    (hCDex₁ J).choose_spec.choose_spec.choose_spec.choose_spec.choose
  let xFvsF : Nat → List Expr := fun J =>
    (hCDex₁ J).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let xrestF : Nat → Expr := fun J =>
    (hCDex₁ J).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let eissF : Nat → (Name → Nat) → List (List AnnotTerm) := fun J =>
    (hCDex₁ J).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)) := fun J =>
    (hCDex₁ J).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  have hCD₁ : ∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA →
      MutualCtorDataI mp₁.base2 env p.toBlock.members3
        (fms.getD (p.toBlock.ctors.getD J default).member default).cvTa.name
        p.toBlock.lps cA.1 p.toBlock.nP cA.2
        (fms.getD (p.toBlock.ctors.getD J default).member default).nIdx
        (fms.getD (p.toBlock.ctors.getD J default).member default).s
        (Level.isEquiv f₀.s Level.zero == some true) p.toBlock.large
        (idxF₁ J) (dsF J) (esF J) (srcsF J) (kinds.getD J []) (fvsPF J) (xFvsF J)
        (xrestF J) (eissF J) (tssF J) := fun J =>
    (hCDex₁ J).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
  have hident : ∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA →
      idxF J = idxF₁ J ∧ fvsPF₀ J = fvsPF J ∧ xFvsF₀ J = xFvsF J ∧ xrestF₀ J = xrestF J ∧
      (∀ ψ : Name → Nat, esF₀ J ψ = esF J ψ) ∧
      (∀ ψ : Name → Nat, eissF₀ J ψ = eissF J ψ) ∧
      (∀ ψ : Name → Nat, tssF₀ J ψ = tssF J ψ) ∧
      ∀ (ψ : Name → Nat) (i : Nat), i < cA.2 → kindAt (ksF J) i ≠ .recursive →
        kindAt (ksF J) i ≠ .reflexive →
        ((dsF₀ J ψ).getD (p.toBlock.nP + i) default).2.2
          = ((dsF J ψ).getD (p.toBlock.nP + i) default).2.2 :=
    fun J cA hJ => mutualCtorDataI_ident hagree₁ (hCD₀ J cA hJ) (hCD₁ J cA hJ)
  -- **the real chains**: the member-leaf readings, and the X-chains
  -- are their shadow
  let FssRf : (Name → Nat) → List (List AnnotTerm) := fun ψ =>
    mutFss p.toBlock.nP ctorsA.length dsF ψ
  have hFssShadow : ∀ (ψ : Name → Nat) (J : Nat), J < ctorsA.length →
      shadowFs p.toBlock.nP (kindsOf (ksF J)) (nFs J)
          (((dsF J ψ).drop p.toBlock.nP).map (·.2.2))
        = (Fss0f ψ).getD J [] := by
    intro ψ J hJ
    rw [mutFss0_getD hJ]
    refine shadowFs_congr fun i hi hr => ?_
    have hlen₀ : (dsF₀ J ψ).length = p.toBlock.nP + nFs J := (hCD₀ J _ (hcAGet J hJ)).len ψ
    have hlen₁ : (dsF J ψ).length = p.toBlock.nP + nFs J := (hCD₁ J _ (hcAGet J hJ)).len ψ
    have hks : (kindsOf (ksF J)).getD i .ordinary = kindAt (ksF J) i := by
      rw [kindsOf_getD (by rw [(hksJ J _ (hcAGet J hJ)).1]; exact hi)]
    rw [drop_map_getD hlen₁ hi, drop_map_getD hlen₀ hi]
    refine ((hident J _ (hcAGet J hJ)).2.2.2.2.2.2.2 ψ i hi (fun hk => hr ?_) (fun hk => hr ?_)).symm
    · exact ⟨Nat.le_add_right _ _, Or.inl (by rw [Nat.add_sub_cancel_left, hks]; exact hk)⟩
    · exact ⟨Nat.le_add_right _ _, Or.inr (by rw [Nat.add_sub_cancel_left, hks]; exact hk)⟩
  have hagreeM1 : ∀ n : Name, (env.find? n).isSome = true →
      mp.base2.acval n = mp₁.base2.acval n := by
    intro n hn
    refine (hoff₁ n (fun t f hft hh => ?_)).symm
    rw [hh, hfreshF t f hft] at hn
    exact nomatch hn
  have hFD₂ : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      FormerData mp₁.base2 f.cvTa (p.toBlock.nP + f.nIdx) f₀.s (ppsF t) (lvlsF t) :=
    fun t f hft => FormerData.crossEnv (hFD t f hft) (hcbF t f hft) hFP hLG hPJ hagreeM1
  have hleafT₁ : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f → ∀ ψ : Name → Nat,
      ∃ B, mp₁.base2.acval f.cvTa.name ψ = mkLamsC (f.s.eval ψ + 1) (ppsF t ψ) B := by
    intro t f hft ψ
    refine ⟨mutualLeafBodyAV (Wf ψ) (f₀.s.eval ψ) f.nIdx (Idssf ψ) rssf (tlssf ψ) (Eissf ψ)
      (Fss0f ψ) (Essf ψ) t, ?_⟩
    rw [hsEq t f hft ψ, hleaf₁ t f hft]
    exact mutualTyAVI_eq_mkLamsC _ _ _ _ _ _ _ _ _ _ _
  have hChainFull : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      ∀ (ψ : Name → Nat) (ρp : Nat → V),
        Sat V (((ppsF t ψ).take p.toBlock.nP).map (·.2.2)).reverse ρp →
        FixChainsOkI (Wf ψ) (f₀.s.eval ψ) ρp (auxIds (Wf ψ) (Idssf ψ)) 1 rssf (tlssf ψ)
          (Eissf ψ) (Fss0f ψ) (Essf ψ) ∧
        ChainsRealI (auxFamI (Wf ψ) (f₀.s.eval ψ) ρp (Idssf ψ) rssf (tlssf ψ) (Eissf ψ)
            (Fss0f ψ) (Essf ψ)) (Wf ψ) (f₀.s.eval ψ) ρp (auxIds (Wf ψ) (Idssf ψ)) rssf
          (tlssf ψ) (Eissf ψ) (Fss0f ψ) (FssRf ψ) (Essf ψ) ∧
        (∀ X, X ∈ˢ lfpFamSpace V (f₀.s.eval ψ) (idxSet (Wf ψ) ρp (auxIds (Wf ψ) (Idssf ψ))) →
          ∀ τ, τ ∈ˢ idxSet (Wf ψ) ρp (auxIds (Wf ψ) (Idssf ψ)) →
            SumFieldsValid (cons τ (cons X ρp))
              (chainsXI (Wf ψ) (auxIds (Wf ψ) (Idssf ψ)) 1 rssf (tlssf ψ) (Eissf ψ)
                (Fss0f ψ) (Essf ψ))) := by
    intro t f hft ψ ρp hρ
    obtain ⟨hTagJ, hVJ⟩ := hIdxAll t f hft ψ ρp hρ
    have hFs₀ : ∀ J : Nat, J < ctorsA.length → ((Fss0f ψ).getD J []).length = nFs J := by
      intro J hJ; rw [mutFss0_getD hJ]; exact shadowFs_length
    have hFsR : ∀ J : Nat, J < ctorsA.length → ((FssRf ψ).getD J []).length = nFs J := by
      intro J hJ
      rw [mutFss_getD hJ, List.length_map, List.length_drop, (hCD₁ J _ (hcAGet J hJ)).len ψ]
      show p.toBlock.nP + nFs J - p.toBlock.nP = nFs J
      omega
    have hEsL : ∀ J : Nat, J < ctorsA.length → ((Essf ψ).getD J []).length = 1 := by
      intro J hJ; rw [mutEss'_getD hJ]; rfl
    refine (mutualChainFacts_of (V := V) (nP := p.toBlock.nP) (n := ctorsA.length)
      (ksF := ksF) (nFs := nFs) (rss := rssf) (tlss := tlssf ψ) (Eiss' := Eissf ψ)
      (Fss₀ := Fss0f ψ) (Fss := FssRf ψ) (Ess' := Essf ψ) hTagJ hVJ
      (by show ((List.range ctorsA.length).map _).length = _; simp)
      (by show ((List.range ctorsA.length).map _).length = _; simp)
      (mutEss'_length (n := ctorsA.length))
      (fun J hJ => mutRss_getD hJ) hFs₀ hFsR hEsL
      (fun J hJ => (hChainJ t f hft ψ ρp hρ J hJ).1)
      (fun J hJ => (hChainJ t f hft ψ ρp hρ J hJ).2)
      ?_).2
    intro J hJ
    have hJg := hcAGet J hJ
    have hmt : memF J < fms.length := hmotLt J hJ
    have hmtG := hfmGet _ hmt
    obtain ⟨hnF, sorts, hsj, hrun⟩ := hrunC J _ hJg
    have hPropJ : (Level.isEquiv f₀.s Level.zero == some true) = true →
        ∀ ψ' : Name → Nat, Level.eval ψ' (fms.getD (memF J) default).s
          = Level.eval ψ' Level.zero := by
      intro hp ψ'
      rw [hsEq _ _ hmtG ψ']
      exact Level.isEquiv_sound (beq_iff_eq.mp hp) ψ'
    have hFDm := FormerData.congr_sort (hFD₂ _ _ hmtG) (fun ψ' => (hsEq _ _ hmtG ψ').symm)
    have hleafTm : ∀ ψ' : Name → Nat, ∃ B,
        mp₁.base2.acval (fms.getD (memF J) default).cvTa.name ψ'
          = mkLamsC ((fms.getD (memF J) default).s.eval ψ' + 1) (ppsF (memF J) ψ') B :=
      hleafT₁ _ _ hmtG
    have hρJ : Sat V (((ppsF (memF J) ψ).take p.toBlock.nP).map (·.2.2)).reverse ρp :=
      hframeAll t (memF J) f _ hft hmtG ψ ρp hρ
    obtain ⟨hid1, hid2, hid3, hid4, hidEs, hidEis, hidTss, hidDs⟩ := hident J _ hJg
    have hEL₁ : (eissF J ψ).length = nFs J := (hCD₁ J _ hJg).eissLen ψ
    have hCJ := (hChainJ t f hft ψ ρp hρ J hJ).1
    rw [mutTlss_getD hJ, ← hFssShadow ψ J hJ, mutEss'_getD hJ, mutEiss'_getDJ hJ
      ((hCD₀ J _ hJg).eissLen ψ), hidTss ψ, hidEs ψ, hidEis ψ] at hCJ
    have hrealJ := mutualChainReal_at (W := Wf ψ) (mem := memF J) (Idss := Idssf ψ)
      (rss := rssf) (tlss := tlssf ψ) (Eiss' := Eissf ψ) (Fss₀ := Fss0f ψ) (Ess' := Essf ψ)
      hμ mp₁ hrun (hfindF _ _ hmtG) hPropJ hFDm hleafTm (hCD₁ J _ hJg) ψ ρp hρJ hTagJ
      (by rw [hsEq _ _ hmtG ψ]; exact hCJ)
      ?_ (by rw [hsEq _ _ hmtG ψ]; exact ((hMCO t f hft).2 ψ ρp hρ).2.2.1)
    · rw [mutRss_getD hJ, mutTlss_getD hJ, ← hFssShadow ψ J hJ, mutFss_getD hJ,
        mutEiss'_getDJ hJ ((hCD₀ J _ hJg).eissLen ψ), hidTss ψ, hidEis ψ]
      rw [hsEq _ _ hmtG ψ] at hrealJ
      exact hrealJ
    · intro i hi _
      obtain ⟨-, -, htgt⟩ := hksJ J _ hJg
      have htl := htgt i
      have htG := hfmGet _ htl
      obtain ⟨hnm, hni⟩ := hmemT _ _ htG
      refine ⟨ppsF (tgtAt (ksF J) i) ψ, ?_, ?_, hIdssGet ψ _ htl, ?_, ?_⟩
      · rw [hni, List.length_map, List.length_drop, (hFD₂ _ _ htG).len ψ]
        omega
      · rw [List.length_map, List.length_drop, (hFD₂ _ _ htG).len ψ]
        omega
      · exact hframeAll t _ f _ hft htG ψ ρp hρ
      · have hlen : (((ppsF (tgtAt (ksF J) i) ψ).drop p.toBlock.nP).map (·.2.2)).length
            = (fms.getD (tgtAt (ksF J) i) default).nIdx := by
          rw [List.length_map, List.length_drop, (hFD₂ _ _ htG).len ψ]
          exact Nat.add_sub_cancel_left _ _
        have h1 : mp₁.base2.acval (fms.getD (tgtAt (ksF J) i) default).cvTa.name ψ
            = mutualTyAVI (Wf ψ) (f₀.s.eval ψ) (ppsF (tgtAt (ksF J) i) ψ)
                (fms.getD (tgtAt (ksF J) i) default).nIdx (Idssf ψ) rssf (tlssf ψ) (Eissf ψ)
                (Fss0f ψ) (Essf ψ) (tgtAt (ksF J) i) := by
          rw [hleaf₁ _ _ htG]
        rw [hnm, h1, hsEq _ _ hmtG ψ, hlen]
  have hReal : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      ∀ (ψ : Name → Nat) (ρp : Nat → V),
        Sat V (((ppsF t ψ).take p.toBlock.nP).map (·.2.2)).reverse ρp →
        ChainsRealI (auxFamI (Wf ψ) (f₀.s.eval ψ) ρp (Idssf ψ) rssf (tlssf ψ) (Eissf ψ)
            (Fss0f ψ) (Essf ψ)) (Wf ψ) (f₀.s.eval ψ) ρp (auxIds (Wf ψ) (Idssf ψ)) rssf
          (tlssf ψ) (Eissf ψ) (Fss0f ψ) (FssRf ψ) (Essf ψ) :=
    fun t f hft ψ ρp hρ => (hChainFull t f hft ψ ρp hρ).2.1
  -- the constructors' frames at the member leaves
  have hframesJ : ∀ (J : Nat), J < ctorsA.length →
      (∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat V (((ppsF (memF J) ψ).take p.toBlock.nP).map (·.2.2)).reverse ρ ↔
          Sat V (((dsF J ψ).take p.toBlock.nP).map (·.2.2)).reverse ρ) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat V (((dsF J ψ).take p.toBlock.nP).map (·.2.2)).reverse ρ →
          FieldsOkB ((fms.getD (memF J) default).s.eval ψ) ρ
            (((dsF J ψ).drop p.toBlock.nP).map (·.2.2)) ∧
          FieldsValid ρ (((dsF J ψ).drop p.toBlock.nP).map (·.2.2)) ∧
          ((Level.isEquiv f₀.s Level.zero == some true) = false →
            FieldsBound ((fms.getD (memF J) default).s.eval ψ) ρ
              (((dsF J ψ).drop p.toBlock.nP).map (·.2.2))) ∧
          (∀ bs : List V, SpineFit ρ (((dsF J ψ).drop p.toBlock.nP).map (·.2.2)) bs →
            (∀ E ∈ esF J ψ, WellDenotedV V (consList bs ρ) E) ∧
            SpineFit ρ (((ppsF (memF J) ψ).drop p.toBlock.nP).map (·.2.2))
              (idxValsAt ρ (esF J ψ) bs))) := by
    intro J hJ
    have hJg := hcAGet J hJ
    have hmt : memF J < fms.length := hmotLt J hJ
    have hmtG := hfmGet _ hmt
    obtain ⟨hnF, sorts, hsj, hrun⟩ := hrunC J _ hJg
    have hPropJ : (Level.isEquiv f₀.s Level.zero == some true) = true →
        ∀ ψ' : Name → Nat, Level.eval ψ' (fms.getD (memF J) default).s
          = Level.eval ψ' Level.zero := by
      intro hp ψ'
      rw [hsEq _ _ hmtG ψ']
      exact Level.isEquiv_sound (beq_iff_eq.mp hp) ψ'
    have hFDm := FormerData.congr_sort (hFD₂ _ _ hmtG) (fun ψ' => (hsEq _ _ hmtG ψ').symm)
    obtain ⟨h1, h2, -⟩ := mutualCtorFrames hμ mp₁ hrun (hfindF _ _ hmtG) hPropJ hFDm
      (hCD₁ J _ hJg).toCtorDataI (hleafT₁ _ _ hmtG)
    exact ⟨h1, h2⟩
  -- the member leaves, as the constructor stage reads them
  let leafT : Nat → (Name → Nat) → AnnotTerm := fun J ψ =>
    mutualTyAVI (Wf ψ) (f₀.s.eval ψ) (ppsF (memF J) ψ) (fms.getD (memF J) default).nIdx
      (Idssf ψ) rssf (tlssf ψ) (Eissf ψ) (Fss0f ψ) (Essf ψ) (memF J)
  have hleafTJ : ∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA →
      ∀ ψ : Name → Nat,
        mp₁.base2.acval (fms.getD (memF J) default).cvTa.name ψ = leafT J ψ := by
    intro J cA hJ ψ
    rw [hleaf₁ _ _ (hfmGet _ (hmotLt J (List.getElem?_eq_some_iff.mp hJ).1))]
  have hleafClosed : ∀ (J : Nat), J < ctorsA.length → ∀ ψ : Name → Nat,
      Term.bvarsBelow 0 (leafT J ψ).erase := by
    intro J hJ ψ
    exact mutualTyAVI_below ((hFD₂ _ _ (hfmGet _ (hmotLt J hJ))).below ψ)
      ((hFD₂ _ _ (hfmGet _ (hmotLt J hJ))).len ψ) (hIdsBelow ψ) (hchainBelow ψ)
  -- **the constructor's fibre fold**
  have hfold : ∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA →
      ∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat V (((ppsF (memF J) ψ).take p.toBlock.nP).map (·.2.2)).reverse ρ →
        ∀ bs : List V, SpineFit ρ (((dsF J ψ).drop p.toBlock.nP).map (·.2.2)) bs →
          interp V (consList bs ρ)
              (AnnotTerm.mkAppN (leafT J ψ) (paramBvars p.toBlock.nP cA.2 ++ esF J ψ))
            = sumSet (f₀.s.eval ψ) (sumFibre (f₀.s.eval ψ)
                (consList (idxValsAt ρ
                  [tagTupleAV (Wf ψ) (memF J) cA.2 (Idssf ψ) (esF J ψ)] bs) ρ)
                (rChains 1 1 (FssRf ψ) (Essf ψ))) := by
    intro J cA hJ ψ ρ hρ bs hsp
    have hJl : J < ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
    have hmt : memF J < fms.length := hmotLt J hJl
    have hmtG := hfmGet _ hmt
    have hlenM : (ppsF (memF J) ψ).length
        = p.toBlock.nP + (((ppsF (memF J) ψ).drop p.toBlock.nP).map (·.2.2)).length := by
      rw [List.length_map, List.length_drop, (hFD₂ _ _ hmtG).len ψ]
      omega
    have hIdsM : (Idssf ψ)[memF J]?
        = some (((ppsF (memF J) ψ).drop p.toBlock.nP).map (·.2.2)) := hIdssGet ψ _ hmt
    have hlenbs : bs.length = cA.2 := by
      rw [hsp.length_eq, List.length_map, List.length_drop, (hCD₁ J _ hJ).len ψ]
      omega
    obtain ⟨hTagJ, hVJ⟩ := hIdxAll (memF J) _ hmtG ψ ρ hρ
    have hfr := (hframesJ J hJl).2 ψ ρ ((hframesJ J hJl).1 ψ ρ |>.mp hρ)
    obtain ⟨hEok, hfit⟩ := hfr.2.2.2 bs hsp
    have hA : ∀ σ : Nat → V, interp V σ (leafT J ψ)
        = interp V (fun j => ρ (j + p.toBlock.nP))
            (mutualTyAVI (Wf ψ) (f₀.s.eval ψ) (ppsF (memF J) ψ)
              (((ppsF (memF J) ψ).drop p.toBlock.nP).map (·.2.2)).length (Idssf ψ) rssf
              (tlssf ψ) (Eissf ψ) (Fss0f ψ) (Essf ψ) (memF J)) := by
      intro σ
      have hlen' : (((ppsF (memF J) ψ).drop p.toBlock.nP).map (·.2.2)).length
          = (fms.getD (memF J) default).nIdx := by
        rw [List.length_map, List.length_drop, (hFD₂ _ _ hmtG).len ψ]
        exact Nat.add_sub_cancel_left _ _
      rw [hlen']
      exact interp_closed V (hleafClosed J hJl ψ) σ _
    have hf := mutualCtorFold (V := V) (nF := cA.2) (mem := memF J) (Fss := FssRf ψ)
      hlenM hIdsM hTagJ (hXAll (memF J) _ hmtG ψ ρ hρ).1
      (hReal (memF J) _ hmtG ψ ρ hρ) hρ hA hlenbs (fun E hE => (hEok E hE).1) ?_
    · rw [paramBvars_eq_paramBvarsAt]
      exact hf
    · exact hfit
  -- the constructors' names, freshness and resolution
  have hnamesC : ctorsA.map (·.1.name) = p.toBlock.ctors.map (·.cv.name) := by
    refine List.ext_getElem? fun J => ?_
    rw [List.getElem?_map, List.getElem?_map]
    cases hJ : ctorsA[J]? with
    | none =>
      have hn : p.toBlock.ctors[J]? = none := by
        rw [List.getElem?_eq_none_iff] at hJ ⊢; omega
      rw [hn]
      rfl
    | some cA =>
      have hJl : J < ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
      obtain ⟨-, sorts, -, hrun⟩ := hrunC J cA hJ
      obtain ⟨⟨ty', hccv⟩, -, -⟩ := ConLeche.checkMutualCtor_shape hrun
      obtain ⟨-, -, -, -, -, -, _, _, _, -, -, -, -, -, hty⟩ := ConLeche.checkConstantVal_inv hccv
      rw [hctorGet J hJl]
      simp only [Option.map_some, Option.some.injEq]
      rw [hty]
  have hndA : (ctorsA.map (·.1.name)).Nodup := by rw [hnamesC]; exact hndC
  have hfreshC : ∀ c ∈ ctorsA, (ConLeche.consMutualFormers fms env).find? c.1.name = none :=
    ConLeche.Semantics.checkMutualCtors_fresh hctors
  have hresC : ∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA →
      cA.1.type.constsResolve (ConLeche.consMutualFormers fms env) = true := by
    intro J cA hJ
    obtain ⟨-, sorts, -, hrun⟩ := hrunC J cA hJ
    obtain ⟨⟨ty', hccv⟩, -, -⟩ := ConLeche.checkMutualCtor_shape hrun
    obtain ⟨-, -, -, -, -, -, _, _, _, -, -, htr, -, -, hty⟩ := ConLeche.checkConstantVal_inv hccv
    rw [hty]; exact htr
  have hmono₁ : ∀ e : Expr, Expr.constsResolve env e = true →
      Expr.constsResolve (ConLeche.consMutualFormers fms env) e = true :=
    fun e h => constsResolve_consMutualFormers h
  have hE₁ : ConLeche.EtaFamiliesClosed (ConLeche.consMutualFormers fms env) :=
    ConLeche.Semantics.EtaFamiliesClosed.ofFreshExt hE
      (ConLeche.Semantics.mutualFormers_freshExt hformers)
  have hCDparams₁ : ∀ J : Nat, J < ctorsA.length → ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ q ∈ p.toBlock.lps, ψ₁ q = ψ₂ q) → dsF J ψ₁ = dsF J ψ₂ := by
    intro J hJl ψ₁ ψ₂ hφ
    have hJ := hcAGet J hJl
    have hφ' : ∀ q ∈ (ctorsA.getD J default).1.levelParams, ψ₁ q = ψ₂ q := by
      rw [hlpsC J _ hJ]; exact hφ
    exact ((hCD₁ J _ hJ).params ψ₁ ψ₂ hφ').1
  have hFssOkP : ∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA →
      ∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat V (((dsF J ψ).take p.toBlock.nP).map (·.2.2)).reverse ρ →
        SumFieldsOkB (f₀.s.eval ψ) ρ (FssRf ψ) ∧ SumFieldsValid ρ (FssRf ψ) := by
    intro J cA hJ ψ ρ hρ
    have hJl : J < ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
    have hρM : Sat V (((ppsF (memF J) ψ).take p.toBlock.nP).map (·.2.2)).reverse ρ :=
      ((hframesJ J hJl).1 ψ ρ).mpr hρ
    have hall : ∀ J' : Nat, J' < ctorsA.length →
        FieldsOkB (f₀.s.eval ψ) ρ (((dsF J' ψ).drop p.toBlock.nP).map (·.2.2)) ∧
          FieldsValid ρ (((dsF J' ψ).drop p.toBlock.nP).map (·.2.2)) := by
      intro J' hJ'
      have hρM' : Sat V (((ppsF (memF J') ψ).take p.toBlock.nP).map (·.2.2)).reverse ρ :=
        hframeAll (memF J) (memF J') _ _ (hfmGet _ (hmotLt J hJl)) (hfmGet _ (hmotLt J' hJ'))
          ψ ρ hρM
      have hfr := (hframesJ J' hJ').2 ψ ρ (((hframesJ J' hJ').1 ψ ρ).mp hρM')
      rw [hsEq _ _ (hfmGet _ (hmotLt J' hJ')) ψ] at hfr
      exact ⟨hfr.1, hfr.2.1⟩
    refine ⟨fun Fs hFs => ?_, fun Fs hFs => ?_⟩
    · obtain ⟨J', hJ', rfl⟩ := List.mem_map.mp (show Fs ∈ (List.range ctorsA.length).map
        (fun J => ((dsF J ψ).drop p.toBlock.nP).map (·.2.2)) from hFs)
      exact (hall J' (List.mem_range.mp hJ')).1
    · obtain ⟨J', hJ', rfl⟩ := List.mem_map.mp (show Fs ∈ (List.range ctorsA.length).map
        (fun J => ((dsF J ψ).drop p.toBlock.nP).map (·.2.2)) from hFs)
      exact (hall J' (List.mem_range.mp hJ')).2
  have hfoundC : ∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA →
      CtorMembersFound (ConLeche.consMutualFormers fms env) p.toBlock.members3
        (fun t => (fms.getD t default).cvTa.name) memF ksF J cA.2 := by
    intro J cA hJ
    have hJl : J < ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
    refine ⟨by rw [hfindF _ _ (hfmGet _ (hmotLt J hJl))]; rfl, fun i hi _ => ?_⟩
    have htl := (hksJ J cA hJ).2.2 i
    rw [(hmemT _ _ (hfmGet _ htl)).1, hfindF _ _ (hfmGet _ htl)]
    rfl
  have hpendC : MutualPendingAt mp₁.base2 (ConLeche.consMutualFormers fms env)
      p.toBlock.members3 p.toBlock.lps p.toBlock.nP
      (Level.isEquiv f₀.s Level.zero == some true) p.toBlock.large
      (fun t => (fms.getD t default).cvTa.name) (fun t => (fms.getD t default).nIdx) memF
      (fun J => (fms.getD (memF J) default).s) idxF₁ dsF esF srcsF ksF fvsPF xFvsF xrestF
      eissF tssF ctorsA 0 := by
    intro J cA _ hJ
    refine ⟨hfreshC cA (List.mem_of_getElem? hJ), hresC J cA hJ, ?_, hlpsC J cA hJ, ?_⟩
    · intro e he
      refine hmono₁ e ?_
      have hr := (hCD₁ J cA hJ).opened.residRes
      rw [← (hCD₁ J cA hJ).idxEq] at hr
      exact hr e he
    · exact MutualCtorDataI.monoEnv₀ hmono₁ (hCD₁ J cA hJ)
  -- **the constructors' stage**
  obtain ⟨mp₂, hE₂, hfound₂, hleaf₂, hcons₂, -, hleafC₂, hag₂⟩ :=
    stageMutualCtors (V := V) (μ := μ) (F := F)
      (memberNames := p.toBlock.memberNames) (members := p.toBlock.members3)
      (lps := p.toBlock.lps) (nP := p.toBlock.nP)
      (isProp := Level.isEquiv f₀.s Level.zero == some true) (large := p.toBlock.large)
      (env₀ := ConLeche.consMutualFormers fms env)
      (Tname := fun t => (fms.getD t default).cvTa.name)
      (nIdxOf := fun t => (fms.getD t default).nIdx) (mots := memF)
      (resSortOf := fun J => (fms.getD (memF J) default).s)
      (cvTaOf := fun t => (fms.getD t default).cvTa)
      (idxF := idxF₁) (dsF := dsF) (esF := esF) (srcsF := srcsF) (ksF := ksF)
      (fvsPF := fvsPF) (xFvsF := xFvsF) (xrestF := xrestF) (eissF := eissF) (tssF := tssF)
      (ctorsA := ctorsA) (W := Wf) (w := fun ψ => f₀.s.eval ψ) (Idss := Idssf)
      (FssR := FssRf) (Ess' := Essf) (ppsOf := ppsF) (leafT := leafT)
      (Inv := fun {_} _ => True) mp₁ hndA
      (fun J cA hJ => by
        obtain ⟨-, sorts, -, hrun⟩ := hrunC J cA hJ
        exact ⟨_, sorts, hrun⟩)
      (fun J cA hJ ψ => hsEq _ _ (hfmGet _ (hmotLt J (List.getElem?_eq_some_iff.mp hJ).1)) ψ)
      hfold
      (fun J cA hJ ψ => by
        have hJl : J < ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
        show ((List.range ctorsA.length).map _)[J]? = _
        rw [List.getElem?_map, List.getElem?_range hJl]
        rfl)
      (fun J cA hJ ψ => by
        have hJl : J < ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
        have hlen : (Essf ψ).length = ctorsA.length := mutEss'_length
        have hgd := mutEss'_getD (n := ctorsA.length) (W := Wf ψ) (Idss := Idssf ψ)
          (memF := memF) (nFs := nFs) (esF := esF₀) (ψ := ψ) hJl
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (show J < (Essf ψ).length from by rw [hlen]; exact hJl)] at hgd
        rw [List.getElem?_eq_getElem (show J < (Essf ψ).length from by rw [hlen]; exact hJl)]
        have hnF : cA.2 = nFs J := by
          show cA.2 = (ctorsA.getD J default).2
          rw [List.getD_eq_getElem?_getD, hJ]; rfl
        rw [hnF, ← (hident J cA hJ).2.2.2.2.1 ψ]
        exact congrArg some hgd)
      (fun ψ₁ ψ₂ hφ => ⟨((hFD 0 f₀ hf0).params ψ₁ ψ₂
          (by rw [hlpsF 0 f₀ hf0]; exact hφ)).2,
        by
          show mutFss _ _ _ _ = mutFss _ _ _ _
          unfold mutFss
          exact List.map_congr_left (fun J hJ => by
            rw [hCDparams₁ J (List.mem_range.mp hJ) ψ₁ ψ₂ hφ])⟩)
      (fun ψ Fs hFs => by
        obtain ⟨J, hJ, rfl⟩ := List.mem_map.mp (show Fs ∈ (List.range ctorsA.length).map
          (fun J => ((dsF J ψ).drop p.toBlock.nP).map (·.2.2)) from hFs)
        have hh := (DomsBelow.drop p.toBlock.nP
          ((hCD₁ J _ (hcAGet J (List.mem_range.mp hJ))).below ψ)).fields
        rwa [Nat.zero_add] at hh)
      (fun J cA hJ => (hframesJ J (List.getElem?_eq_some_iff.mp hJ).1).1)
      hFssOkP (fun _ _ _ _ _ _ _ _ => trivial) hE₁ hfoundC hleafTJ hpendC trivial
  -- the members' data at the constructors' carrier
  obtain ⟨hFPc, hLGc, hPJc⟩ := consMutualCtors_extend (nP := p.toBlock.nP) hfreshC hndA
  have hcbF₁ : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      ConstsBound (ConLeche.consMutualFormers fms env) f.cvTa.type := by
    intro t f hft
    obtain ⟨cv, cv', bs, -, hccv, -, -, -⟩ := hposF t f hft
    obtain ⟨-, -, -, -, -, -, _, _, _, -, -, htr, -, -, hty⟩ := ConLeche.checkConstantVal_inv hccv
    exact constsBound_of_constsResolve _ (hmono₁ _ (by rw [hty]; exact htr))
  have hFD₃ : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      FormerData mp₂.base2 f.cvTa (p.toBlock.nP + f.nIdx) f₀.s (ppsF t) (lvlsF t) :=
    fun t f hft => FormerData.crossEnv (hFD₂ t f hft) (hcbF₁ t f hft) hFPc hLGc hPJc
      (fun n hn => (hag₂ n (fun cA hcA hh => by
        rw [hh, hfreshC cA hcA] at hn
        exact nomatch hn)).symm)
  -- the generators' data, read off `mutualGenData`
  obtain ⟨hf4, hc4⟩ := Prod.mk.inj hgd
  have hlen4F : formers4.length = fms.length := by rw [← hf4]; simp
  have hget4F : ∀ t : Nat, t < fms.length →
      formers4.getD t default
        = ⟨(fms.getD t default).cvTa.name, (fms.getD t default).nIdx,
           (fms.getD t default).cvTa.type⟩ := by
    intro t ht
    rw [← hf4, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem ht, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
    rfl
  have hlen4C : ctors4.length = ctorsA.length := by
    have h1 : kinds.length = ctorsA.length := hlenAK.symm
    rw [← hc4, List.length_zipWith, List.length_zip, h1, hlenA]
    omega
  -- **the members' reading premises**
  have hFFacts : ∀ t : Nat, t < fms.length →
      MutualFormerFacts mp₂.base2 p.toBlock.lps p.toBlock.nP (formers4.getD t default)
        (fms.getD t default).cvTa (fms.getD t default).s (ppsF t) (lvlsF t) := by
    intro t ht
    have hft := hfmGet t ht
    obtain ⟨bs, hstrip⟩ := hstripF _ _ hft
    refine ⟨⟨{}, ?_⟩, by rw [hget4F t ht], hlpsF _ _ hft, ⟨bs, by rw [hget4F t ht]; exact hstrip⟩,
      ?_⟩
    · rw [hget4F t ht]
      exact hFPc (hfindF _ _ hft)
    · rw [hget4F t ht]
      exact FormerData.congr_sort (hFD₃ _ _ hft) (fun ψ => (hsEq _ _ hft ψ).symm)
  have hFReads : ∀ ψ : Name → Nat,
      FormerReadsM mp₂.base2 ψ p.toBlock.lps p.toBlock.nP
        (fun t => mp₂.base2.acval (fms.getD t default).cvTa.name ψ)
        (fun t => (fms.getD t default).nIdx)
        (fun t => (ppsF t ψ).take p.toBlock.nP) (fun t => (ppsF t ψ).drop p.toBlock.nP)
        formers4 :=
    fun ψ => formerReadsM_of
      (fun t ht => by rw [hget4F t (by rw [← hlen4F]; exact ht)])
      (fun t ht => by rw [hget4F t (by rw [← hlen4F]; exact ht)])
      (fun t ht => hFFacts t (by rw [← hlen4F]; exact ht)) ψ
  -- **`Tname`'s totality**: `mutualRecData_of` asks for member `q`'s
  -- former at EVERY `q`, so the `getD`-default must be a MEMBER
  -- (`default`'s name is `Name.anonymous`, which no environment
  -- carries)
  have hfmF₀ : ∀ q : Nat, ∃ t : Nat, fms[t]? = some (fms.getD q f₀) := by
    intro q
    cases hq : fms[q]? with
    | none =>
      refine ⟨0, ?_⟩
      rw [hf0, List.getD_eq_getElem?_getD, hq]
      rfl
    | some f =>
      refine ⟨q, ?_⟩
      rw [hq, List.getD_eq_getElem?_getD, hq]
      rfl
  have hgetDf₀ : ∀ t : Nat, t < fms.length → fms.getD t f₀ = fms.getD t default := by
    intro t ht
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
    rfl
  -- **the constructors' reading premises**
  have hCReads : ∀ ψ : Name → Nat,
      MutualCtorReadsM mp₂.base2 ψ p.toBlock.lps p.toBlock.nP
        (fun t => (fms.getD t f₀).cvTa.name) (fun t => (fms.getD t default).nIdx) memF
        (fun J => tgtAt (ksF J)) ctors4
        (fixCtorDataList dsF esF (fun J => kindsOf (ksF J)) eissF tssF ψ ctorsA 0) := by
    intro ψ
    refine mutualCtorReadsM_of (env₀ := ConLeche.consMutualFormers fms env)
      (members := p.toBlock.members3) (isProp := Level.isEquiv f₀.s Level.zero == some true)
      (large := p.toBlock.large) (resSortOf := fun J => (fms.getD (memF J) default).s)
      (idxF := idxF₁) (srcsF := srcsF) (fvsPF := fvsPF) (xFvsF := xFvsF) (xrestF := xrestF)
      ψ hlen4C ?_ ?_ ?_
    · intro J cA hJ
      have hJl : J < ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
      have hzip : (p.toBlock.ctors.zip ctorsA)[J]?
          = some (p.toBlock.ctors.getD J default, cA) := by
        rw [List.zip, List.getElem?_zipWith, hctorGet J hJl, hJ]
      rw [← hc4, List.getElem?_zipWith, hzip,
        List.getElem?_eq_getElem (show J < kinds.length by rw [← hlenAK]; exact hJl)]
      simp only [Option.some.injEq]
      have hnm : cA.1.name = (p.toBlock.ctors.getD J default).cv.name := by
        have h1 := congrArg (fun l => l[J]?) hnamesC
        rw [List.getElem?_map, List.getElem?_map, hJ, hctorGet J hJl] at h1
        simpa using h1
      have hnF : cA.2 = (p.toBlock.ctors.getD J default).nF := (hrunC J cA hJ).1
      rw [← hnm, ← hnF]
      show _ = MutualCtor4.mk cA.1.name cA.2 cA.1.type (p.toBlock.ctors.getD J default).member
        (ConLeche.mutualRecFieldsOf (kinds.getD J []))
      have hkJ : (kinds.getD J [] : List (RecFieldKind × Nat))
          = kinds[J]'(show J < kinds.length by omega) := by
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (show J < kinds.length by omega)]
        rfl
      rw [hkJ]
    · intro J i hJ _
      have htl := (hksJ J _ (hcAGet J hJ)).2.2 i
      refine ⟨?_, (hmemT _ _ (hfmGet _ htl)).2.symm⟩
      show (fms.getD (tgtAt (ksF J) i) f₀).cvTa.name = _
      rw [hgetDf₀ _ htl]
      exact (hmemT _ _ (hfmGet _ htl)).1.symm
    · intro J cA hJ
      have hJl : J < ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
      have hfacts := (hcons₂ J cA hJl hJ).1
      refine ⟨hfacts.1, hfacts.2.1, ?_⟩
      dsimp only
      rw [show fms.getD (memF J) f₀ = fms.getD (memF J) default from hgetDf₀ _ (hmotLt J hJl)]
      exact hfacts.2.2
  have hfTname : ∀ q : Nat, ∃ ci : ConstantInfo,
      (ConLeche.consMutualCtors p.toBlock.nP ctorsA (ConLeche.consMutualFormers fms env)).find?
          (fms.getD q f₀).cvTa.name = some ci ∧
        ci.toConstantVal.levelParams = p.toBlock.lps := by
    intro q
    obtain ⟨t, ht⟩ := hfmF₀ q
    exact ⟨.indInfo (fms.getD q f₀).cvTa {}, hFPc (hfindF t _ ht), hlpsF t _ ht⟩
  -- **member `t`'s stored recursor type's reading** (`mutualRecData_of`)
  obtain ⟨hlenRec, hallRec⟩ := ConLeche.checkMutualRecTys_inv hrectys
  have hkF : p.toBlock.k = fms.length := by
    show p.toBlock.formers.length = fms.length
    rw [hlenFms]
  have hmots4 : ∀ J, J < ctors4.length → memF J < formers4.length := by
    intro J hJ
    rw [hlen4F]
    exact hmotLt J (by rw [← hlen4C]; exact hJ)
  have hRDs : ∀ t : Nat, t < fms.length →
      MutualRecData mp₂.base2 (cvRas.getD t default) p.toBlock.nP fms.length ctorsA.length
        ((fms.getD t default).nIdx) t p.toBlock.elimLevel
        (mutualRdsAV mp₂.base2 fms.length p.toBlock.nP p.toBlock.elimLevel
          (fun t ψ => mp₂.base2.acval (fms.getD t default).cvTa.name ψ)
          (fun t => (fms.getD t default).nIdx)
          (fun t ψ => (ppsF t ψ).take p.toBlock.nP) (fun t ψ => (ppsF t ψ).drop p.toBlock.nP)
          (fun ψ => fixCtorDataList dsF esF (fun J => kindsOf (ksF J)) eissF tssF ψ ctorsA 0)
          memF (fun J => tgtAt (ksF J)) t) := by
    intro t ht
    obtain ⟨cvRa, hget, hrun⟩ := hallRec t (by rw [hkF]; exact ht)
    have hcv : cvRas.getD t default = cvRa := by rw [List.getD_eq_getElem?_getD, hget]; rfl
    rw [hcv]
    have h := (mutualRecData_of (V := V) hμ mp₂ hrun hFReads hCReads hmots4 hfTname
      (show t < formers4.length by rw [hlen4F]; exact ht)).1
    rw [hlen4F, hlen4C] at h
    exact h
  -- **the recursor stage's data** (`MutualRecParts`): the chain lists
  -- are the block's CONCRETE spellings, so the datum's derived lists
  -- and the stage's agree by `rfl`
  let prts : MutualRecParts :=
    { ℓ := fun ψ => p.toBlock.elimLevel.eval ψ
      W := Wf
      wB := fun ψ => f₀.s.eval ψ
      s := fun ψ => auxRecSort (Wf ψ) (Wf ψ) (f₀.s.eval ψ) (p.toBlock.elimLevel.eval ψ)
      bb := fun ψ => pwBit ψ (Level.zeronessOf p.toBlock.elimLevel)
      k := fms.length
      n := ctorsA.length
      nP := p.toBlock.nP
      elimL := p.toBlock.elimLevel
      Lof := fun t ψ => mp₂.base2.acval (fms.getD t default).cvTa.name ψ
      nIdxOf := fun t => (fms.getD t default).nIdx
      ppsOf := fun t ψ => (ppsF t ψ).take p.toBlock.nP
      ipsOf := fun t ψ => (ppsF t ψ).drop p.toBlock.nP
      Idss := Idssf
      FssR := FssRf
      Fss₀ := Fss0f
      Ess' := Essf
      rss := rssf
      tlss := tlssf
      EissO := fun ψ => mutEiss0 ctorsA.length eissF ψ
      Eiss' := Eissf
      mems := memF
      tgts := fun J => tgtAt (ksF J)
      cds := fun ψ => fixCtorDataList dsF esF (fun J => kindsOf (ksF J)) eissF tssF ψ ctorsA 0 }
  have hRDs' : ∀ t : Nat, t < prts.k →
      MutualRecData mp₂.base2 (cvRas.getD t default) prts.nP prts.k prts.n (prts.nIdxOf t) t
        prts.elimL (prts.rds mp₂.base2 t) := hRDs
  -- **the member leaf's typing hypotheses** (`MutualLeafHyp`)
  have hyp : prts.LeafHyp V mp₂.base2 := by
    intro t ht ψ
    refine
      { hℓ := rfl
        hb := rfl
        hbz := (pwBit_zeronessOf ψ _).symm
        hlenP := ?hlenP
        hk := hIdssLen ψ
        hLs := by simp [MutualRecParts.Ls]
        hnIdxs := by simp [MutualRecParts.nIdxs]
        hipss := by simp [MutualRecParts.ipss]
        hn := ?hn
        hmm := ht
        hmems := ?hmems
        htgts := ?htgts
        hIdss := ?hIdss
        hleafM := ?hleafM
        hcd := ?hcd
        hframes := ?hframes
        hclL := ?hclL
        hclR := ?hclR
        haux := ?haux
        hauxConc := ?hauxConc
        hstore := ?hstore }
    case hlenP =>
      show (List.take p.toBlock.nP (ppsF 0 ψ)).length = p.toBlock.nP
      rw [List.length_take, (hFD₂ 0 f₀ hf0).len ψ]
      omega
    case hn => exact fixCtorDataList_length _ _ _ _ _ _ _ _
    case hmems => exact fun J hJ => hmotLt J hJ
    case htgts =>
      intro J i
      by_cases hJ : J < ctorsA.length
      · exact (hksJ J _ (hcAGet J hJ)).2.2 i
      · have hk : (kinds.getD J [] : List (RecFieldKind × Nat)) = [] := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [← hlenAK]; omega)]
          rfl
        have h0 : tgtAt (kinds.getD J []) i = 0 := by rw [hk]; simp [tgtAt]
        show tgtAt (kinds.getD J []) i < fms.length
        rw [h0]
        exact hk0
    case hIdss =>
      intro q hq
      have hnq : prts.nIdxs.getD q 0 = prts.nIdxOf q := getD_range_map _ _ _ hq _
      have hgq : (prts.ipss ψ).getD q [] = prts.ipsOf q ψ := getD_range_map _ _ _ hq _
      refine ⟨((ppsF q ψ).drop p.toBlock.nP).map (·.2.2), hIdssGet ψ q hq, ?_, by rw [hgq]⟩
      rw [List.length_map, List.length_drop, (hFD₂ q _ (hfmGet q hq)).len ψ, hnq]
      exact Nat.add_sub_cancel_left _ _
    case hleafM =>
      -- member `q`'s stored leaf is the block's leaf at the BLOCK's
      -- parameter telescope: a λ-tower congruence over `mkLamsAV`
      -- under the pointwise `interp` equality of the two parameter
      -- domains (`hdomM`, `paramFrames`' second component)
      intro q hq ρp _hρ σ
      have hqf := hfmGet q hq
      -- the leaf as it is STORED: member `q`'s OWN parameter telescope
      have hLq : (prts.Ls ψ).getD q default
          = mutualTyAVI (Wf ψ) (f₀.s.eval ψ) (ppsF q ψ) (fms.getD q default).nIdx
              (Idssf ψ) rssf (tlssf ψ) (Eissf ψ) (Fss0f ψ) (Essf ψ) q := by
        rw [show (prts.Ls ψ).getD q default = prts.Lof q ψ from getD_range_map _ _ _ hq _]
        show mp₂.base2.acval (fms.getD q default).cvTa.name ψ = _
        rw [hag₂ _ (fun cA hcA hh => by
            have hs := hfindF q _ hqf
            rw [hh, hfreshC cA hcA] at hs
            exact nomatch hs)]
        exact congrFun (hleaf₁ q _ hqf) ψ
      have hips : (prts.ipss ψ).getD q [] = (ppsF q ψ).drop p.toBlock.nP :=
        getD_range_map _ _ _ hq _
      have hnIq : prts.nIdxs.getD q 0 = (fms.getD q default).nIdx := getD_range_map _ _ _ hq _
      rw [hLq, hips, hnIq]
      -- the leaf is closed, so the two frames agree
      rw [interp_closed V
        (mutualTyAVI_below ((hFD₂ q _ hqf).below ψ) ((hFD₂ q _ hqf).len ψ)
          (hIdsBelow ψ) (hchainBelow ψ)) σ (fun j => ρp (j + p.toBlock.nP))]
      -- the two telescopes differ only in their parameter block
      rw [mutualTyAVI_eq_mkLamsC, mutualTyAVI_eq_mkLamsC]
      show interp V _ (mkLamsAV (((ppsF q ψ)).map fun d => (f₀.s.eval ψ + 1, d.2.2)) _)
        = interp V _ (mkLamsAV ((((ppsF 0 ψ).take p.toBlock.nP
            ++ (ppsF q ψ).drop p.toBlock.nP)).map fun d => (f₀.s.eval ψ + 1, d.2.2)) _)
      rw [show ((ppsF q ψ)).map (fun d => (f₀.s.eval ψ + 1, d.2.2))
            = ((ppsF q ψ).take p.toBlock.nP).map (fun d => (f₀.s.eval ψ + 1, d.2.2))
              ++ ((ppsF q ψ).drop p.toBlock.nP).map (fun d => (f₀.s.eval ψ + 1, d.2.2)) from by
          rw [← List.map_append, List.take_append_drop],
        List.map_append]
      refine mkLamsAV_congr_doms (V := V) (rest := (((ppsF q ψ).drop p.toBlock.nP).map
        fun d => (f₀.s.eval ψ + 1, d.2.2))) ?_
      rw [show ((ppsF q ψ).take p.toBlock.nP).map (fun d => (f₀.s.eval ψ + 1, d.2.2))
          = (((ppsF q ψ).take p.toBlock.nP).map (·.2.2)).map
            (fun A => (f₀.s.eval ψ + 1, A)) from by rw [List.map_map]; rfl,
        show ((ppsF 0 ψ).take p.toBlock.nP).map (fun d => (f₀.s.eval ψ + 1, d.2.2))
          = (((ppsF 0 ψ).take p.toBlock.nP).map (·.2.2)).map
            (fun A => (f₀.s.eval ψ + 1, A)) from by rw [List.map_map]; rfl]
      refine lamDomsAgree_of_rows ?_ ?_
      · rw [List.length_map, List.length_map, List.length_take, List.length_take,
          (hFD₂ q _ hqf).len ψ, (hFD₂ 0 f₀ hf0).len ψ]
        omega
      · intro i hi as hsp
        rw [List.length_map, List.length_take, (hFD₂ q _ hqf).len ψ] at hi
        refine hdomM q _ hqf ψ i (by omega) _ ?_
        have h := sat_of_spineFit (Δ₀ := []) (Sat_nil V _) hsp
        rwa [List.append_nil] at h
    case hcd =>
      -- **BLOCKED** at the second conjunct — see the note at the end
      -- of this proof
      sorry
    case hframes =>
      intro ρp hρ
      have hρ0 : Sat V ((((ppsF 0 ψ).take p.toBlock.nP).map (·.2.2)).reverse) ρp := hρ
      obtain ⟨hTag, hV⟩ := hIdxAll 0 f₀ hf0 ψ ρp hρ0
      obtain ⟨hFix, hRealρ, hXV⟩ := hChainFull 0 f₀ hf0 ψ ρp hρ0
      obtain ⟨hX, -⟩ := hXAll 0 f₀ hf0 ψ ρp hρ0
      -- the constructors' own parameter frames
      have hρJ : ∀ J : Nat, J < ctorsA.length →
          Sat V (((dsF J ψ).take p.toBlock.nP).map (·.2.2)).reverse ρp := by
        intro J hJ
        exact ((hframesJ J hJ).1 ψ ρp).mp
          (hframeAll 0 (memF J) f₀ _ hf0 (hfmGet _ (hmotLt J hJ)) ψ ρp hρ0)
      refine ⟨hTag, hV, hFix, hX,
        fixBodyAVI_validV (auxIds_idxOk hTag) (auxIds_fieldsValid hV) hXV, ?_, ?_, ?_⟩
      · -- `fieldsB`: the REAL field chains are graded at any constructor's frame
        by_cases hne : 0 < ctorsA.length
        · exact (hFssOkP 0 _ (hcAGet 0 hne) ψ ρp (hρJ 0 hne)).1
        · have h0 : ctorsA.length = 0 := by omega
          show SumFieldsOkB _ ρp (mutFss p.toBlock.nP ctorsA.length dsF ψ)
          rw [h0]
          intro Fs hFs
          simp only [mutFss, List.range_zero, List.map_nil] at hFs
          exact nomatch hFs
      · -- `ctor`: the constructor's index expressions at a field spine,
        -- and its value in the auxiliary fibre at its own tag
        -- (`mutualCtorFold` + `fixFamI_app_eq_sum` at the 1-tuple
        -- spine, `sumMkAV_fold`/`restricted_member_intro`)
        sorry
      · -- `slot`: the same at a recursive slot's telescope spine and
        -- its TARGET member's tag (`ChainFacts.gr`'s `SlotFit`)
        sorry
    case hclL =>
      exact auxFormerAV_below (domsBelow_take ((hFD₂ 0 f₀ hf0).below ψ))
        (by rw [List.length_take, (hFD₂ 0 f₀ hf0).len ψ]; omega)
        (hIdsBelow ψ) (hchainBelow ψ)
    case hclR =>
      -- the auxiliary recursor's leaf is closed
      sorry
    case haux =>
      -- `auxRecLeafFacts` (`MutualRecPre2.lean`); its `AuxFrameOk.minors`
      -- goes through `minorTag_facts`, whose `hctorOk` is DESIGN §8.4's
      -- recorded gap (the mixed-regime chain lemma)
      sorry
    case hauxConc =>
      -- `auxConc_facts`' universe component
      sorry
    case hstore =>
      intro ρ
      have hnq : prts.nIdxs.getD t 0 = prts.nIdxOf t := getD_range_map _ _ _ ht _
      rw [hnq]
      exact (hRDs t ht).okTy ψ ρ
  -- **WIP (M2.5f)**: the members' readings and the block's
  -- `MutualRecParts` are in (`hRDs'` is `stageMutualRecs`' `hRDs` at
  -- the bundle, by `rfl`); the recursor stage (`stageMutualRecs`) and
  -- the table stage (`stageMutualTables`) are what is left.
  --
  -- **BLOCKED at `MutualRecParts.LeafHyp`** (`MutualRecTyping.lean`'s
  -- `MutualLeafHyp`, field `hcd`, second conjunct):
  --
  --   `(cd.2.2.1.take nP).map (·.2.2) = pps.map (·.2.2)`
  --
  -- asks for a SYNTACTIC identity of constructor `J`'s parameter
  -- binder READING with the block's, and neither side is free here:
  -- `cd.2.2.1` is pinned to `dsF J ψ` by `CtorReadRT.read` (and again
  -- by `hcd`'s own `hleafC`, whose `sumMkAV wB J cd.2.2.1 …` is what
  -- `stageMutualCtors` stored), while `pps = prts.ppsOf 0 ψ` is pinned
  -- to member `0`'s telescope reading by `FormerReadM.read` through
  -- `mutualRdsAV`'s `ppsOf 0 ψ` — the generated recursor type takes
  -- its parameter Πs from former `0`.  The checker relates the two
  -- only SEMANTICALLY: `checkMutualCtor` compares them with
  -- `checkStructDomsAt`'s `isDefEq` and `mutualCrossChecks` compares
  -- the members' with `mutualDomsOk`'s, which is what `paramFrames`
  -- turns into `hframesJ`/`hframeM` (a `Sat`-iff plus a pointwise
  -- `interp` equality).  Both consumers of the conjunct
  -- (`MutualRecTyping.lean`'s `hsatC` and `MutualRuleFires.lean`'s
  -- `hlenqs`/`hsatC`) only ever transfer `Sat` across it, so the
  -- honest repair is to weaken the conjunct to that iff — a change to
  -- `MutualRecTyping.lean`, which is another lane's file.
  sorry

end ConLeche.Model
