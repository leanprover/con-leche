module

public import ConLeche.Model.Inductives.MutualStageFormer
public import ConLeche.Model.Inductives.MutualStageCtor
public import ConLeche.Model.Inductives.MutualStageRec
public import ConLeche.Model.Inductives.MutualStageTable
public import ConLeche.Model.Inductives.MutualRuleOk
public import ConLeche.Model.Inductives.MutualRuleRead
public import ConLeche.Model.Inductives.MutualRecPre2
public import ConLeche.Semantics.Inductives.DeclMutual
import ConLeche.Model.Inductives.MutualRuleFires
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

**The stage is fully applied**: every conjunct the four stages ask is
discharged here, `stageMutualTables` included.  The last one to fall
was the table stage's block-wide `Prop`-ness bit against the MEMBER's
own result-sort spelling (`d.isProp = (Level.isEquiv f.s .zero == some
true)`), which the checker relates only semantically
(`mutualCrossChecks`' `Level.isEquiv f.s f₀.s = some true`); it needs
no transitivity of `Level.isEquiv`, because at `.zero` that test is
COMPLETE — `simplify` decides the zero level (`isPropBit_congr` and
the kit above it).

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

/-! ## Kit: `Level.isEquiv · .zero` is COMPLETE

The block's `isProp` bit is `Level.isEquiv f₀.s .zero == some true` at
the FIRST member, while `checkStructProjTable` — and `MutualTableOk`
after it — reads each member's OWN result-sort spelling; the checker
relates the two only semantically (`mutualCrossChecks`' `Level.isEquiv
f.s f₀.s = some true`).  Bridging them syntactically looks like
transitivity of `Level.isEquiv`, which the tree does not have — but at
the level `.zero` it needs none: `simplify` DECIDES the zero level, so
`isEquiv · .zero` is complete, and the bit is a function of the
member's sort's MEANING.  (The two lemmas are about `Level` alone and
belong in `Verify/Level.lean`; they live here until a lane owns that
file.) -/

/-- **`simplify` decides the zero level**: a level that evaluates to
`0` under every assignment simplifies to `.zero`.  Structural: a
`param` is nonzero at `fun _ => 1` and a `succ` everywhere; a
simplified `max`'s two sides must both vanish, and a simplified
`imax`'s right side must (else the `imax` takes the `max`, which is at
least its right side). -/
theorem simplify_eq_zero_of_eval : ∀ {a : Level},
    (∀ ψ : Name → Nat, Level.eval ψ a = 0) → Level.simplify a = Level.zero := by
  intro a
  induction a with
  | zero => intro _; rfl
  | param n => intro h; have := h (fun _ => 1); simp [Level.eval] at this
  | succ l _ => intro h; have := h (fun _ => 0); simp [Level.eval] at this
  | max l r ihl ihr =>
    intro h
    have hl : ∀ ψ : Name → Nat, Level.eval ψ l = 0 := by
      intro ψ; have := h ψ; simp only [Level.eval] at this; omega
    have hr : ∀ ψ : Name → Nat, Level.eval ψ r = 0 := by
      intro ψ; have := h ψ; simp only [Level.eval] at this; omega
    show Level.combining (Level.simplify l) (Level.simplify r) = Level.zero
    rw [ihl hl, ihr hr]
    rfl
  | imax l r _ ihr =>
    intro h
    have hr : ∀ ψ : Name → Nat, Level.eval ψ r = 0 := by
      intro ψ
      by_cases hz : Level.eval ψ r = 0
      · exact hz
      · have := h ψ
        simp only [Level.eval, if_neg hz] at this
        omega
    simp only [Level.simplify, ihr hr]
    split <;> rfl

/-- **The completeness `Level.isEquiv_sound` is missing, at `.zero`**:
a level that vanishes under every assignment IS `isEquiv`-equal to
`.zero` — the second disjunct of `isEquiv` (`simplify l = simplify r`,
`isEquiv_eq_withoutPtr`) fires, no `leq` involved. -/
theorem isEquiv_zero_of_eval {a : Level}
    (h : ∀ ψ : Name → Nat, Level.eval ψ a = 0) :
    Level.isEquiv a Level.zero = some true := by
  rw [Level.isEquiv_eq_withoutPtr,
    if_pos (show Level.simplify a = Level.simplify Level.zero from simplify_eq_zero_of_eval h)]
  rfl

/-- The block's `Prop`-ness bit is a function of the member's sort's
MEANING: two levels with the same evaluation everywhere give the same
bit (completeness one way, `isEquiv_sound` the other). -/
theorem isPropBit_congr {a b : Level} (hab : ∀ ψ : Name → Nat, Level.eval ψ a = Level.eval ψ b) :
    (Level.isEquiv a Level.zero == some true) = (Level.isEquiv b Level.zero == some true) := by
  have hcomp : ∀ u : Level, (∀ ψ : Name → Nat, Level.eval ψ u = 0) →
      (Level.isEquiv u Level.zero == some true) = true := fun u hu => by
    rw [isEquiv_zero_of_eval hu]; rfl
  have hsound : ∀ u : Level, (Level.isEquiv u Level.zero == some true) = true →
      ∀ ψ : Name → Nat, Level.eval ψ u = 0 := fun u hu ψ =>
    Level.isEquiv_sound (beq_iff_eq.mp hu) ψ
  exact Bool.eq_iff_iff.mpr
    ⟨fun ha => hcomp b (fun ψ => by rw [← hab ψ]; exact hsound _ ha ψ),
     fun hb => hcomp a (fun ψ => by rw [hab ψ]; exact hsound _ hb ψ)⟩

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

/-- **`EntriesOk` from the binder-by-binder rows**: every entry
graded, valid and — in the graph regime — in the sort `s`, at every
spine fitting the earlier binders. -/
theorem entriesOk_of_rows {s : Nat} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      (∀ (k : Nat) (d : Nat × Nat × AnnotTerm), ds[k]? = some d →
        ∀ as : List V, SpineFit ρ ((ds.map (·.2.2)).take k) as →
          WellDenotedV V (consList as ρ) d.2.2 ∧
            (s ≠ 0 → interp V (consList as ρ) d.2.2 ∈ˢ (univ s : V))) →
      EntriesOk V s ρ ds
  | [], _, _ => trivial
  | d :: ds, ρ, h => by
    obtain ⟨hok, hu⟩ := h 0 d rfl [] trivial
    refine ⟨hok, hu, fun a ha => entriesOk_of_rows fun k d' hk as hsp => ?_⟩
    have h' := h (k + 1) d' (by simpa using hk) (a :: as) ⟨ha, hsp⟩
    rwa [consList_cons] at h'

/-- **The parameter binders as the auxiliary recursor's entries**: the
former's Π-tower grades them hereditarily and `FormerData.lvls` puts
each in its own universe, which the recursor's sort dominates. -/
theorem formerParamsOk {env : Env} {m : EnvModel V env} {cvT : ConstantVal} {nP nIdx : Nat}
    {resSort : Level} {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {lvls : (Name → Nat) → List Nat}
    (hFD : FormerData m cvT (nP + nIdx) resSort pps lvls)
    {s b : Nat} {ψ : Name → Nat} (hu : s ≠ 0 → ∀ i, i < nP → (lvls ψ).getD i 0 ≤ s)
    (ρb : Nat → V) : EntriesOk V s ρb (rebit b ((pps ψ).take nP)) := by
  have hlen : (pps ψ).length = nP + nIdx := hFD.len ψ
  have hlenT : ((pps ψ).take nP).length = nP := by rw [List.length_take]; omega
  obtain ⟨hokB, -⟩ := WellDenoted_mkPisAV_inv (hFD.okTy ψ ρb).1
  obtain ⟨hvB, -⟩ := AnnotValid_mkPisAV_inv (hFD.okTy ψ ρb).2
  refine entriesOk_of_rows fun k d hk as hsp => ?_
  have hkl : k < nP := by
    have h := (List.getElem?_eq_some_iff.mp hk).1
    rw [rebit_length, hlenT] at h
    exact h
  have hdk : d.2.2 = ((pps ψ).map (·.2.2)).getD k default := by
    have h1 : (rebit b ((pps ψ).take nP))[k]? = some d := hk
    rw [rebit, List.getElem?_map, List.getElem?_take_of_lt hkl,
      List.getElem?_eq_getElem (show k < (pps ψ).length by omega)] at h1
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (show k < (pps ψ).length by omega), ← Option.some.inj h1]
    rfl
  have hsp' : SpineFit ρb (((pps ψ).map (·.2.2)).take k) as := by
    have h1 : SpineFit ρb (((rebit b ((pps ψ).take nP)).map (·.2.2)).take k) as := hsp
    rwa [rebit_map_dom, ← List.map_take, List.take_take,
      Nat.min_eq_left (Nat.le_of_lt hkl), List.map_take] at h1
  have hsat : Sat V ((((pps ψ).take k).map (·.2.2)).reverse) (consList as ρb) := by
    have h := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρb)
      (show SpineFit ρb ((((pps ψ).take k).map (·.2.2))) as by rwa [List.map_take])
    rwa [List.append_nil] at h
  have hentry : ((pps ψ).map (·.2.2)).getD k default = ((pps ψ).getD k default).2.2 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (show k < (pps ψ).length by omega)]
    rfl
  refine ⟨⟨?_, ?_⟩, fun hs => ?_⟩
  · rw [hdk]
    exact fieldsOkB_getD hokB (by rw [List.length_map]; omega) hsp'
  · rw [hdk]
    exact fieldsValid_getD hvB (by rw [List.length_map]; omega) hsp'
  · rw [hdk, hentry]
    exact univ_mono (hu hs k hkl) _ (hFD.lvl ψ k (by omega) (consList as ρb) hsat)

/-- **A leaf's hereditary premise over an appended telescope**: the
leading binders graded and in the graph regime, the premise at every
spine fitting them. -/
theorem paramsOkXI_append {u w : Nat} {Ids : List AnnotTerm} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
    {Fss Ess : List (List AnnotTerm)} :
    ∀ {ds rest : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      (∀ d ∈ ds, d.2.1 ≠ 0) → FieldsOkB 0 ρ (ds.map (·.2.2)) →
      (∀ as : List V, SpineFit ρ (ds.map (·.2.2)) as →
        ParamsOkXI u w (consList as ρ) Ids rss tlss Eiss Fss Ess rest) →
      ParamsOkXI u w ρ Ids rss tlss Eiss Fss Ess (ds ++ rest)
  | [], _, _, _, _, h => by simpa using h [] trivial
  | d :: ds, rest, ρ, hb, hok, h => by
    refine ⟨hb d List.mem_cons_self, hok.1, fun a ha => ?_⟩
    refine paramsOkXI_append (ds := ds) (fun d' hd' => hb d' (List.mem_cons_of_mem _ hd'))
      (hok.2.2 a ha) fun as hsp => ?_
    have h' := h (a :: as) ⟨ha, hsp⟩
    rwa [consList_cons] at h'

/-- The same for the λ-tower's bit validity. -/
theorem underTowerValid_append {b : AnnotTerm} :
    ∀ {ds rest : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      FieldsValid ρ (ds.map (·.2.2)) →
      (∀ as : List V, SpineFit ρ (ds.map (·.2.2)) as → UnderTowerValid (consList as ρ) b rest) →
      UnderTowerValid ρ b (ds ++ rest)
  | [], _, _, _, h => by simpa using h [] trivial
  | d :: ds, rest, ρ, hv, h => by
    refine ⟨hv.1, fun a ha => ?_⟩
    refine underTowerValid_append (ds := ds) (hv.2 a ha) fun as hsp => ?_
    have h' := h (a :: as) ⟨ha, hsp⟩
    rwa [consList_cons] at h'

/-- **A stored rule's shape, positionally**: it is `recRuleBits` of the
generated record at one of the member's own constructors. -/
theorem mutualRules_getElem? {find? : Name → Option ConstantInfo} {recName : Name}
    {nP mI rP : Nat} {recTy : Expr} :
    ∀ {l : List (MutualCtor × Expr)} {r : RecRule},
      r ∈ ConLeche.mutualRules find? recName nP mI rP recTy l →
      ∃ cr ∈ l, r = ConLeche.recRuleBits find? recName
        { ctor := cr.1.cv.name, nfields := cr.1.nF, ctorParams := nP,
          fire := if Expr.recRulePlain recTy mI rP nP then .plain else .inert,
          rhs := cr.2, paramsBlind := true }
  | [], _, h => by simp [ConLeche.mutualRules] at h
  | cr :: cs, r, h => by
    simp only [ConLeche.mutualRules, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨cr, List.mem_cons_self, rfl⟩
    · obtain ⟨cr', hm, he⟩ := mutualRules_getElem? h
      exact ⟨cr', List.mem_cons_of_mem _ hm, he⟩

/-! ## Kit: the group store's environment extension

The store conses the `k` recursors onto the constructors' carrier, so
every lookup, literal guard and projection table there survives — which
is all `denoteMeta_envExtend_mono` asks to carry a reading across. -/

/-- A lookup past the store's conses at a name none of them carries. -/
theorem storeMutualRecs_find?_of_ne {b : MutualBlock} {fms : List MutualFormerA}
    {rulesOf : List (List (MutualCtor × Expr))} {env₂ : Env} :
    ∀ {l : List (ConstantVal × Nat)} {env : Env} {n : Name},
      (∀ x ∈ l, n ≠ x.1.name) →
      (ConLeche.storeMutualRecs env₂ b fms rulesOf l env).find? n = env.find? n
  | [], _, _, _ => rfl
  | (cvRa, mIdx) :: rest, env, n, hne => by
    show (ConLeche.storeMutualRecs env₂ b fms rulesOf rest _).find? n = _
    rw [storeMutualRecs_find?_of_ne (fun x hx => hne x (List.mem_cons_of_mem _ hx))]
    exact find?_cons_of_name_ne (c := .recInfo cvRa
      (b.rulePrefix + (fms.getD mIdx default).nIdx) b.rulePrefix
      (ConLeche.mutualRules env₂.find? cvRa.name b.nP
        (b.rulePrefix + (fms.getD mIdx default).nIdx) b.rulePrefix cvRa.type
        (rulesOf.getD mIdx [])))
      (fun hh => hne (cvRa, mIdx) List.mem_cons_self hh.symm)

/-- The store finds each of its own heads. -/
theorem storeMutualRecs_find?_self {b : MutualBlock} {fms : List MutualFormerA}
    {rulesOf : List (List (MutualCtor × Expr))} {env₂ : Env} :
    ∀ {l : List (ConstantVal × Nat)} {env : Env} {x : ConstantVal × Nat},
      x ∈ l → (l.map (·.1.name)).Nodup →
      (ConLeche.storeMutualRecs env₂ b fms rulesOf l env).find? x.1.name
        = some (.recInfo x.1 (b.rulePrefix + (fms.getD x.2 default).nIdx) b.rulePrefix
            (ConLeche.mutualRules env₂.find? x.1.name b.nP
              (b.rulePrefix + (fms.getD x.2 default).nIdx) b.rulePrefix x.1.type
              (rulesOf.getD x.2 [])))
  | (cvRa, mIdx) :: rest, env, x, hx, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hx with rfl | hx'
    · show (ConLeche.storeMutualRecs env₂ b fms rulesOf rest _).find? cvRa.name = _
      rw [storeMutualRecs_find?_of_ne
        (fun y hy hh => hnd.1 (by rw [hh]; exact List.mem_map_of_mem hy))]
      exact ConLeche.Env.find?_cons_self _ _
    · show (ConLeche.storeMutualRecs env₂ b fms rulesOf rest _).find? x.1.name = _
      exact storeMutualRecs_find?_self hx' hnd.2

/-- **The store's extension facts**: the `k` heads are fresh at the
carrier and carry distinct names, so the three inputs of
`denoteMeta_envExtend_mono` hold. -/
theorem storeMutualRecs_extend {b : MutualBlock} {fms : List MutualFormerA}
    {rulesOf : List (List (MutualCtor × Expr))} {env₂ : Env} :
    ∀ {l : List (ConstantVal × Nat)} {env : Env},
      (∀ x ∈ l, env.find? x.1.name = none) → (l.map (·.1.name)).Nodup →
      FindPreserved env (ConLeche.storeMutualRecs env₂ b fms rulesOf l env) ∧
      LitGuardsMono env (ConLeche.storeMutualRecs env₂ b fms rulesOf l env) ∧
      ∀ (sn : Name) (i : Nat), env.findProj? sn i = none →
        (ConLeche.storeMutualRecs env₂ b fms rulesOf l env).findProj? sn i = none
  | [], _, _, _ => ⟨fun h => h, ⟨id, id⟩, fun _ _ h => h⟩
  | (cvRa, mIdx) :: rest, env, hfr, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have hfresh : env.find? cvRa.name = none := hfr (cvRa, mIdx) List.mem_cons_self
    have hntc : ∀ tbl : ConLeche.ProjTable,
        (ConstantInfo.recInfo cvRa (b.rulePrefix + (fms.getD mIdx default).nIdx) b.rulePrefix
          (ConLeche.mutualRules env₂.find? cvRa.name b.nP
            (b.rulePrefix + (fms.getD mIdx default).nIdx) b.rulePrefix cvRa.type
            (rulesOf.getD mIdx []))) ≠ .projInfo tbl := by
      intro tbl h
      exact nomatch h
    have hfr' : ∀ x ∈ rest,
        (⟨ConstantInfo.recInfo cvRa (b.rulePrefix + (fms.getD mIdx default).nIdx) b.rulePrefix
            (ConLeche.mutualRules env₂.find? cvRa.name b.nP
              (b.rulePrefix + (fms.getD mIdx default).nIdx) b.rulePrefix cvRa.type
              (rulesOf.getD mIdx [])) :: env.consts⟩ : Env).find? x.1.name = none := by
      intro x hx
      rw [find?_cons_of_name_ne (c := .recInfo cvRa
        (b.rulePrefix + (fms.getD mIdx default).nIdx) b.rulePrefix
        (ConLeche.mutualRules env₂.find? cvRa.name b.nP
          (b.rulePrefix + (fms.getD mIdx default).nIdx) b.rulePrefix cvRa.type
          (rulesOf.getD mIdx [])))
        (show ¬ cvRa.name = x.1.name from fun hh =>
          hnd.1 (by rw [hh]; exact List.mem_map_of_mem hx))]
      exact hfr x (List.mem_cons_of_mem _ hx)
    obtain ⟨hF, hG, hP⟩ := storeMutualRecs_extend (l := rest) hfr' hnd.2
    refine ⟨fun h => hF (findPreserved_cons hfresh h), ?_, fun sn i h => ?_⟩
    · exact ⟨fun h => hG.1 ((litGuardsMono_cons hfresh).1 h),
        fun h => hG.2 ((litGuardsMono_cons hfresh).2 h)⟩
    · exact hP sn i (ConLeche.Verify.findProj?_cons_of_base_none hntc sn i h)

/-- **A reading crosses the group store**: the `k` recursor heads are
fresh at the constructors' carrier and the store's carrier agrees with
it on every name found there, so a prefix reading is reproduced
verbatim (`denoteMeta_acval_congr` then `denoteMeta_envExtend_mono`). -/
theorem denoteMeta_toStore {b : MutualBlock} {fms : List MutualFormerA}
    {rulesOf : List (List (MutualCtor × Expr))} {env₂ : Env}
    {acval acv : Name → (Name → Nat) → AnnotTerm} {l : List (ConstantVal × Nat)}
    (hfr : ∀ x ∈ l, env₂.find? x.1.name = none) (hndl : (l.map (·.1.name)).Nodup)
    (hag : ∀ n, (env₂.find? n).isSome = true → acval n = acv n)
    (ψ : Name → Nat) (d : Nat) (e : Expr) (hcb : ConstsBound env₂ e)
    {ea : AnnotTerm} (h : denoteMeta acval env₂ ψ d e = some ea) :
    denoteMeta acv (ConLeche.storeMutualRecs env₂ b fms rulesOf l env₂) ψ d e = some ea := by
  obtain ⟨hF, hG, hP⟩ := storeMutualRecs_extend (b := b) (fms := fms) (rulesOf := rulesOf)
    (env₂ := env₂) hfr hndl
  refine denoteMeta_envExtend_mono hF hG hP d e hcb ?_
  rw [← denoteMeta_acval_congr hag d e]
  exact h

/-- **A rule's binder data at two carriers**: agreeing on every
constructor's leaf is enough. -/
theorem mutualRuleDataAV_congrm {env' : Env} {m : EnvModel V env} {m' : EnvModel V env'}
    {ψ : Name → Nat} {Ls : List AnnotTerm} {nP : Nat} {nIdxs : List Nat} {ℓ : Level}
    {pps : List (Nat × Nat × AnnotTerm)} {ipss : List (List (Nat × Nat × AnnotTerm))}
    {cds : List CtorDatumR} {mots : Nat → Nat} {tgts : Nat → Nat → Nat}
    {ds : List (Nat × Nat × AnnotTerm)}
    (h : ∀ cd ∈ cds, m.acval cd.1 ψ = m'.acval cd.1 ψ) :
    mutualRuleDataAV m ψ Ls nP nIdxs ℓ pps ipss cds mots tgts ds
      = mutualRuleDataAV m' ψ Ls nP nIdxs ℓ pps ipss cds mots tgts ds := by
  unfold mutualRuleDataAV
  rw [fixMinorsDataM_congrm _ _ cds Ls.length h]

/-- **A rule's core at two leaf tables**: only the recursive slots'
TARGET recursors are read. -/
theorem mutualRuleCoreAV_congr_Rof {b : Nat} {Rof Rof' : Nat → AnnotTerm} {tgts : Nat → Nat}
    {nP k n nF j : Nat} {recIdx : List Nat}
    {tls : List (List (Nat × Nat × AnnotTerm))} {Eiss : List (List AnnotTerm)}
    (h : ∀ i ∈ recIdx, Rof (tgts i) = Rof' (tgts i)) :
    mutualRuleCoreAV b Rof tgts nP k n nF j recIdx tls Eiss
      = mutualRuleCoreAV b Rof' tgts nP k n nF j recIdx tls Eiss := by
  unfold mutualRuleCoreAV
  congr 2
  exact List.map_congr_left fun i hi => by rw [h i hi]

/-- **A member's reading crosses an environment extension**: its type
resolves at the smaller environment and its own leaf does not move. -/
theorem FormerReadM.crossEnv {env env' : Env} {m : EnvModel V env} {m' : EnvModel V env'}
    {ψ : Name → Nat} {lps : List Name} {nP : Nat} {f : ConLeche.MutualFormer} {L : AnnotTerm}
    {nIdx : Nat} {pps ips : List (Nat × Nat × AnnotTerm)}
    (h : FormerReadM m ψ lps nP f L nIdx pps ips)
    (hcb : ConstsBound env f.tty)
    (hF : FindPreserved env env') (hG : LitGuardsMono env env')
    (hproj : ∀ (sn : Name) (i : Nat), env.findProj? sn i = none → env'.findProj? sn i = none)
    (hag : ∀ n : Name, (env.find? n).isSome = true → m.acval n = m'.acval n) :
    FormerReadM m' ψ lps nP f L nIdx pps ips where
  find := by
    obtain ⟨ci, hci, hlp⟩ := h.find
    exact ⟨ci, hF hci, hlp⟩
  leaf := by
    obtain ⟨ci, hci, -⟩ := h.find
    rw [h.leaf, hag f.name (by rw [hci]; rfl)]
  idxCount := h.idxCount
  hasFvar := h.hasFvar
  bounded := h.bounded
  stripP := h.stripP
  strip := h.strip
  read := by
    obtain ⟨ppsAll, w, hr, hl, hp, hi⟩ := h.read
    refine ⟨ppsAll, w, ?_, hl, hp, hi⟩
    refine denoteMeta_envExtend_mono hF hG hproj 0 f.tty hcb ?_
    rw [← denoteMeta_acval_congr hag]
    exact hr

/-- **A constructor's reading crosses an environment extension**: its
type resolves at the smaller environment, and neither its own member's
leaf nor any target member's moves. -/
theorem CtorReadRT.crossEnv {env env' : Env} {m : EnvModel V env} {m' : EnvModel V env'}
    {ψ : Name → Nat} {T : Name} {Tt : Nat → Name} {lps : List Name} {nP nIdx : Nat}
    {nIt : Nat → Nat} {c : Name × Nat × Expr × List Nat} {cd : CtorDatumR}
    (h : CtorReadRT m ψ T Tt lps nP nIdx nIt c cd)
    (hcb : ConstsBound env c.2.2.1)
    (hF : FindPreserved env env') (hG : LitGuardsMono env env')
    (hproj : ∀ (sn : Name) (i : Nat), env.findProj? sn i = none → env'.findProj? sn i = none)
    (hag : ∀ n : Name, (env.find? n).isSome = true → m.acval n = m'.acval n)
    (hagT : m.acval T ψ = m'.acval T ψ)
    (hagTt : ∀ i ∈ c.2.2.2, m.acval (Tt i) ψ = m'.acval (Tt i) ψ) :
    CtorReadRT m' ψ T Tt lps nP nIdx nIt c cd where
  name := h.name
  nF := h.nF
  find := by
    obtain ⟨ci, hci, hlp⟩ := h.find
    exact ⟨ci, hF hci, hlp⟩
  hasFvar := h.hasFvar
  bounded := h.bounded
  resid := h.resid
  read := by
    rw [← hagT]
    refine denoteMeta_envExtend_mono hF hG hproj 0 c.2.2.1 hcb ?_
    rw [← denoteMeta_acval_congr hag]
    exact h.read
  len := h.len
  lenE := h.lenE
  recIdx := h.recIdx
  recIdxBnd := h.recIdxBnd
  recIdxSorted := h.recIdxSorted
  eissLen := h.eissLen
  eisLen := h.eisLen
  tlsLen := h.tlsLen
  teleLen := h.teleLen
  fieldRead := fun i hi fvs o hop x hx => by
    obtain ⟨hfvs, -⟩ := openPisAtFvars_constsBound (nP + c.2.1) hcb hop
    obtain ⟨ty, hy⟩ := (opening_vars_at hop).2.1 (nP + i) x hx
    have hb := hfvs x (List.mem_of_getElem? hx)
    rw [hy, constsBound_fvar] at hb
    refine denoteMeta_envExtend_mono hF hG hproj (nP + i) x.fvarTypeD ?_ ?_
    · rw [hy]; exact hb
    · rw [← denoteMeta_acval_congr hag]
      exact h.fieldRead i hi fvs o hop x hx
  fieldArity := h.fieldArity
  recEntry := fun i hi => by
    rw [← hagTt i hi]
    exact h.recEntry i hi

/-! ## Kit: the generated right-hand side reads only the block's recursors

`mutualRecRhs` names a recursor only at a recursive field's TARGET
member, and those are all block members; `denoteMeta_mutualRecRhs`
asks for its `recOf` to be stored at EVERY index, so the caller passes
a total table agreeing with `MutualBlock.recName` below `k`. -/

theorem mutualIhApp_congr_recOf {recOf recOf' : Nat → Name} {rlvls : List Level}
    {pw : ConLeche.PropWhen} {nP k n nF i m' : Nat} {tele : List (Expr × BinderMeta)}
    {idx : List Expr} (h : recOf m' = recOf' m') :
    ConLeche.mutualIhApp recOf rlvls pw nP k n nF i m' tele idx
      = ConLeche.mutualIhApp recOf' rlvls pw nP k n nF i m' tele idx := by
  unfold ConLeche.mutualIhApp
  rw [h]

theorem mutualRuleBody_congr_recOf {recOf recOf' : Nat → Name} {rlvls : List Level}
    {pw : ConLeche.PropWhen} {nP k n nF J : Nat} {recFields : List (Nat × Nat)}
    {teleOf : Nat → List (Expr × BinderMeta)} {idxOf : Nat → List Expr}
    (h : ∀ im ∈ recFields, recOf im.2 = recOf' im.2) :
    ConLeche.mutualRuleBody recOf rlvls pw nP k n nF J recFields teleOf idxOf
      = ConLeche.mutualRuleBody recOf' rlvls pw nP k n nF J recFields teleOf idxOf := by
  unfold ConLeche.mutualRuleBody
  congr 2
  exact List.map_congr_left fun im him => mutualIhApp_congr_recOf (h im him)

theorem mutualRecRhs_congr_recOf {lps : List Name} {elim : Name} {large : Bool} {nP : Nat}
    {formers : List ConLeche.MutualFormer} {ctors : List ConLeche.MutualCtor4}
    {recOf recOf' : Nat → Name} {rlvls : List Level} {J : Nat}
    (h : ∀ c ∈ ctors, ∀ im ∈ c.recFields, recOf im.2 = recOf' im.2) :
    ConLeche.mutualRecRhs lps elim large nP formers ctors recOf rlvls J
      = ConLeche.mutualRecRhs lps elim large nP formers ctors recOf' rlvls J := by
  unfold ConLeche.mutualRecRhs
  cases hc : ctors[J]? with
  | none => rfl
  | some c =>
    cases hf : formers[0]? with
    | none => rfl
    | some f₀ =>
      simp only []
      rw [mutualRuleBody_congr_recOf (h c (List.mem_of_getElem? hc))]

/-! ## Kit: the block's `.proj` bookkeeping

The table stage asks that no stored piece mentions `T.proj j` for a
member `T`.  The pre-block environment gives it for free (`T` is fresh
there, and a `.proj T j` node needs `T` stored), and the block's own
conses give it because every piece is either read before the block or
GENERATED from pieces that are (`MutualRuleFires.lean`'s `NoProj`
section). -/

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

/-- An empty projection slot survives the constructors' conses. -/
theorem findProj?_none_consMutualCtors {T : Name} {i nP : Nat} :
    ∀ {ctorsA : List (ConstantVal × Nat)} {env₀ : Env}, env₀.findProj? T i = none →
      (ConLeche.consMutualCtors nP ctorsA env₀).findProj? T i = none
  | [], _, h => h
  | _ :: _, _, h => by
    simp only [ConLeche.consMutualCtors]
    exact findProj?_none_consMutualCtors
      (findProj?_none_cons (fun _ hh => ConstantInfo.noConfusion hh) h)

/-- An empty projection slot survives the recursors' group store. -/
theorem findProj?_none_storeMutualRecs {T : Name} {i : Nat} {envR : Env}
    {b : ConLeche.MutualBlock} {fms : List MutualFormerA}
    {rulesOf : List (List (ConLeche.MutualCtor × Expr))} :
    ∀ {l : List (ConstantVal × Nat)} {env₀ : Env}, env₀.findProj? T i = none →
      (ConLeche.storeMutualRecs envR b fms rulesOf l env₀).findProj? T i = none
  | [], _, h => h
  | _ :: _, _, h => by
    simp only [ConLeche.storeMutualRecs]
    exact findProj?_none_storeMutualRecs
      (findProj?_none_cons (fun _ hh => ConstantInfo.noConfusion hh) h)

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

/-- `NoProjEnv` across the recursors' group store. -/
theorem noProjEnv_storeMutualRecs {T : Name} {i : Nat} {envR : Env} {b : ConLeche.MutualBlock}
    {fms : List MutualFormerA} {rulesOf : List (List (ConLeche.MutualCtor × Expr))} :
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
    refine ⟨(hall _ List.mem_cons_self).2 r hr, ?_⟩
    intro lvls pins hfire
    obtain ⟨cr, -, rfl⟩ := mutualRules_getElem? hr
    simp only [ConLeche.recRuleBits] at hfire
    split at hfire <;> exact nomatch hfire

/-! ## The rule's grading, off the member leaf's hypotheses -/

set_option maxHeartbeats 3200000 in
/-- **The mutual rule's right-hand side is graded** (task #278 M2.5f):
`mutualRuleOk` at `MutualLeafHyp`'s data.  Everything but the leaf
table's own four facts is read off the block's hypotheses — the minors'
spaces (`interp_minorAVAtRM`), the constructors' chains and index
readings (`MutualFrameOkM`), the inductive hypotheses' spines
(`mutualIhSpine_of`) and, in the `Prop` regime, the motives' own spaces
(`interp_memberMotive` at `piTele_app_univZero`). -/
theorem mutualRuleOk_of {env : Env} {m : EnvModel V env} {ψ : Name → Nat} {elimL : Level}
    {ℓ W wB nP s b k n : Nat} {Ls : List AnnotTerm} {nIdxs : List Nat}
    {pps : List (Nat × Nat × AnnotTerm)} {ipss : List (List (Nat × Nat × AnnotTerm))}
    {Idss : List (List AnnotTerm)} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
    {EissO Eiss' : List (List (List AnnotTerm))} {FssR Fss₀ Ess' : List (List AnnotTerm)}
    {mems : Nat → Nat} {tgts : Nat → Nat → Nat} {cds : List CtorDatumR} {mm : Nat}
    (hmm : mm < k)
    (hall : ∀ t, t < k → MutualLeafHyp V m ψ elimL ℓ W wB nP s b k n Ls nIdxs pps ipss Idss
      rss tlss EissO Eiss' FssR Fss₀ Ess' mems tgts cds t)
    -- the constructors' field chains are bit-valid at the parameter frame
    (hFssV : ∀ ρp : Nat → V, Sat V ((pps.map (·.2.2)).reverse) ρp → SumFieldsValid ρp FssR)
    -- a recursive slot's telescope is graded and valid, and the field
    -- applies along it (`SlotTagOk`'s UNTAGGED half)
    (hslots : ∀ ρp : Nat → V, Sat V ((pps.map (·.2.2)).reverse) ρp →
      ∀ (q : Nat) (cdq : CtorDatumR), cds[q]? = some cdq →
      ∀ fs : List V, SpineFit ρp ((cdq.2.2.1.drop nP).map (·.2.2)) fs →
      ∀ i ∈ recIdx (rss.getD q []) cdq.2.1,
        FieldsOkB wB (consList (fs.take i) ρp) (((tlss.getD q []).getD i []).map (·.2.2)) ∧
        FieldsValid (consList (fs.take i) ρp) (((tlss.getD q []).getD i []).map (·.2.2)) ∧
        ∀ bs : List V, SpineFit (consList (fs.take i) ρp)
          (((tlss.getD q []).getD i []).map (·.2.2)) bs → AppChainOk (fs.getD i pt) bs)
    {J : Nat} {cd : CtorDatumR} (hcdJ : cds[J]? = some cd)
    -- the constructor's index readings, and its slots', have the
    -- TARGET member's index count
    (hEsLenJ : cd.2.2.2.1.length = nIdxs.getD (mems J) 0)
    (hEisLenJ : ∀ i ∈ recIdx (rss.getD J []) cd.2.1,
      ((EissO.getD J []).getD i []).length = nIdxs.getD (tgts J i) 0)
    -- the leaf table's own facts
    {Rof : Nat → AnnotTerm}
    (hRcl : ∀ t, Term.bvarsBelow 0 (Rof t).erase)
    (hRok : ∀ (t : Nat) (σ : Nat → V), WellDenotedV V σ (Rof t))
    (hRmem : ∀ t, t < k → ∀ σ : Nat → V, interp V σ (Rof t) ∈ˢ interp V σ
      (mkPisAV (mutualRecDataAV m ψ Ls nP nIdxs elimL pps ipss cds mems tgts t)
        (mutualConcAV k n (nIdxs.getD t 0) t)))
    (ρ : Nat → V) :
    WellDenotedV V ρ
      (mkLamsAV (mutualRuleDataAV m ψ Ls nP nIdxs elimL pps ipss cds mems tgts cd.2.2.1)
        (mutualRuleCoreAV b Rof (tgts J) nP k n cd.2.1 J cd.2.2.2.2.1 cd.2.2.2.2.2.2
          cd.2.2.2.2.2.1)) := by
  have hh := hall mm hmm
  obtain ⟨hlenDs, htakeP, hleafC, hclC, hFsj, hrecIdxJ, htlsJ, hEissOJ, hEiss'J⟩ :=
    hh.hcd J cd hcdJ
  have hJn : J < n := by
    have h := (List.getElem?_eq_some_iff.mp hcdJ).1
    rwa [hh.hn] at h
  have hIdsLen : ∀ t, t < k → (Idss.getD t []).length = nIdxs.getD t 0 := by
    intro t ht
    obtain ⟨Ids, hIds, hlenIds, -⟩ := hh.hIdss t ht
    rw [List.getD_eq_getElem?_getD, hIds, Option.getD_some, hlenIds]
  -- **the motives' spaces** at a fitting motive spine
  have hmotSp : ∀ ρp : Nat → V, Sat V ((pps.map (·.2.2)).reverse) ρp →
      ∀ Ms : List V, SpineFit ρp ((motivesDataGo (fun t => Ls.getD t default)
          (fun t => nIdxs.getD t 0) (fun t => ipss.getD t []) ψ nP elimL b k 0).map (·.2.2)) Ms →
      ∀ t, t < k → Ms.getD t pt ∈ˢ memberMotSp ℓ W wB ρp Idss rss tlss Eiss' Fss₀ Ess' t := by
    intro ρp hsatP Ms hspM t ht
    have hF := hh.hframes ρp hsatP
    obtain ⟨Ids', hIds', hlenIds', hipd'⟩ := hh.hIdss t ht
    have hlenTake : (Ms.take t).length = t := by
      rw [List.length_take, hspM.length_eq, List.length_map, motivesDataGo_length]
      omega
    have hmem := FixKI.spineFit_getD_mem' hspM (l := t)
      (by rw [List.length_map, motivesDataGo_length]; exact ht)
    have hentry : ((motivesDataGo (fun q => Ls.getD q default) (fun q => nIdxs.getD q 0)
        (fun q => ipss.getD q []) ψ nP elimL b k 0).map (·.2.2)).getD t default
        = (motiveAVIL (Ls.getD t default) ψ nP (nIdxs.getD t 0) elimL
            (ipss.getD t [])).liftN (0 + t) 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map,
        motivesDataGo_getElem? _ _ _ ψ nP elimL b k 0 t ht]
      rfl
    have hsh : shiftE t 0 (consList (Ms.take t) ρp) = ρp := by
      simpa [hlenTake] using shiftE_consList (Ms.take t) ρp
    rw [hentry, interp_liftN, Nat.zero_add, hsh,
      interp_memberMotive hh.hℓ hh.hlenP hipd' hlenIds' hsatP hF.tag hF.chains hIds'
        (fun σ' => hh.hleafM t ht _ hsatP σ')] at hmem
    exact hmem
  refine mutualRuleOk (Ess := cds.map (·.2.2.2.1)) (Fss := FssR) (Eiss := EissO) (tlss := tlss)
    (rss := rss) (mm := mm) (Rof := Rof)
    hh.hbz hh.hb hh.hLs hh.hlenP hh.hn hcdJ hlenDs hFsj ?_ hrecIdxJ hEissOJ.symm htlsJ.symm
    hleafC hclC (fun ρp => (htakeP ρp).symm) (hh.hmems J hJn) (fun i _ => hh.htgts J i)
    hEisLenJ hh.hstore hRcl hRok hRmem ?_ ?_ ?_ ?_ ?_ ?_ ?_ ρ
  · -- the constructors' index readings, positionally
    rw [List.getElem?_map, hcdJ]
    rfl
  · -- `hRconc0`: a `Prop` conclusion is a truth value
    intro h0 t ht σ as hsp
    exact (mutualRecBody_facts (hall t ht) σ as hsp).2.2 (hh.hbz.mp h0)
  · -- `hminor`: the minor premise reads the ih-extended minor space
    intro ρp hsatP Ms hlenMs q cdq hcdq ms hlenms
    have hF := hh.hframes ρp hsatP
    obtain ⟨hlenDsq, htakePq, hleafCq, hclCq, hFsjq, hrecIdxq, htlsq, hEissOq, -⟩ :=
      hh.hcd q cdq hcdq
    have hqn : q < n := by
      have h := (List.getElem?_eq_some_iff.mp hcdq).1
      rwa [hh.hn] at h
    have hEssq : (cds.map (·.2.2.2.1)).getD q [] = cdq.2.2.2.1 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, hcdq]
      rfl
    have hFssq : FssR.getD q [] = (cdq.2.2.1.drop nP).map (·.2.2) := by
      rw [List.getD_eq_getElem?_getD, hFsjq]
      rfl
    rw [hrecIdxq, htlsq, hEissOq, hEssq, hFssq]
    exact interp_minorAVAtRM (Ms := Ms) (ℓ := ℓ) (Fss := FssR) (rss := rss) (tlss := tlss)
      (Eiss := EissO) hh.hbz hlenMs hlenms (hh.hmems q hqn) hlenDsq
      (fun i _ => hh.htgts q i) hleafCq hclCq hFsjq hF.fieldsB ((htakePq ρp).mpr hsatP)
  · -- `hfields`: the chains are graded and valid
    intro ρp hsatP
    have hF := hh.hframes ρp hsatP
    have hmemF : (cd.2.2.1.drop nP).map (·.2.2) ∈ FssR := List.mem_of_getElem? hFsj
    exact ⟨hF.fieldsB, hF.fieldsB _ hmemF, hFssV ρp hsatP _ hmemF⟩
  · -- `hteles`: a recursive slot's telescope, and its index readings
    intro ρp hsatP as₂ hsp i hi
    have hF := hh.hframes ρp hsatP
    obtain ⟨hok, hval, hchain⟩ := hslots ρp hsatP J cd hcdJ as₂ hsp i hi
    exact ⟨hok, hval, fun bs hbs =>
      ⟨fun E hE => ((hF.slot J cd hcdJ i hi as₂ hsp bs hbs).1 E hE).1,
        fun E hE => ((hF.slot J cd hcdJ i hi as₂ hsp bs hbs).1 E hE).2, hchain bs hbs⟩⟩
  · -- `hih`: the inductive hypothesis' own spine
    intro ρ' as₁ Ms ms as₂ hlen₁ hlenMs hspB hspD i hi bs hbs
    have hpre : (mutualRecDataAV m ψ Ls nP nIdxs elimL pps ipss cds mems tgts mm).take
          (nP + k + n)
        = rebit b pps ++ motivesDataGo (fun t => Ls.getD t default) (fun t => nIdxs.getD t 0)
            (fun t => ipss.getD t []) ψ nP elimL b k 0
          ++ fixMinorsDataM mems tgts m ψ nP b cds k := by
      unfold mutualRecDataAV
      rw [hh.hb, hh.hLs, hh.hn]
      have hlenX : (rebit b pps ++ motivesDataGo (fun t => Ls.getD t default)
          (fun t => nIdxs.getD t 0) (fun t => ipss.getD t []) ψ nP elimL b k 0
          ++ fixMinorsDataM mems tgts m ψ nP b cds k).length = nP + k + n := by
        rw [List.length_append, List.length_append, rebit_length, hh.hlenP,
          motivesDataGo_length, fixMinorsDataM_length, hh.hn]
      rw [List.append_assoc, List.take_append_of_le_length (by omega),
        List.take_of_length_le (by omega)]
    rw [hpre, List.map_append, List.map_append, rebit_map_dom] at hspB
    obtain ⟨u, v, heq, hsp₂, hspS⟩ := spineFit_append_inv hspB
    have hlenU : u.length = nP + k := by
      rw [hsp₂.length_eq, List.length_append, List.length_map, List.length_map, hh.hlenP,
        motivesDataGo_length]
    obtain ⟨rfl, rfl⟩ : as₁ ++ Ms = u ∧ ms = v :=
      List.append_inj heq (by rw [List.length_append, hlen₁, hlenMs, hlenU])
    obtain ⟨ps', Ms', heq₂, hspP, hspM⟩ := spineFit_append_inv hsp₂
    have hlenPs' : ps'.length = nP := by rw [hspP.length_eq, List.length_map, hh.hlenP]
    obtain ⟨rfl, rfl⟩ : as₁ = ps' ∧ Ms = Ms' := List.append_inj heq₂ (by rw [hlen₁, hlenPs'])
    have hlenms : ms.length = n := by
      rw [hspS.length_eq, List.length_map, fixMinorsDataM_length, hh.hn]
    have hlenbs : bs.length = ((tlss.getD J []).getD i []).length := by
      rw [hbs.length_eq, List.length_map]
    have hstep := (mutualIhSpine_of (hall mm hmm) hcdJ hlenMs hlenms hspP hspM hspS hspD
      i hi bs hbs).2.2.2
    rw [show Semantics.frameIdx ((tlss.getD J []).getD i []).length
        (consList bs (consList (as₂.take i) (consList as₁ ρ'))) = bs from by
      rw [← hlenbs]; exact frameIdx_consList' bs _] at hstep
    exact hstep
  · -- `hzeroC`: the `Prop` conclusion is a truth value
    intro h0 ρp hsatP Ms hspM acc
    have hF := hh.hframes ρp hsatP
    have hmot := hmotSp ρp hsatP Ms hspM (mems J) (hh.hmems J hJn)
    rw [memberMotSp_eq hF.tag (by rw [hh.hk]; exact hh.hmems J hJn)] at hmot
    show SetTheory.app ((idxValsAt ρp cd.2.2.2.1 acc).foldl SetTheory.app
      (Ms.getD (mems J) pt)) (ctorValI wB J acc) ∈ˢ (univZero : V)
    exact piTele_app_univZero h0 hmot
      (by rw [idxValsAt, List.length_map, hEsLenJ, hIdsLen _ (hh.hmems J hJn)]) _
  · -- `hzeroD`: a `Prop` ih domain is a truth value
    intro h0 ρp hsatP Ms hspM as₂ A hA
    have hF := hh.hframes ρp hsatP
    have har : (FssR.getD J []).length = cd.2.1 := by
      rw [List.getD_eq_getElem?_getD, hFsj, Option.getD_some, List.length_map, List.length_drop,
        hlenDs]
      omega
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hA
    have hi₂ : i ∈ recIdx (rss.getD J []) (FssR.getD J []).length := hi
    rw [har] at hi₂
    have hmotT := hmotSp ρp hsatP Ms hspM (tgts J i) (hh.htgts J i)
    rw [memberMotSp_eq hF.tag (by rw [hh.hk]; exact hh.htgts J i)] at hmotT
    rw [h0]
    refine piTele_zero_mem_univZero fun as hfit => ?_
    rw [List.nil_append]
    exact piTele_app_univZero h0 hmotT
      (by rw [List.length_map, hEisLenJ i hi₂, hIdsLen _ (hh.htgts J i)]) _

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

set_option maxHeartbeats 25600000 in
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
  -- the chain lists, positionally
  have hFssG : ∀ (ψ : Name → Nat) (J : Nat), J < ctorsA.length →
      (FssRf ψ)[J]? = some (((dsF J ψ).drop p.toBlock.nP).map (·.2.2)) := by
    intro ψ J hJ
    show ((List.range ctorsA.length).map _)[J]? = _
    rw [List.getElem?_map, List.getElem?_range hJ]
    rfl
  have hEssG : ∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA → ∀ ψ : Name → Nat,
      (Essf ψ)[J]? = some [tagTupleAV (Wf ψ) (memF J) cA.2 (Idssf ψ) (esF J ψ)] := by
    intro J cA hJ ψ
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
    exact congrArg some hgd
  have hEssD : ∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA → ∀ ψ : Name → Nat,
      (Essf ψ).getD J [] = [tagTupleAV (Wf ψ) (memF J) cA.2 (Idssf ψ) (esF J ψ)] := by
    intro J cA hJ ψ
    rw [List.getD_eq_getElem?_getD, hEssG J cA hJ ψ]
    rfl
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
      hEssG
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
  -- the generators' constructor records, positionally
  have hget4C : ∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA →
      ctors4[J]? = some (MutualCtor4.mk cA.1.name cA.2 cA.1.type
        (p.toBlock.ctors.getD J default).member
        (ConLeche.mutualRecFieldsOf (kinds.getD J []))) := by
    intro J cA hJ
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
    have hkJ : (kinds.getD J [] : List (RecFieldKind × Nat))
        = kinds[J]'(show J < kinds.length by omega) := by
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show J < kinds.length by omega)]
      rfl
    rw [hkJ]
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
    · exact hget4C
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
  -- the constructors' data, decoded positionally
  have hdecG : ∀ (ψ : Name → Nat) (J : Nat) (cd : CtorDatumR),
      (fixCtorDataList dsF esF (fun J => kindsOf (ksF J)) eissF tssF ψ ctorsA 0)[J]? = some cd →
      ∃ cA, ctorsA[J]? = some cA ∧ J < ctorsA.length ∧
        cd = (cA.1.name, cA.2, dsF J ψ, esF J ψ, ConLeche.recIdxOf (kindsOf (ksF J)),
          eissF J ψ, tssF J ψ) := by
    intro ψ J cd hJd
    rw [fixCtorDataList_getElem?] at hJd
    obtain ⟨cA, hcA, hEq⟩ := Option.map_eq_some_iff.mp hJd
    refine ⟨cA, hcA, (List.getElem?_eq_some_iff.mp hcA).1, ?_⟩
    rw [← hEq]
    simp only [Nat.zero_add]
  -- the REAL field chains are closed at the parameters
  have hFssBelowG : ∀ (ψ : Name → Nat), ∀ Fs ∈ FssRf ψ, FieldsBelow p.toBlock.nP Fs := by
    intro ψ Fs hFs
    obtain ⟨J, hJ, rfl⟩ := List.mem_map.mp (show Fs ∈ (List.range ctorsA.length).map
      (fun J => ((dsF J ψ).drop p.toBlock.nP).map (·.2.2)) from hFs)
    have hh := (DomsBelow.drop p.toBlock.nP
      ((hCD₁ J _ (hcAGet J (List.mem_range.mp hJ))).below ψ)).fields
    rwa [Nat.zero_add] at hh
  -- each constructor datum's closedness facts
  have hRawCtor : ∀ (ψ : Name → Nat) (J : Nat) (cd : CtorDatumR),
      (fixCtorDataList dsF esF (fun J => kindsOf (ksF J)) eissF tssF ψ ctorsA 0)[J]? = some cd →
      RawCtorBelow p.toBlock.nP mp₂.base2 ψ cd := by
    intro ψ J cd hJd
    obtain ⟨cA, hcA, hJl, rfl⟩ := hdecG ψ J cd hJd
    exact
      { leaf := mp₂.base2.cval_closedL cA.1.name ψ
        doms := (hCD₁ J cA hcA).below ψ
        len := (hCD₁ J cA hcA).len ψ
        esBelow := (hCD₁ J cA hcA).belowE ψ
        recIdxBnd := fun i hi => by
          have h := mem_recIdxOf.mp hi
          rw [kindsOf_length, (hksJ J cA hcA).1] at h
          exact h.1
        tssBelow := (hCD₁ J cA hcA).tssBelow ψ
        eissBelow := (hCD₁ J cA hcA).eissBelow ψ }
  -- **the block's data at one parameter frame** (`MutualFrameOkM`)
  have hFrameOkG : ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V ((((ppsF 0 ψ).take p.toBlock.nP).map (·.2.2)).reverse) ρp →
      MutualFrameOkM V mp₂.base2 (Wf ψ) (f₀.s.eval ψ) p.toBlock.nP (Idssf ψ) rssf (tlssf ψ)
        (mutEiss0 ctorsA.length eissF ψ) (Eissf ψ) (FssRf ψ) (Fss0f ψ) (Essf ψ) memF
        (fun J => tgtAt (ksF J))
        (fixCtorDataList dsF esF (fun J => kindsOf (ksF J)) eissF tssF ψ ctorsA 0) ρp := by
    intro ψ
    have hdec := hdecG ψ
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
      -- (`fixFamI_app_eq_sum` at the 1-tuple spine, then
      -- `restricted_member_intro` at the constructor's restricted chain)
      intro J cd hJd fs hfs
      obtain ⟨cA, hcA, hJl, rfl⟩ := hdec J cd hJd
      have hfrJ := (hframesJ J hJl).2 ψ ρp (hρJ J hJl)
      obtain ⟨hEok, hfit⟩ := hfrJ.2.2.2 fs hfs
      have hIdsM := hIdssGet ψ (memF J) (hmotLt J hJl)
      refine ⟨fun E hE => (hEok E hE).1, ?_, ?_⟩
      · intro Ids hIds
        obtain rfl : Ids = ((ppsF (memF J) ψ).drop p.toBlock.nP).map (·.2.2) :=
          Option.some.inj (hIds.symm.trans hIdsM)
        exact hfit
      · have hlenbs : fs.length = cA.2 := by
          rw [hfs.length_eq, List.length_map, List.length_drop, (hCD₁ J cA hcA).len ψ,
            Nat.add_sub_cancel_left]
        have hfrs : shiftE cA.2 0 (consList fs ρp) = ρp := by
          rw [← hlenbs]; exact shiftE_consList _ _
        obtain ⟨hval, -⟩ := tagTupleAV_facts hTag hIdsM hfrs (fun E hE => (hEok E hE).1) hfit
        have hsp1 : SpineFit ρp (auxIds (Wf ψ) (Idssf ψ))
            [inj (memF J) (mkTower (idxValsAt ρp (esF J ψ) fs ++ [pt]))] := by
          refine ⟨?_, trivial⟩
          rw [(tagTyAV_facts hTag).1]
          exact tagTuple_mem hTag hIdsM hfit
        have hsum := fixFamI_app_eq_sum hX hRealρ hsp1
        rw [show (auxIds (Wf ψ) (Idssf ψ)).length = 1 from rfl] at hsum
        have hchain : (rChains 1 1 (FssRf ψ) (Essf ψ))[J]?
            = some (rChain 1 1 (((dsF J ψ).drop p.toBlock.nP).map (·.2.2))
                [tagTupleAV (Wf ψ) (memF J) cA.2 (Idssf ψ) (esF J ψ)]) := by
          rw [rChains_getElem?, hFssG ψ J hJl, hEssG J cA hcA ψ]
        have hlenI : ([inj (memF J) (mkTower (idxValsAt ρp (esF J ψ) fs ++ [pt]))] : List V).length
            = 1 := rfl
        have hshift : shiftE 1 0
            (consList [inj (memF J) (mkTower (idxValsAt ρp (esF J ψ) fs ++ [pt]))] ρp) = ρp := by
          rw [← hlenI]; exact shiftE_consList _ _
        have hmemF : (if f₀.s.eval ψ = 0 then (pt : V) else mkTower (fs ++ [pt]))
            ∈ˢ sumFibre (f₀.s.eval ψ)
                (consList [inj (memF J) (mkTower (idxValsAt ρp (esF J ψ) fs ++ [pt]))] ρp)
                (rChains 1 1 (FssRf ψ) (Essf ψ)) J := by
          rw [sumFibre_of_getElem? hchain]
          refine restricted_member_intro ?_ ?_
          · rw [spineFit_liftFields, hshift]
            exact hfs
          · rw [EqAll_idxEqsAt (by simp) hfs.length_eq, hshift, frameIdx_consList hlenI]
            show idxValsAt ρp [tagTupleAV (Wf ψ) (memF J) cA.2 (Idssf ψ) (esF J ψ)] fs = _
            rw [idxValsAt, List.map_singleton, hval]
            rfl
        show ctorValI (f₀.s.eval ψ) J fs ∈ˢ _
        unfold auxFib auxTup auxFamI
        rw [hsum]
        unfold ctorValI
        rcases Nat.eq_zero_or_pos (f₀.s.eval ψ) with hw | hw
        · rw [hw] at hmemF ⊢
          rw [if_pos rfl] at hmemF ⊢
          exact pt_mem_sumSet_zero hmemF
        · have hw' : f₀.s.eval ψ ≠ 0 := Nat.pos_iff_ne_zero.mp hw
          rw [if_neg hw'] at hmemF ⊢
          exact inj_mem hw' hmemF
    · -- `slot`: the same at a recursive slot's telescope spine and
      -- its TARGET member's tag.  The RAW index facts come off the
      -- real entry (`recEntry`/`reflEntry` + `leafSpineFit`), the
      -- fibre membership off the real chain (`chainRealI_at`,
      -- `slotSet_fold_mem`).
      intro J cd hJd i hi fs hfs as hbs
      obtain ⟨cA, hcA, hJl, rfl⟩ := hdec J cd hJd
      have hlenDs := (hCD₁ J cA hcA).len ψ
      have hksLen : (kindsOf (ksF J)).length = cA.2 := by
        rw [kindsOf_length]; exact (hksJ J cA hcA).1
      have hmemI := mem_recIdx.mp hi
      have hilt : i < cA.2 := hmemI.1
      have hrb : (rsOf (kindsOf (ksF J))).getD i false = true := by
        rw [← mutRss_getD (n := ctorsA.length) (ksF := ksF) hJl]
        exact hmemI.2
      have hkind : kindAt (ksF J) i = .recursive ∨ kindAt (ksF J) i = .reflexive := by
        have h := (rsOf_getD_iff (by rw [hksLen]; exact hilt)).mp hrb
        rwa [kindsOf_getD (by rw [(hksJ J cA hcA).1]; exact hilt)] at h
      have htgt : tgtAt (ksF J) i < fms.length := (hksJ J cA hcA).2.2 i
      have htG := hfmGet _ htgt
      have hIdsT := hIdssGet ψ (tgtAt (ksF J) i) htgt
      have hlenF : (((dsF J ψ).drop p.toBlock.nP).map (·.2.2)).length = cA.2 := by
        rw [List.length_map, List.length_drop, hlenDs, Nat.add_sub_cancel_left]
      have hlenfs : fs.length = cA.2 := by rw [hfs.length_eq, hlenF]
      have hlenTake : (fs.take i).length = i := by rw [List.length_take, hlenfs]; omega
      have htlsJ : ((tlssf ψ).getD J []).getD i [] = (tssF J ψ).getD i [] := by
        show ((mutTlss ctorsA.length tssF₀ ψ).getD J []).getD i [] = _
        rw [mutTlss_getD hJl, (hident J cA hcA).2.2.2.2.2.2.1 ψ]
      have hbs' : SpineFit (consList (fs.take i) ρp)
          (((tssF J ψ).getD i []).map (·.2.2)) as := by
        rw [← htlsJ]; exact hbs
      have hlenAs : as.length = ((tssF J ψ).getD i []).length := by
        rw [hbs'.length_eq, List.length_map]
      have hfrJ := (hframesJ J hJl).2 ψ ρp (hρJ J hJl)
      have hokEntry : WellDenoted V (consList (fs.take i) ρp)
          ((((dsF J ψ).drop p.toBlock.nP).map (·.2.2)).getD i default) :=
        fieldsOkB_getD hfrJ.1 (by rw [hlenF]; exact hilt)
          (spineFit_take_prefix hfs (by rw [hlenF]; omega))
      have hvEntry : AnnotValid V (consList (fs.take i) ρp)
          ((((dsF J ψ).drop p.toBlock.nP).map (·.2.2)).getD i default) :=
        fieldsValid_getD hfrJ.2.1 (by rw [hlenF]; exact hilt)
          (spineFit_take_prefix hfs (by rw [hlenF]; omega))
      rw [drop_map_getD hlenDs hilt] at hokEntry hvEntry
      -- the target member's leaf
      have hlenT : (ppsF (tgtAt (ksF J) i) ψ).length
          = p.toBlock.nP
            + (((ppsF (tgtAt (ksF J) i) ψ).drop p.toBlock.nP).map (·.2.2)).length := by
        rw [List.length_map, List.length_drop, (hFD₂ _ _ htG).len ψ]; omega
      have hLtower : ∃ B, mp₁.base2.acval
          (mutualNameOf p.toBlock.members3 (tgtAt (ksF J) i)) ψ
          = mkLamsC (f₀.s.eval ψ + 1) (ppsF (tgtAt (ksF J) i) ψ) B := by
        rw [(hmemT _ _ htG).1]
        obtain ⟨B, hB⟩ := hleafT₁ _ _ htG ψ
        exact ⟨B, by rw [hB, hsEq _ _ htG ψ]⟩
      have hclT : Term.bvarsBelow 0
          (mp₁.base2.acval (mutualNameOf p.toBlock.members3 (tgtAt (ksF J) i)) ψ).erase :=
        mp₁.base2.cval_closedL _ ψ
      have hnIdxT : (((ppsF (tgtAt (ksF J) i) ψ).drop p.toBlock.nP).map (·.2.2)).length
          = mutualNIdxOf p.toBlock.members3 (tgtAt (ksF J) i) := by
        rw [List.length_map, List.length_drop, (hFD₂ _ _ htG).len ψ, (hmemT _ _ htG).2]
        omega
      -- **the RAW index facts** at the slot's telescope spine
      have hraw : (∀ E ∈ (eissF J ψ).getD i [],
            WellDenotedV V (consList as (consList (fs.take i) ρp)) E) ∧
          SpineFit ρp (((ppsF (tgtAt (ksF J) i) ψ).drop p.toBlock.nP).map (·.2.2))
            (((eissF J ψ).getD i []).map
              (interp V (consList as (consList (fs.take i) ρp)))) := by
        have hEl : ((eissF J ψ).getD i []).length
            = (((ppsF (tgtAt (ksF J) i) ψ).drop p.toBlock.nP).map (·.2.2)).length := by
          rw [hnIdxT]
          rcases hkind with hk | hk
          · exact (hCD₁ J cA hcA).eisLen ψ i hk hilt
          · exact (hCD₁ J cA hcA).eisLenRefl ψ i hk hilt
        rcases hkind with hk | hk
        · -- a finitary recursive field: the telescope is empty
          have hnone : (tssF J ψ).getD i [] = []
            := (hCD₁ J cA hcA).tssNone ψ i (by rw [hk]; exact fun h => nomatch h)
          obtain rfl : as = [] := by
            rw [hnone] at hlenAs
            exact List.eq_nil_of_length_eq_zero hlenAs
          rw [(hCD₁ J cA hcA).recEntry ψ i hk hilt] at hokEntry hvEntry
          obtain ⟨hEok, hfit⟩ := leafSpineFit hlenT hclT hLtower hlenTake hEl hokEntry
          obtain ⟨-, hargs⟩ := AnnotValid.mkAppN_inv hvEntry
          exact ⟨fun E hE => ⟨hEok E hE, hargs E (List.mem_append_right _ hE)⟩, hfit⟩
        · -- a reflexive field: peel the telescope's Π-tower
          rw [(hCD₁ J cA hcA).reflEntry ψ i hk hilt] at hokEntry hvEntry
          obtain ⟨-, hBody⟩ := WellDenoted_mkPisAV_inv hokEntry
          obtain ⟨-, hBodyV⟩ := AnnotValid_mkPisAV_inv hvEntry
          have hok := hBody as hbs'
          have hokv := hBodyV as hbs'
          rw [← consList_append] at hok hokv
          have hlenSA : (fs.take i ++ as).length = i + ((tssF J ψ).getD i []).length := by
            rw [List.length_append, hlenTake, hlenAs]
          have hok' : WellDenoted V (consList (fs.take i ++ as) ρp)
              (AnnotTerm.mkAppN
                (mp₁.base2.acval (mutualNameOf p.toBlock.members3 (tgtAt (ksF J) i)) ψ)
                (paramBvarsAt p.toBlock.nP
                    (p.toBlock.nP + (i + ((tssF J ψ).getD i []).length))
                  ++ (eissF J ψ).getD i [])) := by
            rw [show p.toBlock.nP + (i + ((tssF J ψ).getD i []).length)
              = p.toBlock.nP + i + ((tssF J ψ).getD i []).length from by omega]
            exact hok
          obtain ⟨hEok, hfit⟩ := leafSpineFit hlenT hclT hLtower hlenSA hEl hok'
          obtain ⟨-, hargs⟩ := AnnotValid.mkAppN_inv hokv
          rw [consList_append] at hEok hfit
          refine ⟨fun E hE => ⟨hEok E hE, ?_⟩, hfit⟩
          have hv := hargs E (List.mem_append_right _ hE)
          rwa [consList_append] at hv
      -- the block's chain lists at `J`
      have hFssJ : (FssRf ψ).getD J [] = ((dsF J ψ).drop p.toBlock.nP).map (·.2.2) :=
        mutFss_getD hJl
      have hnFJ : nFs J = cA.2 := by
        show (ctorsA.getD J default).2 = cA.2
        rw [List.getD_eq_getElem?_getD, hcA]; rfl
      have hlenEis0 : (eissF₀ J ψ).length = nFs J := by
        rw [(hident J cA hcA).2.2.2.2.2.1 ψ, (hCD₁ J cA hcA).eissLen ψ, hnFJ]
      have hEisJ : ((Eissf ψ).getD J []).getD i []
          = [tagTupleAV (Wf ψ) (tgtAt (ksF J) i) (i + ((tssF J ψ).getD i []).length)
              (Idssf ψ) ((eissF J ψ).getD i [])] := by
        rw [mutEiss'_getD hJl (by rw [hnFJ]; exact hilt) hlenEis0,
          (hident J cA hcA).2.2.2.2.2.2.1 ψ, (hident J cA hcA).2.2.2.2.2.1 ψ]
      -- the real chain's slot
      have hJF : J < (FssRf ψ).length := by rw [mutFss_length]; exact hJl
      have hcR := hRealρ.2.2.2.2 J hJF
      have hcw := chainRealI_at ((Fss0f ψ).getD J []) ((FssRf ψ).getD J []) 0 [] fs rfl hcR
        (by rw [hFssJ]; exact hfs) i (by rw [hFssJ, hlenF]; exact hilt)
        (by rw [Nat.zero_add]; exact hmemI.2)
      rw [Nat.zero_add, List.nil_append] at hcw
      obtain ⟨-, heqF⟩ := hcw
      have hfield : fs.getD i pt ∈ˢ slotSet (f₀.s.eval ψ) (Wf ψ)
          (consList (fs.take i) ρp) (((tlssf ψ).getD J []).getD i [])
          (((Eissf ψ).getD J []).getD i [])
          (auxFamI (Wf ψ) (f₀.s.eval ψ) ρp (Idssf ψ) rssf (tlssf ψ) (Eissf ψ)
            (Fss0f ψ) (Essf ψ)) := by
        have h := FixKI.spineFit_getD_mem' (by rw [hFssJ]; exact hfs)
          (show i < ((FssRf ψ).getD J []).length by rw [hFssJ, hlenF]; exact hilt)
        rwa [heqF] at h
      have hfamU : ∀ t : V, SetTheory.app
          (auxFamI (Wf ψ) (f₀.s.eval ψ) ρp (Idssf ψ) rssf (tlssf ψ) (Eissf ψ)
            (Fss0f ψ) (Essf ψ)) t ∈ˢ (univ (f₀.s.eval ψ) : V) := by
        intro t'
        exact famApp_mem_univ (fixFamI_mem _ _ _ _ _ _ _ _ _) t'
      have hfold := slotSet_fold_mem hfamU hfield (by rw [htlsJ]; exact hbs')
      rw [hEisJ] at hfold
      have hfrT : shiftE (i + ((tssF J ψ).getD i []).length) 0
          (consList as (consList (fs.take i) ρp)) = ρp := by
        rw [← consList_append, show i + ((tssF J ψ).getD i []).length = (fs.take i ++ as).length
            from by rw [List.length_append, hlenTake, hlenAs]]
        exact shiftE_consList _ _
      obtain ⟨hvalT, -⟩ := tagTupleAV_facts hTag hIdsT hfrT (fun E hE => (hraw.1 E hE).1) hraw.2
      rw [List.map_singleton, hvalT] at hfold
      refine ⟨?_, ?_, ?_⟩
      · show ∀ E ∈ ((mutEiss0 ctorsA.length eissF ψ).getD J []).getD i [], _
        rw [mutEiss0_getD hJl]
        exact hraw.1
      · intro Ids hIds
        obtain rfl : Ids = ((ppsF (tgtAt (ksF J) i) ψ).drop p.toBlock.nP).map (·.2.2) :=
          Option.some.inj (hIds.symm.trans hIdsT)
        show SpineFit ρp _ ((((mutEiss0 ctorsA.length eissF ψ).getD J []).getD i []).map _)
        rw [mutEiss0_getD hJl]
        exact hraw.2
      · show as.foldl SetTheory.app (fs.getD i pt) ∈ˢ _
        rw [show ((mutEiss0 ctorsA.length eissF ψ).getD J []).getD i []
            = (eissF J ψ).getD i [] from by rw [mutEiss0_getD hJl]]
        unfold auxFib auxTup
        exact hfold
  -- the slots' telescopes are closed at their own depth
  have hTbelowG : ∀ (ψ : Name → Nat) (j i : Nat),
      DomsBelow (p.toBlock.nP + i) (((tlssf ψ).getD j []).getD i []) := by
    intro ψ j i
    by_cases hj : j < ctorsA.length
    · show DomsBelow _ (((mutTlss ctorsA.length tssF₀ ψ).getD j []).getD i [])
      rw [mutTlss_getD hj]
      exact (hCD₀ j _ (hcAGet j hj)).tssBelow ψ i
    · show DomsBelow _ (((mutTlss ctorsA.length tssF₀ ψ).getD j []).getD i [])
      rw [show (mutTlss ctorsA.length tssF₀ ψ).getD j [] = [] from by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [mutTlss]; omega)]
        rfl]
      exact trivial
  -- every tagged slot IS a tagged tuple over raw, scoped expressions
  have hslotTagG : ∀ ψ : Name → Nat,
      AuxSlotTagged (Wf ψ) p.toBlock.nP (Idssf ψ) (tlssf ψ) (Eissf ψ) := by
    intro ψ j i E hE
    have hE' : E ∈ ((mutEiss' (Wf ψ) (Idssf ψ) ksF nFs tssF₀ eissF₀ ψ).getD j []).getD i [] := hE
    by_cases hj : j < ctorsA.length
    · have hEL : (eissF₀ j ψ).length = nFs j := (hCD₀ j _ (hcAGet j hj)).eissLen ψ
      by_cases hi : i < nFs j
      · rw [mutEiss'_getD hj hi hEL, List.mem_singleton] at hE'
        refine ⟨tgtAt (ksF j) i, (eissF₀ j ψ).getD i [], fun E' hE'' => ?_, ?_⟩
        · have hh := (hCD₀ j _ (hcAGet j hj)).eissBelow ψ i E' hE''
          show Term.bvarsBelow
            (p.toBlock.nP + i + (((mutTlss ctorsA.length tssF₀ ψ).getD j []).getD i []).length)
            E'.erase
          rw [mutTlss_getD hj]
          exact hh
        · show E = tagTupleAV (Wf ψ) (tgtAt (ksF j) i)
            (i + (((mutTlss ctorsA.length tssF₀ ψ).getD j []).getD i []).length) (Idssf ψ) _
          rw [mutTlss_getD hj]
          exact hE'
      · rw [mutEiss'_getDJ hj hEL, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hi)] at hE'
        exact nomatch hE'
    · rw [show (mutEiss' (Wf ψ) (Idssf ψ) ksF nFs tssF₀ eissF₀ ψ).getD j [] = [] from by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
          show (mutEiss' (Wf ψ) (Idssf ψ) ksF nFs tssF₀ eissF₀ ψ).length ≤ j
          unfold mutEiss' mutualEiss
          simp only [List.length_map, List.length_range, mutEiss0_length]
          omega)]
        rfl] at hE'
      exact nomatch hE'
  -- **the block's regime**: a `Prop` block eliminates into `Prop` only
  have hw0G : ∀ ψ : Name → Nat, f₀.s.eval ψ = 0 → p.toBlock.elimLevel.eval ψ = 0 := by
    intro ψ h0
    show (ConLeche.structElimLevel p.toBlock.elim p.toBlock.large).eval ψ = 0
    cases hL : p.toBlock.large with
    | false =>
      rw [ConLeche.structElimLevel, if_neg Bool.false_ne_true]
      rfl
    | true =>
      exfalso
      have hnz : f₀.s.isNeverZero = true := by rw [← hlarge, hL]
      rw [ConLeche.Level.isNeverZero_eq_isNever] at hnz
      exact pwBit_ne_zero_of_isNever hnz ψ ((pwBit_zeronessOf ψ f₀.s).mpr h0)
  -- **the auxiliary former's typing** (`AuxFrameOk.former`): its leaf
  -- is the fixpoint route's at the parameter-and-TAG telescope
  have hAuxParamsG : ∀ (ψ : Name → Nat) (σ : Nat → V),
      ParamsOkXI (Wf ψ) (f₀.s.eval ψ) σ (auxIds (Wf ψ) (Idssf ψ)) rssf (tlssf ψ) (Eissf ψ)
        (Fss0f ψ) (Essf ψ)
        ((ppsF 0 ψ).take p.toBlock.nP ++ tagIps (Wf ψ) (Idssf ψ)) ∧
      UnderTowerValid σ
        (.app ((fixBodyAVI (Wf ψ) (f₀.s.eval ψ) (auxIds (Wf ψ) (Idssf ψ))
            (auxIds (Wf ψ) (Idssf ψ)).length rssf (tlssf ψ) (Eissf ψ) (Fss0f ψ) (Essf ψ)).liftN
              (auxIds (Wf ψ) (Idssf ψ)).length 0)
          (mkTowerGo (Wf ψ) (auxIds (Wf ψ) (Idssf ψ))))
        ((ppsF 0 ψ).take p.toBlock.nP ++ tagIps (Wf ψ) (Idssf ψ)) := by
    intro ψ σ
    have hlen0 := (hFD₂ 0 f₀ hf0).len ψ
    have hsplitP : mkPisAV (ppsF 0 ψ) (AnnotTerm.sort (f₀.s.eval ψ))
        = mkPisAV ((ppsF 0 ψ).take p.toBlock.nP)
            (mkPisAV ((ppsF 0 ψ).drop p.toBlock.nP) (AnnotTerm.sort (f₀.s.eval ψ))) := by
      rw [← mkPisAV_append, List.take_append_drop]
    have hokTy := (hFD₂ 0 f₀ hf0).okTy ψ σ
    rw [hsplitP] at hokTy
    obtain ⟨hokP, -⟩ := WellDenoted_mkPisAV_inv hokTy.1
    obtain ⟨hvP, -⟩ := AnnotValid_mkPisAV_inv hokTy.2
    -- at a spine fitting the parameters, the tag binder and the base
    have hstep : ∀ ps : List V,
        SpineFit σ (((ppsF 0 ψ).take p.toBlock.nP).map (·.2.2)) ps →
        Sat V ((((ppsF 0 ψ).take p.toBlock.nP).map (·.2.2)).reverse) (consList ps σ) := by
      intro ps hps
      have h := sat_of_spineFit (Δ₀ := []) (Sat_nil V σ) hps
      rwa [List.append_nil] at h
    constructor
    · refine paramsOkXI_append (fun d hd => ?_) hokP fun ps hps => ?_
      · exact (hFD₂ 0 f₀ hf0).bits ψ d (List.mem_of_mem_take hd)
      · obtain ⟨hTag, hVal⟩ := hIdxAll 0 f₀ hf0 ψ (consList ps σ) (hstep ps hps)
        obtain ⟨hFix, -, hXV⟩ := hChainFull 0 f₀ hf0 ψ (consList ps σ) (hstep ps hps)
        refine ⟨hTag.1, (tagTyAV_facts hTag).2.2, fun a' ha' => ?_⟩
        rw [(tagTyAV_facts hTag).1] at ha'
        refine ⟨?_, ?_, ?_⟩
        · show IdxOk (Wf ψ) (shiftE 1 0 (cons a' (consList ps σ))) (auxIds (Wf ψ) (Idssf ψ))
          rw [show shiftE 1 0 (cons a' (consList ps σ)) = consList ps σ from by
            rw [show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]]
          exact auxIds_idxOk hTag
        · show FixChainsOkI (Wf ψ) (f₀.s.eval ψ) (shiftE 1 0 (cons a' (consList ps σ)))
            (auxIds (Wf ψ) (Idssf ψ)) 1 rssf (tlssf ψ) (Eissf ψ) (Fss0f ψ) (Essf ψ)
          rw [show shiftE 1 0 (cons a' (consList ps σ)) = consList ps σ from by
            rw [show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]]
          exact hFix
        · have hmem : a' ∈ˢ interp V (consList ps σ) (tagTyAV (Wf ψ) (Idssf ψ)) := by
            rw [(tagTyAV_facts hTag).1]; exact ha'
          rw [show shiftE (auxIds (Wf ψ) (Idssf ψ)).length 0 (cons a' (consList ps σ))
              = consList ps σ from by
            rw [show (auxIds (Wf ψ) (Idssf ψ)).length = 0 + 1 from rfl, shiftE_succ_cons,
              shiftE_zero_zero]]
          exact ⟨hmem, trivial⟩
    · refine underTowerValid_append hvP fun ps hps => ?_
      obtain ⟨hTag, hVal⟩ := hIdxAll 0 f₀ hf0 ψ (consList ps σ) (hstep ps hps)
      obtain ⟨-, -, hXV⟩ := hChainFull 0 f₀ hf0 ψ (consList ps σ) (hstep ps hps)
      refine ⟨sumBodyAV_validV (uChains_validV hVal), fun a ha => ?_⟩
      rw [(tagTyAV_facts hTag).1] at ha
      have hsp : SpineFit (consList ps σ) (auxIds (Wf ψ) (Idssf ψ)) [a] := by
        refine ⟨?_, trivial⟩
        rw [(tagTyAV_facts hTag).1]
        exact ha
      have h := fixBody_validV (u := Wf ψ) (w := f₀.s.eval ψ)
        (Ids := auxIds (Wf ψ) (Idssf ψ)) (rss := rssf) (tlss := tlssf ψ) (Eiss := Eissf ψ)
        (Fss := Fss0f ψ) (Ess := Essf ψ) (auxIds_idxOk hTag) (auxIds_fieldsValid hVal) hXV hsp
      exact h
  have hLeafTG : ∀ (ψ : Name → Nat) (ρ₀ : Nat → V),
      LeafTyping (auxFormerAV (Wf ψ) (f₀.s.eval ψ) ((ppsF 0 ψ).take p.toBlock.nP) (Idssf ψ)
          rssf (tlssf ψ) (Eissf ψ) (Fss0f ψ) (Essf ψ)) (f₀.s.eval ψ)
        ((ppsF 0 ψ).take p.toBlock.nP ++ tagIps (Wf ψ) (Idssf ψ)) ρ₀ := by
    intro ψ ρ₀
    have hcl : Term.bvarsBelow 0 (auxFormerAV (Wf ψ) (f₀.s.eval ψ)
        ((ppsF 0 ψ).take p.toBlock.nP) (Idssf ψ) rssf (tlssf ψ) (Eissf ψ) (Fss0f ψ)
        (Essf ψ)).erase :=
      auxFormerAV_below (domsBelow_take ((hFD₂ 0 f₀ hf0).below ψ))
        (by rw [List.length_take, (hFD₂ 0 f₀ hf0).len ψ]; omega)
        (hIdsBelow ψ) (hchainBelow ψ)
    refine ⟨fun σ => ⟨?_, ?_⟩, fun σ => ?_, ?_⟩
    · show WellDenoted V σ (nativeTyAVI (Wf ψ) (f₀.s.eval ψ)
        ((ppsF 0 ψ).take p.toBlock.nP ++ tagIps (Wf ψ) (Idssf ψ)) (auxIds (Wf ψ) (Idssf ψ))
        rssf (tlssf ψ) (Eissf ψ) (Fss0f ψ) (Essf ψ))
      exact nativeTyAVI_wellDenoted (hAuxParamsG ψ σ).1
    · show AnnotValid V σ (mkLamsAV
        (((ppsF 0 ψ).take p.toBlock.nP ++ tagIps (Wf ψ) (Idssf ψ)).map
          fun d => (f₀.s.eval ψ + 1, d.2.2)) _)
      exact mkLamsC_validV (m := f₀.s.eval ψ + 1) (hAuxParamsG ψ σ).2
    · rw [interp_closed V hcl σ ρ₀]
      exact nativeTyAVI_mem (hAuxParamsG ψ ρ₀).1
    · intro d hd
      rcases List.mem_append.mp hd with h | h
      · exact (hFD₂ 0 f₀ hf0).bits ψ d (List.mem_of_mem_take h)
      · have h' : d ∈ [((Wf ψ), (Wf ψ), tagTyAV (Wf ψ) (Idssf ψ))] := h
        rw [List.mem_singleton] at h'
        subst h'
        show Wf ψ ≠ 0
        show 1 + ((List.range fms.length).map fun q => (lvlsF q ψ).foldl max 0).foldl max 0 ≠ 0
        omega
  -- **the constructor leaf's APPLICATION grading** (`minorTag_facts`'
  -- `hctorOk`): its type's reading is a Π-tower whose CODOMAIN bits are
  -- uniform (`CtorDataI.bits` — a Π-type's sort is the `imax` with the
  -- constructor's result sort), so `appChainOk_of_mkPisAV'` applies
  have hCtorOkG : ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V ((((ppsF 0 ψ).take p.toBlock.nP).map (·.2.2)).reverse) ρp →
      ∀ (J : Nat) (cd : CtorDatumR),
        (fixCtorDataList dsF esF (fun J => kindsOf (ksF J)) eissF tssF ψ ctorsA 0)[J]? = some cd →
      ∀ (M : V) (ms : List V) (fs : List V),
        SpineFit ρp ((cd.2.2.1.drop p.toBlock.nP).map (·.2.2)) fs →
        WellDenotedV V (consList fs (consList ms (cons M ρp)))
          (AnnotTerm.mkAppN (mp₂.base2.acval cd.1 ψ)
            (paramBvarsAt p.toBlock.nP (p.toBlock.nP + (1 + ms.length) + cd.2.1)
              ++ fieldBvars cd.2.1)) := by
    intro ψ ρp hρ J cd hJd M ms fs hfs
    obtain ⟨cA, hcA, hJl, rfl⟩ := hdecG ψ J cd hJd
    have hlenDs := (hCD₁ J cA hcA).len ψ
    have hρJ : Sat V (((dsF J ψ).take p.toBlock.nP).map (·.2.2)).reverse ρp :=
      ((hframesJ J hJl).1 ψ ρp).mp
        (hframeAll 0 (memF J) f₀ _ hf0 (hfmGet _ (hmotLt J hJl)) ψ ρp hρ)
    have hlenP' : ((((dsF J ψ).take p.toBlock.nP).map (·.2.2))).length = p.toBlock.nP := by
      rw [List.length_map, List.length_take, hlenDs]; omega
    have hlenF : (((dsF J ψ).drop p.toBlock.nP).map (·.2.2)).length = cA.2 := by
      rw [List.length_map, List.length_drop, hlenDs, Nat.add_sub_cancel_left]
    have hlenfs : fs.length = cA.2 := by rw [hfs.length_eq, hlenF]
    have hsplit : (dsF J ψ).take p.toBlock.nP ++ (dsF J ψ).drop p.toBlock.nP = dsF J ψ :=
      List.take_append_drop _ _
    -- the bits are uniform at the constructor's result sort
    have hbitsD : ∀ d ∈ (dsF J ψ).take p.toBlock.nP ++ (dsF J ψ).drop p.toBlock.nP,
        (f₀.s.eval ψ = 0 ↔ d.2.1 = 0) := by
      intro d hd
      rw [hsplit] at hd
      rw [← hsEq _ _ (hfmGet _ (hmotLt J hJl)) ψ]
      exact (hCD₁ J cA hcA).bits ψ d hd
    -- the constructor's leaf, its premise and its typing at the parameter frame
    have hleafCJ := hleafC₂ J cA hcA ψ
    have hbody : ∀ ρ : Nat → V, Sat V (((dsF J ψ).take p.toBlock.nP).map (·.2.2)).reverse ρ →
        ∀ bs : List V, SpineFit ρ (((dsF J ψ).drop p.toBlock.nP).map (·.2.2)) bs →
          interp V (consList bs ρ)
              (ctorBodyAVI mp₂.base2 (fms.getD (memF J) default).cvTa.name p.toBlock.nP cA.2 ψ
                (esF J ψ))
            = sumSet (f₀.s.eval ψ) (sumFibre (f₀.s.eval ψ)
                (consList (idxValsAt ρ
                  [tagTupleAV (Wf ψ) (memF J) cA.2 (Idssf ψ) (esF J ψ)] bs) ρ)
                (rChains 1 1 (FssRf ψ) (Essf ψ))) := by
      intro ρ hρ' bs hbs
      have h := hfold J cA hcA ψ ρ (((hframesJ J hJl).1 ψ ρ).mpr hρ') bs hbs
      show interp V (consList bs ρ)
        (AnnotTerm.mkAppN (mp₂.base2.acval (fms.getD (memF J) default).cvTa.name ψ)
          (paramBvars p.toBlock.nP cA.2 ++ esF J ψ)) = _
      rw [hleaf₂ J cA hcA ψ]
      exact h
    have hpre := mutualCtorMkPre (V := V) (J := J) (w := f₀.s.eval ψ) hlenDs
      (fun ρ => by
        have h := (hCD₁ J cA hcA).okTy ψ ρ
        show WellDenotedV V ρ (mkPisAV (dsF J ψ)
          (ctorBodyAVI mp₂.base2 (fms.getD (memF J) default).cvTa.name p.toBlock.nP cA.2 ψ
            (esF J ψ)))
        unfold ctorBodyAVI at h ⊢
        rwa [hleafTJ J cA hcA ψ, ← hleaf₂ J cA hcA ψ] at h)
      (hFssG ψ J hJl) (hEssG J cA hcA ψ) rfl
      (fun ρ hρ' => (hFssOkP J cA hcA ψ ρ hρ').1)
      hbody (fun k => ρp (k + p.toBlock.nP))
    have hsp₁ := spineFit_of_sat (Δ₀ := []) (Ds := ((dsF J ψ).take p.toBlock.nP).map (·.2.2))
      (ρ := ρp) (by rw [List.append_nil]; exact hρJ)
    rw [hlenP'] at hsp₁
    have hspFull : SpineFit (fun k => ρp (k + p.toBlock.nP)) ((dsF J ψ).map (·.2.2))
        ((List.range p.toBlock.nP).reverse.map ρp ++ fs) := by
      rw [← hsplit, List.map_append]
      exact SpineFit.append hsp₁ (by rw [consList_range_reverse]; exact hfs)
    have hmemL : interp V (fun k => ρp (k + p.toBlock.nP)) (mp₂.base2.acval cA.1.name ψ)
        ∈ˢ interp V (fun k => ρp (k + p.toBlock.nP))
          (mkPisAV (dsF J ψ)
            (ctorBodyAVI mp₂.base2 (fms.getD (memF J) default).cvTa.name p.toBlock.nP cA.2 ψ
              (esF J ψ))) := by
      have h := sumMkAV_mem (pds := (dsF J ψ).take p.toBlock.nP)
        (fds := (dsF J ψ).drop p.toBlock.nP)
        (bodyC := ctorBodyAVI mp₂.base2 (fms.getD (memF J) default).cvTa.name p.toBlock.nP cA.2 ψ
          (esF J ψ)) hbitsD hpre
      rw [hsplit] at h
      rw [hleafCJ]
      exact h
    -- the application chain at the parameter frame
    have hchain0 : AppChainOk (interp V (fun k => ρp (k + p.toBlock.nP))
        (mp₂.base2.acval cA.1.name ψ)) ((List.range p.toBlock.nP).reverse.map ρp ++ fs) := by
      refine appChainOk_of_mkPisAV' (m := f₀.s.eval ψ) ?_ ?_ hmemL hspFull
      · intro d hd
        exact hbitsD d (by rw [hsplit]; exact hd)
      · intro h0 as' hsp'
        rw [← hsplit, List.map_append] at hsp'
        obtain ⟨ps', fs', rfl, hp', hf'⟩ := spineFit_append_inv hsp'
        have hsatP : Sat V (((dsF J ψ).take p.toBlock.nP).map (·.2.2)).reverse
            (consList ps' (fun k => ρp (k + p.toBlock.nP))) := by
          have h := sat_of_spineFit (Δ₀ := []) (Sat_nil V (fun k => ρp (k + p.toBlock.nP))) hp'
          rwa [List.append_nil] at h
        rw [consList_append, hbody _ hsatP fs' hf', h0]
        exact sumSet_zero_mem_univZero _
    -- the frame below the fields, and the arguments' values
    have hσ : ∀ k, consList fs (consList ms (cons M ρp)) (k + ((1 + ms.length) + cA.2)) = ρp k := by
      intro k
      rw [show k + ((1 + ms.length) + cA.2) = (k + (1 + ms.length)) + fs.length from by omega,
        consList_apply_add,
        show k + (1 + ms.length) = (k + 1) + ms.length from by omega, consList_apply_add]
      rfl
    have hargsv : ((paramBvarsAt p.toBlock.nP (p.toBlock.nP + (1 + ms.length) + cA.2)
          ++ fieldBvars cA.2)).map (interp V (consList fs (consList ms (cons M ρp))))
        = (List.range p.toBlock.nP).reverse.map ρp ++ fs := by
      rw [List.map_append,
        show p.toBlock.nP + (1 + ms.length) + cA.2 = p.toBlock.nP + ((1 + ms.length) + cA.2)
          from by omega,
        map_paramBvarsAt_interp hσ]
      congr 1
      show ((List.range cA.2).map fun k => (AnnotTerm.bvar (cA.2 - 1 - k))).map
        (interp V (consList fs (consList ms (cons M ρp)))) = fs
      exact map_fieldBvars_interp hlenfs _
    have hclC : Term.bvarsBelow 0 (mp₂.base2.acval cA.1.name ψ).erase :=
      mp₂.base2.cval_closedL _ ψ
    have hfv : interp V (consList fs (consList ms (cons M ρp))) (mp₂.base2.acval cA.1.name ψ)
        = interp V (fun k => ρp (k + p.toBlock.nP)) (mp₂.base2.acval cA.1.name ψ) :=
      interp_closed V hclC _ _
    have hargsok : ∀ a ∈ paramBvarsAt p.toBlock.nP (p.toBlock.nP + (1 + ms.length) + cA.2)
        ++ fieldBvars cA.2, WellDenotedV V (consList fs (consList ms (cons M ρp))) a := by
      intro a ha
      rcases List.mem_append.mp ha with h | h
      · obtain ⟨k, -, rfl⟩ := List.mem_map.mp h
        exact ⟨trivial, trivial⟩
      · obtain ⟨k, -, rfl⟩ := List.mem_map.mp h
        exact ⟨trivial, trivial⟩
    refine ⟨(mkAppN_wellDenoted_of_chain (mp₂.base2.acval_wellDenoted _ ψ _)
      (fun a ha => (hargsok a ha).1) ?_).1, mkAppN_validV (mp₂.acval_validV _ ψ _)
      (fun a ha => (hargsok a ha).2)⟩
    rw [hargsv, hfv]
    exact hchain0
  -- **a recursive slot's tagged facts** (`minorTag_facts`' `hslots`)
  have hSlotTagG : ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V ((((ppsF 0 ψ).take p.toBlock.nP).map (·.2.2)).reverse) ρp →
      ∀ (J : Nat) (cd : CtorDatumR),
        (fixCtorDataList dsF esF (fun J => kindsOf (ksF J)) eissF tssF ψ ctorsA 0)[J]? = some cd →
      ∀ fs : List V, SpineFit ρp ((cd.2.2.1.drop p.toBlock.nP).map (·.2.2)) fs →
      ∀ i ∈ recIdx (rssf.getD J []) cd.2.1,
        SlotTagOk (Wf ψ) (f₀.s.eval ψ) i ρp fs (Idssf ψ) rssf (tlssf ψ) (Eissf ψ) (Fss0f ψ)
          (Essf ψ) (((tlssf ψ).getD J []).getD i []) (((Eissf ψ).getD J []).getD i []) := by
    intro ψ ρp hρ J cd hJd fs hfs i hi
    obtain ⟨cA, hcA, hJl, rfl⟩ := hdecG ψ J cd hJd
    obtain ⟨hFix, hRealρ, -⟩ := hChainFull 0 f₀ hf0 ψ ρp hρ
    obtain ⟨hTag, hV⟩ := hIdxAll 0 f₀ hf0 ψ ρp hρ
    have hρJ : Sat V (((dsF J ψ).take p.toBlock.nP).map (·.2.2)).reverse ρp :=
      ((hframesJ J hJl).1 ψ ρp).mp
        (hframeAll 0 (memF J) f₀ _ hf0 (hfmGet _ (hmotLt J hJl)) ψ ρp hρ)
    have hlenDs := (hCD₁ J cA hcA).len ψ
    have hksLen : (kindsOf (ksF J)).length = cA.2 := by
      rw [kindsOf_length]; exact (hksJ J cA hcA).1
    have hmemI := mem_recIdx.mp hi
    have hilt : i < cA.2 := hmemI.1
    have hrb : (rsOf (kindsOf (ksF J))).getD i false = true := by
      rw [← mutRss_getD (n := ctorsA.length) (ksF := ksF) hJl]
      exact hmemI.2
    have hkind : kindAt (ksF J) i = .recursive ∨ kindAt (ksF J) i = .reflexive := by
      have h := (rsOf_getD_iff (by rw [hksLen]; exact hilt)).mp hrb
      rwa [kindsOf_getD (by rw [(hksJ J cA hcA).1]; exact hilt)] at h
    have htgt : tgtAt (ksF J) i < fms.length := (hksJ J cA hcA).2.2 i
    have htG := hfmGet _ htgt
    have hIdsT := hIdssGet ψ (tgtAt (ksF J) i) htgt
    have hlenF : (((dsF J ψ).drop p.toBlock.nP).map (·.2.2)).length = cA.2 := by
      rw [List.length_map, List.length_drop, hlenDs, Nat.add_sub_cancel_left]
    have hlenfs : fs.length = cA.2 := by rw [hfs.length_eq, hlenF]
    have hlenTake : (fs.take i).length = i := by rw [List.length_take, hlenfs]; omega
    have htlsJ : ((tlssf ψ).getD J []).getD i [] = (tssF J ψ).getD i [] := by
      show ((mutTlss ctorsA.length tssF₀ ψ).getD J []).getD i [] = _
      rw [mutTlss_getD hJl, (hident J cA hcA).2.2.2.2.2.2.1 ψ]
    have hfrJ := (hframesJ J hJl).2 ψ ρp hρJ
    have hokEntry : WellDenoted V (consList (fs.take i) ρp)
        ((((dsF J ψ).drop p.toBlock.nP).map (·.2.2)).getD i default) :=
      fieldsOkB_getD hfrJ.1 (by rw [hlenF]; exact hilt)
        (spineFit_take_prefix hfs (by rw [hlenF]; omega))
    have hvEntry : AnnotValid V (consList (fs.take i) ρp)
        ((((dsF J ψ).drop p.toBlock.nP).map (·.2.2)).getD i default) :=
      fieldsValid_getD hfrJ.2.1 (by rw [hlenF]; exact hilt)
        (spineFit_take_prefix hfs (by rw [hlenF]; omega))
    rw [drop_map_getD hlenDs hilt] at hokEntry hvEntry
    -- the target member's leaf
    have hlenT : (ppsF (tgtAt (ksF J) i) ψ).length
        = p.toBlock.nP
          + (((ppsF (tgtAt (ksF J) i) ψ).drop p.toBlock.nP).map (·.2.2)).length := by
      rw [List.length_map, List.length_drop, (hFD₂ _ _ htG).len ψ]; omega
    have hLtower : ∃ B, mp₁.base2.acval
        (mutualNameOf p.toBlock.members3 (tgtAt (ksF J) i)) ψ
        = mkLamsC (f₀.s.eval ψ + 1) (ppsF (tgtAt (ksF J) i) ψ) B := by
      rw [(hmemT _ _ htG).1]
      obtain ⟨B, hB⟩ := hleafT₁ _ _ htG ψ
      exact ⟨B, by rw [hB, hsEq _ _ htG ψ]⟩
    have hclT : Term.bvarsBelow 0
        (mp₁.base2.acval (mutualNameOf p.toBlock.members3 (tgtAt (ksF J) i)) ψ).erase :=
      mp₁.base2.cval_closedL _ ψ
    have hnIdxT : (((ppsF (tgtAt (ksF J) i) ψ).drop p.toBlock.nP).map (·.2.2)).length
        = mutualNIdxOf p.toBlock.members3 (tgtAt (ksF J) i) := by
      rw [List.length_map, List.length_drop, (hFD₂ _ _ htG).len ψ, (hmemT _ _ htG).2]
      omega
    have hEl : ((eissF J ψ).getD i []).length
        = (((ppsF (tgtAt (ksF J) i) ψ).drop p.toBlock.nP).map (·.2.2)).length := by
      rw [hnIdxT]
      rcases hkind with hk | hk
      · exact (hCD₁ J cA hcA).eisLen ψ i hk hilt
      · exact (hCD₁ J cA hcA).eisLenRefl ψ i hk hilt
    -- the telescope's validity, and the RAW index facts at every spine
    have hTV : FieldsValid (consList (fs.take i) ρp) (((tssF J ψ).getD i []).map (·.2.2)) ∧
        ∀ as : List V, SpineFit (consList (fs.take i) ρp)
          (((tssF J ψ).getD i []).map (·.2.2)) as →
          (∀ E ∈ (eissF J ψ).getD i [],
            WellDenotedV V (consList as (consList (fs.take i) ρp)) E) ∧
          SpineFit ρp (((ppsF (tgtAt (ksF J) i) ψ).drop p.toBlock.nP).map (·.2.2))
            (((eissF J ψ).getD i []).map
              (interp V (consList as (consList (fs.take i) ρp)))) := by
      rcases hkind with hk | hk
      · -- a finitary recursive field: the telescope is empty
        have hnone : (tssF J ψ).getD i [] = []
          := (hCD₁ J cA hcA).tssNone ψ i (by rw [hk]; exact fun h => nomatch h)
        rw [(hCD₁ J cA hcA).recEntry ψ i hk hilt] at hokEntry hvEntry
        obtain ⟨hEok, hfit⟩ := leafSpineFit hlenT hclT hLtower hlenTake hEl hokEntry
        obtain ⟨-, hargs⟩ := AnnotValid.mkAppN_inv hvEntry
        refine ⟨by rw [hnone]; exact trivial, fun as hbs => ?_⟩
        obtain rfl : as = [] := by
          have := hbs.length_eq
          rw [hnone] at this
          exact List.eq_nil_of_length_eq_zero (by simpa using this)
        exact ⟨fun E hE => ⟨hEok E hE, hargs E (List.mem_append_right _ hE)⟩, hfit⟩
      · -- a reflexive field: peel the telescope's Π-tower
        rw [(hCD₁ J cA hcA).reflEntry ψ i hk hilt] at hokEntry hvEntry
        obtain ⟨-, hBody⟩ := WellDenoted_mkPisAV_inv hokEntry
        obtain ⟨hTVal, hBodyV⟩ := AnnotValid_mkPisAV_inv hvEntry
        refine ⟨hTVal, fun as hbs => ?_⟩
        have hlenAs : as.length = ((tssF J ψ).getD i []).length := by
          rw [hbs.length_eq, List.length_map]
        have hok := hBody as hbs
        have hokv := hBodyV as hbs
        rw [← consList_append] at hok hokv
        have hlenSA : (fs.take i ++ as).length = i + ((tssF J ψ).getD i []).length := by
          rw [List.length_append, hlenTake, hlenAs]
        have hshift : p.toBlock.nP + (i + ((tssF J ψ).getD i []).length)
            = p.toBlock.nP + i + ((tssF J ψ).getD i []).length := by omega
        have hok' : WellDenoted V (consList (fs.take i ++ as) ρp)
            (AnnotTerm.mkAppN
              (mp₁.base2.acval (mutualNameOf p.toBlock.members3 (tgtAt (ksF J) i)) ψ)
              (paramBvarsAt p.toBlock.nP
                  (p.toBlock.nP + (i + ((tssF J ψ).getD i []).length))
                ++ (eissF J ψ).getD i [])) := by
          rw [hshift]; exact hok
        obtain ⟨hEok, hfit⟩ := leafSpineFit hlenT hclT hLtower hlenSA hEl hok'
        obtain ⟨-, hargs⟩ := AnnotValid.mkAppN_inv hokv
        rw [consList_append] at hEok hfit
        refine ⟨fun E hE => ⟨hEok E hE, ?_⟩, hfit⟩
        have := hargs E (List.mem_append_right _ hE)
        rwa [consList_append] at this
    -- the block's chain lists at `J`
    have hFssJ : (FssRf ψ).getD J [] = ((dsF J ψ).drop p.toBlock.nP).map (·.2.2) :=
      mutFss_getD hJl
    have hnFJ : nFs J = cA.2 := by
      show (ctorsA.getD J default).2 = cA.2
      rw [List.getD_eq_getElem?_getD, hcA]; rfl
    have hlenEis0 : (eissF₀ J ψ).length = nFs J := by
      rw [(hident J cA hcA).2.2.2.2.2.1 ψ, (hCD₁ J cA hcA).eissLen ψ, hnFJ]
    have hEisJ : ((Eissf ψ).getD J []).getD i []
        = [tagTupleAV (Wf ψ) (tgtAt (ksF J) i) (i + ((tssF J ψ).getD i []).length)
            (Idssf ψ) ((eissF J ψ).getD i [])] := by
      rw [mutEiss'_getD hJl (by rw [hnFJ]; exact hilt) hlenEis0,
        (hident J cA hcA).2.2.2.2.2.2.1 ψ, (hident J cA hcA).2.2.2.2.2.1 ψ]
    -- the real chain's slot
    have hJF : J < (FssRf ψ).length := by rw [mutFss_length]; exact hJl
    have hcR := hRealρ.2.2.2.2 J hJF
    have hcw := chainRealI_at ((Fss0f ψ).getD J []) ((FssRf ψ).getD J []) 0 [] fs rfl hcR
      (by rw [hFssJ]; exact hfs) i (by rw [hFssJ, hlenF]; exact hilt)
      (by rw [Nat.zero_add]; exact hmemI.2)
    rw [Nat.zero_add, List.nil_append] at hcw
    obtain ⟨hSlotFit, heqF⟩ := hcw
    have hfield : fs.getD i pt ∈ˢ slotSet (f₀.s.eval ψ) (Wf ψ)
        (consList (fs.take i) ρp) (((tlssf ψ).getD J []).getD i [])
        (((Eissf ψ).getD J []).getD i [])
        (auxFamI (Wf ψ) (f₀.s.eval ψ) ρp (Idssf ψ) rssf (tlssf ψ) (Eissf ψ)
          (Fss0f ψ) (Essf ψ)) := by
      have h := FixKI.spineFit_getD_mem' (by rw [hFssJ]; exact hfs)
        (show i < ((FssRf ψ).getD J []).length by rw [hFssJ, hlenF]; exact hilt)
      rwa [heqF] at h
    have hfamU : ∀ t : V, SetTheory.app
        (auxFamI (Wf ψ) (f₀.s.eval ψ) ρp (Idssf ψ) rssf (tlssf ψ) (Eissf ψ)
          (Fss0f ψ) (Essf ψ)) t ∈ˢ (univ (f₀.s.eval ψ) : V) := by
      intro t'
      exact famApp_mem_univ (fixFamI_mem _ _ _ _ _ _ _ _ _) t'
    refine ⟨hSlotFit.1, by rw [htlsJ]; exact hTV.1,
      tgtAt (ksF J) i, (eissF J ψ).getD i [], by rw [hEisJ, htlsJ], fun bs hbs => ?_⟩
    have hbs' : SpineFit (consList (fs.take i) ρp)
        (((tssF J ψ).getD i []).map (·.2.2)) bs := by rw [← htlsJ]; exact hbs
    have hlenBs : bs.length = ((tssF J ψ).getD i []).length := by
      rw [hbs'.length_eq, List.length_map]
    obtain ⟨hEok, hfit⟩ := hTV.2 bs hbs'
    have hfold := slotSet_fold_mem hfamU hfield hbs
    rw [hEisJ] at hfold
    have hfrT : shiftE (i + ((tssF J ψ).getD i []).length) 0
        (consList bs (consList (fs.take i) ρp)) = ρp := by
      rw [← consList_append, show i + ((tssF J ψ).getD i []).length = (fs.take i ++ bs).length
          from by rw [List.length_append, hlenTake, hlenBs]]
      exact shiftE_consList _ _
    obtain ⟨hvalT, -⟩ := tagTupleAV_facts hTag hIdsT hfrT (fun E hE => (hEok E hE).1) hfit
    rw [List.map_singleton, hvalT] at hfold
    refine ⟨hEok, ⟨_, hIdsT, hfit⟩, slotSet_chainOk hfamU hfield hbs, ?_⟩
    unfold auxFib auxTup
    exact hfold
  -- **the auxiliary recursor's frame facts** (`AuxFrameOk`)
  have hfrmG : ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V ((((ppsF 0 ψ).take p.toBlock.nP).map (·.2.2)).reverse) ρp →
      AuxFrameOk mp₂.base2 ψ (p.toBlock.elimLevel.eval ψ) (Wf ψ) (f₀.s.eval ψ)
        (pwBit ψ (Level.zeronessOf p.toBlock.elimLevel)) p.toBlock.nP
        ((ppsF 0 ψ).take p.toBlock.nP) (Idssf ψ) rssf (tlssf ψ) (Eissf ψ) (Fss0f ψ) (Essf ψ)
        (auxCtorData (Wf ψ) (Idssf ψ) memF (fun J => tgtAt (ksF J))
          (fixCtorDataList dsF esF (fun J => kindsOf (ksF J)) eissF tssF ψ ctorsA 0)) ρp := by
    intro ψ ρp hρ
    obtain ⟨hTag, hVal⟩ := hIdxAll 0 f₀ hf0 ψ ρp hρ
    obtain ⟨hFix, -, -⟩ := hChainFull 0 f₀ hf0 ψ ρp hρ
    obtain ⟨hX, -⟩ := hXAll 0 f₀ hf0 ψ ρp hρ
    refine ⟨hTag, hVal, hFix, hX, hLeafTG ψ (fun k => ρp (k + p.toBlock.nP)), ?_⟩
    intro j cd' hcd' M hM ms hms
    rw [auxCtorData_getElem?] at hcd'
    obtain ⟨cd, hcdj, rfl⟩ := Option.map_eq_some_iff.mp hcd'
    obtain ⟨cA, hcA, hJl, rfl⟩ := hdecG ψ j cd hcdj
    have hlenDs := (hCD₁ j cA hcA).len ψ
    have hρJ : Sat V (((dsF j ψ).take p.toBlock.nP).map (·.2.2)).reverse ρp :=
      ((hframesJ j hJl).1 ψ ρp).mp
        (hframeAll 0 (memF j) f₀ _ hf0 (hfmGet _ (hmotLt j hJl)) ψ ρp hρ)
    have hfrJ := (hframesJ j hJl).2 ψ ρp hρJ
    have hnFJ : nFs j = cA.2 := by
      show (ctorsA.getD j default).2 = cA.2
      rw [List.getD_eq_getElem?_getD, hcA]; rfl
    have hlenEis0 : (eissF₀ j ψ).length = nFs j := by
      rw [(hident j cA hcA).2.2.2.2.2.1 ψ, (hCD₁ j cA hcA).eissLen ψ, hnFJ]
    -- the datum's chain entries, positionally
    have hris : ConLeche.recIdxOf (kindsOf (ksF j)) = recIdx (rssf.getD j []) cA.2 := by
      rw [mutRss_getD hJl, ← (hksJ j cA hcA).1, ← kindsOf_length, recIdx_rsOf]
    have htls : tssF j ψ = (tlssf ψ).getD j [] := by
      show _ = (mutTlss ctorsA.length tssF₀ ψ).getD j []
      rw [mutTlss_getD hJl]
      exact ((hident j cA hcA).2.2.2.2.2.2.1 ψ).symm
    have hEiss : ((List.range cA.2).map fun i =>
          [tagTupleAV (Wf ψ) (tgtAt (ksF j) i) (i + ((tssF j ψ).getD i []).length) (Idssf ψ)
            ((eissF j ψ).getD i [])])
        = (Eissf ψ).getD j [] := by
      rw [mutEiss'_getDJ hJl hlenEis0, (hident j cA hcA).2.2.2.2.2.2.1 ψ,
        (hident j cA hcA).2.2.2.2.2.1 ψ, hnFJ]
    show WellDenotedV V (consList ms (cons M ρp))
        (minorAVAtR mp₂.base2 cA.1.name ψ p.toBlock.nP cA.2
          (pwBit ψ (Level.zeronessOf p.toBlock.elimLevel)) (1 + j) (dsF j ψ)
          [tagTupleAV (Wf ψ) (memF j) cA.2 (Idssf ψ) (esF j ψ)]
          (ConLeche.recIdxOf (kindsOf (ksF j))) (tssF j ψ)
          ((List.range cA.2).map fun i =>
            [tagTupleAV (Wf ψ) (tgtAt (ksF j) i) (i + ((tssF j ψ).getD i []).length) (Idssf ψ)
              ((eissF j ψ).getD i [])])) ∧
      interp V (consList ms (cons M ρp))
        (minorAVAtR mp₂.base2 cA.1.name ψ p.toBlock.nP cA.2
          (pwBit ψ (Level.zeronessOf p.toBlock.elimLevel)) (1 + j) (dsF j ψ)
          [tagTupleAV (Wf ψ) (memF j) cA.2 (Idssf ψ) (esF j ψ)]
          (ConLeche.recIdxOf (kindsOf (ksF j))) (tssF j ψ)
          ((List.range cA.2).map fun i =>
            [tagTupleAV (Wf ψ) (tgtAt (ksF j) i) (i + ((tssF j ψ).getD i []).length) (Idssf ψ)
              ((eissF j ψ).getD i [])]))
        ∈ˢ (univ (if p.toBlock.elimLevel.eval ψ = 0 then 0
          else Nat.max (f₀.s.eval ψ) (p.toBlock.elimLevel.eval ψ)) : V)
    rw [hris, hEiss, htls]
    have hFok : FieldsOkB (f₀.s.eval ψ) ρp (((dsF j ψ).drop p.toBlock.nP).map (·.2.2)) := by
      rw [← hsEq _ _ (hfmGet _ (hmotLt j hJl)) ψ]
      exact hfrJ.1
    refine minorTag_facts (pwBit_zeronessOf ψ _).symm (hw0G ψ) hms hTag hVal hM hlenDs
      hFok hfrJ.2.1 (fun fs hfs => ⟨(hfrJ.2.2.2 fs hfs).1,
        ⟨_, hIdssGet ψ (memF j) (hmotLt j hJl), (hfrJ.2.2.2 fs hfs).2⟩⟩)
      (fun fs hfs => ?_) (fun fs hfs => ?_) (fun fs hfs i hi => ?_)
    · have h := hCtorOkG ψ ρp hρ j _ hcdj M ms fs hfs
      rw [hms] at h
      exact h
    · rw [interp_ctorAppAV (o := 1 + j) (by omega) hlenDs (hleafC₂ j cA hcA ψ)
        (mp₂.base2.cval_closedL _ ψ) (hFssG ψ j hJl) (hFssOkP j cA hcA ψ ρp hρJ).1 hρJ hfs]
      exact ((hFrameOkG ψ ρp hρ).ctor j _ hcdj fs hfs).2.2
    · exact hSlotTagG ψ ρp hρ j _ hcdj fs hfs i hi
  -- **the auxiliary family's chains and the constructors' readings**
  -- (`auxRecLeafFacts`' `hchains`)
  have hchainsG : ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V ((((ppsF 0 ψ).take p.toBlock.nP).map (·.2.2)).reverse) ρp →
      XChainsOk (Wf ψ) (f₀.s.eval ψ) ρp ((tagIps (Wf ψ) (Idssf ψ)).map (·.2.2)) rssf (tlssf ψ)
          (Eissf ψ) (Fss0f ψ) (Essf ψ) ∧
      ChainsRealI (fixFamI (Wf ψ) (f₀.s.eval ψ) ρp ((tagIps (Wf ψ) (Idssf ψ)).map (·.2.2)) 1
          rssf (tlssf ψ) (Eissf ψ) (Fss0f ψ) (Essf ψ)) (Wf ψ) (f₀.s.eval ψ) ρp
          ((tagIps (Wf ψ) (Idssf ψ)).map (·.2.2)) rssf (tlssf ψ) (Eissf ψ) (Fss0f ψ) (FssRf ψ)
          (Essf ψ) ∧
      (∀ j, j < ctorsA.length → FieldsOkB (f₀.s.eval ψ) ρp ((FssRf ψ).getD j []) ∧
        ∀ bs : List V, SpineFit ρp ((FssRf ψ).getD j []) bs →
          (∀ E ∈ (Essf ψ).getD j [], WellDenoted V (consList bs ρp) E) ∧
          SpineFit ρp ((tagIps (Wf ψ) (Idssf ψ)).map (·.2.2))
            (idxValsAt ρp ((Essf ψ).getD j []) bs)) := by
    intro ψ ρp hρ
    obtain ⟨hTag, hVal⟩ := hIdxAll 0 f₀ hf0 ψ ρp hρ
    obtain ⟨hFix, hReal, -⟩ := hChainFull 0 f₀ hf0 ψ ρp hρ
    obtain ⟨hX, -⟩ := hXAll 0 f₀ hf0 ψ ρp hρ
    rw [tagIps_doms]
    refine ⟨hX, hReal, fun j hj => ?_⟩
    have hcA := hcAGet j hj
    have hlenDs := (hCD₁ j _ hcA).len ψ
    have hρJ : Sat V (((dsF j ψ).take p.toBlock.nP).map (·.2.2)).reverse ρp :=
      ((hframesJ j hj).1 ψ ρp).mp
        (hframeAll 0 (memF j) f₀ _ hf0 (hfmGet _ (hmotLt j hj)) ψ ρp hρ)
    have hfrJ := (hframesJ j hj).2 ψ ρp hρJ
    have hFssJ : (FssRf ψ).getD j [] = ((dsF j ψ).drop p.toBlock.nP).map (·.2.2) :=
      mutFss_getD hj
    have hnFJ : nFs j = (ctorsA.getD j default).2 := rfl
    have hlenF : (((dsF j ψ).drop p.toBlock.nP).map (·.2.2)).length = (ctorsA.getD j default).2 := by
      rw [List.length_map, List.length_drop, hlenDs, Nat.add_sub_cancel_left]
    refine ⟨by rw [hFssJ, ← hsEq _ _ (hfmGet _ (hmotLt j hj)) ψ]; exact hfrJ.1, fun bs hbs => ?_⟩
    rw [hFssJ] at hbs
    obtain ⟨hEok, hfit⟩ := hfrJ.2.2.2 bs hbs
    have hlenbs : bs.length = (ctorsA.getD j default).2 := by rw [hbs.length_eq, hlenF]
    have hfr : shiftE (ctorsA.getD j default).2 0 (consList bs ρp) = ρp := by
      rw [← hlenbs]; exact shiftE_consList _ _
    obtain ⟨hvalT, hokT⟩ := tagTupleAV_facts hTag (hIdssGet ψ (memF j) (hmotLt j hj)) hfr
      (fun E hE => (hEok E hE).1) hfit
    rw [hEssD j _ hcA ψ]
    refine ⟨fun E hE => by rw [List.mem_singleton] at hE; subst hE; exact hokT, ?_⟩
    show SpineFit ρp (auxIds (Wf ψ) (Idssf ψ))
      ([tagTupleAV (Wf ψ) (memF j) (ctorsA.getD j default).2 (Idssf ψ) (esF j ψ)].map
        (interp V (consList bs ρp)))
    rw [List.map_singleton, hvalT]
    refine ⟨?_, trivial⟩
    rw [(tagTyAV_facts hTag).1]
    exact tagTuple_mem hTag (hIdssGet ψ (memF j) (hmotLt j hj)) hfit
  -- **the minors' readings** (`auxRecLeafFacts`' `hminorRead`)
  have hminorReadG : ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V ((((ppsF 0 ψ).take p.toBlock.nP).map (·.2.2)).reverse) ρp →
      ∀ (j : Nat) (cd : CtorDatumR),
        (auxCtorData (Wf ψ) (Idssf ψ) memF (fun J => tgtAt (ksF J))
          (fixCtorDataList dsF esF (fun J => kindsOf (ksF J)) eissF tssF ψ ctorsA 0))[j]?
          = some cd →
      ∀ (M : V) (ms : List V), ms.length = j →
        interp V (consList ms (cons M ρp))
            (minorAVAtR mp₂.base2 cd.1 ψ p.toBlock.nP cd.2.1
              (pwBit ψ (Level.zeronessOf p.toBlock.elimLevel)) (1 + j) cd.2.2.1 cd.2.2.2.1
              cd.2.2.2.2.1 cd.2.2.2.2.2.2 cd.2.2.2.2.2.1)
          = minorSpI (p.toBlock.elimLevel.eval ψ)
              (fun fs => ihSpL (p.toBlock.elimLevel.eval ψ)
                (concI (f₀.s.eval ψ) ρp M ((Essf ψ).getD j []) j fs)
                (ihDomsI (p.toBlock.elimLevel.eval ψ) ρp M rssf (tlssf ψ) (Eissf ψ)
                  (fun j' => ((FssRf ψ).getD j' []).length) j fs))
              ((FssRf ψ).getD j []) ρp [] := by
    intro ψ ρp hρ j cd' hcd' M ms hms
    rw [auxCtorData_getElem?] at hcd'
    obtain ⟨cd, hcdj, rfl⟩ := Option.map_eq_some_iff.mp hcd'
    obtain ⟨cA, hcA, hJl, rfl⟩ := hdecG ψ j cd hcdj
    have hlenDs := (hCD₁ j cA hcA).len ψ
    have hρJ : Sat V (((dsF j ψ).take p.toBlock.nP).map (·.2.2)).reverse ρp :=
      ((hframesJ j hJl).1 ψ ρp).mp
        (hframeAll 0 (memF j) f₀ _ hf0 (hfmGet _ (hmotLt j hJl)) ψ ρp hρ)
    have hnFJ : nFs j = cA.2 := by
      show (ctorsA.getD j default).2 = cA.2
      rw [List.getD_eq_getElem?_getD, hcA]; rfl
    have hlenEis0 : (eissF₀ j ψ).length = nFs j := by
      rw [(hident j cA hcA).2.2.2.2.2.1 ψ, (hCD₁ j cA hcA).eissLen ψ, hnFJ]
    have hris : ConLeche.recIdxOf (kindsOf (ksF j)) = recIdx (rssf.getD j []) cA.2 := by
      rw [mutRss_getD hJl, ← (hksJ j cA hcA).1, ← kindsOf_length, recIdx_rsOf]
    have htls : tssF j ψ = (tlssf ψ).getD j [] := by
      show _ = (mutTlss ctorsA.length tssF₀ ψ).getD j []
      rw [mutTlss_getD hJl]
      exact ((hident j cA hcA).2.2.2.2.2.2.1 ψ).symm
    have hEiss : ((List.range cA.2).map fun i =>
          [tagTupleAV (Wf ψ) (tgtAt (ksF j) i) (i + ((tssF j ψ).getD i []).length) (Idssf ψ)
            ((eissF j ψ).getD i [])])
        = (Eissf ψ).getD j [] := by
      rw [mutEiss'_getDJ hJl hlenEis0, (hident j cA hcA).2.2.2.2.2.2.1 ψ,
        (hident j cA hcA).2.2.2.2.2.1 ψ, hnFJ]
    show interp V (consList ms (cons M ρp))
        (minorAVAtR mp₂.base2 cA.1.name ψ p.toBlock.nP cA.2
          (pwBit ψ (Level.zeronessOf p.toBlock.elimLevel)) (1 + j) (dsF j ψ)
          [tagTupleAV (Wf ψ) (memF j) cA.2 (Idssf ψ) (esF j ψ)]
          (ConLeche.recIdxOf (kindsOf (ksF j))) (tssF j ψ)
          ((List.range cA.2).map fun i =>
            [tagTupleAV (Wf ψ) (tgtAt (ksF j) i) (i + ((tssF j ψ).getD i []).length) (Idssf ψ)
              ((eissF j ψ).getD i [])])) = _
    rw [hris, hEiss, htls, hEssD j cA hcA ψ, mutFss_getD hJl]
    exact interp_minorAVAtR (ℓ := p.toBlock.elimLevel.eval ψ) (Fss := FssRf ψ) (rss := rssf)
      (tlss := tlssf ψ) (Eiss := Eissf ψ) (pwBit_zeronessOf ψ _).symm hms hlenDs
      (hleafC₂ j cA hcA ψ) (mp₂.base2.cval_closedL _ ψ) (hFssG ψ j hJl)
      (hFssOkP j cA hcA ψ ρp hρJ).1 hρJ
  -- **the chains' validity** (`auxRecLeafFacts`' `hvFss`)
  have hvFssG : ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V ((((ppsF 0 ψ).take p.toBlock.nP).map (·.2.2)).reverse) ρp →
      SumFieldsValid ρp (FssRf ψ) ∧
      (∀ j, j < ctorsA.length → ∀ bs : List V, SpineFit ρp ((FssRf ψ).getD j []) bs →
        ∀ E ∈ (Essf ψ).getD j [], AnnotValid V (consList bs ρp) E) ∧
      (∀ j, j < ctorsA.length → ∀ i ∈ recIdx (rssf.getD j []) ((FssRf ψ).getD j []).length,
        ∀ fs : List V, SpineFit ρp ((FssRf ψ).getD j []) fs →
        FieldsValid (consList (fs.take i) ρp) ((((tlssf ψ).getD j []).getD i []).map (·.2.2)) ∧
        ∀ bs : List V, SpineFit (consList (fs.take i) ρp)
          ((((tlssf ψ).getD j []).getD i []).map (·.2.2)) bs →
        ∀ E ∈ ((Eissf ψ).getD j []).getD i [],
          AnnotValid V (consList bs (consList (fs.take i) ρp)) E) := by
    intro ψ ρp hρ
    obtain ⟨hTag, hVal⟩ := hIdxAll 0 f₀ hf0 ψ ρp hρ
    have hρJ : ∀ j, j < ctorsA.length →
        Sat V (((dsF j ψ).take p.toBlock.nP).map (·.2.2)).reverse ρp := by
      intro j hj
      exact ((hframesJ j hj).1 ψ ρp).mp
        (hframeAll 0 (memF j) f₀ _ hf0 (hfmGet _ (hmotLt j hj)) ψ ρp hρ)
    refine ⟨?_, fun j hj bs hbs E hE => ?_, fun j hj i hi fs hfs => ?_⟩
    · by_cases hne : 0 < ctorsA.length
      · exact (hFssOkP 0 _ (hcAGet 0 hne) ψ ρp (hρJ 0 hne)).2
      · have h0 : ctorsA.length = 0 := by omega
        show SumFieldsValid ρp (mutFss p.toBlock.nP ctorsA.length dsF ψ)
        rw [h0]
        intro Fs hFs
        simp only [mutFss, List.range_zero, List.map_nil] at hFs
        exact nomatch hFs
    · have hcA := hcAGet j hj
      have hlenDs := (hCD₁ j _ hcA).len ψ
      have hfrJ := (hframesJ j hj).2 ψ ρp (hρJ j hj)
      rw [mutFss_getD hj] at hbs
      obtain ⟨hEok, hfit⟩ := hfrJ.2.2.2 bs hbs
      have hlenbs : bs.length = (ctorsA.getD j default).2 := by
        rw [hbs.length_eq, List.length_map, List.length_drop, hlenDs, Nat.add_sub_cancel_left]
      have hfr : shiftE (ctorsA.getD j default).2 0 (consList bs ρp) = ρp := by
        rw [← hlenbs]; exact shiftE_consList _ _
      rw [hEssD j _ hcA ψ, List.mem_singleton] at hE
      subst hE
      exact tagTupleAV_validVC hVal (hIdssGet ψ (memF j) (hmotLt j hj)) hfr
        (fun E hE => (hEok E hE).2)
    · have hcA := hcAGet j hj
      have hlenDs := (hCD₁ j _ hcA).len ψ
      have hlenFj : ((FssRf ψ).getD j []).length = (ctorsA.getD j default).2 := by
        rw [mutFss_getD hj, List.length_map, List.length_drop, hlenDs, Nat.add_sub_cancel_left]
      have hcdj : (fixCtorDataList dsF esF (fun J => kindsOf (ksF J)) eissF tssF ψ ctorsA 0)[j]?
          = some ((ctorsA.getD j default).1.name, (ctorsA.getD j default).2, dsF j ψ, esF j ψ,
              ConLeche.recIdxOf (kindsOf (ksF j)), eissF j ψ, tssF j ψ) := by
        rw [fixCtorDataList_getElem?, hcA]
        simp only [Nat.zero_add, Option.map_some]
      rw [mutFss_getD hj] at hfs
      have hslot := hSlotTagG ψ ρp hρ j _ hcdj fs hfs i (by rw [← hlenFj]; exact hi)
      refine ⟨hslot.2.1, fun bs hbs E hE => ?_⟩
      obtain ⟨tgt, Es, heq, hrest⟩ := hslot.2.2
      obtain ⟨hEok, -, -, -⟩ := hrest bs hbs
      rw [heq, List.mem_singleton] at hE
      subst hE
      have hlenBs : bs.length = (((tlssf ψ).getD j []).getD i []).length := by
        rw [hbs.length_eq, List.length_map]
      have hilt : i < (ctorsA.getD j default).2 := by
        have h := (mem_recIdx.mp hi).1
        rwa [hlenFj] at h
      have hlenTake : (fs.take i).length = i := by
        rw [List.length_take, hfs.length_eq, List.length_map, List.length_drop,
          (hCD₁ j _ hcA).len ψ]
        omega
      have hfrT : shiftE (i + (((tlssf ψ).getD j []).getD i []).length) 0
          (consList bs (consList (fs.take i) ρp)) = ρp := by
        rw [← consList_append,
          show i + (((tlssf ψ).getD j []).getD i []).length = (fs.take i ++ bs).length from by
            rw [List.length_append, hlenTake, hlenBs]]
        exact shiftE_consList _ _
      obtain ⟨Ids, hIds⟩ : ∃ Ids, (Idssf ψ)[tgt]? = some Ids := by
        obtain ⟨-, ⟨Ids, hIds, -⟩, -, -⟩ := hrest bs hbs
        exact ⟨Ids, hIds⟩
      exact tagTupleAV_validVC hVal hIds hfrT (fun E hE => (hEok E hE).2)
  -- **the auxiliary recursor's leaf is closed** (`nativeRecAVI_below`
  -- at `auxRecDataAV_below`)
  have hclRG : ∀ ψ : Name → Nat, Term.bvarsBelow 0
      (auxRecAV mp₂.base2 ψ (p.toBlock.elimLevel.eval ψ) (Wf ψ) (f₀.s.eval ψ) p.toBlock.nP
        (auxRecSort (Wf ψ) (Wf ψ) (f₀.s.eval ψ) (p.toBlock.elimLevel.eval ψ))
        p.toBlock.elimLevel ((ppsF 0 ψ).take p.toBlock.nP) (Idssf ψ) rssf (tlssf ψ) (Eissf ψ)
        (FssRf ψ) (Fss0f ψ) (Essf ψ) memF (fun J => tgtAt (ksF J))
        (fixCtorDataList dsF esF (fun J => kindsOf (ksF J)) eissF tssF ψ ctorsA 0)).erase := by
    intro ψ
    have hlenP0 : ((ppsF 0 ψ).take p.toBlock.nP).length = p.toBlock.nP := by
      rw [List.length_take, (hFD₂ 0 f₀ hf0).len ψ]; omega
    have hlenFssR : (FssRf ψ).length = ctorsA.length := mutFss_length
    have hEssB : ∀ j, j < (FssRf ψ).length →
        ((Essf ψ).getD j []).length = 1 ∧
        ∀ E ∈ (Essf ψ).getD j [],
          Term.bvarsBelow (p.toBlock.nP + ((FssRf ψ).getD j []).length) E.erase := by
      intro j hj
      rw [hlenFssR] at hj
      rw [mutEss'_getD hj, mutFss_getD hj]
      refine ⟨rfl, fun E hE => ?_⟩
      rw [List.mem_singleton] at hE
      subst hE
      rw [show (((dsF j ψ).drop p.toBlock.nP).map (·.2.2)).length = nFs j from by
        rw [List.length_map, List.length_drop, (hCD₁ j _ (hcAGet j hj)).len ψ]
        show p.toBlock.nP + nFs j - p.toBlock.nP = nFs j
        omega]
      exact tagTupleAV_belowM (nP := p.toBlock.nP) (W := Wf ψ) (m := memF j) (d := nFs j)
        (hIdsBelow ψ) (fun E hE => (hCD₀ j _ (hcAGet j hj)).belowE ψ E hE)
    show Term.bvarsBelow 0 (nativeRecAVI _ _ _ (FssRf ψ) (Essf ψ) (auxIds (Wf ψ) (Idssf ψ))
      rssf (tlssf ψ) (Eissf ψ) (auxRecDataAV mp₂.base2 ψ (Wf ψ) (f₀.s.eval ψ) p.toBlock.nP
        p.toBlock.elimLevel ((ppsF 0 ψ).take p.toBlock.nP) (Idssf ψ) rssf (tlssf ψ) (Eissf ψ)
        (Fss0f ψ) (Essf ψ) memF (fun J => tgtAt (ksF J))
        (fixCtorDataList dsF esF (fun J => kindsOf (ksF J)) eissF tssF ψ ctorsA 0)) _).erase
    refine nativeRecAVI_below 0
      (auxRecDataAV_below (domsBelow_take ((hFD₂ 0 f₀ hf0).below ψ)) hlenP0
        (hIdsBelow ψ) (hchainBelow ψ) (hRawCtor ψ))
      ?_ rfl ?_ (hFssBelowG ψ) ?_ ?_
    · unfold auxRecDataAV
      rw [fixRecDataAVL_length hlenP0 (show (tagIps (Wf ψ) (Idssf ψ)).length = 1 from rfl),
        auxCtorData_length, fixCtorDataList_length, hlenFssR,
        show (auxIds (Wf ψ) (Idssf ψ)).length = 1 from rfl]
      omega
    · intro Fs' hFs'
      rw [show (auxIds (Wf ψ) (Idssf ψ)).length = 1 from rfl, hlenFssR] at hFs'
      have hb := rChains_below (d := 1 + ctorsA.length + 1) (nIdx := 1) (K := p.toBlock.nP)
        (by omega) (hFssBelowG ψ) hEssB Fs' hFs'
      rw [show (auxIds (Wf ψ) (Idssf ψ)).length = 1 from rfl, hlenFssR]
      exact fieldsBelow_mono (by omega) hb
    · -- the slots' telescopes
      intro j i
      by_cases hj : j < ctorsA.length
      · show DomsBelow _ (((mutTlss ctorsA.length tssF₀ ψ).getD j []).getD i [])
        rw [mutTlss_getD hj]
        exact (hCD₀ j _ (hcAGet j hj)).tssBelow ψ i
      · show DomsBelow _ (((mutTlss ctorsA.length tssF₀ ψ).getD j []).getD i [])
        rw [show (mutTlss ctorsA.length tssF₀ ψ).getD j [] = [] from by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [mutTlss]; omega)]
          rfl]
        exact trivial
    · -- the slots' index expressions
      intro j i E hE
      have hE' : E ∈ ((mutEiss' (Wf ψ) (Idssf ψ) ksF nFs tssF₀ eissF₀ ψ).getD j []).getD i [] := hE
      show Term.bvarsBelow
        (p.toBlock.nP + i + (((mutTlss ctorsA.length tssF₀ ψ).getD j []).getD i []).length) E.erase
      by_cases hj : j < ctorsA.length
      · have hEL : (eissF₀ j ψ).length = nFs j := (hCD₀ j _ (hcAGet j hj)).eissLen ψ
        rw [mutTlss_getD hj]
        by_cases hi : i < nFs j
        · rw [mutEiss'_getD hj hi hEL, List.mem_singleton] at hE'
          subst hE'
          have hb := tagTupleAV_belowM (nP := p.toBlock.nP) (W := Wf ψ)
            (m := tgtAt (ksF j) i)
            (d := i + ((tssF₀ j ψ).getD i []).length) (hIdsBelow ψ) (fun E hE => by
              have hh := (hCD₀ j _ (hcAGet j hj)).eissBelow ψ i E hE
              rwa [show p.toBlock.nP + i + ((tssF₀ j ψ).getD i []).length
                = p.toBlock.nP + (i + ((tssF₀ j ψ).getD i []).length) from by omega] at hh)
          rwa [show p.toBlock.nP + (i + ((tssF₀ j ψ).getD i []).length)
            = p.toBlock.nP + i + ((tssF₀ j ψ).getD i []).length from by omega] at hb
        · rw [mutEiss'_getDJ hj hEL, List.getD_eq_getElem?_getD, List.getElem?_map,
            List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hi)] at hE'
          exact nomatch hE'
      · rw [show (mutEiss' (Wf ψ) (Idssf ψ) ksF nFs tssF₀ eissF₀ ψ).getD j [] = [] from by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
            show (mutEiss' (Wf ψ) (Idssf ψ) ksF nFs tssF₀ eissF₀ ψ).length ≤ j
            unfold mutEiss' mutualEiss
            simp only [List.length_map, List.length_range, mutEiss0_length]
            omega)]
          rfl] at hE'
        exact nomatch hE'
  -- **the auxiliary recursor's own facts** (`auxRecLeafFacts`,
  -- `auxConc_facts`)
  have hlenP0G : ∀ ψ : Name → Nat, ((ppsF 0 ψ).take p.toBlock.nP).length = p.toBlock.nP := by
    intro ψ
    rw [List.length_take, (hFD₂ 0 f₀ hf0).len ψ]; omega
  have hclLG : ∀ ψ : Name → Nat, Term.bvarsBelow 0
      (auxFormerAV (Wf ψ) (f₀.s.eval ψ) ((ppsF 0 ψ).take p.toBlock.nP) (Idssf ψ) rssf (tlssf ψ)
        (Eissf ψ) (Fss0f ψ) (Essf ψ)).erase := fun ψ =>
    auxFormerAV_below (domsBelow_take ((hFD₂ 0 f₀ hf0).below ψ)) (hlenP0G ψ)
      (hIdsBelow ψ) (hchainBelow ψ)
  have hEisLenG : ∀ (ψ : Name → Nat) (j i : Nat),
      i ∈ recIdx (rssf.getD j []) ((FssRf ψ).getD j []).length →
      (((Eissf ψ).getD j []).getD i []).length = 1 := by
    intro ψ j i hi
    by_cases hj : j < ctorsA.length
    · have hcA := hcAGet j hj
      have hlenFj : ((FssRf ψ).getD j []).length = nFs j := by
        rw [mutFss_getD hj, List.length_map, List.length_drop, (hCD₁ j _ hcA).len ψ,
          Nat.add_sub_cancel_left]
      have hilt : i < nFs j := by
        have h := (mem_recIdx.mp hi).1
        rwa [hlenFj] at h
      have hlenEis0 : (eissF₀ j ψ).length = nFs j := by
        rw [(hident j _ hcA).2.2.2.2.2.1 ψ, (hCD₁ j _ hcA).eissLen ψ]
      rw [mutEiss'_getD hj hilt hlenEis0]
      rfl
    · exfalso
      have h := (mem_recIdx.mp hi).2
      rw [show rssf.getD j [] = [] from by
        show (mutRss ctorsA.length ksF).getD j [] = []
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [mutRss]; omega)]
        rfl] at h
      simp at h
  have hppsG : ∀ (ψ : Name → Nat) (ρb : Nat → V),
      EntriesOk V (auxRecSort (Wf ψ) (Wf ψ) (f₀.s.eval ψ) (p.toBlock.elimLevel.eval ψ)) ρb
        (rebit (pwBit ψ (Level.zeronessOf p.toBlock.elimLevel)) ((ppsF 0 ψ).take p.toBlock.nP)) := by
    intro ψ ρb
    refine formerParamsOk (hFD₂ 0 f₀ hf0) (fun hs i hi => ?_) ρb
    have hℓ0 : p.toBlock.elimLevel.eval ψ ≠ 0 := fun h0 =>
      hs ((auxRecSort_zero_iff _ _ _ _).mpr h0)
    exact Nat.le_trans (hWge ψ 0 i hk0) (auxRecSort_ge _ _ _ _ hℓ0).1
  have hauxG : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      WellDenotedV V ρ
        (auxRecAV mp₂.base2 ψ (p.toBlock.elimLevel.eval ψ) (Wf ψ) (f₀.s.eval ψ) p.toBlock.nP
          (auxRecSort (Wf ψ) (Wf ψ) (f₀.s.eval ψ) (p.toBlock.elimLevel.eval ψ))
          p.toBlock.elimLevel ((ppsF 0 ψ).take p.toBlock.nP) (Idssf ψ) rssf (tlssf ψ) (Eissf ψ)
          (FssRf ψ) (Fss0f ψ) (Essf ψ) memF (fun J => tgtAt (ksF J))
          (fixCtorDataList dsF esF (fun J => kindsOf (ksF J)) eissF tssF ψ ctorsA 0)) ∧
      interp V ρ
          (auxRecAV mp₂.base2 ψ (p.toBlock.elimLevel.eval ψ) (Wf ψ) (f₀.s.eval ψ) p.toBlock.nP
            (auxRecSort (Wf ψ) (Wf ψ) (f₀.s.eval ψ) (p.toBlock.elimLevel.eval ψ))
            p.toBlock.elimLevel ((ppsF 0 ψ).take p.toBlock.nP) (Idssf ψ) rssf (tlssf ψ) (Eissf ψ)
            (FssRf ψ) (Fss0f ψ) (Essf ψ) memF (fun J => tgtAt (ksF J))
            (fixCtorDataList dsF esF (fun J => kindsOf (ksF J)) eissF tssF ψ ctorsA 0))
        ∈ˢ interp V ρ (mkPisAV
          (auxRecDataAV mp₂.base2 ψ (Wf ψ) (f₀.s.eval ψ) p.toBlock.nP p.toBlock.elimLevel
            ((ppsF 0 ψ).take p.toBlock.nP) (Idssf ψ) rssf (tlssf ψ) (Eissf ψ) (Fss0f ψ) (Essf ψ)
            memF (fun J => tgtAt (ksF J))
            (fixCtorDataList dsF esF (fun J => kindsOf (ksF J)) eissF tssF ψ ctorsA 0))
          (recConcAV ctorsA.length 1)) := by
    intro ψ
    exact auxRecLeafFacts rfl rfl (pwBit_zeronessOf ψ _).symm (hw0G ψ)
      (auxRecSort_zero_iff _ _ _ _)
      (fun h0 => (auxRecSort_ge _ _ _ _ h0).2.1)
      (fun h0 => (auxRecSort_ge _ _ _ _ h0).2.2.1)
      (fun h0 => (auxRecSort_ge _ _ _ _ h0).2.2.2)
      (hlenP0G ψ) (by rw [auxCtorData_length, fixCtorDataList_length]) mutFss_length mutEss'_length
      (fun j hj => by rw [hEssD j _ (hcAGet j hj) ψ]; rfl) (hEisLenG ψ) (hIdsBelow ψ)
      (hslotTagG ψ) (hTbelowG ψ)
      (auxRecDataAV_below (domsBelow_take ((hFD₂ 0 f₀ hf0).below ψ)) (hlenP0G ψ)
        (hIdsBelow ψ) (hchainBelow ψ) (hRawCtor ψ))
      (hclLG ψ) (hppsG ψ) (hfrmG ψ) (hchainsG ψ) (hminorReadG ψ) (hvFssG ψ)
  have hauxConcG : ∀ (ψ : Name → Nat) (ρ : Nat → V) (as : List V),
      SpineFit ρ ((auxRecDataAV mp₂.base2 ψ (Wf ψ) (f₀.s.eval ψ) p.toBlock.nP
          p.toBlock.elimLevel ((ppsF 0 ψ).take p.toBlock.nP) (Idssf ψ) rssf (tlssf ψ) (Eissf ψ)
          (Fss0f ψ) (Essf ψ) memF (fun J => tgtAt (ksF J))
          (fixCtorDataList dsF esF (fun J => kindsOf (ksF J)) eissF tssF ψ ctorsA 0)).map (·.2.2))
        as →
      interp V (consList as ρ) (recConcAV ctorsA.length 1)
        ∈ˢ (univ (p.toBlock.elimLevel.eval ψ) : V) := by
    intro ψ ρ as hsp
    exact (auxConc_facts (m := mp₂.base2) (ψ := ψ) (W := Wf ψ) (wB := f₀.s.eval ψ)
      (Fss := FssRf ψ)
      (cds := auxCtorData (Wf ψ) (Idssf ψ) memF (fun J => tgtAt (ksF J))
        (fixCtorDataList dsF esF (fun J => kindsOf (ksF J)) eissF tssF ψ ctorsA 0))
      rfl rfl (hlenP0G ψ) (by rw [auxCtorData_length, fixCtorDataList_length])
      (hclLG ψ) (hfrmG ψ) (hminorReadG ψ) ρ as hsp).2
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
    have hdec := hdecG ψ
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
      intro J cd hJd
      obtain ⟨cA, hcA, hJl, rfl⟩ := hdec J cd hJd
      have hnFJ : nFs J = cA.2 := by
        show (ctorsA.getD J default).2 = cA.2
        rw [List.getD_eq_getElem?_getD, hcA]; rfl
      refine ⟨(hCD₁ J cA hcA).len ψ, ?_, hleafC₂ J cA hcA ψ,
        mp₂.base2.cval_closedL cA.1.name ψ, ?_, ?_, ?_, ?_, ?_⟩
      · exact fun ρ => ((hframesJ J hJl).1 ψ ρ).symm.trans
          (hframeM (memF J) _ (hfmGet _ (hmotLt J hJl)) ψ ρ)
      · show (mutFss p.toBlock.nP ctorsA.length dsF ψ)[J]? = _
        show ((List.range ctorsA.length).map _)[J]? = _
        rw [List.getElem?_map, List.getElem?_range hJl]
        rfl
      · show ConLeche.recIdxOf (kindsOf (ksF J))
          = recIdx ((mutRss ctorsA.length ksF).getD J []) cA.2
        rw [mutRss_getD hJl, ← (hksJ J cA hcA).1, ← kindsOf_length, recIdx_rsOf]
      · show tssF J ψ = (mutTlss ctorsA.length tssF₀ ψ).getD J []
        rw [mutTlss_getD hJl]
        exact ((hident J cA hcA).2.2.2.2.2.2.1 ψ).symm
      · show eissF J ψ = (mutEiss0 ctorsA.length eissF ψ).getD J []
        rw [mutEiss0_getD hJl]
      · show (mutEiss' (Wf ψ) (Idssf ψ) ksF nFs tssF₀ eissF₀ ψ).getD J []
          = (List.range cA.2).map fun i =>
            [tagTupleAV (Wf ψ) (tgtAt (ksF J) i)
              (i + (((mutTlss ctorsA.length tssF₀ ψ).getD J []).getD i []).length) (Idssf ψ)
              (((mutEiss0 ctorsA.length eissF ψ).getD J []).getD i [])]
        rw [mutEiss'_getDJ hJl
            (by rw [(hident J cA hcA).2.2.2.2.2.1 ψ, (hCD₁ J cA hcA).eissLen ψ, hnFJ]),
          mutTlss_getD hJl, mutEiss0_getD hJl, hnFJ,
          (hident J cA hcA).2.2.2.2.2.1 ψ]
    case hframes => exact hFrameOkG ψ
    case hclL =>
      exact auxFormerAV_below (domsBelow_take ((hFD₂ 0 f₀ hf0).below ψ))
        (by rw [List.length_take, (hFD₂ 0 f₀ hf0).len ψ]; omega)
        (hIdsBelow ψ) (hchainBelow ψ)
    case hclR => exact hclRG ψ
    case haux => exact hauxG ψ
    case hauxConc => exact hauxConcG ψ
    case hstore =>
      intro ρ
      have hnq : prts.nIdxs.getD t 0 = prts.nIdxOf t := getD_range_map _ _ _ ht _
      rw [hnq]
      exact (hRDs t ht).okTy ψ ρ
  -- **the recursor stage** and **the table stage**
  have hnCtors : prts.n = p.toBlock.n := hlenA
  have hk : cvRas.length = prts.k := by rw [hlenRec]; exact hkF
  -- **the recursors' shape**, off `checkMutualRecTy`'s run
  have hRecShape : ∀ t, t < prts.k → ∃ recTy : Expr,
      cvRas.getD t default = ⟨p.toBlock.recName t, p.toBlock.rlps, recTy⟩ ∧
      recTy.allLevelParamsDefined p.toBlock.rlps = true ∧
      recTy.constsResolve (ConLeche.consMutualCtors p.toBlock.nP ctorsA
        (ConLeche.consMutualFormers fms env)) = true ∧
      recTy.looseBVarsBounded 0 = true ∧ recTy.hasFvar = false ∧
      ∀ cvR, (p.members[t]?).map (·.cvR) = some cvR → ∃ cvRi,
        ConLeche.checkConstantVal (ConLeche.fueledOps μ F)
          (ConLeche.consMutualCtors p.toBlock.nP ctorsA
            (ConLeche.consMutualFormers fms env)) cvR = .ok cvRi := by
    intro t ht
    obtain ⟨cvRa, hget, hrun⟩ := hallRec t (by rw [hkF]; exact ht)
    obtain ⟨recTy, sty, u, -, hlp, hres, hbv, hfv, -, -, hstream, rfl⟩ :=
      ConLeche.checkMutualRecTy_shape hrun
    refine ⟨recTy, ?_, hlp, hres, hbv, hfv, fun cvR hcv => ?_⟩
    · rw [List.getD_eq_getElem?_getD, hget]; rfl
    · refine (hstream cvR ?_).imp fun cvRi h => h.1
      show Option.bind (some (p.members.map fun mb => (mb.cvR, mb.rules)))
        (fun rs => (rs[t]?).map (·.1)) = some cvR
      show ((p.members.map fun mb => (mb.cvR, mb.rules))[t]?).map (·.1) = some cvR
      rw [List.getElem?_map]
      cases hm : p.members[t]? with
      | none => rw [hm] at hcv; exact nomatch hcv
      | some mb =>
        rw [hm] at hcv
        simp only [Option.map_some] at hcv ⊢
        exact hcv
  -- **the recursors' own constant checks**, off the stream's records
  have hmembersLen : p.members.length = prts.k := by
    show p.members.length = fms.length
    rw [← hkF]
    show _ = (p.members.map fun mb => (mb.cv, mb.nIdx)).length
    rw [List.length_map]
  have hCVcheck : ∀ t, t < prts.k → ∃ mb : ConLeche.MutualMember, p.members[t]? = some mb ∧
      (cvRas.getD t default).name = mb.cvR.name ∧
      ∃ cvRi, ConLeche.checkConstantVal (ConLeche.fueledOps μ F)
        (ConLeche.consMutualCtors p.toBlock.nP ctorsA
          (ConLeche.consMutualFormers fms env)) mb.cvR = .ok cvRi := by
    intro t ht
    obtain ⟨recTy, hcv, -, -, -, -, hstream⟩ := hRecShape t ht
    obtain ⟨mb, hmb⟩ : ∃ mb, p.members[t]? = some mb :=
      ⟨_, List.getElem?_eq_getElem (by rw [hmembersLen]; exact ht)⟩
    refine ⟨mb, hmb, ?_, hstream mb.cvR (by rw [hmb]; rfl)⟩
    rw [hcv]
    show p.toBlock.recName t = mb.cvR.name
    rw [ConLeche.MutualParts.toBlock_recName hmb,
      ConLeche.mutualRecPinOk_name hpinOk (by rw [show p.k = prts.k from hmembersLen]; exact ht)
        hmb]
  have hfreshR : ∀ t, t < prts.k →
      (ConLeche.consMutualCtors p.toBlock.nP ctorsA
        (ConLeche.consMutualFormers fms env)).find? (cvRas.getD t default).name = none := by
    intro t ht
    obtain ⟨mb, -, hname, cvRi, hcvi⟩ := hCVcheck t ht
    rw [hname]
    exact (ConLeche.checkConstantVal_inv hcvi).1
  have hnres : ∀ t, t < prts.k →
      ConLeche.reservedBasisNames.contains (cvRas.getD t default).name = false := by
    intro t ht
    obtain ⟨mb, -, hname, cvRi, hcvi⟩ := hCVcheck t ht
    rw [hname]
    exact (ConLeche.checkConstantVal_inv hcvi).2.1
  have hpshape : ∀ t, t < prts.k →
      (cvRas.getD t default).name.isProjFnShape = false := by
    intro t ht
    obtain ⟨mb, -, hname, cvRi, hcvi⟩ := hCVcheck t ht
    rw [hname]
    exact (ConLeche.checkConstantVal_inv hcvi).2.2.1
  have hnd : (cvRas.map (·.name)).Nodup := by
    have hmapEq : cvRas.map (·.name) = (List.range prts.k).map p.toBlock.recName := by
      refine List.ext_getElem? fun t => ?_
      rw [List.getElem?_map, List.getElem?_map]
      by_cases ht : t < prts.k
      · obtain ⟨recTy, hcv, -, -, -, -, -⟩ := hRecShape t ht
        rw [List.getElem?_range ht,
          List.getElem?_eq_getElem (show t < cvRas.length by rw [hk]; exact ht)]
        have : cvRas[t] = cvRas.getD t default := by
          rw [List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem (show t < cvRas.length by rw [hk]; exact ht)]
          rfl
        rw [this, hcv]
        rfl
      · rw [List.getElem?_eq_none (by rw [hk]; omega),
          List.getElem?_eq_none (by simp; omega)]
        rfl
    rw [hmapEq, show prts.k = p.toBlock.k from hkF.symm]
    have hNd := hNodup
    unfold ConLeche.MutualBlock.blockNames at hNd
    exact (List.nodup_append.mp hNd).2.1
  have hresR : ∀ t, t < prts.k → (cvRas.getD t default).type.constsResolve
      (ConLeche.consMutualCtors p.toBlock.nP ctorsA
        (ConLeche.consMutualFormers fms env)) = true := by
    intro t ht
    obtain ⟨recTy, hcv, -, hres, -, -, -⟩ := hRecShape t ht
    rw [hcv]; exact hres
  have hAparams : ∀ t, t < prts.k → ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ q ∈ (cvRas.getD t default).levelParams, ψ₁ q = ψ₂ q) →
      prts.leaf mp₂.base2 t ψ₁ = prts.leaf mp₂.base2 t ψ₂ := by
    intro t ht ψ₁ ψ₂ hφR
    obtain ⟨recTy, hcv, -, -, -, -, -⟩ := hRecShape t ht
    rw [hcv] at hφR
    have hφRl : ∀ q ∈ p.toBlock.rlps, ψ₁ q = ψ₂ q := hφR
    have hφ : ∀ q ∈ p.toBlock.lps, ψ₁ q = ψ₂ q := by
      intro q hq
      refine hφRl q ?_
      show q ∈ (if p.toBlock.large then p.toBlock.elim :: p.toBlock.lps else p.toBlock.lps)
      cases p.toBlock.large
      · exact hq
      · exact List.mem_cons_of_mem _ hq
    have hev : p.toBlock.elimLevel.eval ψ₁ = p.toBlock.elimLevel.eval ψ₂ := by
      show Level.eval ψ₁ (ConLeche.structElimLevel p.toBlock.elim p.toBlock.large)
        = Level.eval ψ₂ (ConLeche.structElimLevel p.toBlock.elim p.toBlock.large)
      unfold ConLeche.structElimLevel
      cases hL : p.toBlock.large
      · rfl
      · show ψ₁ p.toBlock.elim = ψ₂ p.toBlock.elim
        refine hφRl p.toBlock.elim ?_
        show p.toBlock.elim ∈ (if p.toBlock.large then p.toBlock.elim :: p.toBlock.lps
          else p.toBlock.lps)
        rw [hL]
        exact List.mem_cons_self
    have hbb : pwBit ψ₁ (Level.zeronessOf p.toBlock.elimLevel)
        = pwBit ψ₂ (Level.zeronessOf p.toBlock.elimLevel) := by
      by_cases hz : p.toBlock.elimLevel.eval ψ₁ = 0
      · rw [(pwBit_zeronessOf ψ₁ _).mpr hz, (pwBit_zeronessOf ψ₂ _).mpr (by rw [← hev]; exact hz)]
      · have n1 : pwBit ψ₁ (Level.zeronessOf p.toBlock.elimLevel) ≠ 0 := fun h =>
          hz ((pwBit_zeronessOf ψ₁ _).mp h)
        have n2 : pwBit ψ₂ (Level.zeronessOf p.toBlock.elimLevel) ≠ 0 := fun h =>
          hz (by rw [hev]; exact (pwBit_zeronessOf ψ₂ _).mp h)
        have e1 : pwBit ψ₁ (Level.zeronessOf p.toBlock.elimLevel) = 1 := by
          unfold pwBit
          split
          · next h => exact absurd (by unfold pwBit; rw [if_pos h]) n1
          · rfl
        have e2 : pwBit ψ₂ (Level.zeronessOf p.toBlock.elimLevel) = 1 := by
          unfold pwBit
          split
          · next h => exact absurd (by unfold pwBit; rw [if_pos h]) n2
          · rfl
        rw [e1, e2]
    have hwB : f₀.s.eval ψ₁ = f₀.s.eval ψ₂ :=
      ((hFD 0 f₀ hf0).params ψ₁ ψ₂ (by rw [hlpsF 0 f₀ hf0]; exact hφ)).2
    obtain ⟨hW, hIdss, htlss, hEiss, hFss0, hEss⟩ := hParams ψ₁ ψ₂ hφ
    have hLs : prts.Ls ψ₁ = prts.Ls ψ₂ := by
      show (List.range fms.length).map _ = (List.range fms.length).map _
      refine List.map_congr_left fun q hq => ?_
      have hql : q < fms.length := List.mem_range.mp hq
      refine mp₂.base2.acval_params _ _ (hFPc (hfindF q _ (hfmGet q hql))) ψ₁ ψ₂ ?_
      show ∀ r ∈ (fms.getD q default).cvTa.levelParams, ψ₁ r = ψ₂ r
      rw [hlpsF q _ (hfmGet q hql)]
      exact hφ
    have hpps0 : (ppsF 0 ψ₁).take p.toBlock.nP = (ppsF 0 ψ₂).take p.toBlock.nP := by
      rw [(hppsPar 0 hk0 ψ₁ ψ₂ hφ).1]
    have hipss : prts.ipss ψ₁ = prts.ipss ψ₂ := by
      show (List.range fms.length).map _ = (List.range fms.length).map _
      refine List.map_congr_left fun q hq => ?_
      show (ppsF q ψ₁).drop p.toBlock.nP = (ppsF q ψ₂).drop p.toBlock.nP
      rw [(hppsPar q (List.mem_range.mp hq) ψ₁ ψ₂ hφ).1]
    have hFssR : FssRf ψ₁ = FssRf ψ₂ := by
      show mutFss p.toBlock.nP ctorsA.length dsF ψ₁ = mutFss p.toBlock.nP ctorsA.length dsF ψ₂
      unfold mutFss
      exact List.map_congr_left fun J hJ => by
        rw [hCDparams₁ J (List.mem_range.mp hJ) ψ₁ ψ₂ hφ]
    have hcds : prts.cds ψ₁ = prts.cds ψ₂ := by
      show fixCtorDataList dsF esF (fun J => kindsOf (ksF J)) eissF tssF ψ₁ ctorsA 0
        = fixCtorDataList dsF esF (fun J => kindsOf (ksF J)) eissF tssF ψ₂ ctorsA 0
      refine List.ext_getElem? fun J => ?_
      rw [fixCtorDataList_getElem?, fixCtorDataList_getElem?]
      cases hJ : ctorsA[J]? with
      | none => rfl
      | some cA =>
        have hJl : J < ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
        obtain ⟨hd, he, hei, ht'⟩ := hCDparams J hJl ψ₁ ψ₂ hφ
        have hidJ := hident J cA hJ
        have hesF : esF J ψ₁ = esF J ψ₂ := by
          rw [← hidJ.2.2.2.2.1 ψ₁, ← hidJ.2.2.2.2.1 ψ₂, he]
        have heissF : eissF J ψ₁ = eissF J ψ₂ := by
          rw [← hidJ.2.2.2.2.2.1 ψ₁, ← hidJ.2.2.2.2.2.1 ψ₂, hei]
        have htssF : tssF J ψ₁ = tssF J ψ₂ := by
          rw [← hidJ.2.2.2.2.2.2.1 ψ₁, ← hidJ.2.2.2.2.2.2.1 ψ₂, ht']
        simp only [Nat.zero_add]
        rw [hCDparams₁ J hJl ψ₁ ψ₂ hφ, hesF, heissF, htssF]
    show mutualRecAVI mp₂.base2 ψ₁ (p.toBlock.elimLevel.eval ψ₁) (Wf ψ₁) (f₀.s.eval ψ₁)
        p.toBlock.nP (auxRecSort (Wf ψ₁) (Wf ψ₁) (f₀.s.eval ψ₁) (p.toBlock.elimLevel.eval ψ₁))
        (pwBit ψ₁ (Level.zeronessOf p.toBlock.elimLevel)) p.toBlock.elimLevel (prts.Ls ψ₁)
        prts.nIdxs ((ppsF 0 ψ₁).take p.toBlock.nP) (prts.ipss ψ₁) (Idssf ψ₁) rssf (tlssf ψ₁)
        (Eissf ψ₁) (FssRf ψ₁) (Fss0f ψ₁) (Essf ψ₁) memF (fun J => tgtAt (ksF J))
        (prts.cds ψ₁) t
      = mutualRecAVI mp₂.base2 ψ₂ (p.toBlock.elimLevel.eval ψ₂) (Wf ψ₂) (f₀.s.eval ψ₂)
        p.toBlock.nP (auxRecSort (Wf ψ₂) (Wf ψ₂) (f₀.s.eval ψ₂) (p.toBlock.elimLevel.eval ψ₂))
        (pwBit ψ₂ (Level.zeronessOf p.toBlock.elimLevel)) p.toBlock.elimLevel (prts.Ls ψ₂)
        prts.nIdxs ((ppsF 0 ψ₂).take p.toBlock.nP) (prts.ipss ψ₂) (Idssf ψ₂) rssf (tlssf ψ₂)
        (Eissf ψ₂) (FssRf ψ₂) (Fss0f ψ₂) (Essf ψ₂) memF (fun J => tgtAt (ksF J))
        (prts.cds ψ₂) t
    rw [hev, hW, hwB, hbb, hLs, hpps0, hipss, hIdss, htlss, hEiss, hFssR, hFss0, hEss, hcds]
    refine mutualRecAVI_congrψ hbb hev fun cd hcd => ?_
    -- a constructor's leaf reads only the block's level parameters
    obtain ⟨J, hJ⟩ := List.getElem?_of_mem hcd
    rw [show prts.cds ψ₂ = fixCtorDataList dsF esF (fun J => kindsOf (ksF J)) eissF tssF ψ₂
        ctorsA 0 from rfl, fixCtorDataList_getElem?] at hJ
    obtain ⟨cA, hcA, hcdEq⟩ := Option.map_eq_some_iff.mp hJ
    have hJl : J < ctorsA.length := (List.getElem?_eq_some_iff.mp hcA).1
    have hname : cd.1 = cA.1.name := by rw [← hcdEq]
    rw [hname]
    refine mp₂.base2.acval_params _ _ (hcons₂ J cA hJl hcA).1.1 ψ₁ ψ₂ ?_
    show ∀ r ∈ cA.1.levelParams, ψ₁ r = ψ₂ r
    rw [hlpsC J cA hcA]
    exact hφ
  have htyWF : ∀ t, t < prts.k → (cvRas.getD t default).type.hasFvar = false ∧
      (cvRas.getD t default).type.allLevelParamsDefined
        (cvRas.getD t default).levelParams = true ∧
      (cvRas.getD t default).type.looseBVarsBounded 0 = true := by
    intro t ht
    obtain ⟨recTy, hcv, hlp, -, hbv, hfv, -⟩ := hRecShape t ht
    rw [hcv]
    exact ⟨hfv, hlp, hbv⟩
  -- **the block's rule rows at the group store** (`mutualRecRuleLaw`)
  -- the group store's own extension facts (the recursors are fresh at
  -- the constructors' carrier and pairwise distinct)
  have hfrZ : ∀ x ∈ cvRas.zipIdx,
      (ConLeche.consMutualCtors p.toBlock.nP ctorsA
        (ConLeche.consMutualFormers fms env)).find? x.1.name = none := by
    intro x hx
    have hg := List.mk_mem_zipIdx_iff_getElem?.mp
      (show (x.1, x.2) ∈ cvRas.zipIdx by simpa using hx)
    have hlt : x.2 < prts.k := by
      have := (List.getElem?_eq_some_iff.mp hg).1
      rw [hk] at this
      exact this
    have hd : cvRas.getD x.2 default = x.1 := by
      rw [List.getD_eq_getElem?_getD, hg]; rfl
    rw [← hd]
    exact hfreshR x.2 hlt
  have hndZ : (cvRas.zipIdx.map (·.1.name)).Nodup := by
    have he : cvRas.zipIdx.map (·.1.name) = cvRas.map (·.name) := by
      rw [show (fun (x : ConstantVal × Nat) => x.1.name)
          = (fun cv : ConstantVal => cv.name) ∘ Prod.fst from rfl, ← List.map_map]
      congr 1
      simp
    rw [he]
    exact hnd
  obtain ⟨hFPS, hLGS, hPJS⟩ := storeMutualRecs_extend (b := p.toBlock) (fms := fms)
    (rulesOf := rulesOf) hfrZ hndZ
  have hFPcS : ∀ n : Name,
      ((ConLeche.consMutualFormers fms env).find? n).isSome = true →
      ((ConLeche.consMutualCtors p.toBlock.nP ctorsA
        (ConLeche.consMutualFormers fms env)).find? n).isSome = true := by
    intro n hn
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn
    rw [hFPc hci]; rfl
  have hcbF₂ : ∀ (q : Nat) (f : MutualFormerA), fms[q]? = some f →
      ConstsBound (ConLeche.consMutualCtors p.toBlock.nP ctorsA
        (ConLeche.consMutualFormers fms env)) f.cvTa.type := by
    intro q f hq
    obtain ⟨cv, cv', bs, -, hccv, -, -, -⟩ := hposF q f hq
    obtain ⟨-, -, -, -, -, -, _, _, _, -, -, htr, -, -, hty⟩ := ConLeche.checkConstantVal_inv hccv
    exact constsBound_of_constsResolve _
      (Expr.constsResolve_le hFPcS (hmono₁ _ (by rw [hty]; exact htr)))
  have hcbCC : ∀ (J' : Nat) (cA : ConstantVal × Nat), ctorsA[J']? = some cA →
      ConstsBound (ConLeche.consMutualCtors p.toBlock.nP ctorsA
        (ConLeche.consMutualFormers fms env)) cA.1.type := fun J' cA hJ' =>
    constsBound_of_constsResolve _ (Expr.constsResolve_le hFPcS (hresC J' cA hJ'))
  -- **the auxiliary recursor's premise** (`auxFixPre_of`, `ruleFires_of`'s `hpre`)
  have hpreG : ∀ ψ : Name → Nat, FixPre V (prts.ℓ ψ) (prts.wB ψ) (prts.W ψ) prts.nP
      (prts.FssR ψ) (prts.Ess' ψ) (prts.Fss₀ ψ) (auxIds (prts.W ψ) (prts.Idss ψ)) prts.rss
      (prts.tlss ψ) (prts.Eiss' ψ)
      (auxRecDataAV mp₂.base2 ψ (prts.W ψ) (prts.wB ψ) prts.nP prts.elimL (prts.ppsOf 0 ψ)
        (prts.Idss ψ) prts.rss (prts.tlss ψ) (prts.Eiss' ψ) (prts.Fss₀ ψ) (prts.Ess' ψ)
        prts.mems prts.tgts (prts.cds ψ)) (prts.s ψ) := by
    intro ψ
    have h := auxFixPre_of (V := V) (m := mp₂.base2) (ψ := ψ) rfl rfl
      (pwBit_zeronessOf ψ _).symm (hw0G ψ)
      (auxRecSort_zero_iff _ _ _ _)
      (fun h0 => (auxRecSort_ge _ _ _ _ h0).2.1)
      (fun h0 => (auxRecSort_ge _ _ _ _ h0).2.2.1)
      (fun h0 => (auxRecSort_ge _ _ _ _ h0).2.2.2)
      (hlenP0G ψ) (by rw [auxCtorData_length, fixCtorDataList_length]) mutFss_length
      mutEss'_length
      (fun j hj => by rw [hEssD j _ (hcAGet j hj) ψ]; rfl) (hEisLenG ψ) (hIdsBelow ψ)
      (hslotTagG ψ) (hTbelowG ψ)
      (auxRecDataAV_below (domsBelow_take ((hFD₂ 0 f₀ hf0).below ψ)) (hlenP0G ψ)
        (hIdsBelow ψ) (hchainBelow ψ) (hRawCtor ψ))
      (hclLG ψ) (hppsG ψ) (hfrmG ψ) (hchainsG ψ) (hminorReadG ψ)
    rw [tagIps_doms] at h
    exact h
  have hlawsG : ∀ (acv : Name → (Name → Nat) → AnnotTerm),
      (∀ t, t < prts.k → ∀ ψ : Name → Nat,
        acv (cvRas.getD t default).name ψ = prts.leaf mp₂.base2 t ψ) →
      (∀ n : Name, (∀ t, t < prts.k → n ≠ (cvRas.getD t default).name) →
        acv n = mp₂.base2.acval n) →
      ∀ m₃ : EnvModel V (ConLeche.storeMutualRecs
          (ConLeche.consMutualCtors p.toBlock.nP ctorsA (ConLeche.consMutualFormers fms env))
          p.toBlock fms rulesOf cvRas.zipIdx
          (ConLeche.consMutualCtors p.toBlock.nP ctorsA (ConLeche.consMutualFormers fms env))),
        m₃.acval = acv → ∀ (φ : Name → Nat) (t : Nat), t < prts.k →
        ∀ rl ∈ ConLeche.mutualRules
            (ConLeche.consMutualCtors p.toBlock.nP ctorsA
              (ConLeche.consMutualFormers fms env)).find?
            (cvRas.getD t default).name p.toBlock.nP
            (p.toBlock.rulePrefix + (fms.getD t default).nIdx) p.toBlock.rulePrefix
            (cvRas.getD t default).type (rulesOf.getD t []),
          RecRule.fire rl ≠ .inert →
          RecRuleLaw m₃ φ (cvRas.getD t default).name (cvRas.getD t default)
            (p.toBlock.rulePrefix + (fms.getD t default).nIdx) p.toBlock.rulePrefix rl := by
    intro acv hacvL hacvN m₃ hac φ t ht rl hrl hfire
    -- the stored rule's shape, and the constructor it belongs to
    obtain ⟨cr, hcr, rfl⟩ := mutualRules_getElem? hrl
    obtain ⟨hlenU, hallU⟩ := ConLeche.checkMutualAllRules_inv hrules
    obtain ⟨rules, hrget, hrun⟩ := hallU t (by rw [hkF]; exact ht)
    have hrD : rulesOf.getD t [] = rules := by
      rw [List.getD_eq_getElem?_getD, hrget]; rfl
    rw [hrD] at hcr
    obtain ⟨-, hlenR, hallR⟩ := ConLeche.checkMutualMemberRules_inv hrun
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hcr
    obtain ⟨J, c, rhs, hown, hget, hgen, -, -, -, -⟩ :=
      hallR i (by rw [← hlenR]; exact (List.getElem?_eq_some_iff.mp hi).1)
    obtain rfl : cr = (c, rhs) := Option.some.inj (hi.symm.trans hget)
    -- `J` is a block position, `c` is its constructor, and it is member `t`'s
    have hownMem := List.mem_filter.mp (List.mem_of_getElem? hown)
    obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hownMem.1
    obtain ⟨hxc, hxJ⟩ : x.1 = c ∧ x.2 = J := by
      constructor
      · have := congrArg Prod.snd hxe; simpa using this
      · have := congrArg Prod.fst hxe; simpa using this
    have hxget : p.toBlock.ctors[J]? = some c := by
      have h := List.mk_mem_zipIdx_iff_getElem?.mp
        (show (x.1, x.2) ∈ p.toBlock.ctors.zipIdx by simpa using hx)
      rw [hxc, hxJ] at h
      exact h
    have hJl : J < ctorsA.length := by
      rw [hlenA]
      exact (List.getElem?_eq_some_iff.mp hxget).1
    have hcJ : p.toBlock.ctors.getD J default = c := by
      rw [List.getD_eq_getElem?_getD, hxget]; rfl
    have hmemJ : memF J = t := by
      show (p.toBlock.ctors.getD J default).member = t
      rw [hcJ]
      have := hownMem.2
      simpa using this
    have hcA := hcAGet J hJl
    have hnm : (ctorsA.getD J default).1.name = c.cv.name := by
      have h1 := congrArg (fun l => l[J]?) hnamesC
      rw [List.getElem?_map, List.getElem?_map, hcA, hxget] at h1
      simpa using h1
    have hnF : (ctorsA.getD J default).2 = c.nF := by
      have h := (hrunC J _ hcA).1
      rw [h, hcJ]
    -- the rule fires (`recRulePlain`); otherwise `hfire` is refuted
    by_cases hplain : Expr.recRulePlain (cvRas.getD t default).type
        (p.toBlock.rulePrefix + (fms.getD t default).nIdx) p.toBlock.rulePrefix p.toBlock.nP = true
    case neg =>
      refine absurd ?_ hfire
      show RecRule.fire (ConLeche.recRuleBits _ _ _) = RecRuleFire.inert
      simp only [ConLeche.recRuleBits]
      exact if_neg hplain
    -- the store's transfer
    have hagAcv : ∀ n, ((ConLeche.consMutualCtors p.toBlock.nP ctorsA
        (ConLeche.consMutualFormers fms env)).find? n).isSome = true →
        mp₂.base2.acval n = acv n := by
      intro n hn
      refine (hacvN n fun q hq hh => ?_).symm
      rw [hh, hfreshR q hq] at hn
      exact nomatch hn
    have hFindS : ∀ {n : Name} {ci : ConstantInfo},
        (ConLeche.consMutualCtors p.toBlock.nP ctorsA
          (ConLeche.consMutualFormers fms env)).find? n = some ci →
        (ConLeche.storeMutualRecs
          (ConLeche.consMutualCtors p.toBlock.nP ctorsA (ConLeche.consMutualFormers fms env))
          p.toBlock fms rulesOf cvRas.zipIdx
          (ConLeche.consMutualCtors p.toBlock.nP ctorsA
            (ConLeche.consMutualFormers fms env))).find? n = some ci :=
      (storeMutualRecs_extend hfrZ hndZ).1
    -- the block data at `J`
    have hlpsCJ : (ctorsA.getD J default).1.levelParams = p.toBlock.lps := hlpsC J _ hcA
    have hlenDsJ : ∀ ψ : Name → Nat, (dsF J ψ).length = p.toBlock.nP + c.nF := by
      intro ψ; rw [(hCD₁ J _ hcA).len ψ, hnF]
    have hlenEsJ : ∀ ψ : Name → Nat, (esF J ψ).length = prts.nIdxOf t := by
      intro ψ
      show (esF J ψ).length = (fms.getD t default).nIdx
      rw [← hmemJ]
      exact (hCD₁ J _ hcA).lenE ψ
    have hcdJ : ∀ ψ : Name → Nat, (prts.cds ψ)[J]? = some (c.cv.name, c.nF, dsF J ψ, esF J ψ,
        ConLeche.recIdxOf (kindsOf (ksF J)), eissF J ψ, tssF J ψ) := by
      intro ψ
      show (fixCtorDataList dsF esF (fun J => kindsOf (ksF J)) eissF tssF ψ ctorsA 0)[J]? = _
      rw [fixCtorDataList_getElem?, hcA]
      simp only [Option.map_some, Nat.zero_add]
      rw [hnm, hnF]
    have hfC : (ConLeche.storeMutualRecs
        (ConLeche.consMutualCtors p.toBlock.nP ctorsA (ConLeche.consMutualFormers fms env))
        p.toBlock fms rulesOf cvRas.zipIdx
        (ConLeche.consMutualCtors p.toBlock.nP ctorsA
          (ConLeche.consMutualFormers fms env))).find? c.cv.name
        = some (.ctorInfo (ctorsA.getD J default).1 p.toBlock.nP c.nF) := by
      rw [← hnm, ← hnF]
      exact hFindS (hcons₂ J _ hJl hcA).1.1
    have hdataParams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ p.toBlock.lps, ψ₁ q = ψ₂ q) →
        ((c.cv.name, c.nF, dsF J ψ₁, esF J ψ₁, ConLeche.recIdxOf (kindsOf (ksF J)),
            eissF J ψ₁, tssF J ψ₁) : CtorDatumR)
          = (c.cv.name, c.nF, dsF J ψ₂, esF J ψ₂, ConLeche.recIdxOf (kindsOf (ksF J)),
            eissF J ψ₂, tssF J ψ₂) ∧
        prts.FssR ψ₁ = prts.FssR ψ₂ ∧ prts.wB ψ₁ = prts.wB ψ₂ := by
      intro ψ₁ ψ₂ hφ
      obtain ⟨-, he, hei, ht'⟩ := hCDparams J hJl ψ₁ ψ₂ hφ
      have hidJ := hident J _ hcA
      have hesF : esF J ψ₁ = esF J ψ₂ := by
        rw [← hidJ.2.2.2.2.1 ψ₁, ← hidJ.2.2.2.2.1 ψ₂, he]
      have heissF : eissF J ψ₁ = eissF J ψ₂ := by
        rw [← hidJ.2.2.2.2.2.1 ψ₁, ← hidJ.2.2.2.2.2.1 ψ₂, hei]
      have htssF : tssF J ψ₁ = tssF J ψ₂ := by
        rw [← hidJ.2.2.2.2.2.2.1 ψ₁, ← hidJ.2.2.2.2.2.2.1 ψ₂, ht']
      refine ⟨by rw [hCDparams₁ J hJl ψ₁ ψ₂ hφ, hesF, heissF, htssF], ?_, ?_⟩
      · show mutFss p.toBlock.nP ctorsA.length dsF ψ₁ = mutFss p.toBlock.nP ctorsA.length dsF ψ₂
        unfold mutFss
        exact List.map_congr_left fun J' hJ' => by
          rw [hCDparams₁ J' (List.mem_range.mp hJ') ψ₁ ψ₂ hφ]
      · exact ((hFD 0 f₀ hf0).params ψ₁ ψ₂ (by rw [hlpsF 0 f₀ hf0]; exact hφ)).2
    have hcbRec : ConstsBound (ConLeche.consMutualCtors p.toBlock.nP ctorsA
        (ConLeche.consMutualFormers fms env)) (cvRas.getD t default).type :=
      constsBound_of_constsResolve _ (hresR t ht)
    have hRD : MutualRecData m₃ (cvRas.getD t default) prts.nP prts.k prts.n (prts.nIdxOf t) t
        prts.elimL (prts.rds mp₂.base2 t) :=
      { read := fun ψ => by
          rw [hac]
          exact denoteMeta_toStore hfrZ hndZ hagAcv ψ 0 _ hcbRec ((hRDs t ht).read ψ)
        len := (hRDs t ht).len
        bits := (hRDs t ht).bits
        okTy := (hRDs t ht).okTy
        below := (hRDs t ht).below
        params := (hRDs t ht).params }
    obtain ⟨-, hGS, hPS⟩ := storeMutualRecs_extend (b := p.toBlock) (fms := fms)
      (rulesOf := rulesOf) hfrZ hndZ
    have hagS : ∀ n : Name, ((ConLeche.consMutualCtors p.toBlock.nP ctorsA
        (ConLeche.consMutualFormers fms env)).find? n).isSome = true →
        mp₂.base2.acval n = m₃.acval n := by
      intro n hn; rw [hac]; exact hagAcv n hn
    have hFPcS : ∀ n : Name,
        ((ConLeche.consMutualFormers fms env).find? n).isSome = true →
        ((ConLeche.consMutualCtors p.toBlock.nP ctorsA
          (ConLeche.consMutualFormers fms env)).find? n).isSome = true := by
      intro n hn
      obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn
      rw [hFPc hci]; rfl
    -- the members' names are not the recursors'
    have hmemNe : ∀ (q : Nat) (f : MutualFormerA), fms[q]? = some f →
        ∀ r, r < prts.k → f.cvTa.name ≠ (cvRas.getD r default).name := by
      intro q f hq r hr hh
      have h1 := hFPc (hfindF q f hq)
      rw [hh, hfreshR r hr] at h1
      exact nomatch h1
    -- **the readings at the store**
    have hFReadsS : ∀ ψ : Name → Nat, FormerReadsM m₃ ψ p.toBlock.lps p.toBlock.nP
        (fun q => mp₂.base2.acval (fms.getD q default).cvTa.name ψ)
        (fun q => (fms.getD q default).nIdx)
        (fun q => (ppsF q ψ).take p.toBlock.nP) (fun q => (ppsF q ψ).drop p.toBlock.nP)
        formers4 := by
      intro ψ q hq
      have hql : q < fms.length := by rw [← hlen4F]; exact hq
      refine (hFReads ψ q hq).crossEnv ?_ hFindS hGS hPS hagS
      show ConstsBound _ (formers4.getD q default).tty
      rw [hget4F q hql]
      exact hcbF₂ q _ (hfmGet q hql)
    have hCReadsS : ∀ ψ : Name → Nat, MutualCtorReadsM m₃ ψ p.toBlock.lps p.toBlock.nP
        (fun q => (fms.getD q f₀).cvTa.name) (fun q => (fms.getD q default).nIdx) memF
        (fun J' => tgtAt (ksF J')) ctors4
        (fixCtorDataList dsF esF (fun J' => kindsOf (ksF J')) eissF tssF ψ ctorsA 0) := by
      intro ψ
      refine ⟨(hCReads ψ).1, fun J' hJ' => ?_⟩
      have hJ'l : J' < ctorsA.length := by rw [← hlen4C]; exact hJ'
      have hbase := (hCReads ψ).2 J' hJ'
      refine ⟨hbase.member, hbase.fields, hbase.base.crossEnv ?_ hFindS hGS hPS hagS ?_ ?_⟩
      · show ConstsBound _ (ctors4.getD J' default).cty
        rw [show ctors4.getD J' default = MutualCtor4.mk (ctorsA.getD J' default).1.name
            (ctorsA.getD J' default).2 (ctorsA.getD J' default).1.type
            (p.toBlock.ctors.getD J' default).member
            (ConLeche.mutualRecFieldsOf (kinds.getD J' [])) from by
          rw [List.getD_eq_getElem?_getD, hget4C J' _ (hcAGet J' hJ'l)]; rfl]
        exact hcbCC J' _ (hcAGet J' hJ'l)
      · rw [hgetDf₀ _ (hmotLt J' hJ'l)]
        exact congrFun
          (hagS _ (by rw [hFPc (hfindF _ _ (hfmGet _ (hmotLt J' hJ'l)))]; rfl)) ψ
      · intro i _
        rw [hgetDf₀ _ ((hksJ J' _ (hcAGet J' hJ'l)).2.2 i)]
        exact congrFun (hagS _ (by
          rw [hFPc (hfindF _ _ (hfmGet _ ((hksJ J' _ (hcAGet J' hJ'l)).2.2 i)))]; rfl)) ψ
    -- **the recursors' table**, total below `k` (`denoteMeta_mutualRecRhs`
    -- asks for its `recOf` at EVERY index)
    have hrecName : ∀ q, q < prts.k → (cvRas.getD q default).name = p.toBlock.recName q := by
      intro q hq
      obtain ⟨recTy, hcv, -, -, -, -, -⟩ := hRecShape q hq
      rw [hcv]
    have hfRS : ∀ q : Nat, ∃ ci : ConstantInfo,
        (ConLeche.storeMutualRecs
          (ConLeche.consMutualCtors p.toBlock.nP ctorsA (ConLeche.consMutualFormers fms env))
          p.toBlock fms rulesOf cvRas.zipIdx
          (ConLeche.consMutualCtors p.toBlock.nP ctorsA
            (ConLeche.consMutualFormers fms env))).find?
          (if q < prts.k then p.toBlock.recName q else p.toBlock.recName 0) = some ci ∧
        ci.toConstantVal.levelParams = p.toBlock.rlps := by
      have hone : ∀ r, r < prts.k → ∃ ci : ConstantInfo,
          (ConLeche.storeMutualRecs
            (ConLeche.consMutualCtors p.toBlock.nP ctorsA (ConLeche.consMutualFormers fms env))
            p.toBlock fms rulesOf cvRas.zipIdx
            (ConLeche.consMutualCtors p.toBlock.nP ctorsA
              (ConLeche.consMutualFormers fms env))).find? (p.toBlock.recName r) = some ci ∧
          ci.toConstantVal.levelParams = p.toBlock.rlps := by
        intro r hr
        obtain ⟨recTy, hcv, -, -, -, -, -⟩ := hRecShape r hr
        have hmem : (cvRas.getD r default, r) ∈ cvRas.zipIdx :=
          List.mk_mem_zipIdx_iff_getElem?.mpr (by
            rw [List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (show r < cvRas.length by rw [hk]; exact hr)]
            rfl)
        refine ⟨.recInfo (cvRas.getD r default)
            (p.toBlock.rulePrefix + (fms.getD r default).nIdx) p.toBlock.rulePrefix
            (ConLeche.mutualRules (ConLeche.consMutualCtors p.toBlock.nP ctorsA
              (ConLeche.consMutualFormers fms env)).find? (cvRas.getD r default).name
              p.toBlock.nP (p.toBlock.rulePrefix + (fms.getD r default).nIdx)
              p.toBlock.rulePrefix (cvRas.getD r default).type (rulesOf.getD r [])), ?_, ?_⟩
        · rw [← hrecName r hr]
          exact storeMutualRecs_find?_self hmem hndZ
        · show (cvRas.getD r default).levelParams = p.toBlock.rlps
          rw [hcv]
      intro q
      by_cases hq : q < prts.k
      · rw [if_pos hq]; exact hone q hq
      · rw [if_neg hq]; exact hone 0 hk0
    have hfTS : ∀ q : Nat, ∃ ci : ConstantInfo,
        (ConLeche.storeMutualRecs
          (ConLeche.consMutualCtors p.toBlock.nP ctorsA (ConLeche.consMutualFormers fms env))
          p.toBlock fms rulesOf cvRas.zipIdx
          (ConLeche.consMutualCtors p.toBlock.nP ctorsA
            (ConLeche.consMutualFormers fms env))).find? (fms.getD q f₀).cvTa.name = some ci ∧
        ci.toConstantVal.levelParams = p.toBlock.lps := by
      intro q
      obtain ⟨ci, hci, hlp⟩ := hfTname q
      exact ⟨ci, hFindS hci, hlp⟩
    have hgen' : ConLeche.mutualRecRhs p.toBlock.lps p.toBlock.elim p.toBlock.large p.toBlock.nP
        formers4 ctors4 (fun q => if q < prts.k then p.toBlock.recName q else p.toBlock.recName 0)
        (p.toBlock.rlps.map Level.param) J = some rhs := by
      rw [← hgen]
      refine mutualRecRhs_congr_recOf fun c' hc' im him => ?_
      obtain ⟨J'', hJ''⟩ := List.getElem?_of_mem hc'
      have hJ''l : J'' < ctorsA.length := by
        rw [← hlen4C]
        exact (List.getElem?_eq_some_iff.mp hJ'').1
      have hfields := ((hCReads (fun _ => 0)).2 J'' (by rw [hlen4C]; exact hJ''l)).fields
      rw [show ctors4.getD J'' default = c' from by
        rw [List.getD_eq_getElem?_getD, hJ'']; rfl] at hfields
      rw [hfields] at him
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp him
      exact if_pos ((hksJ J'' _ (hcAGet J'' hJ''l)).2.2 i)
    -- the constructors' leaves do not move at the store
    have hacvCds : ∀ ψ : Name → Nat, ∀ cd ∈ fixCtorDataList dsF esF
        (fun J' => kindsOf (ksF J')) eissF tssF ψ ctorsA 0,
        m₃.acval cd.1 ψ = mp₂.base2.acval cd.1 ψ := by
      intro ψ cd hcd
      obtain ⟨J', hJ'⟩ := List.getElem?_of_mem hcd
      rw [fixCtorDataList_getElem?] at hJ'
      obtain ⟨cA', hcA', hcdEq⟩ := Option.map_eq_some_iff.mp hJ'
      have hJ'l : J' < ctorsA.length := (List.getElem?_eq_some_iff.mp hcA').1
      have hname : cd.1 = cA'.1.name := by rw [← hcdEq]
      have hne : ∀ r, r < prts.k → cA'.1.name ≠ (cvRas.getD r default).name := by
        intro r hr hh
        have h1 := (hcons₂ J' cA' hJ'l hcA').1.1
        rw [hh, hfreshR r hr] at h1
        exact absurd h1 (by simp)
      rw [hname, hac, hacvN _ hne]
    -- **the rule's right-hand side, read at the store**
    have hread : ∀ ψ : Name → Nat,
        denoteMeta m₃.acval (ConLeche.storeMutualRecs
          (ConLeche.consMutualCtors p.toBlock.nP ctorsA (ConLeche.consMutualFormers fms env))
          p.toBlock fms rulesOf cvRas.zipIdx
          (ConLeche.consMutualCtors p.toBlock.nP ctorsA
            (ConLeche.consMutualFormers fms env))) ψ 0 rhs
        = some (prts.ruleAV mp₂.base2 J
            ((c.cv.name, c.nF, dsF J ψ, esF J ψ, ConLeche.recIdxOf (kindsOf (ksF J)),
              eissF J ψ, tssF J ψ) : CtorDatumR) ψ) := by
      intro ψ
      have hside : ∀ i ∈ ConLeche.recIdxOf (kindsOf (ksF J)),
          m₃.acval (if tgtAt (ksF J) i < prts.k then p.toBlock.recName (tgtAt (ksF J) i)
              else p.toBlock.recName 0) ψ
            = prts.leaf mp₂.base2 (tgtAt (ksF J) i) ψ := by
        intro i _
        have htgtk : tgtAt (ksF J) i < prts.k := (hksJ J _ hcA).2.2 i
        rw [if_pos htgtk, ← hrecName _ htgtk, hac]
        exact hacvL _ htgtk ψ
      rw [denoteMeta_mutualRecRhs (hFReadsS ψ) (hCReadsS ψ) hmots4 hfTS hfRS hgen' (hcdJ ψ),
        hlen4F, hlen4C, mutualRuleDataAV_congrm (hacvCds ψ),
        mutualRuleCoreAV_congr_Rof
          (Rof := fun t => m₃.acval
            (if t < prts.k then p.toBlock.recName t else p.toBlock.recName 0) ψ)
          (Rof' := fun q => prts.leaf mp₂.base2 q ψ)
          (tgts := tgtAt (ksF J)) (recIdx := ConLeche.recIdxOf (kindsOf (ksF J))) hside]
      rfl
    -- **the rule's right-hand side is graded** (`mutualRuleOk`)
    have hRuleOk : ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenotedV V ρ
        (prts.ruleAV mp₂.base2 J ((c.cv.name, c.nF, dsF J ψ, esF J ψ,
          ConLeche.recIdxOf (kindsOf (ksF J)), eissF J ψ, tssF J ψ) : CtorDatumR) ψ) := by
      intro ψ ρ
      -- the leaf table, total below `k`
      have hlt : ∀ q : Nat, (if q < prts.k then q else 0) < prts.k := by
        intro q
        by_cases h : q < prts.k
        · rw [if_pos h]; exact h
        · rw [if_neg h]; exact hk0
      have hRcl : ∀ q : Nat, Term.bvarsBelow 0
          (prts.leaf mp₂.base2 (if q < prts.k then q else 0) ψ).erase := fun q =>
        prts.leaf_below hyp (hlt q) ψ ((hRDs' _ (hlt q)).below ψ) ((hRDs' _ (hlt q)).len ψ)
          (hIdsBelow ψ) (hchainBelow ψ)
      have hRok : ∀ (q : Nat) (σ : Nat → V),
          WellDenotedV V σ (prts.leaf mp₂.base2 (if q < prts.k then q else 0) ψ) := fun q σ =>
        (prts.leaf_facts hyp (hlt q) ψ σ).1
      have hRmem : ∀ q, q < prts.k → ∀ σ : Nat → V,
          interp V σ (prts.leaf mp₂.base2 (if q < prts.k then q else 0) ψ) ∈ˢ interp V σ
            (mkPisAV (mutualRecDataAV mp₂.base2 ψ (prts.Ls ψ) prts.nP prts.nIdxs prts.elimL
              (prts.ppsOf 0 ψ) (prts.ipss ψ) (prts.cds ψ) prts.mems prts.tgts q)
              (mutualConcAV prts.k prts.n (prts.nIdxs.getD q 0) q)) := by
        intro q hq σ
        rw [if_pos hq, prts.nIdxs_getD hq]
        exact (prts.leaf_facts hyp hq ψ σ).2
      -- a recursive slot's telescope (`SlotTagOk`'s untagged half)
      have hslots : ∀ ρp : Nat → V,
          Sat V (((prts.ppsOf 0 ψ).map (·.2.2)).reverse) ρp →
          ∀ (q : Nat) (cdq : CtorDatumR), (prts.cds ψ)[q]? = some cdq →
          ∀ fs : List V, SpineFit ρp ((cdq.2.2.1.drop prts.nP).map (·.2.2)) fs →
          ∀ i ∈ recIdx (prts.rss.getD q []) cdq.2.1,
            FieldsOkB (prts.wB ψ) (consList (fs.take i) ρp)
              ((((prts.tlss ψ).getD q []).getD i []).map (·.2.2)) ∧
            FieldsValid (consList (fs.take i) ρp)
              ((((prts.tlss ψ).getD q []).getD i []).map (·.2.2)) ∧
            ∀ bs : List V, SpineFit (consList (fs.take i) ρp)
              ((((prts.tlss ψ).getD q []).getD i []).map (·.2.2)) bs →
              AppChainOk (fs.getD i pt) bs := by
        intro ρp hsatP q cdq hq fs hfs i hi
        have hst := hSlotTagG ψ ρp hsatP q cdq hq fs hfs i hi
        obtain ⟨tgt, Es, -, hrest⟩ := hst.2.2
        exact ⟨hst.1, hst.2.1, fun bs hbs => (hrest bs hbs).2.2.1⟩
      -- the constructor's index readings, and its slots', at the target
      have hmemJk : prts.mems J < prts.k := by
        show memF J < fms.length
        rw [hmemJ]; exact ht
      have hEsLenJ : (esF J ψ).length = prts.nIdxs.getD (prts.mems J) 0 := by
        rw [prts.nIdxs_getD hmemJk,
          show prts.nIdxOf (prts.mems J) = prts.nIdxOf t from by
            show (fms.getD (memF J) default).nIdx = (fms.getD t default).nIdx
            rw [hmemJ]]
        exact hlenEsJ ψ
      have hEisLenJ : ∀ i ∈ recIdx (prts.rss.getD J []) c.nF,
          (((prts.EissO ψ).getD J []).getD i []).length
            = prts.nIdxs.getD (prts.tgts J i) 0 := by
        intro i hi
        have htgt : tgtAt (ksF J) i < fms.length := (hksJ J _ hcA).2.2 i
        have htG := hfmGet _ htgt
        have hksLen : (kindsOf (ksF J)).length = (ctorsA.getD J default).2 := by
          rw [kindsOf_length]; exact (hksJ J _ hcA).1
        have hi' : i ∈ recIdx (rssf.getD J []) (ctorsA.getD J default).2 := by
          rw [hnF]; exact hi
        have hmemI := mem_recIdx.mp hi'
        have hilt : i < (ctorsA.getD J default).2 := hmemI.1
        have hrb : (rsOf (kindsOf (ksF J))).getD i false = true := by
          rw [← mutRss_getD (n := ctorsA.length) (ksF := ksF) hJl]
          exact hmemI.2
        have hkind : kindAt (ksF J) i = .recursive ∨ kindAt (ksF J) i = .reflexive := by
          have h := (rsOf_getD_iff (by rw [hksLen]; exact hilt)).mp hrb
          rwa [kindsOf_getD (by rw [(hksJ J _ hcA).1]; exact hilt)] at h
        rw [prts.nIdxs_getD htgt,
          show ((prts.EissO ψ).getD J []).getD i [] = (eissF J ψ).getD i [] from by
            show ((mutEiss0 ctorsA.length eissF ψ).getD J []).getD i [] = _
            rw [mutEiss0_getD hJl]]
        show ((eissF J ψ).getD i []).length = (fms.getD (tgtAt (ksF J) i) default).nIdx
        rw [← (hmemT _ _ htG).2]
        rcases hkind with hk | hk
        · exact (hCD₁ J _ hcA).eisLen ψ i hk hilt
        · exact (hCD₁ J _ hcA).eisLenRefl ψ i hk hilt
      show WellDenotedV V ρ (mkLamsAV (mutualRuleDataAV mp₂.base2 ψ (prts.Ls ψ) prts.nP
          prts.nIdxs prts.elimL (prts.ppsOf 0 ψ) (prts.ipss ψ) (prts.cds ψ) prts.mems prts.tgts
          (dsF J ψ))
        (mutualRuleCoreAV (prts.bb ψ) (fun q => prts.leaf mp₂.base2 q ψ) (prts.tgts J) prts.nP
          prts.k prts.n c.nF J (ConLeche.recIdxOf (kindsOf (ksF J))) (tssF J ψ) (eissF J ψ)))
      rw [mutualRuleCoreAV_congr_Rof (Rof := fun q => prts.leaf mp₂.base2 q ψ)
        (Rof' := fun q => prts.leaf mp₂.base2 (if q < prts.k then q else 0) ψ)
        (tgts := prts.tgts J) (recIdx := ConLeche.recIdxOf (kindsOf (ksF J)))
        (fun i _ => by rw [if_pos ((hksJ J _ hcA).2.2 i)])]
      exact mutualRuleOk_of ht (fun q hq => hyp q hq ψ)
        (fun ρp hsatP => (hvFssG ψ ρp hsatP).1) hslots (hcdJ ψ) hEsLenJ hEisLenJ
        hRcl hRok hRmem ρ
    -- **the rule fires** (`ruleFires_of`)
    have hrPG : p.toBlock.rulePrefix = prts.nP + prts.k + prts.n := by
      show p.toBlock.nP + p.toBlock.k + p.toBlock.n = p.toBlock.nP + fms.length + ctorsA.length
      rw [hkF, hlenA]
      rfl
    have hfires : prts.RuleFires V mp₂.base2 t J
        (p.toBlock.rulePrefix + (fms.getD t default).nIdx) p.toBlock.rulePrefix
        (fun ψ => ((c.cv.name, c.nF, dsF J ψ, esF J ψ, ConLeche.recIdxOf (kindsOf (ksF J)),
          eissF J ψ, tssF J ψ) : CtorDatumR)) :=
      ruleFires_of prts hyp ht (by rw [hrPG]) hrPG hcdJ (fun ψ => (hRDs' t ht).len ψ)
        (fun ψ d hd => (hRDs' t ht).bits ψ d hd) hRuleOk
        (fun ψ ρ => (prts.leaf_facts hyp ht ψ ρ).2)
        (fun q hq ψ => prts.leaf_below hyp hq ψ ((hRDs' q hq).below ψ) ((hRDs' q hq).len ψ)
          (hIdsBelow ψ) (hchainBelow ψ))
        hw0G hpreG
    -- **the rule's law** (`mutualRecRuleLaw`)
    have hruleE : ConLeche.recRuleBits (ConLeche.consMutualCtors p.toBlock.nP ctorsA
          (ConLeche.consMutualFormers fms env)).find? (cvRas.getD t default).name
        { ctor := c.cv.name, nfields := c.nF, ctorParams := p.toBlock.nP,
          fire := if Expr.recRulePlain (cvRas.getD t default).type
              (p.toBlock.rulePrefix + (fms.getD t default).nIdx) p.toBlock.rulePrefix
              p.toBlock.nP then .plain else .inert,
          rhs := rhs, paramsBlind := true }
        = { ctor := c.cv.name, nfields := c.nF, ctorParams := prts.nP, fire := .plain,
            rhs := rhs,
            k := ConLeche.recRuleKOf (ConLeche.consMutualCtors p.toBlock.nP ctorsA
              (ConLeche.consMutualFormers fms env)).find? c.cv.name,
            eta := ConLeche.recRuleEtaOf (ConLeche.consMutualCtors p.toBlock.nP ctorsA
              (ConLeche.consMutualFormers fms env)).find? (cvRas.getD t default).name c.cv.name,
            paramsBlind := true } := by
      rw [if_pos hplain]
      rfl
    refine mutualRecRuleLaw prts m₃ (m₀ := mp₂.base2) (t := t) (J := J)
      (Tname := (fms.getD (memF J) f₀).cvTa.name)
      (by rw [hrPG]) hrPG hruleE hcdJ hlenDsJ (fun ψ => rfl) hlenEsJ hlpsCJ hfC
      (fun ψ => by rw [hac]; exact hacvL t ht ψ) ?_ hdataParams hRD ?_ hread hRuleOk hfires φ
    · -- the constructor's leaf does not move at the store
      intro ψ
      rw [hacvCds ψ _ (List.mem_of_getElem? (hcdJ ψ))]
      exact ((hyp t ht ψ).hcd J _ (hcdJ ψ)).2.2.1
    · -- the constructor's type, read at the store
      intro ψ
      have hcr := ((hCReadsS ψ).2 J (by rw [hlen4C]; exact hJl)).base.read
      have hc4 : ctors4.getD J default = MutualCtor4.mk c.cv.name c.nF
          (ctorsA.getD J default).1.type (p.toBlock.ctors.getD J default).member
          (ConLeche.mutualRecFieldsOf (kinds.getD J [])) := by
        rw [List.getD_eq_getElem?_getD, hget4C J _ hcA, ← hnm, ← hnF]
        rfl
      rw [hc4, show (fixCtorDataList dsF esF (fun J' => kindsOf (ksF J')) eissF tssF ψ ctorsA 0).getD J
            default = ((c.cv.name, c.nF, dsF J ψ, esF J ψ,
              ConLeche.recIdxOf (kindsOf (ksF J)), eissF J ψ, tssF J ψ) : CtorDatumR) from by
        rw [List.getD_eq_getElem?_getD, hcdJ ψ]; rfl] at hcr
      exact hcr

  obtain ⟨mp₄, hacc₄, hoff₄⟩ := stageMutualRecs prts hyp mp₂ hrectys hrules hk hnd hfreshR
    hresR hE₂ hRDs' hIdsBelow hchainBelow hAparams hnres hpshape htyWF
    (hreps fms cvRas rulesOf _ mp₂ prts _ mp₂.base2 hyp hk rfl hnCtors).1
    (by
      -- **`hctorStored`**: a stored rule's constructor is one of the
      -- member's own, hence a constructor of the block, hence stored
      intro t ht r hr
      obtain ⟨cr, hcr, rfl⟩ := mutualRules_getElem? hr
      obtain ⟨hlenU, hallU⟩ := ConLeche.checkMutualAllRules_inv hrules
      obtain ⟨rules, hrget, hrun⟩ := hallU t (by rw [hkF]; exact ht)
      have hrD : rulesOf.getD t [] = rules := by
        rw [List.getD_eq_getElem?_getD, hrget]; rfl
      rw [hrD] at hcr
      obtain ⟨-, hlenR, hallR⟩ := ConLeche.checkMutualMemberRules_inv hrun
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hcr
      obtain ⟨J, c, rhs, hown, hget, -, -, -, -, -⟩ :=
        hallR i (by rw [← hlenR]; exact (List.getElem?_eq_some_iff.mp hi).1)
      obtain rfl : cr = (c, rhs) := Option.some.inj (hi.symm.trans hget)
      -- the member's own constructor is one of the block's
      have hmemC : c ∈ p.toBlock.ctors := by
        have h := List.mem_of_getElem? hown
        have h2 := List.mem_filter.mp h
        obtain ⟨x, hx, hxe⟩ := List.mem_map.mp h2.1
        obtain rfl : x.1 = c := by
          have := congrArg Prod.snd hxe
          simpa using this
        have hx' := List.mk_mem_zipIdx_iff_getElem?.mp (by
          show (x.1, x.2) ∈ p.toBlock.ctors.zipIdx
          simpa using hx)
        exact List.mem_of_getElem? hx'
      -- and every block constructor is stored
      obtain ⟨J', hJ'⟩ : ∃ J', ctorsA[J']? = some (ctorsA.getD J' default) ∧
          (ctorsA.getD J' default).1.name = c.cv.name := by
        obtain ⟨J', hJ'⟩ := List.getElem?_of_mem
          (show c.cv.name ∈ p.toBlock.ctors.map (·.cv.name) from List.mem_map_of_mem hmemC)
        rw [← hnamesC, List.getElem?_map] at hJ'
        obtain ⟨cA, hcA, hnm⟩ := Option.map_eq_some_iff.mp hJ'
        refine ⟨J', hcAGet J' (List.getElem?_eq_some_iff.mp hcA).1, ?_⟩
        rw [show ctorsA.getD J' default = cA from by
          rw [List.getD_eq_getElem?_getD, hcA]; rfl]
        exact hnm
      have hJl' : J' < ctorsA.length := (List.getElem?_eq_some_iff.mp hJ'.1).1
      refine ⟨(ctorsA.getD J' default).1, p.toBlock.nP, (ctorsA.getD J' default).2, ?_⟩
      show _ = _
      rw [ConLeche.recRuleBits_ctor, ← hJ'.2]
      exact (hcons₂ J' _ hJl' hJ'.1).1.1)
    hlawsG
    (hreps fms cvRas rulesOf _ mp₂ prts _ mp₂.base2 hyp hk rfl hnCtors).2
  -- the carrier does not move at the group store, off the recursors
  have hagS4 : ∀ n : Name, ((ConLeche.consMutualCtors p.toBlock.nP ctorsA
      (ConLeche.consMutualFormers fms env)).find? n).isSome = true →
      mp₂.base2.acval n = mp₄.base2.acval n := by
    intro n hn
    refine (hoff₄ n fun q hq hh => ?_).symm
    rw [hh, hfreshR q hq] at hn
    exact nomatch hn
  -- **the members' `.proj` bookkeeping**: the member is not stored
  -- before the block, so nothing stored there mentions its
  -- projections; the block's own pieces are read (the members' and
  -- constructors' types) or GENERATED from them (the recursors and
  -- their rules) at an environment where the member's slot is empty
  have hnpG : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f → ∀ j : Nat,
      NoProjEnv (ConLeche.storeMutualRecs
        (ConLeche.consMutualCtors p.toBlock.nP ctorsA (ConLeche.consMutualFormers fms env))
        p.toBlock fms rulesOf cvRas.zipIdx
        (ConLeche.consMutualCtors p.toBlock.nP ctorsA
          (ConLeche.consMutualFormers fms env))) f.cvTa.name j := by
    intro t f hft j
    have h0 : NoProjEnv env f.cvTa.name j :=
      noProjEnv_of_fresh mp.base2.wf (hfreshF t f hft) j
    have hnpT : ∀ f' ∈ fms, Expr.NoProjAt f.cvTa.name j f'.cvTa.type := by
      intro f' hf'
      obtain ⟨t', hft'⟩ := List.getElem?_of_mem hf'
      obtain ⟨cv, cv', bs, -, hccv, -, -, -⟩ := hposF t' f' hft'
      obtain ⟨-, -, -, -, -, -, _, _, _, -, -, htr, -, -, hty⟩ :=
        ConLeche.checkConstantVal_inv hccv
      exact ConLeche.Expr.noProjAt_of_constsResolve (hfreshF t f hft) _ (by rw [hty]; exact htr)
    have h1 : NoProjEnv (ConLeche.consMutualFormers fms env) f.cvTa.name j :=
      noProjEnv_consMutualFormers h0 hnpT
    have hslot : (ConLeche.consMutualFormers fms env).findProj? f.cvTa.name j = none :=
      findProj?_none_consMutualFormers
        (findProj?_none_of_indFresh mp.base2.proj_ok (hfreshF t f hft) j)
    have hnpC : ∀ cA ∈ ctorsA, Expr.NoProjAt f.cvTa.name j cA.1.type := by
      intro cA hcA
      obtain ⟨J, hJ⟩ := List.getElem?_of_mem hcA
      obtain ⟨-, sorts, -, hrun⟩ := hrunC J cA hJ
      obtain ⟨⟨ty', hccv⟩, -, -⟩ := ConLeche.checkMutualCtor_shape hrun
      obtain ⟨-, -, -, -, -, hnfv, ty, -, -, hann, -, -, -, -, hty⟩ :=
        ConLeche.checkConstantVal_inv hccv
      rw [hty]
      exact ConLeche.annotateCore_noProjAt μ hann hnfv hslot
    have h2 : NoProjEnv (ConLeche.consMutualCtors p.toBlock.nP ctorsA
        (ConLeche.consMutualFormers fms env)) f.cvTa.name j :=
      noProjEnv_consMutualCtors h1 hnpC
    have hnpF4 : ∀ f' ∈ formers4, Expr.NoProjAt f.cvTa.name j f'.tty := by
      intro f' hf'
      rw [← hf4] at hf'
      obtain ⟨f'', hf'', rfl⟩ := List.mem_map.mp hf'
      exact hnpT f'' hf''
    have hnpC4 : ∀ c' ∈ ctors4, Expr.NoProjAt f.cvTa.name j c'.cty := by
      intro c' hc'
      obtain ⟨J, hJ⟩ := List.getElem?_of_mem hc'
      have hJl : J < ctorsA.length := by
        rw [← hlen4C]; exact (List.getElem?_eq_some_iff.mp hJ).1
      have hg := hget4C J _ (hcAGet J hJl)
      rw [hg] at hJ
      obtain rfl : c' = MutualCtor4.mk (ctorsA.getD J default).1.name
          (ctorsA.getD J default).2 (ctorsA.getD J default).1.type
          (p.toBlock.ctors.getD J default).member
          (ConLeche.mutualRecFieldsOf (kinds.getD J [])) := (Option.some.inj hJ).symm
      exact hnpC _ (List.mem_of_getElem? (hcAGet J hJl))
    refine noProjEnv_storeMutualRecs h2 fun x hx => ?_
    have hg := List.mk_mem_zipIdx_iff_getElem?.mp (show (x.1, x.2) ∈ cvRas.zipIdx by simpa using hx)
    have hlt : x.2 < prts.k := by
      have := (List.getElem?_eq_some_iff.mp hg).1
      rw [hk] at this
      exact this
    have hd : cvRas.getD x.2 default = x.1 := by
      rw [List.getD_eq_getElem?_getD, hg]; rfl
    constructor
    · -- the recursor's type is the generated one
      obtain ⟨cvRa, hget, hrun⟩ := hallRec x.2 (by rw [hkF]; exact hlt)
      obtain ⟨recTy, sty, u, hgenR, -, -, -, -, -, -, -, rfl⟩ :=
        ConLeche.checkMutualRecTy_shape hrun
      have hx1 : x.1 = (⟨p.toBlock.recName x.2, p.toBlock.rlps, recTy⟩ : ConstantVal) := by
        rw [← hd, List.getD_eq_getElem?_getD, hget]; rfl
      rw [hx1]
      show Expr.NoProjAt f.cvTa.name j recTy
      exact noProjAt_mutualRecTy hgenR hnpF4 hnpC4
    · -- the recursor's rules are the generated ones
      intro r hr
      obtain ⟨cr, hcr, rfl⟩ := mutualRules_getElem? hr
      obtain ⟨hlenU, hallU⟩ := ConLeche.checkMutualAllRules_inv hrules
      obtain ⟨rules, hrget, hrun⟩ := hallU x.2 (by rw [hkF]; exact hlt)
      have hrD : rulesOf.getD x.2 [] = rules := by
        rw [List.getD_eq_getElem?_getD, hrget]; rfl
      rw [hrD] at hcr
      obtain ⟨-, hlenR, hallR⟩ := ConLeche.checkMutualMemberRules_inv hrun
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hcr
      obtain ⟨J, c, rhs, -, hget, hgen, -, -, -, -⟩ :=
        hallR i (by rw [← hlenR]; exact (List.getElem?_eq_some_iff.mp hi).1)
      obtain rfl : cr = (c, rhs) := Option.some.inj (hi.symm.trans hget)
      show Expr.NoProjAt f.cvTa.name j rhs
      exact noProjAt_mutualRecRhs hgen hnpF4 hnpC4
  -- **stage 5: the structure-like members' projection tables**
  have hE₃ : ConLeche.EtaFamiliesClosed (ConLeche.storeMutualRecs
      (ConLeche.consMutualCtors p.toBlock.nP ctorsA (ConLeche.consMutualFormers fms env))
      p.toBlock fms rulesOf cvRas.zipIdx
      (ConLeche.consMutualCtors p.toBlock.nP ctorsA
        (ConLeche.consMutualFormers fms env))) := by
    refine EtaFamiliesClosed.ofFreshExt hE
      ((mutualFormers_freshExt hformers).trans
        ((consMutualCtors_freshExt (nP := p.toBlock.nP) (checkMutualCtors_fresh hctors)).trans
          (storeMutualRecs_freshExt (checkMutualRecTys_fresh hpinOk hrectys))))
  let dBlk : TableBlockData :=
    { lps := p.toBlock.lps
      nP := p.toBlock.nP
      isProp := (Level.isEquiv f₀.s Level.zero == some true)
      W := Wf
      Idss := Idssf
      FssR := FssRf
      Ess' := Essf
      Fss₀ := Fss0f
      rss := rssf
      tlss := tlssf
      Eiss' := Eissf }
  have hmemTbl : ∀ q ∈ fms.zipIdx,
      MutualTableOk mp₄.base2 dBlk (fun _ => {}) p.toBlock ctorsA sortss q.1 q.2 := by
    intro q hq
    have hget : fms[q.2]? = some q.1 :=
      List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using hq)
    have hlt : q.2 < fms.length := (List.getElem?_eq_some_iff.mp hget).1
    have hgetD : fms.getD q.2 default = q.1 := by
      rw [List.getD_eq_getElem?_getD, hget]; rfl
    have hgetD₀ : fms.getD q.2 f₀ = q.1 := by
      rw [List.getD_eq_getElem?_getD, hget]; rfl
    refine ⟨fun j => hnpG q.2 q.1 hget j, hFPS (hFPc (hfindF q.2 q.1 hget)), ?_⟩
    intro J c hown hnIdx
    -- constructor `J` of the block is this member's only one
    have hmemOwn : (J, c) ∈ p.toBlock.ownCtors q.2 := by rw [hown]; exact List.mem_cons_self
    have hownMem := List.mem_filter.mp hmemOwn
    obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hownMem.1
    obtain ⟨hxc, hxJ⟩ : x.1 = c ∧ x.2 = J := by
      constructor
      · have := congrArg Prod.snd hxe; simpa using this
      · have := congrArg Prod.fst hxe; simpa using this
    have hxget : p.toBlock.ctors[J]? = some c := by
      have h := List.mk_mem_zipIdx_iff_getElem?.mp
        (show (x.1, x.2) ∈ p.toBlock.ctors.zipIdx by simpa using hx)
      rw [hxc, hxJ] at h
      exact h
    have hJl : J < ctorsA.length := by
      rw [hlenA]; exact (List.getElem?_eq_some_iff.mp hxget).1
    have hcA := hcAGet J hJl
    have hcJ : p.toBlock.ctors.getD J default = c := by
      rw [List.getD_eq_getElem?_getD, hxget]; rfl
    have hmemJ : memF J = q.2 := by
      show (p.toBlock.ctors.getD J default).member = q.2
      rw [hcJ]
      have := hownMem.2
      simpa using this
    have hnF : (ctorsA.getD J default).2 = c.nF := by
      have h := (hrunC J _ hcA).1
      rw [h, hcJ]
    have hnm : (ctorsA.getD J default).1.name = c.cv.name := by
      have h1 := congrArg (fun l => l[J]?) hnamesC
      rw [List.getElem?_map, List.getElem?_map, hcA, hxget] at h1
      simpa using h1
    -- the member's own data, at the member index
    have hmtG : fms[memF J]? = some q.1 := by rw [hmemJ]; exact hget
    have hmtG' : fms[memF J]? = some (fms.getD (memF J) default) :=
      hfmGet _ (by rw [hmemJ]; exact hlt)
    have hmemD : fms.getD (memF J) default = q.1 := by rw [hmemJ]; exact hgetD
    have hmemD₀ : fms.getD (memF J) f₀ = q.1 := by rw [hmemJ]; exact hgetD₀
    -- the constructor's stage, and its sorts
    obtain ⟨-, sorts, hsj, hrunJ⟩ := hrunC J _ hcA
    have hsortsD : sortss.getD J [] = sorts := by
      rw [List.getD_eq_getElem?_getD, hsj]; rfl
    have hPropJ : (Level.isEquiv f₀.s Level.zero == some true) = true →
        ∀ ψ' : Name → Nat, Level.eval ψ' (fms.getD (memF J) default).s
          = Level.eval ψ' Level.zero := by
      intro hp ψ'
      rw [hsEq _ _ hmtG' ψ']
      exact Level.isEquiv_sound (beq_iff_eq.mp hp) ψ'
    have hFDm := FormerData.congr_sort (hFD₂ _ _ hmtG') (fun ψ' => (hsEq _ _ hmtG' ψ').symm)
    obtain ⟨-, -, hlenS, hleqS, hsortsAll⟩ := mutualCtorFrames hμ mp₁ hrunJ (hfindF _ _ hmtG')
      hPropJ hFDm (hCD₁ J _ hcA).toCtorDataI (hleafT₁ _ _ hmtG')
    -- the member's sort, spelled at the block's
    have hsq : ∀ ψ : Name → Nat, q.1.s.eval ψ = f₀.s.eval ψ := hsEq _ _ hget
    -- a structure-like member has no index, so its telescope IS its
    -- parameter telescope
    have htakeP : ∀ ψ : Name → Nat, (ppsF q.2 ψ).take p.toBlock.nP = ppsF q.2 ψ := by
      intro ψ
      refine List.take_of_length_le ?_
      rw [(hFD₂ _ _ hget).len ψ, hnIdx]
      omega
    refine ⟨(ctorsA.getD J default).1, ppsF q.2, dsF J, esF J, lvlsF q.2, rfl, hnm,
      ?_, hlpsF _ _ hget, ?_, hlpsC J _ hcA, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- the block's members carry the capability record `{}`
      intro hh
      exact absurd (show (false : Bool) = true from hh) (by simp)
    · -- the constructor is stored at the group store
      have h := (hcons₂ J _ hJl hcA).1.1
      rw [hnF] at h
      exact hFPS h
    · -- the constructor's telescope
      obtain ⟨cbs, es, hstrip, -⟩ := (hCD₁ J _ hcA).resid
      rw [← hnF, hstrip]
      rfl
    · -- the BLOCK's `isProp` bit (member `0`'s spelling) IS this
      -- member's own: the members' sorts agree semantically
      -- (`mutualCrossChecks`, `hsq`) and `isEquiv · .zero` is complete
      -- (`isPropBit_congr`)
      show (Level.isEquiv f₀.s Level.zero == some true)
        = (Level.isEquiv q.1.s Level.zero == some true)
      exact isPropBit_congr (fun ψ => (hsq ψ).symm)
    · -- the member's name is not a projection function's
      obtain ⟨cv, cv', bs, -, hccv, -, -, -⟩ := hposF q.2 q.1 hget
      obtain ⟨-, -, hsh, -, -, -, _, _, _, -, -, -, -, -, hty⟩ :=
        ConLeche.checkConstantVal_inv hccv
      rw [hty]; exact hsh
    · -- the constructor's name is not a projection function's
      obtain ⟨⟨ty', hccv⟩, -, -⟩ := ConLeche.checkMutualCtor_shape hrunJ
      obtain ⟨-, -, hsh, -, -, -, _, _, _, -, -, -, -, -, hty⟩ :=
        ConLeche.checkConstantVal_inv hccv
      rw [hty]; exact hsh
    · -- the member's name is not reserved
      obtain ⟨cv, cv', bs, -, hccv, -, -, -⟩ := hposF q.2 q.1 hget
      obtain ⟨-, hres, -, -, -, -, _, _, _, -, -, -, -, -, hty⟩ :=
        ConLeche.checkConstantVal_inv hccv
      rw [hty]; exact hres
    · -- the member's RECURSOR name is not reserved
      obtain ⟨mb, hmb, hnameR, -⟩ := hCVcheck q.2 hlt
      have hnr := hnres q.2 hlt
      rw [hnameR, ConLeche.mutualRecPinOk_name hpinOk
        (by rw [show p.k = prts.k from hmembersLen]; exact hlt) hmb] at hnr
      have hnameM : q.1.cvTa.name = mb.cv.name := by
        have h1 := congrArg (fun l => l[q.2]?) hnamesF
        rw [List.getElem?_map, hget] at h1
        have h2 : p.toBlock.memberNames[q.2]? = some mb.cv.name := by
          show (p.toBlock.formers.map (·.1.name))[q.2]? = _
          rw [List.getElem?_map]
          show ((p.members.map fun mb' => (mb'.cv, mb'.nIdx))[q.2]?).map (·.1.name) = _
          rw [List.getElem?_map, hmb]
          rfl
        rw [h2] at h1
        simpa using h1
      rw [hnameM]
      exact hnr
    · -- the constructor's name is not reserved
      obtain ⟨⟨ty', hccv⟩, -, -⟩ := ConLeche.checkMutualCtor_shape hrunJ
      obtain ⟨-, hres, -, -, -, -, _, _, _, -, -, -, -, -, hty⟩ :=
        ConLeche.checkConstantVal_inv hccv
      rw [hty]; exact hres
    · -- the member's binder data, at the group store
      have hFDq := FormerData.congr_sort (hFD₃ _ _ hget) (fun ψ => (hsq ψ).symm)
      rw [hnIdx] at hFDq
      exact FormerData.crossEnv hFDq (hcbF₂ q.2 q.1 hget) hFPS hLGS hPJS hagS4
    · -- the constructor's type, read at the group store
      intro ψ
      have hr := ((hCReads ψ).2 J (by rw [hlen4C]; exact hJl)).base.read
      have hc4 : ctors4.getD J default = MutualCtor4.mk c.cv.name c.nF
          (ctorsA.getD J default).1.type (p.toBlock.ctors.getD J default).member
          (ConLeche.mutualRecFieldsOf (kinds.getD J [])) := by
        rw [List.getD_eq_getElem?_getD, hget4C J _ hcA, ← hnm, ← hnF]
        rfl
      rw [hc4, show (fixCtorDataList dsF esF (fun J' => kindsOf (ksF J')) eissF tssF ψ
            ctorsA 0).getD J default = ((c.cv.name, c.nF, dsF J ψ, esF J ψ,
            ConLeche.recIdxOf (kindsOf (ksF J)), eissF J ψ, tssF J ψ) : CtorDatumR) from by
          rw [List.getD_eq_getElem?_getD, fixCtorDataList_getElem?, hcA]
          simp only [Nat.zero_add, Option.map_some, Option.getD_some]
          rw [hnm, hnF]] at hr
      have hr' := denoteMeta_toStore (b := p.toBlock) (fms := fms) (rulesOf := rulesOf)
        hfrZ hndZ hagS4 ψ 0 _ (hcbCC J _ hcA) hr
      rw [hmemD₀] at hr'
      show denoteMeta mp₄.base2.acval _ ψ 0 (ctorsA.getD J default).1.type
        = some (mkPisAV (dsF J ψ) (ctorBodyAVI mp₄.base2 q.1.cvTa.name p.toBlock.nP c.nF ψ
            (esF J ψ)))
      rw [show ctorBodyAVI mp₄.base2 q.1.cvTa.name p.toBlock.nP c.nF ψ (esF J ψ)
          = AnnotTerm.mkAppN (mp₄.base2.acval q.1.cvTa.name ψ)
            (paramBvars p.toBlock.nP c.nF ++ esF J ψ) from rfl,
        ← hagS4 q.1.cvTa.name (by rw [hFPc (hfindF q.2 q.1 hget)]; rfl)]
      exact hr'
    · -- the constructor's binder count
      intro ψ
      rw [(hCD₁ J _ hcA).len ψ, hnF]
    · -- the constructor's binder data is closed
      exact fun ψ => (hCD₁ J _ hcA).below ψ
    · -- the fields' sorts are bounded at a non-`Prop` block
      intro k hk hp
      rw [hsortsD]
      have h := hleqS k (by rw [hnF]; exact hk) hp
      rw [hmemD] at h
      exact h
    · -- the member's leaf, at the group store
      intro ψ
      rw [← hagS4 q.1.cvTa.name (by rw [hFPc (hfindF q.2 q.1 hget)]; rfl)]
      have h := hleaf₂ J _ hcA ψ
      rw [hmemD] at h
      show mp₂.base2.acval q.1.cvTa.name ψ = _
      rw [h]
      show mutualTyAVI (Wf ψ) (f₀.s.eval ψ) (ppsF (memF J) ψ)
          (fms.getD (memF J) default).nIdx (Idssf ψ) rssf (tlssf ψ) (Eissf ψ) (Fss0f ψ)
          (Essf ψ) (memF J) = _
      rw [hmemJ, hgetD, hnIdx, hsq ψ]
    · -- the constructor's leaf, at the group store
      intro ψ
      rw [← hagS4 (ctorsA.getD J default).1.name
        (by rw [(hcons₂ J _ hJl hcA).1.1]; rfl), hleafC₂ J _ hcA ψ, hsq ψ]
    · -- the member's carrier, folded: the leaf at a parameter spine is
      -- the block's restricted tagged union at the member's own tag
      intro ψ ρ ts hsp
      have hsatQ : Sat V (((ppsF q.2 ψ).map (·.2.2)).reverse) (consList ts ρ) := by
        have h := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hsp
        rwa [List.append_nil] at h
      have hsatQ' : Sat V ((((ppsF q.2 ψ).take p.toBlock.nP).map (·.2.2)).reverse)
          (consList ts ρ) := by rw [htakeP ψ]; exact hsatQ
      have hsat0 : Sat V ((((ppsF 0 ψ).take p.toBlock.nP).map (·.2.2)).reverse)
          (consList ts ρ) := hframeAll q.2 0 q.1 f₀ hget hf0 ψ _ hsatQ'
      obtain ⟨hTag, -⟩ := hIdxAll 0 f₀ hf0 ψ (consList ts ρ) hsat0
      obtain ⟨hFix, hRealρ, -⟩ := hChainFull 0 f₀ hf0 ψ (consList ts ρ) hsat0
      obtain ⟨hX, -⟩ := hXAll 0 f₀ hf0 ψ (consList ts ρ) hsat0
      have hIdsQ : (Idssf ψ)[q.2]? = some [] := by
        have h := hIdssGet ψ q.2 hlt
        rwa [show ((ppsF q.2 ψ).drop p.toBlock.nP).map (·.2.2) = [] from by
          rw [List.drop_eq_nil_of_le (by rw [(hFD₂ _ _ hget).len ψ, hnIdx]; omega),
            List.map_nil]] at h
      have hbase : MutualBaseI (Wf ψ) (f₀.s.eval ψ) (consList ts ρ) 0 (Idssf ψ) rssf (tlssf ψ)
          (Eissf ψ) (Fss0f ψ) (Essf ψ) q.2 :=
        ⟨by rw [shiftE_zero_zero]; exact hTag, by rw [shiftE_zero_zero]; exact hFix,
          [], hIdsQ, rfl, by rw [shiftE_zero_zero]; exact trivial⟩
      have hsp1 : SpineFit (consList ts ρ) (auxIds (Wf ψ) (Idssf ψ))
          [inj q.2 (mkTower [pt])] := by
        refine ⟨?_, trivial⟩
        rw [(tagTyAV_facts hTag).1]
        exact tagTuple_mem hTag hIdsQ (show SpineFit (consList ts ρ) [] [] from trivial)
      have hsum := fixFamI_app_eq_sum hX hRealρ hsp1
      rw [show (auxIds (Wf ψ) (Idssf ψ)).length = 1 from rfl] at hsum
      show ts.foldl SetTheory.app (interp V ρ (mutualTyAVI (Wf ψ) (q.1.s.eval ψ) (ppsF q.2 ψ) 0
          (Idssf ψ) rssf (tlssf ψ) (Eissf ψ) (Fss0f ψ) (Essf ψ) q.2))
        = mutualCarrierAt (q.1.s.eval ψ) q.2 (FssRf ψ) (Essf ψ) (consList ts ρ)
      rw [hsq ψ, mutualTyAVI_fold hsp hbase, shiftE_zero_zero]
      show SetTheory.app (auxFamI (Wf ψ) (f₀.s.eval ψ) (consList ts ρ) (Idssf ψ) rssf (tlssf ψ)
          (Eissf ψ) (Fss0f ψ) (Essf ψ)) (auxTup (Wf ψ) (inj q.2 (mkTower [pt]))) = _
      unfold auxFamI auxTup
      rw [hsum]
      rfl
    · -- the constructor's field chain, positionally
      exact fun ψ => hFssG ψ J hJl
    · -- every OTHER constructor's tag is another member's, so the
      -- member's fibre is its own constructor's alone
      intro ψ ρp hρ j hj Fs' Es'' hFs' hEs'' fs hfit
      have hjl : j < ctorsA.length := by
        have h := (List.getElem?_eq_some_iff.mp hFs').1
        rwa [show (FssRf ψ).length = ctorsA.length from mutFss_length] at h
      have hcAj := hcAGet j hjl
      obtain rfl : Fs' = ((dsF j ψ).drop p.toBlock.nP).map (·.2.2) :=
        Option.some.inj (hFs'.symm.trans (hFssG ψ j hjl))
      obtain rfl : Es'' = [tagTupleAV (Wf ψ) (memF j) (ctorsA.getD j default).2 (Idssf ψ)
          (esF j ψ)] := Option.some.inj (hEs''.symm.trans (hEssG j _ hcAj ψ))
      -- the frames: the block's parameters are the same at every member
      have hρM : Sat V (((ppsF (memF J) ψ).take p.toBlock.nP).map (·.2.2)).reverse ρp :=
        ((hframesJ J hJl).1 ψ ρp).mpr hρ
      have hρj : Sat V (((dsF j ψ).take p.toBlock.nP).map (·.2.2)).reverse ρp :=
        ((hframesJ j hjl).1 ψ ρp).mp
          (hframeAll (memF J) (memF j) _ _ (hfmGet _ (hmotLt J hJl))
            (hfmGet _ (hmotLt j hjl)) ψ ρp hρM)
      have hfr := (hframesJ j hjl).2 ψ ρp hρj
      obtain ⟨hEok, hfitE⟩ := hfr.2.2.2 fs hfit
      have hlenfs : fs.length = (ctorsA.getD j default).2 := by
        rw [hfit.length_eq, List.length_map, List.length_drop, (hCD₁ j _ hcAj).len ψ]
        omega
      have hshift : shiftE (ctorsA.getD j default).2 0 (consList fs ρp) = ρp := by
        rw [← hlenfs]; exact shiftE_consList _ _
      obtain ⟨hTag, -⟩ := hIdxAll 0 f₀ hf0 ψ ρp
        (hframeAll (memF J) 0 _ _ (hfmGet _ (hmotLt J hJl)) hf0 ψ ρp hρM)
      obtain ⟨hval, -⟩ := tagTupleAV_facts hTag (hIdssGet ψ (memF j) (hmotLt j hjl)) hshift
        (fun E hE => (hEok E hE).1) hfitE
      have hne : memF j ≠ q.2 := by
        -- a constructor of ANOTHER member: this member owns only `J`
        intro hh
        refine hj ?_
        have hmem : (j, p.toBlock.ctors.getD j default) ∈ p.toBlock.ownCtors q.2 := by
          refine List.mem_filter.mpr ⟨?_, ?_⟩
          · refine List.mem_map.mpr ⟨(p.toBlock.ctors.getD j default, j), ?_, rfl⟩
            refine List.mk_mem_zipIdx_iff_getElem?.mpr ?_
            rw [List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (show j < p.toBlock.ctors.length by
                rw [← hlenA]; exact hjl)]
            rfl
          · show ((p.toBlock.ctors.getD j default).member == q.2) = true
            rw [show (p.toBlock.ctors.getD j default).member = memF j from rfl, hh]
            exact beq_self_eq_true _
        rw [hown, List.mem_singleton] at hmem
        exact (Prod.mk.inj hmem).1
      exact ⟨memF j, _, hne, hval⟩
    · -- the block's chains are graded at the constructor's frame
      intro ψ ρ hρ
      rw [hsq ψ]
      exact (hFssOkP J _ hcA ψ ρ hρ).1
    · -- the two parameter frames agree
      intro ψ ρ
      have h := (hframesJ J hJl).1 ψ ρ
      rw [hmemJ, htakeP ψ] at h
      exact h
    · -- the constructor's fields are graded and valid
      intro ψ ρ hρ
      have h := (hframesJ J hJl).2 ψ ρ hρ
      rw [hmemD] at h
      exact ⟨h.1, h.2.1⟩
    · -- the fields are bounded at a non-`Prop` block
      intro ψ ρ hρ hp
      have h := (hframesJ J hJl).2 ψ ρ hρ
      rw [hmemD] at h
      exact h.2.2.1 hp
    · -- the fields' readings lie in their sorts' universes
      intro ψ ρ hρ k hk as hsp
      rw [hsortsD]
      exact hsortsAll ψ ρ hρ k (by rw [hnF]; exact hk) as hsp
  obtain ⟨mp₅, -, -⟩ := stageMutualTables (d := dBlk) (capsOf := fun _ => {}) mp₄ rfl rfl hE₃
    htbl hndF hmemTbl
  exact ⟨mp₅⟩

end ConLeche.Model
