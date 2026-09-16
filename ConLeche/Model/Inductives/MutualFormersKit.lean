module

public import ConLeche.Model.Inductives.MutualStageFormer
public import ConLeche.Model.Inductives.MutualRecRead
public section

/-!
# The mutual block's formers/constructor-reading kit (task #315)

The target-agnostic kit task #278 kept inside its big assembly file:
the completeness of `Level.isEquiv · .zero`, the shadow chain's
agreement off the recursive slots, the λ-tower congruence over its
domains, the formers' conses read positionally, the block's member
table (`members3`), the positivity/kind targets, the conses as
extensions the readings cross, the CHAIN-FREE FIRST PASS of the
formers' loop (`stageMembersG` at an ARBITRARY leaf), the
identification of the two constructor readings
(`mutualCtorDataI_ident`), the opened guard's travel to the formers'
environment, `FieldsBelow` positionally, a member's index telescope
from its former's data alone, and the two `crossEnv` transports of
the recursor's readings.

Everything that mentions a block REPRESENTATION, the recursors' group
store or the generated rules stays with the route that owns it.
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

/-! ## Kit: two index-aligned lists, filtered and mapped alike

The stored rules name the member's own constructors in block order
(`IndRep.rules` at `IndRepData.memberCtors`), and the block carries
those constructors TWICE — as the recognised `MutualCtor`s (whose
`member` field the checker filters on) and as the checked
`ConstantVal`s of `ctorsA` (whose global index the model's `mots`
reads).  The two lists are index-aligned, so the filtered name lists
coincide. -/

omit [SetTheory V] in
/-- **Index-aligned filters agree**: two lists of the same length whose
entries agree, at every position, on the bit the filter reads and the
name the map takes give the same list. -/
theorem zipIdx_filter_map_eq {α β : Type} {pA : α × Nat → Bool} {pB : β × Nat → Bool}
    {fA : α × Nat → Name} {fB : β × Nat → Name} :
    ∀ (as : List α) (bs : List β) (k : Nat), as.length = bs.length →
      (∀ (i : Nat) (a : α) (b : β), as[i]? = some a → bs[i]? = some b →
        pA (a, k + i) = pB (b, k + i) ∧ fA (a, k + i) = fB (b, k + i)) →
      ((as.zipIdx k).filter pA).map fA = ((bs.zipIdx k).filter pB).map fB
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, hlen, _ => by simp at hlen
  | a :: as, b :: bs, k, hlen, h => by
    have h0 := h 0 a b rfl rfl
    rw [Nat.add_zero] at h0
    have hrest : ((as.zipIdx (k + 1)).filter pA).map fA
        = ((bs.zipIdx (k + 1)).filter pB).map fB := by
      refine zipIdx_filter_map_eq as bs (k + 1) (by simpa using hlen) fun i a' b' ha hb => ?_
      have := h (i + 1) a' b' (by simpa using ha) (by simpa using hb)
      rwa [show k + (i + 1) = k + 1 + i from by omega] at this
    rw [List.zipIdx_cons, List.zipIdx_cons, List.filter_cons, List.filter_cons, h0.1]
    cases hp : pB (b, k) with
    | false => simpa using hrest
    | true => simp [h0.2, hrest]

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

/-- A lookup past a cons whose head carries another name. -/
theorem find?_cons_of_name_ne {c : ConstantInfo} {env : Env} {n : Name} (h : ¬ c.name = n) :
    (Env.mk (c :: env.consts)).find? n = env.find? n := by
  rw [ConLeche.Env.find?_cons, if_neg h]

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
    (h : FormerData m cvT nP s pps) (hs : ∀ ψ : Name → Nat, s.eval ψ = s'.eval ψ) :
    FormerData m cvT nP s' pps where
  read ψ := by rw [← hs ψ]; exact h.read ψ
  len := h.len
  bits := h.bits
  okTy ψ ρ := by rw [← hs ψ]; exact h.okTy ψ ρ
  below := h.below
  params ψ₁ ψ₂ hφ := ⟨(h.params ψ₁ ψ₂ hφ).1, by rw [← hs ψ₁, ← hs ψ₂]; exact (h.params ψ₁ ψ₂ hφ).2⟩

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
    {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (h : FormerData m cvT nP resSort pps)
    (hcb : ConstsBound env cvT.type)
    (hF : FindPreserved env env') (hG : LitGuardsMono env env')
    (hproj : ∀ (sn : Name) (i : Nat), env.findProj? sn i = none → env'.findProj? sn i = none)
    (hag : ∀ n : Name, (env.find? n).isSome = true → m.acval n = m'.acval n) :
    FormerData m' cvT nP resSort pps where
  read ψ := by
    refine denoteMeta_envExtend_mono hF hG hproj 0 cvT.type hcb ?_
    rw [← denoteMeta_acval_congr hag]
    exact h.read ψ
  len := h.len
  bits := h.bits
  okTy := h.okTy
  below := h.below
  params := h.params

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

/-- **The P step at one member's cons with an arbitrary closed leaf.** -/
theorem stageMemberConsG (mp : EnvModelM V μ env) (hE₀ : ConLeche.EtaFamiliesClosed env)
    {cvTa : ConstantVal} (hok : MemberConsOk env cvTa)
    {nP : Nat} {resSort : Level}
    {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hFD : FormerData mp.base2 cvTa nP resSort pps)
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

/-- **The formers' loop at an arbitrary leaf** (`stageMutualFormersGo`
with the fibre leaf abstracted; `idxs i` is the block position of the
loop's `i`-th member).  The leaf's four facts are per member, beside
its binder data. -/
theorem stageMembersGoG {nP : Nat} {resSort : Level} {lps : List Name}
    {Aof : Nat → (Name → Nat) → AnnotTerm}
    {ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} :
    ∀ (fs : List MutualFormerA) (idxs : Nat → Nat) (env' : Env) (mp' : EnvModelM V μ env'),
      ConLeche.EtaFamiliesClosed env' →
      (∀ f ∈ fs, MemberConsOk env' f.cvTa) →
      (fs.map (fun f => f.cvTa.name)).Nodup →
      (∀ (i : Nat) (f : MutualFormerA), fs[i]? = some f →
        f.cvTa.levelParams = lps ∧
        FormerData mp'.base2 f.cvTa (nP + f.nIdx) resSort (ppsF (idxs i)) ∧
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
    {formers : List (ConstantVal × Nat)} {env₁ : Env} {fms : List MutualFormerA}
    (mp : EnvModelM V μ env) (hE : ConLeche.EtaFamiliesClosed env)
    (hrun : ConLeche.mutualFormers (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) nP formers env
      = .ok (env₁, fms))
    (hnd : (fms.map (fun f => f.cvTa.name)).Nodup)
    (hmem : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      f.cvTa.levelParams = lps ∧
      FormerData mp.base2 f.cvTa (nP + f.nIdx) resSort (ppsF t) ∧
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

/-! ## Kit: binder lists, truncated -/

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


end ConLeche.Model
