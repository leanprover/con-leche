module

public import ConLeche.Model.Inductives.MutualRecTyping
public import ConLeche.Model.Inductives.MutualRecData
public import ConLeche.Model.Inductives.MutualRecLaw
import ConLeche.Model.Inductives.StructCaps
import ConLeche.Model.Swap
import ConLeche.Model.Inductives.FixLeafOk
import ConLeche.Model.IndCons
import ConLeche.Model.RecRulesCons
import ConLeche.Verify.Inductives.MutualWF
public section

/-!
# The mutual block's recursor stage (task #278, M2.5d)

The block's `k` member recursors, consed into the model with their
rules.  The kernel does this in three moves
(`Kernel/Inductives/MutualInstall.lean`), and so does this file:

* `provisionMutualRecs` conses the `k` recursors RULE-LESS onto the
  constructors' environment `env₂` — a rule mentions the sibling
  recursors, so every rule is scoped at the environment holding all of
  them.  `stageMutualRecProvision` is the P step at ONE such cons
  (`declStep_preserves_of_ind_rec_cons` with `rules := []`, whose
  `hrec` is `recRules_cons_fresh`: a rule-less recursor owes no rule
  law), `stageMutualRecsProvision` the loop.
* `storeMutualRecs` conses the SAME `k` names, in the same order, onto
  the same `env₂`, differing only in their rules.  The carrier crosses
  that with `EnvModelM.swapP` (`stageMutualRecsStore`), whose `hrecP`
  is the block's own rule law at the FINAL environment —
  `mutualRecRuleLaw`, `FixStageRec.lean`'s `fixRecRuleLaw` at `k`
  motives.

The leaf is member `t`'s recursor leaf `mutualRecAVI … t`
(`MutualRecLeaf.lean`), whose λ-data IS the stored type's reading
(`mutualRdsAV`) — `MutualRecParts` bundles the ψ-indexed data the two
spellings share, so that the two agree by `rfl`.

**The caller's invariant `Inv`** (task #278 M2.7).  The representation
clause (task #280) is owed at EVERY intermediate carrier of the
provisioning loop, and those carriers are anonymous here: the loop
knows only that the next recursor's name is fresh.  So the loop
threads a predicate on carriers the CALLER chooses — the pattern
`stageMutualCtors` already uses — with one step obligation `hInv` (a
fresh recursor's cons preserves it, which for the block's
representations is `IndRep.cross`).  `hrepsP` and `hrepsS` then get
`Inv` at the carrier they are taken at, and `declMutual` supplies the
block's `k` `IndRep`s, built ONCE at the constructors' carrier.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta
  RecRule MutualBlock MutualFormerA MutualFormer MutualCtor MutualCtor4)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The block's data -/

/-- **The ψ-indexed data of a mutual block's recursor stage** — the
arguments the member leaf (`mutualRecAVI`), the stored type's reading
(`mutualRdsAV`) and the leaf's typing hypotheses (`MutualLeafHyp`)
share.  Purely syntactic: no `V`, no environment. -/
structure MutualRecParts : Type where
  /-- the elimination level's value -/
  ℓ : (Name → Nat) → Nat
  /-- the tag telescope's universe -/
  W : (Name → Nat) → Nat
  /-- the block's one result level -/
  wB : (Name → Nat) → Nat
  /-- the auxiliary recursor type's universe -/
  s : (Name → Nat) → Nat
  /-- the elimination level's `PropWhen` bit -/
  bb : (Name → Nat) → Nat
  /-- the number of members -/
  k : Nat
  /-- the number of constructors -/
  n : Nat
  /-- the number of parameters -/
  nP : Nat
  /-- the elimination level -/
  elimL : Level
  /-- member `t`'s former leaf -/
  Lof : Nat → (Name → Nat) → AnnotTerm
  /-- member `t`'s index count -/
  nIdxOf : Nat → Nat
  /-- member `t`'s parameter data -/
  ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)
  /-- member `t`'s index data -/
  ipsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)
  /-- the members' index telescopes -/
  Idss : (Name → Nat) → List (List AnnotTerm)
  /-- the constructors' REAL field chains -/
  FssR : (Name → Nat) → List (List AnnotTerm)
  /-- the constructors' X-chains -/
  Fss₀ : (Name → Nat) → List (List AnnotTerm)
  /-- the constructors' tagged index blocks -/
  Ess' : (Name → Nat) → List (List AnnotTerm)
  /-- the recursive positions, per constructor -/
  rss : List (List Bool)
  /-- the recursive slots' telescopes -/
  tlss : (Name → Nat) → List (List (List (Nat × Nat × AnnotTerm)))
  /-- the recursive slots' RAW index expressions -/
  EissO : (Name → Nat) → List (List (List AnnotTerm))
  /-- the recursive slots' TAGGED index expressions -/
  Eiss' : (Name → Nat) → List (List (List AnnotTerm))
  /-- a constructor's own member -/
  mems : Nat → Nat
  /-- a recursive slot's target member -/
  tgts : Nat → Nat → Nat
  /-- the constructors' data -/
  cds : (Name → Nat) → List CtorDatumR

namespace MutualRecParts

variable (p : MutualRecParts)

/-- The `k` member leaves, as a list. -/
@[expose] def Ls (ψ : Name → Nat) : List AnnotTerm := (List.range p.k).map fun q => p.Lof q ψ

/-- The `k` members' index counts, as a list. -/
@[expose] def nIdxs : List Nat := (List.range p.k).map p.nIdxOf

/-- The `k` members' index data, as a list. -/
@[expose] def ipss (ψ : Name → Nat) : List (List (Nat × Nat × AnnotTerm)) :=
  (List.range p.k).map fun q => p.ipsOf q ψ

/-- **Member `t`'s recursor leaf** at the block's data. -/
@[expose] def leaf {env₀ : Env} (m₀ : EnvModel V env₀) (t : Nat) (ψ : Name → Nat) : AnnotTerm :=
  mutualRecAVI m₀ ψ (p.ℓ ψ) (p.W ψ) (p.wB ψ) p.nP (p.s ψ) (p.bb ψ) p.elimL (p.Ls ψ) p.nIdxs
    (p.ppsOf 0 ψ) (p.ipss ψ) (p.Idss ψ) p.rss (p.tlss ψ) (p.Eiss' ψ) (p.FssR ψ) (p.Fss₀ ψ)
    (p.Ess' ψ) p.mems p.tgts (p.cds ψ) t

/-- **Member `t`'s stored recursor type's binder data** — the leaf's
own λ-data (`leaf_data`). -/
@[expose] def rds {env₀ : Env} (m₀ : EnvModel V env₀) (t : Nat) (ψ : Name → Nat) :
    List (Nat × Nat × AnnotTerm) :=
  mutualRdsAV m₀ p.k p.nP p.elimL p.Lof p.nIdxOf p.ppsOf p.ipsOf p.cds p.mems p.tgts t ψ

/-- Member `t`'s recursor type's conclusion. -/
@[expose] def conc (t : Nat) : AnnotTerm := mutualConcAV p.k p.n (p.nIdxOf t) t

/-- **The member leaf's typing hypotheses**, at every member and every
assignment (`MutualRecTyping.lean`'s `MutualLeafHyp` at the block's
data). -/
@[expose] def LeafHyp (V : Type w) [SetTheory V] {env₀ : Env} (m₀ : EnvModel V env₀) : Prop :=
  ∀ t, t < p.k → ∀ ψ : Name → Nat,
    MutualLeafHyp V m₀ ψ p.elimL (p.ℓ ψ) (p.W ψ) (p.wB ψ) p.nP (p.s ψ) (p.bb ψ) p.k p.n
      (p.Ls ψ) p.nIdxs (p.ppsOf 0 ψ) (p.ipss ψ) (p.Idss ψ) p.rss (p.tlss ψ) (p.EissO ψ)
      (p.Eiss' ψ) (p.FssR ψ) (p.Fss₀ ψ) (p.Ess' ψ) p.mems p.tgts (p.cds ψ) t

omit [SetTheory V] in
/-- Member `t`'s index count, off the list. -/
theorem nIdxs_getD {t : Nat} (ht : t < p.k) : p.nIdxs.getD t 0 = p.nIdxOf t :=
  getD_range_map _ _ _ ht _

/-- **The member recursor leaf's facts** at the block's data: graded,
bit-valid, and in the reading of its stored type. -/
theorem leaf_facts {env₀ : Env} {m₀ : EnvModel V env₀} (hyp : p.LeafHyp V m₀)
    {t : Nat} (ht : t < p.k) (ψ : Name → Nat) (ρ : Nat → V) :
    WellDenotedV V ρ (p.leaf m₀ t ψ) ∧
      interp V ρ (p.leaf m₀ t ψ) ∈ˢ interp V ρ (mkPisAV (p.rds m₀ t ψ) (p.conc t)) := by
  have h := mutualRecLeafFacts (hyp t ht ψ) ρ
  rw [p.nIdxs_getD ht] at h
  exact h

end MutualRecParts

/-! ## One recursor's rule-less cons -/

/-- **The P step at ONE provisioned recursor's cons**: member `t`'s
recursor, consed RULE-LESS (`provisionMutualRecs`' entry) with the leaf
`mutualRecAVI … t`.  Its typing is the leaf's own
(`mutualRecLeafFacts`, through `MutualRecParts.leaf_facts`), its type's
reading the stored recursor type's (`MutualRecData`), its rule law
nothing (`recRules_cons_fresh`: a rule-less recursor owes none) and its
capability obligation nothing either — the cons stores a RECURSOR at
the name the obligation is taken at, so `capsOk_cons_native`'s
block-family branch is refuted by `Env.find?_cons_self` and the rest is
`EtaFamiliesClosed`. -/
theorem stageMutualRecProvision (p : MutualRecParts) {env₀ : Env} {m₀ : EnvModel V env₀}
    (mp : EnvModelM V μ env) (hyp : p.LeafHyp V m₀)
    (hE : ConLeche.EtaFamiliesClosed env)
    {cvRa : ConstantVal} {mI rP t : Nat} (ht : t < p.k)
    (hfresh : env.find? cvRa.name = none)
    (hnres : ConLeche.reservedBasisNames.contains cvRa.name = false)
    (hpshape : cvRa.name.isProjFnShape = false)
    (hwf : ConLeche.EnvWF ⟨.recInfo cvRa mI rP [] :: env.consts⟩)
    (hcb : ConstsBound env cvRa.type)
    (hRD : MutualRecData mp.base2 cvRa p.nP p.k p.n (p.nIdxOf t) t p.elimL (p.rds m₀ t))
    (hAcl : ∀ ψ : Name → Nat, Term.bvarsBelow 0 (p.leaf m₀ t ψ).erase)
    (hAparams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ cvRa.levelParams, ψ₁ q = ψ₂ q) →
      p.leaf m₀ t ψ₁ = p.leaf m₀ t ψ₂)
    (hreps : ∀ m₂ : EnvModel V ⟨.recInfo cvRa mI rP [] :: env.consts⟩,
      m₂.acval = acvalWith mp.base2.acval cvRa.name (p.leaf m₀ t) →
      IndRepsHead env (.recInfo cvRa mI rP []) m₂) :
    ∃ mp' : EnvModelM V μ ⟨.recInfo cvRa mI rP [] :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval cvRa.name (p.leaf m₀ t) := by
  have hcross : ∀ e : Expr, ConsCrossAt (.recInfo cvRa mI rP []) e :=
    fun _ => ConsCrossAt.ofNtc (fun _ h => nomatch h)
  have hread : ∀ ψ : Name → Nat,
      denoteMeta (acvalWith mp.base2.acval cvRa.name (p.leaf m₀ t))
        ⟨.recInfo cvRa mI rP [] :: env.consts⟩ ψ 0 cvRa.type
        = some (mkPisAV (p.rds m₀ t ψ) (p.conc t)) := fun ψ =>
    denoteMeta_cons_mono (c₀ := .recInfo cvRa mI rP []) hfresh (hcross _) ψ 0 hcb (hRD.read ψ)
  refine declStep_preserves_of_ind_rec_cons mp (c₀ := .recInfo cvRa mI rP [])
    (A := p.leaf m₀ t) hfresh hnres ⟨_, _, _, _, rfl⟩
    (ConsHead.ofFresh hwf (fun ψ => hAcl ψ) hnres (fun _ h => nomatch h)
      (fun _ _ _ rules heq r hr => by
        injection heq with _ _ _ hrules
        rw [← hrules] at hr
        exact nomatch hr))
    (fun ψ q => AnnotTerm.liftN_eq_self _ (Term.bvarsBelow.mono (Nat.zero_le q) (hAcl ψ)) 1)
    hAparams (fun ψ ρ => (p.leaf_facts hyp ht ψ ρ).1.1) (fun ψ ρ => (p.leaf_facts hyp ht ψ ρ).1.2)
    (fun ψ => ⟨_, hread ψ⟩) ?_ ?_ ?_ ?_ hreps
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hread ψ).symm.trans hta)
    exact hRD.okTy ψ ρ
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hread ψ).symm.trans hta)
    exact (p.leaf_facts hyp ht ψ ρ).2
  · -- `caps_ok`: the cons stores a RECURSOR at the name the obligation
    -- is taken at, so the block-family branch is vacuous
    intro m₂ hac
    refine capsOk_cons_native mp (c₀ := .recInfo cvRa mI rP []) (A := p.leaf m₀ t)
      (T := cvRa.name) hfresh (ConsCrossEnv.ofNtc fun _ h => nomatch h) hpshape
      (Or.inr fun _ _ h => nomatch h)
      (fun T' cvT' caps' hf _ hres hcape => hE T' cvT' caps' hf hcape hres)
      m₂ hac ?_
    intro cvT' caps' hf _
    have hself := ConLeche.Env.find?_cons_self (ConstantInfo.recInfo cvRa mI rP []) env
    rw [show (ConstantInfo.recInfo cvRa mI rP []).name = cvRa.name from rfl] at hself
    exact nomatch (hself.symm.trans hf)
  · -- `rec_rules`: the provisioned recursor has no rules
    intro m₂ hac φ
    exact recRules_cons_fresh mp (c₀ := .recInfo cvRa mI rP []) (A := p.leaf m₀ t) hfresh
      (ConsCrossEnv.ofNtc fun _ h => nomatch h)
      (fun _ _ _ rules heq => by injection heq with _ _ _ hrules; exact hrules.symm) m₂ hac φ



/-! ## The recursors' rule-less conses, in block order -/

set_option maxHeartbeats 1600000 in
/-- **The provisioning loop** (`provisionMutualRecs`, block order): the
`k` recursors consed rule-less, member `t` with the leaf
`mutualRecAVI … t`.  Every member's stored-type reading crosses each
cons (`MutualRecData.cross`), and the leaves of the members already
consed are untouched — member `t`'s leaf mentions no sibling recursor,
so its typing is available at every step.  The caller's invariant
`Inv` rides along (`hInv` at each cons), so that `hreps` sees it at the
anonymous carrier it is taken at. -/
theorem stageMutualRecsProvisionGo (p : MutualRecParts) {env₀ : Env} {m₀ : EnvModel V env₀}
    (hyp : p.LeafHyp V m₀) {b : MutualBlock} {fms : List MutualFormerA}
    {cvRaOf : Nat → ConstantVal}
    (hAcl : ∀ t, t < p.k → ∀ ψ : Name → Nat, Term.bvarsBelow 0 (p.leaf m₀ t ψ).erase)
    (hAparams : ∀ t, t < p.k → ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ q ∈ (cvRaOf t).levelParams, ψ₁ q = ψ₂ q) → p.leaf m₀ t ψ₁ = p.leaf m₀ t ψ₂)
    (hnres : ∀ t, t < p.k → ConLeche.reservedBasisNames.contains (cvRaOf t).name = false)
    (hpshape : ∀ t, t < p.k → (cvRaOf t).name.isProjFnShape = false)
    (htyWF : ∀ t, t < p.k → (cvRaOf t).type.hasFvar = false ∧
      (cvRaOf t).type.allLevelParamsDefined (cvRaOf t).levelParams = true ∧
      (cvRaOf t).type.looseBVarsBounded 0 = true)
    (Inv : ∀ {env' : Env}, EnvModel V env' → Prop)
    (hInv : ∀ {env' : Env} (m' : EnvModel V env') (t : Nat), t < p.k →
      env'.find? (cvRaOf t).name = none → Inv m' →
      ∀ m₂ : EnvModel V ⟨.recInfo (cvRaOf t) (b.rulePrefix + (fms.getD t default).nIdx)
          b.rulePrefix [] :: env'.consts⟩,
        m₂.acval = acvalWith m'.acval (cvRaOf t).name (p.leaf m₀ t) → Inv m₂)
    (hreps : ∀ (env' : Env) (mp' : EnvModelM V μ env') (t : Nat), t < p.k →
      env'.find? (cvRaOf t).name = none → Inv mp'.base2 →
      ∀ m₂ : EnvModel V ⟨.recInfo (cvRaOf t) (b.rulePrefix + (fms.getD t default).nIdx)
          b.rulePrefix [] :: env'.consts⟩,
        m₂.acval = acvalWith mp'.base2.acval (cvRaOf t).name (p.leaf m₀ t) →
        IndRepsHead env' (.recInfo (cvRaOf t) (b.rulePrefix + (fms.getD t default).nIdx)
          b.rulePrefix []) m₂) :
    ∀ (rest : List (ConstantVal × Nat)) (env : Env) (_mp : EnvModelM V μ env),
      (∀ x ∈ rest, x.2 < p.k ∧ x.1 = cvRaOf x.2) →
      (∀ x ∈ rest, env.find? x.1.name = none) →
      (∀ t, t < p.k → (cvRaOf t).type.constsResolve env = true) →
      ConLeche.EtaFamiliesClosed env →
      (rest.map (·.1.name)).Nodup →
      (∀ t, t < p.k → MutualRecData _mp.base2 (cvRaOf t) p.nP p.k p.n (p.nIdxOf t) t p.elimL
        (p.rds m₀ t)) →
      Inv _mp.base2 →
      ∃ mp' : EnvModelM V μ (ConLeche.provisionMutualRecs b fms rest env),
        ConLeche.EtaFamiliesClosed (ConLeche.provisionMutualRecs b fms rest env) ∧
        (∀ t, t < p.k → (cvRaOf t).type.constsResolve
          (ConLeche.provisionMutualRecs b fms rest env) = true) ∧
        (∀ t, t < p.k → MutualRecData mp'.base2 (cvRaOf t) p.nP p.k p.n (p.nIdxOf t) t p.elimL
          (p.rds m₀ t)) ∧
        (∀ x ∈ rest, ∀ ψ : Name → Nat, mp'.base2.acval x.1.name ψ = p.leaf m₀ x.2 ψ) ∧
        (∀ n : Name, (∀ x ∈ rest, n ≠ x.1.name) → mp'.base2.acval n = _mp.base2.acval n) ∧
        Inv mp'.base2
  | [], env, mp, _, _, hres, hE, _, hRDs, hinv =>
    ⟨mp, hE, hres, hRDs, fun x hx => absurd hx (by simp), fun _ _ => rfl, hinv⟩
  | (cvRa, mIdx) :: rest, env, mp, hmem, hfr, hres, hE, hnd, hRDs, hinv => by
    obtain ⟨hmIdx, hcv⟩ := hmem (cvRa, mIdx) List.mem_cons_self
    dsimp only at hmIdx hcv
    subst hcv
    have hfresh : env.find? (cvRaOf mIdx).name = none := hfr _ List.mem_cons_self
    obtain ⟨hfv, hlp, hbv⟩ := htyWF mIdx hmIdx
    have hcb : ConstsBound env (cvRaOf mIdx).type :=
      constsBound_of_constsResolve _ (hres mIdx hmIdx)
    -- the cons's head and its well-formedness
    have hwf : ConLeche.EnvWF ⟨.recInfo (cvRaOf mIdx)
        (b.rulePrefix + (fms.getD mIdx default).nIdx) b.rulePrefix [] :: env.consts⟩ := by
      refine ConLeche.EnvWF.cons mp.base2.wf (ConLeche.structConstWF hfv hlp
        (Expr.constsResolve_mono (hres mIdx hmIdx)) hbv
        (fun _ _ _ heq => nomatch heq) ?_)
      intro cv mI' rP' rules heq r hr
      injection heq with _ _ _ hrules
      rw [← hrules] at hr
      exact nomatch hr
    obtain ⟨mpR, hacR⟩ := stageMutualRecProvision p mp hyp hE hmIdx hfresh
      (hnres mIdx hmIdx) (hpshape mIdx hmIdx) hwf hcb (hRDs mIdx hmIdx) (hAcl mIdx hmIdx)
      (hAparams mIdx hmIdx) (hreps env mp mIdx hmIdx hfresh hinv)
    -- the invariants at the extension
    have hcross : ∀ e : Expr, ConsCrossAt (.recInfo (cvRaOf mIdx)
        (b.rulePrefix + (fms.getD mIdx default).nIdx) b.rulePrefix []) e :=
      fun _ => ConsCrossAt.ofNtc (fun _ h => nomatch h)
    have hndc : (∀ (y : ConstantVal) (q : Nat), (y, q) ∈ rest → ¬ y.name = (cvRaOf mIdx).name) ∧
        (rest.map (·.1.name)).Nodup := by simpa using hnd
    have hneRest : ∀ x ∈ rest, x.1.name ≠ (cvRaOf mIdx).name := by
      intro x hx
      exact hndc.1 x.1 x.2 (by simpa using hx)
    have hE' : ConLeche.EtaFamiliesClosed ⟨.recInfo (cvRaOf mIdx)
        (b.rulePrefix + (fms.getD mIdx default).nIdx) b.rulePrefix [] :: env.consts⟩ :=
      hE.cons_nonind hfresh (fun _ _ heq => nomatch heq)
    have hres' : ∀ t, t < p.k → (cvRaOf t).type.constsResolve
        ⟨.recInfo (cvRaOf mIdx) (b.rulePrefix + (fms.getD mIdx default).nIdx) b.rulePrefix []
          :: env.consts⟩ = true :=
      fun t ht => Expr.constsResolve_mono (hres t ht)
    have hRDs' : ∀ t, t < p.k → MutualRecData mpR.base2 (cvRaOf t) p.nP p.k p.n (p.nIdxOf t) t
        p.elimL (p.rds m₀ t) := fun t ht =>
      (hRDs t ht).cross (c₀ := .recInfo (cvRaOf mIdx)
          (b.rulePrefix + (fms.getD mIdx default).nIdx) b.rulePrefix [])
        hfresh (hcross _) (constsBound_of_constsResolve _ (hres t ht)) mpR.base2 hacR
    obtain ⟨mp', hE'', hres'', hRDs'', hleaf'', hag, hinv'⟩ :=
      stageMutualRecsProvisionGo p hyp hAcl hAparams hnres hpshape htyWF Inv hInv hreps rest _ mpR
        (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
        (fun x hx => by
          rw [ConLeche.Env.find?_cons, if_neg (fun h => hneRest x hx h.symm)]
          exact hfr x (List.mem_cons_of_mem _ hx))
        hres' hE' (by simpa using hndc.2) hRDs'
        (hInv mp.base2 mIdx hmIdx hfresh hinv mpR.base2 hacR)
    refine ⟨mp', hE'', hres'', hRDs'', ?_, ?_, hinv'⟩
    · intro x hx ψ
      rcases List.mem_cons.mp hx with heq | hx'
      · subst heq
        show mp'.base2.acval (cvRaOf mIdx).name ψ = p.leaf m₀ mIdx ψ
        rw [hag (cvRaOf mIdx).name (fun y hy => (hneRest y hy).symm), hacR]
        show acvalWith mp.base2.acval (cvRaOf mIdx).name _ (cvRaOf mIdx).name ψ = _
        rw [acvalWith_self]
      · exact hleaf'' x hx' ψ
    · intro n hn
      rw [hag n (fun x hx => hn x (List.mem_cons_of_mem _ hx)), hacR]
      exact acvalWith_ne (hn _ List.mem_cons_self)


/-- **The recursors' provisioning stage**: the `k` recursors of the
block consed RULE-LESS onto the constructors' environment, member `t`
with the leaf `mutualRecAVI … t`. -/
theorem stageMutualRecsProvision (p : MutualRecParts) {env₀ : Env} {m₀ : EnvModel V env₀}
    (hyp : p.LeafHyp V m₀) {b : MutualBlock} {fms : List MutualFormerA}
    {cvRas : List ConstantVal} {env₂ : Env} (mp₂ : EnvModelM V μ env₂)
    (hlen : cvRas.length = p.k)
    (hAcl : ∀ t, t < p.k → ∀ ψ : Name → Nat, Term.bvarsBelow 0 (p.leaf m₀ t ψ).erase)
    (hAparams : ∀ t, t < p.k → ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ q ∈ (cvRas.getD t default).levelParams, ψ₁ q = ψ₂ q) →
      p.leaf m₀ t ψ₁ = p.leaf m₀ t ψ₂)
    (hnres : ∀ t, t < p.k → ConLeche.reservedBasisNames.contains (cvRas.getD t default).name = false)
    (hpshape : ∀ t, t < p.k → (cvRas.getD t default).name.isProjFnShape = false)
    (htyWF : ∀ t, t < p.k → (cvRas.getD t default).type.hasFvar = false ∧
      (cvRas.getD t default).type.allLevelParamsDefined
        (cvRas.getD t default).levelParams = true ∧
      (cvRas.getD t default).type.looseBVarsBounded 0 = true)
    (Inv : ∀ {env' : Env}, EnvModel V env' → Prop)
    (hInv : ∀ {env' : Env} (m' : EnvModel V env') (t : Nat), t < p.k →
      env'.find? (cvRas.getD t default).name = none → Inv m' →
      ∀ m₂ : EnvModel V ⟨.recInfo (cvRas.getD t default)
          (b.rulePrefix + (fms.getD t default).nIdx) b.rulePrefix [] :: env'.consts⟩,
        m₂.acval = acvalWith m'.acval (cvRas.getD t default).name (p.leaf m₀ t) → Inv m₂)
    (hreps : ∀ (env' : Env) (mp' : EnvModelM V μ env') (t : Nat), t < p.k →
      env'.find? (cvRas.getD t default).name = none → Inv mp'.base2 →
      ∀ m₂ : EnvModel V ⟨.recInfo (cvRas.getD t default)
          (b.rulePrefix + (fms.getD t default).nIdx) b.rulePrefix [] :: env'.consts⟩,
        m₂.acval = acvalWith mp'.base2.acval (cvRas.getD t default).name (p.leaf m₀ t) →
        IndRepsHead env' (.recInfo (cvRas.getD t default)
          (b.rulePrefix + (fms.getD t default).nIdx) b.rulePrefix []) m₂)
    (hnd : (cvRas.map (·.name)).Nodup)
    (hfresh : ∀ t, t < p.k → env₂.find? (cvRas.getD t default).name = none)
    (hres : ∀ t, t < p.k → (cvRas.getD t default).type.constsResolve env₂ = true)
    (hE : ConLeche.EtaFamiliesClosed env₂)
    (hRDs : ∀ t, t < p.k → MutualRecData mp₂.base2 (cvRas.getD t default) p.nP p.k p.n
      (p.nIdxOf t) t p.elimL (p.rds m₀ t))
    (hinv : Inv mp₂.base2) :
    ∃ mp₃ : EnvModelM V μ (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂),
      ConLeche.EtaFamiliesClosed (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂) ∧
      (∀ t, t < p.k → (cvRas.getD t default).type.constsResolve
        (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂) = true) ∧
      (∀ t, t < p.k → MutualRecData mp₃.base2 (cvRas.getD t default) p.nP p.k p.n (p.nIdxOf t) t
        p.elimL (p.rds m₀ t)) ∧
      (∀ t, t < p.k → ∀ ψ : Name → Nat,
        mp₃.base2.acval (cvRas.getD t default).name ψ = p.leaf m₀ t ψ) ∧
      (∀ n : Name, (∀ t, t < p.k → n ≠ (cvRas.getD t default).name) →
        mp₃.base2.acval n = mp₂.base2.acval n) ∧
      Inv mp₃.base2 := by
  -- an entry of `cvRas.zipIdx` is a member with its index
  have hzip : ∀ x ∈ cvRas.zipIdx, x.2 < p.k ∧ x.1 = cvRas.getD x.2 default := by
    intro x hx
    have hget : cvRas[x.2]? = some x.1 := List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using hx)
    exact ⟨by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hget).1,
      by rw [List.getD_eq_getElem?_getD, hget]; rfl⟩
  have hzipNd : (cvRas.zipIdx.map (·.1.name)).Nodup := by
    rw [show cvRas.zipIdx.map (·.1.name) = cvRas.map (·.name) from by
      rw [show (fun x : ConstantVal × Nat => x.1.name) = (fun c : ConstantVal => c.name) ∘ Prod.fst
        from rfl, ← List.map_map, List.zipIdx_map_fst]]
    exact hnd
  obtain ⟨mp₃, hE₃, hres₃, hRDs₃, hleaf₃, hag, hinv₃⟩ :=
    stageMutualRecsProvisionGo p hyp hAcl hAparams hnres hpshape htyWF Inv hInv hreps
      cvRas.zipIdx env₂ mp₂
      hzip (fun x hx => by rw [(hzip x hx).2]; exact hfresh x.2 (hzip x hx).1) hres hE hzipNd hRDs
      hinv
  refine ⟨mp₃, hE₃, hres₃, hRDs₃, ?_, ?_, hinv₃⟩
  · intro t ht ψ
    have hmem : (cvRas.getD t default, t) ∈ cvRas.zipIdx := by
      refine List.mk_mem_zipIdx_iff_getElem?.mpr ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      rfl
    exact hleaf₃ _ hmem ψ
  · intro n hn
    exact hag n fun x hx => by rw [(hzip x hx).2]; exact hn x.2 (hzip x hx).1


/-! ## The rule's spelling and its term-level law -/

namespace MutualRecParts

variable (p : MutualRecParts)

/-- **Rule `J`'s right-hand side**, as the model reads it: the λ-tower
over the rule's binder data (`mutualRuleDataAV`) with the `k`-motive
rule core (`mutualRuleCoreAV`), the inductive hypotheses firing the
member leaves. -/
@[expose] def ruleAV {env₀ : Env} (m₀ : EnvModel V env₀) (J : Nat) (cd : CtorDatumR)
    (ψ : Name → Nat) : AnnotTerm :=
  mkLamsAV (mutualRuleDataAV m₀ ψ (p.Ls ψ) p.nP p.nIdxs p.elimL (p.ppsOf 0 ψ) (p.ipss ψ)
      (p.cds ψ) p.mems p.tgts cd.2.2.1)
    (mutualRuleCoreAV (p.bb ψ) (fun q => p.leaf m₀ q ψ) (p.tgts J) p.nP p.k p.n cd.2.1 J
      cd.2.2.2.2.1 cd.2.2.2.2.2.2 cd.2.2.2.2.2.1)

/-- **The term-level ι law of rule `J` at member `t`** — the mutual
twin of `fixRecLawCore`'s conclusion, at its interface: at term spines
whose readings fit member `t`'s stored binder data with constructor
`J`'s value as the major, the member's leaf applied is the rule's
right-hand side applied, and that application is graded.

`mutualRecLawCore` (`Model/Inductives/MutualRecLaw.lean`) is the law
this names, and `mutualRecIotaCore` its `ℓ ≠ 0` half; the two are
stated at a SPLIT block frame `(p⃗, M⃗, S⃗, ı⃗, t)`, so discharging this
means splitting the spine — `fixRecLawCore` does that for the fixpoint
route inside itself, the mutual route's twin of that step is not
written yet, and until it is this is the stage's one open premise. -/
@[expose] def RuleFires (V : Type w) [SetTheory V] {env₀ : Env} (m₀ : EnvModel V env₀)
    (t J mI rP : Nat) (cdF : (Name → Nat) → CtorDatumR) : Prop :=
  ∀ (ψ : Name → Nat) (ρ : Nat → V) (xs ys : List AnnotTerm),
    xs.length = mI → ys.length = p.nP + (cdF ψ).2.1 →
    SpineFit ρ ((p.rds m₀ t ψ).map (·.2.2))
      ((xs ++ [AnnotTerm.mkAppN (sumMkAV (p.wB ψ) J (cdF ψ).2.2.1
        (((cdF ψ).2.2.1.drop p.nP).map (·.2.2)) (uChains (p.FssR ψ))) ys]).map (interp V ρ)) →
    SpineFit ρ ((cdF ψ).2.2.1.map (·.2.2)) (ys.map (interp V ρ)) →
    (∀ i, i < p.nIdxOf t →
      interp V (consList (ys.map (interp V ρ)) ρ) ((cdF ψ).2.2.2.1.getD i default)
        = interp V ρ (xs.getD (rP + i) default)) →
    interp V ρ (AnnotTerm.mkAppN (p.leaf m₀ t ψ)
        (xs ++ [AnnotTerm.mkAppN (sumMkAV (p.wB ψ) J (cdF ψ).2.2.1
          (((cdF ψ).2.2.1.drop p.nP).map (·.2.2)) (uChains (p.FssR ψ))) ys]))
      = interp V ρ (AnnotTerm.mkAppN (p.ruleAV m₀ J (cdF ψ) ψ)
          (xs.take rP ++ ys.drop p.nP)) ∧
    ((∀ a ∈ xs, WellDenotedV V ρ a) → (∀ c ∈ ys, WellDenotedV V ρ c) →
      WellDenotedV V ρ (AnnotTerm.mkAppN (p.ruleAV m₀ J (cdF ψ) ψ)
        (xs.take rP ++ ys.drop p.nP)))

end MutualRecParts

set_option maxHeartbeats 6400000 in
/-- **The mutual recursor rule's law**, at the environment holding the
whole group (`fixRecRuleLaw` at `k` motives).  The rule's right-hand
side reads to `ruleAV` (`denoteMeta_mutualRecRhs`, taken as `hread`:
every sibling recursor is stored there), its binders are graded
(`mutualRuleOk`, taken as `hRuleOk`), the parameter comparison is
VACUOUS (`paramsBlind := true`) and the `.nested` clauses are vacuous
(the fire is `.plain`); what is left is the ι equation, whose spine
premises — the recursor's fit, the constructor's fit and the index pin
— are extracted here and handed to `RuleFires`. -/
theorem mutualRecRuleLaw (p : MutualRecParts) {env₀ envE : Env} {m₀ : EnvModel V env₀}
    (m : EnvModel V envE)
    {lps : List Name} {cvRa cvC : ConstantVal} {C Tname : Name} {nF t J mI rP : Nat}
    {cdF : (Name → Nat) → CtorDatumR} {rhs : Expr} {kb eb : Bool} {rl : RecRule}
    (hmI : mI = p.nP + p.k + p.n + p.nIdxOf t) (hrP : rP = p.nP + p.k + p.n)
    (hrule : rl = ⟨C, nF, p.nP, .plain, rhs, kb, eb, true⟩)
    -- the datum is the block's `J`-th (the caller's instantiation; the
    -- law itself reads `cdF` and `p.cds` separately)
    (_hcdJ : ∀ ψ : Name → Nat, (p.cds ψ)[J]? = some (cdF ψ))
    (hclen : ∀ ψ : Name → Nat, (cdF ψ).2.2.1.length = p.nP + nF)
    (hcdNF : ∀ ψ : Name → Nat, (cdF ψ).2.1 = nF)
    (hclenE : ∀ ψ : Name → Nat, (cdF ψ).2.2.2.1.length = p.nIdxOf t)
    (hlpsC : cvC.levelParams = lps)
    (hfC : envE.find? C = some (.ctorInfo cvC p.nP nF))
    (hleafR : ∀ ψ : Name → Nat, m.acval cvRa.name ψ = p.leaf m₀ t ψ)
    (hleafC : ∀ ψ : Name → Nat, m.acval C ψ = sumMkAV (p.wB ψ) J (cdF ψ).2.2.1
      (((cdF ψ).2.2.1.drop p.nP).map (·.2.2)) (uChains (p.FssR ψ)))
    (hdataParams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ lps, ψ₁ q = ψ₂ q) →
      cdF ψ₁ = cdF ψ₂ ∧ p.FssR ψ₁ = p.FssR ψ₂ ∧ p.wB ψ₁ = p.wB ψ₂)
    (hRD : MutualRecData m cvRa p.nP p.k p.n (p.nIdxOf t) t p.elimL (p.rds m₀ t))
    (hCread : ∀ ψ : Name → Nat, denoteMeta m.acval envE ψ 0 cvC.type
      = some (mkPisAV (cdF ψ).2.2.1 (ctorBodyAVI m Tname p.nP nF ψ (cdF ψ).2.2.2.1)))
    (hread : ∀ ψ : Name → Nat, denoteMeta m.acval envE ψ 0 rhs = some (p.ruleAV m₀ J (cdF ψ) ψ))
    (hRuleOk : ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenotedV V ρ (p.ruleAV m₀ J (cdF ψ) ψ))
    (hfires : p.RuleFires V m₀ t J mI rP cdF)
    (φ : Name → Nat) :
    RecRuleLaw m φ cvRa.name cvRa mI rP rl := by
  subst hrule
  subst hmI
  subst hrP
  refine ⟨by omega, fun us hus => ?_⟩
  dsimp only
  have hinstR : ∀ (d : Nat) (e : Expr),
      denoteMeta m.acval envE φ d (e.instantiateLevelParams cvRa.levelParams us)
        = denoteMeta m.acval envE (Level.substFn φ cvRa.levelParams us) d e :=
    fun d e => denoteMeta_instLevels (acvalParamsAt_of_core m) φ d e
  generalize hψR : Level.substFn φ cvRa.levelParams us = ψR at hinstR ⊢
  refine ⟨_, by rw [hinstR, hread ψR], hRuleOk ψR, fun _ _ h => absurd h (by simp), ?_⟩
  intro cvj cnP cnF hfcj usj ρ xs ys TVa TVja restR restC hxl hyl husjl hψ _ _ hidx hTVa
    hTVja hfitR hfitC
  -- the constructor found is the block's
  obtain ⟨rfl, rfl, rfl⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj (hfC.symm.trans hfcj))
  -- the level assignments agree on the block's parameters
  have hagree : ∀ q ∈ lps, Level.substFn φ cvC.levelParams usj q = ψR q := by
    have h := hψ
    simp only [ConLeche.recFireComparands] at h
    rw [hlpsC] at h
    rw [hlpsC, ← hψR]
    exact substFn_agree_of_comparand h
  generalize hψC : Level.substFn φ cvC.levelParams usj = ψC at hagree hTVja hfitC hfitR ⊢
  obtain ⟨hcdEq, hFssEq, hwEq⟩ := hdataParams ψC ψR hagree
  -- the recursor type's reading
  have hTVa' : TVa = mkPisAV (p.rds m₀ t ψR) (p.conc t) := by
    have h := hTVa
    rw [hinstR] at h
    exact Option.some.inj (h.symm.trans (hRD.read ψR))
  -- the constructor type's reading
  have hTVja' : TVja = mkPisAV (cdF ψR).2.2.1
      (ctorBodyAVI m Tname p.nP nF ψC (cdF ψR).2.2.2.1) := by
    have h := hTVja
    rw [denoteMeta_instLevels (acvalParamsAt_of_core m) φ 0 cvC.type, hψC] at h
    have h2 := Option.some.inj (h.symm.trans (hCread ψC))
    rw [h2, hcdEq]
  -- the constructor's leaf at this assignment
  have hleafC₂ : m.acval C ψC = sumMkAV (p.wB ψR) J (cdF ψR).2.2.1
      (((cdF ψR).2.2.1.drop p.nP).map (·.2.2)) (uChains (p.FssR ψR)) := by
    rw [hleafC ψC, hcdEq, hwEq, hFssEq]
  -- the recursor's spine fit
  have hspR : SpineFit ρ ((p.rds m₀ t ψR).map (·.2.2))
      ((xs ++ [AnnotTerm.mkAppN (sumMkAV (p.wB ψR) J (cdF ψR).2.2.1
        (((cdF ψR).2.2.1.drop p.nP).map (·.2.2)) (uChains (p.FssR ψR))) ys]).map
        (interp V ρ)) := by
    have hst := stripPisAV_mkPisAV (p.rds m₀ t ψR) (p.conc t)
    rw [hRD.len ψR] at hst
    have htele := piTeleAV_of_stripPisAV hst
    have hfit := hfitR
    rw [hTVa'] at hfit
    try simp only [RecRule.ctor] at hfit
    rw [hleafC₂] at hfit
    have hchain := teleFitPA_to_chain (p.nP + p.k + p.n + p.nIdxOf t + 1) htele
      (by simp [hxl]) hfit
    refine spineFit_of_chain (by simp [hxl, hRD.len ψR]) ?_
    intro q hq
    have := hchain q (by simpa [hRD.len ψR] using hq)
    simpa [hRD.len ψR] using this
  -- the constructor's spine fit
  have hstC := stripPisAV_mkPisAV (cdF ψR).2.2.1
    (ctorBodyAVI m Tname p.nP nF ψC (cdF ψR).2.2.2.1)
  rw [hclen ψR] at hstC
  have hteleC := piTeleAV_of_stripPisAV hstC
  have hspC : SpineFit ρ ((cdF ψR).2.2.1.map (·.2.2)) (ys.map (interp V ρ)) := by
    have hfit := hfitC
    rw [hTVja'] at hfit
    have hchain := teleFitPA_to_chain (p.nP + nF) hteleC (by simpa [hcdNF ψC] using hyl) hfit
    refine spineFit_of_chain (by simp [hyl, hclen ψR]) ?_
    intro q hq
    have := hchain q (by simpa [hclen ψR] using hq)
    simpa [hclen ψR] using this
  -- the index pin
  have hpin : ∀ i, i < p.nIdxOf t →
      interp V (consList (ys.map (interp V ρ)) ρ) ((cdF ψR).2.2.2.1.getD i default)
        = interp V ρ (xs.getD (p.nP + p.k + p.n + i) default) := by
    intro i hi
    obtain ⟨Ha, cargsa, hrestEq, hcarLen, hcarInterp⟩ := hidx
    rcases hcarLen with hcase | hcarLen
    · omega
    have hrest : restC = ConLeche.Model.AnnotTerm.instSeq ys (p.nP + nF - 1)
        (ctorBodyAVI m Tname p.nP nF ψC (cdF ψR).2.2.2.1) := by
      have hfit := hfitC
      rw [hTVja'] at hfit
      exact teleFitPA_rest_eq (p.nP + nF) hteleC (by simpa [hcdNF ψC] using hyl) hfit
    have hrest2 : AnnotTerm.mkAppN Ha cargsa
        = AnnotTerm.mkAppN (ConLeche.Model.AnnotTerm.instSeq ys (p.nP + nF - 1)
            (m.acval Tname ψC))
            ((paramBvars p.nP nF ++ (cdF ψR).2.2.2.1).map
              (ConLeche.Model.AnnotTerm.instSeq ys (p.nP + nF - 1))) := by
      rw [← hrestEq, hrest]
      unfold ctorBodyAVI
      rw [instSeqAV_mkAppN]
    obtain ⟨-, hcargs⟩ := AnnotTerm.mkAppN_inj hrest2
      (by simp [hcarLen, paramBvars, hclenE ψR])
    have hcel : cargsa.getD (p.nP + i) default
        = ConLeche.Model.AnnotTerm.instSeq ys (p.nP + nF - 1)
            ((cdF ψR).2.2.2.1.getD i default) := by
      have h1 := congrArg (fun l => l[p.nP + i]?) hcargs
      simp only [List.getElem?_map, List.getElem?_append_right
        (show (paramBvars p.nP nF).length ≤ p.nP + i by simp [paramBvars]),
        show (paramBvars p.nP nF).length = p.nP by simp [paramBvars],
        Nat.add_sub_cancel_left] at h1
      rw [List.getD_eq_getElem?_getD, h1, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [hclenE ψR]; omega), Option.map_some, Option.getD_some,
        Option.getD_some]
    have hcar := hcarInterp i (by omega)
    rw [hcel, show p.nP + nF - 1 = ys.length - 1 from by rw [hyl], interp_instSeq] at hcar
    rw [← hcar]
    unfold chain
    rw [consN_eq_consList]
  -- the law
  have hlaw := hfires ψR ρ xs ys hxl (by rw [hyl, hcdNF ψR]) hspR hspC hpin
  try simp only [RecRule.ctor, RecRule.ctorParams] at hlaw ⊢
  rw [hleafR ψR, hleafC₂]
  exact hlaw


/-! ## The provision and the store, as a swap -/

section Swap

variable {b : MutualBlock} {fms : List MutualFormerA}
  {rulesOf : List (List (MutualCtor × Expr))} {env₂ : Env}

/-- The head the store conses for entry `(cvRa, mIdx)`. -/
@[expose] def storeHead (env₂ : Env) (b : MutualBlock) (fms : List MutualFormerA)
    (rulesOf : List (List (MutualCtor × Expr))) (x : ConstantVal × Nat) : ConstantInfo :=
  .recInfo x.1 (b.rulePrefix + (fms.getD x.2 default).nIdx) b.rulePrefix
    (ConLeche.mutualRules env₂.find? x.1.name b.nP
      (b.rulePrefix + (fms.getD x.2 default).nIdx) b.rulePrefix x.1.type (rulesOf.getD x.2 []))

/-- A lookup past a cons whose head carries another name. -/
theorem find?_cons_of_name_ne {c : ConstantInfo} {env : Env} {n : Name} (h : ¬ c.name = n) :
    (Env.mk (c :: env.consts)).find? n = env.find? n := by
  rw [ConLeche.Env.find?_cons, if_neg h]

/-- **The provision and the store are a shape-level swap**: the same
`k` names, in the same order, on lookup-comparable environments,
differing only in their rule lists. -/
theorem swapShList_provision_store :
    ∀ (l : List (ConstantVal × Nat)) {env env' : Env},
      ConLeche.SwapShList env.consts env'.consts →
      ConLeche.SwapShList (ConLeche.provisionMutualRecs b fms l env).consts
        (ConLeche.storeMutualRecs env₂ b fms rulesOf l env').consts
  | [], _, _, h => h
  | (cvRa, mIdx) :: rest, env, env', h => by
    simp only [ConLeche.provisionMutualRecs, ConLeche.storeMutualRecs]
    exact swapShList_provision_store rest
      (ConLeche.SwapShList.cons (Or.inr ⟨cvRa, _, _, _, rfl, rfl⟩) h)

/-- **The swap sits at no reserved basis name**: the only entries the
store changes are the block's recursors. -/
theorem swapNResS_provision_store :
    ∀ (l : List (ConstantVal × Nat)) {env env' : Env},
      (∀ x ∈ l, ConLeche.reservedBasisNames.contains x.1.name = false) →
      SwapNResS env env' →
      SwapNResS (ConLeche.provisionMutualRecs b fms l env)
        (ConLeche.storeMutualRecs env₂ b fms rulesOf l env')
  | [], _, _, _, h => h
  | (cvRa, mIdx) :: rest, env, env', hres, h => by
    simp only [ConLeche.provisionMutualRecs, ConLeche.storeMutualRecs]
    refine swapNResS_provision_store rest (fun x hx => hres x (List.mem_cons_of_mem _ hx)) ?_
    intro n cv mI rP rules h₀ h₃
    by_cases hn : cvRa.name = n
    · refine Or.inr ?_
      show ConLeche.reservedBasisNames.contains n = false
      rw [← hn]
      exact hres (cvRa, mIdx) List.mem_cons_self
    · rw [find?_cons_of_name_ne (c := .recInfo cvRa
        (b.rulePrefix + (fms.getD mIdx default).nIdx) b.rulePrefix []) hn] at h₀
      rw [find?_cons_of_name_ne (c := .recInfo cvRa
        (b.rulePrefix + (fms.getD mIdx default).nIdx) b.rulePrefix
        (ConLeche.mutualRules env₂.find? cvRa.name b.nP
          (b.rulePrefix + (fms.getD mIdx default).nIdx) b.rulePrefix cvRa.type
          (rulesOf.getD mIdx []))) hn] at h₃
      exact h n cv mI rP rules h₀ h₃

/-- The store's lookups: the base environment's, or one of the `k`
stored recursors. -/
theorem storeMutualRecs_find?_inv :
    ∀ {l : List (ConstantVal × Nat)} {env : Env} {n : Name} {c : ConstantInfo},
      (ConLeche.storeMutualRecs env₂ b fms rulesOf l env).find? n = some c →
      env.find? n = some c ∨ ∃ x ∈ l, c = storeHead env₂ b fms rulesOf x ∧ x.1.name = n
  | [], _, _, _, h => Or.inl h
  | (cvRa, mIdx) :: rest, env, n, c, h => by
    simp only [ConLeche.storeMutualRecs] at h
    rcases storeMutualRecs_find?_inv h with h' | ⟨x, hx, hc, hn⟩
    · rw [ConLeche.Env.find?_cons] at h'
      split at h'
      · next hname =>
        exact Or.inr ⟨(cvRa, mIdx), List.mem_cons_self, (Option.some.inj h').symm, hname⟩
      · exact Or.inl h'
    · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, hc, hn⟩

/-- The provision's lookups, at a name none of the `k` recursors
carries: the base environment's. -/
theorem provisionMutualRecs_find?_of_ne :
    ∀ {l : List (ConstantVal × Nat)} {env : Env} {n : Name},
      (∀ x ∈ l, n ≠ x.1.name) →
      (ConLeche.provisionMutualRecs b fms l env).find? n = env.find? n
  | [], _, _, _ => rfl
  | (cvRa, mIdx) :: rest, env, n, hne => by
    simp only [ConLeche.provisionMutualRecs]
    rw [provisionMutualRecs_find?_of_ne (fun x hx => hne x (List.mem_cons_of_mem _ hx)),
      ConLeche.Env.find?_cons,
      if_neg (fun hh => hne (cvRa, mIdx) List.mem_cons_self hh.symm)]

/-- **The three remaining syntactic environment facts survive the
swap** (`swapEnvFacts`'s non-`EnvWF` half, with the `RuleFacts`
premise replaced by the store's own rule data). -/
theorem swapFacts_of_shList {env₀ env₃ : Env} {cval : TConstVal}
    (hsw : ConLeche.SwapShList env₀.consts env₃.consts)
    (hnres : SwapNResS env₀ env₃)
    (hctors₀ : ConLeche.RecCtorsStored env₀)
    (hbp₀ : BasisPinnedTT env₀ cval)
    (hproj₀ : ProjOkT env₀)
    (hnew : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      env₃.find? n = some (.recInfo cv mI rP rules) →
      env₀.find? n = some (.recInfo cv mI rP rules) ∨
      ∀ r ∈ rules,
        (∃ cvj cnP cnF, env₀.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF)) ∧
        (r.k = true → ConLeche.recRuleKOf env₀.find? r.ctor = true) ∧
        (r.eta = true → ConLeche.recRuleEtaOf env₀.find? n r.ctor = true)) :
    ConLeche.RecCtorsStored env₃ ∧ BasisPinnedTT env₃ cval ∧ ProjOkT env₃ := by
  have hcg : ConLeche.SwapCongr env₀ env₃ := ConLeche.SwapShList.congr hsw
  have hcorr := ConLeche.swapSh_find?_corr hsw
  have hsame : ∀ (n : Name) (ci : ConstantInfo),
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      (env₃.find? n = some ci ↔ env₀.find? n = some ci) :=
    fun n ci hnr => ⟨fun h => hcg.findDown n ci h hnr, fun h => hcg.findUp n ci h hnr⟩
  have hkeep : ∀ (m : Name) (ci : ConstantInfo),
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      env₀.find? m = some ci → env₃.find? m = some ci :=
    fun m ci hnr hf => hcg.findUp m ci hf hnr
  refine ⟨?_, ?_, ?_⟩
  · -- `RecCtorsStored`
    intro n cv mI rP rules hf r hr
    rcases hnew n cv mI rP rules hf with hf₀ | hfacts
    · obtain ⟨⟨cvj, cnP, cnF, hfc⟩, hk, he⟩ := hctors₀ n cv mI rP rules hf₀ r hr
      exact ⟨⟨cvj, cnP, cnF, hkeep _ _
          (fun _ _ _ _ hcon => ConstantInfo.noConfusion hcon) hfc⟩,
        fun hb => recRuleKOf_mono hkeep (hk hb),
        fun hb => recRuleEtaOf_mono hkeep (he hb)⟩
    · obtain ⟨⟨cvj, cnP, cnF, hfc⟩, hk, he⟩ := hfacts r hr
      exact ⟨⟨cvj, cnP, cnF, hkeep _ _
          (fun _ _ _ _ hcon => ConstantInfo.noConfusion hcon) hfc⟩,
        fun hb => recRuleKOf_mono hkeep (hk hb),
        fun hb => recRuleEtaOf_mono hkeep (he hb)⟩
  · -- `BasisPinnedTT`: a genuinely swapped entry is never reserved
    intro n ci hf hres
    have hf₀ : env₀.find? n = some ci := by
      rcases hcorr n with heq | ⟨cv, mI, rP, rules, h₀, h₃, -⟩
      · rw [← heq]; exact hf
      · rcases hnres n cv mI rP rules h₀ h₃ with rfl | hnr
        · rw [h₃] at hf
          obtain rfl := Option.some.inj hf
          exact h₀
        · rw [hnr] at hres
          exact nomatch hres
    exact hbp₀ n ci hf₀ hres
  · -- `ProjOkT`: projection tables are untouched
    intro n tbl hf i hi
    exact ConLeche.TowerHead.mono (fun n' ci hnr hf' => (hsame n' ci hnr).mpr hf')
      (hproj₀ n tbl ((hsame _ _ (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf) i hi)

end Swap


/-! ## The store: the swap -/

set_option maxHeartbeats 1600000 in
/-- **The recursors' store stage**: the carrier at the provisioned
environment crosses to the environment holding the SAME `k` recursors
WITH their rules (`storeMutualRecs`), by `EnvModelM.swapP`.

`EnvWF` at the store is `mutual_recs_wf`'s (a rule is scoped at the
provision, and the store finds every name the provision finds); the
other three syntactic facts are transported (`swapFacts_of_shList`),
the representation clause is the caller's (task #280 — `declMutual`
assembles it from the block's representations at the PROVISIONED
carrier through `mutualIndReps_of`), and the rule rows are the prefix's own — transported by `RecRuleLaw.swapP` — plus
the block's, which `mutualRecRuleLaw` supplies. -/
theorem stageMutualRecsStore (p : MutualRecParts)
    {b : MutualBlock} {fms : List MutualFormerA} {cvRas : List ConstantVal}
    {rulesOf : List (List (MutualCtor × Expr))} {env₂ : Env}
    {formers4 : List MutualFormer} {ctors4 : List MutualCtor4}
    {streamRecs : Option (List (ConstantVal × List RecRule))} {F : Nat}
    (henv₂ : ConLeche.EnvWF env₂)
    (hrectys : ConLeche.checkMutualRecTys (ConLeche.fueledOps μ F) env₂ b formers4 ctors4
      streamRecs b.k = .ok cvRas)
    (hrules : ConLeche.checkMutualAllRules (m := ConLeche.CheckM)
      (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂) b formers4 ctors4 streamRecs b.k
      = .ok rulesOf)
    (mpP : EnvModelM V μ (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂))
    (hk : cvRas.length = p.k)
    (hfresh : ∀ t, t < p.k → env₂.find? (cvRas.getD t default).name = none)
    (hnres : ∀ t, t < p.k →
      ConLeche.reservedBasisNames.contains (cvRas.getD t default).name = false)
    -- every stored rule's constructor is stored at the constructors'
    -- environment (the block's own constructors, consed there)
    (hctorStored : ∀ t, t < p.k → ∀ r ∈ ConLeche.mutualRules env₂.find?
        (cvRas.getD t default).name b.nP (b.rulePrefix + (fms.getD t default).nIdx)
        b.rulePrefix (cvRas.getD t default).type (rulesOf.getD t []),
      ∃ cvj cnP cnF, env₂.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF))
    -- the block's own rule rows at the FINAL carrier (`mutualRecRuleLaw`)
    (hlaws : ∀ m₃ : EnvModel V (ConLeche.storeMutualRecs env₂ b fms rulesOf cvRas.zipIdx env₂),
      m₃.acval = mpP.base2.acval → ∀ (φ : Name → Nat) (t : Nat), t < p.k →
      ∀ rl ∈ ConLeche.mutualRules env₂.find? (cvRas.getD t default).name b.nP
          (b.rulePrefix + (fms.getD t default).nIdx) b.rulePrefix
          (cvRas.getD t default).type (rulesOf.getD t []),
        RecRule.fire rl ≠ .inert →
        RecRuleLaw m₃ φ (cvRas.getD t default).name (cvRas.getD t default)
          (b.rulePrefix + (fms.getD t default).nIdx) b.rulePrefix rl)
    -- the representation clause at the store (task #280)
    (hreps : ∀ m₃ : EnvModel V (ConLeche.storeMutualRecs env₂ b fms rulesOf cvRas.zipIdx env₂),
      m₃.acval = mpP.base2.acval → IndReps m₃) :
    ∃ mp₃ : EnvModelM V μ (ConLeche.storeMutualRecs env₂ b fms rulesOf cvRas.zipIdx env₂),
      mp₃.base2.acval = mpP.base2.acval ∧ mp₃.base2.cvalE = mpP.base2.cvalE := by
  -- the block's entries
  have hzip : ∀ x ∈ cvRas.zipIdx, x.2 < p.k ∧ x.1 = cvRas.getD x.2 default := by
    intro x hx
    have hget : cvRas[x.2]? = some x.1 := List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using hx)
    exact ⟨by rw [← hk]; exact (List.getElem?_eq_some_iff.mp hget).1,
      by rw [List.getD_eq_getElem?_getD, hget]; rfl⟩
  -- the swap
  have hsw : ConLeche.SwapShList (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂).consts
      (ConLeche.storeMutualRecs env₂ b fms rulesOf cvRas.zipIdx env₂).consts :=
    swapShList_provision_store _ (ConLeche.SwapShList.of_eq env₂.consts)
  have hnresS : SwapNResS (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂)
      (ConLeche.storeMutualRecs env₂ b fms rulesOf cvRas.zipIdx env₂) :=
    swapNResS_provision_store _
      (fun x hx => by rw [(hzip x hx).2]; exact hnres x.2 (hzip x hx).1)
      (SwapNResS.of_eq env₂)
  have hcg := ConLeche.SwapShList.congr hsw
  -- the constructors' environment sits inside the provision
  have hmono : ∀ (n : Name) (c : ConstantInfo), env₂.find? n = some c →
      (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂).find? n = some c := by
    intro n c h
    rw [provisionMutualRecs_find?_of_ne ?ne]
    · exact h
    case ne =>
      intro x hx hn
      have := hfresh x.2 (hzip x hx).1
      rw [← (hzip x hx).2, ← hn, h] at this
      exact nomatch this
  have hkeep₂ : ∀ (n : Name) (ci : ConstantInfo),
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) → env₂.find? n = some ci →
      (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂).find? n = some ci :=
    fun n ci _ h => hmono n ci h
  -- the store's own rules: their constructors and their rescue bits
  have hnew : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      (ConLeche.storeMutualRecs env₂ b fms rulesOf cvRas.zipIdx env₂).find? n
        = some (.recInfo cv mI rP rules) →
      (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂).find? n
        = some (.recInfo cv mI rP rules) ∨
      ∀ r ∈ rules,
        (∃ cvj cnP cnF, (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂).find?
          (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF)) ∧
        (r.k = true → ConLeche.recRuleKOf
          (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂).find? r.ctor = true) ∧
        (r.eta = true → ConLeche.recRuleEtaOf
          (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂).find? n r.ctor = true) := by
    intro n cv mI rP rules hf
    rcases storeMutualRecs_find?_inv hf with h₂ | ⟨x, hx, hc, hn⟩
    · exact Or.inl (hmono _ _ h₂)
    right
    obtain ⟨rfl, rfl, rfl, rfl⟩ := ConstantInfo.recInfo.inj hc
    obtain ⟨hxk, hxv⟩ := hzip x hx
    intro r hr
    rw [hxv] at hr
    obtain ⟨hkb, heb⟩ := ConLeche.mutualRules_bits hr
    obtain ⟨cvj, cnP, cnF, hfc⟩ := hctorStored x.2 hxk r hr
    refine ⟨⟨cvj, cnP, cnF, hmono _ _ hfc⟩, fun hb => ?_, fun hb => ?_⟩
    · exact recRuleKOf_mono hkeep₂ (by rw [← hkb]; exact hb)
    · rw [← hn, hxv]
      exact recRuleEtaOf_mono hkeep₂ (by rw [← heb]; exact hb)
  obtain ⟨hctors₃, hbp₃, hproj₃⟩ :=
    swapFacts_of_shList hsw hnresS mpP.base2.rec_ctors mpP.base2.basis_pinnedL
      mpP.base2.proj_ok hnew
  -- the rule rows at the swapped carrier
  have hrecP : ∀ m₃ : EnvModel V (ConLeche.storeMutualRecs env₂ b fms rulesOf cvRas.zipIdx env₂),
      m₃.acval = mpP.base2.acval → ∀ φ : Name → Nat, RecRules m₃ φ := by
    intro m₃ hac φ n cv mI rP rules hf rl hrl hfire
    rcases storeMutualRecs_find?_inv hf with h₂ | ⟨x, hx, hc, hn⟩
    · exact RecRuleLaw.swapP hcg hac
        (mpP.rec_rules φ n cv mI rP rules (hmono _ _ h₂) rl hrl hfire)
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := ConstantInfo.recInfo.inj hc
      obtain ⟨hxk, hxv⟩ := hzip x hx
      rw [← hn, hxv]
      rw [hxv] at hrl
      exact hlaws m₃ hac φ x.2 hxk rl hrl hfire
  exact EnvModelM.swapP mpP hsw (ConLeche.mutual_recs_wf henv₂ hrectys hrules) hctors₃ hbp₃
    hproj₃ hrecP hreps


/-! ## The leaf is closed -/

omit [SetTheory V] in
/-- A lifted field chain is bounded at the lifted depth. -/
theorem liftFields_below {n : Nat} :
    ∀ {Fs : List AnnotTerm} {K k : Nat}, FieldsBelow K Fs → FieldsBelow (K + n) (liftFields n k Fs)
  | [], _, _, _ => trivial
  | F :: Fs, K, k, h => ⟨by
      rw [AnnotTerm.erase_liftN]
      exact VExprAux.bvarsBelow_liftN n _ K k h.1, by
      have := liftFields_below (n := n) (Fs := Fs) (K := K + 1) (k := k + 1) h.2
      rwa [show K + 1 + n = K + n + 1 from by omega] at this⟩

omit [SetTheory V] in
/-- Binder data built from a bounded field chain with constant bits. -/
theorem domsBelow_mapBits {u v : Nat} :
    ∀ {Fs : List AnnotTerm} {K : Nat}, FieldsBelow K Fs →
      DomsBelow K (Fs.map fun F => (u, v, F))
  | [], _, _ => trivial
  | _ :: _, _, h => ⟨h.1, domsBelow_mapBits h.2⟩

omit [SetTheory V] in
/-- **Tag minor `m'`'s type is closed** at its K-frame position. -/
theorem tagMinorTyAV_below {ℓ W w m' nP : Nat} {Idss : List (List AnnotTerm)}
    (hIds : ∀ Ids ∈ Idss, FieldsBelow nP Ids) :
    Term.bvarsBelow (nP + (1 + m')) (tagMinorTyAV ℓ W w m' Idss : AnnotTerm).erase := by
  have hIdsm : FieldsBelow nP (Idss.getD m' []) := by
    rw [List.getD_eq_getElem?_getD]
    cases hm : Idss[m']? with
    | none => exact trivial
    | some Ids => exact hIds Ids (List.mem_of_getElem? hm)
  unfold tagMinorTyAV
  refine mkPisAV_below_of (domsBelow_mapBits (liftFields_below (n := 1 + m') hIdsm)) ?_
  rw [List.length_map, liftFields_length]
  simp only [AnnotTerm.erase_app, Term.bvarsBelow]
  refine ⟨?_, ?_⟩
  · show (Idss.getD m' []).length + m' < nP + (1 + m') + (Idss.getD m' []).length
    omega
  · have := tagTupleAV_below (W := W) (nP := nP) (m := m')
      (d := 1 + m' + (Idss.getD m' []).length) (Idss := Idss)
      (Es := teleVarsAV (Idss.getD m' []).length) hIds (fun E hE => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hE
        have := List.mem_range.mp hq
        show (Idss.getD m' []).length - 1 - q < nP + (1 + m' + (Idss.getD m' []).length)
        omega)
    exact Term.bvarsBelow.mono (by omega) this

omit [SetTheory V] in
/-- **The tag recursor's binder data is closed** at the parameter frame. -/
theorem dispDs_below {ℓ W w k nP : Nat} {Idss : List (List AnnotTerm)}
    (hIds : ∀ Ids ∈ Idss, FieldsBelow nP Ids) :
    DomsBelow nP (dispDs ℓ W w k Idss) := by
  refine ⟨?_, ?_⟩
  · show Term.bvarsBelow nP (tagMotTyAV ℓ W w Idss : AnnotTerm).erase
    unfold tagMotTyAV
    exact ⟨tagTyAV_below hIds, trivial⟩
  · refine domsBelow_of_getD (K := nP + 1) fun q hq => ?_
    rw [List.length_map, List.length_range] at hq
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (show q < (List.range k).length from by simpa using hq),
      List.getElem_range]
    have := tagMinorTyAV_below (ℓ := ℓ) (W := W) (w := w) (m' := q) (nP := nP) hIds
    exact Term.bvarsBelow.mono (by omega) this

omit [SetTheory V] in
/-- **The tag recursor is closed** at the parameter frame: its binder
data is, and its residual is the tag's case split on chains bounded
there. -/
theorem dispTowerAV_below {ℓ W w k nP : Nat} {Idss : List (List AnnotTerm)}
    (hIds : ∀ Ids ∈ Idss, FieldsBelow nP Ids) :
    Term.bvarsBelow nP (dispTowerAV ℓ W w k Idss : AnnotTerm).erase := by
  have hchains : ∀ Fs' ∈ rChains (k + 1) 0 Idss (List.replicate k []),
      FieldsBelow (nP + (k + 1)) Fs' :=
    rChains_below (Nat.zero_le _) hIds (fun j _ => by
      rw [List.getD_eq_getElem?_getD]
      cases hj : (List.replicate k ([] : List AnnotTerm))[j]? with
      | none => exact ⟨rfl, fun E hE => nomatch hE⟩
      | some Es =>
        have : Es = [] := by
          have := List.getElem?_eq_some_iff.mp hj
          rw [← this.2]
          exact List.getElem_replicate _
        subst this
        exact ⟨rfl, fun E hE => nomatch hE⟩)
  refine mkLamsC_below (dispDs_below hIds) ?_
  rw [show (dispDs ℓ W w k Idss).length = k + 1 from by simp [dispDs]]
  unfold dispLamAV dispBodyAV
  simp only [AnnotTerm.erase_lam, AnnotTerm.erase_app, Term.bvarsBelow]
  refine ⟨?_, ?_, ?_⟩
  · rw [AnnotTerm.erase_liftN]
    have := VExprAux.bvarsBelow_liftN (k + 1) (tagTyAV W Idss : AnnotTerm).erase nP 0
      (tagTyAV_below hIds)
    exact Term.bvarsBelow.mono (by omega) this
  · have := caseRecAVI_below (ℓ := dispLevel w ℓ) (w := W) (K := nP + (k + 1))
      (Fss := rChains (k + 1) 0 Idss (List.replicate k []))
      (ar := fun j => (Idss.getD j []).length) (ihArgs := fun _ _ => [])
      (n := k) (nIdx := 0) (by omega) hchains (fun _ _ a ha => nomatch ha) k
      (D := 1) (j := 0) (kx := .fst (.bvar 0)) (by
        show Term.bvarsBelow (nP + (k + 1) + 1) (Term.fst (Term.bvar 0))
        show 0 < nP + (k + 1) + 1
        omega)
    exact this
  · show Term.bvarsBelow (nP + (k + 1) + 1) (Term.snd (Term.bvar 0))
    show 0 < nP + (k + 1) + 1
    omega


omit [SetTheory V] in
/-- **The tag motive is closed** at the parameter frame: the tag type,
the auxiliary functor and the auxiliary tupler all are. -/
theorem tagMotAV_below {ℓ W w nP : Nat} {Idss : List (List AnnotTerm)}
    {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
    {Eiss' : List (List (List AnnotTerm))} {Fss Ess' : List (List AnnotTerm)}
    (hIds : ∀ Ids ∈ Idss, FieldsBelow nP Ids)
    (hchains : ∀ chain ∈ chainsXI W (auxIds W Idss) 1 rss tlss Eiss' Fss Ess',
      FieldsBelow (nP + 2) chain) :
    Term.bvarsBelow nP (tagMotAV ℓ W w Idss rss tlss Eiss' Fss Ess' : AnnotTerm).erase := by
  have hauxB : FieldsBelow nP (auxIds W Idss) := ⟨tagTyAV_below hIds, trivial⟩
  unfold tagMotAV auxAtAV
  simp only [AnnotTerm.erase_lam, AnnotTerm.erase_pi, AnnotTerm.erase_sort, AnnotTerm.erase_app,
    Term.bvarsBelow]
  refine ⟨tagTyAV_below hIds, ⟨?_, ?_⟩, trivial⟩
  · rw [AnnotTerm.erase_liftN]
    exact VExprAux.bvarsBelow_liftN 1 _ nP 0 (fixBodyAVI_below hauxB hchains)
  · rw [AnnotTerm.erase_mkAppN]
    refine VExprAux.bvarsBelow_mkAppN ?_ ?_
    · rw [AnnotTerm.erase_liftN]
      exact VExprAux.bvarsBelow_liftN 1 _ nP 0 (tuplerAV_below hauxB)
    · intro a ha
      obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp ha
      rw [List.mem_singleton] at ha₀
      subst ha₀
      show 0 < nP + 1
      omega


omit [SetTheory V] in
/-- **The motive dispatch is closed** at the frame it sits in: the tag
recursor and the tag motive are scoped at the parameters, and the
block's motive variables sit inside the frame. -/
theorem motDispAV_below {ℓ W w D mOff k nP : Nat} {Idss : List (List AnnotTerm)}
    {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
    {Eiss' : List (List (List AnnotTerm))} {Fss Ess' : List (List AnnotTerm)}
    (hmOff : mOff + k ≤ D)
    (hTower : Term.bvarsBelow nP (dispTowerAV ℓ W w k Idss).erase)
    (hMot : Term.bvarsBelow nP (tagMotAV ℓ W w Idss rss tlss Eiss' Fss Ess').erase) :
    Term.bvarsBelow (nP + D)
      (motDispAV ℓ W w D mOff k Idss rss tlss Eiss' Fss Ess' : AnnotTerm).erase := by
  unfold motDispAV
  rw [AnnotTerm.erase_mkAppN]
  refine VExprAux.bvarsBelow_mkAppN ?_ ?_
  · rw [AnnotTerm.erase_liftN]
    exact VExprAux.bvarsBelow_liftN D _ nP 0 hTower
  · intro a ha
    obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp ha
    rcases List.mem_cons.mp ha₀ with rfl | ha'
    · rw [AnnotTerm.erase_liftN]
      exact VExprAux.bvarsBelow_liftN D _ nP 0 hMot
    · obtain ⟨m', hm', rfl⟩ := List.mem_map.mp ha'
      have := List.mem_range.mp hm'
      show mOff + k - 1 - m' < nP + D
      omega

omit [SetTheory V] in
/-- **The member recursor's body is closed** under its binder tower:
the auxiliary recursor's leaf is closed, the dispatch and the tagged
tuple are scoped at the parameters, and everything else is a variable
of the frame. -/
theorem mutualRecBodyAV_below {ℓ W w nP k n nIdx t : Nat} {Idss : List (List AnnotTerm)}
    {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
    {Eiss' : List (List (List AnnotTerm))} {Fss₀ Ess' : List (List AnnotTerm)}
    {auxLeaf : AnnotTerm}
    (hIds : ∀ Ids ∈ Idss, FieldsBelow nP Ids)
    (hAux : Term.bvarsBelow 0 auxLeaf.erase)
    (hTower : Term.bvarsBelow nP (dispTowerAV ℓ W w k Idss).erase)
    (hMot : Term.bvarsBelow nP (tagMotAV ℓ W w Idss rss tlss Eiss' Fss₀ Ess').erase) :
    Term.bvarsBelow (nP + (k + n + nIdx + 1))
      (mutualRecBodyAV ℓ W w nP k n nIdx t Idss rss tlss Eiss' Fss₀ Ess' auxLeaf).erase := by
  unfold mutualRecBodyAV
  rw [AnnotTerm.erase_mkAppN]
  refine VExprAux.bvarsBelow_mkAppN ?_ ?_
  · rw [AnnotTerm.liftN_eq_self _ hAux (k + n + nIdx + 1)]
    exact Term.bvarsBelow.mono (Nat.zero_le _) hAux
  · intro a ha
    obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp ha
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha₀
    rcases ha₀ with ((((ha | ha) | ha) | ha) | ha)
    · -- the parameter variables
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
      have := List.mem_range.mp hq
      show nP + (k + n + nIdx + 1) - 1 - q < nP + (k + n + nIdx + 1)
      omega
    · -- the dispatch
      subst ha
      exact motDispAV_below (by omega) hTower hMot
    · -- the minor variables
      obtain ⟨J, hJ, rfl⟩ := List.mem_map.mp ha
      have := List.mem_range.mp hJ
      show nIdx + 1 + n - 1 - J < nP + (k + n + nIdx + 1)
      omega
    · -- the tagged tuple of the index variables
      subst ha
      exact tagTupleAV_below hIds (fun E hE =>
        Term.bvarsBelow.mono (by omega)
          (idxVarsAV_below (K := nP + (k + n + nIdx + 1) - 1) (by omega) E hE))
    · -- the major
      subst ha
      show 0 < nP + (k + n + nIdx + 1)
      omega

/-- **Member `t`'s recursor leaf is closed**: its binder data is
(`MutualRecData.below`), the auxiliary recursor's leaf is
(`MutualLeafHyp.hclR`) and its body is `mutualRecBodyAV_below`'s. -/
theorem MutualRecParts.leaf_below (p : MutualRecParts) {env₀ : Env} {m₀ : EnvModel V env₀}
    (hyp : p.LeafHyp V m₀) {t : Nat} (ht : t < p.k) (ψ : Name → Nat)
    (hds : DomsBelow 0 (p.rds m₀ t ψ))
    (hlen : (p.rds m₀ t ψ).length = p.nP + p.k + p.n + p.nIdxOf t + 1)
    (hIds : ∀ Ids ∈ p.Idss ψ, FieldsBelow p.nP Ids)
    (hchains : ∀ chain ∈ chainsXI (p.W ψ) (auxIds (p.W ψ) (p.Idss ψ)) 1 p.rss (p.tlss ψ)
        (p.Eiss' ψ) (p.Fss₀ ψ) (p.Ess' ψ),
      FieldsBelow (p.nP + 2) chain) :
    Term.bvarsBelow 0 (p.leaf m₀ t ψ).erase := by
  have hh := hyp t ht ψ
  have hLs : (p.Ls ψ).length = p.k := by simp [MutualRecParts.Ls]
  unfold MutualRecParts.leaf mutualRecAVI
  rw [hLs, hh.hn, p.nIdxs_getD ht]
  refine mkLamsC_below hds ?_
  rw [Nat.zero_add, show (mutualRecDataAV m₀ ψ (p.Ls ψ) p.nP p.nIdxs p.elimL (p.ppsOf 0 ψ)
    (p.ipss ψ) (p.cds ψ) p.mems p.tgts t).length = p.nP + p.k + p.n + p.nIdxOf t + 1 from hlen]
  exact Term.bvarsBelow.mono (by omega)
    (mutualRecBodyAV_below hIds hh.hclR (dispTowerAV_below hIds) (tagMotAV_below hIds hchains))


/-! ## The stage -/

set_option maxHeartbeats 1600000 in
/-- **The mutual block's recursor stage**: the `k` member recursors
consed into the model with their rules.  The provision
(`stageMutualRecsProvision`) and the store (`stageMutualRecsStore`)
run back to back; at the end member `t`'s recursor carries the leaf
`mutualRecAVI … t` and every other constant keeps the value the
constructors' stage gave it. -/
theorem stageMutualRecs (p : MutualRecParts) {env₀ : Env} {m₀ : EnvModel V env₀}
    (hyp : p.LeafHyp V m₀)
    {b : MutualBlock} {fms : List MutualFormerA} {cvRas : List ConstantVal}
    {rulesOf : List (List (MutualCtor × Expr))} {env₂ : Env}
    {formers4 : List MutualFormer} {ctors4 : List MutualCtor4}
    {streamRecs : Option (List (ConstantVal × List RecRule))} {F : Nat}
    (mp₂ : EnvModelM V μ env₂)
    (hrectys : ConLeche.checkMutualRecTys (ConLeche.fueledOps μ F) env₂ b formers4 ctors4
      streamRecs b.k = .ok cvRas)
    (hrules : ConLeche.checkMutualAllRules (m := ConLeche.CheckM)
      (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂) b formers4 ctors4 streamRecs b.k
      = .ok rulesOf)
    (hk : cvRas.length = p.k)
    (hnd : (cvRas.map (·.name)).Nodup)
    (hfresh : ∀ t, t < p.k → env₂.find? (cvRas.getD t default).name = none)
    (hres : ∀ t, t < p.k → (cvRas.getD t default).type.constsResolve env₂ = true)
    (hE : ConLeche.EtaFamiliesClosed env₂)
    (hRDs : ∀ t, t < p.k → MutualRecData mp₂.base2 (cvRas.getD t default) p.nP p.k p.n
      (p.nIdxOf t) t p.elimL (p.rds m₀ t))
    (hIds : ∀ ψ : Name → Nat, ∀ Ids ∈ p.Idss ψ, FieldsBelow p.nP Ids)
    (hchains : ∀ ψ : Name → Nat, ∀ chain ∈ chainsXI (p.W ψ) (auxIds (p.W ψ) (p.Idss ψ)) 1 p.rss
        (p.tlss ψ) (p.Eiss' ψ) (p.Fss₀ ψ) (p.Ess' ψ),
      FieldsBelow (p.nP + 2) chain)
    (hAparams : ∀ t, t < p.k → ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ q ∈ (cvRas.getD t default).levelParams, ψ₁ q = ψ₂ q) →
      p.leaf m₀ t ψ₁ = p.leaf m₀ t ψ₂)
    (hnres : ∀ t, t < p.k →
      ConLeche.reservedBasisNames.contains (cvRas.getD t default).name = false)
    (hpshape : ∀ t, t < p.k → (cvRas.getD t default).name.isProjFnShape = false)
    (htyWF : ∀ t, t < p.k → (cvRas.getD t default).type.hasFvar = false ∧
      (cvRas.getD t default).type.allLevelParamsDefined
        (cvRas.getD t default).levelParams = true ∧
      (cvRas.getD t default).type.looseBVarsBounded 0 = true)
    (Inv : ∀ {env' : Env}, EnvModel V env' → Prop)
    (hInv : ∀ {env' : Env} (m' : EnvModel V env') (t : Nat), t < p.k →
      env'.find? (cvRas.getD t default).name = none → Inv m' →
      ∀ m₂ : EnvModel V ⟨.recInfo (cvRas.getD t default)
          (b.rulePrefix + (fms.getD t default).nIdx) b.rulePrefix [] :: env'.consts⟩,
        m₂.acval = acvalWith m'.acval (cvRas.getD t default).name (p.leaf m₀ t) → Inv m₂)
    (hinv₂ : Inv mp₂.base2)
    (hrepsP : ∀ (env' : Env) (mp' : EnvModelM V μ env') (t : Nat), t < p.k →
      env'.find? (cvRas.getD t default).name = none → Inv mp'.base2 →
      ∀ m₂ : EnvModel V ⟨.recInfo (cvRas.getD t default)
          (b.rulePrefix + (fms.getD t default).nIdx) b.rulePrefix [] :: env'.consts⟩,
        m₂.acval = acvalWith mp'.base2.acval (cvRas.getD t default).name (p.leaf m₀ t) →
        IndRepsHead env' (.recInfo (cvRas.getD t default)
          (b.rulePrefix + (fms.getD t default).nIdx) b.rulePrefix []) m₂)
    (hctorStored : ∀ t, t < p.k → ∀ r ∈ ConLeche.mutualRules env₂.find?
        (cvRas.getD t default).name b.nP (b.rulePrefix + (fms.getD t default).nIdx)
        b.rulePrefix (cvRas.getD t default).type (rulesOf.getD t []),
      ∃ cvj cnP cnF, env₂.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF))
    -- the block's rule rows at the FINAL carrier (`mutualRecRuleLaw`),
    -- at any carrier whose leaves are the block's
    (hlaws : ∀ (acv : Name → (Name → Nat) → AnnotTerm),
      (∀ t, t < p.k → ∀ ψ : Name → Nat, acv (cvRas.getD t default).name ψ = p.leaf m₀ t ψ) →
      (∀ n : Name, (∀ t, t < p.k → n ≠ (cvRas.getD t default).name) →
        acv n = mp₂.base2.acval n) →
      ∀ m₃ : EnvModel V (ConLeche.storeMutualRecs env₂ b fms rulesOf cvRas.zipIdx env₂),
        m₃.acval = acv → ∀ (φ : Name → Nat) (t : Nat), t < p.k →
        ∀ rl ∈ ConLeche.mutualRules env₂.find? (cvRas.getD t default).name b.nP
            (b.rulePrefix + (fms.getD t default).nIdx) b.rulePrefix
            (cvRas.getD t default).type (rulesOf.getD t []),
          RecRule.fire rl ≠ .inert →
          RecRuleLaw m₃ φ (cvRas.getD t default).name (cvRas.getD t default)
            (b.rulePrefix + (fms.getD t default).nIdx) b.rulePrefix rl)
    -- the representation clause at the store (task #280): the block's
    -- `k` representations at the PROVISIONED carrier (`Inv`) are what
    -- the store's clause is assembled from
    -- and whatever else the caller reads off the store's carrier (task
    -- #279 M-B′ step 3c (c): the block's own representations)
    (Out : EnvModel V (ConLeche.storeMutualRecs env₂ b fms rulesOf cvRas.zipIdx env₂) → Prop)
    (hrepsS : ∀ mpP : EnvModelM V μ (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂),
      Inv mpP.base2 →
      ∀ m₃ : EnvModel V (ConLeche.storeMutualRecs env₂ b fms rulesOf cvRas.zipIdx env₂),
        m₃.acval = mpP.base2.acval → IndReps m₃ ∧ Out m₃) :
    ∃ mp₄ : EnvModelM V μ (ConLeche.storeMutualRecs env₂ b fms rulesOf cvRas.zipIdx env₂),
      (∀ t, t < p.k → ∀ ψ : Name → Nat,
        mp₄.base2.acval (cvRas.getD t default).name ψ = p.leaf m₀ t ψ) ∧
      (∀ n : Name, (∀ t, t < p.k → n ≠ (cvRas.getD t default).name) →
        mp₄.base2.acval n = mp₂.base2.acval n) ∧
      Out mp₄.base2 := by
  have hAcl : ∀ t, t < p.k → ∀ ψ : Name → Nat, Term.bvarsBelow 0 (p.leaf m₀ t ψ).erase :=
    fun t ht ψ => p.leaf_below hyp ht ψ ((hRDs t ht).below ψ) ((hRDs t ht).len ψ) (hIds ψ)
      (hchains ψ)
  obtain ⟨mpP, -, -, -, hleafP, hagP, hinvP⟩ :=
    stageMutualRecsProvision p hyp mp₂ hk hAcl hAparams hnres hpshape htyWF Inv hInv hrepsP hnd
      hfresh hres hE hRDs hinv₂
  obtain ⟨mp₄, hacc, -⟩ :=
    stageMutualRecsStore p mp₂.base2.wf hrectys hrules mpP hk hfresh hnres hctorStored
      (fun m₃ hac => hlaws mpP.base2.acval hleafP hagP m₃ hac)
      (fun m₃ hac => (hrepsS mpP hinvP m₃ hac).1)
  exact ⟨mp₄, fun t ht ψ => by rw [hacc]; exact hleafP t ht ψ,
    fun n hn => by rw [hacc]; exact hagP n hn, (hrepsS mpP hinvP mp₄.base2 hacc).2⟩


end ConLeche.Model
