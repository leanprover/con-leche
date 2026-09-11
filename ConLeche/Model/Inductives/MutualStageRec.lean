module

public import ConLeche.Model.Inductives.MutualRecTyping
public import ConLeche.Model.Inductives.MutualRecData
public import ConLeche.Model.Inductives.MutualRecLaw
public import ConLeche.Model.Inductives.StructCaps
public import ConLeche.Model.Swap
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
def LeafHyp (V : Type w) [SetTheory V] {env₀ : Env} (m₀ : EnvModel V env₀) : Prop :=
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
so its typing is available at every step. -/
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
    (hreps : ∀ (env' : Env) (mp' : EnvModelM V μ env') (t : Nat), t < p.k →
      env'.find? (cvRaOf t).name = none →
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
      ∃ mp' : EnvModelM V μ (ConLeche.provisionMutualRecs b fms rest env),
        ConLeche.EtaFamiliesClosed (ConLeche.provisionMutualRecs b fms rest env) ∧
        (∀ t, t < p.k → (cvRaOf t).type.constsResolve
          (ConLeche.provisionMutualRecs b fms rest env) = true) ∧
        (∀ t, t < p.k → MutualRecData mp'.base2 (cvRaOf t) p.nP p.k p.n (p.nIdxOf t) t p.elimL
          (p.rds m₀ t)) ∧
        (∀ x ∈ rest, ∀ ψ : Name → Nat, mp'.base2.acval x.1.name ψ = p.leaf m₀ x.2 ψ) ∧
        (∀ n : Name, (∀ x ∈ rest, n ≠ x.1.name) → mp'.base2.acval n = _mp.base2.acval n)
  | [], env, mp, _, _, hres, hE, _, hRDs =>
    ⟨mp, hE, hres, hRDs, fun x hx => absurd hx (by simp), fun _ _ => rfl⟩
  | (cvRa, mIdx) :: rest, env, mp, hmem, hfr, hres, hE, hnd, hRDs => by
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
      (hAparams mIdx hmIdx) (hreps env mp mIdx hmIdx hfresh)
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
    obtain ⟨mp', hE'', hres'', hRDs'', hleaf'', hag⟩ :=
      stageMutualRecsProvisionGo p hyp hAcl hAparams hnres hpshape htyWF hreps rest _ mpR
        (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
        (fun x hx => by
          rw [ConLeche.Env.find?_cons, if_neg (fun h => hneRest x hx h.symm)]
          exact hfr x (List.mem_cons_of_mem _ hx))
        hres' hE' (by simpa using hndc.2) hRDs'
    refine ⟨mp', hE'', hres'', hRDs'', ?_, ?_⟩
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
    (hreps : ∀ (env' : Env) (mp' : EnvModelM V μ env') (t : Nat), t < p.k →
      env'.find? (cvRas.getD t default).name = none →
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
      (p.nIdxOf t) t p.elimL (p.rds m₀ t)) :
    ∃ mp₃ : EnvModelM V μ (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂),
      ConLeche.EtaFamiliesClosed (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂) ∧
      (∀ t, t < p.k → (cvRas.getD t default).type.constsResolve
        (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂) = true) ∧
      (∀ t, t < p.k → MutualRecData mp₃.base2 (cvRas.getD t default) p.nP p.k p.n (p.nIdxOf t) t
        p.elimL (p.rds m₀ t)) ∧
      (∀ t, t < p.k → ∀ ψ : Name → Nat,
        mp₃.base2.acval (cvRas.getD t default).name ψ = p.leaf m₀ t ψ) ∧
      (∀ n : Name, (∀ t, t < p.k → n ≠ (cvRas.getD t default).name) →
        mp₃.base2.acval n = mp₂.base2.acval n) := by
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
  obtain ⟨mp₃, hE₃, hres₃, hRDs₃, hleaf₃, hag⟩ :=
    stageMutualRecsProvisionGo p hyp hAcl hAparams hnres hpshape htyWF hreps cvRas.zipIdx env₂ mp₂
      hzip (fun x hx => by rw [(hzip x hx).2]; exact hfresh x.2 (hzip x hx).1) hres hE hzipNd hRDs
  refine ⟨mp₃, hE₃, hres₃, hRDs₃, ?_, ?_⟩
  · intro t ht ψ
    have hmem : (cvRas.getD t default, t) ∈ cvRas.zipIdx := by
      refine List.mk_mem_zipIdx_iff_getElem?.mpr ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      rfl
    exact hleaf₃ _ hmem ψ
  · intro n hn
    exact hag n fun x hx => by rw [(hzip x hx).2]; exact hn x.2 (hzip x hx).1


end ConLeche.Model
