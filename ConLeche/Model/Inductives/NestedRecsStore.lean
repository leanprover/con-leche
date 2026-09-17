module

public import ConLeche.Model.Inductives.NestedRecsStage
import ConLeche.Semantics.Tower.SigChainWire
import ConLeche.Model.Inductives.BlockRecLeaf
import ConLeche.Model.IndCons
import ConLeche.Model.RecRulesCons
import ConLeche.Verify.Inductives.StructWF
public section

/-!
# The nested block's recursors: the rule-less conses (task #315, M7-2, item 5)

`MutualRecsProvision.lean`'s twin at the NESTED route's
`provisionNestedRecs` (PLAN-M7 §4a).  Two things differ from the
mutual loop and nothing else does:

* the kernel's list is one of TRIPLES `(cvRa, mI, rP)` — the read-back
  supplies the recursor's argument sums per entry, where the mutual
  route computes them from the block — so the loop is restated over
  the triples paired with their class index;
* the stored type's reading is not `mutualConcAV`-shaped.  A restored
  recursor type reads to `mkPisAV (rdsM c ψ) (concM c)`
  (`NestedRecReadings`), whose conclusion is the SCRATCH block's, so
  the cons step is stated at an arbitrary reading `T c ψ`
  (`nestedRecProvisionCons`) — `recProvisionCons` consumes its
  `MutualRecData` through `read`/`okTy` alone, and those are the two
  hypotheses here.

The leaf is the chosen tuple's projection at the level assignment
RESTRICTED to the recursors' level parameters (`nestedRecLeaf`, the
mutual `BlockModel.recLeaf`'s twin at `kT` classes), so its stability
under those parameters is definitional; its closedness and bit
validity are `blockRecAVI_below`/`blockRecAVI_validV` at the readings'
and the equations' own (`NestedRecReadings.below`/`.okTy`,
`NestedRecEqs.below`/`.valid`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecFieldKind IndCaps
  RecRule NestedParts MutualBlock AuxStored ElimState)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## One recursor's rule-less cons, at an arbitrary reading -/

/-- **The P step at ONE provisioned recursor's cons** (`recProvisionCons`
with the stored type's reading left arbitrary): the recursor consed
RULE-LESS with the leaf `A`.  Its typing is the leaf's own (`hleaf`),
its type's reading `T` (`hread`, graded by `hokTy`), its rule law
nothing (`recRules_cons_fresh`) and its capability obligation nothing
either — the cons stores a RECURSOR at the name the obligation is taken
at, so `capsOk_cons_native`'s block-family branch is refuted by
`Env.find?_cons_self` and the rest is `EtaFamiliesClosed`. -/
theorem nestedRecProvisionCons (mp : EnvModelM V μ env) (hE : ConLeche.EtaFamiliesClosed env)
    {cvRa : ConstantVal} {mI rP : Nat} {T A : (Name → Nat) → AnnotTerm}
    (hreadA : ∀ ψ : Name → Nat, denoteMeta mp.base2.acval env ψ 0 cvRa.type = some (T ψ))
    (hokTy : ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenotedV V ρ (T ψ))
    (hleaf : ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenotedV V ρ (A ψ) ∧
      interp V ρ (A ψ) ∈ˢ interp V ρ (T ψ))
    (hfresh : env.find? cvRa.name = none)
    (hnres : ConLeche.reservedBasisNames.contains cvRa.name = false)
    (hpshape : cvRa.name.isProjFnShape = false)
    (hwf : ConLeche.EnvWF ⟨.recInfo cvRa mI rP [] :: env.consts⟩)
    (hcb : ConstsBound env cvRa.type)
    (hAcl : ∀ ψ : Name → Nat, Term.bvarsBelow 0 (A ψ).erase)
    (hAparams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ cvRa.levelParams, ψ₁ q = ψ₂ q) → A ψ₁ = A ψ₂) :
    ∃ mp' : EnvModelM V μ ⟨.recInfo cvRa mI rP [] :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval cvRa.name A := by
  have hcross : ∀ e : Expr, ConsCrossAt (.recInfo cvRa mI rP []) e :=
    fun _ => ConsCrossAt.ofNtc (fun _ h => nomatch h)
  have hread : ∀ ψ : Name → Nat,
      denoteMeta (acvalWith mp.base2.acval cvRa.name A)
        ⟨.recInfo cvRa mI rP [] :: env.consts⟩ ψ 0 cvRa.type = some (T ψ) := fun ψ =>
    denoteMeta_cons_mono (c₀ := .recInfo cvRa mI rP []) hfresh (hcross _) ψ 0 hcb (hreadA ψ)
  refine declStep_preserves_of_ind_rec_cons mp (c₀ := .recInfo cvRa mI rP [])
    (A := A) hfresh hnres ⟨_, _, _, _, rfl⟩
    (ConsHead.ofFresh hwf (fun ψ => hAcl ψ) hnres (fun _ h => nomatch h)
      (fun _ _ _ rules heq r hr => by
        injection heq with _ _ _ hrules
        rw [← hrules] at hr
        exact nomatch hr))
    (fun ψ q => AnnotTerm.liftN_eq_self _ (Term.bvarsBelow.mono (Nat.zero_le q) (hAcl ψ)) 1)
    hAparams (fun ψ ρ => (hleaf ψ ρ).1.1) (fun ψ ρ => (hleaf ψ ρ).1.2)
    (fun ψ => ⟨_, hread ψ⟩) ?_ ?_ ?_ ?_
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hread ψ).symm.trans hta)
    exact hokTy ψ ρ
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hread ψ).symm.trans hta)
    exact (hleaf ψ ρ).2
  · -- `caps_ok`: the cons stores a RECURSOR at the name the obligation
    -- is taken at, so the block-family branch is vacuous
    intro m₂ hac
    refine capsOk_cons_native mp (c₀ := .recInfo cvRa mI rP []) (A := A)
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
    exact recRules_cons_fresh mp (c₀ := .recInfo cvRa mI rP []) (A := A) hfresh
      (ConsCrossEnv.ofNtc fun _ h => nomatch h)
      (fun _ _ _ rules heq => by injection heq with _ _ _ hrules; exact hrules.symm) m₂ hac φ

/-! ## The leaf, and its three laws -/

/-- **Class `c`'s restored recursor leaf** (the mutual `BlockModel.recLeaf`'s
twin at `kT` classes): the chosen tuple's `c`-th projection
(`blockLeafAV`) at the stage's readings, taken at the level assignment
RESTRICTED to the recursors' level parameters — the leaf then depends
on those parameters alone BY CONSTRUCTION, and the readings agree at
the two assignments (`NestedRecReadings.params`). -/
@[expose] def nestedRecLeaf (kT : Nat) (s : (Name → Nat) → Nat)
    (rdsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (concM : Nat → AnnotTerm)
    (eqs : (Name → Nat) → List AnnotTerm) (rlps : List Name) (c : Nat) (ψ : Name → Nat) :
    AnnotTerm :=
  blockLeafAV (s (restrictΨ rlps ψ)) kT (fun t => rdsM t (restrictΨ rlps ψ)) concM
    (eqs (restrictΨ rlps ψ)) c

section Leaf

variable {env₂ : Env} {m : EnvModel V env₂} {d : BlockModel V} {pc : Nat → PinCtors V}
  {cvRms cvRns : List ConstantVal} {rlps : List Name} {elimL : Level} {s : (Name → Nat) → Nat}
  {rdsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {concM : Nat → AnnotTerm}
  {eqs : (Name → Nat) → List AnnotTerm}

/-- **The leaf depends on the recursors' level parameters alone** —
`restrictΨ` being the leaf's own argument. -/
theorem nestedRecLeaf_params {kT : Nat} {c : Nat} {ψ₁ ψ₂ : Name → Nat}
    (hφ : ∀ q ∈ rlps, ψ₁ q = ψ₂ q) :
    nestedRecLeaf kT s rdsM concM eqs rlps c ψ₁ = nestedRecLeaf kT s rdsM concM eqs rlps c ψ₂ := by
  unfold nestedRecLeaf
  rw [restrictΨ_congr hφ]

/-- **The leaf is closed**: the readings' Π-towers are
(`NestedRecReadings.tyBelow`) and the equations are closed under the
`kT` tuple binders (`NestedRecEqs.below`), which is
`blockRecAVI_below`'s hypothesis pair at `K = 0`. -/
theorem nestedRecLeaf_below
    (R : NestedRecReadings m d pc cvRms cvRns rlps elimL s rdsM concM)
    (E : NestedRecEqs d pc (fun ψ => elimL.eval ψ) rdsM concM eqs)
    (c : Nat) (ψ : Name → Nat) :
    Term.bvarsBelow 0 (nestedRecLeaf d.kT s rdsM concM eqs rlps c ψ).erase := by
  unfold nestedRecLeaf blockLeafAV
  refine ConLeche.Semantics.blockRecAVI_below (K := 0) (fun t ht => R.tyBelow t _ ht)
    (fun e he => ?_) c
  rw [Nat.zero_add]
  exact E.below _ e he

/-- **The leaf is typed at its reading, graded and bit-valid**: the
chosen tuple's `c`-th projection is a member of the reading at the
RESTRICTED assignment (`NestedRecTuple`), which is the reading at `ψ`
(`NestedRecReadings.params` at `restrictΨ_agree`); its bit validity is
`blockRecAVI_validV` at the readings' and the equations' own. -/
theorem nestedRecLeaf_typed
    (R : NestedRecReadings m d pc cvRms cvRns rlps elimL s rdsM concM)
    (E : NestedRecEqs d pc (fun ψ => elimL.eval ψ) rdsM concM eqs)
    (Tu : NestedRecTuple d s rdsM concM eqs)
    (c : Nat) (hc : c < d.kT) (ψ : Name → Nat) (ρ : Nat → V) :
    WellDenotedV V ρ (nestedRecLeaf d.kT s rdsM concM eqs rlps c ψ) ∧
      interp V ρ (nestedRecLeaf d.kT s rdsM concM eqs rlps c ψ)
        ∈ˢ interp V ρ (mkPisAV (rdsM c ψ) (concM c)) := by
  obtain ⟨a, ha, -⟩ := Tu (restrictΨ rlps ψ) ρ
  obtain ⟨hmem, hval, hwd⟩ := ha c hc
  -- the reading at `ψ` is the reading at the restricted assignment
  have hrds : rdsM c ψ = rdsM c (restrictΨ rlps ψ) :=
    R.params c ψ _ hc fun q hq => (restrictΨ_agree rlps ψ q hq).symm
  unfold nestedRecLeaf
  refine ⟨⟨hwd, ?_⟩, by rw [hrds, hval]; exact hmem⟩
  unfold blockLeafAV
  exact blockRecAVI_validV
    (fun t ht => ⟨R.sort t _ ρ ht, (R.okTy t _ ρ ht).1, (R.okTy t _ ρ ht).2⟩)
    (fun rs hlen hrs e he => ⟨(E.heq _ ρ rs hlen hrs e he).1, (E.heq _ ρ rs hlen hrs e he).2,
      E.valid _ ρ rs hlen hrs e he⟩) c

end Leaf

/-! ## The loop, in class order -/

/-- **The provisioning loop** (`provisionNestedRecs`, class order): the
`kT` recursors consed rule-less, class `c` with the leaf `A c`.  Each
entry is a TRIPLE paired with its class index; the kernel's list is the
triples alone (`rest.map (·.1)`).  Every class's stored-type reading
crosses each cons (`denoteMeta_cons_mono`), and the leaves of the
classes already consed are untouched — a leaf mentions no recursor
name, so its typing is available at every step. -/
theorem nestedRecsProvisionGo {kT : Nat} {T A : Nat → (Name → Nat) → AnnotTerm}
    {cvOf : Nat → ConstantVal}
    (hokTy : ∀ c, c < kT → ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenotedV V ρ (T c ψ))
    (hleaf : ∀ c, c < kT → ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenotedV V ρ (A c ψ) ∧
      interp V ρ (A c ψ) ∈ˢ interp V ρ (T c ψ))
    (hAcl : ∀ c, c < kT → ∀ ψ : Name → Nat, Term.bvarsBelow 0 (A c ψ).erase)
    (hAparams : ∀ c, c < kT → ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ q ∈ (cvOf c).levelParams, ψ₁ q = ψ₂ q) → A c ψ₁ = A c ψ₂)
    (hnres : ∀ c, c < kT → ConLeche.reservedBasisNames.contains (cvOf c).name = false)
    (hpshape : ∀ c, c < kT → (cvOf c).name.isProjFnShape = false)
    (htyWF : ∀ c, c < kT → (cvOf c).type.hasFvar = false ∧
      (cvOf c).type.allLevelParamsDefined (cvOf c).levelParams = true ∧
      (cvOf c).type.looseBVarsBounded 0 = true) :
    ∀ (rest : List ((ConstantVal × Nat × Nat) × Nat)) (env : Env) (_mp : EnvModelM V μ env),
      (∀ x ∈ rest, x.2 < kT ∧ x.1.1 = cvOf x.2) →
      (∀ x ∈ rest, env.find? x.1.1.name = none) →
      (∀ c, c < kT → (cvOf c).type.constsResolve env = true) →
      ConLeche.EtaFamiliesClosed env →
      (rest.map (·.1.1.name)).Nodup →
      (∀ c, c < kT → ∀ ψ : Name → Nat,
        denoteMeta _mp.base2.acval env ψ 0 (cvOf c).type = some (T c ψ)) →
      ∃ mp' : EnvModelM V μ (ConLeche.provisionNestedRecs (rest.map (·.1)) env),
        ConLeche.EtaFamiliesClosed (ConLeche.provisionNestedRecs (rest.map (·.1)) env) ∧
        (∀ c, c < kT → (cvOf c).type.constsResolve
          (ConLeche.provisionNestedRecs (rest.map (·.1)) env) = true) ∧
        (∀ c, c < kT → ∀ ψ : Name → Nat,
          denoteMeta mp'.base2.acval (ConLeche.provisionNestedRecs (rest.map (·.1)) env) ψ 0
            (cvOf c).type = some (T c ψ)) ∧
        (∀ x ∈ rest, ∀ ψ : Name → Nat, mp'.base2.acval x.1.1.name ψ = A x.2 ψ) ∧
        (∀ nm : Name, (∀ x ∈ rest, nm ≠ x.1.1.name) → mp'.base2.acval nm = _mp.base2.acval nm)
  | [], env, mp, _, _, hres, hE, _, hreads =>
    ⟨mp, hE, hres, hreads, fun x hx => absurd hx (by simp), fun _ _ => rfl⟩
  | ((cvRa, mI, rP), c) :: rest, env, mp, hmem, hfr, hres, hE, hnd, hreads => by
    obtain ⟨hcT, hcv⟩ := hmem ((cvRa, mI, rP), c) List.mem_cons_self
    dsimp only at hcT hcv
    subst hcv
    have hfresh : env.find? (cvOf c).name = none := hfr _ List.mem_cons_self
    obtain ⟨hfv, hlp, hbv⟩ := htyWF c hcT
    have hcb : ConstsBound env (cvOf c).type := constsBound_of_constsResolve _ (hres c hcT)
    -- the cons's head and its well-formedness
    have hwf : ConLeche.EnvWF ⟨.recInfo (cvOf c) mI rP [] :: env.consts⟩ := by
      refine ConLeche.EnvWF.cons mp.base2.wf (ConLeche.structConstWF hfv hlp
        (Expr.constsResolve_mono (hres c hcT)) hbv (fun _ _ _ heq => nomatch heq) ?_)
      intro cv mI' rP' rules heq r hr
      injection heq with _ _ _ hrules
      rw [← hrules] at hr
      exact nomatch hr
    obtain ⟨mpR, hacR⟩ := nestedRecProvisionCons mp hE (hreads c hcT) (hokTy c hcT) (hleaf c hcT)
      hfresh (hnres c hcT) (hpshape c hcT) hwf hcb (hAcl c hcT) (hAparams c hcT)
    -- the invariants at the extension
    have hcross : ∀ e : Expr, ConsCrossAt (.recInfo (cvOf c) mI rP []) e :=
      fun _ => ConsCrossAt.ofNtc (fun _ h => nomatch h)
    have hndc : (∀ (y : ConstantVal × Nat × Nat) (q : Nat), (y, q) ∈ rest →
        ¬ y.1.name = (cvOf c).name) ∧ (rest.map (·.1.1.name)).Nodup := by simpa using hnd
    have hneRest : ∀ x ∈ rest, x.1.1.name ≠ (cvOf c).name := by
      intro x hx
      exact hndc.1 x.1 x.2 (by simpa using hx)
    have hE' : ConLeche.EtaFamiliesClosed ⟨.recInfo (cvOf c) mI rP [] :: env.consts⟩ :=
      hE.cons_nonind hfresh (fun _ _ heq => nomatch heq)
    have hres' : ∀ t, t < kT →
        (cvOf t).type.constsResolve ⟨.recInfo (cvOf c) mI rP [] :: env.consts⟩ = true :=
      fun t ht => Expr.constsResolve_mono (hres t ht)
    have hreads' : ∀ t, t < kT → ∀ ψ : Name → Nat,
        denoteMeta mpR.base2.acval ⟨.recInfo (cvOf c) mI rP [] :: env.consts⟩ ψ 0 (cvOf t).type
          = some (T t ψ) := by
      intro t ht ψ
      rw [hacR]
      exact denoteMeta_cons_mono (c₀ := .recInfo (cvOf c) mI rP []) hfresh (hcross _) ψ 0
        (constsBound_of_constsResolve _ (hres t ht)) (hreads t ht ψ)
    obtain ⟨mp', hE'', hres'', hreads'', hleaf'', hag⟩ :=
      nestedRecsProvisionGo hokTy hleaf hAcl hAparams hnres hpshape htyWF rest _ mpR
        (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
        (fun x hx => by
          rw [ConLeche.Env.find?_cons, if_neg (fun h => hneRest x hx h.symm)]
          exact hfr x (List.mem_cons_of_mem _ hx))
        hres' hE' (by simpa using hndc.2) hreads'
    refine ⟨mp', hE'', hres'', hreads'', ?_, ?_⟩
    · intro x hx ψ
      rcases List.mem_cons.mp hx with heq | hx'
      · subst heq
        show mp'.base2.acval (cvOf c).name ψ = A c ψ
        rw [hag (cvOf c).name (fun y hy => (hneRest y hy).symm), hacR]
        show acvalWith mp.base2.acval (cvOf c).name _ (cvOf c).name ψ = _
        rw [acvalWith_self]
      · exact hleaf'' x hx' ψ
    · intro nm hn
      rw [hag nm (fun x hx => hn x (List.mem_cons_of_mem _ hx)), hacR]
      exact acvalWith_ne (hn _ List.mem_cons_self)

/-- **The recursors' provisioning stage**: the `kT` restored recursors
of the block consed RULE-LESS onto the constructors' environment, class
`c` with the leaf `A c`.  The kernel's list is the triples in class
order (`L`), and the loop runs on `L.zipIdx`. -/
theorem nestedRecsProvision {kT : Nat} {T A : Nat → (Name → Nat) → AnnotTerm}
    {cvOf : Nat → ConstantVal} {L : List (ConstantVal × Nat × Nat)} {env₂ : Env}
    (mp₂ : EnvModelM V μ env₂) (hlen : L.length = kT)
    (hL : ∀ (c : Nat) (x : ConstantVal × Nat × Nat), L[c]? = some x → x.1 = cvOf c)
    (hokTy : ∀ c, c < kT → ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenotedV V ρ (T c ψ))
    (hleaf : ∀ c, c < kT → ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenotedV V ρ (A c ψ) ∧
      interp V ρ (A c ψ) ∈ˢ interp V ρ (T c ψ))
    (hAcl : ∀ c, c < kT → ∀ ψ : Name → Nat, Term.bvarsBelow 0 (A c ψ).erase)
    (hAparams : ∀ c, c < kT → ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ q ∈ (cvOf c).levelParams, ψ₁ q = ψ₂ q) → A c ψ₁ = A c ψ₂)
    (hnres : ∀ c, c < kT → ConLeche.reservedBasisNames.contains (cvOf c).name = false)
    (hpshape : ∀ c, c < kT → (cvOf c).name.isProjFnShape = false)
    (htyWF : ∀ c, c < kT → (cvOf c).type.hasFvar = false ∧
      (cvOf c).type.allLevelParamsDefined (cvOf c).levelParams = true ∧
      (cvOf c).type.looseBVarsBounded 0 = true)
    (hnd : (L.map (·.1.name)).Nodup)
    (hfresh : ∀ c, c < kT → env₂.find? (cvOf c).name = none)
    (hres : ∀ c, c < kT → (cvOf c).type.constsResolve env₂ = true)
    (hE : ConLeche.EtaFamiliesClosed env₂)
    (hreads : ∀ c, c < kT → ∀ ψ : Name → Nat,
      denoteMeta mp₂.base2.acval env₂ ψ 0 (cvOf c).type = some (T c ψ)) :
    ∃ mp₃ : EnvModelM V μ (ConLeche.provisionNestedRecs L env₂),
      ConLeche.EtaFamiliesClosed (ConLeche.provisionNestedRecs L env₂) ∧
      (∀ c, c < kT → (cvOf c).type.constsResolve (ConLeche.provisionNestedRecs L env₂) = true) ∧
      (∀ c, c < kT → ∀ ψ : Name → Nat,
        denoteMeta mp₃.base2.acval (ConLeche.provisionNestedRecs L env₂) ψ 0 (cvOf c).type
          = some (T c ψ)) ∧
      (∀ c, c < kT → ∀ ψ : Name → Nat, mp₃.base2.acval (cvOf c).name ψ = A c ψ) ∧
      (∀ nm : Name, (∀ c, c < kT → nm ≠ (cvOf c).name) →
        mp₃.base2.acval nm = mp₂.base2.acval nm) := by
  -- an entry of `L.zipIdx` is a triple at its class index
  have hzip : ∀ x ∈ L.zipIdx, x.2 < kT ∧ x.1.1 = cvOf x.2 := by
    intro x hx
    have hget : L[x.2]? = some x.1 := List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using hx)
    exact ⟨by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hget).1, hL x.2 x.1 hget⟩
  have hmapFst : L.zipIdx.map (·.1) = L := by simp
  have hndZ : (L.zipIdx.map (·.1.1.name)).Nodup := by
    have hmm : L.zipIdx.map (fun x : (ConstantVal × Nat × Nat) × Nat => x.1.1.name)
        = (L.zipIdx.map (·.1)).map (fun y : ConstantVal × Nat × Nat => y.1.name) := by
      rw [List.map_map]; rfl
    rw [hmm, hmapFst]
    exact hnd
  rw [← hmapFst]
  obtain ⟨mp₃, hE₃, hres₃, hreads₃, hleaf₃, hag⟩ :=
    nestedRecsProvisionGo (cvOf := cvOf) (T := T) (A := A) hokTy hleaf hAcl hAparams hnres hpshape
      htyWF L.zipIdx env₂ mp₂ hzip
      (fun x hx => by rw [(hzip x hx).2]; exact hfresh x.2 (hzip x hx).1) hres hE hndZ hreads
  refine ⟨mp₃, hE₃, hres₃, hreads₃, ?_, ?_⟩
  · intro c hc ψ
    have hmem : (L.getD c default, c) ∈ L.zipIdx := by
      refine List.mk_mem_zipIdx_iff_getElem?.mpr ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      rfl
    have := hleaf₃ _ hmem ψ
    rw [hL c (L.getD c default) (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl)] at this
    exact this
  · intro nm hn
    exact hag nm fun x hx => by rw [(hzip x hx).2]; exact hn x.2 (hzip x hx).1

end ConLeche.Model
