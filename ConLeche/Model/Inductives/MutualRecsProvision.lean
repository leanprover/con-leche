module

public import ConLeche.Model.Inductives.MutualRecData
import ConLeche.Model.IndCons
import ConLeche.Model.RecRulesCons
import ConLeche.Verify.Inductives.StructWF
public section

/-!
# The recursors' rule-less conses (task #315 U-8, M4 s4a)

The kernel's `provisionMutualRecs` conses the block's `k` recursors
RULE-LESS onto the constructors' environment (a rule mentions the
sibling recursors, so every rule is scoped at the environment holding
all of them); `storeMutualRecs` later conses the SAME names with
their rules (the store is a swap, M4 s4b).  Here the P step at ONE
rule-less cons (`recProvisionCons`: `declStep_preserves_of_ind_rec_cons`
with `rules := []`, whose `rec_rules` obligation is
`recRules_cons_fresh` — a rule-less recursor owes no rule law — and
whose `caps_ok` obligation is vacuous at a recursor) and the loop in
block order (`recsProvisionGo`, `recsProvision`), generic in the
leaf: member `t`'s leaf `A t` is any term family that is closed,
stable under the recursor's level parameters, graded, bit-valid and
in the reading of the stored recursor type (`MutualRecData`).  The
stored types' readings cross every cons (`MutualRecData.cross`), and
the leaves of the members already consed are untouched.

The reference (`inductives`' `stageMutualRecsProvision`) threaded a
caller's carrier invariant through the loop; the uniform datum needs
none — `BlockReps` is transported once, at the end (`MutualRecsStage`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps RecRule
  MutualBlock MutualFormerA)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## One recursor's rule-less cons -/

/-- **The P step at ONE provisioned recursor's cons**: member `t`'s
recursor, consed RULE-LESS (`provisionMutualRecs`' entry) with the
leaf `A t`.  Its typing is the leaf's own (`hleaf`), its type's reading
the stored recursor type's (`MutualRecData`), its rule law nothing
(`recRules_cons_fresh`) and its capability obligation nothing either —
the cons stores a RECURSOR at the name the obligation is taken at, so
`capsOk_cons_native`'s block-family branch is refuted by
`Env.find?_cons_self` and the rest is `EtaFamiliesClosed`. -/
theorem recProvisionCons (mp : EnvModelM V μ env) (hE : ConLeche.EtaFamiliesClosed env)
    {k nP n : Nat} {nIdxOf : Nat → Nat} {elimL : Level}
    {rds : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {A : Nat → (Name → Nat) → AnnotTerm}
    {cvRa : ConstantVal} {mI rP t : Nat}
    (hleaf : ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenotedV V ρ (A t ψ) ∧
      interp V ρ (A t ψ) ∈ˢ interp V ρ (mkPisAV (rds t ψ) (mutualConcAV k n (nIdxOf t) t)))
    (hfresh : env.find? cvRa.name = none)
    (hnres : ConLeche.reservedBasisNames.contains cvRa.name = false)
    (hpshape : cvRa.name.isProjFnShape = false)
    (hwf : ConLeche.EnvWF ⟨.recInfo cvRa mI rP [] :: env.consts⟩)
    (hcb : ConstsBound env cvRa.type)
    (hRD : MutualRecData mp.base2 cvRa nP k n (nIdxOf t) t elimL (rds t))
    (hAcl : ∀ ψ : Name → Nat, Term.bvarsBelow 0 (A t ψ).erase)
    (hAparams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ cvRa.levelParams, ψ₁ q = ψ₂ q) →
      A t ψ₁ = A t ψ₂) :
    ∃ mp' : EnvModelM V μ ⟨.recInfo cvRa mI rP [] :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval cvRa.name (A t) := by
  have hcross : ∀ e : Expr, ConsCrossAt (.recInfo cvRa mI rP []) e :=
    fun _ => ConsCrossAt.ofNtc (fun _ h => nomatch h)
  have hread : ∀ ψ : Name → Nat,
      denoteMeta (acvalWith mp.base2.acval cvRa.name (A t))
        ⟨.recInfo cvRa mI rP [] :: env.consts⟩ ψ 0 cvRa.type
        = some (mkPisAV (rds t ψ) (mutualConcAV k n (nIdxOf t) t)) := fun ψ =>
    denoteMeta_cons_mono (c₀ := .recInfo cvRa mI rP []) hfresh (hcross _) ψ 0 hcb (hRD.read ψ)
  refine declStep_preserves_of_ind_rec_cons mp (c₀ := .recInfo cvRa mI rP [])
    (A := A t) hfresh hnres ⟨_, _, _, _, rfl⟩
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
    exact hRD.okTy ψ ρ
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hread ψ).symm.trans hta)
    exact (hleaf ψ ρ).2
  · -- `caps_ok`: the cons stores a RECURSOR at the name the obligation
    -- is taken at, so the block-family branch is vacuous
    intro m₂ hac
    refine capsOk_cons_native mp (c₀ := .recInfo cvRa mI rP []) (A := A t)
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
    exact recRules_cons_fresh mp (c₀ := .recInfo cvRa mI rP []) (A := A t) hfresh
      (ConsCrossEnv.ofNtc fun _ h => nomatch h)
      (fun _ _ _ rules heq => by injection heq with _ _ _ hrules; exact hrules.symm) m₂ hac φ

/-! ## The loop, in block order -/

/-- **The provisioning loop** (`provisionMutualRecs`, block order): the
`k` recursors consed rule-less, member `t` with the leaf `A t`.  Every
member's stored-type reading crosses each cons (`MutualRecData.cross`),
and the leaves of the members already consed are untouched — member
`t`'s leaf mentions no sibling recursor, so its typing is available at
every step. -/
theorem recsProvisionGo {k nP n : Nat} {nIdxOf : Nat → Nat} {elimL : Level}
    {rds : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {A : Nat → (Name → Nat) → AnnotTerm} {b : MutualBlock} {fms : List MutualFormerA}
    {cvRaOf : Nat → ConstantVal}
    (hleaf : ∀ t, t < k → ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenotedV V ρ (A t ψ) ∧
      interp V ρ (A t ψ) ∈ˢ interp V ρ (mkPisAV (rds t ψ) (mutualConcAV k n (nIdxOf t) t)))
    (hAcl : ∀ t, t < k → ∀ ψ : Name → Nat, Term.bvarsBelow 0 (A t ψ).erase)
    (hAparams : ∀ t, t < k → ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ q ∈ (cvRaOf t).levelParams, ψ₁ q = ψ₂ q) → A t ψ₁ = A t ψ₂)
    (hnres : ∀ t, t < k → ConLeche.reservedBasisNames.contains (cvRaOf t).name = false)
    (hpshape : ∀ t, t < k → (cvRaOf t).name.isProjFnShape = false)
    (htyWF : ∀ t, t < k → (cvRaOf t).type.hasFvar = false ∧
      (cvRaOf t).type.allLevelParamsDefined (cvRaOf t).levelParams = true ∧
      (cvRaOf t).type.looseBVarsBounded 0 = true) :
    ∀ (rest : List (ConstantVal × Nat)) (env : Env) (_mp : EnvModelM V μ env),
      (∀ x ∈ rest, x.2 < k ∧ x.1 = cvRaOf x.2) →
      (∀ x ∈ rest, env.find? x.1.name = none) →
      (∀ t, t < k → (cvRaOf t).type.constsResolve env = true) →
      ConLeche.EtaFamiliesClosed env →
      (rest.map (·.1.name)).Nodup →
      (∀ t, t < k → MutualRecData _mp.base2 (cvRaOf t) nP k n (nIdxOf t) t elimL (rds t)) →
      ∃ mp' : EnvModelM V μ (ConLeche.provisionMutualRecs b fms rest env),
        ConLeche.EtaFamiliesClosed (ConLeche.provisionMutualRecs b fms rest env) ∧
        (∀ t, t < k → (cvRaOf t).type.constsResolve
          (ConLeche.provisionMutualRecs b fms rest env) = true) ∧
        (∀ t, t < k → MutualRecData mp'.base2 (cvRaOf t) nP k n (nIdxOf t) t elimL (rds t)) ∧
        (∀ x ∈ rest, ∀ ψ : Name → Nat, mp'.base2.acval x.1.name ψ = A x.2 ψ) ∧
        (∀ nm : Name, (∀ x ∈ rest, nm ≠ x.1.name) → mp'.base2.acval nm = _mp.base2.acval nm)
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
    obtain ⟨mpR, hacR⟩ := recProvisionCons mp hE (hleaf mIdx hmIdx) hfresh
      (hnres mIdx hmIdx) (hpshape mIdx hmIdx) hwf hcb (hRDs mIdx hmIdx) (hAcl mIdx hmIdx)
      (hAparams mIdx hmIdx)
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
    have hres' : ∀ t, t < k → (cvRaOf t).type.constsResolve
        ⟨.recInfo (cvRaOf mIdx) (b.rulePrefix + (fms.getD mIdx default).nIdx) b.rulePrefix []
          :: env.consts⟩ = true :=
      fun t ht => Expr.constsResolve_mono (hres t ht)
    have hRDs' : ∀ t, t < k → MutualRecData mpR.base2 (cvRaOf t) nP k n (nIdxOf t) t
        elimL (rds t) := fun t ht =>
      (hRDs t ht).cross (c₀ := .recInfo (cvRaOf mIdx)
          (b.rulePrefix + (fms.getD mIdx default).nIdx) b.rulePrefix [])
        hfresh (hcross _) (constsBound_of_constsResolve _ (hres t ht)) mpR.base2 hacR
    obtain ⟨mp', hE'', hres'', hRDs'', hleaf'', hag⟩ :=
      recsProvisionGo hleaf hAcl hAparams hnres hpshape htyWF rest _ mpR
        (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
        (fun x hx => by
          rw [ConLeche.Env.find?_cons, if_neg (fun h => hneRest x hx h.symm)]
          exact hfr x (List.mem_cons_of_mem _ hx))
        hres' hE' (by simpa using hndc.2) hRDs'
    refine ⟨mp', hE'', hres'', hRDs'', ?_, ?_⟩
    · intro x hx ψ
      rcases List.mem_cons.mp hx with heq | hx'
      · subst heq
        show mp'.base2.acval (cvRaOf mIdx).name ψ = A mIdx ψ
        rw [hag (cvRaOf mIdx).name (fun y hy => (hneRest y hy).symm), hacR]
        show acvalWith mp.base2.acval (cvRaOf mIdx).name _ (cvRaOf mIdx).name ψ = _
        rw [acvalWith_self]
      · exact hleaf'' x hx' ψ
    · intro nm hn
      rw [hag nm (fun x hx => hn x (List.mem_cons_of_mem _ hx)), hacR]
      exact acvalWith_ne (hn _ List.mem_cons_self)

/-- **The recursors' provisioning stage**: the `k` recursors of the
block consed RULE-LESS onto the constructors' environment, member `t`
with the leaf `A t`. -/
theorem recsProvision {k nP n : Nat} {nIdxOf : Nat → Nat} {elimL : Level}
    {rds : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {A : Nat → (Name → Nat) → AnnotTerm} {b : MutualBlock} {fms : List MutualFormerA}
    {cvRas : List ConstantVal} {env₂ : Env} (mp₂ : EnvModelM V μ env₂)
    (hlen : cvRas.length = k)
    (hleaf : ∀ t, t < k → ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenotedV V ρ (A t ψ) ∧
      interp V ρ (A t ψ) ∈ˢ interp V ρ (mkPisAV (rds t ψ) (mutualConcAV k n (nIdxOf t) t)))
    (hAcl : ∀ t, t < k → ∀ ψ : Name → Nat, Term.bvarsBelow 0 (A t ψ).erase)
    (hAparams : ∀ t, t < k → ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ q ∈ (cvRas.getD t default).levelParams, ψ₁ q = ψ₂ q) → A t ψ₁ = A t ψ₂)
    (hnres : ∀ t, t < k → ConLeche.reservedBasisNames.contains (cvRas.getD t default).name = false)
    (hpshape : ∀ t, t < k → (cvRas.getD t default).name.isProjFnShape = false)
    (htyWF : ∀ t, t < k → (cvRas.getD t default).type.hasFvar = false ∧
      (cvRas.getD t default).type.allLevelParamsDefined
        (cvRas.getD t default).levelParams = true ∧
      (cvRas.getD t default).type.looseBVarsBounded 0 = true)
    (hnd : (cvRas.map (·.name)).Nodup)
    (hfresh : ∀ t, t < k → env₂.find? (cvRas.getD t default).name = none)
    (hres : ∀ t, t < k → (cvRas.getD t default).type.constsResolve env₂ = true)
    (hE : ConLeche.EtaFamiliesClosed env₂)
    (hRDs : ∀ t, t < k → MutualRecData mp₂.base2 (cvRas.getD t default) nP k n (nIdxOf t) t
      elimL (rds t)) :
    ∃ mp₃ : EnvModelM V μ (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂),
      ConLeche.EtaFamiliesClosed (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂) ∧
      (∀ t, t < k → (cvRas.getD t default).type.constsResolve
        (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂) = true) ∧
      (∀ t, t < k → MutualRecData mp₃.base2 (cvRas.getD t default) nP k n (nIdxOf t) t
        elimL (rds t)) ∧
      (∀ t, t < k → ∀ ψ : Name → Nat, mp₃.base2.acval (cvRas.getD t default).name ψ = A t ψ) ∧
      (∀ nm : Name, (∀ t, t < k → nm ≠ (cvRas.getD t default).name) →
        mp₃.base2.acval nm = mp₂.base2.acval nm) := by
  -- an entry of `cvRas.zipIdx` is a member with its index
  have hzip : ∀ x ∈ cvRas.zipIdx, x.2 < k ∧ x.1 = cvRas.getD x.2 default := by
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
    recsProvisionGo (cvRaOf := fun t => cvRas.getD t default) hleaf hAcl hAparams hnres hpshape
      htyWF cvRas.zipIdx env₂ mp₂
      hzip (fun x hx => by rw [(hzip x hx).2]; exact hfresh x.2 (hzip x hx).1) hres hE hzipNd hRDs
  refine ⟨mp₃, hE₃, hres₃, hRDs₃, ?_, ?_⟩
  · intro t ht ψ
    have hmem : (cvRas.getD t default, t) ∈ cvRas.zipIdx := by
      refine List.mk_mem_zipIdx_iff_getElem?.mpr ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      rfl
    exact hleaf₃ _ hmem ψ
  · intro nm hn
    exact hag nm fun x hx => by rw [(hzip x hx).2]; exact hn x.2 (hzip x hx).1

end ConLeche.Model
