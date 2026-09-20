module

public import ConLeche.Model.Inductives.NestedLoop
import ConLeche.Model.Inductives.StructRows
import ConLeche.Model.Inductives.BlockRecFrames
import ConLeche.Model.Inductives.BlockRepCross
import ConLeche.Model.Inductives.ContainerCross
import ConLeche.Model.Inductives.MutualFormersKit
import ConLeche.Model.Inductives.StructEntryKit
import ConLeche.Model.Inductives.StructRecKit2
import ConLeche.Model.Annot.BitInstall
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Annot.BitExtend
import ConLeche.Model.Steps.Stuck
import ConLeche.Model.Steps.Accepted
import ConLeche.Model.Install
import ConLeche.Model.IndTele
import ConLeche.Verify.Inductives.ContainerFrame
import ConLeche.Verify.Inductives.NestedGroupInv
import ConLeche.Verify.Inductives.NestedAuxFormers
import ConLeche.Verify.Inductives.NestedElimInv
import ConLeche.Verify.Inductives.NestedInv
import ConLeche.Verify.Inductives.NestedCopySort
import ConLeche.Verify.Inductives.NestedCopyProv
import ConLeche.Verify.Denote.Install
public section

/-!
# The pins' facts at the prefix model (task #315, M6 s9)

`NestedPinsStaged` (`NestedLoop.lean`) discharged modulo four named
facts (DESIGN §U.21): one `PinSyn` per pin of the elimination is
CONSTRUCTED from the pin's record (K.28's source, `nestedCopySrcOk_inv`),
the mint group's record (K.29, `nestedGroupsOk_inv`) and the container's
block model (the strengthened premise `PinsModeled`/`ContainerModeled`,
`DeclNestedCore.lean`), read at the group's BASE pin so that one block
model serves the whole group; the components' readings at the prefix
model are the pin's own reading (`pinDs`), which needs the pin's
`inferType` run AT THE PREFIX ENVIRONMENT and the pins' free variables
to be the block's parameter openers — the run conjuncts K.30
(`NestedPinsRun.scoped`; U-19 named this `NestedPinsScoped`); the group's
syntactic fields (`NestedPinGroupSyn`: the segment, the block at every
member, the typing, the injection shape, the pin's shape fields, the
same-universe fact `w`, the pins' recorded index universes `pinU`, the
constructor counts, the components' fit `DsFit`) are PROVED; the
identities (`NestedPinGroupIds`: `idx`, `inst`) stay NAMED with this
consumer — `NestedPinsIdent` (the copy-instantiation identities).

The index universes are no longer among them (task #315 L-A, DESIGN
§U.22): a pin's recorded `u` IS its container's index universe at the
group's level assignment, so `NestedPinGroup.pinU` is a fact of
`pinOf`'s construction and the named `NestedPinsU` is gone.  Nor is the
pin-free restriction (task #315 L-C, DESIGN §U.24): `noPins` is gone
from the group — the assembly reads a container's own pins through its
`pinLeaf` and `pinMono` — and the named `NestedPinsFix` with it.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecFieldKind RecRule
  NestedParts MutualBlock ElimState NestedPin IndCaps ContainerInfo ContainerMember AuxStored
  fueledOps)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## Kit: the prefix formers' cons extends the pre-block environment -/

/-- **The formers' conses extend the environment**: lookups, the
literal guards and the absence of projection tables are preserved
across the conses of fresh, pairwise distinct members. -/
theorem consMutualFormers_ext :
    ∀ {fms : List MutualFormerA} {env : Env},
      (∀ f ∈ fms, env.find? f.cvTa.name = none) → (fms.map (·.cvTa.name)).Nodup →
      FindPreserved env (ConLeche.consMutualFormers fms env) ∧
      LitGuardsMono env (ConLeche.consMutualFormers fms env) ∧
      ∀ (sn : Name) (i : Nat), env.findProj? sn i = none →
        (ConLeche.consMutualFormers fms env).findProj? sn i = none
  | [], _, _, _ => ⟨fun h => h, ⟨id, id⟩, fun _ _ h => h⟩
  | f :: fs, env, hfresh, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have hf : env.find? f.cvTa.name = none := hfresh f List.mem_cons_self
    have hF₁ : FindPreserved env ⟨.indInfo f.cvTa {} :: env.consts⟩ :=
      findPreserved_cons (c₀ := .indInfo f.cvTa {}) hf
    have hG₁ : LitGuardsMono env ⟨.indInfo f.cvTa {} :: env.consts⟩ :=
      litGuardsMono_cons (c₀ := .indInfo f.cvTa {}) hf
    have hP₁ := ConLeche.Verify.findProj?_cons_of_base_none (env := env)
      (c₀ := .indInfo f.cvTa {}) (fun _ h => nomatch h)
    have hfresh' : ∀ g ∈ fs, (⟨.indInfo f.cvTa {} :: env.consts⟩ : Env).find? g.cvTa.name = none := by
      intro g hg
      rw [find?_cons_of_name_ne (c := .indInfo f.cvTa {}) (fun h => hnd.1 (by
        have h' : f.cvTa.name = g.cvTa.name := h
        rw [h']
        exact List.mem_map_of_mem hg))]
      exact hfresh g (List.mem_cons_of_mem _ hg)
    obtain ⟨hF₂, hG₂, hP₂⟩ := consMutualFormers_ext hfresh' hnd.2
    exact ⟨fun h => hF₂ (hF₁ h), ⟨fun h => hG₂.1 (hG₁.1 h), fun h => hG₂.2 (hG₁.2 h)⟩,
      fun sn i h => hP₂ sn i (hP₁ sn i h)⟩

/-- **A lookup at the formers' conses is the base's or a former's own
`indInfo`** — the kinds half of the same conses, with no freshness and
no `Nodup`: `consMutualFormers` conses nothing else. -/
theorem consMutualFormers_find?_cases :
    ∀ {fms : List MutualFormerA} {env : Env} {n : Name} {c : ConstantInfo},
      (ConLeche.consMutualFormers fms env).find? n = some c →
      env.find? n = some c ∨ ∃ f ∈ fms, c = .indInfo f.cvTa {}
  | [], _, _, _, h => Or.inl h
  | g :: gs, env, n, c, h => by
    have h' : (ConLeche.consMutualFormers gs
        ⟨.indInfo g.cvTa {} :: env.consts⟩).find? n = some c := h
    rcases consMutualFormers_find?_cases h' with h₁ | ⟨f, hf, rfl⟩
    · by_cases hn : (ConstantInfo.indInfo g.cvTa {}).name = n
      · rw [ConLeche.Env.find?_cons, if_pos hn] at h₁
        exact Or.inr ⟨g, List.mem_cons_self, (Option.some.inj h₁).symm⟩
      · rw [ConLeche.Env.find?_cons, if_neg hn] at h₁
        exact Or.inl h₁
    · exact Or.inr ⟨f, List.mem_cons_of_mem _ hf, rfl⟩

/-- **A STORED CONTAINER'S GROUP IS READ THE SAME PAST THE FORMERS'
CONSES** (task #315 M7-3 session 20): `ContainerModeled.crossEnv`'s
`hci` at the prefix environment.

`containerInfo?` consults the environment at the container's own
constant, at its recursor and at each member the recursor's motive
names; a reading can therefore only MOVE if one of the conses answers
a lookup that failed before, and `containerInfo?_ext_ind_eq` is
exactly the statement that at a container the base already stores it
cannot — given that the new names are fresh (`hfresh`) and that no
cons is a recursor, which here holds because every one of them is an
`indInfo` (`consMutualFormers_find?_cases`). -/
theorem containerInfo?_consMutualFormers {fms : List MutualFormerA} {env : Env}
    (hwf : ConLeche.EnvWF env) (hrc : ConLeche.RecCtorsStored env)
    (hfresh : ∀ f ∈ fms, env.find? f.cvTa.name = none) {J : Name}
    (hJ : (env.find? J).isSome = true) :
    ConLeche.containerInfo? (ConLeche.consMutualFormers fms env) J
      = ConLeche.containerInfo? env J := by
  have hfreshN : ∀ n ∈ fms.map (·.cvTa.name), env.find? n = none := by
    intro n hn
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hn
    exact hfresh f hf
  -- off the new names the two environments answer the same lookups
  have hne : ∀ n : Name, n ∉ fms.map (·.cvTa.name) →
      (ConLeche.consMutualFormers fms env).find? n = env.find? n := by
    intro n hn
    exact consMutualFormers_find?_of_ne fun g hg heq => hn (heq ▸ List.mem_map_of_mem hg)
  have hstored : ∀ n : Name, (env.find? n).isSome = true → n ∉ fms.map (·.cvTa.name) := by
    intro n hn hmem
    rw [hfreshN n hmem] at hn
    exact nomatch hn
  refine ConLeche.containerInfo?_ext_ind_eq (N := fms.map (·.cvTa.name))
    (fun n c hf => ?_) (fun n c hf => ?_) hfreshN (fun n cv mI rP rules hf hmem => ?_) hwf hrc
    (hstored J hJ)
  · rw [hne n (hstored n (by rw [hf]; rfl))]; exact hf
  · by_cases hn : n ∈ fms.map (·.cvTa.name)
    · exact Or.inr hn
    · rw [hne n hn] at hf; exact Or.inl hf
  · -- a consed constant is an `indInfo`, and the base has nothing at a new name
    rcases consMutualFormers_find?_cases hf with h₁ | ⟨f, -, hc⟩
    · rw [hfreshN _ hmem] at h₁; exact nomatch h₁
    · exact nomatch hc

/-- **A STORED CONTAINER'S OWN-PIN TABLE IS READ THE SAME AT THE PREFIX
ENVIRONMENT** (task #315 M7-3): `ContainerOwnPinsSyn.crossIndOf` at the
members' cons — `containerInfo?_consMutualFormers`' twin for the clause
`ContainerModeled.ownPins`, and with the same frame.

`consMutualFormers` conses `.indInfo`s only, so neither `hrecN` nor
`hmimN` can fire: a name the cons answers with a recursor is the base's,
and the base has nothing at a name the cons claims as new.  The walk
therefore cannot grow at ANY container, which is what the crossing
needs. -/
theorem ownPinsSyn_consMutualFormers {fms : List MutualFormerA} {env : Env}
    {m : EnvModel V env} {ci : ContainerInfo} {d : BlockModel V}
    (hwf : ConLeche.EnvWF env) (hrc : ConLeche.RecCtorsStored env)
    (hfresh : ∀ f ∈ fms, env.find? f.cvTa.name = none)
    (C : ContainerModeled m ci d) (h : ContainerOwnPinsSyn (V := V) env d) :
    ContainerOwnPinsSyn (V := V) (ConLeche.consMutualFormers fms env) d := by
  have hfreshN : ∀ n ∈ fms.map (·.cvTa.name), env.find? n = none := by
    intro n hn
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hn
    exact hfresh f hf
  have hne : ∀ n : Name, n ∉ fms.map (·.cvTa.name) →
      (ConLeche.consMutualFormers fms env).find? n = env.find? n := by
    intro n hn
    exact consMutualFormers_find?_of_ne fun g hg heq => hn (heq ▸ List.mem_map_of_mem hg)
  have hstored : ∀ n : Name, (env.find? n).isSome = true → n ∉ fms.map (·.cvTa.name) := by
    intro n hn hmem
    rw [hfreshN n hmem] at hn
    exact nomatch hn
  -- a consed constant is an `indInfo`, so no new name answers a recursor
  have hnotRec : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      (ConLeche.consMutualFormers fms env).find? n = some (.recInfo cv mI rP rules) →
      n ∈ fms.map (·.cvTa.name) → False := by
    intro n cv mI rP rules hf hmem
    rcases consMutualFormers_find?_cases hf with h₁ | ⟨f, -, hc⟩
    · rw [hfreshN _ hmem] at h₁; exact nomatch h₁
    · exact nomatch hc
  refine ContainerOwnPinsSyn.crossIndOf (N := fms.map (·.cvTa.name))
    (fun n c hf => by rw [hne n (hstored n (by rw [hf]; rfl))]; exact hf)
    (fun n c hf => ?_) hfreshN
    (fun n cv mI rP rules hf hmem => absurd hf (fun hf' => hnotRec _ cv mI rP rules hf' hmem))
    (fun n j cv mI rP rules hf hmem =>
      absurd hf (fun hf' => hnotRec _ cv mI rP rules hf' hmem))
    hwf hrc (recMajorHeadStored_of_envWF hwf) C h
  by_cases hn : n ∈ fms.map (·.cvTa.name)
  · exact Or.inr hn
  · rw [hne n hn] at hf; exact Or.inl hf

/-! ## Kit: two small converses -/

/-- **Well-scopedness from the leaves** (`WScoped_leaves`' converse):
a term whose closure leaves are all below the depth and scoped at
their own index is well-scoped at the depth. -/
theorem WScoped_of_leaves : ∀ (e : Expr) {d : Nat},
    (∀ l ∈ e.fvarLeaves, l.1 < d ∧ Expr.WScoped l.1 l.2) → Expr.WScoped d e := by
  intro e
  induction e with
  | fvar idx ty _ =>
    intro d h
    simp only [Expr.WScoped]
    exact h (idx, ty) (by simp [Expr.fvarLeaves])
  | app f a ihf iha =>
    intro d h
    simp only [Expr.WScoped]
    exact ⟨ihf fun l hl => h l (by simp [Expr.fvarLeaves, hl]),
      iha fun l hl => h l (by simp [Expr.fvarLeaves, hl])⟩
  | lam ty b _ ihty ihb =>
    intro d h
    simp only [Expr.WScoped]
    exact ⟨ihty fun l hl => h l (by simp [Expr.fvarLeaves, hl]),
      ihb fun l hl => h l (by simp [Expr.fvarLeaves, hl])⟩
  | forallE ty b _ ihty ihb =>
    intro d h
    simp only [Expr.WScoped]
    exact ⟨ihty fun l hl => h l (by simp [Expr.fvarLeaves, hl]),
      ihb fun l hl => h l (by simp [Expr.fvarLeaves, hl])⟩
  | letE ty v b ihty ihv ihb =>
    intro d h
    simp only [Expr.WScoped]
    exact ⟨ihty fun l hl => h l (by simp [Expr.fvarLeaves, hl]),
      ihv fun l hl => h l (by simp [Expr.fvarLeaves, hl]),
      ihb fun l hl => h l (by simp [Expr.fvarLeaves, hl])⟩
  | proj s i x ih =>
    intro d h
    simp only [Expr.WScoped]
    exact ih fun l hl => h l (by simp [Expr.fvarLeaves, hl])
  | bvar _ => intro _ _; simp [Expr.WScoped]
  | sort _ => intro _ _; simp [Expr.WScoped]
  | const _ _ => intro _ _; simp [Expr.WScoped]
  | lit _ => intro _ _; simp [Expr.WScoped]

/-- The function part of a well-scoped application is well-scoped
(`lbb_mkAppN_fn`'s twin at the scope predicate). -/
theorem WScoped_mkAppN_fn {d : Nat} : ∀ {xs : List Expr} {f : Expr},
    Expr.WScoped d (Expr.mkAppN f xs) → Expr.WScoped d f := by
  intro xs
  induction xs with
  | nil => intro f h; exact h
  | cons x xs ih =>
    intro f h
    have h' : Expr.WScoped d f ∧ Expr.WScoped d x := by
      simpa only [Expr.WScoped] using ih (f := Expr.app f x) h
    exact h'.1

/-- The arguments of a well-scoped application are well-scoped
(`lbb_mkAppN_args`' twin at the scope predicate): the form a reading
premise asks of a pin's COMPONENTS, given the pin's own scope. -/
theorem WScoped_mkAppN_args {d : Nat} : ∀ {xs : List Expr} {f : Expr},
    Expr.WScoped d (Expr.mkAppN f xs) → ∀ x ∈ xs, Expr.WScoped d x := by
  intro xs
  induction xs with
  | nil => intro f _ x hx; exact nomatch hx
  | cons x xs ih =>
    intro f h y hy
    rcases List.mem_cons.mp hy with rfl | hy'
    · have h' : Expr.WScoped d f ∧ Expr.WScoped d y := by
        simpa only [Expr.WScoped] using
          WScoped_mkAppN_fn (xs := xs) (f := Expr.app f y) h
      exact h'.2
    · exact ih h y hy'

/-- **A spine's readings are the pointwise readings** (the relation is
functional). -/
theorem DenoteMetaSpine.eq_map {acval : Name → (Name → Nat) → AnnotTerm} {φ : Name → Nat}
    {d : Nat} : ∀ {as : List Expr} {vs : List AnnotTerm},
      DenoteMetaSpine acval env φ d as vs →
      vs = as.map fun e => (denoteMeta acval env φ d e).getD default := by
  intro as vs h
  induction h with
  | nil => rfl
  | cons ha _ ih => rw [List.map_cons, ha, Option.getD_some, ih]

/-- **The parameter prefix of a former's reading, as the opened context**:
the first `nP` domains of a `mkPisAV` tower over `nP + nIdx` binders,
innermost first. -/
theorem piTeleAV_mkPisAV_take {nP nIdx : Nat} (pps : List (Nat × Nat × AnnotTerm))
    (hlen : pps.length = nP + nIdx) (C : AnnotTerm) :
    PiTeleAV nP (mkPisAV pps C) (((pps.take nP).map (·.2.2)).reverse) (mkPisAV (pps.drop nP) C) := by
  have h := piTeleAV_mkPisAV (pps.take nP) (mkPisAV (pps.drop nP) C)
  rw [← mkPisAV_append, List.take_append_drop, List.length_take, hlen,
    Nat.min_eq_left (Nat.le_add_right _ _)] at h
  exact h

/-! ## Kit: the container's block model crosses to the prefix model

`ContainerModeled.crossEnv` — every model-dependent clause travels, the
arities and counts are model-free — lives in `ContainerCross.lean`
(task #315 M7-3), below this file with the rest of the field's
maintenance kit. -/

/-- **The prefix formers' cons, as a crossing**: from the pre-block
model to any model of the prefix formers' environment agreeing with it
off the members — the four hypotheses of `crossEnv`. -/
theorem prefixCross_of {fms : List MutualFormerA} {k : Nat} {mp : EnvModelM V μ env}
    (mp₁' : EnvModelM V μ (ConLeche.consMutualFormers (fms.take k) env))
    (hfresh : ∀ f ∈ fms.take k, env.find? f.cvTa.name = none)
    (hnd : ((fms.take k).map (·.cvTa.name)).Nodup)
    (hoff' : ∀ n : Name, (∀ (t : Nat) (f : MutualFormerA), t < k → fms[t]? = some f → n ≠ f.cvTa.name) →
      mp₁'.base2.acval n = mp.base2.acval n) :
    (∀ (n : Name) (c : ConstantInfo), (∀ cv mI rP rules, c ≠ .recInfo cv mI rP rules) →
      env.find? n = some c → (ConLeche.consMutualFormers (fms.take k) env).find? n = some c) ∧
    (∀ e : Expr, e.constsResolve env = true →
      e.constsResolve (ConLeche.consMutualFormers (fms.take k) env) = true) ∧
    (∀ n : Name, (env.find? n).isSome = true → mp₁'.base2.acval n = mp.base2.acval n) ∧
    (∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta mp.base2.acval env ψ dp e = some ea →
      denoteMeta mp₁'.base2.acval (ConLeche.consMutualFormers (fms.take k) env) ψ dp e = some ea) := by
  obtain ⟨hF, hG, hP⟩ := consMutualFormers_ext hfresh hnd
  have hag : ∀ n : Name, (env.find? n).isSome = true → mp₁'.base2.acval n = mp.base2.acval n := by
    intro n hn
    refine hoff' n fun t f ht hft heq => ?_
    have hft' : f ∈ fms.take k := List.mem_of_getElem? (by
      rw [List.getElem?_take_of_lt ht]; exact hft)
    rw [heq, hfresh f hft'] at hn
    exact nomatch hn
  refine ⟨fun _ _ _ hf => hF hf, constsResolve_of_findPreserved hF, hag, ?_⟩
  intro ψ dp e ea he
  refine denoteMeta_env_mono hF hG hP dp e ?_
  rw [denoteMeta_acval_congr (env := env) (φ := ψ) hag]
  exact he

/-! ## Kit: a pin's graded reading and its fit -/

/-- **A pin's reading at the model of the environment its `inferType`
ran at** — graded at every frame satisfying the block's parameter
context: the first former's opening (`opened_of`) supplies the context,
the pin's free variables being that opening's variables supplies the
scope and the leaves' bounds, and the checker's claims (`inferRow`)
supply the grading. -/
theorem pinRead_of_inferAt (hμ : μ.verifiedChecks = true) {F nP nIdx₀ : Nat}
    (mp₁ : EnvModelM V μ env) {cvT₀ : ConstantVal} {s₀ : Level}
    {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hFD : FormerData mp₁.base2 cvT₀ (nP + nIdx₀) s₀ pps)
    (hcl : cvT₀.type.hasFvar = false) (hbt : cvT₀.type.looseBVarsBounded 0 = true)
    {fvs : List Expr} {o : Expr} (hop : ConLeche.openPisAtFvars nP cvT₀.type 0 = some (fvs, o))
    {pin ty : Expr} (hi : ConLeche.inferTypeCore μ env F nP pin = .ok ty)
    (hb : pin.looseBVarsBounded 0 = true) (hleaf : ∀ l ∈ pin.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs)
    (ψ : Name → Nat) :
    ∃ ea, denoteMeta mp₁.base2.acval env ψ nP pin = some ea ∧
      ∀ ρ : Nat → V, Sat V ((((pps ψ).take nP).map (·.2.2)).reverse) ρ → WellDenotedV V ρ ea := by
  obtain ⟨Γ, R, htele, O⟩ := opened_of (V := V) hop hcl hbt (hFD.read ψ) (hFD.okTy ψ)
  obtain ⟨rfl, -⟩ := PiTeleAV.unique htele
    (piTeleAV_mkPisAV_take (pps ψ) (hFD.len ψ) (.sort (s₀.eval ψ)))
  have hlenF : fvs.length = nP := openPisAtFvars_length nP hop
  have hidx := openPisAtFvars_index nP cvT₀.type 0 hop
  -- a leaf is an opener at its own index
  have hleafAt : ∀ l ∈ pin.fvarLeaves, fvs[l.1]? = some (Expr.fvar l.1 l.2) := by
    intro l hl
    obtain ⟨pos, hpos⟩ := List.getElem?_of_mem (hleaf l hl)
    obtain ⟨ty', hx⟩ := hidx pos _ hpos
    rw [Nat.zero_add] at hx
    obtain ⟨rfl, -⟩ : l.1 = pos ∧ l.2 = ty' := by
      injection hx with a b
      exact ⟨a, b⟩
    exact hpos
  have hws : Expr.WScoped nP pin := by
    refine WScoped_of_leaves pin fun l hl => ?_
    have hat := hleafAt l hl
    obtain ⟨-, hw, -, -, -⟩ := O.var l.1 _ hat
    exact ⟨by rw [← hlenF]; exact (List.getElem?_eq_some_iff.mp hat).1, hw⟩
  have hL : Expr.LeavesBounded pin := by
    intro l hl
    obtain ⟨-, -, hbd, -, -⟩ := O.var l.1 _ (hleafAt l hl)
    exact hbd
  have hC : CtxOk mp₁.base2 ψ nP ((((pps ψ).take nP).map (·.2.2)).reverse) pin := by
    have := O.ctx (i := nP) (Nat.le_refl _) hws hleaf
    rwa [Nat.sub_self, List.drop_zero] at this
  obtain ⟨ea, hea⟩ := acceptedReads_of mp₁.base2 ψ hi hws hb hL
  obtain ⟨-, -, hok, -, -⟩ := (claimsAt_of hμ mp₁ ψ F).inferRow hi hws hb hL hC hea
  exact ⟨ea, hea, hok⟩

/-- **A graded application of a container at its parameters fits the
container's parameter telescope** — `nestedFit_of_wd`'s twin at the
parameters (the member's telescope prefix reframed as the block
model's `params` by the frame clause). -/
theorem pinFit_of_wd {m : EnvModel V env} {dJ : BlockModel V} {i : Nat} {J : Name}
    {cvT cvR : ConstantVal} {mI rP : Nat} {rules : List RecRule}
    (hI : IsBlockModel m J cvT cvR mI rP rules dJ i) (hreps : IsBlockModels m dJ)
    {ψJ : Name → Nat} (hFT : FormersTyped m dJ ψJ)
    (hfr : ∀ ρ : Nat → V, Sat V (dJ.params ψJ).reverse ρ ↔
      Sat V (((dJ.ppsM i ψJ).take dJ.nP).map (·.2.2)).reverse ρ)
    {Ds : List AnnotTerm} (hDl : Ds.length = dJ.nP) {ρ : Nat → V}
    (hwd : WellDenoted V ρ (AnnotTerm.mkAppN (m.acval J ψJ) Ds)) :
    SpineFit ρ (dJ.params ψJ) (Ds.map (interp V ρ)) := by
  have hFT' := hFT i hI.memberLt ρ
  rw [hI.member] at hFT'
  have hfit := spineFit_of_wellDenoted_mkAppN_pis (C := .sort (dJ.w ψJ)) (ds := dJ.ppsM i ψJ)
    (σ := ρ) (ρ := ρ) (fv := interp V ρ (m.acval J ψJ))
    (fun d' hd' => hI.former.bits ψJ d' hd')
    (by rw [hDl, hI.ppsM_length]; exact Nat.le_add_right _ _) hwd rfl hFT'
  rw [hDl] at hfit
  obtain ⟨cvT₀, cvR₀, mI₀, rP₀, rules₀, hI₀⟩ := hreps 0 (Nat.lt_of_le_of_lt (Nat.zero_le _) hI.memberLt)
  refine spineFit_of_frames ?_ (fun ρ' => (hfr ρ').symm) hfit
  show (((dJ.ppsM i ψJ).take dJ.nP).map (·.2.2)).length = (((dJ.ppsM 0 ψJ).take dJ.nP).map (·.2.2)).length
  rw [List.length_map, List.length_map, List.length_take, List.length_take, hI.ppsM_length,
    hI₀.ppsM_length, Nat.min_eq_left (Nat.le_add_right _ _), Nat.min_eq_left (Nat.le_add_right _ _)]

/-! ## One pin's data against two records (task #315 PINF) -/

/-- **ONE PIN'S INDEX DATA, READ OFF TWO RECORDS** (task #315 PINF):
a recorded pin `pq` whose container is member `i₂` of that container's
own block model `B ciB`, and a pin `qq` of another block model `d` at
the SAME container name seen through `d`'s `PinShapes` view at the same
family `B`, have one index-tuple sort and one index telescope — as soon
as their level assignments agree on the container's own level
parameters.

**This is the identification `NestedPinGroupSyn.pinViews` deliberately
omitted**, paid here rather than by a structure parameter: the view
`pinViews` hands back is at an ANONYMOUS block model, and two anonymous
models of one container group cannot be compared (`blockOf` is a choice
function with no uniqueness in this tier).  Both sides here read the
family `B` at the same `ci`, which `containerInfo?`'s functionality
forces from the pins' NAME equality — so no equality of choices is
demanded and none is needed.

The assignments are compared POINTWISE on the container's own level
parameters and never as functions: that is the form the copies' side
produces (`copyPinFCorr`'s level agreement), and the two congruences
that consume it — `IsBlockModel.uParams` for the sort and
`FormerData.params` for the telescope — are stated over exactly that
membership. -/
theorem pinOwn_core {env₀ : Env} {m₀ : EnvModel V env₀} {B : ContainerInfo → BlockModel V}
    {d : BlockModel V} {pc : Nat → PinCtors V} (hSh : PinShapes m₀ B d pc)
    {qq : Nat} (hqq : qq < d.nPins) {ciB : ContainerInfo}
    (hciB : ContainerModeled m₀ ciB (B ciB)) {pq : PinSyn} {i₂ : Nat}
    (hJ : pq.J = (d.pinAt qq).J)
    (hciB' : ConLeche.containerInfo? env₀ pq.J = some ciB)
    (hi₂ : i₂ < (B ciB).k) (hname₂ : (B ciB).memberName i₂ = pq.J)
    (hu₂ : ∀ φ : Name → Nat, pq.u φ = (B ciB).uM i₂ (pq.ψJ φ))
    (hpps₂ : pq.pps = (B ciB).ppsM i₂) (hnP₂ : pq.nPJ = (B ciB).nP)
    {cv : ConstantVal} {caps : IndCaps}
    (hfind : env₀.find? pq.J = some (.indInfo cv caps)) (φ ψ' : Name → Nat)
    (hag : ∀ pp ∈ cv.levelParams, pq.ψJ φ pp = (d.pinAt qq).ψJ ψ' pp) :
    pq.u φ = (d.pinAt qq).u ψ' ∧ pq.Ids φ = (d.pinAt qq).Ids ψ' := by
  -- the pin of `d`, in its own group, against the SAME family
  obtain ⟨a, kk, i', ci', hqe, hi', hci', hview, -, -⟩ := hSh qq hqq
  obtain rfl : ciB = ci' := Option.some.inj ((hJ ▸ hciB').symm.trans hci')
  subst hqe
  -- the two member indices name one member, hence are one index
  have hnameV : (d.pinAt (a + i')).J = (B ciB).memberName i' := hview.name i' hi'
  obtain rfl : i₂ = i' :=
    hciB.memberName_inj hciB' hi₂ (by rw [hview.kEq]; exact hi')
      (by rw [hname₂, hJ, hnameV])
  -- the container's own record at that member, and its level parameters
  obtain ⟨M, hM⟩ : ∃ M, ciB.members[i₂]? = some M :=
    ⟨_, List.getElem?_eq_getElem (by rw [← hciB.k]; exact hi₂)⟩
  obtain ⟨hMname, -, cvR, mI, rP, rules, hI⟩ := hciB.member i₂ M hM
  obtain ⟨cvT₀, -, -, -, rP₀, -, -, -, -, -, hmems⟩ := ConLeche.containerInfo?_inv hciB'
  obtain ⟨cvC, capsC, -, -, -, hfC, -, hMlps, -, -, -, -⟩ := hmems M (List.mem_of_getElem? hM)
  have hMJ : M.name = pq.J := by rw [← hMname, hname₂]
  obtain rfl : cvC = cv := by
    rw [hMJ] at hfC
    exact (ConLeche.ConstantInfo.indInfo.inj (Option.some.inj (hfC.symm.trans hfind))).1
  have hag' : ∀ pp ∈ M.lps, pq.ψJ φ pp = (d.pinAt (a + i₂)).ψJ ψ' pp := by
    rw [hMlps]; exact hag
  -- the sort and the telescope, moved along the two congruences
  have hψ : (d.pinAt (a + i₂)).ψJ ψ' = (d.pinAt a).ψJ ψ' := (hview.same i₂ hi' ψ').1
  refine ⟨?_, ?_⟩
  · rw [hu₂ φ, hI.uParams i₂ hi₂ _ _ hag', hview.pinU i₂ hi' ψ', hψ]
  · show ((pq.pps (pq.ψJ φ)).drop pq.nPJ).map (·.2.2)
      = (((d.pinAt (a + i₂)).pps ((d.pinAt (a + i₂)).ψJ ψ')).drop
          (d.pinAt (a + i₂)).nPJ).map (·.2.2)
    rw [hpps₂, hnP₂, hview.pinPps i₂ hi', hview.pinNP i₂ hi',
      (hI.former.params _ _ hag').1]

/-! ## The group's facts, split into the PROVED and the NAMED halves -/

section Assembly

variable {F : Nat} {g : Bool} {mp : EnvModelM V μ env} {p : NestedParts} {b : MutualBlock}
  {fms : List MutualFormerA} {f₀ : MutualFormerA} {ctorsA : List (ConstantVal × Nat)}
  {sortss : List (List Level)} {kinds : List (List (RecFieldKind × Nat))}
  {mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env)}
  {ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {W : (Name → Nat) → Nat}
  {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
  {fvsPF xFvsF : Nat → List Expr} {xrestF : Nat → Expr}
  {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
  {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
  {ctorsR : List (List (ConstantVal × Nat × Nat))}
  {dsR : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {xFvsR : Nat → Nat → List Expr}
  {pinsS : List PinSyn} {env₂ : Env}

local notation "D" => (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
  srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS)

local notation "PG" => NestedPinGroup (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀)
  (ctorsA := ctorsA) (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF)
  (dsF := dsF) (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
  (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS)

/-- **A pin group's SYNTACTIC facts** (PROVED this session, DESIGN
§U.21 (c)): `NestedPinGroup` without `noPins`/`u`/`idx`/`inst` — the
segment, the container's block model at every member, `IsBlockModel`
at each pin's container (with the pin's level assignment SPELLED as
the substitution at the container's level parameters), the typing,
the injection shape, the pin's shape fields (the recorded index
universe `pinU` among them — each pin's is its container's, §U.22),
the same-universe fact `w`, the constructor counts and the components'
fit. -/
structure NestedPinGroupSyn (st : ElimState) (m : EnvModel V env₂) (q₀ kJ : Nat) (dJ : BlockModel V) :
    Prop where
  seg : q₀ + kJ ≤ pinsS.length
  kpos : 0 < kJ
  /-- the group IS the elimination's mint group (task #315 L-E, at lane
  L-B's request: every group-indexed run Bool — K.32 among them — is
  keyed by the pin's recorded `grpBase`/`grpSize`) -/
  grp : ∀ i, i < kJ →
    (st.pins.getD (q₀ + i) default).grpBase = q₀ ∧ (st.pins.getD (q₀ + i) default).grpSize = kJ
  /-- the container's block model in the container's own terms, at the
  pin's OWN `containerInfo?` group (task #315 L-E, at lane L-B's
  request: `ordFree`/`pinsNotMembers` live here, not in `IsBlockModel`) -/
  modeled : ∀ i, i < kJ → ∀ ci : ContainerInfo,
    ConLeche.containerInfo? env ((D).pinAt (q₀ + i)).J = some ci → ContainerModeled m ci dJ
  /-- **the group's OWN pins read the same at the ELIMINATION's
  environment** (task #315, integration 3r): `ContainerModeled.pinConts`
  (lane M7-3 session 20) says a pin's container reads the same at
  `d.env₀` as at the record's environment — and `modeled`'s record is at
  the FORMERS' prefix model, so a consumer working at `env`, where
  `replaceAllNested` actually runs, cannot use it there.  The
  construction discharges this from the PRE-BLOCK record, whose own
  `pinConts` concludes at `env` on the nose; lane L-B's pin route spends
  it where it used to name `dJ.env₀ = env` as an input. -/
  contsEnv : ∀ q', q' < dJ.nPins → ∀ ci' : ContainerInfo,
    ConLeche.containerInfo? dJ.env₀ (dJ.pinAt q').J = some ci' →
    ConLeche.containerInfo? env (dJ.pinAt q').J = some ci'
  reps : IsBlockModels m dJ
  kEq : dJ.k = kJ
  rep : ∀ i, i < kJ → ∃ (cvT cvR : ConstantVal) (mI rP : Nat) (rules : List RecRule),
    IsBlockModel m ((D).pinAt (q₀ + i)).J cvT cvR mI rP rules dJ i ∧
    ∀ ψ : Name → Nat,
      ((D).pinAt (q₀ + i)).ψJ ψ = Level.substFn ψ cvT.levelParams ((D).pinAt (q₀ + i)).lvls
  typed : ∀ ψ : Name → Nat, FormersTyped m dJ ψ
  pinsTyped : ∀ ψ : Name → Nat, PinsTyped m dJ ψ
  inj : ∀ (ψJ : Name → Nat) (mm' j : Nat) (fs : List V),
    dJ.inj ψJ mm' j fs = injW (dJ.w ψJ) j (mkTower (fs ++ [pt]))
  pinU : ∀ i, i < kJ → ∀ (ψ : Name → Nat) (i' : Nat), i' < kJ →
    ((D).pinAt (q₀ + i')).u ψ = dJ.uM i' (((D).pinAt (q₀ + i)).ψJ ψ)
  pinNP : ∀ i, i < kJ → ((D).pinAt (q₀ + i)).nPJ = dJ.nP
  pinNIdx : ∀ i, i < kJ → ((D).pinAt (q₀ + i)).nIdx = dJ.nIdxAt i
  pinPps : ∀ i, i < kJ → ((D).pinAt (q₀ + i)).pps = dJ.ppsM i
  pinDsLen : ∀ i, i < kJ → ∀ ψ : Name → Nat, (((D).pinAt (q₀ + i)).Ds ψ).length = dJ.nP
  /-- the group's pins share the level arguments and the components -/
  same : ∀ i, i < kJ →
    ((D).pinAt (q₀ + i)).lvls = ((D).pinAt q₀).lvls ∧
    ((D).pinAt (q₀ + i)).DsE = ((D).pinAt q₀).DsE
  /-- the group's pins share the components' READINGS (task #315 L-E:
  `PinGroupView.same`'s second half) -/
  sameDs : ∀ i, i < kJ → ∀ ψ : Name → Nat, ((D).pinAt (q₀ + i)).Ds ψ = ((D).pinAt q₀).Ds ψ
  w : ∀ i, i < kJ → ∀ ψ : Name → Nat, dJ.w (((D).pinAt (q₀ + i)).ψJ ψ) = f₀.s.eval ψ
  ctorCount : ∀ i', i' < kJ → (dJ.ctorsM i').length = (b.ownCtors (p.k + q₀ + i')).length
  DsFit : ∀ i, i < kJ → ∀ (ψ : Name → Nat) (ρ : Nat → V) (as : List V),
    SpineFit ρ ((D).params ψ) as →
    SpineFit (consList as ρ) (dJ.params (((D).pinAt (q₀ + i)).ψJ ψ))
      ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V (consList as ρ)))
  /-- `rep` at the STORED constant (task #315 L-B): the block at the
  pin's container is asserted at the constant the environment holds
  under that name — the syntactic identities read the stored type -/
  stored : ∀ i, i < kJ → ∃ (cvT : ConstantVal) (caps : IndCaps) (cvR : ConstantVal) (mI rP : Nat)
    (rules : List RecRule),
    env₂.find? ((D).pinAt (q₀ + i)).J = some (.indInfo cvT caps) ∧
    IsBlockModel m ((D).pinAt (q₀ + i)).J cvT cvR mI rP rules dJ i ∧
    ∀ ψ : Name → Nat,
      ((D).pinAt (q₀ + i)).ψJ ψ = Level.substFn ψ cvT.levelParams ((D).pinAt (q₀ + i)).lvls
  /-- the group's pins share the level assignment (the members of a
  container group share their level parameters; task #315 L-B) -/
  ψJEq : ∀ i i', i < kJ → i' < kJ → ∀ ψ : Name → Nat,
    ((D).pinAt (q₀ + i)).ψJ ψ = ((D).pinAt (q₀ + i')).ψJ ψ
  /-- **`dJ`'s OWN pins, VIEWED** (task #315 L-E, at lane L-B's
  request): every pin of the CONTAINER's block model sits in a group of
  some block model, which is what carries its parameter count
  (`PinGroupView.pinNP`), its projection data (`pinPps`) and its
  universe (`pinU`) at the composed assignment.

  **Consequences, not an identification.**  The identification "`dJ` IS
  the chosen model at its container" would drag the PRE-BLOCK model onto
  this structure — a new PARAMETER, which breaks named-argument call
  sites silently at twelve places in four files.  That cost stands.

  **The SECOND reason this docstring used to give is STALE** (task #315
  L-E, 2026-09-18).  It said the identification "is not cheaply
  available anyway: `blockOf` is a choice function with no uniqueness in
  this tier, so `crossEnv` gives 'satisfies the predicate', never
  equality".  **No equality is demanded, so no uniqueness is needed.**
  `PinShapes` takes the container model family ABSTRACTLY
  (`B : ContainerInfo → BlockModel V`, not `blockOf`) and hands back
  `PinGroupView d (B ci) q₀ kJ` at the pin's own container record —
  `NestedCopyInst.lean` records that correction in terms, against an
  earlier revision of its own comment that had made the same mistake.
  Two sides that both read `B` at the same `ci` agree by construction,
  and `ci` is forced by the pins' NAME equality through
  `containerInfo?`'s functionality, not by any choice being unique.

  So the objection to naming the model is the threading cost alone.
  These three consequences are what the consumer actually reads, they
  mention no object the record does not already carry, and so they are
  FIELDS.

  **AND THE COST LEG HAS NOW BEEN PAID, WITHOUT THE PARAMETER** (task
  #315 PINF).  The consequence this field does NOT carry — a pin's index
  data against the NAMED model of its container — is what residual 3's
  `PinCorr` needs, and it is not reachable from the anonymous view: two
  models of one container group are incomparable here.  It is also not
  reachable from the discharger's own `PinsModeled`, which gives
  `PinShapes` at `blockOf mp.base2 ci` while the residual's `dJ` is
  bound abstractly by `NestedPinsIdsAt`.  What closes it is `pinOwn`
  below, which states the identification AGAINST THE BLOCK'S OWN PIN
  TABLE — an object this structure already carries — so the producer,
  which does hold the pre-block model, discharges it and no call site
  moves. -/
  pinViews : ∀ qq, qq < dJ.nPins → ∃ (a kk i' : Nat) (dJ' : BlockModel V),
    qq = a + i' ∧ i' < kk ∧ PinGroupView dJ dJ' a kk
  /-- **THE BLOCK'S PIN AND THE CONTAINER'S OWN PIN ARE ONE PIN'S INDEX
  DATA** (task #315 PINF): where a pin of the BLOCK spells one of `dJ`'s
  own pins — the same container name, and level assignments agreeing on
  that container's own level parameters — the two records give one
  index-tuple sort and one index telescope.

  **This is the identification `pinViews` omits, stated where it can be
  discharged rather than bought with a structure parameter.**  `pinViews`
  hands its view back at an ANONYMOUS block model, and two anonymous
  models of one container group cannot be compared; naming the model in
  `pinViews` itself would put the pre-block model on this structure — the
  parameter its own docstring prices.  This clause needs no such
  parameter: it mentions only the block's own pin table (`pinsS`, through
  `D`) and `dJ`, and its producer, which HAS the pre-block model, closes
  it with `pinOwn_core` at the one family `blockOf mp.base2`.

  The consumer is residual 3's `PinCorr`, whose `u` and `Ids` clauses
  (`copyPinFUIds`) are exactly this at the block pin the copy's nested
  field landed on; the level agreement is `copyPinFCorr`'s, pointwise and
  not as functions. -/
  pinOwn : ∀ qq, qq < dJ.nPins → ∀ q₂, q₂ < pinsS.length →
    ((D).pinAt q₂).J = (dJ.pinAt qq).J →
    ∀ (cv : ConstantVal) (caps : IndCaps),
      env₂.find? (dJ.pinAt qq).J = some (.indInfo cv caps) →
    ∀ φ ψ' : Name → Nat,
      (∀ pp ∈ cv.levelParams, ((D).pinAt q₂).ψJ φ pp = (dJ.pinAt qq).ψJ ψ' pp) →
      ((D).pinAt q₂).u φ = (dJ.pinAt qq).u ψ' ∧
      ((D).pinAt q₂).Ids φ = (dJ.pinAt qq).Ids ψ'
  /-- **the block model's constructors ARE the pin's own container
  member's**, by name and in order, and the parameter counts agree
  (task #315 L-B): a pin records its OWN container's group, the block
  model is the group's BASE member's, and a member record is a
  function of the environment at its name and the group's `nP`
  (`containerInfo?_member_det`) — so the copies' identities may read
  the constructor records the mint copied off positionally. -/
  ctorsOf : ∀ i', i' < kJ → ∀ (ciJ : ContainerInfo) (J : ContainerMember),
    ConLeche.containerInfo? env ((D).pinAt (q₀ + i')).J = some ciJ →
    J ∈ ciJ.members → J.name = ((D).pinAt (q₀ + i')).J →
    (dJ.ctorsM i').map (·.1.name) = J.ctors.map (·.name) ∧ dJ.nP = ciJ.nP

/-- **A pin group's IDENTITY facts** (NAMED, DESIGN §U.21 (e), §U.22,
§U.24): the copy-instantiation identities (K.28's pre-image computed
through `replaceAllNested`'s action; at a container that is itself
nested, `CopyCtorInst.pinF`).  The pin-free restriction `noPins` is
gone (task #315 L-C), and the index-universe agreement `u` with it
(task #315 L-A: a pin's recorded universe is its container's,
`NestedPinGroupSyn.pinU`). -/
structure NestedPinGroupIds (m : EnvModel V env₂) (q₀ kJ : Nat) (dJ : BlockModel V) : Prop where
  idx : ∀ i, i < kJ → ∀ (ψ : Name → Nat) (i' : Nat), i' < kJ →
    blockIds b.nP ppsF ψ (p.k + q₀ + i')
      = instTele (((D).pinAt (q₀ + i)).Ds ψ) 0 (dJ.IdsM i' (((D).pinAt (q₀ + i)).ψJ ψ))
  /-- the copies' constructor SHAPES (lane L-B) -/
  shape :
    ∀ i, i < kJ → ∀ (cvT : ConstantVal) (caps : IndCaps),
      env₂.find? ((D).pinAt (q₀ + i)).J = some (.indInfo cvT caps) →
      ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V ((D).params ψ).reverse ρp →
      ∀ i', i' < kJ → ∀ j, j < (dJ.ctorsM i').length →
      CopyShapeA (V := V) (nP := b.nP) (k := p.k) (resSort := f₀.s) (ppsA := ppsF) (W := W)
        (pins := pinsS) (offs := b.ownOffset) (memberNames := (D).memberNames)
        (tgtsG := mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA))
        (rss := blkRss ctorsA kinds) (tlss := fun ψ => mutTlss ctorsA.length tssF ψ)
        (Eiss₀ := fun ψ => mutEiss0 ctorsA.length eissF ψ)
        (Fss₀ := fun ψ => blkFss0 b ctorsA kinds dsF ψ)
        (Ess₀ := fun ψ => mutEss0 ctorsA.length esF ψ) (ψ := ψ) (ρp := ρp)
        m.acval dJ (((D).pinAt (q₀ + i)).ψJ ψ) (((D).pinAt (q₀ + i)).Ds ψ)
        ((D).pinAt (q₀ + i)).DsE cvT.levelParams ((D).pinAt (q₀ + i)).lvls q₀ kJ i' j
  /-- the copies' ENTRIES at the auxiliary carrier (`nestedPinLeaf_all`) -/
  entry :
    ∀ i, i < kJ → ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V ((D).params ψ).reverse ρp →
      ∀ i', i' < kJ → ∀ j, j < (dJ.ctorsM i').length →
      CopyEntryA (V := V) (nP := b.nP) (k := p.k) (resSort := f₀.s) (ppsA := ppsF) (W := W)
        (pins := pinsS) (offs := b.ownOffset) (mems := mutMems ctorsA.length (mutMemF b))
        (nFs := mutNFs ctorsA.length (mutNFOf ctorsA))
        (tgtsG := mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA))
        (rss := blkRss ctorsA kinds) (tlss := fun ψ => mutTlss ctorsA.length tssF ψ)
        (Eiss₀ := fun ψ => mutEiss0 ctorsA.length eissF ψ)
        (Fss₀ := fun ψ => blkFss0 b ctorsA kinds dsF ψ)
        (Ess₀ := fun ψ => mutEss0 ctorsA.length esF ψ) (ψ := ψ) (ρp := ρp)
        dJ (((D).pinAt (q₀ + i)).ψJ ψ) (((D).pinAt (q₀ + i)).Ds ψ) q₀ kJ i' j
  /-- **the instance map, as the assembly's σ** (task #315 WIDE (3′)):
  the NAMED residual of this structure, discharged from K.61, K.62 and
  K.66 at the run (`NestedPinsRun.instMapSigmaFacts`, `instTgtAt`,
  `instOutAt`). -/
  inst : PinGroupInst (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
    (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF)
    (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
    (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS) q₀ kJ dJ
  /-- **THE OWNER'S HALF OF THE TWO COPIES' FIELD-DATA TIE** (task #315
  WIDE (3), step 1(a), K.69's model side): at a field the pin's
  container calls ORDINARY and the block's rewrite made recursive,
  whose block target is not a member of the block, the OWNER's own
  recomputation of the field's target reads as an application whose
  arguments past the head container's parameters are the COPY's index
  expressions (`OrdTargetRead`).

  `inst`'s `hordσ` relates the two copies' TARGETS; this relates their
  index EXPRESSIONS, which is what the wide identification's pin half
  asks for where it compares two index spines rather than two class
  numbers.  The frame (`ψ`, `ρp`) and a fitting prefix are INPUTS, the
  way `CopyCtorShape`'s `ordF` conjunct takes them.

  The guard is the level-instantiated stored DOMAIN's head and not
  `ordTargetDom`'s: `instSeq_getAppFn_const` carries a constant head
  forward through the components' instantiation and not back.  A
  constant-headed domain is not a `Π`, so the recomputation's tower is
  empty under this guard and the cut is the field's own `l`; the
  statement keeps the general cut (`OrdTargetRead` computes it) so
  that relaxing the guard to the stripped head moves nothing else. -/
  ordTgt : ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V ((D).params ψ).reverse ρp →
      ∀ i', i' < kJ → ∀ j, j < (dJ.ctorsM i').length → ∀ l,
      l < ((dJ.Fss i' (((D).pinAt q₀).ψJ ψ)).getD j []).length →
      ((dJ.rss i').getD j []).getD l false = false →
      ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l false = true →
      ¬ ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 < p.k →
      ∀ (cA : ConstantVal × Nat) (bs : List (Expr × ConLeche.BinderMeta)) (rr : Expr)
        (dom : Expr × ConLeche.BinderMeta) (lps lpsC : List Name),
      (dJ.ctorsM i')[j]? = some cA →
      cA.1.type.stripPis (dJ.nP + cA.2) = some (bs, rr) →
      bs[dJ.nP + l]? = some dom →
      ∀ i₀, i₀ < kJ → ∀ (ciC : ContainerInfo) (Jm : ContainerMember),
      ConLeche.containerInfo? env ((D).pinAt (q₀ + i₀)).J = some ciC →
      ciC.members[i']? = some Jm → Jm.lps = lpsC →
      ∀ (K : Name) (usK : List Level),
      (Expr.instantiateLevelParams lpsC ((D).pinAt (q₀ + i')).lvls dom.1).getAppFn
          = .const K usK →
      ∃ z : Nat, z < (D).nPins ∧
        ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
          (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 = p.k + z ∧
        (((mutEiss0 ctorsA.length eissF ψ).getD
          (b.ownOffset (p.k + q₀ + i') + j) []).getD l []).length = ((D).pinAt z).nIdx ∧
        OrdTargetRead (V := V) m.acval env₂ ψ ρp b.nP l
          (((D).pinAt q₀).Ds ψ)
          ((dJ.Fss i' (((D).pinAt q₀).ψJ ψ)).getD j [])
          (((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l [])
          (((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l [])
          ((D).pinAt z).nPJ lpsC dJ.nP (q₀ + i') ((D).ownPinTerms lps) dom.1
  /-- **THE OWNER'S HALF OF THE TWO COPIES' FIELD-DATA TIE, AT A
  MEMBER TARGET** (task #315 WIDE (3), step 3): `ordTgt`'s sibling at
  the other arm of the target split — the block's rewrite sent the
  field to one of the BLOCK's own members, and the owner's own
  recomputation of its target reads as an application whose arguments
  past the BLOCK's parameters are the COPY's index expressions.

  The two counts are the MEMBER's own (`b.nP` for the head's
  parameters, `nIdxAt` for the index expressions) where the pin arm
  reads the target pin's `nPJ`/`nIdx`; nothing here names a container
  record, because at a member target the positivity normalisation
  lands on the copy's stored domain with no rewrite between them. -/
  ordTgtMem : ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V ((D).params ψ).reverse ρp →
      ∀ i', i' < kJ → ∀ j, j < (dJ.ctorsM i').length → ∀ l,
      l < ((dJ.Fss i' (((D).pinAt q₀).ψJ ψ)).getD j []).length →
      ((dJ.rss i').getD j []).getD l false = false →
      ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l false = true →
      ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 < p.k →
      ∀ (cA : ConstantVal × Nat) (bs : List (Expr × ConLeche.BinderMeta)) (rr : Expr)
        (dom : Expr × ConLeche.BinderMeta) (lps lpsC : List Name),
      (dJ.ctorsM i')[j]? = some cA →
      cA.1.type.stripPis (dJ.nP + cA.2) = some (bs, rr) →
      bs[dJ.nP + l]? = some dom →
      ∀ i₀, i₀ < kJ → ∀ (ciC : ContainerInfo) (Jm : ContainerMember),
      ConLeche.containerInfo? env ((D).pinAt (q₀ + i₀)).J = some ciC →
      ciC.members[i']? = some Jm → Jm.lps = lpsC →
      ∀ (K : Name) (usK : List Level),
      (Expr.instantiateLevelParams lpsC ((D).pinAt (q₀ + i')).lvls dom.1).getAppFn
          = .const K usK →
      ∃ mm : Nat, mm < p.k ∧
        ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
          (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 = mm ∧
        (((mutEiss0 ctorsA.length eissF ψ).getD
          (b.ownOffset (p.k + q₀ + i') + j) []).getD l []).length = (D).nIdxAt mm ∧
        OrdTargetRead (V := V) m.acval env₂ ψ ρp b.nP l
          (((D).pinAt q₀).Ds ψ)
          ((dJ.Fss i' (((D).pinAt q₀).ψJ ψ)).getD j [])
          (((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l [])
          (((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l [])
          b.nP lpsC dJ.nP (q₀ + i') ((D).ownPinTerms lps) dom.1

local notation "PGS" => NestedPinGroupSyn (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀)
  (ctorsA := ctorsA) (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF)
  (dsF := dsF) (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
  (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS)

local notation "PGI" => NestedPinGroupIds (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀)
  (ctorsA := ctorsA) (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF)
  (dsF := dsF) (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
  (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS)

/-- The group from its two halves. -/
theorem NestedPinGroupSyn.ofParts {st : ElimState} {m : EnvModel V env₂} {q₀ kJ : Nat}
    {dJ : BlockModel V} (S : PGS st m q₀ kJ dJ) (I : PGI m q₀ kJ dJ) : PG m q₀ kJ dJ :=
  { seg := S.seg, kpos := S.kpos, reps := S.reps, kEq := S.kEq
    rep := fun i hi => by
      obtain ⟨cvT, cvR, mI, rP, rules, hI, -⟩ := S.rep i hi
      exact ⟨cvT, cvR, mI, rP, rules, hI⟩
    typed := S.typed, pinsTyped := S.pinsTyped, inj := S.inj, pinU := S.pinU, pinNP := S.pinNP, pinNIdx := S.pinNIdx
    pinPps := S.pinPps, pinDsLen := S.pinDsLen, w := S.w, idx := I.idx
    same := fun i hi ψ => ⟨S.ψJEq i 0 hi S.kpos ψ, S.sameDs i hi ψ⟩
    lvls := fun i hi => (S.same i hi).1
    sameE := fun i hi => (S.same i hi).2
    stored := fun i hi => by
      obtain ⟨cvT, caps, cvR, mI, rP, rules, hf, -, hψ⟩ := S.stored i hi
      exact ⟨cvT, caps, hf, hψ⟩
    ctorCount := S.ctorCount, ctorsOf := S.ctorsOf, DsFit := S.DsFit, shape := I.shape
    entry := I.entry, inst := I.inst, ordTgt := I.ordTgt, ordTgtMem := I.ordTgtMem }

local notation "ENV₁" => (ConLeche.consMutualFormers (fms.take p.k) env)

/-- **The pins' syntactic facts at the prefix model** (PROVED this
session): `NestedPinFacts` with its `groups` field at `NestedPinGroupSyn`
— the records, the components' readings, and every pin in a group whose
syntactic half holds. -/
structure NestedPinSynFacts (st : ElimState) (mp₁ : EnvModelM V μ ENV₁) : Prop where
  pinsLen : pinsS.length = st.pins.length
  pinRec : ∀ (q : Nat) (pin : NestedPin), st.pins[q]? = some pin →
    (pinsS.getD q default).J = pin.container ∧
    pin.pin = Expr.mkAppN (.const pin.container (pinsS.getD q default).lvls) (pinsS.getD q default).DsE
  pinDs : ∀ q, q < pinsS.length → ∀ ψ : Name → Nat,
    DenoteMetaSpine mp₁.base2.acval ENV₁ ψ b.nP (pinsS.getD q default).DsE
      ((pinsS.getD q default).Ds ψ)
  /-- **the pins' components are GRADED at the block's parameter frame**
  (task #315 M7-2): the tail carries `nestedPinsOk` only at `envAux`
  and at `envOut`, while the pin's own type-check — `nestedPinsOk`'s
  `inferType` at the block's PARAMETER context, which is the guard a
  grading needs — is packaged at `NestedPinsRun.pinRead`; this clause
  is the bridge, and the nested rule's pin conjunct spends it at the
  recursor's padded frame. -/
  pinWd : ∀ q, q < pinsS.length → ∀ (ψ : Name → Nat) (ρ : Nat → V),
    Sat V ((((ppsF 0 ψ).take b.nP).map (·.2.2)).reverse) ρ →
    ∀ A ∈ (pinsS.getD q default).Ds ψ, WellDenotedV V ρ A
  groups : ∀ (dsR' : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (xFvsR' : Nat → Nat → List Expr) (q : Nat), q < pinsS.length →
    ∃ (q₀ kJ i : Nat) (dJ : BlockModel V), q = q₀ + i ∧ i < kJ ∧
      NestedPinGroupSyn (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
        (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF)
        (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
        (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR') (xFvsR := xFvsR') (pinsS := pinsS)
        st mp₁.base2 q₀ kJ dJ
  /-- **the same groups with their container's block model NAMED**
  (task #315 M7-2, DESIGN §U.36 (d)): at the container record the pin's
  own name reads, the group's model is `blockOf mp.base2 ci` — the value
  `groupSyn` constructs anyway.  `NestedTailOut.groups` is its consumer:
  the route's lift to `EnvModelB` needs the assignment `B`, not merely
  the existence of a model. -/
  groupsAt : ∀ (dsR' : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (xFvsR' : Nat → Nat → List Expr) (q : Nat), q < pinsS.length →
    ∀ ci : ConLeche.ContainerInfo,
      ConLeche.containerInfo? env (pinsS.getD q default).J = some ci →
      ∃ q₀ kJ i : Nat, q = q₀ + i ∧ i < kJ ∧
        NestedPinGroupSyn (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
          (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF)
          (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
          (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR') (xFvsR := xFvsR') (pinsS := pinsS)
          st mp₁.base2 q₀ kJ (blockOf mp.base2 ci)
  /-- **the copy's index count is the pin's** (task #315 R3, at the
  `ordF`-right arm's PIN target): `NestedPinFacts` carries this fact
  already, but the copies' SHAPE is stated at this record, and the
  index fit at a pin target needs the aux former's arity to be the
  pin's.  It is `NestedPinsRun.pinNIdx` read through `pinsOf_getD`, so
  the record's only producer proves it with nothing new. -/
  pinNIdx : ∀ q, q < pinsS.length →
    (fms.getD (p.k + q) default).nIdx = (pinsS.getD q default).nIdx

/-- **The pins' SEMANTIC data, PER PIN** (task #315 L-E, at lane L-B's
request, DESIGN §U.113): at every pin `q` — at the pin, not at a group
index — its level assignment is the substitution of its recorded level
arguments for its CONTAINER's own level parameters, its container's
block model carries the block's sort at that assignment, and its index
universe and parameter telescope are that model's at the GROUP-RELATIVE
index `i = q - grpBase`.

**Derived, not recorded, and that is the point.**  All of it comes off
`groups`, a field this record already has, through
`NestedPinGroupSyn`'s `stored` (the container's constant and the level
law), `w` (the sort), `pinU`, `pinPps` and `pinNP` (the index data),
with `grp` identifying the group's base with the pin table's own
`grpBase`.  So no new clause is added and NOTHING is imposed on any
producer: the fact holds at EVERY producer of `NestedPinSynFacts` by
construction, which is what the request's own check asked to be
confirmed — and confirming it this way is stronger than enumerating
producers, since a later producer cannot fail it either. -/
theorem NestedPinSynFacts.pinSem {st : ElimState} {mpP : EnvModelM V μ ENV₁}
    (SF : NestedPinSynFacts (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
      (kinds := kinds) (env := env) (mp := mp) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF)
      (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
      (tssF := tssF) (ctorsR := ctorsR) (pinsS := pinsS) st mpP)
    (dsR' : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (xFvsR' : Nat → Nat → List Expr) (q : Nat) (hq : q < pinsS.length) :
    ∃ (q₀ kJ i : Nat) (dJ : BlockModel V) (cvT : ConstantVal) (caps : IndCaps),
      q = q₀ + i ∧ i < kJ ∧ (st.pins.getD q default).grpBase = q₀ ∧
      (ENV₁).find? ((D).pinAt q).J = some (ConstantInfo.indInfo cvT caps) ∧
      (∀ ψ : Name → Nat, ((D).pinAt q).ψJ ψ
        = Level.substFn ψ cvT.levelParams ((D).pinAt q).lvls) ∧
      (∀ ψ : Name → Nat, dJ.w (((D).pinAt q).ψJ ψ) = f₀.s.eval ψ) ∧
      (∀ ψ : Name → Nat, ((D).pinAt q).u ψ = dJ.uM i (((D).pinAt q).ψJ ψ)) ∧
      ((D).pinAt q).pps = dJ.ppsM i ∧ ((D).pinAt q).nPJ = dJ.nP := by
  obtain ⟨q₀, kJ, i, dJ, rfl, hi, S⟩ := SF.groups dsR' xFvsR' q hq
  obtain ⟨cvT, caps, -, -, -, -, hfind, -, hψJ⟩ := S.stored i hi
  exact ⟨q₀, kJ, i, dJ, cvT, caps, rfl, hi, (S.grp i hi).1, hfind, hψJ,
    fun ψ => S.w i hi ψ, fun ψ => S.pinU i hi ψ i hi, S.pinPps i hi, S.pinNP i hi⟩

end Assembly

/-! ## The construction: one `PinSyn` per pin, from the records

The `PinSyn` of pin `q` is a TOTAL function of the elimination's state,
the pre-block environment and the containers' block models: the pin's
record gives the container and (K.28's source) the level arguments and
the components; the mint group's BASE pin (K.29) gives the container
group `ci₀` whose block model `blockOf` serves every pin of the group
at member `q - grpBase`; the components' readings are their readings at
the prefix model.  The facts the run certifies about these readers are
`PinData`.
-/

section Construction

/-- The elimination's `q`-th pin (total). -/
def pinAtE (st : ElimState) (q : Nat) : NestedPin := st.pins.getD q default

/-- The reader, spelled out: the group records (`NestedPinGroupSyn.grp`)
name the pin by the list, the arms of the copies' identities by the
reader (task #315 L-B — the definition is private to this module, so
the identity travels as a lemma). -/
theorem pinAtE_eq (st : ElimState) (q : Nat) : pinAtE st q = st.pins.getD q default := by rfl

/-- The copy minted for pin `q` (total). -/
def copyAtE (st : ElimState) (p : NestedParts) (q : Nat) : ConLeche.AuxType :=
  st.types.getD (p.k + q) default

/-- The copy's source record — its container, level arguments and
components (total). -/
def srcAtE (st : ElimState) (p : NestedParts) (q : Nat) : Name × List Level × List Expr :=
  (copyAtE st p q).src.getD (.anonymous, [], [])

/-- The group of pin `q`'s BASE pin, as `containerInfo?` reads it (total). -/
def baseInfo (env : Env) (st : ElimState) (q : Nat) : ContainerInfo :=
  (ConLeche.containerInfo? env (pinAtE st (pinAtE st q).grpBase).container).getD default

/-- The `i`-th member of pin `q`'s group (total). -/
def memberOf (env : Env) (st : ElimState) (q i : Nat) : ContainerMember :=
  (baseInfo env st q).members.getD i default

/-- **The `PinSyn` of pin `q`**: the pin's container, K.28's level
arguments and components, the container's level assignment as the
substitution at the group member's level parameters, the group block
model's arities at member `q - grpBase`, the components' readings at
the prefix carrier `acval` and environment `env₁`, and — the pin's own
index universe — THE CONTAINER's, the group block model's `uM` at that
member and that level assignment (§U.22; the block's `W` is the
members' universe, not a copy's). -/
noncomputable def pinOf (m : EnvModel V env) (st : ElimState) (p : NestedParts)
    (acval : Name → (Name → Nat) → AnnotTerm) (env₁ : Env) (nP : Nat) (q : Nat) : PinSyn :=
  { J := (pinAtE st q).container
    lvls := (srcAtE st p q).2.1
    ψJ := fun ψ => Level.substFn ψ (memberOf env st q (q - (pinAtE st q).grpBase)).lps (srcAtE st p q).2.1
    nPJ := (blockOf m (baseInfo env st q)).nP
    DsE := (srcAtE st p q).2.2
    Ds := fun ψ => (srcAtE st p q).2.2.map fun e => (denoteMeta acval env₁ ψ nP e).getD default
    nIdx := (blockOf m (baseInfo env st q)).nIdxAt (q - (pinAtE st q).grpBase)
    u := fun ψ => (blockOf m (baseInfo env st q)).uM (q - (pinAtE st q).grpBase)
      (Level.substFn ψ (memberOf env st q (q - (pinAtE st q).grpBase)).lps (srcAtE st p q).2.1)
    pps := (blockOf m (baseInfo env st q)).ppsM (q - (pinAtE st q).grpBase) }

/-- **The facts the run certifies about pin `q`'s readers**: K.28 (the
source, the copy as `mkCopy`'s output at it), K.29 (the segment, the
group's size and components' count, every group pin's container and
record at the BASE pin's group) and K.14 (the base pin's group has the
pin's own group's parameter count and member names). -/
structure PinData (env : Env) (st : ElimState) (p : NestedParts) (pbs : List (Expr × ConLeche.BinderMeta))
    (q : Nat) : Prop where
  lt : q < st.pins.length
  pin : st.pins[q]? = some (pinAtE st q)
  ty : st.types[p.k + q]? = some (copyAtE st p q)
  src : (copyAtE st p q).src
    = some ((pinAtE st q).container, (srcAtE st p q).2.1, (srcAtE st p q).2.2)
  pinEq : (pinAtE st q).pin
    = Expr.mkAppN (.const (pinAtE st q).container (srcAtE st p q).2.1) (srcAtE st p q).2.2
  /-- K.28 at the pin, and K.14 tying the pin's own group to the base's -/
  own : ∃ ci : ContainerInfo, ConLeche.containerInfo? env (pinAtE st q).container = some ci ∧
    (srcAtE st p q).2.2.length = ci.nP ∧ (pinAtE st q).grpSize = ci.members.length ∧
    ci.nP = (baseInfo env st q).nP ∧
    ci.members.map (·.name) = (baseInfo env st q).members.map (·.name) ∧
    ∃ J : ContainerMember, ci.members.find? (fun J => J.name == (pinAtE st q).container) = some J ∧
      J.name = (pinAtE st q).container ∧
      ∃ c : ConLeche.AuxType,
        ConLeche.mkCopy pbs (srcAtE st p q).2.1 (srcAtE st p q).2.2 (copyAtE st p q).name J = .ok c ∧
        c.type = (copyAtE st p q).type ∧
        c.ctors.map (fun x => (x.1, x.2.2)) = (copyAtE st p q).ctors.map (fun x => (x.1, x.2.2))
  seg : (pinAtE st q).grpBase ≤ q ∧ q < (pinAtE st q).grpBase + (pinAtE st q).grpSize ∧
    (pinAtE st q).grpBase + (pinAtE st q).grpSize ≤ st.pins.length
  base : ConLeche.containerInfo? env (pinAtE st (pinAtE st q).grpBase).container
    = some (baseInfo env st q)
  baseLen : (baseInfo env st q).members.length = (pinAtE st q).grpSize
  /-- every pin of the group, at the base's group -/
  grp : ∀ i, i < (pinAtE st q).grpSize →
    (pinAtE st ((pinAtE st q).grpBase + i)).container = (memberOf env st q i).name ∧
    (pinAtE st ((pinAtE st q).grpBase + i)).grpBase = (pinAtE st q).grpBase ∧
    (pinAtE st ((pinAtE st q).grpBase + i)).grpSize = (pinAtE st q).grpSize ∧
    (copyAtE st p ((pinAtE st q).grpBase + i)).src
      = some ((memberOf env st q i).name, (srcAtE st p q).2.1, (srcAtE st p q).2.2) ∧
    (baseInfo env st q).members[i]? = some (memberOf env st q i)

/-- A list position reads its `getD`. -/
private theorem getD_of_getElem? {α : Type} [Inhabited α] {l : List α} {i : Nat} {a : α}
    (h : l[i]? = some a) : l.getD i default = a := by
  rw [List.getD_eq_getElem?_getD, h]; rfl

/-- **`PinData` at every pin, from the three Bools.** -/
theorem pinData_of {env : Env} {st : ElimState} {p : NestedParts}
    {pbs : List (Expr × ConLeche.BinderMeta)}
    (hK28 : ∀ (q : Nat) (qn : NestedPin), st.pins[q]? = some qn →
      ∃ (t : ConLeche.AuxType) (Jn : Name) (lvls : List Level) (Ds : List Expr)
        (ci : ContainerInfo) (J : ContainerMember) (c : ConLeche.AuxType),
        st.types[p.k + q]? = some t ∧ t.src = some (Jn, lvls, Ds) ∧ Jn = qn.container ∧
        qn.pin = Expr.mkAppN (.const Jn lvls) Ds ∧ ConLeche.containerInfo? env Jn = some ci ∧
        ci.members.find? (fun J => J.name == Jn) = some J ∧ J.name = Jn ∧
        ConLeche.mkCopy pbs lvls Ds t.name J = .ok c ∧ c.name = t.name ∧ c.type = t.type ∧
        c.ctors.map (fun x => (x.1, x.2.2)) = t.ctors.map (fun x => (x.1, x.2.2)))
    (hgrp : ConLeche.nestedGroupsOk env p st = true)
    (hcont : ConLeche.nestedContainersOk env st.pins = true) :
    ∀ q, q < st.pins.length → PinData env st p pbs q := by
  intro q hq
  have hpin : st.pins[q]? = some (pinAtE st q) := by
    unfold pinAtE
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]; rfl
  -- K.29 at the pin
  obtain ⟨t, ci, Jn, lvls, Ds, hty, hci, hsrc, hb1, hb2, hb3, hsz, hDl, hall⟩ :=
    ConLeche.nestedGroupsOk_inv hgrp q _ hpin
  -- K.28 at the pin
  obtain ⟨t', Jn', lvls', Ds', ci', J, c, hty', hsrc', hJnq, hpinEq, hci', hJ, hJn, hmk, -, hct, hcc⟩ :=
    hK28 q _ hpin
  obtain rfl : t = t' := Option.some.inj (hty.symm.trans hty')
  have hsrcEq := Option.some.inj (hsrc.symm.trans hsrc')
  obtain ⟨rfl, rfl, rfl⟩ : Jn = Jn' ∧ lvls = lvls' ∧ Ds = Ds' :=
    ⟨congrArg Prod.fst hsrcEq, congrArg (fun x => x.2.1) hsrcEq, congrArg (fun x => x.2.2) hsrcEq⟩
  subst hJnq
  have hcieq : ci' = ci := Option.some.inj (hci'.symm.trans hci)
  rw [hcieq] at hJ
  have hcopy : copyAtE st p q = t := getD_of_getElem? hty
  have hsrcE : srcAtE st p q = ((pinAtE st q).container, lvls, Ds) := by
    unfold srcAtE; rw [hcopy, hsrc]; rfl
  -- the base pin, its group (K.14 at the pin's own group)
  obtain ⟨-, hgroups⟩ := ConLeche.nestedContainersOk_group hcont
  obtain ⟨ciq, hciq, hmem⟩ := hgroups _ (List.mem_of_getElem? hpin)
  obtain rfl : ci = ciq := Option.some.inj (hci.symm.trans hciq)
  have hkpos : 0 < (pinAtE st q).grpSize := by omega
  obtain ⟨q0, J0, t0, hq0, hJ0, -, hq0c, hq0b, hq0s, -⟩ := hall 0 hkpos
  rw [Nat.add_zero] at hq0
  obtain ⟨ci₀, hci₀, hnP₀, hnames₀⟩ := hmem J0 (List.mem_of_getElem? hJ0)
  have hbaseE : pinAtE st (pinAtE st q).grpBase = q0 := getD_of_getElem? hq0
  have hbase : ConLeche.containerInfo? env (pinAtE st (pinAtE st q).grpBase).container
      = some (baseInfo env st q) := by
    unfold baseInfo
    rw [hbaseE, hq0c, hci₀]; rfl
  have hbaseI : baseInfo env st q = ci₀ := by
    unfold baseInfo; rw [hbaseE, hq0c, hci₀]; rfl
  have hlen₀ : ci₀.members.length = ci.members.length := by
    have := congrArg List.length hnames₀
    simpa using this
  refine ⟨hq, hpin, by rw [hcopy]; exact hty, by rw [hcopy, hsrcE]; exact hsrc,
    by rw [hsrcE]; exact hpinEq, ⟨ci, hci, by rw [hsrcE]; exact hDl, hsz, by rw [hbaseI]; exact hnP₀.symm,
      by rw [hbaseI]; exact hnames₀.symm, J, hJ, hJn, c, by rw [hsrcE, hcopy]; exact hmk,
      by rw [hcopy]; exact hct, by rw [hcopy]; exact hcc⟩,
    ⟨hb1, hb2, hb3⟩, hbase, by rw [hbaseI, hlen₀]; exact hsz.symm, ?_⟩
  intro i hi
  obtain ⟨qi, Ji, ti, hqi, hJi, hti, hqic, hqib, hqis, htis⟩ := hall i hi
  have hqiE : pinAtE st ((pinAtE st q).grpBase + i) = qi := getD_of_getElem? hqi
  -- the base's `i`-th member carries the same name
  obtain ⟨Mi, hMi, hMiname⟩ : ∃ Mi : ContainerMember, ci₀.members[i]? = some Mi ∧ Mi.name = Ji.name := by
    have h1 : (ci.members.map (·.name))[i]? = some Ji.name := by
      rw [List.getElem?_map, hJi]; rfl
    rw [← hnames₀, List.getElem?_map] at h1
    obtain ⟨Mi, hMi, hMn⟩ := Option.map_eq_some_iff.mp h1
    exact ⟨Mi, hMi, hMn⟩
  have hmemE : memberOf env st q i = Mi := by
    unfold memberOf; rw [hbaseI]; exact getD_of_getElem? hMi
  have hcopyi : copyAtE st p ((pinAtE st q).grpBase + i) = ti := by
    unfold copyAtE
    rw [← Nat.add_assoc]
    exact getD_of_getElem? hti
  refine ⟨by rw [hqiE, hqic, hmemE, hMiname], by rw [hqiE, hqib], by rw [hqiE, hqis], ?_,
    by rw [hbaseI, hmemE]; exact hMi⟩
  rw [hcopyi, htis, hmemE, hMiname, hsrcE]

end Construction

/-! ## The run's conjuncts, bundled -/

/-- **The nested run's conjuncts through the restore, bundled** — the
hypotheses of `NestedPinsStaged` (`NestedLoop.lean`), verbatim, as one
record, so that the named facts below can quantify over them once. -/
structure NestedPinsRun (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat) {env : Env}
    (mp : EnvModelM V μ env) (p : NestedParts) (st : ElimState) (b : MutualBlock) (envAux : Env)
    (stored : List AuxStored) (ctorsR : List (List (ConstantVal × Nat × Nat)))
    (fmsA ctorsA₀ : List ConstantVal)
    (fms : List MutualFormerA) (f₀ : MutualFormerA) (ctorsA : List (ConstantVal × Nat))
    (sortss : List (List Level)) (kinds : List (List (RecFieldKind × Nat)))
    (mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env))
    (ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (W : (Name → Nat) → Nat)
    (idxF : Nat → List Expr) (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
    (fvsPF xFvsF : Nat → List Expr) (xrestF : Nat → Expr)
    (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)))
    (mp₁' : EnvModelM V μ (ConLeche.consMutualFormers (fms.take p.k) env)) : Prop where
  hμ : μ.verifiedChecks = true
  hE : ConLeche.EtaFamiliesClosed env
  hPM : PinsModeled mp.base2 st.pins
  h0 : (p.formers.all (fun f => !f.1.type.mentionsNestedAux) &&
      (p.ctors.map (fun c => c.cv.type)).all (fun t => !t.mentionsNestedAux)) = true
  h1 : uniformIndOccsOk p.memberNames (p.lps.map Level.param) p.nP
      (p.ctors.map (fun c => c.cv.type)) = true
  hfA : ConLeche.nestedAnnotFormers (m := ConLeche.CheckM) (fueledOps μ F) env p.nP p.formers
      = .ok fmsA
  hcA : ConLeche.nestedAnnotCtors (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.nestedFormerEnv fmsA env) p.ctors = .ok ctorsA₀
  helim : ConLeche.elimNested env p.nP p.lps (ConLeche.nestedTypes0 p fmsA ctorsA₀) = .ok st
  hcount : st.pins.length = p.numNested
  hfresh : ConLeche.copiesFresh env p.k st = true
  hcont : ConLeche.nestedContainersOk env st.pins = true
  hb : ConLeche.auxBlock p st = some b
  haux : ConLeche.checkMutualCore (m := ConLeche.CheckM) (fueledOps μ F) env b none true
      = .ok envAux
  hstored : ConLeche.auxStoredAll envAux b b.k = some stored
  hclosed : ConLeche.pinsClosed p.nP st.pins = true
  hpinsAux : ConLeche.nestedPinsOk (m := ConLeche.CheckM) (fueledOps μ F) envAux p.nP st.pins
      = .ok ()
  hcaps : (stored.take p.k).all (fun a => !a.caps.eta && (env.find? a.cvTa.name).isNone) = true
  hsrc : ConLeche.nestedCopySrcOk env p st = true
  hgrp : ConLeche.nestedGroupsOk env p st = true
  hscoped : ConLeche.pinsScoped p.nP st = true
  /-- **THE COPIES' TARGETS** (K.32, task #315 L-E, DESIGN §U.64): a
  copy's group-internal recursive field points at the copy of the
  container member its own field points at — what the copies'
  identities read on the `ordF` arm -/
  hK32 : ConLeche.nestedCopyTargetsOk env p b st stored = true
  hkinds : ConLeche.nestedPinKindsOk p b st stored = true
  /-- **THE PINS' CONTAINER INSTANCES AND RANK** (K.37, task #315 L-E,
  DESIGN §U.55): the model's induction measure for the global entry
  theorem's step (iii) — an OWN reference stays inside the instance, a
  reference that LEAVES it goes to a strictly smaller rank, the rank is
  a function of the instance, and a mint group is one instance -/
  hrank : ConLeche.nestedPinRankOk env p b st stored = true
  /-- **THE POSITIVITY NORMALISATION ON THE MINTED COPY** (K.42, task
  #315, lane L-B): at every field of every copy's constructor that the
  record's filter admits — ORDINARY, **or** with a target below `p.k`,
  i.e. at one of the block's own MEMBERS (the kernel lane's widening of
  2026-09-18) — the stored domain IS the positivity normalisation of
  the MINTED one; what the copies' identities read on the `ordF`-LEFT
  arm and, at a member target, on the `ordF`-RIGHT one, with the
  rewrite's own leg (which needs `pinLeaf`, and is circular) gone -/
  hK42 : ∃ (jobs : List (Nat × Expr × Expr)) (ws : List Expr),
      ConLeche.nestedOrdDomPairs env p st stored (ConLeche.nestedPinKinds p b stored) = some jobs ∧
      ConLeche.nestedOrdNorms (m := ConLeche.CheckM) (fueledOps μ F)
          (ConLeche.consNestedFormers (stored.take p.k) env) b.memberNames jobs = .ok ws ∧
      ws = jobs.map (·.2.2)
  /-- **THE SAME WALK AT A PIN TARGET, REWRITTEN** (K.51, task #315,
  lane L-B): the pin-target twin of `hK42` — the stored domain is the
  REWRITTEN normalisation of the minted one, which is what lets the
  `ordF`-RIGHT arm read a pin target off the minted domain -/
  hK51 : ∃ (params : List Expr) (pbs₀ : List (Expr × BinderMeta))
      (jobsP : List (Nat × Expr × Expr)) (wsP : List Expr),
      ConLeche.nestedRewriteData p st = some (params, pbs₀) ∧
      ConLeche.nestedPinDomPairs env p st stored
          (ConLeche.nestedPinKinds p b stored) = some jobsP ∧
      ConLeche.nestedPinNorms (m := ConLeche.CheckM) (fueledOps μ F)
          (ConLeche.consNestedFormers (stored.take p.k) env) b.memberNames jobsP = .ok wsP ∧
      ConLeche.nestedPinRewrites env p st params pbs₀ jobsP wsP = true
  /-- **A CONTAINER'S NESTED FIELD LANDS ON A BLOCK PIN** (K.60, task
  #315, lane PINF): K.32's twin the other way round — at a container
  field that is itself nested through a FURTHER stored container
  carrying one of the container's own members, the copy's corresponding
  field is classified `.recursive` into a PIN of the block.  What the
  copies' `pinF` arm reads for its conjunct 1 and for `copyPinFCorr`'s
  `hkA` -/
  hK60 : ConLeche.nestedCopyPinFieldsOk env p b st stored = true
  /-- **A CONTAINER'S REFLEXIVE NESTED FIELD LANDS ON A BLOCK PIN**
  (K.63, task #315, lane PINF): `hK60`'s guard one `Π`-tower down,
  where a reflexive field's stored domain is a `Π` and `hK60` therefore
  claims nothing.  The two are computed by ONE walk; the copies' `pinF`
  arm reads this one at a reflexive nested field -/
  hK63 : ConLeche.nestedCopyReflFieldsOk env p b st stored = true
  /-- **THE CONTAINER INSTANCE MAP** (K.61, task #315, lane WIDE): every
  own pin of a pin's container, instantiated at that pin's own level
  arguments and components, IS a pin of the block (totality), and a
  copy's field sitting at one of those own pins records the map's value
  as its target.  The wide identification's `σ` runs on this map; it may
  COLLAPSE and is not checked injective -/
  hK61 : ConLeche.nestedInstMapOk env p b st stored = true
  /-- **A REWRITTEN ORDINARY FIELD LEAVES THE INSTANCE** (K.62, task
  #315, lane WIDE): at an `ordF`-right edge — one whose container-side
  field mentions no member of the container's own group — the recorded
  target is OUTSIDE `hK61`'s image.  The wide identification's `houtσ`,
  which `nestedPinEdges_mem` may only exhibit where this record is in
  scope -/
  hK62 : ConLeche.nestedOrdOutsideOk env p b st stored = true
  /-- **and a rewritten ORDINARY field's target IS the owning
  container's own class, imaged** (task #315 K.67): K.62's positive
  twin at the same guard — where `hK62` says the target is not in the
  instance, this says which class of the OWNING container it is the
  image of.  The wide identification's PIN half reads it; the member
  half reads only `hK62`. -/
  hK67 : ConLeche.nestedOrdTargetOk μ env p b st stored = true
  /-- **and it is THIS block's own class, by its own recomputation**
  (task #315 K.68): K.67's SELF-RELATIVE twin — no owner, no parent,
  no instance map.  `hK67` is what the block's OWN side of the wide
  correspondence reads; this is what a LATER block reads of this one,
  carried onto the container's model through `PinShapes`. -/
  hK68 : ConLeche.nestedOrdSelfTargetOk env p b st stored = true
  /-- **AND ITS DOMAIN IS THE OWNER'S, ONE SUBSTITUTION APART** (task
  #315 K.69): K.67 and K.68 compare the two copies' TARGETS at a field
  the container calls ordinary; this compares their field DOMAINS —
  the block's copy's is the owner's, instantiated at the block pin's
  levels and components — under the guard that the OWNER's copy FIRED.
  That guard is what lets the positivity normalisation be pushed across
  the instantiation at all: a term already at a constant inductive head
  is its own normalisation (`normPosDomM_indApp`) and stays so under
  the substitution, while the mixed corner — the block's copy fires
  where the owner's did not — is REAL and is the model's entry arm. -/
  hK69 : ConLeche.nestedOrdNormOk μ env p b st stored = true
  hpinsE : ConLeche.nestedPinsOk (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.consMutualFormers (fms.take p.k) env) p.nP st.pins = .ok ()
  /-- **THE PINS' CONSTANTS RESOLVE** (K.64, task #315, lane LE): at the
  prefix formers' environment, every constant a pin names is stored and
  every `.proj` node in it names a stored structure.  Nothing else in
  the run carries it — `nestedPinsOk` runs `hasFvar`,
  `looseBVarsBounded` and `inferType` and not `projTablesOk`, and a
  reading ignores an `.fvar`'s annotation and settles a `.proj` node
  with a table or the pair fallback — and the clause carrying a
  container's pins' components' READINGS needs it to cross a later
  install's projection table -/
  hK64 : ConLeche.pinsResolve (ConLeche.consMutualFormers (fms.take p.k) env) st.pins = true
  hformers : ConLeche.mutualFormers (m := ConLeche.CheckM) (fueledOps μ F) b.nP b.formers env true
      = .ok (ConLeche.consMutualFormers fms env, fms)
  h : MutualFormersFacts V F true mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
      fvsPF xFvsF xrestF eissF tssF
  hbk : b.k = p.k + st.pins.length
  h3 : ConLeche.mutualCtorsGrouped b.ctors = true
  hnd : b.blockNames.Nodup
  hctorsA : ConLeche.checkMutualCtors (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.consMutualFormers fms env) b fms (Level.isEquiv f₀.s .zero == some true) true b.ctors
      = .ok (ctorsA, sortss)
  hleafM' : ∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f →
      mp₁'.base2.acval f.cvTa.name = mutMemberLeaf b fms f₀ ctorsA kinds ppsF W dsF esF eissF tssF t
  hoff' : ∀ n : Name, (∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f → n ≠ f.cvTa.name) →
      mp₁'.base2.acval n = mp.base2.acval n
  hfind' : ∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f →
      (ConLeche.consMutualFormers (fms.take p.k) env).find? f.cvTa.name = some (.indInfo f.cvTa {}) ∧
      FormerData mp₁'.base2 f.cvTa (b.nP + f.nIdx) f₀.s (ppsF t)
  hctors : (stored.take p.k).mapM (fun a =>
        ConLeche.restoreCtors (m := ConLeche.CheckM) (fueledOps μ F)
          (ConLeche.consMutualFormers (fms.take p.k) env) (ConLeche.restoreTbl p st) p.lps
          a.ctors)
      = .ok ctorsR

/-! ## The named facts -/

/-- The named identity facts' common shape: at the run and at any
`PinSyn` list whose syntactic facts hold, every group whose syntactic
half holds has the identity `P`. -/
@[expose] def NestedPinsIdsAt (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat)
    (P : ∀ {env : Env}, EnvModelM V μ env → ∀ (p : NestedParts), ElimState → MutualBlock →
      ∀ (fms : List MutualFormerA), MutualFormerA → List (ConstantVal × Nat) →
      List (List (RecFieldKind × Nat)) → (Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) →
      ((Name → Nat) → Nat) → (Nat → List Expr) →
      (Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) → (Nat → (Name → Nat) → List AnnotTerm) →
      (Nat → List (Option Nat)) → (Nat → List Expr) → (Nat → Expr) →
      (Nat → (Name → Nat) → List (List AnnotTerm)) →
      (Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))) →
      List (List (ConstantVal × Nat × Nat)) →
      (Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) → (Nat → Nat → List Expr) →
      List PinSyn → EnvModelM V μ (ConLeche.consMutualFormers (fms.take p.k) env) →
      Nat → Nat → BlockModel V → Prop) : Prop :=
  ∀ {env : Env} (mp : EnvModelM V μ env) (p : NestedParts) (st : ElimState) (b : MutualBlock)
    (envAux : Env) (stored : List AuxStored) (ctorsR : List (List (ConstantVal × Nat × Nat)))
    (fmsA ctorsA₀ : List ConstantVal)
    (fms : List MutualFormerA) (f₀ : MutualFormerA) (ctorsA : List (ConstantVal × Nat))
    (sortss : List (List Level)) (kinds : List (List (RecFieldKind × Nat)))
    (mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env))
    (ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (W : (Name → Nat) → Nat)
    (idxF : Nat → List Expr) (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
    (fvsPF xFvsF : Nat → List Expr) (xrestF : Nat → Expr)
    (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)))
    (mp₁' : EnvModelM V μ (ConLeche.consMutualFormers (fms.take p.k) env)),
    NestedPinsRun V μ F mp p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁
      ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁' →
    ∀ pinsS : List PinSyn,
      NestedPinSynFacts (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
        (kinds := kinds) (env := env) (mp := mp) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF)
        (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
        (tssF := tssF) (ctorsR := ctorsR) (pinsS := pinsS) st mp₁' →
      ∀ (dsR : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
        (xFvsR : Nat → Nat → List Expr) (q₀ kJ : Nat) (dJ : BlockModel V),
        NestedPinGroupSyn (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
          (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF)
          (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
          (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS)
          st mp₁'.base2 q₀ kJ dJ →
        P mp p st b fms f₀ ctorsA kinds ppsF W idxF dsF esF srcsF fvsPF xrestF eissF tssF ctorsR
          dsR xFvsR pinsS mp₁' q₀ kJ dJ


/-- **The copy-instantiation identities** (NAMED, the identities;
consumer `nestedPinsStaged_of`): `NestedPinGroup.idx`, `.shape` and
`.entry` — K.28's pre-image computed through `replaceAllNested`'s
action (the shape, lane L-B) and the entries at the auxiliary carrier
(the whole block's theorem, lane L-E). -/
@[expose] def NestedPinsIdent (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat) : Prop :=
  NestedPinsIdsAt V μ F fun {env} _ p _ b fms f₀ ctorsA kinds ppsF W idxF dsF esF srcsF fvsPF
      xrestF eissF tssF ctorsR dsR xFvsR pinsS mp₁' q₀ kJ dJ =>
    (∀ i, i < kJ → ∀ (ψ : Name → Nat) (i' : Nat), i' < kJ →
      blockIds b.nP ppsF ψ (p.k + q₀ + i')
        = instTele ((pinsS.getD (q₀ + i) default).Ds ψ) 0
            (dJ.IdsM i' ((pinsS.getD (q₀ + i) default).ψJ ψ))) ∧
    (∀ i, i < kJ → ∀ (cvT : ConstantVal) (caps : IndCaps),
      (ConLeche.consMutualFormers (fms.take p.k) env).find? (pinsS.getD (q₀ + i) default).J
        = some (.indInfo cvT caps) →
      ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (((ppsF 0 ψ).take b.nP).map (·.2.2)).reverse ρp →
      ∀ i', i' < kJ → ∀ j, j < (dJ.ctorsM i').length →
      CopyShapeA (V := V) (nP := b.nP) (k := p.k) (resSort := f₀.s) (ppsA := ppsF) (W := W)
        (pins := pinsS) (offs := b.ownOffset) (memberNames := (fms.take p.k).map (·.cvTa.name))
        (tgtsG := mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA))
        (rss := blkRss ctorsA kinds) (tlss := fun ψ => mutTlss ctorsA.length tssF ψ)
        (Eiss₀ := fun ψ => mutEiss0 ctorsA.length eissF ψ)
        (Fss₀ := fun ψ => blkFss0 b ctorsA kinds dsF ψ)
        (Ess₀ := fun ψ => mutEss0 ctorsA.length esF ψ) (ψ := ψ) (ρp := ρp)
        mp₁'.base2.acval dJ ((pinsS.getD (q₀ + i) default).ψJ ψ) ((pinsS.getD (q₀ + i) default).Ds ψ)
        (pinsS.getD (q₀ + i) default).DsE
        cvT.levelParams (pinsS.getD (q₀ + i) default).lvls q₀ kJ i' j) ∧
    (∀ i, i < kJ → ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (((ppsF 0 ψ).take b.nP).map (·.2.2)).reverse ρp →
      ∀ i', i' < kJ → ∀ j, j < (dJ.ctorsM i').length →
      CopyEntryA (V := V) (nP := b.nP) (k := p.k) (resSort := f₀.s) (ppsA := ppsF) (W := W)
        (pins := pinsS) (offs := b.ownOffset) (mems := mutMems ctorsA.length (mutMemF b))
        (nFs := mutNFs ctorsA.length (mutNFOf ctorsA))
        (tgtsG := mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA))
        (rss := blkRss ctorsA kinds) (tlss := fun ψ => mutTlss ctorsA.length tssF ψ)
        (Eiss₀ := fun ψ => mutEiss0 ctorsA.length eissF ψ)
        (Fss₀ := fun ψ => blkFss0 b ctorsA kinds dsF ψ)
        (Ess₀ := fun ψ => mutEss0 ctorsA.length esF ψ) (ψ := ψ) (ρp := ρp)
        dJ ((pinsS.getD (q₀ + i) default).ψJ ψ) ((pinsS.getD (q₀ + i) default).Ds ψ) q₀ kJ i' j) ∧
    PinGroupInst (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
      (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF)
      (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
      (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS) q₀ kJ dJ ∧
    (∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (((ppsF 0 ψ).take b.nP).map (·.2.2)).reverse ρp →
      ∀ i', i' < kJ → ∀ j, j < (dJ.ctorsM i').length → ∀ l,
      l < ((dJ.Fss i' ((pinsS.getD q₀ default).ψJ ψ)).getD j []).length →
      ((dJ.rss i').getD j []).getD l false = false →
      ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l false = true →
      ¬ ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 < p.k →
      ∀ (cA : ConstantVal × Nat) (bs : List (Expr × ConLeche.BinderMeta)) (rr : Expr)
        (dom : Expr × ConLeche.BinderMeta) (lps lpsC : List Name),
      (dJ.ctorsM i')[j]? = some cA →
      cA.1.type.stripPis (dJ.nP + cA.2) = some (bs, rr) →
      bs[dJ.nP + l]? = some dom →
      ∀ i₀, i₀ < kJ → ∀ (ciC : ContainerInfo) (Jm : ContainerMember),
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i₀) default).J = some ciC →
      ciC.members[i']? = some Jm → Jm.lps = lpsC →
      ∀ (K : Name) (usK : List Level),
      (Expr.instantiateLevelParams lpsC (pinsS.getD (q₀ + i') default).lvls dom.1).getAppFn
          = .const K usK →
      ∃ z : Nat, z < pinsS.length ∧
        ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
          (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 = p.k + z ∧
        (((mutEiss0 ctorsA.length eissF ψ).getD
          (b.ownOffset (p.k + q₀ + i') + j) []).getD l []).length
          = (pinsS.getD z default).nIdx ∧
        OrdTargetRead (V := V) mp₁'.base2.acval
          (ConLeche.consMutualFormers (fms.take p.k) env) ψ ρp b.nP l
          ((pinsS.getD q₀ default).Ds ψ)
          ((dJ.Fss i' ((pinsS.getD q₀ default).ψJ ψ)).getD j [])
          (((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l [])
          (((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l [])
          (pinsS.getD z default).nPJ lpsC dJ.nP (q₀ + i')
          ((nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF
            xrestF eissF tssF ctorsR dsR xFvsR pinsS).ownPinTerms lps) dom.1) ∧
    (∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (((ppsF 0 ψ).take b.nP).map (·.2.2)).reverse ρp →
      ∀ i', i' < kJ → ∀ j, j < (dJ.ctorsM i').length → ∀ l,
      l < ((dJ.Fss i' ((pinsS.getD q₀ default).ψJ ψ)).getD j []).length →
      ((dJ.rss i').getD j []).getD l false = false →
      ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l false = true →
      ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 < p.k →
      ∀ (cA : ConstantVal × Nat) (bs : List (Expr × ConLeche.BinderMeta)) (rr : Expr)
        (dom : Expr × ConLeche.BinderMeta) (lps lpsC : List Name),
      (dJ.ctorsM i')[j]? = some cA →
      cA.1.type.stripPis (dJ.nP + cA.2) = some (bs, rr) →
      bs[dJ.nP + l]? = some dom →
      ∀ i₀, i₀ < kJ → ∀ (ciC : ContainerInfo) (Jm : ContainerMember),
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i₀) default).J = some ciC →
      ciC.members[i']? = some Jm → Jm.lps = lpsC →
      ∀ (K : Name) (usK : List Level),
      (Expr.instantiateLevelParams lpsC (pinsS.getD (q₀ + i') default).lvls dom.1).getAppFn
          = .const K usK →
      ∃ mm : Nat, mm < p.k ∧
        ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
          (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 = mm ∧
        (((mutEiss0 ctorsA.length eissF ψ).getD
          (b.ownOffset (p.k + q₀ + i') + j) []).getD l []).length
          = (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF
            xrestF eissF tssF ctorsR dsR xFvsR pinsS).nIdxAt mm ∧
        OrdTargetRead (V := V) mp₁'.base2.acval
          (ConLeche.consMutualFormers (fms.take p.k) env) ψ ρp b.nP l
          ((pinsS.getD q₀ default).Ds ψ)
          ((dJ.Fss i' ((pinsS.getD q₀ default).ψJ ψ)).getD j [])
          (((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l [])
          (((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l [])
          b.nP lpsC dJ.nP (q₀ + i')
          ((nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF
            xrestF eissF tssF ctorsR dsR xFvsR pinsS).ownPinTerms lps) dom.1)

/-! ## The group's pins, described uniformly -/

section GroupPins

variable {st : ElimState} {p : NestedParts} {pbs : List (Expr × ConLeche.BinderMeta)}

/-- **The `PinSyn` of the `i`-th pin of pin `q`'s group** — the record
`pinOf` builds at it, spelled at the BASE pin's data. -/
noncomputable def groupPin (m : EnvModel V env) (st : ElimState) (p : NestedParts)
    (acval : Name → (Name → Nat) → AnnotTerm) (env₁ : Env) (nP : Nat) (q i : Nat) : PinSyn :=
  { J := (memberOf env st q i).name
    lvls := (srcAtE st p q).2.1
    ψJ := fun ψ => Level.substFn ψ (memberOf env st q i).lps (srcAtE st p q).2.1
    nPJ := (blockOf m (baseInfo env st q)).nP
    DsE := (srcAtE st p q).2.2
    Ds := fun ψ => (srcAtE st p q).2.2.map fun e => (denoteMeta acval env₁ ψ nP e).getD default
    nIdx := (blockOf m (baseInfo env st q)).nIdxAt i
    u := fun ψ => (blockOf m (baseInfo env st q)).uM i
      (Level.substFn ψ (memberOf env st q i).lps (srcAtE st p q).2.1)
    pps := (blockOf m (baseInfo env st q)).ppsM i }

variable (PD : PinData env st p pbs q)
include PD

theorem PinData.srcAtE_group {i : Nat} (hi : i < (pinAtE st q).grpSize) :
    srcAtE st p ((pinAtE st q).grpBase + i)
      = ((memberOf env st q i).name, (srcAtE st p q).2.1, (srcAtE st p q).2.2) := by
  unfold srcAtE
  rw [(PD.grp i hi).2.2.2.1]
  rfl

theorem PinData.baseInfo_group {i : Nat} (hi : i < (pinAtE st q).grpSize) :
    baseInfo env st ((pinAtE st q).grpBase + i) = baseInfo env st q := by
  unfold baseInfo
  rw [(PD.grp i hi).2.1]

/-- **The group's members share their level parameters**: every member's
stored former has the container's own (`containerInfo?` tests
`cvC.levelParams == cvT.levelParams` at each), so the group's pins
share their level assignment `ψJ` — what the per-component index
universes are read at (DESIGN §U.22). -/
theorem PinData.lps_group {i i' : Nat} (hi : i < (pinAtE st q).grpSize)
    (hi' : i' < (pinAtE st q).grpSize) :
    (memberOf env st q i).lps = (memberOf env st q i').lps := by
  obtain ⟨cvT, -, -, -, rP, -, -, -, -, -, hM⟩ := ConLeche.containerInfo?_inv PD.base
  have hmem : ∀ n, n < (pinAtE st q).grpSize →
      memberOf env st q n ∈ (baseInfo env st q).members := by
    intro n hn
    have hlt : n < (baseInfo env st q).members.length := by rw [PD.baseLen]; exact hn
    show (baseInfo env st q).members.getD n default ∈ _
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    exact List.getElem_mem hlt
  obtain ⟨cvC, -, -, -, -, -, -, h1, -, h2, -, -⟩ := hM _ (hmem i hi)
  obtain ⟨cvC', -, -, -, -, -, -, h1', -, h2', -, -⟩ := hM _ (hmem i' hi')
  rw [h1, h2, h1', h2']

/-- The `i`-th pin of the group, at `pinOf`. -/
theorem PinData.pinOf_group (m : EnvModel V env) (acval : Name → (Name → Nat) → AnnotTerm) (env₁ : Env)
    (nP : Nat) {i : Nat} (hi : i < (pinAtE st q).grpSize) :
    pinOf m st p acval env₁ nP ((pinAtE st q).grpBase + i) = groupPin m st p acval env₁ nP q i := by
  have h1 := (PD.grp i hi).1
  have h2 := (PD.grp i hi).2.1
  have hs := PD.srcAtE_group hi
  have hb := PD.baseInfo_group hi
  have hidx : (pinAtE st q).grpBase + i - (pinAtE st ((pinAtE st q).grpBase + i)).grpBase = i := by
    rw [h2]; exact Nat.add_sub_cancel_left _ _
  have hm : memberOf env st ((pinAtE st q).grpBase + i) i = memberOf env st q i := by
    unfold memberOf; rw [hb]
  unfold pinOf groupPin
  rw [h1, hs, hb, hidx, hm]

/-- The `i`-th pin of the group: its own record, at the base's data. -/
theorem PinData.pinEq_group (PDi : PinData env st p pbs ((pinAtE st q).grpBase + i))
    (hi : i < (pinAtE st q).grpSize) :
    (pinAtE st ((pinAtE st q).grpBase + i)).pin
      = Expr.mkAppN (.const (memberOf env st q i).name (srcAtE st p q).2.1) (srcAtE st p q).2.2 := by
  rw [PDi.pinEq, (PD.grp i hi).1, PD.srcAtE_group hi]

end GroupPins

/-- **The pins' `PinSyn` list**: one `pinOf` per pin of the elimination. -/
noncomputable def pinsOf (m : EnvModel V env) (st : ElimState) (p : NestedParts)
    (acval : Name → (Name → Nat) → AnnotTerm) (env₁ : Env) (nP : Nat) : List PinSyn :=
  (List.range st.pins.length).map (pinOf m st p acval env₁ nP)

theorem pinsOf_length (m : EnvModel V env) (st : ElimState) (p : NestedParts)
    (acval : Name → (Name → Nat) → AnnotTerm) (env₁ : Env) (nP : Nat) :
    (pinsOf m st p acval env₁ nP).length = st.pins.length := by
  simp [pinsOf]

theorem pinsOf_getD (m : EnvModel V env) (st : ElimState) (p : NestedParts)
    (acval : Name → (Name → Nat) → AnnotTerm) (env₁ : Env) (nP : Nat)
    {q : Nat} (hq : q < st.pins.length) :
    (pinsOf m st p acval env₁ nP).getD q default = pinOf m st p acval env₁ nP q := by
  unfold pinsOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hq]
  rfl

/-! ## The discharge -/

section Discharge

variable {F : Nat} {mp : EnvModelM V μ env} {p : NestedParts} {st : ElimState} {b : MutualBlock}
  {envAux : Env} {stored : List AuxStored} {ctorsR : List (List (ConstantVal × Nat × Nat))}
  {fmsA ctorsA₀ : List ConstantVal}
  {fms : List MutualFormerA} {f₀ : MutualFormerA} {ctorsA : List (ConstantVal × Nat)}
  {sortss : List (List Level)} {kinds : List (List (RecFieldKind × Nat))}
  {mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env)}
  {ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {W : (Name → Nat) → Nat}
  {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
  {fvsPF xFvsF : Nat → List Expr} {xrestF : Nat → Expr}
  {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
  {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
  {mp₁' : EnvModelM V μ (ConLeche.consMutualFormers (fms.take p.k) env)}
  (R : NestedPinsRun V μ F mp p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁
    ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁')
include R

local notation "ENV₁" => (ConLeche.consMutualFormers (fms.take p.k) env)

/-- The pins' data, at the first former's parameter binders. -/
theorem NestedPinsRun.pinData : ∃ pbs : List (Expr × ConLeche.BinderMeta), pbs.length = p.nP ∧
    ∀ q, q < st.pins.length → PinData env st p pbs q := by
  obtain ⟨t₀, pbs, body, -, hstrip₀, hK28⟩ := ConLeche.nestedCopySrcOk_inv R.hsrc
  exact ⟨pbs, Expr.stripPis_length _ hstrip₀, pinData_of hK28 R.hgrp R.hcont⟩

/-- **A PIN'S COMPONENTS ARE NONEMPTY, so its container has a
parameter** (task #315 M7-4, DESIGN §U.45): `replaceIfNested` mints a
pin only where `nestedOccOk` finds a member of the growing list
mentioned among `args.take ci.nP`, and the elimination's provenance
record carries that verdict at every copy it appended
(`elimNested_copyCtors`).  At `ci.nP = 0` the tested list is empty, so
the verdict is `false` and no pin is minted.  This is what discharges
`ContainerModeled.inj`'s guard at the one place that reads the
clause. -/
theorem NestedPinsRun.pinDsPos {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    {q : Nat} (hq : q < st.pins.length) : 0 < (srcAtE st p q).2.2.length := by
  have hlen0 : (ConLeche.nestedTypes0 p fmsA ctorsA₀).length = p.k := by
    rw [ConLeche.nestedTypes0_length, ConLeche.nestedAnnotFormers_length R.hfA,
      ConLeche.NestedParts.k]
  obtain ⟨t₀, params, o, pbs₀, o', h1, h2, h3, hcopy⟩ := ConLeche.elimNested_copyCtors R.helim
  have hty : st.types[(ConLeche.nestedTypes0 p fmsA ctorsA₀).length + q]?
      = some (copyAtE st p q) := by
    rw [hlen0]; exact (hPD q hq).ty
  obtain ⟨-, -, -, J, lvls, Ds, -, -, -, hsrc, -, -, -, hany, -, -⟩ := hcopy q _ hty
  have hDs : Ds = (srcAtE st p q).2.2 :=
    (Prod.mk.inj (Prod.mk.inj (Option.some.inj (hsrc.symm.trans (hPD q hq).src))).2).2
  obtain ⟨a, ha, -⟩ := List.any_eq_true.mp hany
  rw [← hDs]
  exact List.length_pos_of_mem ha

/-- The crossing from the pre-block model to the prefix model. -/
theorem NestedPinsRun.cross :
    (∀ (n : Name) (c : ConstantInfo), (∀ cv mI rP rules, c ≠ .recInfo cv mI rP rules) →
      env.find? n = some c → (ENV₁).find? n = some c) ∧
    (∀ e : Expr, e.constsResolve env = true → e.constsResolve (ENV₁) = true) ∧
    (∀ n : Name, (env.find? n).isSome = true → mp₁'.base2.acval n = mp.base2.acval n) ∧
    (∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta mp.base2.acval env ψ dp e = some ea →
      denoteMeta mp₁'.base2.acval (ENV₁) ψ dp e = some ea) := by
  refine prefixCross_of mp₁' ?_ ?_ R.hoff'
  · intro f hf
    obtain ⟨t, ht⟩ := List.getElem?_of_mem (List.mem_of_mem_take hf)
    exact R.h.fresh t f ht
  · rw [List.map_take]
    refine List.Nodup.sublist (List.take_sublist _ _) ?_
    rw [R.h.names]
    have h0 := R.hnd
    unfold ConLeche.MutualBlock.blockNames at h0
    exact (List.nodup_append.mp (List.nodup_append.mp h0).1).1

/-- **A STORED CONTAINER'S GROUP IS READ THE SAME AT THE PREFIX
ENVIRONMENT** — `containerInfo?_consMutualFormers` at the run, whose
`hfresh` is the members' own (`MutualFormersFacts.fresh`) and whose
well-formedness is the pre-block model's.  `ContainerModeled.crossEnv`'s
`hci` on this lane: a pin's container's OWN pins are containers stored
before the block, so this is the shape the crossing asks for. -/
theorem NestedPinsRun.contsCross {J : Name} {ci : ContainerInfo}
    (h : ConLeche.containerInfo? env J = some ci) :
    ConLeche.containerInfo? (ENV₁) J = some ci := by
  obtain ⟨cv, caps, hf⟩ := containerInfo?_found h
  have hfr : ∀ f ∈ fms.take p.k, env.find? f.cvTa.name = none := by
    intro f hf'
    obtain ⟨t, ht⟩ := List.getElem?_of_mem (List.mem_of_mem_take hf')
    exact R.h.fresh t f ht
  rw [containerInfo?_consMutualFormers mp.base2.wf mp.base2.rec_ctors hfr (by rw [hf]; rfl)]
  exact h

/-- **A STORED CONTAINER'S OWN PINS ARE READ THE SAME AT THE PREFIX
ENVIRONMENT** — `ownPinsSyn_consMutualFormers` at the run, whose
freshness is the members' own (`MutualFormersFacts.fresh`) and whose
well-formedness is the pre-block model's.  `ContainerModeled.crossEnv`'s
`hownCross` on this lane. -/
theorem NestedPinsRun.ownCross {ci : ContainerInfo} {d : BlockModel V}
    (C : ContainerModeled mp.base2 ci d) (h : ContainerOwnPinsSyn (V := V) env d) :
    ContainerOwnPinsSyn (V := V) (ENV₁) d := by
  refine ownPinsSyn_consMutualFormers mp.base2.wf mp.base2.rec_ctors ?_ C h
  intro f hf'
  obtain ⟨t, ht⟩ := List.getElem?_of_mem (List.mem_of_mem_take hf')
  exact R.h.fresh t f ht

/-- The block has a member; the first former's type is closed and
bounded, and its data hold at the prefix model. -/
theorem NestedPinsRun.former0 :
    0 < p.k ∧ f₀.cvTa.type.hasFvar = false ∧ f₀.cvTa.type.looseBVarsBounded 0 = true ∧
    FormerData mp₁'.base2 f₀.cvTa (b.nP + f₀.nIdx) f₀.s (ppsF 0) := by
  have hk0 : 0 < p.k := by
    have hlenA : fmsA.length = p.k := ConLeche.nestedAnnotFormers_length R.hfA
    have he := R.helim
    unfold ConLeche.elimNested at he
    cases hh : (ConLeche.nestedTypes0 p fmsA ctorsA₀).head? with
    | none =>
      rw [hh] at he
      exact nomatch he
    | some t₀ =>
      have hlen := ConLeche.nestedTypes0_length p fmsA ctorsA₀
      rw [hlenA] at hlen
      cases hl : ConLeche.nestedTypes0 p fmsA ctorsA₀ with
      | nil => rw [hl] at hh; exact nomatch hh
      | cons x xs => rw [hl] at hlen; simp only [List.length_cons] at hlen; omega
  obtain ⟨hchecks, -⟩ := ConLeche.mutualFormers_inv R.hformers
  obtain ⟨cv', hd⟩ := ConLeche.mutualFormerChecksG_checked hchecks f₀ (List.mem_of_getElem? R.h.first)
  exact ⟨hk0, hd.noFvar, hd.bounded, (R.hfind' 0 f₀ hk0 R.h.first).2⟩

/-- **The auxiliary formers ARE the elimination's types** at the
auxiliary route: the checked former at `t` is the declared constant
(`⟨name, lps, type⟩` of the `t`-th type), and strips at its index
count to its sort. -/
theorem NestedPinsRun.formerType :
    ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f → ∀ ty : ConLeche.AuxType,
      st.types[t]? = some ty →
      f.cvTa = ⟨ty.name, p.lps, ty.type⟩ ∧
      ∃ bs : List (Expr × ConLeche.BinderMeta), ty.type.stripPis (b.nP + f.nIdx) = some (bs, .sort f.s) := by
  intro t f hft ty hty
  obtain ⟨hchecks, -⟩ := ConLeche.mutualFormers_inv R.hformers
  obtain ⟨cv, nIdx, hl, hnIdx, hcv⟩ := ConLeche.mutualFormerChecksTrue_at hchecks t f hft
  obtain ⟨hnP, hform⟩ := ConLeche.auxBlock_former R.hb
  obtain ⟨nIdx', hl', hcount⟩ := hform t ty hty
  have heq := Option.some.inj (hl.symm.trans hl')
  obtain ⟨rfl, rfl⟩ : cv = ⟨ty.name, p.lps, ty.type⟩ ∧ nIdx = nIdx' :=
    ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
  obtain ⟨bs, u, hstrip⟩ := ConLeche.auxIdxCount_stripPis hcount
  have hcvTa : f.cvTa = ⟨ty.name, p.lps, ty.type⟩ := hcv ⟨bs, u, by rw [hnP]; exact hstrip⟩
  obtain ⟨bs', hstrip'⟩ := R.h.strip t f hft
  rw [hcvTa] at hstrip'
  exact ⟨hcvTa, bs', hstrip'⟩

/-- **THE PINS' SCOPE AND TYPING AT THE PREFIX ENVIRONMENT** (K.30's
two conjuncts consumed, task #315 U-20 — the named fact
`NestedPinsScoped` of U-19, discharged): the run's third `nestedPinsOk`
IS at the prefix formers' environment (`consNestedFormers_take_eq`,
applied by `nestedCoreModeled_of`), and `pinsScoped` inverted at the
elimination's first type — the first former's own type (`formerType`
at `t = 0`) — gives the openers every pin's free variables lie among,
with no loose bound variable. -/
theorem NestedPinsRun.scoped :
    ConLeche.nestedPinsOk (m := ConLeche.CheckM) (fueledOps μ F) (ENV₁) p.nP st.pins = .ok () ∧
    ∃ (fvs : List Expr) (o : Expr), ConLeche.openPisAtFvars b.nP f₀.cvTa.type 0 = some (fvs, o) ∧
      ∀ q ∈ st.pins, q.pin.looseBVarsBounded 0 = true ∧
        ∀ l ∈ q.pin.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs := by
  refine ⟨R.hpinsE, ?_⟩
  obtain ⟨t₀, params, o, ht₀, hop, hall⟩ := ConLeche.pinsScoped_inv R.hscoped
  have hnP : b.nP = p.nP := (ConLeche.auxBlock_former R.hb).1
  have hty : st.types[0]? = some t₀ := by rw [← List.head?_eq_getElem?]; exact ht₀
  obtain ⟨hcvTa, -⟩ := R.formerType 0 f₀ R.h.first t₀ hty
  refine ⟨params, o, ?_, hall⟩
  rw [hcvTa, hnP]
  exact hop

/-- **THE PINS ARE WELL-SCOPED AT THE BLOCK'S PARAMETERS** (K.30's
second conjunct, at the scope PREDICATE): `scoped` hands the pin's
free-variable leaves among the first former's openers, and the opened
former's `var` clause turns each opener into its own index bound and
its annotation's scope — which is what `WScoped_of_leaves` asks for.
It is the machinery `pinRead_of_inferAt` runs for the pin as a whole,
taken on its own so that a consumer wanting a pin's COMPONENTS scoped
(`ContainerOwnPins`' premise, through `WScoped_mkAppN_args`) needs no
reading. -/
theorem NestedPinsRun.pinsWScoped : ∀ q ∈ st.pins, Expr.WScoped b.nP q.pin := by
  obtain ⟨-, hcl, hbt, hFD₀⟩ := R.former0
  obtain ⟨-, fvs, o, hop, hsc⟩ := R.scoped
  obtain ⟨Γ, Rt, htele, O⟩ :=
    opened_of (V := V) hop hcl hbt (hFD₀.read (fun _ => 0)) (hFD₀.okTy (fun _ => 0))
  have hlenF : fvs.length = b.nP := openPisAtFvars_length b.nP hop
  have hidx := openPisAtFvars_index b.nP f₀.cvTa.type 0 hop
  intro q hq
  refine WScoped_of_leaves q.pin fun l hl => ?_
  obtain ⟨pos, hpos⟩ := List.getElem?_of_mem ((hsc q hq).2 l hl)
  obtain ⟨ty', hx⟩ := hidx pos _ hpos
  rw [Nat.zero_add] at hx
  obtain ⟨rfl, -⟩ : l.1 = pos ∧ l.2 = ty' := by
    injection hx with a bb
    exact ⟨a, bb⟩
  obtain ⟨-, hw, -, -, -⟩ := O.var l.1 _ hpos
  exact ⟨by rw [← hlenF]; exact (List.getElem?_eq_some_iff.mp hpos).1, hw⟩

/-- **THE PINS' CONSTANTS RESOLVE AT THE PREFIX ENVIRONMENT** (task
#315 K.64 consumed, lane LE): `scoped`'s neighbour — the record
inverted, per pin.  Its consumer is the container clause carrying a
pin's components' READINGS, which crosses a later install only under
the projection guard, and which takes that guard from this fact the
way every other subject of the crossing does
(`ProjFree.of_constsResolve`). -/
theorem NestedPinsRun.resolved :
    ∀ q ∈ st.pins, q.pin.constsResolve (ENV₁) = true :=
  fun q hq => (ConLeche.pinsResolve_inv R.hK64 q hq).1

/-- **THE PINS' `.proj` NODES NAME STORED TABLES** (task #315 K.64's
second conjunct, lane LE): `resolved`'s sibling, and the guard at the
block's OWN install — a member is stored at this environment, so
resolution says nothing about a `.proj` node at one of them, while the
table walk does, because a member's TABLE is consed only at the end of
the install. -/
theorem NestedPinsRun.pinsProjTables :
    ∀ q ∈ st.pins, q.pin.projTablesOk (ENV₁) = true :=
  fun q hq => (ConLeche.pinsResolve_inv R.hK64 q hq).2

/-- **A pin's reading at the prefix model** (K.30 consumed): the pin's
`inferType` run at the prefix environment and its scope give its
reading, graded at every frame fitting the block's parameters. -/
theorem NestedPinsRun.pinRead
    (hpinsE : ConLeche.nestedPinsOk (m := ConLeche.CheckM) (fueledOps μ F) (ENV₁) p.nP st.pins = .ok ())
    {fvs : List Expr} {o : Expr} (hop : ConLeche.openPisAtFvars b.nP f₀.cvTa.type 0 = some (fvs, o))
    (hsc : ∀ q ∈ st.pins, q.pin.looseBVarsBounded 0 = true ∧
      ∀ l ∈ q.pin.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs)
    {q : Nat} (hq : q < st.pins.length) (ψ : Name → Nat) :
    ∃ ea, denoteMeta mp₁'.base2.acval (ENV₁) ψ b.nP (pinAtE st q).pin = some ea ∧
      ∀ ρ : Nat → V, Sat V ((((ppsF 0 ψ).take b.nP).map (·.2.2)).reverse) ρ → WellDenotedV V ρ ea := by
  obtain ⟨-, hcl, hbt, hFD₀⟩ := R.former0
  have hnP : b.nP = p.nP := (ConLeche.auxBlock_former R.hb).1
  have hmem : pinAtE st q ∈ st.pins := by
    unfold pinAtE
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
    exact List.getElem_mem hq
  obtain ⟨-, -, ty, hi⟩ := ConLeche.nestedPinsOk_inv hpinsE _ hmem
  rw [← hnP] at hi
  obtain ⟨hb, hleaf⟩ := hsc _ hmem
  exact pinRead_of_inferAt R.hμ mp₁' hFD₀ hcl hbt hop hi hb hleaf ψ


local notation "PINS" => (pinsOf mp.base2 st p mp₁'.base2.acval (ConLeche.consMutualFormers (fms.take p.k) env) b.nP)

/-- **The pin groups' syntactic half, at every pin** (the group of the
pin's BASE pin, its block model, the fields from K.28/K.29/K.14, the
same-universe fact and the components' fit). -/
theorem NestedPinsRun.groupSyn
    (hpinsE : ConLeche.nestedPinsOk (m := ConLeche.CheckM) (fueledOps μ F) (ENV₁) p.nP st.pins = .ok ())
    {fvs : List Expr} {o : Expr} (hop : ConLeche.openPisAtFvars b.nP f₀.cvTa.type 0 = some (fvs, o))
    (hsc : ∀ q ∈ st.pins, q.pin.looseBVarsBounded 0 = true ∧
      ∀ l ∈ q.pin.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs)
    {pbs : List (Expr × ConLeche.BinderMeta)} (hpbs : pbs.length = p.nP)
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    (dsR' : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (xFvsR' : Nat → Nat → List Expr)
    {q : Nat} (hq : q < st.pins.length) :
    ∃ (q₀ kJ i : Nat) (ci : ConLeche.ContainerInfo),
      ConLeche.containerInfo? env ((PINS).getD q default).J = some ci ∧
      q = q₀ + i ∧ i < kJ ∧
      NestedPinGroupSyn (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
        (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF)
        (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
        (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR') (xFvsR := xFvsR') (pinsS := PINS)
        st mp₁'.base2 q₀ kJ (blockOf mp.base2 ci) := by
  obtain ⟨hF, hres, hag, hde⟩ := R.cross
  have hnP : b.nP = p.nP := (ConLeche.auxBlock_former R.hb).1
  have hlenS : (PINS).length = st.pins.length := pinsOf_length _ _ _ _ _ _
  have hget : ∀ n, n < st.pins.length → (PINS).getD n default
      = pinOf mp.base2 st p mp₁'.base2.acval (ENV₁) b.nP n := fun n hn => pinsOf_getD _ _ _ _ _ _ hn
  have hpinAt : ∀ n, (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
      srcsF fvsPF xrestF eissF tssF ctorsR dsR' xFvsR' (PINS)).pinAt n = (PINS).getD n default :=
    fun _ => rfl
  have PD := hPD q hq
  -- the group: its base, size, member index
  obtain ⟨hb1, hb2, hb3⟩ := PD.seg
  have hkpos : 0 < (pinAtE st q).grpSize := by omega
  -- the base pin's group's block model, at the pre-block model, crossed
  have hbaseMem : pinAtE st (pinAtE st q).grpBase ∈ st.pins := by
    have hlt : (pinAtE st q).grpBase < st.pins.length := by omega
    show st.pins.getD (pinAtE st q).grpBase default ∈ st.pins
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    exact List.getElem_mem hlt
  have CM₀ : ContainerModeled mp.base2 (baseInfo env st q) (blockOf mp.base2 (baseInfo env st q)) :=
    blockOf_spec (R.hPM _ hbaseMem _ PD.base)
  have CM : ContainerModeled mp₁'.base2 (baseInfo env st q) (blockOf mp.base2 (baseInfo env st q)) :=
    CM₀.crossEnv hF hres hag hde (by rw [CM₀.k, PD.baseLen]; exact hkpos)
      (fun _ _ _ h => R.contsCross h) (R.ownCross CM₀)
  have hkJ : (blockOf mp.base2 (baseInfo env st q)).k = (pinAtE st q).grpSize := by
    rw [CM.k, PD.baseLen]
  -- the group's pins, described
  have hgp : ∀ i, i < (pinAtE st q).grpSize →
      (PINS).getD ((pinAtE st q).grpBase + i) default
        = groupPin mp.base2 st p mp₁'.base2.acval (ENV₁) b.nP q i := by
    intro i hi
    rw [hget _ (by omega)]
    exact PD.pinOf_group _ _ _ _ hi
  -- the components' count
  obtain ⟨ci, hci, hDl, -, hnPci, -, -⟩ := PD.own
  have hDsLen : (srcAtE st p q).2.2.length = (blockOf mp.base2 (baseInfo env st q)).nP := by
    rw [hDl, hnPci, CM.nP]
  -- the stored container of the `i`-th member, from the base's group
  have hmemInfo : ∀ i, i < (pinAtE st q).grpSize →
      ∃ (cvC : ConstantVal) (capsC : IndCaps) (cvRc : ConstantVal) (mIc rPc : Nat)
        (rulesC : List RecRule),
        env.find? (memberOf env st q i).name = some (.indInfo cvC capsC) ∧
        env.find? ((memberOf env st q i).name.str "rec") = some (.recInfo cvRc mIc rPc rulesC) ∧
        (memberOf env st q i).lps = cvC.levelParams ∧ (memberOf env st q i).type = cvC.type ∧
        (memberOf env st q i).ctors.length = rulesC.length := by
    intro i hi
    have hinv := ConLeche.containerInfo?_inv PD.base
    obtain ⟨_cvT, _caps, _cvR, _mI, rP, _rules, -, -, -, -, hall⟩ := hinv
    obtain ⟨cvC, capsC, cvRc, mIc, rulesC, hf, hr, hlps, hty, -, hcl, -⟩ :=
      hall _ (List.mem_of_getElem? (PD.grp i hi).2.2.2.2)
    exact ⟨cvC, capsC, cvRc, mIc, _, rulesC, hf, hr, hlps, hty, hcl⟩
  -- the `i`-th pin's own copy record (K.28 at that pin), tied to the base's member
  have hownAt : ∀ i, i < (pinAtE st q).grpSize →
      ∃ (J : ContainerMember) (c : ConLeche.AuxType),
        J.name = (memberOf env st q i).name ∧
        ConLeche.mkCopy pbs (srcAtE st p q).2.1 (srcAtE st p q).2.2
          (copyAtE st p ((pinAtE st q).grpBase + i)).name J = .ok c ∧
        c.type = (copyAtE st p ((pinAtE st q).grpBase + i)).type ∧
        c.ctors.length = (copyAtE st p ((pinAtE st q).grpBase + i)).ctors.length ∧
        c.ctors.length = J.ctors.length ∧
        (srcAtE st p q).2.1.length = J.lps.length ∧
        ∃ (cvC : ConstantVal) (capsC : IndCaps) (cvRc : ConstantVal) (mIc rPc : Nat)
          (rulesC : List RecRule),
          env.find? J.name = some (.indInfo cvC capsC) ∧
          env.find? (J.name.str "rec") = some (.recInfo cvRc mIc rPc rulesC) ∧
          J.lps = cvC.levelParams ∧ J.type = cvC.type ∧ J.ctors.length = rulesC.length := by
    intro i hi
    have PDi := hPD ((pinAtE st q).grpBase + i) (by omega)
    obtain ⟨cii, hcii, -, -, -, -, J, hJ, hJn, c, hmk, hct, hcc⟩ := PDi.own
    rw [PD.srcAtE_group hi] at hmk
    have hJn' : J.name = (memberOf env st q i).name := by rw [hJn, (PD.grp i hi).1]
    obtain ⟨hlvls, -, -, -, hclen, -⟩ := ConLeche.mkCopy_inv hmk
    have hinv := ConLeche.containerInfo?_inv hcii
    obtain ⟨_cvT, _caps, _cvR, _mI, rP, _rules, -, -, -, -, hall⟩ := hinv
    obtain ⟨cvC, capsC, cvRc, mIc, rulesC, hf, hr, hlps, hty, -, hcl, -⟩ :=
      hall _ (List.mem_of_find?_eq_some hJ)
    refine ⟨J, c, hJn', hmk, hct, ?_, hclen, hlvls, cvC, capsC, cvRc, mIc, _, rulesC, hf, hr, hlps,
      hty, hcl⟩
    have := congrArg List.length hcc
    simpa using this
  -- the two records of a member name agree
  have hsame : ∀ i, i < (pinAtE st q).grpSize →
      ∀ (J : ContainerMember), J.name = (memberOf env st q i).name →
      ∀ (cvC : ConstantVal) (capsC : IndCaps) (cvC' : ConstantVal) (capsC' : IndCaps),
        env.find? J.name = some (.indInfo cvC capsC) →
        env.find? (memberOf env st q i).name = some (.indInfo cvC' capsC') → cvC = cvC' := by
    intro i _ J hJ cvC capsC cvC' capsC' h1 h2
    rw [hJ] at h1
    exact (ConstantInfo.indInfo.inj (Option.some.inj (h1.symm.trans h2))).1
  -- IsBlockModel at member i, at the prefix model
  have hIB : ∀ i, i < (pinAtE st q).grpSize →
      (blockOf mp.base2 (baseInfo env st q)).memberName i = (memberOf env st q i).name ∧
      ((blockOf mp.base2 (baseInfo env st q)).ctorsM i).map (·.1.name)
        = (memberOf env st q i).ctors.map (·.name) ∧
      ∃ (cvR : ConstantVal) (mI rP : Nat) (rules : List RecRule),
        IsBlockModel mp₁'.base2 (memberOf env st q i).name
          ⟨(memberOf env st q i).name, (memberOf env st q i).lps, (memberOf env st q i).type⟩
          cvR mI rP rules (blockOf mp.base2 (baseInfo env st q)) i :=
    fun i hi => CM.member i _ (PD.grp i hi).2.2.2.2
  -- the pin's OWN container reads back as its group's base (K.14's two
  -- agreements at `containerInfo?_eq_of_names`), so the group's block
  -- model is the assignment's value at the pin's own reading — which is
  -- what `ContainerModeled`'s consumers key it by (task #315 M7-3
  -- session 12)
  obtain ⟨ciq, hciq, -, -, hnPq, hnamesq, -⟩ := PD.own
  have hciqJ : ConLeche.containerInfo? env ((PINS).getD q default).J = some ciq := by
    rw [hget q hq]; exact hciq
  have hciqEq : ciq = baseInfo env st q :=
    ConLeche.containerInfo?_eq_of_names hciq PD.base hnPq hnamesq
  refine ⟨(pinAtE st q).grpBase, (pinAtE st q).grpSize, q - (pinAtE st q).grpBase,
    ciq, hciqJ, by omega, by omega, ?_⟩
  rw [hciqEq]
  refine
    { seg := by rw [hlenS]; exact hb3
      kpos := hkpos
      grp := fun i hi => ⟨(PD.grp i hi).2.1, (PD.grp i hi).2.2.1⟩
      modeled := fun i hi ci' hci' => by
        rw [hpinAt, hgp i hi] at hci'
        change ConLeche.containerInfo? env (memberOf env st q i).name = some ci' at hci'
        have PDi := hPD ((pinAtE st q).grpBase + i) (by omega)
        obtain ⟨cii, hcii, -, -, hnPi, hnamesi, -⟩ := PDi.own
        rw [(PD.grp i hi).1] at hcii
        rw [PD.baseInfo_group hi] at hnPi hnamesi
        obtain rfl : ci' = cii := Option.some.inj (hci'.symm.trans hcii)
        rw [ConLeche.containerInfo?_eq_of_names hci' PD.base hnPi hnamesi]
        exact CM
      contsEnv := CM₀.pinConts
      pinViews := by
        -- the container's OWN pins' views, off its `BlockAt`'s `PinShapes`
        obtain ⟨-, -, hSh⟩ := R.hPM _ hbaseMem _ PD.base
        intro qq hqq
        obtain ⟨a, kk, i', ci', hqe, hi', -, hview, -, -⟩ := hSh qq hqq
        exact ⟨a, kk, i', blockOf mp.base2 ci', hqe, hi', hview⟩
      pinOwn := by
        -- the container's own pins' views at the family, and the BLOCK
        -- pin's own group at the same family: `pinOwn_core` joins them
        obtain ⟨-, -, hSh⟩ := R.hPM _ hbaseMem _ PD.base
        intro qq hqq q₂ hq₂ hJeq cv caps hfind φ ψ' hag
        rw [hpinAt] at hJeq hag ⊢
        rw [← hJeq] at hfind
        have hq₂' : q₂ < st.pins.length := by rw [← hlenS]; exact hq₂
        have PD₂ := hPD q₂ hq₂'
        obtain ⟨hb1₂, hb2₂, hb3₂⟩ := PD₂.seg
        have hm₂ : q₂ - (pinAtE st q₂).grpBase < (pinAtE st q₂).grpSize := by omega
        have hq₂e : (pinAtE st q₂).grpBase + (q₂ - (pinAtE st q₂).grpBase) = q₂ := by omega
        have hbaseMem₂ : pinAtE st (pinAtE st q₂).grpBase ∈ st.pins := by
          have hlt : (pinAtE st q₂).grpBase < st.pins.length := by omega
          show st.pins.getD (pinAtE st q₂).grpBase default ∈ st.pins
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
          exact List.getElem_mem hlt
        have CM₂ : ContainerModeled mp.base2 (baseInfo env st q₂)
            (blockOf mp.base2 (baseInfo env st q₂)) :=
          blockOf_spec (R.hPM _ hbaseMem₂ _ PD₂.base)
        obtain ⟨ci₂, hci₂, -, -, hnP₂, hnames₂, -⟩ := PD₂.own
        obtain rfl : ci₂ = baseInfo env st q₂ :=
          ConLeche.containerInfo?_eq_of_names hci₂ PD₂.base hnP₂ hnames₂
        have hgq₂ : (PINS).getD q₂ default
            = pinOf mp.base2 st p mp₁'.base2.acval (ENV₁) b.nP q₂ := hget q₂ hq₂'
        have hJ₂ : ((PINS).getD q₂ default).J = (pinAtE st q₂).container := by
          rw [hgq₂]; rfl
        have hci₂J : ConLeche.containerInfo? env ((PINS).getD q₂ default).J
            = some (baseInfo env st q₂) := by rw [hJ₂]; exact hci₂
        have hi₂ : q₂ - (pinAtE st q₂).grpBase
            < (blockOf mp.base2 (baseInfo env st q₂)).k := by
          rw [CM₂.k, PD₂.baseLen]; exact hm₂
        have hname₂ : (blockOf mp.base2 (baseInfo env st q₂)).memberName
              (q₂ - (pinAtE st q₂).grpBase) = ((PINS).getD q₂ default).J := by
          have hc := (PD₂.grp _ hm₂).1
          rw [hq₂e] at hc
          rw [hJ₂, hc]
          exact (CM₂.member _ _ (PD₂.grp _ hm₂).2.2.2.2).1
        -- the container is none of the block's own formers, so the two
        -- environments hold the same constant under its name
        have hne : ∀ g ∈ fms.take p.k, g.cvTa.name ≠ ((PINS).getD q₂ default).J := by
          intro g hg heq
          obtain ⟨cvX, capsX, hfX⟩ := containerInfo?_found hci₂J
          obtain ⟨t, ht⟩ := List.getElem?_of_mem (List.mem_of_mem_take hg)
          have hfr := R.h.fresh t g ht
          rw [heq, hfX] at hfr
          exact nomatch hfr
        have hfindEnv : env.find? ((PINS).getD q₂ default).J = some (.indInfo cv caps) := by
          rw [← consMutualFormers_find?_of_ne (env := env) hne]
          exact hfind
        exact pinOwn_core (m₀ := mp.base2) (B := blockOf mp.base2) hSh hqq CM₂ hJeq hci₂J
          hi₂ hname₂ (fun φ' => by rw [hgq₂]; rfl) (by rw [hgq₂]; rfl) (by rw [hgq₂]; rfl)
          hfindEnv φ ψ' hag
      reps := CM.reps
      kEq := hkJ
      rep := ?_
      typed := fun ψ => (CM.typed ψ).1
      pinsTyped := fun ψ => (CM.typed ψ).2.2
      inj := CM.inj (by rw [CM.nP, ← hnPci, ← hDl]; exact R.pinDsPos hPD hq)
      pinU := fun i hi ψ i' hi' => by
        rw [hpinAt, hpinAt, hgp i' hi', hgp i hi]
        show (blockOf mp.base2 (baseInfo env st q)).uM i'
            (Level.substFn ψ (memberOf env st q i').lps (srcAtE st p q).2.1)
          = (blockOf mp.base2 (baseInfo env st q)).uM i'
            (Level.substFn ψ (memberOf env st q i).lps (srcAtE st p q).2.1)
        rw [PD.lps_group hi' hi]
      pinNP := fun i hi => by rw [hpinAt, hgp i hi]; rfl
      pinNIdx := fun i hi => by rw [hpinAt, hgp i hi]; rfl
      pinPps := fun i hi => by rw [hpinAt, hgp i hi]; rfl
      pinDsLen := fun i hi ψ => by
        rw [hpinAt, hgp i hi]
        show ((srcAtE st p q).2.2.map _).length = _
        rw [List.length_map, hDsLen]
      same := fun i hi => by
        have h0 := hgp 0 hkpos
        rw [Nat.add_zero] at h0
        rw [hpinAt, hpinAt, hgp i hi, h0]
        exact ⟨rfl, rfl⟩
      sameDs := fun i hi ψ => by
        have h0 := hgp 0 hkpos
        rw [Nat.add_zero] at h0
        rw [hpinAt, hpinAt, hgp i hi, h0]
        rfl
      w := ?_
      ctorCount := ?_
      DsFit := ?_
      stored := ?_
      ψJEq := ?_
      ctorsOf := ?_ }
  · -- rep: the block at the `i`-th pin's container, the level assignment spelled
    intro i hi
    obtain ⟨-, -, cvR, mI, rP, rules, hI⟩ := hIB i hi
    refine ⟨⟨(memberOf env st q i).name, (memberOf env st q i).lps, (memberOf env st q i).type⟩,
      cvR, mI, rP, rules, ?_, fun ψ => ?_⟩
    · rw [hpinAt, hgp i hi]; exact hI
    · rw [hpinAt, hgp i hi]; rfl
  · -- w: the copy's sort is the container's at the pin's level assignment
    intro i hi ψ
    rw [hpinAt, hgp i hi]
    show (blockOf mp.base2 (baseInfo env st q)).resSort.eval
        (Level.substFn ψ (memberOf env st q i).lps (srcAtE st p q).2.1) = f₀.s.eval ψ
    obtain ⟨-, -, cvR, mI, rP, rules, hI⟩ := hIB i hi
    obtain ⟨bsM, sM, hstripM, hsM⟩ := hI.strip
    obtain ⟨J, c, hJn, hmk, hct, -, -, -, cvC, capsC, -, -, -, -, hfJ, -, hlpsJ, htyJ, -⟩ :=
      hownAt i hi
    obtain ⟨cvC', capsC', -, -, -, -, hfM, -, hlpsM, htyM, -⟩ := hmemInfo i hi
    have hcv := hsame i hi J hJn cvC capsC cvC' capsC' hfJ hfM
    have hJty : J.type = (memberOf env st q i).type := by rw [htyJ, htyM, hcv]
    have hJlps : J.lps = (memberOf env st q i).lps := by rw [hlpsJ, hlpsM, hcv]
    have hJ' : J.type.stripPis ((srcAtE st p q).2.2.length + (blockOf mp.base2 (baseInfo env st q)).nIdxAt i)
        = some (bsM, .sort sM) := by
      rw [hJty, hDsLen]
      exact hstripM
    obtain ⟨bs', hstrip'⟩ := ConLeche.mkCopy_stripPis_sort hmk hJ'
    rw [hct] at hstrip'
    -- the auxiliary former at this copy
    have hlt : p.k + ((pinAtE st q).grpBase + i) < fms.length := by
      rw [R.h.lenFms, R.hbk]; omega
    have PDi := hPD ((pinAtE st q).grpBase + i) (by omega)
    obtain ⟨hcvTa, bsF, hstripF⟩ := R.formerType _ _ (fms_get hlt) _ PDi.ty
    rw [hpbs, ← hnP] at hstrip'
    obtain ⟨-, -, hsEq⟩ := ConLeche.stripPis_sort_unique hstrip' hstripF
    rw [R.h.sEq _ _ (fms_get hlt) ψ |>.symm, ← hsEq, ConLeche.Level.eval_subst, ← hJlps, ← hsM]
  · -- ctorCount: the container member's constructor count is the copy's
    intro i' hi'
    obtain ⟨-, hcnt, -⟩ := hIB i' hi'
    obtain ⟨J, c, hJn, -, -, hcc, hcJ, -, cvC, capsC, cvRc, mIc, rPc, rulesC, hfJ, hrJ, -, -, hclJ⟩ :=
      hownAt i' hi'
    obtain ⟨cvC', capsC', cvRc', mIc', rPc', rulesC', -, hrM, -, -, hclM⟩ := hmemInfo i' hi'
    have PDi := hPD ((pinAtE st q).grpBase + i') (by omega)
    have hown := ConLeche.auxBlock_ownCtors_length R.hb _ _ PDi.ty
    rw [hJn] at hrJ
    have hrules : rulesC = rulesC' :=
      (ConLeche.ConstantInfo.recInfo.inj (Option.some.inj (hrJ.symm.trans hrM))).2.2.2
    rw [← Nat.add_assoc] at hown
    have hcnt' : ((blockOf mp.base2 (baseInfo env st q)).ctorsM i').length
        = (memberOf env st q i').ctors.length := by
      have := congrArg List.length hcnt
      simpa using this
    rw [hcnt', hown, ← hcc, hcJ, hclJ, hclM, hrules]
  · -- DsFit: the components' readings fit the container's parameters
    intro i hi ψ ρ as hsp
    rw [hpinAt, hgp i hi]
    show SpineFit (consList as ρ)
      ((blockOf mp.base2 (baseInfo env st q)).params
        (Level.substFn ψ (memberOf env st q i).lps (srcAtE st p q).2.1))
      (((srcAtE st p q).2.2.map fun e =>
          (denoteMeta mp₁'.base2.acval (ENV₁) ψ b.nP e).getD default).map (interp V (consList as ρ)))
    obtain ⟨-, -, cvR, mI, rP, rules, hI⟩ := hIB i hi
    obtain ⟨J, -, hJn, -, -, -, -, hlvls, cvC, capsC, -, -, -, -, hfJ, -, hlpsJ, -, -⟩ := hownAt i hi
    obtain ⟨cvC', capsC', -, -, -, -, hfM, -, hlpsM, -, -⟩ := hmemInfo i hi
    have hcv := hsame i hi J hJn cvC capsC cvC' capsC' hfJ hfM
    have PDi := hPD ((pinAtE st q).grpBase + i) (by omega)
    obtain ⟨ea, hea, hok⟩ := R.pinRead hpinsE hop hsc (q := (pinAtE st q).grpBase + i) (by omega) ψ
    rw [PD.pinEq_group PDi hi] at hea
    obtain ⟨fa, vs, hfa, hspine, rfl⟩ := denoteMeta_mkAppN_inv hea
    have hfM₁ : (ENV₁).find? (memberOf env st q i).name = some (.indInfo cvC' capsC') :=
      hF _ _ (fun _ _ _ _ h => nomatch h) hfM
    rw [denoteMeta_const hfM₁ (by
      show (srcAtE st p q).2.1.length = cvC'.levelParams.length
      rw [hlvls, hlpsJ, hcv])] at hfa
    obtain rfl := Option.some.inj hfa
    have hvs := hspine.eq_map
    have hSat : Sat V ((((ppsF 0 ψ).take b.nP).map (·.2.2)).reverse) (consList as ρ) := by
      have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hsp
      rwa [List.append_nil] at this
    have hwd := (hok _ hSat).1
    rw [← hvs]
    have hfr := CM.frame i (by rw [hkJ]; exact hi)
    have hψ : Level.substFn ψ (ConstantInfo.indInfo cvC' capsC').toConstantVal.levelParams (srcAtE st p q).2.1
        = Level.substFn ψ (memberOf env st q i).lps (srcAtE st p q).2.1 := by
      show Level.substFn ψ cvC'.levelParams _ = _
      rw [hlpsM]
    rw [hψ] at hwd
    refine pinFit_of_wd hI CM.reps (CM.typed _).1 (hfr _) ?_ hwd
    rw [hvs, List.length_map, hDsLen]
  · -- stored: the block at the STORED constant of the `i`-th pin's container
    intro i hi
    obtain ⟨-, -, cvR, mI, rP, rules, hI⟩ := hIB i hi
    obtain ⟨cvC, capsC, -, -, -, -, hfM, -, hlpsM, htyM, -⟩ := hmemInfo i hi
    have hname : cvC.name = (memberOf env st q i).name := ConLeche.Env.find?_name hfM
    have hcv : cvC = ⟨(memberOf env st q i).name, (memberOf env st q i).lps, (memberOf env st q i).type⟩ := by
      cases cvC
      simp only [ConstantVal.mk.injEq]
      exact ⟨hname, hlpsM.symm, htyM.symm⟩
    refine ⟨⟨(memberOf env st q i).name, (memberOf env st q i).lps, (memberOf env st q i).type⟩,
      capsC, cvR, mI, rP, rules, ?_, ?_, fun ψ => ?_⟩
    · rw [hpinAt, hgp i hi]
      show (ENV₁).find? (memberOf env st q i).name = _
      rw [← hcv]
      exact hF _ _ (fun _ _ _ _ h => nomatch h) hfM
    · rw [hpinAt, hgp i hi]; exact hI
    · rw [hpinAt, hgp i hi]; rfl
  · -- ψJEq: the group's members share their level parameters
    intro i i' hi hi' ψ
    rw [hpinAt, hpinAt, hgp i hi, hgp i' hi']
    show Level.substFn ψ (memberOf env st q i).lps (srcAtE st p q).2.1
      = Level.substFn ψ (memberOf env st q i').lps (srcAtE st p q).2.1
    obtain ⟨cvT₀, _caps₀, _cvR₀, _mI₀, rP₀, _rules₀, -, -, -, -, hall⟩ :=
      ConLeche.containerInfo?_inv PD.base
    have hlps : ∀ i, i < (pinAtE st q).grpSize → (memberOf env st q i).lps = cvT₀.levelParams := by
      intro i hi
      obtain ⟨cvC, _capsC, _cvRc, _mIc, _rulesC, -, -, hlpsM, -, hlpsT, -, -⟩ :=
        hall _ (List.mem_of_getElem? (PD.grp i hi).2.2.2.2)
      rw [hlpsM, hlpsT]
    rw [hlps i hi, hlps i' hi']
  · -- ctorsOf: the pin's own container member IS the base group's
    intro i' hi' ciJ J hciJ hJmem hJname
    rw [hpinAt, hgp i' hi'] at hciJ hJname
    change ConLeche.containerInfo? env (memberOf env st q i').name = some ciJ at hciJ
    change J.name = (memberOf env st q i').name at hJname
    have PDi := hPD ((pinAtE st q).grpBase + i') (by omega)
    obtain ⟨cii, hcii, -, -, hnPi, -, -, -, -, -, -, -, -⟩ := PDi.own
    have hbase : (pinAtE st ((pinAtE st q).grpBase + i')).grpBase = (pinAtE st q).grpBase :=
      (PD.grp i' hi').2.1
    have hbi : baseInfo env st ((pinAtE st q).grpBase + i') = baseInfo env st q := by
      unfold baseInfo; rw [hbase]
    rw [(PD.grp i' hi').1] at hcii
    obtain rfl : cii = ciJ := Option.some.inj (hcii.symm.trans hciJ)
    rw [hbi] at hnPi
    have hMmem : memberOf env st q i' ∈ (baseInfo env st q).members :=
      List.mem_of_getElem? (PD.grp i' hi').2.2.2.2
    obtain rfl : J = memberOf env st q i' :=
      ConLeche.containerInfo?_member_det hciJ PD.base hnPi hJmem hMmem hJname
    exact ⟨(hIB i' hi').2.1, by rw [CM.nP, hnPi]⟩

/-- **A pin's level assignment is the substitution at its container's
level parameters** (`NestedPinFacts.pinψ`, U-19b's interface; task
#315 U-20): at the prefix environment's record of the pin's container,
the pin's level arguments count the record's parameters and `pinOf`'s
`ψJ` is the substitution at them — the group member's `lps` ARE the
record's (`containerInfo?_inv` at the base's group), and K.28's
`mkCopy` fixes the count (`mkCopy_inv`). -/
theorem NestedPinsRun.pinψ {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    {q : Nat} (hq : q < st.pins.length) (cvT : ConstantVal) (caps : IndCaps)
    (hfind : (ENV₁).find? (pinOf mp.base2 st p mp₁'.base2.acval (ENV₁) b.nP q).J
      = some (.indInfo cvT caps)) :
    (pinOf mp.base2 st p mp₁'.base2.acval (ENV₁) b.nP q).lvls.length = cvT.levelParams.length ∧
    ∀ ψ : Name → Nat, (pinOf mp.base2 st p mp₁'.base2.acval (ENV₁) b.nP q).ψJ ψ
      = Level.substFn ψ cvT.levelParams (pinOf mp.base2 st p mp₁'.base2.acval (ENV₁) b.nP q).lvls := by
  obtain ⟨hF, -, -, -⟩ := R.cross
  have PD := hPD q hq
  obtain ⟨hb1, hb2, -⟩ := PD.seg
  have hi : q - (pinAtE st q).grpBase < (pinAtE st q).grpSize := by omega
  have hqi : (pinAtE st q).grpBase + (q - (pinAtE st q).grpBase) = q := by omega
  have hg := PD.grp _ hi
  rw [hqi] at hg
  obtain ⟨hcontE, -, -, -, hmemE⟩ := hg
  -- the member's record at the pre-block environment, crossed
  obtain ⟨_, _, _, _, _, _, -, -, -, -, hall⟩ := ConLeche.containerInfo?_inv PD.base
  obtain ⟨cvC, capsC, -, -, -, hfM, -, hlpsM, -, -, -, -⟩ := hall _ (List.mem_of_getElem? hmemE)
  have hfM₁ : (ENV₁).find? (memberOf env st q (q - (pinAtE st q).grpBase)).name
      = some (.indInfo cvC capsC) := hF _ _ (fun _ _ _ _ h => nomatch h) hfM
  have hfind' : (ENV₁).find? (memberOf env st q (q - (pinAtE st q).grpBase)).name
      = some (.indInfo cvT caps) := by rw [← hcontE]; exact hfind
  have hcv : cvC = cvT := (ConstantInfo.indInfo.inj (Option.some.inj (hfM₁.symm.trans hfind'))).1
  -- K.28: the copy's level arguments count the member's parameters
  obtain ⟨ci, hci, -, -, -, -, J, hJfind, hJn, c, hmk, -, -⟩ := PD.own
  obtain ⟨hlvls, -, -, -, -, -⟩ := ConLeche.mkCopy_inv hmk
  obtain ⟨_, _, _, _, _, _, -, -, -, -, hall'⟩ := ConLeche.containerInfo?_inv hci
  obtain ⟨cvC', capsC', -, -, -, hfJ, -, hlpsJ, -, -, -, -⟩ :=
    hall' _ (List.mem_of_find?_eq_some hJfind)
  rw [hJn, hcontE] at hfJ
  have hcv' : cvC' = cvC := (ConstantInfo.indInfo.inj (Option.some.inj (hfJ.symm.trans hfM))).1
  refine ⟨?_, fun ψ => ?_⟩
  · show (srcAtE st p q).2.1.length = cvT.levelParams.length
    rw [hlvls, hlpsJ, hcv', hcv]
  · show Level.substFn ψ (memberOf env st q (q - (pinAtE st q).grpBase)).lps (srcAtE st p q).2.1
      = Level.substFn ψ cvT.levelParams (srcAtE st p q).2.1
    rw [hlpsM, hcv]

/-- **The copy's index count is the pin's** (`NestedPinFacts.pinNIdx`,
U-19b's interface; task #315 U-20): the auxiliary former at `p.k + q`
strips at the block's parameters plus its index count to its sort
(`formerType`), and so does `mkCopy`'s output at the container member's
index count (`IsBlockModel.strip` at the group's block model, through
`mkCopy_stripPis_sort`); `stripPis_sort_unique` equates the counts. -/
theorem NestedPinsRun.pinNIdx {pbs : List (Expr × ConLeche.BinderMeta)} (hpbs : pbs.length = p.nP)
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    {q : Nat} (hq : q < st.pins.length) :
    (fms.getD (p.k + q) default).nIdx
      = (pinOf mp.base2 st p mp₁'.base2.acval (ENV₁) b.nP q).nIdx := by
  obtain ⟨hF, hres, hag, hde⟩ := R.cross
  have hnP : b.nP = p.nP := (ConLeche.auxBlock_former R.hb).1
  have PD := hPD q hq
  obtain ⟨hb1, hb2, -⟩ := PD.seg
  have hi : q - (pinAtE st q).grpBase < (pinAtE st q).grpSize := by omega
  have hqi : (pinAtE st q).grpBase + (q - (pinAtE st q).grpBase) = q := by omega
  have hg := PD.grp _ hi
  rw [hqi] at hg
  obtain ⟨hcontE, -, -, -, hmemE⟩ := hg
  -- the group's block model, at the prefix model
  have hbaseMem : pinAtE st (pinAtE st q).grpBase ∈ st.pins := by
    have hlt : (pinAtE st q).grpBase < st.pins.length := by omega
    show st.pins.getD (pinAtE st q).grpBase default ∈ st.pins
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    exact List.getElem_mem hlt
  have CM₀ : ContainerModeled mp.base2 (baseInfo env st q) (blockOf mp.base2 (baseInfo env st q)) :=
    blockOf_spec (R.hPM _ hbaseMem _ PD.base)
  have CM : ContainerModeled mp₁'.base2 (baseInfo env st q) (blockOf mp.base2 (baseInfo env st q)) :=
    CM₀.crossEnv hF hres hag hde (by rw [CM₀.k, PD.baseLen]; omega)
      (fun _ _ _ h => R.contsCross h) (R.ownCross CM₀)
  obtain ⟨-, -, cvR, mI, rP, rules, hI⟩ := CM.member _ _ hmemE
  obtain ⟨bsM, sM, hstripM, -⟩ := hI.strip
  -- K.28 at the pin: the copy from the member `J`, whose type is the member's
  obtain ⟨ci, hci, hDl, -, hnPci, -, J, hJfind, hJn, c, hmk, hct, -⟩ := PD.own
  obtain ⟨_, _, _, _, _, _, -, -, -, -, hall'⟩ := ConLeche.containerInfo?_inv hci
  obtain ⟨cvC', capsC', -, -, -, hfJ, -, -, htyJ, -, -, -⟩ :=
    hall' _ (List.mem_of_find?_eq_some hJfind)
  obtain ⟨_, _, _, _, _, _, -, -, -, -, hall⟩ := ConLeche.containerInfo?_inv PD.base
  obtain ⟨cvC, capsC, -, -, -, hfM, -, -, htyM, -, -, -⟩ := hall _ (List.mem_of_getElem? hmemE)
  rw [hJn, hcontE] at hfJ
  have hcv : cvC' = cvC := (ConstantInfo.indInfo.inj (Option.some.inj (hfJ.symm.trans hfM))).1
  have hDsLen : (srcAtE st p q).2.2.length = (blockOf mp.base2 (baseInfo env st q)).nP := by
    rw [hDl, hnPci, CM.nP]
  have hJ' : J.type.stripPis ((srcAtE st p q).2.2.length
      + (blockOf mp.base2 (baseInfo env st q)).nIdxAt (q - (pinAtE st q).grpBase))
      = some (bsM, .sort sM) := by
    rw [htyJ, hcv, ← htyM, hDsLen]
    exact hstripM
  obtain ⟨bs', hstrip'⟩ := ConLeche.mkCopy_stripPis_sort hmk hJ'
  rw [hct] at hstrip'
  -- the auxiliary former at this copy
  have hlt : p.k + q < fms.length := by rw [R.h.lenFms, R.hbk]; omega
  obtain ⟨-, bsF, hstripF⟩ := R.formerType _ _ (fms_get hlt) _ PD.ty
  rw [hpbs, ← hnP] at hstrip'
  obtain ⟨hn, -, -⟩ := ConLeche.stripPis_sort_unique hstrip' hstripF
  show _ = (blockOf mp.base2 (baseInfo env st q)).nIdxAt (q - (pinAtE st q).grpBase)
  omega

/-- **The pins' syntactic facts at the prefix model** (PROVED): the
records, the components' readings and every group's syntactic half,
at `pinsOf`. -/
theorem NestedPinsRun.synFacts
    (hpinsE : ConLeche.nestedPinsOk (m := ConLeche.CheckM) (fueledOps μ F) (ENV₁) p.nP st.pins = .ok ())
    {fvs : List Expr} {o : Expr} (hop : ConLeche.openPisAtFvars b.nP f₀.cvTa.type 0 = some (fvs, o))
    (hsc : ∀ q ∈ st.pins, q.pin.looseBVarsBounded 0 = true ∧
      ∀ l ∈ q.pin.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs) :
    NestedPinSynFacts (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
      (kinds := kinds) (env := env) (mp := mp) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF)
      (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
      (tssF := tssF) (ctorsR := ctorsR) (pinsS := PINS) st mp₁' := by
  obtain ⟨pbs, hpbs, hPD⟩ := R.pinData
  have hlenS : (PINS).length = st.pins.length := pinsOf_length _ _ _ _ _ _
  have hget : ∀ n, n < st.pins.length → (PINS).getD n default
      = pinOf mp.base2 st p mp₁'.base2.acval (ENV₁) b.nP n := fun n hn => pinsOf_getD _ _ _ _ _ _ hn
  refine ⟨hlenS, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the records
    intro q pin hpin
    have hq : q < st.pins.length := (List.getElem?_eq_some_iff.mp hpin).1
    have PD := hPD q hq
    obtain rfl : pin = pinAtE st q := Option.some.inj (hpin.symm.trans PD.pin)
    rw [hget q hq]
    exact ⟨rfl, PD.pinEq⟩
  · -- the components' readings
    intro q hq ψ
    rw [hlenS] at hq
    rw [hget q hq]
    have PD := hPD q hq
    obtain ⟨ea, hea, -⟩ := R.pinRead hpinsE hop hsc hq ψ
    rw [PD.pinEq] at hea
    obtain ⟨fa, vs, -, hspine, -⟩ := denoteMeta_mkAppN_inv hea
    have hvs := hspine.eq_map
    show DenoteMetaSpine _ _ _ _ (srcAtE st p q).2.2 ((srcAtE st p q).2.2.map _)
    rw [← hvs]
    exact hspine
  · -- the components' GRADING, off the pin's own `inferType`
    intro q hq ψ ρ hsat A hA
    rw [hlenS] at hq
    rw [hget q hq] at hA
    have PD := hPD q hq
    obtain ⟨ea, hea, hok⟩ := R.pinRead hpinsE hop hsc hq ψ
    rw [PD.pinEq] at hea
    obtain ⟨fa, vs, -, hspine, rfl⟩ := denoteMeta_mkAppN_inv hea
    have hvs := hspine.eq_map
    have hA' : A ∈ vs := by
      rw [hvs]
      exact hA
    obtain ⟨hw, hv⟩ := hok ρ hsat
    exact ⟨(WellDenoted.mkAppN_inv hw).2 A hA', (AnnotValid.mkAppN_inv hv).2 A hA'⟩
  · -- the groups
    intro dsR' xFvsR' q hq
    rw [hlenS] at hq
    obtain ⟨q₀, kJ, i, ci, -, hqe, hi, S⟩ := R.groupSyn hpinsE hop hsc hpbs hPD dsR' xFvsR' hq
    exact ⟨q₀, kJ, i, _, hqe, hi, S⟩
  · -- the groups, with the container's model NAMED (task #315 M7-2):
    -- the SAME construction, read at the reading `groupSyn` returns
    intro dsR' xFvsR' q hq ci hci
    rw [hlenS] at hq
    obtain ⟨q₀, kJ, i, ci', hci', hqe, hi, S⟩ :=
      R.groupSyn hpinsE hop hsc hpbs hPD dsR' xFvsR' hq
    obtain rfl : ci = ci' := Option.some.inj (hci.symm.trans hci')
    exact ⟨q₀, kJ, i, hqe, hi, S⟩
  · -- the copy's index count is the pin's (task #315 R3)
    intro q hq
    rw [hlenS] at hq
    rw [hget q hq]
    exact R.pinNIdx hpbs hPD hq

end Discharge

/-! ## The consumer -/

/-- **`NestedPinsStaged` modulo the ONE named fact**: the
copy-instantiation identities.  (The pins' scope and typing at the
prefix environment are K.30's conjuncts, `NestedPinsRun.scoped`; the
pin-free containers, `NestedPinsFix`, were DISCHARGED by task #315 L-C —
the assembly reads a container's own pins through its `pinLeaf` and
`pinMono`, DESIGN §U.24; the index-universe agreement, `NestedPinsU`, by
task #315 L-A — a pin's recorded universe is its container's,
DESIGN §U.22.) -/
theorem nestedPinsStaged_of {F : Nat} (hId : NestedPinsIdent V μ F) : NestedPinsStaged V μ F := by
  intro hμ env mp hE p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W
    idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁' hPM h0 h1 hfA hcA helim hcount hfresh hcont
    hb haux hstored hclosed hpinsAux hcaps hsrc hgrp hscoped hK32 hkinds hrank hK42 hK51 hK60 hK63 hK61 hK62 hK67 hK68 hK69 hpinsE hK64 hformers h hbk
    h3 hnd hctorsA hleafM' hoff' hfind' hctors
  have R : NestedPinsRun V μ F mp p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀ ctorsA sortss kinds
      mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁' :=
    ⟨hμ, hE, hPM, h0, h1, hfA, hcA, helim, hcount, hfresh, hcont, hb, haux, hstored, hclosed, hpinsAux,
      hcaps, hsrc, hgrp, hscoped, hK32, hkinds, hrank, hK42, hK51, hK60, hK63, hK61, hK62, hK67, hK68, hK69, hpinsE, hK64, hformers, h, hbk, h3, hnd, hctorsA,
      hleafM',
      hoff', hfind', hctors⟩
  obtain ⟨hpinsE, fvs, o, hop, hsc⟩ := R.scoped
  obtain ⟨pbs, hpbs, hPD⟩ := R.pinData
  have SF := R.synFacts hpinsE hop hsc
  refine ⟨_, SF.pinsLen, SF.pinRec, SF.pinDs, SF.pinWd, ?_, ?_, ?_, ?_, ?_⟩
  · -- pinψ: the level assignment at the prefix environment's record
    intro q hq cvT caps hfind
    rw [pinsOf_length] at hq
    rw [pinsOf_getD _ _ _ _ _ _ hq] at hfind ⊢
    exact R.pinψ hPD hq cvT caps hfind
  · -- pinNP: the pin's parameter count is its container's (task #315
    -- M7-3 session 11): the group's own `pinNP` against the block
    -- model that `modeled` says represents the container's group —
    -- both `NestedPinGroupSyn`'s, which `ofParts` drops
    intro q hq ci hci
    obtain ⟨q₀, kJ, i, dJ, hqe, hi, S⟩ :=
      SF.groups (fun _ _ _ => []) (fun _ _ => []) q hq
    subst hqe
    exact (S.pinNP i hi).trans (S.modeled i hi ci hci).nP
  · -- pinNIdx: the copy's index count
    intro q hq
    rw [pinsOf_length] at hq
    rw [pinsOf_getD _ _ _ _ _ _ hq]
    exact R.pinNIdx hpbs hPD hq
  -- the groups, and the groups KEYED by the pin's container's reading
  -- (task #315 M7-3 session 12): ONE construction, `groupSyn`'s, read
  -- twice — the keyed form is the one `ContainerModeled`'s consumers
  -- need (the container's block model NAMED as the environment
  -- model's own assignment at its reading), the existential form the
  -- one the loop and the reading law read
  · intro dsR' xFvsR' q hq
    obtain ⟨q₀, kJ, i, dJ, hqe, hi, S⟩ := SF.groups dsR' xFvsR' q hq
    refine ⟨q₀, kJ, i, dJ, hqe, hi, S.ofParts ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · exact (hId mp p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W
        idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁' R _ SF dsR' xFvsR' q₀ kJ dJ S).1
    · exact (hId mp p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W
        idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁' R _ SF dsR' xFvsR' q₀ kJ dJ S).2.1
    · exact (hId mp p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W
        idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁' R _ SF dsR' xFvsR' q₀ kJ dJ S).2.2.1
    · exact (hId mp p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W
        idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁' R _ SF dsR' xFvsR' q₀ kJ dJ S).2.2.2.1
    · exact (hId mp p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W
        idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁' R _ SF dsR' xFvsR' q₀ kJ dJ S).2.2.2.2.1
    · exact (hId mp p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W
        idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁' R _ SF dsR' xFvsR' q₀ kJ dJ S).2.2.2.2.2
  intro dsR' xFvsR' q hq ci hci
  rw [pinsOf_length] at hq
  obtain ⟨q₀, kJ, i, ci', hci', hqe, hi, S⟩ := R.groupSyn hpinsE hop hsc hpbs hPD dsR' xFvsR' hq
  obtain rfl : ci = ci' := Option.some.inj (hci.symm.trans hci')
  refine ⟨q₀, kJ, i, hqe, hi, S.ofParts ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (hId mp p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W
      idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁' R _ SF dsR' xFvsR' q₀ kJ _ S).1
  · exact (hId mp p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W
      idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁' R _ SF dsR' xFvsR' q₀ kJ _ S).2.1
  · exact (hId mp p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W
      idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁' R _ SF dsR' xFvsR' q₀ kJ _ S).2.2.1
  · exact (hId mp p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W
      idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁' R _ SF dsR' xFvsR' q₀ kJ _ S).2.2.2.1
  · exact (hId mp p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W
      idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁' R _ SF dsR' xFvsR' q₀ kJ _ S).2.2.2.2.1
  · exact (hId mp p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W
      idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁' R _ SF dsR' xFvsR' q₀ kJ _ S).2.2.2.2.2

end ConLeche.Model

