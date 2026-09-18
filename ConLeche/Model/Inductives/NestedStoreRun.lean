module

public import ConLeche.Model.Inductives.NestedRecRule
public import ConLeche.Verify.Inductives.NestedRecsWF
import ConLeche.Model.Inductives.NestedRecsSwap
import ConLeche.Model.Swap
import ConLeche.Model.Inductives.BlockStageTable
import ConLeche.Model.Inductives.MutualNoProj
import ConLeche.Verify.Inductives.NestedAuxFormers
import ConLeche.Verify.Inductives.ContainerFrame
public import ConLeche.Model.Inductives.NestedTables
import ConLeche.Verify.Inductives.NestedRecDoor
import ConLeche.Verify.Inductives.NestedRecNames
import ConLeche.Verify.Inductives.NestedRestoreKit
import ConLeche.Verify.Inductives.NestedElimInv
import ConLeche.Verify.Inductives.NestedRecRuleKit
import ConLeche.Verify.Inductives.NestedAuxInv
import ConLeche.Verify.Inductives.NestedTablesInv
import ConLeche.Verify.Inductives.StructWF
public section

/-!
# The restored recursors' STORE, at the run (task #315, M7-2, item 5 step 3b)

`nestedRecsStore` (`NestedRecsSwap.lean`) is generic in the list of
quadruples the kernel conses; this file is that list AT THE RUN — the
one `checkNested` builds — with the swap's per-entry premises read off
the run's own reports.

Three things happen here, and then the stage they are for:

* `nestedStoreList` names the list (`NestedTailIn.htbl`'s), and
  `nestedProvOf_nestedStoreList` says its projection IS the provision
  list `nestedProvList` the rules were scoped at — the ONE fact that
  ties `storeNestedRecs` to `provisionNestedRecs` at the run, and a
  `zip`/`take`/`drop` argument the swap itself was deliberately kept
  free of;
* `nestedStoreList_mem` describes an entry: it is class `c`'s restored
  recursor, its arities and its restored rules;
* `NestedTailIn.storeTys`/`storeRules` are the swap's two per-entry
  premises, off `NestedTailIn.recCvDoor` and `restoreRules_at`
  respectively — with the `.nested` fire's shape off
  `nestedFireShape_inv`, which is `ConstWF`'s nested clause conjunct
  for conjunct.

Above them sit the stage and the two faces stated over it: the
recursors' stage itself (`nestedRecsStored_of`, `NestedRecsStored`),
the `NoProjEnv` bookkeeping the projection tables ask for
(`NestedTailIn.storeNoProj`, whose rule clause covers the `.nested`
fire's PINS — the one place a nested block's store is not the mutual
route's), and the recorded tables' data
(`NestedTailIn.tablesData`/`nestedTablesData_of`: the scratch
install's own table, its guards carried across the restore, and
`tableMember_of`'s bundle at the nested block model).  K.50's record
`NestedRuleBitsOf` is the stage's one remaining premise here.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecFieldKind RecRule
  NestedParts MutualBlock AuxStored ElimState NestedPin IndCaps ContainerInfo ProjTable fueledOps)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

/-! ## Kit: the two zips -/

/-- A doubly zipped list's left projection drops the third component,
when the third list is long enough for the `zip` not to truncate. -/
theorem zip_zip_map {α β γ δ : Type} (f : β → δ) :
    ∀ (l₁ : List α) (l₂ : List β) (l₃ : List γ), l₂.length ≤ l₃.length →
      (l₁.zip (l₂.zip l₃)).map (fun x => (x.1, f x.2.1)) = l₁.zip (l₂.map f)
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | _ :: _, _ :: _, [], h => by simp at h
  | a :: l₁, x :: l₂, y :: l₃, h => by
    rw [List.zip_cons_cons, List.zip_cons_cons, List.map_cons, List.map_cons,
      List.zip_cons_cons, zip_zip_map f l₁ l₂ l₃ (by simpa using h)]

/-- An entry of a doubly zipped list carries the three lists' entries
at one index. -/
theorem zip_zip_getElem? {α β γ : Type} :
    ∀ (l₁ : List α) (l₂ : List β) (l₃ : List γ) (i : Nat) (x : α × β × γ),
      (l₁.zip (l₂.zip l₃))[i]? = some x →
      l₁[i]? = some x.1 ∧ l₂[i]? = some x.2.1 ∧ l₃[i]? = some x.2.2
  | [], _, _, _, _, h => by simp [List.zip] at h
  | _ :: _, [], _, _, _, h => by simp [List.zip] at h
  | _ :: _, _ :: _, [], _, _, h => by simp [List.zip] at h
  | _ :: _, _ :: _, _ :: _, 0, _, h => by
    simp only [List.zip_cons_cons, List.getElem?_cons_zero, Option.some.injEq] at h
    rw [← h]
    exact ⟨rfl, rfl, rfl⟩
  | _ :: l₁, _ :: l₂, _ :: l₃, i + 1, x, h => by
    simp only [List.zip_cons_cons, List.getElem?_cons_succ] at h
    exact zip_zip_getElem? l₁ l₂ l₃ i x h

/-! ## The swap at a NAMED provision list -/

/-- **`nestedRecsStore` at a provision list the caller NAMES**: the
swap is stated at `nestedProvOf l`, the projection of its own
quadruples, while the run's provision is `nestedProvList` — the list
the restored rules were actually scoped at.  The two are equal
(`nestedProvOf_nestedStoreList`), but the equality sits under
`EnvModelM`'s index, so it has to be spent before the model is built,
not after.  This wrapper is that `subst`, and nothing else. -/
theorem nestedRecsStore_at {env₂ : Env} {l : List (ConstantVal × Nat × Nat × List RecRule)}
    {prov : List (ConstantVal × Nat × Nat)} (hprov : ConLeche.nestedProvOf l = prov)
    (henv₂ : ConLeche.EnvWF env₂)
    (mpP : EnvModelM V μ (ConLeche.provisionNestedRecs prov env₂))
    (hfresh : ∀ x ∈ l, env₂.find? x.1.name = none)
    (hnres : ∀ x ∈ l, ConLeche.reservedBasisNames.contains x.1.name = false)
    (htys : ∀ x ∈ l, x.1.type.hasFvar = false ∧
      x.1.type.allLevelParamsDefined x.1.levelParams = true ∧
      x.1.type.constsResolve env₂ = true ∧ x.1.type.looseBVarsBounded 0 = true)
    (hrulesWF : ∀ x ∈ l, ∀ r ∈ x.2.2.2,
      (RecRule.rhs r).hasFvar = false ∧
      (RecRule.rhs r).allLevelParamsDefined x.1.levelParams = true ∧
      (RecRule.rhs r).constsResolve (ConLeche.provisionNestedRecs prov env₂) = true ∧
      (RecRule.rhs r).looseBVarsBounded 0 = true ∧
      ∀ lvls pins, RecRule.fire r = .nested lvls pins →
        x.2.2.1 ≤ x.2.1 ∧
        (∀ u ∈ lvls, u.allParamsDefined x.1.levelParams = true) ∧
        (∀ pin ∈ pins, pin.hasFvar = false ∧
          pin.allLevelParamsDefined x.1.levelParams = true ∧
          pin.constsResolve (ConLeche.provisionNestedRecs prov env₂) = true ∧
          pin.looseBVarsBounded x.2.2.1 = true) ∧
        ∃ pre dom body bm D,
          x.1.type.stripPis x.2.1 = some (pre, .forallE dom body bm) ∧
          dom.getAppFn = .const D lvls ∧
          dom.getAppArgs =
            pins.map (Expr.liftLooseBVars (x.2.1 - x.2.2.1) 0) ++
              (List.range (x.2.1 - x.2.2.1)).map
                (fun i => Expr.bvar (x.2.1 - x.2.2.1 - 1 - i)))
    (hctorStored : ∀ x ∈ l, ∀ r ∈ x.2.2.2,
      (∃ cvj cnP cnF, (ConLeche.provisionNestedRecs prov env₂).find?
        (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF)) ∧
      (r.k = true → ConLeche.recRuleKOf
        (ConLeche.provisionNestedRecs prov env₂).find? r.ctor = true) ∧
      (r.eta = true → ConLeche.recRuleEtaOf
        (ConLeche.provisionNestedRecs prov env₂).find? x.1.name r.ctor = true))
    (hlaws : ∀ m₃ : EnvModel V (ConLeche.storeNestedRecs l env₂),
      m₃.acval = mpP.base2.acval → ∀ φ : Name → Nat, ∀ x ∈ l, ∀ rl ∈ x.2.2.2,
        RecRule.fire rl ≠ .inert →
        RecRuleLaw m₃ φ x.1.name x.1 x.2.1 x.2.2.1 rl) :
    ∃ mp₃ : EnvModelM V μ (ConLeche.storeNestedRecs l env₂),
      mp₃.base2.acval = mpP.base2.acval ∧ mp₃.base2.cvalE = mpP.base2.cvalE := by
  subst hprov
  exact nestedRecsStore henv₂ mpP hfresh hnres htys hrulesWF hctorStored hlaws

/-! ## `NoProjEnv` across the nested install's conses

The projection-table face asks for `NoProjEnv` at the environment the
recursors' store leaves, at every member's every slot
(`BlockTableMember.nproj`).  These are the mutual route's three cons
lemmas (`MutualNoProj.lean`) at the nested install's own three
conses — with ONE difference, and it is the whole reason the recursors'
step is not a copy: a nested block's stored rules FIRE `.nested`, so
`NoProjEnv`'s rule clause asks for the fire's PINS as well as the
right-hand side.
-/

/-- An empty projection slot survives the restored members' conses. -/
theorem findProj?_none_consNestedFormers {T : Name} {i : Nat} :
    ∀ {as : List AuxStored} {env₀ : Env}, env₀.findProj? T i = none →
      (ConLeche.consNestedFormers as env₀).findProj? T i = none
  | [], _, h => h
  | _ :: _, _, h => by
    simp only [ConLeche.consNestedFormers]
    exact findProj?_none_consNestedFormers
      (findProj?_none_cons (fun _ hh => ConstantInfo.noConfusion hh) h)

/-- An empty projection slot survives the restored constructors' conses. -/
theorem findProj?_none_consNestedCtors {T : Name} {i : Nat} :
    ∀ {cs : List (ConstantVal × Nat × Nat)} {env₀ : Env}, env₀.findProj? T i = none →
      (ConLeche.consNestedCtors cs env₀).findProj? T i = none
  | [], _, h => h
  | (_, _, _) :: _, _, h => by
    simp only [ConLeche.consNestedCtors]
    exact findProj?_none_consNestedCtors
      (findProj?_none_cons (fun _ hh => ConstantInfo.noConfusion hh) h)

/-- An empty projection slot survives the rule-less provision. -/
theorem findProj?_none_provisionNestedRecs {T : Name} {i : Nat} :
    ∀ {l : List (ConstantVal × Nat × Nat)} {env₀ : Env}, env₀.findProj? T i = none →
      (ConLeche.provisionNestedRecs l env₀).findProj? T i = none
  | [], _, h => h
  | (_, _, _) :: _, _, h => by
    simp only [ConLeche.provisionNestedRecs]
    exact findProj?_none_provisionNestedRecs
      (findProj?_none_cons (fun _ hh => ConstantInfo.noConfusion hh) h)

/-- An empty projection slot survives the recursors' store. -/
theorem findProj?_none_storeNestedRecs {T : Name} {i : Nat} :
    ∀ {l : List (ConstantVal × Nat × Nat × List RecRule)} {env₀ : Env},
      env₀.findProj? T i = none →
      (ConLeche.storeNestedRecs l env₀).findProj? T i = none
  | [], _, h => h
  | (_, _, _, _) :: _, _, h => by
    simp only [ConLeche.storeNestedRecs]
    exact findProj?_none_storeNestedRecs
      (findProj?_none_cons (fun _ hh => ConstantInfo.noConfusion hh) h)

/-- `NoProjEnv` across the restored members' conses. -/
theorem noProjEnv_consNestedFormers {T : Name} {i : Nat} :
    ∀ {as : List AuxStored} {env₀ : Env}, NoProjEnv env₀ T i →
      (∀ a ∈ as, Expr.NoProjAt T i a.cvTa.type) →
      NoProjEnv (ConLeche.consNestedFormers as env₀) T i
  | [], _, h, _ => h
  | a :: rest, env₀, h, hall => by
    simp only [ConLeche.consNestedFormers]
    refine noProjEnv_consNestedFormers (h.cons (c₀ := .indInfo a.cvTa a.caps)
      (NoProjHead.ofType (hall a List.mem_cons_self) (fun _ _ _ hh => nomatch hh)
        (fun _ _ _ _ hh => nomatch hh) (fun _ hh => nomatch hh)))
      (fun a' ha' => hall a' (List.mem_cons_of_mem _ ha'))

/-- `NoProjEnv` across the restored constructors' conses. -/
theorem noProjEnv_consNestedCtors {T : Name} {i : Nat} :
    ∀ {cs : List (ConstantVal × Nat × Nat)} {env₀ : Env}, NoProjEnv env₀ T i →
      (∀ c ∈ cs, Expr.NoProjAt T i c.1.type) →
      NoProjEnv (ConLeche.consNestedCtors cs env₀) T i
  | [], _, h, _ => h
  | (cv, nP, nF) :: rest, env₀, h, hall => by
    simp only [ConLeche.consNestedCtors]
    refine noProjEnv_consNestedCtors (h.cons (c₀ := .ctorInfo cv nP nF)
      (NoProjHead.ofType (hall (cv, nP, nF) List.mem_cons_self) (fun _ _ _ hh => nomatch hh)
        (fun _ _ _ _ hh => nomatch hh) (fun _ hh => nomatch hh)))
      (fun c' hc' => hall c' (List.mem_cons_of_mem _ hc'))

/-- `NoProjEnv` across the restored recursors' store: the type, every
rule's right-hand side, and — the nested route's own clause — every
`.nested` fire's PINS. -/
theorem noProjEnv_storeNestedRecs {T : Name} {i : Nat} :
    ∀ {l : List (ConstantVal × Nat × Nat × List RecRule)} {env₀ : Env}, NoProjEnv env₀ T i →
      (∀ x ∈ l, Expr.NoProjAt T i x.1.type ∧
        ∀ r ∈ x.2.2.2, Expr.NoProjAt T i (RecRule.rhs r) ∧
          ∀ lvls pins, RecRule.fire r = .nested lvls pins →
            ∀ pin ∈ pins, Expr.NoProjAt T i pin) →
      NoProjEnv (ConLeche.storeNestedRecs l env₀) T i
  | [], _, h, _ => h
  | (cv, mI, rP, rules) :: rest, env₀, h, hall => by
    simp only [ConLeche.storeNestedRecs]
    refine noProjEnv_storeNestedRecs (h.cons (c₀ := .recInfo cv mI rP rules)
      ⟨(hall _ List.mem_cons_self).1, (fun _ _ _ hh => nomatch hh), ?_,
        (fun _ hh => nomatch hh)⟩)
      (fun x hx => hall x (List.mem_cons_of_mem _ hx))
    intro cv' mI' rP' rules' heq r hr
    injection heq with _ _ _ hrules
    rw [← hrules] at hr
    exact (hall _ List.mem_cons_self).2 r hr

/-! ## The store list at the run -/

section Run

variable {env : Env} {F : Nat} {mp : EnvModelM V μ env} {p : NestedParts} {envOut : Env}
  {st : ElimState} {b : MutualBlock} {envAux : Env} {stored : List AuxStored}
  {ctorsR : List (List (ConstantVal × Nat × Nat))} {cvRms cvRns : List ConstantVal}
  {rulesM rulesN : List (List RecRule)} {fmsA ctorsA₀ : List ConstantVal}
  {fms : List MutualFormerA} {f₀ : MutualFormerA} {ctorsA : List (ConstantVal × Nat)}
  {sortss : List (List Level)} {kinds : List (List (RecFieldKind × Nat))}
  {mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env)}
  {ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {W : (Name → Nat) → Nat}
  {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
  {fvsPF xFvsF : Nat → List Expr} {xrestF : Nat → Expr}
  {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
  {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
  {dsR : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {xFvsR : Nat → Nat → List Expr}
  {pinsS : List PinSyn}
  {mp₂ : EnvModelM V μ (ConLeche.consNestedCtors ctorsR.flatten
    (ConLeche.consMutualFormers (fms.take p.k) env))}

local notation "ENV2" => (ConLeche.consNestedCtors ctorsR.flatten
  (ConLeche.consMutualFormers (fms.take p.k) env))

local notation "DB" => (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
  srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS)

variable (I : NestedTailIn F mp p envOut st b envAux stored ctorsR cvRms cvRns rulesM rulesN
  fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF eissF
  tssF dsR xFvsR pinsS mp₂)

include I

omit I in
/-- **The quadruple list the store conses** — `NestedTailIn.htbl`'s,
named: the members' restored recursors with their arities and rules,
then the mimics'. -/
@[expose] def nestedStoreList (p : NestedParts) (stored : List AuxStored)
    (cvRms cvRns : List ConstantVal) (rulesM rulesN : List (List RecRule)) :
    List (ConstantVal × Nat × Nat × List RecRule) :=
  (cvRms.zip ((stored.take p.k).zip rulesM)).map (fun (cv, a, rs) => (cv, a.mI, a.rP, rs))
    ++ (cvRns.zip ((stored.drop p.k).zip rulesN)).map (fun (cv, a, rs) => (cv, a.mI, a.rP, rs))

omit I in
/-- **THE STORE'S LIST PROJECTS TO THE PROVISION'S** — the one fact
tying `storeNestedRecs` to the `provisionNestedRecs` every restored
rule was scoped at.  Both `zip`s truncate, so it needs the rule rows to
be as many as the stored records, which the two `mapM`s give. -/
theorem nestedProvOf_nestedStoreList
    (hM : (stored.take p.k).length ≤ rulesM.length)
    (hN : (stored.drop p.k).length ≤ rulesN.length) :
    ConLeche.nestedProvOf (nestedStoreList p stored cvRms cvRns rulesM rulesN)
      = nestedProvList p stored cvRms cvRns := by
  unfold ConLeche.nestedProvOf nestedStoreList nestedProvList
  rw [List.map_append, List.map_map, List.map_map]
  congr 1
  · exact zip_zip_map (fun a : AuxStored => (a.mI, a.rP)) cvRms _ rulesM hM
  · exact zip_zip_map (fun a : AuxStored => (a.mI, a.rP)) cvRns _ rulesN hN

omit I in
/-- A `map` of a doubly zipped list, at a member. -/
theorem mem_zip_zip_map {α β γ δ : Type} (g : α × β × γ → δ) {l₁ : List α} {l₂ : List β}
    {l₃ : List γ} {y : δ} (hy : y ∈ (l₁.zip (l₂.zip l₃)).map g) :
    ∃ (i : Nat) (a : α) (x : β) (z : γ),
      l₁[i]? = some a ∧ l₂[i]? = some x ∧ l₃[i]? = some z ∧ y = g (a, x, z) := by
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
  obtain ⟨i, hi⟩ := List.getElem?_of_mem ht
  obtain ⟨h1, h2, h3⟩ := zip_zip_getElem? l₁ l₂ l₃ i t hi
  exact ⟨i, t.1, t.2.1, t.2.2, h1, h2, h3, rfl⟩

omit I in
/-- **AN ENTRY OF THE STORE'S LIST IS A CLASS**: class `c`'s restored
recursor, the auxiliary record's two arities, and the class's restored
rules (`nestedRulesAt`).  Stated over the two recursor lists' own
lengths, so it needs neither the block nor the tail. -/
theorem nestedStoreList_mem (hlenM : cvRms.length = p.k)
    {x : ConstantVal × Nat × Nat × List RecRule}
    (hx : x ∈ nestedStoreList p stored cvRms cvRns rulesM rulesN) :
    ∃ c, c < p.k + cvRns.length ∧ x.1 = nestedRecCvAt p.k cvRms cvRns c ∧
      x.2.1 = (stored.getD c default).mI ∧ x.2.2.1 = (stored.getD c default).rP ∧
      x.2.2.2 = nestedRulesAt p.k rulesM rulesN c := by
  unfold nestedStoreList at hx
  rcases List.mem_append.mp hx with hx' | hx'
  · obtain ⟨c, cv, a, rs, h1, h2, h3, rfl⟩ := mem_zip_zip_map _ hx'
    have hck : c < p.k := by
      have := (List.getElem?_eq_some_iff.mp h1).1
      rw [hlenM] at this; exact this
    have ha : stored[c]? = some a := by rw [← List.getElem?_take_of_lt hck]; exact h2
    refine ⟨c, by omega, ?_, ?_, ?_, ?_⟩
    · show cv = _
      unfold nestedRecCvAt
      rw [if_pos hck, List.getD_eq_getElem?_getD, h1]
      rfl
    · show a.mI = _
      rw [List.getD_eq_getElem?_getD, ha]
      rfl
    · show a.rP = _
      rw [List.getD_eq_getElem?_getD, ha]
      rfl
    · show rs = _
      unfold nestedRulesAt
      rw [if_pos hck, List.getD_eq_getElem?_getD, h3]
      rfl
  · obtain ⟨j, cv, a, rs, h1, h2, h3, rfl⟩ := mem_zip_zip_map _ hx'
    have hjn : j < cvRns.length := (List.getElem?_eq_some_iff.mp h1).1
    have ha : stored[p.k + j]? = some a := by rw [← List.getElem?_drop]; exact h2
    have hck : ¬ p.k + j < p.k := by omega
    refine ⟨p.k + j, by omega, ?_, ?_, ?_, ?_⟩
    · show cv = _
      unfold nestedRecCvAt
      rw [if_neg hck, show p.k + j - p.k = j from by omega,
        List.getD_eq_getElem?_getD, h1]
      rfl
    · show a.mI = _
      rw [List.getD_eq_getElem?_getD, ha]
      rfl
    · show a.rP = _
      rw [List.getD_eq_getElem?_getD, ha]
      rfl
    · show rs = _
      unfold nestedRulesAt
      rw [if_neg hck, show p.k + j - p.k = j from by omega,
        List.getD_eq_getElem?_getD, h3]
      rfl

/-! ## The swap's per-entry premises, at the run -/

/-- **THE STORE'S ENTRIES AT THE FRONT DOOR** — `nestedRecsStore`'s
`hfresh`, `hnres` and `htys` in one: every entry of the store's list is
class `c`'s restored recursor, and `NestedTailIn.recCvDoor` reports its
name free at the restored environment, neither reserved nor
projection-shaped, with its type closed, fvar-free, level-complete and
resolving there. -/
theorem NestedTailIn.storeDoor :
    ∀ x ∈ nestedStoreList p stored cvRms cvRns rulesM rulesN,
      (ENV2).find? x.1.name = none ∧
      ConLeche.reservedBasisNames.contains x.1.name = false ∧
      x.1.type.hasFvar = false ∧
      x.1.type.allLevelParamsDefined x.1.levelParams = true ∧
      x.1.type.constsResolve (ENV2) = true ∧
      x.1.type.looseBVarsBounded 0 = true := by
  intro x hx
  obtain ⟨c, hc, hcv, -, -, -⟩ := nestedStoreList_mem I.lenM hx
  have hcb : c < b.k := by rw [I.out.bk, ← I.lenN] at *; exact hc
  obtain ⟨hfr, hnres, -, hfv, hlp, hbv, hres⟩ := I.recCvDoor hcb
  rw [hcv]
  exact ⟨hfr, hnres, hfv, hlp, hres, hbv⟩

/-- **THE STORE'S RULES, AT THE PROVISION** — `nestedRecsStore`'s
`hrulesWF`: every restored rule's right-hand side is closed, fvar-free,
level-complete and resolves at the environment `restoreRules` ran at
(`restoreRules_at`), and a `.nested` fire carries exactly the shape
`nestedFireShape` certified (`nestedFireShape_inv`) — which is
`ConstWF`'s nested clause conjunct for conjunct.  Only a MIMIC fires
`.nested`; a member's fire is `.plain`-or-`.inert` and the clause is
vacuous there.

Stated at `nestedProvList` (the environment the rules were checked at);
`nestedProvOf_nestedStoreList` is the caller's one rewrite. -/
theorem NestedTailIn.storeRules :
    ∀ x ∈ nestedStoreList p stored cvRms cvRns rulesM rulesN, ∀ r ∈ x.2.2.2,
      (RecRule.rhs r).hasFvar = false ∧
      (RecRule.rhs r).allLevelParamsDefined x.1.levelParams = true ∧
      (RecRule.rhs r).constsResolve
        (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)) = true ∧
      (RecRule.rhs r).looseBVarsBounded 0 = true ∧
      ∀ lvls pins, RecRule.fire r = .nested lvls pins →
        x.2.2.1 ≤ x.2.1 ∧
        (∀ u ∈ lvls, u.allParamsDefined x.1.levelParams = true) ∧
        (∀ pin ∈ pins, pin.hasFvar = false ∧
          pin.allLevelParamsDefined x.1.levelParams = true ∧
          pin.constsResolve
            (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)) = true ∧
          pin.looseBVarsBounded x.2.2.1 = true) ∧
        ∃ pre dom body bm D,
          x.1.type.stripPis x.2.1 = some (pre, .forallE dom body bm) ∧
          dom.getAppFn = .const D lvls ∧
          dom.getAppArgs =
            pins.map (Expr.liftLooseBVars (x.2.1 - x.2.2.1) 0) ++
              (List.range (x.2.1 - x.2.2.1)).map
                (fun i => Expr.bvar (x.2.1 - x.2.2.1 - 1 - i)) := by
  intro x hx r hr
  obtain ⟨c, hc, hcv, hmI, hrP, hrs⟩ := nestedStoreList_mem I.lenM hx
  have hcb : c < b.k := by rw [I.out.bk, ← I.lenN] at *; exact hc
  obtain ⟨a, ha⟩ : ∃ a, stored[c]? = some a :=
    ⟨_, List.getElem?_eq_getElem (by rw [I.storedLen]; exact hcb)⟩
  have haD : stored.getD c default = a := by rw [List.getD_eq_getElem?_getD, ha]; rfl
  rw [haD] at hmI hrP
  obtain ⟨hlenR, hallR⟩ := ConLeche.restoreRules_at (I.restRulesRun hcb ha)
  rw [hrs] at hr
  obtain ⟨ii, hoAt⟩ := List.getElem?_of_mem hr
  obtain ⟨rl, hrlAt⟩ : ∃ rl, a.rules[ii]? = some rl :=
    ⟨_, List.getElem?_eq_getElem (by
      rw [← hlenR]; exact (List.getElem?_eq_some_iff.mp hoAt).1)⟩
  obtain ⟨-, hlps, hres, hbv, hfv, -, -, -, -, -, hMem, hMim⟩ := hallR ii rl r hrlAt hoAt
  refine ⟨hfv, by rw [hcv]; exact hlps, hres, hbv, ?_⟩
  intro lvls pins hfire
  by_cases hck : p.k ≤ c
  · -- a MIMIC: the fire IS `nestedFireShape`, and its inversion is the clause
    obtain ⟨-, hfireN⟩ := hMim (by simp only [decide_eq_true_eq]; exact hck)
    rcases hsh : ConLeche.nestedFireShape
        (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2))
        (nestedRecCvAt p.k cvRms cvRns c).levelParams
        (nestedRecCvAt p.k cvRms cvRns c).type a.mI a.rP (RecRule.ctorParams r) with _ | lp
    · rw [hsh] at hfireN; rw [hfireN] at hfire; exact nomatch hfire
    · rw [hsh] at hfireN
      rw [hfireN] at hfire
      obtain ⟨rfl, rfl⟩ : lvls = lp.1 ∧ pins = lp.2 := by
        injection hfire with h1 h2
        exact ⟨h1.symm, h2.symm⟩
      obtain ⟨hle, pre, dom, body, bm, Dn, hstrip, hhead, -, -, hlift, hdrop, hpins, hlvls⟩ :=
        ConLeche.nestedFireShape_inv (by rw [hsh])
      rw [hcv, hmI, hrP]
      refine ⟨hle, hlvls, fun pin hpin => ?_, pre, dom, body, bm, Dn, hstrip, hhead, ?_⟩
      · obtain ⟨p1, p2, p3, p4⟩ := hpins pin hpin
        exact ⟨p1, p4, p3, p2⟩
      · rw [← hlift, ← hdrop, List.take_append_drop]
  · -- a MEMBER: the fire is `.plain` or `.inert`, never `.nested`
    obtain ⟨-, hfireP⟩ := hMem (by simp only [decide_eq_false_iff_not]; exact hck)
    rw [hfireP] at hfire
    split at hfire <;> exact nomatch hfire

/-- **THE STORE'S RULES' CONSTRUCTORS, AND THEIR RESCUE BITS** —
`nestedRecsStore`'s `hctorStored`.  The first conjunct is
`restoreRules_at`'s verbatim: a restored rule whose constructor is not
stored at the provision is INVALID (task #279 K.24), so the lookup is
the run's own verdict.

The other two are **K.50's**, taken here in the shape its inversion
will have (DESIGN §U.29 (gggg)): `restoreRules` copies `k` and `eta`
from the SCRATCH rule while RENAMING the constructor, so what
`mutualRules_bits` says about the scratch rule at `envAux` and what
`ConstWF` asks of the stored rule at the provision differ in BOTH
arguments, and no lemma in the tree relates them across the copies'
capability records.

**K.50 records the two conjuncts THEMSELVES**, at the provisioned
environment where `ConstWF` asks for them — not the bits `false`.
Recording the bits `false` would DECLINE 35 of the 41 Mathlib cone
blocks and 7 of the 27 shadow fixtures: η is about a structure's single
constructor and its recursor not being a projection function, not about
field counts, and a copy of a structure-like container is
structure-like.  The K half is vacuous on both corpora today (dropping
`!r.k` fails 24/27 and 41/41) and is recorded anyway, nothing making it
so in principle.  So this hypothesis passes straight through to the
kernel's own record. -/
theorem NestedTailIn.storeCtors
    (hbits : ∀ c, c < b.k → ∀ r ∈ nestedRulesAt p.k rulesM rulesN c,
      (RecRule.k r = true → ConLeche.recRuleKOf
        (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)).find?
        (RecRule.ctor r) = true) ∧
      (RecRule.eta r = true → ConLeche.recRuleEtaOf
        (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)).find?
        (nestedRecCvAt p.k cvRms cvRns c).name (RecRule.ctor r) = true)) :
    ∀ x ∈ nestedStoreList p stored cvRms cvRns rulesM rulesN, ∀ r ∈ x.2.2.2,
      (∃ cvj cnP cnF,
        (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)).find?
          (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF)) ∧
      (RecRule.k r = true → ConLeche.recRuleKOf
        (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)).find?
        (RecRule.ctor r) = true) ∧
      (RecRule.eta r = true → ConLeche.recRuleEtaOf
        (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)).find?
        x.1.name (RecRule.ctor r) = true) := by
  intro x hx r hr
  obtain ⟨c, hc, hcv, -, -, hrs⟩ := nestedStoreList_mem I.lenM hx
  have hcb : c < b.k := by rw [I.out.bk, ← I.lenN] at *; exact hc
  obtain ⟨a, ha⟩ : ∃ a, stored[c]? = some a :=
    ⟨_, List.getElem?_eq_getElem (by rw [I.storedLen]; exact hcb)⟩
  obtain ⟨hlenR, hallR⟩ := ConLeche.restoreRules_at (I.restRulesRun hcb ha)
  rw [hrs] at hr
  obtain ⟨hk0, he0⟩ := hbits c hcb r hr
  obtain ⟨ii, hoAt⟩ := List.getElem?_of_mem hr
  obtain ⟨rl, hrlAt⟩ : ∃ rl, a.rules[ii]? = some rl :=
    ⟨_, List.getElem?_eq_getElem (by
      rw [← hlenR]; exact (List.getElem?_eq_some_iff.mp hoAt).1)⟩
  obtain ⟨-, -, -, -, -, -, -, hfindC, -, -, -, -⟩ := hallR ii rl r hrlAt hoAt
  obtain ⟨cvj, cnF, hfc⟩ := hfindC
  exact ⟨⟨cvj, RecRule.ctorParams r, cnF, hfc⟩, hk0, by rw [hcv]; exact he0⟩

/-! ## The restored field domains, against the auxiliary ones -/

/-- **THE RESTORED AND THE AUXILIARY FIELD DOMAINS READ ALIKE AT THE
TAIL** — `nestedDomAgree_of` (`NestedCore.lean`) at the restored
constructors' model.  Its six data are the tail's own: the restored
domains' LENGTH, their parameter prefix and their plain positions come
from `NestedStageFacts.domFacts`, their grading and their NESTED
positions' shape off the block model's own constructor record
(`BlockCtorData` at `(DB).dsF mm j = dsR mm j`, which
`NestedCoreOut.reps` publishes).

This is what carries the constructor stage's FIELD facts — the
grading, the bounds and the field sorts' universes — across the
restore, and so what the projection tables' `MutualTableFacts` at the
nested block model rests on. -/
theorem NestedTailIn.domAgree {mm j : Nat} (hmm : mm < p.k)
    {c : ConstantVal × Nat × Nat} (hc : (ctorsR.getD mm [])[j]? = some c)
    {cA : ConstantVal × Nat} (hJ : ctorsA[b.ownOffset mm + j]? = some cA)
    (hnF : c.2.2 = cA.2) (hmemJ : mutMemF b (b.ownOffset mm + j) = mm) :
    ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((dsF (b.ownOffset mm + j) ψ).take b.nP).map (·.2.2)).reverse ρ →
      ∀ l, l < cA.2 → ∀ fs₁ : List V, fs₁.length = l →
        SpineFit ρ ((((dsF (b.ownOffset mm + j) ψ).drop b.nP).map (·.2.2)).take l) fs₁ →
        SpineFit ρ ((((dsR mm j ψ).drop b.nP).map (·.2.2)).take l) fs₁ →
        interp V (consList fs₁ ρ) ((dsF (b.ownOffset mm + j) ψ).getD (b.nP + l) default).2.2
          = interp V (consList fs₁ ρ) ((dsR mm j ψ).getD (b.nP + l) default).2.2 := by
  have hjl : j < (ctorsR.getD mm []).length := (List.getElem?_eq_some_iff.mp hc).1
  have hdom := I.out.stage.domFacts
  have hcM : ((DB).ctorsM mm)[j]? = some (c.1, c.2.2) := by
    change ((ctorsR.getD mm []).map fun c => (c.1, c.2.2))[j]? = _
    rw [List.getElem?_map, hc]
    rfl
  obtain ⟨cvR, mI, rP, rules, hI⟩ := I.out.reps mm hmm
  obtain ⟨-, -, hCD⟩ := hI.ctors mm j _ hmm hcM
  have hnFl : ∀ l, l < cA.2 → l < c.2.2 := fun l hl => by rw [hnF]; exact hl
  refine nestedDomAgree_of I.hμ I.out.facts I.out.grouped I.out.bk mp₂.base2
    I.out.stage.groups hJ hmemJ (fun ψ => ?_)
    (R := fun ψ => ctorBodyAVI mp₂.base2 ((DB).memberName mm) (DB).nP c.2.2 ψ
      ((DB).esF mm j ψ))
    (fun ψ ρ => (hCD.okTy ψ ρ).1) (fun ψ => (hdom mm j ψ hmm hjl).2.1)
    (fun ψ l _ hpl => (hdom mm j ψ hmm hjl).2.2 l hpl)
    (fun ψ l q hl hq hk => ⟨hCD.nestEntry ψ l q hq hk (hnFl l hl),
      hCD.nestEisLen ψ l q hq hk (hnFl l hl)⟩)
    (fun ψ l q hl hq hk => ⟨hCD.nestReflEntry ψ l q hq hk (hnFl l hl),
      hCD.nestEisLenRefl ψ l q hq hk (hnFl l hl)⟩)
  rw [(hdom mm j ψ hmm hjl).1]
  exact (I.out.facts.CD _ _ hJ).len ψ

/-! ## The nested block model's table facts -/

/-- A constructor position of a member is the auxiliary block's, at the
member's own offset (`ownCtors`' grouping), so the block's constructor
table sends it back to that member. -/
theorem NestedTailIn.memF {mm : Nat} (hmm : mm < p.k) {j : Nat}
    (hj : j < (ctorsR.getD mm []).length) : mutMemF b (b.ownOffset mm + j) = mm := by
  have hjo : j < (b.ownCtors mm).length := by
    rw [← I.out.stage.ctorsLen mm hmm]; exact hj
  obtain ⟨q, hq⟩ : ∃ q, (b.ownCtors mm)[j]? = some q := ⟨_, List.getElem?_eq_getElem hjo⟩
  obtain ⟨J, ct⟩ := q
  obtain ⟨hcJ, hmemc⟩ := ConLeche.ownCtors_getElem?_ctors hq
  have hJ : J = b.ownOffset mm + j := ConLeche.ownCtors_getElem?_idx I.out.grouped hq
  show (b.ctors.getD (b.ownOffset mm + j) default).member = mm
  rw [← hJ, List.getD_eq_getElem?_getD, hcJ]
  exact hmemc

/-- **THE NESTED BLOCK MODEL'S TABLE FACTS** (task #315 M7-2) —
`MutualTableFacts` (`DeclBlock.lean`) at the nested run's data, which
is what `tableMember_of` reads of a structure-like member beyond the
block model itself.  The three fields come from three different
places:

* `inj` is `rfl`: `BlockModel.ofNested`'s injection IS the tagged tower
  at the MEMBER-LOCAL position;
* `frame` is `MutualFormersFacts.frame` verbatim — the nested block
  model's members are the scratch block's first `p.k`, with the same
  parameter readings `ppsF`, so the cross-member identification is the
  scratch one;
* `sorts` is the real content, because it is about the RESTORED field
  domains `dsR`.  The field SORTS are the scratch constructor stage's
  (`sortsJ`) and so are the grading, the bounds and the sorts'
  universes (`framesJ`) — all stated at the AUXILIARY domains `dsF`.
  `NestedTailIn.domAgree` carries each of them across the restore:
  the parameter prefix is literally equal (`domFacts`), so the frame
  transfers, and the field entries read alike, so the universes do
  (`fieldsOkB_of_agree`, `fieldsBound_of_agree`).  The restored list's
  own `WellDenoted`/`AnnotValid` halves — which no agreement can give
  — come from its Π-tower's truthfulness, the block model's
  constructor record (`CtorDataI.okTy`). -/
theorem NestedTailIn.tableFacts : MutualTableFacts b fms sortss (DB) where
  inj _ _ _ _ := rfl
  frame t ht ψ ρ := by
    have ht' : t < p.k := ht
    have htl : t < fms.length := by
      rw [I.out.facts.lenFms, I.out.bk]; omega
    exact I.out.facts.frame t _ (List.getElem?_eq_getElem htl) ψ ρ
  sorts mm j cA hmm hj := by
    -- the restored constructor at that position, and the auxiliary one
    obtain ⟨c, hc, hcaEq⟩ : ∃ c, (ctorsR.getD mm [])[j]? = some c ∧ cA = (c.1, c.2.2) := by
      have hm : ((ctorsR.getD mm []).map fun cc => (cc.1, cc.2.2))[j]? = some cA := hj
      rw [List.getElem?_map] at hm
      cases hcc : (ctorsR.getD mm [])[j]? with
      | none => rw [hcc] at hm; exact nomatch hm
      | some c' => exact ⟨c', rfl, by rw [hcc] at hm; exact (Option.some.inj hm).symm⟩
    subst hcaEq
    have hjl : j < (ctorsR.getD mm []).length := (List.getElem?_eq_some_iff.mp hc).1
    obtain ⟨cAx, hJ, hnF, -, -, -⟩ := I.out.stage.ctorFacts mm j c hmm hc
    have hmemJ : mutMemF b (b.ownOffset mm + j) = mm := I.memF hmm hjl
    have hJl : b.ownOffset mm + j < ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
    have hmtl : mutMemF b (b.ownOffset mm + j) < fms.length := I.out.facts.motLt _ hJl
    have hmtG : fms[mutMemF b (b.ownOffset mm + j)]?
        = some (fms.getD (mutMemF b (b.ownOffset mm + j)) default) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hmtl]; rfl
    obtain ⟨sorts, hss, hlenS, hleqS, hmemS⟩ := I.out.facts.sortsJ I.hμ hJ
    -- the restored constructor's record at the block model
    have hcM : ((DB).ctorsM mm)[j]? = some (c.1, c.2.2) := hj
    obtain ⟨cvR, mI, rP, rules, hIb⟩ := I.out.reps mm hmm
    obtain ⟨-, -, hCD⟩ := hIb.ctors mm j _ hmm hcM
    have hsEq : ∀ ψ : Name → Nat,
        (fms.getD (mutMemF b (b.ownOffset mm + j)) default).s.eval ψ = f₀.s.eval ψ :=
      fun ψ => I.out.facts.sEq _ _ hmtG ψ
    refine ⟨sorts, hss, by rw [hlenS]; exact hnF.symm, ?_, ?_⟩
    · intro k hk hp
      have h := hleqS k (by rw [← hnF]; exact hk) hp
      rw [hmemJ] at h
      exact h
    intro ψ ρ hsatR
    -- the lengths, and the parameter frame at the AUXILIARY domains
    have hdom := I.out.stage.domFacts mm j ψ hmm hjl
    have hlenDsA : (dsF (b.ownOffset mm + j) ψ).length = b.nP + cAx.2 :=
      (I.out.facts.CD _ _ hJ).len ψ
    have hlenDsR : (dsR mm j ψ).length = b.nP + cAx.2 := by rw [hdom.1]; exact hlenDsA
    have hsatA : Sat V (((dsF (b.ownOffset mm + j) ψ).take b.nP).map (·.2.2)).reverse ρ := by
      rw [← hdom.2.1]; exact hsatR
    have hlenA : ((((dsF (b.ownOffset mm + j) ψ).drop b.nP).map (·.2.2))).length = cAx.2 := by
      rw [List.length_map, List.length_drop, hlenDsA]; omega
    have hlenR : ((((dsR mm j ψ).drop b.nP).map (·.2.2))).length = cAx.2 := by
      rw [List.length_map, List.length_drop, hlenDsR]; omega
    -- THE AGREEMENT, in the field lists' own currency
    have hag : ∀ l, l < cAx.2 → ∀ fs : List V, fs.length = l →
        SpineFit ρ ((((dsF (b.ownOffset mm + j) ψ).drop b.nP).map (·.2.2)).take l) fs →
        SpineFit ρ ((((dsR mm j ψ).drop b.nP).map (·.2.2)).take l) fs →
        interp V (consList fs ρ)
            ((((dsF (b.ownOffset mm + j) ψ).drop b.nP).map (·.2.2)).getD l default)
          = interp V (consList fs ρ)
            ((((dsR mm j ψ).drop b.nP).map (·.2.2)).getD l default) := by
      intro l hl fs hfl h1 h2
      rw [fieldsGetD _ _ _ (by rw [hlenDsA]; omega), fieldsGetD _ _ _ (by rw [hlenDsR]; omega)]
      exact I.domAgree hmm hc hJ hnF hmemJ ψ ρ hsatA l hl fs hfl h1 h2
    -- the restored Π-tower's own truthfulness and validity
    have hlenTake : ((((dsF (b.ownOffset mm + j) ψ).take b.nP).map (·.2.2))).length = b.nP := by
      rw [List.length_map, List.length_take, hlenDsA]
      exact Nat.min_eq_left (Nat.le_add_right _ _)
    have hspP := spineFit_of_sat (Δ₀ := [])
      (Ds := ((dsF (b.ownOffset mm + j) ψ).take b.nP).map (·.2.2)) (ρ := ρ)
      (by rw [List.append_nil]; exact hsatA)
    rw [hlenTake] at hspP
    have hρ : consList ((List.range b.nP).reverse.map ρ) (fun i => ρ (i + b.nP)) = ρ :=
      consList_range_reverse b.nP ρ
    have hpfit : SpineFit (fun i => ρ (i + b.nP))
        (((dsR mm j ψ).take b.nP).map (·.2.2)) ((List.range b.nP).reverse.map ρ) := by
      rw [hdom.2.1]; exact hspP
    have hsplitR : (dsR mm j ψ).take b.nP ++ (dsR mm j ψ).drop b.nP = dsR mm j ψ :=
      List.take_append_drop _ _
    have hdsEq : (DB).dsF mm j ψ = dsR mm j ψ := rfl
    have hokW := (hCD.okTy ψ (fun i => ρ (i + b.nP))).1
    have hokV := (hCD.okTy ψ (fun i => ρ (i + b.nP))).2
    rw [hdsEq, ← hsplitR, mkPisAV_append] at hokW hokV
    have hokR0 : FieldsOkB 0 ρ (((dsR mm j ψ).drop b.nP).map (·.2.2)) := by
      have h1 := (WellDenoted_mkPisAV_inv hokW).2 _ hpfit
      rw [hρ] at h1
      exact (WellDenoted_mkPisAV_inv h1).1
    have hvR : FieldsValid ρ (((dsR mm j ψ).drop b.nP).map (·.2.2)) := by
      have h1 := (AnnotValid_mkPisAV_inv hokV).2 _ hpfit
      rw [hρ] at h1
      exact (AnnotValid_mkPisAV_inv h1).1
    -- the auxiliary domains' grading, bounds and sorts
    obtain ⟨hOkA, hVA, hBndA, -⟩ := (I.out.facts.framesJ I.hμ hJl).2 ψ ρ hsatA
    rw [hsEq ψ] at hOkA hBndA
    refine ⟨fieldsOkB_of_agree hlenA hlenR hag hOkA hokR0, hvR,
      fun hp => fieldsBound_of_agree hlenA hlenR hag (hBndA hp), fun k hk as hsp => ?_⟩
    have hkx : k < cAx.2 := by rw [← hnF]; exact hk
    have hspA := (spineFit_take_iff_agree hlenA hlenR hag k (Nat.le_of_lt hkx) as).mpr hsp
    have hlas : as.length = k := by
      have h := SpineFit.length_eq hspA
      rw [List.length_take, hlenA] at h
      omega
    show interp V (consList as ρ) ((((dsR mm j ψ).drop b.nP).map (·.2.2)).getD k default)
      ∈ˢ (univ ((sorts.getD k .zero).eval ψ) : V)
    rw [← hag k hkx as hlas hspA hsp]
    exact hmemS ψ ρ hsatA k hkx as hspA

/-! ## The recorded table's constructor -/

omit I in
/-- Two equal entries of a `Nodup` list sit at one index. -/
private theorem nodup_getElem?_idx {γ : Type} {N : List γ} (hN : N.Nodup) {i j : Nat} {x : γ}
    (hi : N[i]? = some x) (hj : N[j]? = some x) : i = j := by
  obtain ⟨hil, hix⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjl, hjx⟩ := List.getElem?_eq_some_iff.mp hj
  rcases Nat.lt_trichotomy i j with h | h | h
  · exact absurd (hix.trans hjx.symm)
      ((List.pairwise_iff_getElem (R := fun x y => x ≠ y)).mp hN i j hil hjl h)
  · exact h
  · exact absurd (hjx.trans hix.symm)
      ((List.pairwise_iff_getElem (R := fun x y => x ≠ y)).mp hN j i hjl hil h)

/-- **THE RECORDED TABLE'S CONSTRUCTOR IS THE RESTORED CONSTRUCTOR'S**
(task #315 M7-2) — the first of `NestedMemberTableOk`'s three data.

The scratch install's table stage recorded the AUXILIARY constructor's
name (`auxStored_tbl_eq`); the restore keeps every constructor's name
(`restoreCtors_names`); and the auxiliary constructor the read-back
stored at the member's own singleton position IS the constructor
stage's (`auxStored_ctor_eq`, whose name is `b.ctors`' by
`MutualFormersFacts.namesC`).  So the two names are one.

`auxStored_tbl_eq`'s left disjunct — the table stood at the PRE-BLOCK
environment already — is refuted here, as that theorem's docstring
leaves to the consumer: the nested route's own table stage found
`projTableName` free at the STORE environment
(`nestedTables_projTable_fresh`), and the pre-block environment is
below it because all three conses only ADD
(`storeNestedRecs_find?_none`, `consNestedCtors_find?_none`,
`consNestedFormers_find?_none`). -/
theorem NestedTailIn.tblCtor {mIdx : Nat} (hmIdx : mIdx < p.k) {a : AuxStored}
    (ha : stored[mIdx]? = some a) {tbl : ProjTable} (htbl : a.tbl = some tbl)
    {cvCa : ConstantVal} {nPc nFc : Nat} (hcs : ctorsR[mIdx]? = some [(cvCa, nPc, nFc)]) :
    tbl.ctor = cvCa.name := by
  -- the member names are distinct, and this member's is the read-back's
  have hndM : b.memberNames.Nodup := by
    have h0 := I.out.nodup
    unfold ConLeche.MutualBlock.blockNames at h0
    exact (List.nodup_append.mp (List.nodup_append.mp h0).1).1
  obtain ⟨cv, hfm, hdisj⟩ := ConLeche.auxStored_tbl_eq I.haux I.hstored ha htbl
  have hmemAt : b.memberNames[mIdx]? = some cv.name := by
    show (b.formers.map (·.1.name))[mIdx]? = _
    rw [List.getElem?_map, hfm]
    rfl
  have hcvName : cv.name = (p.formers.getD mIdx default).1.name := by
    rw [← I.memberNameAt hmIdx, List.getD_eq_getElem?_getD, hfm]
    rfl
  -- this member's entry of the NESTED table stage's list, and its freshness
  have hzip : ((stored.take p.k).zip ctorsR)[mIdx]? = some (a, [(cvCa, nPc, nFc)]) := by
    rw [List.zip, List.getElem?_zipWith, List.getElem?_take_of_lt hmIdx, ha, hcs]
  have hmemE : ((p.formers.getD mIdx default).1.name, a.tbl, [(cvCa, nPc, nFc)])
      ∈ (((stored.take p.k).zip ctorsR).zipIdx.map fun ((a, cs), mIdx) =>
        ((p.formers.getD mIdx default).1.name, a.tbl, cs)) :=
    List.mem_map_of_mem (List.mk_mem_zipIdx_iff_getElem?.mpr hzip)
  have hfreshEnv : env.find?
      (ConLeche.projTableName (p.formers.getD mIdx default).1.name) = none :=
    ConLeche.consNestedFormers_find?_none (ConLeche.consNestedCtors_find?_none
      (storeNestedRecs_find?_none
        (ConLeche.nestedTables_projTable_fresh I.htbl _ hmemE tbl cvCa nPc nFc htbl rfl)))
  rcases hdisj with hleft | ⟨fms', -, f, ctorsA', sortss', t, J, c, bodies, hformers', -, -,
    hft, hfname, hown, -, -, rfl⟩
  · exfalso
    have hcontra : (some (ConstantInfo.projInfo tbl) : Option ConstantInfo) = none := by
      rw [← hleft, hcvName]
      exact hfreshEnv
    exact nomatch hcontra
  -- the read-back's members are the tail's
  have hfmsEq : fms' = fms :=
    congrArg Prod.snd (Except.ok.inj (hformers'.symm.trans I.out.formers))
  subst hfmsEq
  -- the table's member is this one
  have htEq : t = mIdx := by
    refine nodup_getElem?_idx hndM ?_ hmemAt
    rw [← I.out.facts.names, List.getElem?_map, hft, Option.map_some, hfname]
  rw [htEq] at hown
  -- the member's own constructor, at its global position
  have hown0 : (b.ownCtors mIdx)[0]? = some (J, c) := by rw [hown]; rfl
  obtain ⟨hcJ, -⟩ := ConLeche.ownCtors_getElem?_ctors hown0
  have hJ : J = b.ownOffset mIdx + 0 := ConLeche.ownCtors_getElem?_idx I.out.grouped hown0
  -- the read-back's own constructor at that position
  obtain ⟨hlenA, hallA⟩ := ConLeche.auxStored_ctor_eq I.haux I.out.formers I.out.ctors
    I.out.grouped I.hstored ha
  have hlen1 : a.ctors.length = 1 := by rw [hlenA, hown]; rfl
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, a.ctors[0]? = some c₀ :=
    ⟨a.ctors[0]'(by omega), List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨cA, hcA, hc1, -, -⟩ := hallA 0 c₀ hc₀
  rw [← hJ] at hcA
  -- the restore keeps the name
  obtain ⟨hlenR, hallR⟩ := ConLeche.mapM_except_inv I.hctors
  have hslt : mIdx < stored.length := (List.getElem?_eq_some_iff.mp ha).1
  have hmmR : mIdx < (stored.take p.k).length := by
    rw [List.length_take]
    omega
  obtain ⟨a', l', ha', hl', hrun⟩ := hallR mIdx hmmR
  have haT : (stored.take p.k)[mIdx]? = some a := by
    rw [List.getElem?_take_of_lt hmIdx]; exact ha
  obtain rfl : a' = a := Option.some.inj (ha'.symm.trans haT)
  obtain rfl : l' = [(cvCa, nPc, nFc)] := Option.some.inj (hl'.symm.trans hcs)
  have hnames := ConLeche.restoreCtors_names hrun
  have hcvEq : cvCa.name = c₀.1.name := by
    have h := congrArg (fun l => l[0]?) hnames
    simp only [List.getElem?_map, hc₀] at h
    exact Option.some.inj h
  -- the constructor stage's name is the block record's
  have hcname : cA.1.name = c.cv.name := by
    have h := congrArg (fun l => l[J]?) I.out.facts.namesC
    simp only [List.getElem?_map, hcA, hcJ] at h
    exact Option.some.inj h
  show c.cv.name = cvCa.name
  rw [hcvEq, ← hcname, ← hc1]

/-! ## Kit: a zipped entry, and a `Nodup` list's index -/

omit I in
/-- A zipped list's entry carries BOTH lists' (`zip_getElem?_fst`'s
pair form). -/
theorem zip_getElem?_pair {α β : Type} :
    ∀ (l₁ : List α) (l₂ : List β) (i : Nat) (x : α × β),
      (l₁.zip l₂)[i]? = some x → l₁[i]? = some x.1 ∧ l₂[i]? = some x.2
  | [], _, _, _, h => by simp [List.zip] at h
  | _ :: _, [], _, _, h => by simp [List.zip] at h
  | _ :: _, _ :: _, 0, _, h => by
    simp only [List.zip_cons_cons, List.getElem?_cons_zero, Option.some.injEq] at h
    rw [← h]
    exact ⟨rfl, rfl⟩
  | _ :: l₁, _ :: l₂, i + 1, x, h => by
    simp only [List.zip_cons_cons, List.getElem?_cons_succ] at h
    exact zip_getElem?_pair l₁ l₂ i x h

/-! ## `NoProjEnv` at the recursors' store, at the run -/

/-- **THE STORED RULES' RIGHT-HAND SIDES MENTION ONLY STORED
PROJECTION SLOTS**: `restoreRules_at`'s `projTablesOk` conjunct, the
guard the restore checked at the environment the rules were scoped at,
as a proposition (`projSlotsOk_of_projTablesOk`, K.13). -/
theorem NestedTailIn.storeRuleSlots :
    ∀ x ∈ nestedStoreList p stored cvRms cvRns rulesM rulesN, ∀ r ∈ x.2.2.2,
      ConLeche.Expr.ProjSlotsOk
        (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2))
        (RecRule.rhs r) := by
  intro x hx r hr
  obtain ⟨c, hc, -, -, -, hrs⟩ := nestedStoreList_mem I.lenM hx
  have hcb : c < b.k := by rw [I.out.bk, ← I.lenN] at *; exact hc
  obtain ⟨a, ha⟩ : ∃ a, stored[c]? = some a :=
    ⟨_, List.getElem?_eq_getElem (by rw [I.storedLen]; exact hcb)⟩
  obtain ⟨hlenR, hallR⟩ := ConLeche.restoreRules_at (I.restRulesRun hcb ha)
  rw [hrs] at hr
  obtain ⟨ii, hoAt⟩ := List.getElem?_of_mem hr
  obtain ⟨rl, hrlAt⟩ : ∃ rl, a.rules[ii]? = some rl :=
    ⟨_, List.getElem?_eq_getElem (by
      rw [← hlenR]; exact (List.getElem?_eq_some_iff.mp hoAt).1)⟩
  obtain ⟨-, -, -, -, -, hpo, -, -, -, -, -, -⟩ := hallR ii rl r hrlAt hoAt
  exact ConLeche.Expr.projSlotsOk_of_projTablesOk _ hpo

/-- **NO STORED PIECE MENTIONS A MEMBER'S PROJECTIONS** at the
environment the restored recursors' store leaves (task #315 M7-2) —
the nested twin of `mutualNoProj`, and the last of `tableMember_of`'s
premises the nested route owed.

Four conses, four sources, and only the last is new:

* the PRE-BLOCK environment: the member is not stored there
  (`nestedMembersFresh`), so nothing stored there mentions its
  projections (`noProjEnv_of_fresh`), and its slot is empty
  (`findProj?_none_of_indFresh`);
* the restored MEMBERS: their types resolve at the pre-block
  environment (`mutualFormers_nameFacts`), where the member is fresh;
* the restored CONSTRUCTORS: their `.proj` nodes name a table stored
  at the FORMERS' environment (`restoreCtors_door`'s
  `FrontDoorFacts.slots`), where the member's own slot is still empty;
* the restored RECURSORS: the type off `recCvSlots` — the report
  `restoreRecTys_at` drops and the resolution predicate cannot
  replace — every rule's right-hand side off `storeRuleSlots`, and
  every `.nested` fire's PINS, which are the major domain's lowered
  leading arguments (`NestedTailIn.storeRules`' shape clause) and so
  inherit the type's own freedom through the telescope, the spine and
  the lift (`rg_noProjAt_stripPis`, `rg_noProjAt_getAppArgs`,
  `rg_noProjAt_of_lift`). -/
theorem NestedTailIn.storeNoProj {t : Nat} {f : MutualFormerA}
    (hft : fms[t]? = some f) (j : Nat) :
    NoProjEnv (ConLeche.storeNestedRecs (nestedStoreList p stored cvRms cvRns rulesM rulesN)
      (ENV2)) f.cvTa.name j := by
  obtain ⟨-, hposF⟩ := mutualFormers_nameFacts I.out.formers
  have hfreshT : env.find? f.cvTa.name = none := (hposF t f hft).2.2.1
  -- the pre-block environment
  have h0 : NoProjEnv env f.cvTa.name j := noProjEnv_of_fresh mp.base2.wf hfreshT j
  have hs0 : env.findProj? f.cvTa.name j = none :=
    findProj?_none_of_indFresh mp.base2.proj_ok hfreshT j
  -- the members
  have hnpT : ∀ g ∈ fms.take p.k, Expr.NoProjAt f.cvTa.name j g.cvTa.type := by
    intro g hg
    obtain ⟨t', hg'⟩ := List.getElem?_of_mem hg
    have ht' : t' < p.k := by
      have hl := (List.getElem?_eq_some_iff.mp hg').1
      rw [List.length_take] at hl
      omega
    have hgf : fms[t']? = some g := by rw [← List.getElem?_take_of_lt ht']; exact hg'
    exact ConLeche.Expr.noProjAt_of_constsResolve hfreshT _ (hposF t' g hgf).2.2.2.2.2
  have h1 : NoProjEnv (ConLeche.consMutualFormers (fms.take p.k) env) f.cvTa.name j :=
    noProjEnv_consMutualFormers h0 hnpT
  have hs1 : (ConLeche.consMutualFormers (fms.take p.k) env).findProj? f.cvTa.name j = none :=
    findProj?_none_consMutualFormers hs0
  have hs1' : (ConLeche.consNestedFormers (stored.take p.k) env).findProj? f.cvTa.name j
      = none := by rw [I.henv]; exact hs1
  -- the constructors
  have hnpC : ∀ c ∈ ctorsR.flatten, Expr.NoProjAt f.cvTa.name j c.1.type := by
    intro c hc
    obtain ⟨cs, hcs, hcin⟩ := List.mem_flatten.mp hc
    obtain ⟨mm, hmm⟩ := List.getElem?_of_mem hcs
    obtain ⟨hlenC, hallC⟩ := ConLeche.mapM_except_inv I.hctors
    obtain ⟨a, cs', ha, hcs', hrun⟩ := hallC mm (by
      have h := (List.getElem?_eq_some_iff.mp hmm).1
      omega)
    rw [hmm] at hcs'
    obtain rfl : cs = cs' := by simpa using hcs'
    obtain ⟨jj, hjj⟩ := List.getElem?_of_mem hcin
    obtain ⟨hlenD, hallD⟩ := ConLeche.restoreCtors_door hrun
    obtain ⟨c0, hc0⟩ : ∃ c0, a.ctors[jj]? = some c0 :=
      ⟨_, List.getElem?_eq_getElem (by
        have h := (List.getElem?_eq_some_iff.mp hjj).1
        omega)⟩
    obtain ⟨ty, -, hfd, -, -⟩ := hallD jj c0 c hc0 hjj
    exact ConLeche.Expr.ProjSlotsOk.noProjAt hs1' _ hfd.slots
  have h2 : NoProjEnv (ENV2) f.cvTa.name j := noProjEnv_consNestedCtors h1 hnpC
  have hs2 : (ENV2).findProj? f.cvTa.name j = none := findProj?_none_consNestedCtors hs1
  have hs2P : (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns)
      (ENV2)).findProj? f.cvTa.name j = none := findProj?_none_provisionNestedRecs hs2
  -- the recursors
  refine noProjEnv_storeNestedRecs h2 fun x hx => ⟨?_, fun r hr => ⟨?_, ?_⟩⟩
  · obtain ⟨c, hc, hcv, -, -, -⟩ := nestedStoreList_mem I.lenM hx
    have hcb : c < b.k := by rw [I.out.bk, ← I.lenN] at *; exact hc
    rw [hcv]
    exact ConLeche.Expr.ProjSlotsOk.noProjAt hs2 _ (I.recCvSlots hcb)
  · exact ConLeche.Expr.ProjSlotsOk.noProjAt hs2P _ (I.storeRuleSlots x hx r hr)
  · intro lvls pins hfire pin hpin
    obtain ⟨c, hc, hcv, -, -, -⟩ := nestedStoreList_mem I.lenM hx
    have hcb : c < b.k := by rw [I.out.bk, ← I.lenN] at *; exact hc
    have hty : Expr.NoProjAt f.cvTa.name j x.1.type := by
      rw [hcv]
      exact ConLeche.Expr.ProjSlotsOk.noProjAt hs2 _ (I.recCvSlots hcb)
    obtain ⟨-, -, -, pre, dom, body, bm, Dn, hstrip, -, hargs⟩ :=
      (I.storeRules x hx r hr).2.2.2.2 lvls pins hfire
    obtain ⟨-, hbody⟩ := ConLeche.rg_noProjAt_stripPis x.2.1 hstrip hty
    rw [ConLeche.Expr.noProjAt_forallE] at hbody
    have hmem : pin.liftLooseBVars (x.2.1 - x.2.2.1) 0 ∈ dom.getAppArgs := by
      rw [hargs, List.mem_append]
      exact Or.inl (List.mem_map_of_mem hpin)
    exact ConLeche.rg_noProjAt_of_lift pin 0 (ConLeche.rg_noProjAt_getAppArgs hbody.1 _ hmem)

/-! ## The recorded tables' data, at the run -/

/-- **THE RESTORED MEMBERS' RECORDED TABLES, AT THE RUN** (task #315
M7-2, DESIGN §U.29 items 4 and 5): `NestedTablesDataOf`'s per-entry
clause, `NestedMemberTableOk` at the model of the recursors'
environment.

The nested route RE-USES the table the scratch install built, so the
three data are the SCRATCH stage's (`auxStored_tbl_eq`, whose left
disjunct — the table stood at the pre-block environment already — is
refuted here as at `tblCtor`, by the nested stage's own freshness) and
the bundle is the nested block model's, read at `mp₃`:

* the recorded CONSTRUCTOR is the restored one's, because the restore
  keeps every name (`restoreCtors_door`'s front door) and the
  auxiliary constructor the read-back stored at the member's own
  singleton position is the constructor stage's (`auxStored_ctor_eq`,
  `MutualFormersFacts.namesC`);
* the OFFSET is `1` and the recorded parameter count is `b.nP`, both
  the scratch stage's data, and the restore keeps the stored counts
  (`restoreCtors_door`'s `o.2 = c.2`);
* the GUARDS are the scratch constructor type's, and they are the
  RESTORED type's because the restore moves no bound variable into or
  out of the guards' domains (`rg_structProjGuards_of_run`, §U.29
  (rrrr)/(tttt)) — the one step no agreement could give;
* the BUNDLE is `tableMember_of` at the nested block model: the
  representation at `mp₃` (`hreps₃`, passed in, the parent's own
  `crossEnv` chain), the typings crossed off `NestedCoreOut.typed`
  along the carrier's agreement, the sorts and frames
  `NestedTailIn.tableFacts`, the member's store fact off the members'
  cons and the representation's former, the names' shapes the run's,
  and `NoProjEnv` `NestedTailIn.storeNoProj`.

The face's `S` is keyed by NAME where the mutual route's is keyed by
index, because the nested table stage folds over a name-keyed list; the
inversion is the member list's own `Nodup` (`List.Nodup.idxOf_getElem`).

Consumer: `nestedTablesData_of`, hence `nestedRecsStored_of`. -/
theorem NestedTailIn.tablesData
    (mp₃ : EnvModelM V μ (ConLeche.storeNestedRecs
      (nestedStoreList p stored cvRms cvRns rulesM rulesN) (ENV2)))
    (hag₃ : ∀ n : Name, (∀ c, c < b.k → n ≠ (nestedRecCvAt p.k cvRms cvRns c).name) →
      mp₃.base2.acval n = mp₂.base2.acval n)
    (hreps₃ : IsBlockModelsAt mp₃.base2 (DB) (fun mm => (stored.getD mm default).cvTa))
    (hfind₃ : ∀ (n : Name) (ci : ConstantInfo),
      (ConLeche.consMutualFormers (fms.take p.k) env).find? n = some ci →
      (ConLeche.storeNestedRecs (nestedStoreList p stored cvRms cvRns rulesM rulesN)
        (ENV2)).find? n = some ci) :
    ∀ e ∈ (((stored.take p.k).zip ctorsR).zipIdx.map fun ((a, cs), mIdx) =>
        ((p.formers.getD mIdx default).1.name, a.tbl, cs)),
      NestedMemberTableOk mp₃.base2 (DB).isProp
        (fun T => (DB).tableCarrier (List.idxOf T p.memberNames)) e := by
  -- the member names, and the lists' lengths
  have hslen : stored.length = b.k := I.storedLen
  have hkb : p.k ≤ b.k := by rw [I.out.bk]; omega
  have hcvA := (ConLeche.consNestedFormers_take_eq I.haux I.out.formers I.hstored p.k hkb).2
  have hndB : b.memberNames.Nodup := by
    have h0 := I.out.nodup
    unfold ConLeche.MutualBlock.blockNames at h0
    exact (List.nodup_append.mp (List.nodup_append.mp h0).1).1
  have hndT : ((fms.take p.k).map (·.cvTa.name)).Nodup := by
    rw [show (fms.take p.k).map (·.cvTa.name) = (fms.map (·.cvTa.name)).take p.k from
      List.map_take]
    exact I.fmsNodup.sublist (List.take_sublist _ _)
  have hndM : p.memberNames.Nodup := by rw [← I.out.stage.names]; exact hndT
  -- the two crossings from `mp₂`
  have hag₂₃ : ∀ n : Name, ((ENV2).find? n).isSome = true →
      mp₃.base2.acval n = mp₂.base2.acval n := by
    intro n hn
    refine hag₃ n fun c hc heq => ?_
    have hfr := (I.recCvDoor hc).1
    rw [heq, hfr] at hn
    simp at hn
  have hrepsIB : IsBlockModels mp₂.base2 (DB) := I.out.reps.toIsBlockModels
  have htyped₃ : ∀ ψ : Name → Nat,
      FormersTyped mp₃.base2 (DB) ψ ∧ CtorsTyped mp₃.base2 (DB) ψ := fun ψ =>
    ⟨(I.out.typed ψ).1.crossEnv hag₂₃ hrepsIB, (I.out.typed ψ).2.1.crossEnv hag₂₃ hrepsIB⟩
  have hPT₃ : ∀ ψ : Name → Nat, PinsTyped mp₃.base2 (DB) ψ := fun ψ =>
    (I.out.typed ψ).2.2.crossEnv hag₂₃ hrepsIB I.kpos
  -- the entry
  intro e he
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp he
  obtain ⟨⟨a, cs⟩, mIdx⟩ := z
  intro tbl cvCa nPc nFc htblE hcsE
  have htbl : a.tbl = some tbl := htblE
  have hcsq : cs = [(cvCa, nPc, nFc)] := hcsE
  have hzip : ((stored.take p.k).zip ctorsR)[mIdx]? = some (a, cs) :=
    List.mk_mem_zipIdx_iff_getElem?.mp hz
  obtain ⟨haT, hcsR⟩ := zip_getElem?_pair _ _ _ _ hzip
  have hmIdx : mIdx < p.k := by
    have h := (List.getElem?_eq_some_iff.mp haT).1
    rw [List.length_take] at h
    omega
  have ha : stored[mIdx]? = some a := by rw [← List.getElem?_take_of_lt hmIdx]; exact haT
  -- the recorded table IS the scratch install's
  obtain ⟨cv, hfm, hdisj⟩ := ConLeche.auxStored_tbl_eq I.haux I.hstored ha htbl
  have hmemAt : b.memberNames[mIdx]? = some cv.name := by
    show (b.formers.map (·.1.name))[mIdx]? = _
    rw [List.getElem?_map, hfm]
    rfl
  have hcvName : cv.name = (p.formers.getD mIdx default).1.name := by
    rw [← I.memberNameAt hmIdx, List.getD_eq_getElem?_getD, hfm]
    rfl
  have hfreshEnv : env.find?
      (ConLeche.projTableName (p.formers.getD mIdx default).1.name) = none :=
    ConLeche.consNestedFormers_find?_none (ConLeche.consNestedCtors_find?_none
      (storeNestedRecs_find?_none
        (ConLeche.nestedTables_projTable_fresh I.htbl _ he tbl cvCa nPc nFc htbl hcsq)))
  rcases hdisj with hleft | ⟨fms', f₀', f, ctorsA', sortss', t, J, c, bodies, hformers', hf₀',
    hctors', hft, hfname, hown, hnIdx0, hbodies, rfl⟩
  · exfalso
    have hcontra : (some (ConstantInfo.projInfo tbl) : Option ConstantInfo) = none := by
      rw [← hleft, hcvName]
      exact hfreshEnv
    exact nomatch hcontra
  -- the read-back's stages are the tail's
  have hfmsEq : fms' = fms :=
    congrArg Prod.snd (Except.ok.inj (hformers'.symm.trans I.out.formers))
  rw [hfmsEq] at hft hf₀' hctors'
  have hf₀Eq : f₀' = f₀ := Option.some.inj (hf₀'.symm.trans I.out.facts.first)
  rw [hf₀Eq] at hctors'
  have hcsEq : (ctorsA', sortss') = (ctorsA, sortss) :=
    Except.ok.inj (hctors'.symm.trans I.out.ctors)
  have hcA1 : ctorsA' = ctorsA := congrArg Prod.fst hcsEq
  have hcA2 : sortss' = sortss := congrArg Prod.snd hcsEq
  -- the table's member is this one
  have htEq : t = mIdx := by
    refine nodup_getElem?_idx hndB ?_ hmemAt
    rw [← I.out.facts.names, List.getElem?_map, hft, Option.map_some, hfname]
  rw [htEq] at hft hown
  -- the member's own constructor, at its global position
  have hown0 : (b.ownCtors mIdx)[0]? = some (J, c) := by rw [hown]; rfl
  obtain ⟨hcJ, -⟩ := ConLeche.ownCtors_getElem?_ctors hown0
  have hJeq : J = b.ownOffset mIdx + 0 := ConLeche.ownCtors_getElem?_idx I.out.grouped hown0
  -- the restored constructor at that position
  have hcsD : ctorsR.getD mIdx [] = cs := by rw [List.getD_eq_getElem?_getD, hcsR]; rfl
  have hc0R : (ctorsR.getD mIdx [])[0]? = some (cvCa, nPc, nFc) := by rw [hcsD, hcsq]; rfl
  obtain ⟨cAx, hJcA, hnFeq, -, -, -⟩ := I.out.stage.ctorFacts mIdx 0 _ hmIdx hc0R
  have hJcA' : ctorsA[J]? = some cAx := by rw [hJeq]; exact hJcA
  obtain ⟨-, -, hallC2⟩ := ConLeche.checkMutualCtors_inv I.out.ctors
  obtain ⟨hnFc, sorts, hss, -⟩ := hallC2 J c cAx hcJ hJcA'
  have hcAD : ctorsA.getD J default = cAx := by
    rw [List.getD_eq_getElem?_getD, hJcA']; rfl
  have hsD : sortss.getD J [] = sorts := by rw [List.getD_eq_getElem?_getD, hss]; rfl
  -- the restored constructor's front door, and the auxiliary constant it restores
  obtain ⟨hlenR, hallR⟩ := ConLeche.mapM_except_inv I.hctors
  have hmmR : mIdx < (stored.take p.k).length := by rw [List.length_take]; omega
  obtain ⟨a', l', ha', hl', hrun⟩ := hallR mIdx hmmR
  have haa : a' = a := Option.some.inj (ha'.symm.trans haT)
  have hll : l' = cs := Option.some.inj (hl'.symm.trans hcsR)
  rw [haa, hll] at hrun
  obtain ⟨hlenD, hallD⟩ := ConLeche.restoreCtors_door hrun
  have hlen1 : a.ctors.length = 1 := by rw [← hlenD, hcsq]; rfl
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, a.ctors[0]? = some c₀ :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨ty, hresTy, hfd, hnP2, hoEq⟩ :=
    hallD 0 c₀ (cvCa, nPc, nFc) hc₀ (by rw [hcsq]; rfl)
  obtain ⟨hlenA, hallA⟩ := ConLeche.auxStored_ctor_eq I.haux I.out.formers I.out.ctors
    I.out.grouped I.hstored ha
  obtain ⟨cA', hcA', hc1, hcnP, hcnF⟩ := hallA 0 c₀ hc₀
  have hcA'eq : cA' = cAx := by
    have h := hcA'
    rw [← hJeq, hJcA'] at h
    exact (Option.some.inj h).symm
  rw [hcA'eq] at hc1 hcnF
  -- the restored constructor's data, against the recorded table's
  have hoEq' : cvCa = ({c₀.1 with levelParams := p.lps, type := ty} : ConstantVal) := hoEq
  have hnPc : nPc = b.nP := by
    rw [← hcnP]
    exact congrArg Prod.fst hnP2
  have hnFcx : nFc = cAx.2 := hnFeq
  have hlpsC : cvCa.levelParams = b.lps := by
    rw [hoEq', (ConLeche.auxBlock_fields I.hb).2.1]
  have hcvType : cvCa.type = ty := by rw [hoEq']
  have hcvNameC : cvCa.name = c₀.1.name := by rw [hoEq']
  have hcname : cAx.1.name = c.cv.name := by
    have h := congrArg (fun l => l[J]?) I.out.facts.namesC
    simp only [List.getElem?_map, hJcA', hcJ] at h
    exact Option.some.inj h
  -- the guards, across the restore
  have hguards : ConLeche.structProjGuards cAx.1.type b.nP cAx.2 sorts
      = ConLeche.structProjGuards cvCa.type nPc nFc sorts := by
    rw [hnPc, hnFcx, hcvType]
    refine (ConLeche.rg_structProjGuards_of_run I.hfA I.helim I.hb I.haux I.hfresh
      (ConLeche.mutualFormers_inv I.out.formers).1 I.out.ctors I.out.kindsRun hJcA' ?_ sorts).symm
    rw [← hc1]
    exact hresTy
  -- the block model's readers at this member
  have hftT : (fms.take p.k)[mIdx]? = some f := by
    rw [List.getElem?_take_of_lt hmIdx]; exact hft
  have hname : (DB).memberName mIdx = f.cvTa.name := by
    show ((fms.take p.k).map (·.cvTa.name)).getD mIdx .anonymous = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hftT]
    rfl
  have hnIdxAt : (DB).nIdxAt mIdx = f.nIdx := by
    show ((fms.take p.k).map (·.nIdx)).getD mIdx 0 = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hftT]
    rfl
  have hone : (DB).ctorsM mIdx = [(cvCa, nFc)] := by
    rw [I.out.record.ctors mIdx hmIdx, hcsD, hcsq]
    rfl
  -- the member's store fact at the recursors' model
  have hcvTaEq : (stored.getD mIdx default).cvTa = f.cvTa := by
    obtain ⟨f', hf', hcveq, -, -⟩ := hcvA mIdx _ hmIdx ha
    have hff : f' = f := Option.some.inj (hf'.symm.trans hft)
    rw [List.getD_eq_getElem?_getD, ha, ← hff]
    exact hcveq
  have hstoredM : MemberStored mp₃.base2 b.lps b.nP f (DB).resSort ((DB).ppsM mIdx) := by
    obtain ⟨cvR, mI, rP, rules, hIb⟩ := hreps₃ mIdx hmIdx
    refine
      { find := hfind₃ _ _ (ConLeche.Model.consMutualFormers_find?_self
          (List.mem_of_getElem? hftT) hndT)
        lps := I.out.facts.lps mIdx f hft
        strip := I.out.facts.strip mIdx f hft
        sEq := I.out.facts.sEq mIdx f hft
        data := ?_ }
    show FormerData mp₃.base2 f.cvTa (b.nP + f.nIdx) (DB).resSort ((DB).ppsM mIdx)
    have hFD := hIb.former
    rw [hnIdxAt] at hFD
    rw [← hcvTaEq]
    exact hFD
  -- the names' shapes
  obtain ⟨-, hTshape, hresT, hrecName⟩ := mutualMemberNames I.out.formers mIdx f hft
  have hresR : ConLeche.reservedBasisNames.contains (f.cvTa.name.str "rec") = false := by
    rw [← hrecName, ← I.recCvNameM hmIdx]
    exact (I.recCvDoor (by omega)).2.1
  -- the bundle
  have htm := tableMember_of hreps₃.toIsBlockModels hPT₃ htyped₃ I.tableFacts
    hmIdx hft hname hstoredM rfl hnIdx0 hone hJeq.symm hlpsC
    (I.storeNoProj hft) hTshape hresT hresR
    (by rw [hcvNameC, hc1]; exact (mutualCtorNames I.out.ctors J cAx hJcA').1)
    (by rw [hcvNameC, hc1]; exact (mutualCtorNames I.out.ctors J cAx hJcA').2)
    hss
  refine ⟨f.cvTa, sorts, (DB).ppsM mIdx, (DB).dsF mIdx 0, (DB).esF mIdx 0, ?_, rfl, ?_, ?_⟩
  · -- the recorded constructor is the restored one's
    show c.cv.name = cvCa.name
    rw [hcvNameC, hc1, hcname]
  · -- the guards
    show ConLeche.structProjGuards (ctorsA'.getD J default).1.type b.nP c.nF (sortss'.getD J [])
      = ConLeche.structProjGuards cvCa.type nPc nFc sorts
    rw [hcA1, hcA2, hcAD, hsD, ← hnFc]
    exact hguards
  · -- the bundle, at the entry's own name and the table's own fields
    have hidx : List.idxOf (p.formers.getD mIdx default).1.name p.memberNames = mIdx := by
      have hmemP : p.memberNames[mIdx]? = some (p.formers.getD mIdx default).1.name := by
        show (p.formers.map (·.1.name))[mIdx]? = _
        rw [List.getElem?_map, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (show mIdx < p.formers.length from hmIdx)]
        rfl
      obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hmemP
      rw [← hget]
      exact hndM.idxOf_getElem mIdx hlt
    show TableMember mp₃.base2 b.lps nPc (p.formers.getD mIdx default).1.name f.cvTa cvCa nFc 0
      f.s (DB).isProp sorts ((DB).ppsM mIdx) ((DB).dsF mIdx 0) ((DB).esF mIdx 0)
      ((DB).tableCarrier (List.idxOf (p.formers.getD mIdx default).1.name p.memberNames))
    rw [hidx, hnPc, ← hcvName, ← hfname]
    exact htm

end Run

/-! ## K.50's face -/

/-- **K.50's face** (DESIGN §U.29 (gggg)): at every tail input, every
restored rule's two RESCUE BITS are answered where `ConstWF` asks for
them — at the environment the rules were scoped at, the rule-less
provision.

The record is the two CONJUNCTS and not the two bits.  `restoreRules`
copies `k` and `eta` from the SCRATCH rule while RENAMING the
constructor, so what the scratch block's own check says and what
`ConstWF` asks of the stored rule differ in both arguments, and no
lemma in the tree relates them across the copies' capability records.
Recording the bits `false` instead would DECLINE 35 of the 41 Mathlib
cone blocks and 7 of the 27 shadow fixtures: η is about a structure's
single constructor and its recursor not being a projection function,
not about field counts, and a copy of a structure-like container is
structure-like.  In this form the record holds 27/27 and 41/41 with no
fire at all — the K half vacuously, and recorded anyway, nothing making
it so in principle.

The face names only what it mentions: the two restore runs that produce
the rule rows, and the environment they ran at.  Consumer:
`nestedRecsStored_of`, through `NestedTailIn.storeCtors`. -/
@[expose] def NestedRuleBitsOf (μ : CheckMode) (F : Nat) : Prop :=
  ∀ (env : Env) (p : NestedParts) (st : ElimState) (stored : List AuxStored)
    (ctorsR : List (List (ConstantVal × Nat × Nat))) (cvRms cvRns : List ConstantVal)
    (rulesM rulesN : List (List RecRule)),
    (cvRms.zip (stored.take p.k)).mapM (fun (cvRa, a) =>
        ConLeche.restoreRules (m := ConLeche.CheckM) (fueledOps μ F)
          (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns)
            (ConLeche.consNestedCtors ctorsR.flatten
              (ConLeche.consNestedFormers (stored.take p.k) env)))
          (ConLeche.restoreTbl p st) cvRa.levelParams cvRa.name false cvRa.type a.mI a.rP a.rules)
      = .ok rulesM →
    (cvRns.zip (stored.drop p.k)).mapM (fun (cvRa, a) =>
        ConLeche.restoreRules (m := ConLeche.CheckM) (fueledOps μ F)
          (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns)
            (ConLeche.consNestedCtors ctorsR.flatten
              (ConLeche.consNestedFormers (stored.take p.k) env)))
          (ConLeche.restoreTbl p st) cvRa.levelParams cvRa.name true cvRa.type a.mI a.rP a.rules)
      = .ok rulesN →
    ∀ c, c < p.k + cvRns.length → ∀ r ∈ nestedRulesAt p.k rulesM rulesN c,
      (RecRule.k r = true → ConLeche.recRuleKOf
        (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns)
          (ConLeche.consNestedCtors ctorsR.flatten
            (ConLeche.consNestedFormers (stored.take p.k) env))).find?
        (RecRule.ctor r) = true) ∧
      (RecRule.eta r = true → ConLeche.recRuleEtaOf
        (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns)
          (ConLeche.consNestedCtors ctorsR.flatten
            (ConLeche.consNestedFormers (stored.take p.k) env))).find?
        (nestedRecCvAt p.k cvRms cvRns c).name (RecRule.ctor r) = true)

/-! ## The nested install's conses -/

namespace NestedInstallExt

/-- A stage that conses nothing (`BlockInstallExt.rfl'`'s twin). -/
theorem rfl' (Ms : List Name) (env : Env) : NestedInstallExt Ms env env [] :=
  ⟨⟨rfl, by simp⟩, by simp, by simp, by simp⟩

/-- Two nested install stages compose (`BlockInstallExt.trans`'s twin):
the later stage's names are fresh at the earlier environment, so they
are fresh at the base too. -/
theorem trans {Ms : List Name} {env env₁ env₂ : Env} {new₁ new₂ : List ConstantInfo}
    (h₁ : NestedInstallExt Ms env env₁ new₁) (h₂ : NestedInstallExt Ms env₁ env₂ new₂) :
    NestedInstallExt Ms env env₂ (new₂ ++ new₁) := by
  obtain ⟨⟨hc₁, hf₁⟩, hi₁, hr₁, hp₁⟩ := h₁
  obtain ⟨⟨hc₂, hf₂⟩, hi₂, hr₂, hp₂⟩ := h₂
  refine ⟨⟨by rw [hc₂, hc₁, List.append_assoc], fun c hc => ?_⟩, fun c hc => ?_, fun c hc => ?_,
    fun c hc => ?_⟩ <;> rcases List.mem_append.mp hc with hc' | hc'
  · exact ConLeche.Semantics.find?_none_of_append hc₁ (hf₂ c hc')
  · exact hf₁ c hc'
  · exact hi₂ c hc'
  · exact hi₁ c hc'
  · exact hr₂ c hc'
  · exact hr₁ c hc'
  · exact hp₂ c hc'
  · exact hp₁ c hc'

/-- One fresh cons, as the nested crossing sees it. -/
theorem cons {Ms : List Name} {env : Env} {c₀ : ConstantInfo}
    (hfresh : env.find? c₀.name = none)
    (hi : ∀ (cv : ConstantVal) (caps : IndCaps), c₀ = .indInfo cv caps → c₀.name ∈ Ms)
    (hr : ∀ (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      c₀ = .recInfo cv mI rP rules → ∀ n : Name, c₀.name = n.str "rec" → n ∈ Ms)
    (hp : ∀ tbl : ProjTable, c₀ = .projInfo tbl → tbl.structName ∈ Ms) :
    NestedInstallExt Ms env ⟨c₀ :: env.consts⟩ [c₀] := by
  refine ⟨⟨rfl, ?_⟩, ?_, ?_, ?_⟩ <;> intro c hc <;> (obtain rfl := List.mem_singleton.mp hc)
  · exact hfresh
  · exact hi
  · exact hr
  · exact hp

end NestedInstallExt

/-- **Stage 1**: the restored formers, consed as the block's members. -/
theorem consNestedFormers_installExt {Ms : List Name} {as : List AuxStored} {env : Env}
    (hfresh : ∀ a ∈ as, env.find? a.cvTa.name = none)
    (hMs : ∀ a ∈ as, a.cvTa.name ∈ Ms) :
    NestedInstallExt Ms env (ConLeche.consNestedFormers as env)
      ((as.map fun a => ConstantInfo.indInfo a.cvTa a.caps).reverse) := by
  refine ⟨⟨consNestedFormers_consts, fun c hc => ?_⟩, fun c hc => ?_, fun c hc => ?_,
    fun c hc => ?_⟩ <;>
    (simp only [List.mem_reverse, List.mem_map] at hc; obtain ⟨a, ha, rfl⟩ := hc)
  · exact hfresh a ha
  · exact fun _ _ _ => hMs a ha
  · exact fun _ _ _ _ heq => nomatch heq
  · exact fun _ heq => nomatch heq

/-- **Stage 2**: the restored constructors' conses — no container, no
recursor, no table. -/
theorem consNestedCtors_installExt {Ms : List Name} {cs : List (ConstantVal × Nat × Nat)}
    {env : Env} (hfresh : ∀ c ∈ cs, env.find? c.1.name = none) :
    NestedInstallExt Ms env (ConLeche.consNestedCtors cs env)
      ((cs.map fun c => ConstantInfo.ctorInfo c.1 c.2.1 c.2.2).reverse) := by
  refine ⟨⟨consNestedCtors_consts, fun c hc => ?_⟩, fun c hc => ?_, fun c hc => ?_,
    fun c hc => ?_⟩ <;>
    (simp only [List.mem_reverse, List.mem_map] at hc; obtain ⟨cA, hcA, rfl⟩ := hc)
  · exact hfresh cA hcA
  · exact fun _ _ heq => nomatch heq
  · exact fun _ _ _ _ heq => nomatch heq
  · exact fun _ heq => nomatch heq

/-- **Stage 3**: the restored recursors' store.  The clause is the
CONDITIONAL one: a member's recursor is `T.rec`, and a mimic's name is
no `_.str "rec"` at all. -/
theorem storeNestedRecs_installExt {Ms : List Name}
    {l : List (ConstantVal × Nat × Nat × List RecRule)} {env : Env}
    (hfresh : ∀ x ∈ l, env.find? x.1.name = none)
    (hrec : ∀ x ∈ l, ∀ n : Name, x.1.name = n.str "rec" → n ∈ Ms) :
    NestedInstallExt Ms env (ConLeche.storeNestedRecs l env)
      ((l.map fun x => ConstantInfo.recInfo x.1 x.2.1 x.2.2.1 x.2.2.2).reverse) := by
  refine ⟨⟨storeNestedRecs_consts, fun c hc => ?_⟩, fun c hc => ?_, fun c hc => ?_,
    fun c hc => ?_⟩ <;>
    (simp only [List.mem_reverse, List.mem_map] at hc; obtain ⟨x, hx, rfl⟩ := hc)
  · exact hfresh x hx
  · exact fun _ _ heq => nomatch heq
  · exact fun _ _ _ _ _ => hrec x hx
  · exact fun _ heq => nomatch heq

/-- **Stage 4**: the structure-like members' projection tables — every
table is a MEMBER's. -/
theorem nestedTables_installExt {Ms : List Name} :
    ∀ {l : List (Name × Option ProjTable × List (ConstantVal × Nat × Nat))} {env env' : Env},
      ConLeche.nestedTables (m := ConLeche.CheckM) l env = .ok env' →
      (∀ e ∈ l, e.1 ∈ Ms) →
      ∃ new : List ConstantInfo, NestedInstallExt Ms env env' new
  | [], env, env', h, _ => by
    obtain rfl := ConLeche.nestedTables_nil_inv h
    exact ⟨[], NestedInstallExt.rfl' Ms _⟩
  | (T, tbl?, cs) :: rest, env, env', h, hTs => by
    obtain ⟨envI, hI, hrest⟩ := ConLeche.nestedTables_inv h
    obtain ⟨new₂, h₂⟩ := nestedTables_installExt hrest
      (fun q hq => hTs q (List.mem_cons_of_mem _ hq))
    rcases ConLeche.nestedMemberTable_inv hI with rfl | ⟨tbl, cvCa, nP, nF, -, -, htbl⟩
    · exact ⟨new₂, h₂⟩
    · obtain ⟨bodies, -, -, -, hfreshTbl, rfl⟩ := ConLeche.checkStructProjTable_inv htbl
      refine ⟨_, NestedInstallExt.trans (NestedInstallExt.cons ?_ ?_ ?_ ?_) h₂⟩
      · exact hfreshTbl
      · exact fun _ _ heq => nomatch heq
      · exact fun _ _ _ _ heq => nomatch heq
      · intro tbl' heq
        obtain rfl := ConstantInfo.projInfo.inj heq
        exact hTs (T, tbl?, cs) List.mem_cons_self

/-! ## The recorded tables' face -/

/-- **THE RESTORED MEMBERS' RECORDED TABLES** (task #315 M7-2): at
every tail input and every model of the recursors' environment whose
carrier is the constructors' off the restored recursors, the SCRATCH
block's recorded projection tables carry the data the table stage's P
step asks for — the recorded constructor name is the member's one
restored constructor's, the offset is `1`, the guards are that
constructor's field sorts' `structProjGuards`, and the flat bundle at
it is the member's table carrier (`NestedMemberTableOk`,
`NestedTables.lean`).

The nested route RE-USES the table the scratch install built
(`mutualMemberTable`, `Kernel/Inductives/MutualInstall.lean`) instead
of recomputing it, so the three data are that stage's own and the
bundle is the scratch block model's, read through the restore — a
transfer no module in the tree performs today.  Hence the face.
Consumer: `nestedRecsStored_of`. -/
@[expose] def NestedTablesDataOf (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat) : Prop :=
  ∀ {env : Env} (mp : EnvModelM V μ env) (p : NestedParts) (envOut : Env) (st : ElimState)
    (b : MutualBlock) (envAux : Env) (stored : List AuxStored)
    (ctorsR : List (List (ConstantVal × Nat × Nat))) (cvRms cvRns : List ConstantVal)
    (rulesM rulesN : List (List RecRule)) (fmsA ctorsA₀ : List ConstantVal)
    (fms : List MutualFormerA) (f₀ : MutualFormerA) (ctorsA : List (ConstantVal × Nat))
    (sortss : List (List Level)) (kinds : List (List (RecFieldKind × Nat)))
    (mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env))
    (ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (W : (Name → Nat) → Nat)
    (idxF : Nat → List Expr) (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
    (fvsPF xFvsF : Nat → List Expr) (xrestF : Nat → Expr)
    (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)))
    (dsR : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (xFvsR : Nat → Nat → List Expr)
    (pinsS : List PinSyn)
    (mp₂ : EnvModelM V μ (ConLeche.consNestedCtors ctorsR.flatten
      (ConLeche.consMutualFormers (fms.take p.k) env))),
    NestedTailIn F mp p envOut st b envAux stored ctorsR cvRms cvRns rulesM rulesN fmsA ctorsA₀
      fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF dsR
      xFvsR pinsS mp₂ →
    ∀ mp₃ : EnvModelM V μ (ConLeche.storeNestedRecs
        (nestedStoreList p stored cvRms cvRns rulesM rulesN)
        (ConLeche.consNestedCtors ctorsR.flatten
          (ConLeche.consMutualFormers (fms.take p.k) env))),
      (∀ n : Name, (∀ c, c < b.k → n ≠ (nestedRecCvAt p.k cvRms cvRns c).name) →
        mp₃.base2.acval n = mp₂.base2.acval n) →
      IsBlockModelsAt mp₃.base2
        (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF
          xrestF eissF tssF ctorsR dsR xFvsR pinsS)
        (fun mm => (stored.getD mm default).cvTa) →
      (∀ (n : Name) (ci : ConstantInfo),
        (ConLeche.consMutualFormers (fms.take p.k) env).find? n = some ci →
        (ConLeche.storeNestedRecs (nestedStoreList p stored cvRms cvRns rulesM rulesN)
          (ConLeche.consNestedCtors ctorsR.flatten
            (ConLeche.consMutualFormers (fms.take p.k) env))).find? n = some ci) →
      ∃ (isProp : Bool) (S : Name → (Name → Nat) → (Nat → V) → V),
        ∀ e ∈ (((stored.take p.k).zip ctorsR).zipIdx.map fun ((a, cs), mIdx) =>
            ((p.formers.getD mIdx default).1.name, a.tbl, cs)),
          NestedMemberTableOk mp₃.base2 isProp S e

/-! ## The stage, assembled -/

/-- **THE RECURSORS' STAGE OF A NESTED BLOCK, ASSEMBLED** —
`NestedRecsStored` (DESIGN §U.25 (e) 5), from the readings, the
equations and the chosen tuple, in five steps:

* **the provision** (`NestedTailIn.provisioned`): the `k + nPins`
  restored recursors consed RULE-LESS, class `c` with the tuple's
  `c`-th projection as its leaf, the restored types read there and the
  carrier untouched off those names;
* **the rule law** (`NestedTailIn.recRuleLawsAt`) at every restored
  rule of every class, at that provisioned model;
* **the store swap** (`nestedRecsStore_at` at `nestedStoreList`): the
  same recursors WITH their rules, the front door off
  `NestedTailIn.storeDoor`, the rules' well-formedness off
  `storeRules`, their constructors and rescue bits off `storeCtors`,
  and the laws transported by `RecRuleLaw.swapP`;
* **the tables** (`stageNestedTables`): the structure-like members'
  recorded projection tables, the members' names distinct;
* **the seven fields** of `NestedTailOut`: the install's conses as one
  `NestedInstallExt` (the four stage lemmas above, composed), the two
  agreements along the chain `mp → mp₂ → mpP → mp₃ → mpOut`, the
  lookups' survival, the block's representation at the OUTPUT model —
  crossed unguarded through the provision and the swap and GUARDED
  through the tables, where a new projection table moves a reading, the
  guards being the members' own types' resolution at the pre-block
  environment and the restored constructors' `ProjSlotsOk` at the
  formers' one — and the pins' groups and containers, whose readings do
  not move because every constant the install conses is fresh at the
  pre-block environment (`containerInfo?_ext_ind_eq`).

Three named facts remain: K.50 (`NestedRuleBitsOf`, the restored rules'
two rescue conjuncts at the provision), K.36 (`NestedCtorPinNamesOf`,
the readings' and the equations' own model face) and the recorded
tables' data (`NestedTablesDataOf`).  Consumer:
`nestedTailModeled_of_stage`. -/
theorem nestedRecsStored_of {F : Nat}
    (hbits : NestedRuleBitsOf μ F) (hK36 : NestedCtorPinNamesOf μ F)
    (htbls : NestedTablesDataOf V μ F) :
    NestedRecsStored V μ F := by
  intro env mp p envOut st b envAux stored ctorsR cvRms cvRns rulesM rulesN fmsA ctorsA₀ fms f₀
    ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF dsR xFvsR
    pinsS mp₂ I s rdsM concM R mpA cvRas S E Tu
  -- the lists' lengths
  have hbk : b.k = p.k + pinsS.length := I.out.bk
  have hslen : stored.length = b.k := I.storedLen
  have hM : (stored.take p.k).length ≤ rulesM.length := by
    rw [(ConLeche.mapM_except_inv I.hrulesM).1, List.length_zip, I.lenM, List.length_take, hslen]
    omega
  have hN : (stored.drop p.k).length ≤ rulesN.length := by
    rw [(ConLeche.mapM_except_inv I.hrulesN).1, List.length_zip, I.lenN, List.length_drop, hslen]
    omega
  have hpo : ConLeche.nestedProvOf (nestedStoreList p stored cvRms cvRns rulesM rulesN)
      = nestedProvList p stored cvRms cvRns := nestedProvOf_nestedStoreList hM hN
  -- **(a) the provision**
  obtain ⟨mpP, -, -, hleafP, hagP⟩ := I.provisioned I.recNodup R E Tu
  -- **(b) the rule law at every rule**
  have hnames := hK36 env p st fmsA ctorsA₀ I.hfA I.hcA I.helim I.hcont
  have hK35 := nestedRecTysAuxOk_of_bool I.hb I.hauxApps
  have hK35r := nestedRulesAuxOk_of_bool I.hb I.hauxApps
  have hsw : ConLeche.SwapShList
      (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns)
        (ConLeche.consNestedCtors ctorsR.flatten
          (ConLeche.consMutualFormers (fms.take p.k) env))).consts
      (ConLeche.storeNestedRecs (nestedStoreList p stored cvRms cvRns rulesM rulesN)
        (ConLeche.consNestedCtors ctorsR.flatten
          (ConLeche.consMutualFormers (fms.take p.k) env))).consts := by
    rw [← hpo]
    exact swapShList_provision_store_nested _ (ConLeche.SwapShList.of_eq _)
  have hcg := ConLeche.SwapShList.congr hsw
  -- **(c) the store swap**
  have hbits' : ∀ c, c < b.k → ∀ r ∈ nestedRulesAt p.k rulesM rulesN c,
      (RecRule.k r = true → ConLeche.recRuleKOf
        (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns)
          (ConLeche.consNestedCtors ctorsR.flatten
            (ConLeche.consMutualFormers (fms.take p.k) env))).find?
        (RecRule.ctor r) = true) ∧
      (RecRule.eta r = true → ConLeche.recRuleEtaOf
        (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns)
          (ConLeche.consNestedCtors ctorsR.flatten
            (ConLeche.consMutualFormers (fms.take p.k) env))).find?
        (nestedRecCvAt p.k cvRms cvRns c).name (RecRule.ctor r) = true) := by
    intro c hc r hr
    have h := hbits env p st stored ctorsR cvRms cvRns rulesM rulesN I.hrulesM I.hrulesN c
      (by rw [I.lenN]; omega) r hr
    rw [I.henv] at h
    exact h
  have hlaws : ∀ m₃ : EnvModel V (ConLeche.storeNestedRecs
        (nestedStoreList p stored cvRms cvRns rulesM rulesN)
        (ConLeche.consNestedCtors ctorsR.flatten
          (ConLeche.consMutualFormers (fms.take p.k) env))),
      m₃.acval = mpP.base2.acval → ∀ φ : Name → Nat,
      ∀ x ∈ nestedStoreList p stored cvRms cvRns rulesM rulesN, ∀ rl ∈ x.2.2.2,
        RecRule.fire rl ≠ .inert →
        RecRuleLaw m₃ φ x.1.name x.1 x.2.1 x.2.2.1 rl := by
    intro m₃ hac φ x hx rl hrl hfire
    obtain ⟨c, hc, hcv, hmI, hrP, hrs⟩ := nestedStoreList_mem I.lenM hx
    have hcb : c < b.k := by rw [hbk, ← I.lenN]; exact hc
    obtain ⟨a, ha⟩ : ∃ a, stored[c]? = some a :=
      ⟨_, List.getElem?_eq_getElem (by rw [hslen]; exact hcb)⟩
    have haD : stored.getD c default = a := by rw [List.getD_eq_getElem?_getD, ha]; rfl
    rw [hrs] at hrl
    have hlaw := I.recRuleLawsAt S hnames
      (fun _q₀ _kJ i _dJ G hi ci J h1 h2 h3 => (G.ctorsOf i hi ci J h1 h2 h3).1)
      hK35 R E Tu hleafP hagP hK35r φ hcb ha rl hrl hfire
    rw [hcv, hmI, hrP, haD]
    exact RecRuleLaw.swapP hcg hac hlaw
  obtain ⟨mp₃, hac₃, -⟩ := nestedRecsStore_at hpo mp₂.base2.wf mpP
    (fun x hx => (I.storeDoor x hx).1) (fun x hx => (I.storeDoor x hx).2.1)
    (fun x hx => ⟨(I.storeDoor x hx).2.2.1, (I.storeDoor x hx).2.2.2.1,
      (I.storeDoor x hx).2.2.2.2.1, (I.storeDoor x hx).2.2.2.2.2⟩)
    I.storeRules (I.storeCtors hbits') hlaws
  have hag₃ : ∀ n : Name, (∀ c, c < b.k → n ≠ (nestedRecCvAt p.k cvRms cvRns c).name) →
      mp₃.base2.acval n = mp₂.base2.acval n := by
    intro n hn
    rw [hac₃]
    exact hagP n (fun c hc => hn c (by rw [← I.kT]; exact hc))
  -- **(d) the tables**
  have hclen : ctorsR.length = p.k := by
    rw [(ConLeche.mapM_except_inv I.hctors).1, List.length_take]
    omega
  have hzl : ((stored.take p.k).zip ctorsR).length = p.k := by
    rw [List.length_zip, List.length_take, hclen, hslen]
    omega
  have htblR : ConLeche.nestedTables (m := ConLeche.CheckM)
      (((stored.take p.k).zip ctorsR).zipIdx.map fun ((a, cs), mIdx) =>
        ((p.formers.getD mIdx default).1.name, a.tbl, cs))
      (ConLeche.storeNestedRecs (nestedStoreList p stored cvRms cvRns rulesM rulesN)
        (ConLeche.consNestedCtors ctorsR.flatten
          (ConLeche.consMutualFormers (fms.take p.k) env))) = .ok envOut := by
    rw [← I.henv]
    exact I.htbl
  have hTLnames : ((((stored.take p.k).zip ctorsR).zipIdx.map fun ((a, cs), mIdx) =>
        ((p.formers.getD mIdx default).1.name, a.tbl, cs)).map (·.1)) = p.memberNames := by
    have hpk : p.formers.length = p.k := rfl
    refine List.ext_getElem? fun i => ?_
    rw [List.getElem?_map, List.getElem?_map, List.getElem?_zipIdx]
    show _ = (p.formers.map (·.1.name))[i]?
    rw [List.getElem?_map]
    cases hz : ((stored.take p.k).zip ctorsR)[i]? with
    | none =>
      have hi : ¬ i < p.k := by
        intro h
        rw [List.getElem?_eq_getElem (by rw [hzl]; exact h)] at hz
        exact nomatch hz
      rw [List.getElem?_eq_none (by rw [hpk]; omega)]
      rfl
    | some z =>
      have hi : i < p.k := by
        have h := (List.getElem?_eq_some_iff.mp hz).1
        rw [hzl] at h
        exact h
      obtain ⟨a, cs⟩ := z
      simp only [Option.map_some, Nat.zero_add]
      rw [List.getElem?_eq_getElem (by rw [hpk]; exact hi), List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [hpk]; exact hi)]
      rfl
  have hndM : p.memberNames.Nodup := by
    rw [← I.out.stage.names, show (fms.take p.k).map (·.cvTa.name)
      = (fms.map (·.cvTa.name)).take p.k from List.map_take]
    exact I.fmsNodup.sublist (List.take_sublist _ _)
  -- **the install's conses**
  have hcvA := (ConLeche.consNestedFormers_take_eq I.haux I.out.formers I.hstored p.k
    (by omega)).2
  have hmemFresh : ∀ a ∈ stored.take p.k, env.find? a.cvTa.name = none := by
    intro a ha
    have h := List.all_eq_true.mp I.hcaps a ha
    rw [Bool.and_eq_true] at h
    exact Option.isNone_iff_eq_none.mp h.2
  have hmemMs : ∀ a ∈ stored.take p.k, a.cvTa.name ∈ p.memberNames := by
    intro a ha
    obtain ⟨i, hi⟩ := List.getElem?_of_mem ha
    have hilt : i < p.k := by
      have h := (List.getElem?_eq_some_iff.mp hi).1
      rw [List.length_take] at h
      omega
    have hsi : stored[i]? = some a := by rw [← List.getElem?_take_of_lt hilt]; exact hi
    obtain ⟨f, hf, hcveq, -, -⟩ := hcvA i _ hilt hsi
    rw [← I.out.stage.names]
    exact List.mem_map.mpr ⟨f,
      List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hilt]; exact hf), by rw [← hcveq]⟩
  have hmemStored : ∀ n ∈ p.memberNames, ∃ a ∈ stored.take p.k, a.cvTa.name = n := by
    intro n hn
    rw [← I.out.stage.names] at hn
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hn
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hf
    have hilt : i < p.k := by
      have h := (List.getElem?_eq_some_iff.mp hi).1
      rw [List.length_take] at h
      omega
    have hsi : stored[i]? = some stored[i] := List.getElem?_eq_getElem (by omega)
    obtain ⟨f', hf', hcveq, -, -⟩ := hcvA i _ hilt hsi
    have hfi : fms[i]? = some f := by rw [← List.getElem?_take_of_lt hilt]; exact hi
    obtain rfl : f' = f := Option.some.inj (hf'.symm.trans hfi)
    exact ⟨stored[i], List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hilt]; exact hsi),
      by rw [hcveq]⟩
  have hfC : ∀ c ∈ ctorsR.flatten,
      (ConLeche.consNestedFormers (stored.take p.k) env).find? c.1.name = none := by
    intro c hc
    obtain ⟨cs, hcs, hcin⟩ := List.mem_flatten.mp hc
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hcs
    obtain ⟨hlenC, hallC⟩ := ConLeche.mapM_except_inv I.hctors
    obtain ⟨a, cs', ha, hcs', hrun⟩ := hallC j (by
      have h := (List.getElem?_eq_some_iff.mp hj).1
      omega)
    rw [hj] at hcs'
    obtain rfl : cs = cs' := by simpa using hcs'
    exact ConLeche.restoreCtors_fresh hrun c hcin
  have hrecMs : ∀ x ∈ nestedStoreList p stored cvRms cvRns rulesM rulesN, ∀ n : Name,
      x.1.name = n.str "rec" → n ∈ p.memberNames := by
    intro x hx n hn
    obtain ⟨c, hc, hcv, -, -, -⟩ := nestedStoreList_mem I.lenM hx
    have hcb : c < b.k := by rw [hbk, ← I.lenN]; exact hc
    rw [hcv] at hn
    by_cases hck : c < p.k
    · rw [I.recCvNameM hck] at hn
      unfold ConLeche.MutualBlock.recName at hn
      rw [I.memberNameAt hck] at hn
      obtain rfl : n = (p.formers.getD c default).1.name := ((ConLeche.Name.str.inj hn).1).symm
      have hpk : p.formers.length = p.k := rfl
      refine List.mem_map.mpr ⟨p.formers[c]'(by rw [hpk]; exact hck), List.getElem_mem _, ?_⟩
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hpk]; exact hck)]
      rfl
    · exfalso
      have hj : c - p.k < pinsS.length := by omega
      rw [show c = p.k + (c - p.k) from by omega, I.recCvNameN hj] at hn
      simp only [ConLeche.NestedParts.mimicRecName, ConLeche.Name.appendIndexAfter] at hn
      have hstr : "rec" ++ "_" ++ toString (c - p.k + 1) = "rec" := (ConLeche.Name.str.inj hn).2
      have hlen := congrArg String.length hstr
      rw [String.length_append, String.length_append] at hlen
      have h1 : "_".length = 1 := rfl
      omega
  rw [I.henv] at hfC
  have EF := consNestedFormers_installExt (Ms := p.memberNames) hmemFresh hmemMs
  rw [I.henv] at EF
  have EC := consNestedCtors_installExt (Ms := p.memberNames) (cs := ctorsR.flatten) hfC
  have ER := storeNestedRecs_installExt (Ms := p.memberNames)
    (l := nestedStoreList p stored cvRms cvRns rulesM rulesN)
    (fun x hx => (I.storeDoor x hx).1) hrecMs
  obtain ⟨newT, ET⟩ := nestedTables_installExt (Ms := p.memberNames) htblR
    (fun e he => by rw [← hTLnames]; exact List.mem_map_of_mem he)
  have EI := ((EF.trans EC).trans ER).trans ET
  have hMs : ∀ n ∈ p.memberNames,
      n ∈ (newT ++ ((((nestedStoreList p stored cvRms cvRns rulesM rulesN).map fun x =>
        ConstantInfo.recInfo x.1 x.2.1 x.2.2.1 x.2.2.2).reverse ++
        (((ctorsR.flatten.map fun c => ConstantInfo.ctorInfo c.1 c.2.1 c.2.2).reverse ++
          ((stored.take p.k).map fun a =>
            ConstantInfo.indInfo a.cvTa a.caps).reverse))))).map (·.name) := by
    intro n hn
    obtain ⟨a, ha, rfl⟩ := hmemStored n hn
    rw [List.map_append, List.mem_append]; right
    rw [List.map_append, List.mem_append]; right
    rw [List.map_append, List.mem_append]; right
    rw [List.map_reverse, List.mem_reverse, List.map_map]
    exact List.mem_map_of_mem ha
  have hMs₁₂ : ∀ n ∈ p.memberNames,
      n ∈ (((ctorsR.flatten.map fun c => ConstantInfo.ctorInfo c.1 c.2.1 c.2.2).reverse ++
        ((stored.take p.k).map fun a =>
          ConstantInfo.indInfo a.cvTa a.caps).reverse)).map (·.name) := by
    intro n hn
    obtain ⟨a, ha, rfl⟩ := hmemStored n hn
    rw [List.map_append, List.mem_append]; right
    rw [List.map_reverse, List.mem_reverse, List.map_map]
    exact List.mem_map_of_mem ha
  have hmemFreshN : ∀ n ∈ p.memberNames, env.find? n = none := by
    intro n hn
    obtain ⟨a, ha, rfl⟩ := hmemStored n hn
    exact hmemFresh a ha
  -- **the block's representation at the OUTPUT model**
  have hndP : ((nestedProvList p stored cvRms cvRns).map (·.1.name)).Nodup := by
    rw [nestedProvList_names I.lenM I.lenN I.storedLen hbk]
    exact I.recNodup
  have hFP := ConLeche.provisionNestedRecs_findPreserved (l := nestedProvList p stored cvRms cvRns)
    I.provListFresh
  have hagPs : ∀ n : Name, ((ConLeche.consNestedCtors ctorsR.flatten
      (ConLeche.consMutualFormers (fms.take p.k) env)).find? n).isSome = true →
      mpP.base2.acval n = mp₂.base2.acval n := by
    intro n hn
    refine hagP n fun t ht heq => ?_
    have hfr := (I.recCvDoor (by rw [← I.kT]; exact ht)).1
    rw [heq, hfr] at hn
    simp at hn
  have hrepsP : IsBlockModelsAt mpP.base2
      (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF
        xrestF eissF tssF ctorsR dsR xFvsR pinsS)
      (fun mm => (fms.getD mm default).cvTa) :=
    I.out.reps.crossEnv (fun n ci _ hf => hFP n ci hf)
      (constsResolve_of_findPreserved (fun {n} {c} h => hFP n c h)) hagPs
      (provisionNestedRecs_hde I.provListFresh hndP hagPs)
  have hreps₃ : IsBlockModelsAt mp₃.base2
      (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF
        xrestF eissF tssF ctorsR dsR xFvsR pinsS)
      (fun mm => (stored.getD mm default).cvTa) := by
    refine IsBlockModelsAt.congr (fun c hc => ?_)
      (hrepsP.crossEnv (fun n ci hnr hf => hcg.findUp n ci hf hnr)
        (constsResolve_of_swapCongr hcg) (fun n _ => congrFun hac₃ n) (swap_hde hcg hac₃))
    have hcp : c < p.k := hc
    have hsi : stored[c]? = some stored[c] := List.getElem?_eq_getElem (by omega)
    obtain ⟨f, hf, hcveq, -, -⟩ := hcvA c _ hcp hsi
    rw [List.getD_eq_getElem?_getD, hsi, List.getD_eq_getElem?_getD, hf]
    exact hcveq
  obtain ⟨isProp, SC, hTok⟩ := htbls mp p envOut st b envAux stored ctorsR cvRms cvRns rulesM
    rulesN fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF
    eissF tssF dsR xFvsR pinsS mp₂ I mp₃ hag₃ hreps₃
    (fun n ci hf => ER.toConsExt.ext n ci (EC.toConsExt.ext n ci hf))
  obtain ⟨mpOut, hagT⟩ := stageNestedTables (V := V) (μ := μ) blockTableStep (isProp := isProp)
    (S := SC) _ mp₃ htblR (by rw [hTLnames]; exact hndM) hTok
  -- **the agreements**
  have hagE : AcvalAgrees mp₂.base2 mpOut.base2 := by
    intro n hn
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hn
    rw [hagT n (by rw [ER.toConsExt.ext n c hc]; rfl), hac₃]
    refine hagP n fun t ht heq => ?_
    have hfr := (I.recCvDoor (by rw [← I.kT]; exact ht)).1
    rw [← heq, hc] at hfr
    exact nomatch hfr
  have hag₀ : AcvalAgrees mp.base2 mpOut.base2 := by
    intro n hn
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hn
    have hc₂ := EC.toConsExt.ext n c (EF.toConsExt.ext n c hc)
    refine (hagE n (by rw [hc₂]; rfl)).trans (I.out.stage.agreeR n (fun cR hcR heq => ?_)
      (fun t f ht hf heq => ?_))
    · have := hfC cR hcR
      rw [← heq, EF.toConsExt.ext n c hc] at this
      exact nomatch this
    · have hmem : f.cvTa.name ∈ p.memberNames := by
        rw [← I.out.stage.names]
        exact List.mem_map_of_mem
          (List.mem_of_getElem? (by rw [List.getElem?_take_of_lt ht]; exact hf))
      rw [← heq] at hmem
      rw [hmemFreshN n hmem] at hc
      exact nomatch hc
  have tcR : TableCross p.memberNames
      (ConLeche.storeNestedRecs (nestedStoreList p stored cvRms cvRns rulesM rulesN)
        (ConLeche.consNestedCtors ctorsR.flatten
          (ConLeche.consMutualFormers (fms.take p.k) env))) envOut :=
    nestedTables_cross _ htblR (fun e he => by rw [← hTLnames]; exact List.mem_map_of_mem he)
  have hdeT : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr), ProjFree p.memberNames e →
      ∀ {ea : AnnotTerm},
      denoteMeta mp₃.base2.acval
          (ConLeche.storeNestedRecs (nestedStoreList p stored cvRms cvRns rulesM rulesN)
            (ConLeche.consNestedCtors ctorsR.flatten
              (ConLeche.consMutualFormers (fms.take p.k) env))) ψ dp e = some ea →
        denoteMeta mpOut.base2.acval envOut ψ dp e = some ea := by
    intro ψ dp e hpf ea hr
    rw [denoteMeta_acval_congr (fun n hn => (hagT n hn).symm) dp e] at hr
    exact denoteMeta_env_mono_projFree tcR.find tcR.lit tcR.proj dp e hpf hr
  have hslotM : ∀ T ∈ p.memberNames, ∀ i : Nat,
      (ConLeche.consNestedFormers (stored.take p.k) env).findProj? T i = none := by
    intro T hT i
    rw [I.henv]
    exact findProj?_none_consMutualFormers
      (findProj?_none_of_indFresh mp.base2.proj_ok (hmemFreshN T hT) i)
  have hctorSlots : ∀ (mm j : Nat) (c : ConstantVal × Nat × Nat), mm < p.k →
      (ctorsR.getD mm [])[j]? = some c →
      ConLeche.Expr.ProjSlotsOk (ConLeche.consNestedFormers (stored.take p.k) env) c.1.type := by
    intro mm j c hmm hj
    obtain ⟨hlenC, hallC⟩ := ConLeche.mapM_except_inv I.hctors
    obtain ⟨a, cs, ha, hcs, hrun⟩ := hallC mm (by rw [List.length_take]; omega)
    have hcsD : ctorsR.getD mm [] = cs := by rw [List.getD_eq_getElem?_getD, hcs]; rfl
    rw [hcsD] at hj
    obtain ⟨hlenD, hallD⟩ := ConLeche.restoreCtors_door hrun
    obtain ⟨c0, hc0⟩ : ∃ c0, a.ctors[j]? = some c0 :=
      ⟨_, List.getElem?_eq_getElem (by
        have h := (List.getElem?_eq_some_iff.mp hj).1
        omega)⟩
    obtain ⟨ty, -, hfd, -, -⟩ := hallD j c0 c hc0 hj
    exact hfd.slots
  have hmemProj : ∀ c, c < p.k →
      ProjFree p.memberNames (stored.getD c default).cvTa.type := by
    intro c hc T hT i
    obtain ⟨-, hposF⟩ := mutualFormers_nameFacts I.out.formers
    have hsi : stored[c]? = some stored[c] := List.getElem?_eq_getElem (by omega)
    obtain ⟨f, hf, hcveq, -, -⟩ := hcvA c _ hc hsi
    have hgd : (stored.getD c default).cvTa = f.cvTa := by
      rw [List.getD_eq_getElem?_getD, hsi]
      exact hcveq
    rw [hgd]
    exact ConLeche.Expr.noProjAt_of_constsResolve (hmemFreshN T hT) _ (hposF c f hf).2.2.2.2.2
  have hrepsOut : IsBlockModelsAt mpOut.base2
      (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF
        xrestF eissF tssF ctorsR dsR xFvsR pinsS)
      (fun mm => (stored.getD mm default).cvTa) := by
    intro c hc
    obtain ⟨cvR, mI, rP, rules, hI⟩ := hreps₃ c hc
    refine ⟨cvR, mI, rP, rules, hI.crossEnvG (fun n ci _ hf => tcR.find hf)
      (constsResolve_of_findPreserved tcR.find) hagT hdeT (hmemProj c hc) ?_⟩
    intro mm' j cA hmm' hj
    rw [I.out.record.ctors mm' hmm', List.getElem?_map] at hj
    cases hcj : (ctorsR.getD mm' [])[j]? with
    | none => rw [hcj] at hj; exact nomatch hj
    | some cR =>
      rw [hcj] at hj
      obtain rfl : cA = (cR.1, cR.2.2) := (Option.some.inj hj).symm
      exact fun T hT i =>
        ConLeche.Expr.ProjSlotsOk.noProjAt (hslotM T hT i) _ (hctorSlots mm' j cR hmm' hcj)
  -- **the pins' containers**
  have hpinStored : ∀ q, q < pinsS.length → ∃ ci : ContainerInfo,
      ConLeche.containerInfo? env ((nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W
          idxF dsF esF srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS).pinAt q).J
        = some ci := by
    intro q hq
    have hql : q < st.pins.length := by rw [← I.out.record.nPins]; exact hq
    have hpq : st.pins[q]? = some st.pins[q] := List.getElem?_eq_getElem hql
    obtain ⟨hJ, -⟩ := I.out.record.pin q _ hpq
    obtain ⟨ci, hci, -⟩ := (ConLeche.nestedContainersOk_group I.hcont).2 _
      (List.mem_of_getElem? hpq)
    exact ⟨ci, by rw [hJ]; exact hci⟩
  have E₁₂ := EF.trans EC
  have hci₂ : ∀ (J : Name) (ci : ContainerInfo), ConLeche.containerInfo? env J = some ci →
      ConLeche.containerInfo? (ConLeche.consNestedCtors ctorsR.flatten
        (ConLeche.consMutualFormers (fms.take p.k) env)) J = some ci := by
    intro J ci hci
    obtain ⟨cv, caps, hf⟩ := containerInfo?_found hci
    rw [ConLeche.containerInfo?_ext_ind_eq E₁₂.toConsExt.ext E₁₂.toConsExt.newN
      E₁₂.toConsExt.freshN (E₁₂.recN hMs₁₂) mp.base2.wf mp.base2.rec_ctors
      (I := J) (fun hJ => by rw [E₁₂.toConsExt.freshN J hJ] at hf; exact nomatch hf)]
    exact hci
  have hciOut : ∀ (J : Name) (ci : ContainerInfo), ConLeche.containerInfo? env J = some ci →
      ConLeche.containerInfo? envOut J = some ci := by
    intro J ci hci
    obtain ⟨cv, caps, hf⟩ := containerInfo?_found hci
    rw [ConLeche.containerInfo?_ext_ind_eq EI.toConsExt.ext EI.toConsExt.newN
      EI.toConsExt.freshN (EI.recN hMs) mp.base2.wf mp.base2.rec_ctors
      (I := J) (fun hJ => by rw [EI.toConsExt.freshN J hJ] at hf; exact nomatch hf)]
    exact hci
  -- **the six fields** (integration 3q retired `groups`: the tail
  -- publishes `NestedStageFacts.groupsAt` and `declNested_of` reads it
  -- there, through `conts`' reading at the PRE-BLOCK environment)
  refine ⟨mpOut, ⟨_, EI, hMs⟩, hag₀, hagE, ?_, hrepsOut, ?_⟩
  · intro n c _ hf
    exact ET.toConsExt.ext n c (ER.toConsExt.ext n c hf)
  · intro q hq
    obtain ⟨ci₀, hci₀⟩ := hpinStored q hq
    exact ⟨ci₀, hci₂ _ _ hci₀, hciOut _ _ hci₀, hci₀⟩

/-- **THE RECORDED TABLES' FACE, DISCHARGED** (task #315 M7-2, DESIGN
§U.29 items 4 and 5): `NestedTablesDataOf` at every tail input, the
per-entry clause being `NestedTailIn.tablesData`.  The face's two
model-level hypotheses — the representation at `mp₃` and the store
environment's lookup preservation — are the ones the stage already
derives and passes in, so the transfer from the scratch install's
recorded tables to the nested route's model is a theorem and not a
premise. -/
theorem nestedTablesData_of {F : Nat} : NestedTablesDataOf V μ F := by
  intro env mp p envOut st b envAux stored ctorsR cvRms cvRns rulesM rulesN fmsA ctorsA₀ fms f₀
    ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF dsR xFvsR
    pinsS mp₂ I mp₃ hag₃ hreps₃ hfind₃
  exact ⟨_, _, I.tablesData mp₃ hag₃ hreps₃ hfind₃⟩

/-- **THE CONSUMER** (consumer-first): the recursors' stage of a nested
block closes `NestedTailModeled` — the readings and the equations are
K.36's alone (`nestedTailModeled_of_stage`), and the stage proper is
this lane's, modulo K.50; the recorded tables' data is now the
lane's own theorem (`nestedTablesData_of`). -/
theorem nestedTailModeled_of_two {F : Nat} (hbits : NestedRuleBitsOf μ F)
    (hK36 : NestedCtorPinNamesOf μ F) :
    NestedTailModeled V μ F :=
  nestedTailModeled_of_stage hK36 (nestedRecsStored_of hbits hK36 nestedTablesData_of)

end ConLeche.Model
