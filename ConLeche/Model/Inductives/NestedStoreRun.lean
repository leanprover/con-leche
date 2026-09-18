module

public import ConLeche.Model.Inductives.NestedRecRule
public import ConLeche.Verify.Inductives.NestedRecsWF
public section

/-!
# The restored recursors' STORE, at the run (task #315, M7-2, item 5 step 3b)

`nestedRecsStore` (`NestedRecsSwap.lean`) is generic in the list of
quadruples the kernel conses; this file is that list AT THE RUN — the
one `checkNested` builds — with the swap's per-entry premises read off
the run's own reports.

Three things happen here and nothing else:

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
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecFieldKind RecRule
  NestedParts MutualBlock AuxStored ElimState NestedPin IndCaps fueledOps)

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

end Run

end ConLeche.Model
