module

@[expose] public section

/-!
# Modular checking, for any consistency proof

The fragment's modular theorem (`modular`, `ModularInstance.lean`) has
two halves: a consistency proof for one environment, and the argument
that carries it from module to module.  This file is the second half,
stated over an interface (`ModularSemantics`) that says what the first
half must provide, so that the consistency proof can be swapped (for a
syntactic one, say) without redoing the argument.  It imports nothing.
The fragment's model is one instance (`ModularInstance.lean`), a
syntactic realisation another (`ModularSyntactic.lean`).

There is no global environment and no renaming.  Each module's
environments use the module's own names; what identifies a constant
across modules is its **key** (`Key`), which each module records for
every name it uses: the constant's **home**, the module that declares
it, or, for a proof, its statement.

**The interface.**  Environments, with the names they store
(`Stores`).  Then:

1. **models** (`Mod E`, a type of models, not a proposition), each
   giving every name a **value** (`val`), and one value every proof
   gets (`proofVal`);
2. **assembly** (`Assembled C E same`): an environment `C` is made of
   constants of a family `E` of environments, where `same n i` says
   which members count as having `C`'s constant `n`; every constant
   of `C` has such a member (`assembled_src`);
3. **amalgamation** (`amalgamate`): models of the family that agree
   wherever `C` counts two members as having the same constant (a
   **compatible** family) give one model of `C`, with each member's
   values;
4. **the conservative step** (`step`): if the checker accepts
   declarations `D` over `Γ`, giving `Γ'`, every model of `Γ` extends
   to one of `Γ'` with the same values on `Γ`, and every declaration
   `D` flags as a proof gets the proofs' value.

**Refinement** (`Refines Γ E`: every constant of `Γ` is, at the same
name, one of `E` or an assumption of its type) is assembly from one
environment, and **restriction** (`restrict`) is amalgamation of one
model.  A model of the empty environment is amalgamation of the empty
family.

**Why models must be data.**  A predicate "has a model" is too weak:
let `Γ` assume `c : Nat`, let an import `W` define `c := 5`, and let
`D` add the axiom `c = 0`.  Then `Γ + D` and `W` both have models, but
a module that reads both `W` and `D` has none.  What excludes `D` is
that the step must extend *every* model of `Γ`, including the one
amalgamated from `W`'s, where `c` is `5`.

**The theorem** (`Development.modular`).  A development has, per
module, its context, declarations, own environment, the **views** it
presents to its importers, the modules it imports, and its keys.  A
module is **valid** (`Development.Valid`) if each of its views refines
its own environment, it imports only earlier modules, and either it is
**checked** — its context is assembled from its imports' views, its
declarations are accepted over the context, and every new name is
keyed by the module itself or is a flagged proof — or it is
**compared** — its own environment is assembled from its imports'
views.  If every module is valid, there is a **compatible family** of
models, one of each module's own environment: two modules that store
a name under one key give it one value, and every proof key gets the
proofs' value.  The proof goes module by module: the imports' models,
restricted to their views, are compatible, so they amalgamate to a
model of the context; the step extends it over the declarations; and
the module's new constants carry new keys or are proofs, so the family
stays compatible.  Each module's model is built from its imports'
models alone.
-/

namespace Fragment

universe u w v

/-- **The key of a constant**, what identifies it across modules: the
module that declares it (its **home**), or, for a proof, its
statement. -/
inductive Key (Stmt : Type v) where
  | home (module : Nat)
  | proof (stmt : Stmt)

/-- **What a consistency proof provides for modular checking** (see the
module docstring). -/
structure ModularSemantics where
  /-- environments -/
  Env : Type u
  /-- names -/
  Name : Type u
  /-- the names an environment stores -/
  Stores : Env → Name → Prop
  /-- **the models** of an environment -/
  Mod : Env → Type w
  /-- values -/
  Val : Type w
  /-- **the value** a model gives a name -/
  val : ∀ {E : Env}, Mod E → Name → Val
  /-- **the value of every proof** -/
  proofVal : Val
  /-- **assembly**: `C` is made of constants of the family `E`, the
  member `i` counting as having `C`'s constant `n` when `same n i` -/
  Assembled : Env → ∀ {ι : Type u}, (ι → Env) → (Name → ι → Prop) → Prop
  /-- every constant of an assembled environment has a member that has
  it -/
  assembled_src : ∀ {C : Env} {ι : Type u} {E : ι → Env} {same : Name → ι → Prop},
    Assembled C E same → ∀ n, Stores C n → ∃ i, same n i ∧ Stores (E i) n
  /-- **amalgamation** of a compatible family -/
  amalgamate : ∀ {C : Env} {ι : Type u} {E : ι → Env} {same : Name → ι → Prop},
    Assembled C E same → ∀ m : (i : ι) → Mod (E i),
    (∀ n i i', Stores C n → same n i → same n i' → Stores (E i) n → Stores (E i') n →
      val (m i) n = val (m i') n) →
    ∃ mC : Mod C, ∀ n i, Stores C n → same n i → Stores (E i) n → val mC n = val (m i) n
  /-- declarations -/
  Decls : Type u
  /-- the names declarations flag as proofs -/
  Flagged : Decls → Name → Prop
  /-- **acceptance**: the checker accepts `D` over `Γ`, giving `Γ'` -/
  Accepts : Env → Decls → Env → Prop
  /-- **the conservative step** -/
  step : ∀ {Γ Γ' : Env} {D : Decls}, Accepts Γ D Γ' → ∀ m : Mod Γ,
    ∃ m' : Mod Γ', (∀ n, Stores Γ n → val m' n = val m n) ∧
      ∀ n, Flagged D n → val m' n = proofVal

namespace ModularSemantics

variable (S : ModularSemantics.{u, w})

/-- **Refinement**: `Γ` is assembled from `E` alone, every name counted
as `E`'s. -/
def Refines (Γ E : S.Env) : Prop := S.Assembled Γ (fun _ : PUnit.{u + 1} => E) fun _ _ => True

variable {S}

theorem Refines.stores {Γ E : S.Env} (h : S.Refines Γ E) {n : S.Name} (hn : S.Stores Γ n) :
    S.Stores E n := by
  obtain ⟨_, -, h⟩ := S.assembled_src h n hn
  exact h

/-- **Restriction**: a model of `E` gives one of every refinement of
`E`, with the same values. -/
theorem restrict {Γ E : S.Env} (h : S.Refines Γ E) (m : S.Mod E) :
    ∃ m' : S.Mod Γ, ∀ n, S.Stores Γ n → S.val m' n = S.val m n := by
  obtain ⟨m', hm'⟩ := S.amalgamate h (fun _ => m) fun _ _ _ _ _ _ _ _ => rfl
  exact ⟨m', fun n hn => hm' n ⟨⟩ hn trivial (h.stores hn)⟩

end ModularSemantics

variable {S : ModularSemantics.{u, w}} {Stmt : Type v}

/-- **A development** over `S`: per module its context, declarations,
own environment, the views it presents to its importers, the modules
it imports, and the key of each name it uses. -/
structure Development (S : ModularSemantics.{u, w}) (Stmt : Type v) where
  ctx : Nat → S.Env
  decls : Nat → S.Decls
  own : Nat → S.Env
  views : Nat → List S.Env
  imports : Nat → List Nat
  key : Nat → S.Name → Key Stmt

namespace Development

variable (dev : Development S Stmt)

/-- The views module `i` reads: a view of one of its imports. -/
def Src (i : Nat) : Type u := {x : Nat × S.Env // x.1 ∈ dev.imports i ∧ x.2 ∈ dev.views x.1}

/-- **Assembled from the imports' views**: a constant of `E` counts as a
view's when module `i` and the view's module give its name one key. -/
def Assembled (i : Nat) (E : S.Env) : Prop :=
  S.Assembled E (fun x : dev.Src i => x.1.2) fun n x => dev.key i n = dev.key x.1.1 n

/-- **The new names are keyed by the module, or flagged proofs.** -/
def NewKeys (i : Nat) : Prop :=
  ∀ n, S.Stores (dev.own i) n → ¬ S.Stores (dev.ctx i) n →
    dev.key i n = .home i ∨ (∃ s, dev.key i n = .proof s) ∧ S.Flagged (dev.decls i) n

/-- **A checked module**: its context assembled from its imports' views,
its declarations accepted over it, its new names keyed by it or
flagged proofs. -/
def Checked (i : Nat) : Prop :=
  dev.Assembled i (dev.ctx i) ∧ S.Accepts (dev.ctx i) (dev.decls i) (dev.own i) ∧ dev.NewKeys i

/-- **A compared module**: its own environment assembled from its
imports' views. -/
def Compared (i : Nat) : Prop := dev.Assembled i (dev.own i)

/-- **A valid module**: its views refine its own environment, it imports
earlier modules, and it is checked or compared. -/
structure Valid (i : Nat) : Prop where
  views : ∀ E ∈ dev.views i, S.Refines E (dev.own i)
  imports : ∀ j ∈ dev.imports i, j < i
  checked_or_compared : dev.Checked i ∨ dev.Compared i

/-- **A compatible family** of models below `k`: two modules that store
a name under one key give it one value, and a proof key gets the
proofs' value. -/
def Compatible (k : Nat) (m : (i : Nat) → i < k → S.Mod (dev.own i)) : Prop :=
  (∀ i i' (hi : i < k) (hi' : i' < k) n, S.Stores (dev.own i) n → S.Stores (dev.own i') n →
    dev.key i n = dev.key i' n → S.val (m i hi) n = S.val (m i' hi') n) ∧
  ∀ i (hi : i < k) n s, S.Stores (dev.own i) n → dev.key i n = .proof s →
    S.val (m i hi) n = S.proofVal

variable {dev}

/-- **What a valid module stores**: a constant of one of its imports'
views, under that import's key, or a new one. -/
theorem Valid.src {i : Nat} (hv : dev.Valid i) {n : S.Name} (hn : S.Stores (dev.own i) n) :
    (∃ x : dev.Src i, dev.key i n = dev.key x.1.1 n ∧ S.Stores x.1.2 n ∧
      (dev.Compared i ∨ dev.Checked i ∧ S.Stores (dev.ctx i) n)) ∨
    dev.Checked i ∧ ¬ S.Stores (dev.ctx i) n := by
  rcases hv.checked_or_compared with hc | hc
  · by_cases hC : S.Stores (dev.ctx i) n
    · obtain ⟨x, hx, hs⟩ := S.assembled_src hc.1 n hC
      exact .inl ⟨x, hx, hs, .inr ⟨hc, hC⟩⟩
    · exact .inr ⟨hc, hC⟩
  · obtain ⟨x, hx, hs⟩ := S.assembled_src hc n hn
    exact .inl ⟨x, hx, hs, .inl hc⟩

/-- **A module's homes are itself or earlier modules.** -/
theorem home_le : ∀ i, (∀ j ≤ i, dev.Valid j) →
    ∀ n h, S.Stores (dev.own i) n → dev.key i n = .home h → h ≤ i := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
  intro hv n h hn hk
  have hvi := hv i (Nat.le_refl i)
  rcases hvi.src hn with ⟨⟨⟨j, E⟩, hj, hE⟩, hx, hs, -⟩ | ⟨⟨-, -, hnew⟩, hC⟩
  · have hji : j < i := hvi.imports j hj
    have := ih j hji (fun j' hj' => hv j' (by omega)) n h
      ((hv j (Nat.le_of_lt hji)).views E hE |>.stores hs) (hx.symm.trans hk)
    omega
  · rcases hnew n hn hC with he | ⟨⟨s, hs⟩, -⟩
    · rw [hk] at he; cases he; exact Nat.le_refl i
    · rw [hk] at hs; cases hs

/-- A family below `k` extended by one member at `k`. -/
def extendFam {P : Nat → Sort w} {k : Nat} (m : (i : Nat) → i < k → P i) (x : P k) :
    (i : Nat) → i < k + 1 → P i :=
  fun i hi => if h : i < k then m i h else
    (Nat.le_antisymm (Nat.not_lt.mp h) (Nat.le_of_lt_succ hi) : k = i) ▸ x

theorem extendFam_lt {P : Nat → Sort w} {k : Nat} (m : (i : Nat) → i < k → P i) (x : P k)
    {i : Nat} (hi : i < k + 1) (h : i < k) : extendFam m x i hi = m i h := dite_eq_left h

theorem extendFam_self {P : Nat → Sort w} {k : Nat} (m : (i : Nat) → i < k → P i) (x : P k)
    (hk : k < k + 1) : extendFam m x k hk = x := dite_eq_right (Nat.lt_irrefl k)

/-- **The modular theorem, for any consistency proof**: if every module
below `k` is valid, there is a compatible family of models, one of each
module's own environment. -/
theorem modular : ∀ k, (∀ i < k, dev.Valid i) →
    ∃ m : (i : Nat) → i < k → S.Mod (dev.own i), dev.Compatible k m
  | 0, _ => ⟨fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1, hv => by
    obtain ⟨m, hc, hp⟩ := modular k fun i hi => hv i (Nat.lt_succ_of_lt hi)
    have hk := hv k (Nat.lt_succ_self k)
    have hlt : ∀ x : dev.Src k, x.1.1 < k := fun x => hk.imports _ x.2.1
    -- the imports' models, restricted to their views
    have hview : ∀ x : dev.Src k, ∃ mv : S.Mod x.1.2, ∀ n, S.Stores x.1.2 n →
        S.Stores (dev.own x.1.1) n ∧ S.val mv n = S.val (m x.1.1 (hlt x)) n := by
      intro x
      have hr := (hv x.1.1 (Nat.lt_succ_of_lt (hlt x))).views x.1.2 x.2.2
      obtain ⟨mv, hmv⟩ := ModularSemantics.restrict hr (m x.1.1 (hlt x))
      exact ⟨mv, fun n hn => ⟨hr.stores hn, hmv n hn⟩⟩
    obtain ⟨fam, hfam⟩ := Classical.axiomOfChoice hview
    -- they are compatible, so they amalgamate
    have hcomp : ∀ (C : S.Env) n (x x' : dev.Src k), S.Stores C n → dev.key k n = dev.key x.1.1 n →
        dev.key k n = dev.key x'.1.1 n → S.Stores x.1.2 n → S.Stores x'.1.2 n →
        S.val (fam x) n = S.val (fam x') n := by
      intro C n x x' _ hx hx' hs hs'
      obtain ⟨ho, he⟩ := hfam x n hs
      obtain ⟨ho', he'⟩ := hfam x' n hs'
      rw [he, he']
      exact hc _ _ _ _ n ho ho' (hx.symm.trans hx')
    -- the model of the module's own environment, and where its values come from
    obtain ⟨mk, hmk⟩ : ∃ mk : S.Mod (dev.own k), ∀ n, S.Stores (dev.own k) n →
        (∃ x : dev.Src k, dev.key k n = dev.key x.1.1 n ∧ S.Stores x.1.2 n ∧
          S.val mk n = S.val (fam x) n) ∨
        (dev.key k n = .home k ∨ (∃ s, dev.key k n = .proof s) ∧ S.val mk n = S.proofVal) := by
      rcases hk.checked_or_compared with ⟨hA, hacc, hnew⟩ | hA
      · obtain ⟨mC, hmC⟩ := S.amalgamate hA fam fun n x x' hn => hcomp _ n x x' hn
        obtain ⟨mk, hag, hfl⟩ := S.step hacc mC
        refine ⟨mk, fun n hn => ?_⟩
        by_cases hC : S.Stores (dev.ctx k) n
        · obtain ⟨x, hx, hs⟩ := S.assembled_src hA n hC
          exact .inl ⟨x, hx, hs, (hag n hC).trans (hmC n x hC hx hs)⟩
        · rcases hnew n hn hC with h | ⟨hs, hf⟩
          · exact .inr (.inl h)
          · exact .inr (.inr ⟨hs, hfl n hf⟩)
      · obtain ⟨mk, hmk⟩ := S.amalgamate hA fam fun n x x' hn => hcomp _ n x x' hn
        refine ⟨mk, fun n hn => ?_⟩
        obtain ⟨x, hx, hs⟩ := S.assembled_src hA n hn
        exact .inl ⟨x, hx, hs, hmk n x hn hx hs⟩
    have hhome := home_le (dev := dev)
    -- the new module against an earlier one
    have hnew : ∀ i' (hi' : i' < k) n, S.Stores (dev.own k) n → S.Stores (dev.own i') n →
        dev.key k n = dev.key i' n → S.val mk n = S.val (m i' hi') n := by
      intro i' hi' n hn hn' hkey
      rcases hmk n hn with ⟨x, hx, hs, he⟩ | h | ⟨⟨s, hs⟩, he⟩
      · obtain ⟨ho, he'⟩ := hfam x n hs
        rw [he, he']
        exact hc _ _ _ _ n ho hn' (hx.symm.trans hkey)
      · exfalso
        have := hhome i' (fun j hj => hv j (by omega)) n k hn' (hkey.symm.trans h)
        omega
      · rw [he, hp i' hi' n s hn' (hkey.symm.trans hs)]
    refine ⟨extendFam m mk, fun i i' hi hi' n hn hn' hkey => ?_, fun i hi n s hn hs => ?_⟩
    · by_cases h : i < k
      · by_cases h' : i' < k
        · rw [extendFam_lt m mk hi h, extendFam_lt m mk hi' h']
          exact hc i i' h h' n hn hn' hkey
        · obtain rfl : k = i' := by omega
          rw [extendFam_lt m mk hi h, extendFam_self m mk hi']
          exact (hnew i h n hn' hn hkey.symm).symm
      · obtain rfl : k = i := by omega
        by_cases h' : i' < k
        · rw [extendFam_self m mk hi, extendFam_lt m mk hi' h']
          exact hnew i' h' n hn hn' hkey
        · obtain rfl : k = i' := by omega
          rfl
    · by_cases h : i < k
      · rw [extendFam_lt m mk hi h]
        exact hp i h n s hn hs
      · obtain rfl : k = i := by omega
        rw [extendFam_self m mk hi]
        rcases hmk n hn with ⟨x, hx, hs', he⟩ | h | ⟨-, he⟩
        · obtain ⟨ho, he'⟩ := hfam x n hs'
          rw [he, he']
          exact hp _ _ n s ho (hx.symm.trans hs)
        · rw [hs] at h; cases h
        · exact he

/-- **Every valid module's own environment has a model.** -/
theorem own_model (k : Nat) (hv : ∀ i < k, dev.Valid i) :
    ∀ i < k, Nonempty (S.Mod (dev.own i)) := by
  obtain ⟨m, -⟩ := dev.modular k hv
  exact fun i hi => ⟨m i hi⟩

end Development

end Fragment
