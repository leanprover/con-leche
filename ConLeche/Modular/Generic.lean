module

@[expose] public section

/-!
# The modular argument, over an interface of models

The modular theorem (`ConLeche.modular_model_exists`) has two halves:
a consistency proof for one environment, and the argument that carries
it from module to module.  This file is the second half, stated over an
interface (`ModularSemantics`) that says what the first half must
provide.  The interface gives every proof one shared value, which suits
set models; whether it suits another consistency proof is open.  It
imports nothing; it is the
interface and theorem of the proof-idea paper's fragment
(`whitepaper/Fragment/ModularSemantics.lean`), and con-leche's graded
models are an instance (`ConLeche/Model/Modular/Instance.lean`).

There is no global environment and no renaming.  Each module's
environments use the module's own names.  Two modules' occurrences of a
name are **interchangeable** (`Development.Interchangeable`) when both
were declared by one module, or both are proofs of one statement; each
module records, for every name it uses, the module that declared it or
the proof's statement (`Key`, an internal representation of the
relation).

**The interface.**  Environments, with the names they store
(`Stores`; `c ∈ E` below).  Then:

1. **models** (`Mod E`, a type of models, not a proposition), each
   giving every name a **value** (`val`; `m(c)` below), and one value
   every proof gets (`proofVal`);
2. **assembly** (`Assembled C E`): an environment `C` is made of
   constants of a family `E` of environments, every constant of `C`
   coming from a member that stores it (`assembled_src`);
3. **amalgamation** (`amalgamate`): models of the family that pairwise
   **agree on `C`** (`ModelsAgree`: equal values at every name of `C` both
   members store) give one model of `C` that agrees on `C` with every
   member;
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
module, its context, declarations, own environment, its **sources**
(the views of earlier modules it reads, each with the module that
presents it), and what declared each of its names.  A module is
**valid** (`Development.Valid`) if each source's view refines its
module's own environment and comes from an earlier module, and either
it is **checked** — its context is assembled from its sources, every
copy of a context name in a source is interchangeable with the
module's (`OneCopy`), its declarations are accepted over the context,
and every new name is declared by the module itself or is a flagged
proof — or it is **compared** — its own environment is assembled from
its sources, with one copy in the same sense.  If every module is
valid, there is a **compatible family** of models, one of each
module's own environment: interchangeable occurrences of a name get one
value, and every proof gets the proofs' value.  The proof goes module
by module: the earlier modules' models, restricted to the sources'
views, are compatible for the context (the copies a source stores are
interchangeable with the module's), so they amalgamate to a model of
the context; the step extends it over the declarations; and the
module's new constants are declared by it or are proofs, so the family
stays compatible.  Each module's model is built from its sources'
models alone.
-/

namespace ConLeche.Modular

universe u w v

/-- **What declared a name**, as a module records it: the module that
declared it (its **home**), or, for a proof, its statement.  The
internal representation of interchangeability
(`Development.Interchangeable`). -/
inductive Key (Stmt : Type v) where
  | home (module : Nat)
  | proof (stmt : Stmt)
  deriving DecidableEq, Repr

/-- **Agreement on `C`** (`m ≍_C m'` in the paper): models `m` of `E`
and `m'` of `E'` give the same value to every name of `C` that `E` and
`E'` both store. -/
def ModelsAgree {Env Name : Type u} {Mod : Env → Type w} {Val : Type w}
    (Stores : Env → Name → Prop) (val : ∀ {E : Env}, Mod E → Name → Val)
    (C : Env) {E E' : Env} (m : Mod E) (m' : Mod E') : Prop :=
  ∀ n, Stores C n → Stores E n → Stores E' n → val m n = val m' n

/-- **What a consistency proof provides for modular checking** (see the
module docstring). -/
structure ModularSemantics where
  /-- environments -/
  Env : Type u
  /-- names -/
  Name : Type u
  /-- the names an environment stores (`c ∈ E`) -/
  Stores : Env → Name → Prop
  /-- **the models** of an environment -/
  Mod : Env → Type w
  /-- values -/
  Val : Type w
  /-- **the value** a model gives a name -/
  val : ∀ {E : Env}, Mod E → Name → Val
  /-- **the value of every proof** -/
  proofVal : Val
  /-- **assembly**: `C` is made of constants of the family `E` -/
  Assembled : Env → ∀ {ι : Type u}, (ι → Env) → Prop
  /-- every constant of an assembled environment comes from a member
  that stores it -/
  assembled_src : ∀ {C : Env} {ι : Type u} {E : ι → Env},
    Assembled C E → ∀ n, Stores C n → ∃ i, Stores (E i) n
  /-- **amalgamation** of a family that pairwise agrees on `C` -/
  amalgamate : ∀ {C : Env} {ι : Type u} {E : ι → Env},
    Assembled C E → ∀ m : (i : ι) → Mod (E i),
    (∀ i i', ModelsAgree Stores @val C (m i) (m i')) →
    ∃ mC : Mod C, ∀ i, ModelsAgree Stores @val C mC (m i)
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

/-- **Refinement**: `Γ` is assembled from `E` alone. -/
def Refines (Γ E : S.Env) : Prop := S.Assembled Γ fun _ : PUnit.{u + 1} => E

variable {S}

theorem Refines.stores {Γ E : S.Env} (h : S.Refines Γ E) {n : S.Name} (hn : S.Stores Γ n) :
    S.Stores E n := by
  obtain ⟨_, h⟩ := S.assembled_src h n hn
  exact h

/-- **Restriction**: a model of `E` gives one of every refinement of
`E`, with the same values. -/
theorem restrict {Γ E : S.Env} (h : S.Refines Γ E) (m : S.Mod E) :
    ∃ m' : S.Mod Γ, ∀ n, S.Stores Γ n → S.val m' n = S.val m n := by
  obtain ⟨m', hm'⟩ := S.amalgamate h (fun _ => m) fun _ _ _ _ _ _ => rfl
  exact ⟨m', fun n hn => hm' ⟨⟩ n hn hn (h.stores hn)⟩

end ModularSemantics

variable {S : ModularSemantics.{u, w}} {Stmt : Type v}

/-- **A development** over `S`: per module its context, declarations,
own environment, its sources (the views it reads, each with the module
that presents it), and what declared each name it uses. -/
structure Development (S : ModularSemantics.{u, w}) (Stmt : Type v) where
  ctx : Nat → S.Env
  decls : Nat → S.Decls
  own : Nat → S.Env
  sources : Nat → List (Nat × S.Env)
  key : Nat → S.Name → Key Stmt

namespace Development

variable (dev : Development S Stmt)

/-- Module `i`'s `n` was **declared by** module `h`. -/
def DeclaredBy (i : Nat) (n : S.Name) (h : Nat) : Prop := dev.key i n = .home h

/-- Module `i`'s `n` is **a proof of** the statement `s`. -/
def ProofOf (i : Nat) (n : S.Name) (s : Stmt) : Prop := dev.key i n = .proof s

/-- **Interchangeable occurrences**: modules `i` and `j`'s occurrences
of `n` were both declared by one module, or both are proofs of one
statement. -/
def Interchangeable (i j : Nat) (n : S.Name) : Prop :=
  (∃ h, dev.DeclaredBy i n h ∧ dev.DeclaredBy j n h) ∨
    ∃ s, dev.ProofOf i n s ∧ dev.ProofOf j n s

variable {dev}

theorem interchangeable_iff {i j : Nat} {n : S.Name} :
    dev.Interchangeable i j n ↔ dev.key i n = dev.key j n := by
  unfold Interchangeable DeclaredBy ProofOf
  constructor
  · rintro (⟨h, h1, h2⟩ | ⟨s, h1, h2⟩) <;> rw [h1, h2]
  · intro he
    cases hk : dev.key i n with
    | home h => exact .inl ⟨h, rfl, he ▸ hk⟩
    | proof s => exact .inr ⟨s, rfl, he ▸ hk⟩

/-- **Interchangeability is an equivalence** (for each name). -/
theorem interchangeable_equivalence (n : S.Name) :
    Equivalence fun i j => dev.Interchangeable i j n :=
  ⟨fun _ => interchangeable_iff.mpr rfl,
    fun h => interchangeable_iff.mpr (interchangeable_iff.mp h).symm,
    fun h h' => interchangeable_iff.mpr ((interchangeable_iff.mp h).trans
      (interchangeable_iff.mp h'))⟩

variable (dev)

/-- The sources module `i` reads. -/
def Src (i : Nat) : Type u := {x : Nat × S.Env // x ∈ dev.sources i}

/-- **Assembled from the sources.** -/
def Assembled (i : Nat) (E : S.Env) : Prop := S.Assembled E fun x : dev.Src i => x.1.2

/-- **One copy**: every copy of a name of `E` in a source of module `i`
is interchangeable with module `i`'s occurrence. -/
def OneCopy (i : Nat) (E : S.Env) : Prop :=
  ∀ n, S.Stores E n → ∀ x ∈ dev.sources i, S.Stores x.2 n → dev.Interchangeable i x.1 n

/-- **The new names are declared by the module, or flagged proofs.** -/
def NewNames (i : Nat) : Prop :=
  ∀ n, S.Stores (dev.own i) n → ¬ S.Stores (dev.ctx i) n →
    dev.DeclaredBy i n i ∨ (∃ s, dev.ProofOf i n s) ∧ S.Flagged (dev.decls i) n

/-- **A checked module**: its context assembled from its sources, with
one copy of each name, its declarations accepted over it, its new
names declared by it or flagged proofs. -/
def Checked (i : Nat) : Prop :=
  dev.Assembled i (dev.ctx i) ∧ dev.OneCopy i (dev.ctx i) ∧
    S.Accepts (dev.ctx i) (dev.decls i) (dev.own i) ∧ dev.NewNames i

/-- **A compared module**: its own environment assembled from its
sources, with one copy of each name. -/
def Compared (i : Nat) : Prop := dev.Assembled i (dev.own i) ∧ dev.OneCopy i (dev.own i)

/-- **A valid module**: each source is a view of an earlier module that
refines its own environment, and the module is checked or compared. -/
structure Valid (i : Nat) : Prop where
  sources : ∀ x ∈ dev.sources i, x.1 < i ∧ S.Refines x.2 (dev.own x.1)
  checked_or_compared : dev.Checked i ∨ dev.Compared i

/-- **A compatible family** of models below `k`: interchangeable
occurrences of a name get one value, and a proof gets the proofs'
value. -/
def Compatible (k : Nat) (m : (i : Nat) → i < k → S.Mod (dev.own i)) : Prop :=
  (∀ i i' (hi : i < k) (hi' : i' < k) n, S.Stores (dev.own i) n → S.Stores (dev.own i') n →
    dev.Interchangeable i i' n → S.val (m i hi) n = S.val (m i' hi') n) ∧
  ∀ i (hi : i < k) n s, S.Stores (dev.own i) n → dev.ProofOf i n s →
    S.val (m i hi) n = S.proofVal

variable {dev}

/-- **What a valid module stores**: a constant of one of its sources,
interchangeable with the source module's, or a new one. -/
theorem Valid.src {i : Nat} (hv : dev.Valid i) {n : S.Name} (hn : S.Stores (dev.own i) n) :
    (∃ x : dev.Src i, dev.key i n = dev.key x.1.1 n ∧ S.Stores x.1.2 n ∧
      (dev.Compared i ∨ dev.Checked i ∧ S.Stores (dev.ctx i) n)) ∨
    dev.Checked i ∧ ¬ S.Stores (dev.ctx i) n := by
  rcases hv.checked_or_compared with hc | hc
  · by_cases hC : S.Stores (dev.ctx i) n
    · obtain ⟨x, hs⟩ := S.assembled_src hc.1 n hC
      exact .inl ⟨x, interchangeable_iff.mp (hc.2.1 n hC x.1 x.2 hs), hs, .inr ⟨hc, hC⟩⟩
    · exact .inr ⟨hc, hC⟩
  · obtain ⟨x, hs⟩ := S.assembled_src hc.1 n hn
    exact .inl ⟨x, interchangeable_iff.mp (hc.2 n hn x.1 x.2 hs), hs, .inl hc⟩

/-- **A module's names are declared by itself or earlier modules.** -/
theorem home_le : ∀ i, (∀ j ≤ i, dev.Valid j) →
    ∀ n h, S.Stores (dev.own i) n → dev.key i n = .home h → h ≤ i := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
  intro hv n h hn hk
  have hvi := hv i (Nat.le_refl i)
  rcases hvi.src hn with ⟨⟨⟨j, E⟩, hjE⟩, hx, hs, -⟩ | ⟨⟨-, -, -, hnew⟩, hC⟩
  · obtain ⟨hji, hr⟩ := hvi.sources _ hjE
    have := ih j hji (fun j' hj' => hv j' (by omega)) n h (hr.stores hs) (hx.symm.trans hk)
    omega
  · rcases hnew n hn hC with he | ⟨⟨s, hs⟩, -⟩
    · unfold DeclaredBy at he; rw [hk] at he; cases he; exact Nat.le_refl i
    · unfold ProofOf at hs; rw [hk] at hs; cases hs

/-- A family below `k` extended by one member at `k`. -/
def extendFam {P : Nat → Sort w} {k : Nat} (m : (i : Nat) → i < k → P i) (x : P k) :
    (i : Nat) → i < k + 1 → P i :=
  fun i hi => if h : i < k then m i h else
    (Nat.le_antisymm (Nat.not_lt.mp h) (Nat.le_of_lt_succ hi) : k = i) ▸ x

theorem extendFam_lt {P : Nat → Sort w} {k : Nat} (m : (i : Nat) → i < k → P i) (x : P k)
    {i : Nat} (hi : i < k + 1) (h : i < k) : extendFam m x i hi = m i h := dite_eq_left h

theorem extendFam_self {P : Nat → Sort w} {k : Nat} (m : (i : Nat) → i < k → P i) (x : P k)
    (hk : k < k + 1) : extendFam m x k hk = x := dite_eq_right (Nat.lt_irrefl k)

/-- **The modular theorem, over the interface**: if every module
below `k` is valid, there is a compatible family of models, one of each
module's own environment. -/
theorem modular : ∀ k, (∀ i < k, dev.Valid i) →
    ∃ m : (i : Nat) → i < k → S.Mod (dev.own i), dev.Compatible k m
  | 0, _ => ⟨fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1, hv => by
    obtain ⟨m, hc, hp⟩ := modular k fun i hi => hv i (Nat.lt_succ_of_lt hi)
    have hc : ∀ i i' (hi : i < k) (hi' : i' < k) n, S.Stores (dev.own i) n →
        S.Stores (dev.own i') n → dev.key i n = dev.key i' n →
        S.val (m i hi) n = S.val (m i' hi') n :=
      fun i i' hi hi' n hn hn' he => hc i i' hi hi' n hn hn' (interchangeable_iff.mpr he)
    have hk := hv k (Nat.lt_succ_self k)
    have hlt : ∀ x : dev.Src k, x.1.1 < k := fun x => (hk.sources _ x.2).1
    -- the earlier modules' models, restricted to the sources' views
    have hview : ∀ x : dev.Src k, ∃ mv : S.Mod x.1.2, ∀ n, S.Stores x.1.2 n →
        S.Stores (dev.own x.1.1) n ∧ S.val mv n = S.val (m x.1.1 (hlt x)) n := by
      intro x
      have hr := (hk.sources _ x.2).2
      obtain ⟨mv, hmv⟩ := ModularSemantics.restrict hr (m x.1.1 (hlt x))
      exact ⟨mv, fun n hn => ⟨hr.stores hn, hmv n hn⟩⟩
    obtain ⟨fam, hfam⟩ := Classical.axiomOfChoice hview
    -- with one copy of each name, they agree on `C`, so they amalgamate
    have hcomp : ∀ (C : S.Env), dev.OneCopy k C → ∀ x x' : dev.Src k,
        ModelsAgree S.Stores @S.val C (fam x) (fam x') := by
      intro C h1 x x' n hn hs hs'
      obtain ⟨ho, he⟩ := hfam x n hs
      obtain ⟨ho', he'⟩ := hfam x' n hs'
      rw [he, he']
      exact hc _ _ _ _ n ho ho' ((interchangeable_iff.mp (h1 n hn x.1 x.2 hs)).symm.trans
        (interchangeable_iff.mp (h1 n hn x'.1 x'.2 hs')))
    -- the model of the module's own environment, and where its values come from
    obtain ⟨mk, hmk⟩ : ∃ mk : S.Mod (dev.own k), ∀ n, S.Stores (dev.own k) n →
        (∃ x : dev.Src k, dev.key k n = dev.key x.1.1 n ∧ S.Stores x.1.2 n ∧
          S.val mk n = S.val (fam x) n) ∨
        (dev.key k n = .home k ∨ (∃ s, dev.key k n = .proof s) ∧ S.val mk n = S.proofVal) := by
      rcases hk.checked_or_compared with ⟨hA, h1, hacc, hnew⟩ | ⟨hA, h1⟩
      · obtain ⟨mC, hmC⟩ := S.amalgamate hA fam (hcomp _ h1)
        obtain ⟨mk, hag, hfl⟩ := S.step hacc mC
        refine ⟨mk, fun n hn => ?_⟩
        by_cases hC : S.Stores (dev.ctx k) n
        · obtain ⟨x, hs⟩ := S.assembled_src hA n hC
          exact .inl ⟨x, interchangeable_iff.mp (h1 n hC x.1 x.2 hs), hs,
            (hag n hC).trans (hmC x n hC hC hs)⟩
        · rcases hnew n hn hC with h | ⟨hs, hf⟩
          · exact .inr (.inl h)
          · exact .inr (.inr ⟨hs, hfl n hf⟩)
      · obtain ⟨mk, hmk⟩ := S.amalgamate hA fam (hcomp _ h1)
        refine ⟨mk, fun n hn => ?_⟩
        obtain ⟨x, hs⟩ := S.assembled_src hA n hn
        exact .inl ⟨x, interchangeable_iff.mp (h1 n hn x.1 x.2 hs), hs, hmk x n hn hn hs⟩
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
    · have hkey := interchangeable_iff.mp hkey
      by_cases h : i < k
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
    · have hs : dev.key i n = .proof s := hs
      by_cases h : i < k
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

end ConLeche.Modular
