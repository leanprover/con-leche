module

@[expose] public section

/-!
# Modular checking, over an interface of models

The fragment's modular theorem (`modular`, `ModularInstance.lean`) has
two halves: a consistency proof for one environment, and the argument
that carries it from module to module.  This file is the second half,
stated over an interface (`ModularSemantics`) that says what the first
half must provide.  It imports nothing.  The fragment's model is one
instance (`ModularInstance.lean`).  `ModularSyntactic.lean` is a second,
small one, an illustration of the interface (see there for its limits).
The interface gives every proof one shared value (`proofVal`), which
suits set models; whether it suits another consistency proof is open
until there is such a proof to connect it to.

There is no global environment and no renaming.  Each module's
environments use the module's own names.  Two modules may hold copies
of one name; what the theory asks is that the copies a module reads
**agree**: get one value in the models.  The importer proves that
locally, for each copy a source holds, in one of three ways: the source
is the module the name is read from; the source and the importer both
read it from one earlier module (one record, loaded through two paths);
or both copies are proofs, which every model gives the proofs' value.

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
4. **proofs**: `ProofIn C E n` (`C` proves `E`'s `n` a proof: in
   the fragment, its type is inferred at `C` to be a proposition) gives `n`
   the proofs' value in every model of `E` that agrees on `C` with a
   model of `C` (`proof_val`); `IsThm E n` (`E` stores `n` as a theorem)
   gives it the proofs' value in every model of `E` (`thm_val`);
5. **the conservative step** (`step`): if the checker accepts
   declarations `D` over `Γ`, giving `Γ'`, every model of `Γ` extends
   to one of `Γ'`, keeping every name of `Γ` and its value.

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
presents it), for each context name the module it is **read from**
(`src`), an order among its context names (`rank`), and per context
name the **part below it** (`part`).  A module is **valid**
(`Development.Valid`) if each source's view refines its module's own
environment and comes from an earlier module, its context is assembled
from its sources, every context name is stored by the source of the
module it is read from, its part is assembled from the sources and
holds only context names of smaller rank, and every source that stores
it **agrees** (`Agrees`): it is that module, or it and the module both
read the name from one earlier module, or it and that module's copy are
proofs (`ProofIn` over the part,
or a theorem where the copy comes from); and the module's declarations
are accepted over its context, or the module is **compared** (its own
environment is its context).  If every module is valid, there is a
**compatible family** of models, one of each module's own environment:
each module gives every context name the value the module it is read
from gives it.  The proof goes module by module: the earlier modules'
models, restricted to the sources' views, give every context name its
read value, name by name in rank order (a proof's copies by the part's
model, which the names below already make an amalgam), so they
amalgamate to a model of the context, and the step extends it over the
declarations.  Each module's model is built from its sources' models
alone.
-/

namespace Fragment

universe u w

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
  /-- **`C` proves `E`'s `n` a proof** -/
  ProofIn : Env → Env → Name → Prop
  /-- a proof by `C` gets the proofs' value in every model agreeing on
  `C` with one of `C` -/
  proof_val : ∀ {C E : Env} {n : Name}, ProofIn C E n → ∀ (mC : Mod C) (m : Mod E),
    ModelsAgree Stores @val C mC m → val m n = proofVal
  /-- **`E` stores `n` as a theorem** (in the fragment: a statement `E`
  itself infers to be a proposition) -/
  IsThm : Env → Name → Prop
  /-- a theorem gets the proofs' value in every model -/
  thm_val : ∀ {E : Env} {n : Name}, IsThm E n → ∀ m : Mod E, val m n = proofVal
  /-- declarations -/
  Decls : Type u
  /-- **acceptance**: the checker accepts `D` over `Γ`, giving `Γ'` -/
  Accepts : Env → Decls → Env → Prop
  /-- **the conservative step** -/
  step : ∀ {Γ Γ' : Env} {D : Decls}, Accepts Γ D Γ' → ∀ m : Mod Γ,
    ∃ m' : Mod Γ', ∀ n, Stores Γ n → Stores Γ' n ∧ val m' n = val m n

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

variable {S : ModularSemantics.{u, w}}

/-- **A development** over `S`: per module its context, declarations,
own environment, its sources (the views it reads, each with the module
that presents it), for each context name the module it is read from,
the order among its context names, and the part of its context below
each name. -/
structure Development (S : ModularSemantics.{u, w}) where
  ctx : Nat → S.Env
  decls : Nat → S.Decls
  own : Nat → S.Env
  sources : Nat → List (Nat × S.Env)
  src : Nat → S.Name → Nat
  rank : Nat → S.Name → Nat
  part : Nat → S.Name → S.Env

namespace Development

variable (dev : Development S)

/-- The sources module `i` reads. -/
def Src (i : Nat) : Type u := {x : Nat × S.Env // x ∈ dev.sources i}

/-- **Assembled from the sources.** -/
def Assembled (i : Nat) (E : S.Env) : Prop := S.Assembled E fun x : dev.Src i => x.1.2

/-- **A theorem where the copy comes from**: source `x`'s module stores
`n` as a theorem, or reads it from a module that does. -/
def ThmAt (x : Nat × S.Env) (n : S.Name) : Prop :=
  S.IsThm (dev.own x.1) n ∨ S.Stores (dev.ctx x.1) n ∧ S.IsThm (dev.own (dev.src x.1 n)) n

/-- **Source `x`'s copy of `n` is a proof** for module `i`: proved one
over the part below `n`, or a theorem where it comes from. -/
def ProofSide (i : Nat) (n : S.Name) (x : Nat × S.Env) : Prop :=
  S.ProofIn (dev.part i n) x.2 n ∨ dev.ThmAt x n

/-- **Source `x` agrees with the module `n` is read from** (see the
module docstring): it is that module; or it reads `n` with a source
of some module among its own, and module `i` has a source of that same,
earlier module storing `n` (one record, loaded through two paths); or it
and every source of the read module are proofs at `n`. -/
def Agrees (i : Nat) (n : S.Name) (x : Nat × S.Env) : Prop :=
  x.1 = dev.src i n ∨
    (S.Stores (dev.ctx x.1) n ∧ ∃ z ∈ dev.sources x.1, S.Stores z.2 n ∧
      ∃ w ∈ dev.sources i, w.1 = z.1 ∧ S.Stores w.2 n ∧ w.1 < x.1) ∨
    dev.ProofSide i n x ∧
      ∀ y ∈ dev.sources i, y.1 = dev.src i n → S.Stores y.2 n → dev.ProofSide i n y

/-- **How module `i` reads a context name `n`**: from a source of the
module it is read from, with an assembled part below it, every source
storing it agreeing. -/
structure Reads (i : Nat) (n : S.Name) : Prop where
  read : ∃ x ∈ dev.sources i, x.1 = dev.src i n ∧ S.Stores x.2 n
  part : dev.Assembled i (dev.part i n)
  below : ∀ c, S.Stores (dev.part i n) c → S.Stores (dev.ctx i) c ∧ dev.rank i c < dev.rank i n
  agree : ∀ x ∈ dev.sources i, S.Stores x.2 n → dev.Agrees i n x

/-- **A checked module**: its declarations accepted over its context. -/
def Checked (i : Nat) : Prop := S.Accepts (dev.ctx i) (dev.decls i) (dev.own i)

/-- **A compared module**: its own environment is its context. -/
def Compared (i : Nat) : Prop := dev.own i = dev.ctx i

/-- **A valid module**: each source is a view of an earlier module that
refines its own environment, its context is assembled from the sources
and read from them, and the module is checked or compared. -/
structure Valid (i : Nat) : Prop where
  sources : ∀ x ∈ dev.sources i, x.1 < i ∧ S.Refines x.2 (dev.own x.1)
  assembled : dev.Assembled i (dev.ctx i)
  reads : ∀ n, S.Stores (dev.ctx i) n → dev.Reads i n
  checked_or_compared : dev.Checked i ∨ dev.Compared i

/-- **A compatible family** of models below `k`: each module gives every
context name the value the module it is read from gives it, and so does
every source of the module storing it. -/
def Compatible (k : Nat) (m : (i : Nat) → i < k → S.Mod (dev.own i)) : Prop :=
  ∀ j (hj : j < k) n, S.Stores (dev.ctx j) n →
    ∃ h : dev.src j n < k, S.val (m j hj) n = S.val (m (dev.src j n) h) n ∧
      ∀ y ∈ dev.sources j, ∀ hy : y.1 < k, S.Stores y.2 n →
        S.val (m y.1 hy) n = S.val (m (dev.src j n) h) n

variable {dev}

/-- A family below `k` extended by one member at `k`. -/
def extendFam {P : Nat → Sort w} {k : Nat} (m : (i : Nat) → i < k → P i) (x : P k) :
    (i : Nat) → i < k + 1 → P i :=
  fun i hi => if h : i < k then m i h else
    (Nat.le_antisymm (Nat.not_lt.mp h) (Nat.le_of_lt_succ hi) : k = i) ▸ x

theorem extendFam_lt {P : Nat → Sort w} {k : Nat} (m : (i : Nat) → i < k → P i) (x : P k)
    {i : Nat} (hi : i < k + 1) (h : i < k) : extendFam m x i hi = m i h := dite_eq_left h

theorem extendFam_self {P : Nat → Sort w} {k : Nat} (m : (i : Nat) → i < k → P i) (x : P k)
    (hk : k < k + 1) : extendFam m x k hk = x := dite_eq_right (Nat.lt_irrefl k)

/-- One module's value, whatever proof of its bound. -/
theorem val_congr {k : Nat} (m : (i : Nat) → i < k → S.Mod (dev.own i)) {a b : Nat} (h : a = b)
    (ha : a < k) (hb : b < k) (n : S.Name) : S.val (m a ha) n = S.val (m b hb) n := by
  subst h; rfl

/-- **The modular theorem, over the interface**: if every module below
`k` is valid, there is a compatible family of models, one of each
module's own environment. -/
theorem modular : ∀ k, (∀ i < k, dev.Valid i) →
    ∃ m : (i : Nat) → i < k → S.Mod (dev.own i), dev.Compatible k m
  | 0, _ => ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1, hv => by
    obtain ⟨m, hc⟩ := modular k fun i hi => hv i (Nat.lt_succ_of_lt hi)
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
    have hsrc : ∀ n, S.Stores (dev.ctx k) n → dev.src k n < k := fun n hn => by
      obtain ⟨x, hx, hx1, -⟩ := (hk.reads n hn).read
      exact hx1 ▸ hlt ⟨x, hx⟩
    -- a theorem where a copy comes from gets the proofs' value
    have hthm : ∀ (x : dev.Src k) n, S.Stores x.1.2 n → dev.ThmAt x.1 n →
        S.val (fam x) n = S.proofVal := by
      intro x n hs ht
      rw [(hfam x n hs).2]
      rcases ht with ht | ⟨hctx, ht⟩
      · exact S.thm_val ht _
      · obtain ⟨h, he, -⟩ := hc x.1.1 (hlt x) n hctx
        rw [he]
        exact S.thm_val ht _
    -- every source storing a context name gives it the value of the
    -- module it is read from, in rank order
    have hread : ∀ r, ∀ n (hn : S.Stores (dev.ctx k) n), dev.rank k n = r →
        ∀ x : dev.Src k, S.Stores x.1.2 n →
          S.val (fam x) n = S.val (m (dev.src k n) (hsrc n hn)) n := by
      intro r
      induction r using Nat.strongRecOn with
      | _ r ih =>
      intro n hn hr x hs
      have hR := hk.reads n hn
      -- a proof's copy, by the model of the part below it
      have hside : ∀ z : dev.Src k, S.Stores z.1.2 n → dev.ProofSide k n z.1 →
          S.val (fam z) n = S.proofVal := by
        intro z hz hp
        rcases hp with hp | ht
        · have hag : ∀ y y' : dev.Src k,
              ModelsAgree S.Stores @S.val (dev.part k n) (fam y) (fam y') := by
            intro y y' c hc' hy hy'
            obtain ⟨hcC, hlt'⟩ := hR.below c hc'
            rw [ih _ (hr ▸ hlt') c hcC rfl y hy, ih _ (hr ▸ hlt') c hcC rfl y' hy']
          obtain ⟨mP, hmP⟩ := S.amalgamate hR.part fam hag
          exact S.proof_val hp mP (fam z) (hmP z)
        · exact hthm z n hz ht
      -- source by source, an earlier source's module first
      suffices h : ∀ t, ∀ x : dev.Src k, x.1.1 = t → S.Stores x.1.2 n →
          S.val (fam x) n = S.val (m (dev.src k n) (hsrc n hn)) n from h _ x rfl hs
      intro t
      induction t using Nat.strongRecOn with
      | _ t iht =>
      intro x hxt hs
      rcases hR.agree x.1 x.2 hs with he | ⟨hctx, z, hz, hzs, w, hw, hwz, hws, hwlt⟩ | ⟨hpx, hall⟩
      · rw [(hfam x n hs).2]
        exact val_congr m he _ _ n
      · -- `x.1`'s copy is the one its source `z` gives, which `i`'s source `w` gives too
        rw [(hfam x n hs).2]
        have hzk : z.1 < k :=
          Nat.lt_trans ((hv x.1.1 (Nat.lt_succ_of_lt (hlt x))).sources z hz).1 (hlt x)
        obtain ⟨h, he', hsrcs⟩ := hc x.1.1 (hlt x) n hctx
        rw [he', ← hsrcs z hz hzk hzs, ← iht w.1 (hxt ▸ hwlt) ⟨w, hw⟩ rfl hws, (hfam ⟨w, hw⟩ n hws).2]
        exact val_congr m hwz.symm _ _ n
      · obtain ⟨y, hy, hy1, hys⟩ := hR.read
        rw [hside x hs hpx, ← hside ⟨y, hy⟩ hys (hall y hy hy1 hys), (hfam ⟨y, hy⟩ n hys).2]
        exact val_congr m hy1 _ _ n
    -- so they agree on the context and amalgamate
    obtain ⟨mC, hmC⟩ := S.amalgamate hk.assembled fam fun x x' n hn hs hs' => by
      rw [hread _ n hn rfl x hs, hread _ n hn rfl x' hs']
    obtain ⟨mk, hmk⟩ : ∃ mk : S.Mod (dev.own k), ∀ n, S.Stores (dev.ctx k) n →
        S.val mk n = S.val mC n := by
      rcases hk.checked_or_compared with hacc | hcmp
      · obtain ⟨mk, hmk⟩ := S.step hacc mC
        exact ⟨mk, fun n hn => (hmk n hn).2⟩
      · unfold Compared at hcmp
        rw [hcmp]
        exact ⟨mC, fun _ _ => rfl⟩
    -- the new module's context values are its sources'
    have hnew : ∀ n (hn : S.Stores (dev.ctx k) n),
        S.val mk n = S.val (m (dev.src k n) (hsrc n hn)) n := by
      intro n hn
      obtain ⟨y, hy, hy1, hys⟩ := (hk.reads n hn).read
      rw [hmk n hn, hmC ⟨y, hy⟩ n hn hn hys]
      exact hread _ n hn rfl ⟨y, hy⟩ hys
    refine ⟨extendFam m mk, fun j hj n hn => ?_⟩
    by_cases h : j < k
    · obtain ⟨h', he, hsrcs⟩ := hc j h n hn
      refine ⟨Nat.lt_succ_of_lt h', ?_, fun y hy hyk hys => ?_⟩
      · rw [extendFam_lt m mk hj h, extendFam_lt m mk _ h']
        exact he
      · have hyj : y.1 < k := Nat.lt_trans ((hv j hj).sources y hy).1 h
        rw [extendFam_lt m mk hyk hyj, extendFam_lt m mk _ h']
        exact hsrcs y hy hyj hys
    · obtain rfl : k = j := by omega
      refine ⟨Nat.lt_succ_of_lt (hsrc n hn), ?_, fun y hy hyk hys => ?_⟩
      · rw [extendFam_self m mk hj, extendFam_lt m mk _ (hsrc n hn)]
        exact hnew n hn
      · have hyj : y.1 < k := hlt ⟨y, hy⟩
        rw [extendFam_lt m mk hyk hyj, extendFam_lt m mk _ (hsrc n hn), ← (hfam ⟨y, hy⟩ n hys).2]
        exact hread _ n hn rfl ⟨y, hy⟩ hys

/-- **Every valid module's own environment has a model.** -/
theorem own_model (k : Nat) (hv : ∀ i < k, dev.Valid i) :
    ∀ i < k, Nonempty (S.Mod (dev.own i)) := by
  obtain ⟨m, -⟩ := dev.modular k hv
  exact fun i hi => ⟨m i hi⟩

end Development

end Fragment
