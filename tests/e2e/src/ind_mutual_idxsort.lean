--#export IdxSort.ma_example IdxSort.mb_example IdxSort.mc_example IdxSort.mu_example IdxSort.nt_example IdxSort.nu_example

/- End-to-end fixture (task #227): mutual and nested blocks whose INDEX
   DOMAINS' sorts are not syntactically readable.

   The in-process modeller (`ConLeche/Frontend/InModel/*`) puts a mutual
   or nested member's index telescope into the tag constructor
   (`tag.m : ∀ p⃗ ı⃗_m, tag p⃗`), so the tag family's own universe must
   dominate every index domain's sort — a datum the modeller has to
   emit, with no environment and no `whnf` to compute it.  Task #200's
   syntactic sort inferer read it only where the domain's type is
   SYNTACTICALLY a sort, and the shapes below all need one unfolding
   step, so the block declined ("cannot infer the sort of index j" —
   the #218 finding).

   The shapes, one block each so the residual is exact:

   * `MA`/`MB`: the block's parameter is `(α : id Type)` and the members
     are indexed by `(x : α)` — a VARIABLE whose type is a stuck
     application — and by `(i : IdxW)`, a CONSTANT whose declared type
     is that same stuck application (`def IdxW : id Type := Nat`);
   * `MC`/`MD`: the index domain is `FamW Nat`, a stuck application
     whose HEAD's declared type is stuck too (`def FamW : id (Type →
     Type)`), so the domain's own type cannot be inferred either;
   * `MU`/`MV`: the universe-polymorphic twin — parameter
     `(α : id (Type u))`, index `(a : α)`, so the tag's universe is a
     level EXPRESSION over the block's own parameter;
   * `NT`, `NU`: the two CLOSED domains on NESTED blocks (through
     `List`), which share the kit's tag construction.

   Every block varies its indices (a parameter `f : α → α`, a `Nat.succ`,
   a `!` on the Boolean index): Lean promotes a FIXED index to a
   parameter, and the shape under test would be gone.

   Official's `mk_rec_infos` infers these sorts with the environment and
   accepts.  con-leche computes a sort CEILING (`Kit.sortCeil`): the
   exact sort where the inferer reads one, else a level provably above
   it, which is all the tag family needs (its universe may be larger
   than the least one — the fold checks `field ≤ result`).

   official: 0.  con-leche: 0 (both modes; the twin
   ind_mutual_idxsort_bad, whose index domain is not a type at all,
   rejects with 1 at the generated tag family). -/

namespace IdxSort

/-- An index domain declared at a definition whose own type is stuck. -/
def IdxW : id Type := Nat

/-- A container whose head's declared type is stuck: neither `FamW Nat`
nor its head `FamW` can be typed without unfolding `id`. -/
def FamW : id (Type → Type) := fun X => X → Bool

/- Shape 1: the indices `(x : α)` at `α : id Type` and `(i : IdxW)`. -/
mutual
inductive MA (α : id Type) (f : α → α) : α → IdxW → Type where
  | mk : (x : α) → (i : IdxW) → MB α f x i → MA α f x i
inductive MB (α : id Type) (f : α → α) : α → IdxW → Type where
  | nil : (x : α) → (i : IdxW) → MB α f x i
  | step : (x : α) → (i : IdxW) → MA α f (f x) (Nat.succ i) → MB α f x i
end

noncomputable def MA.size {α : id Type} {f : α → α} {x : α} {i : IdxW}
    (t : MA α f x i) : Nat :=
  MA.rec (motive_1 := fun _ _ _ => Nat) (motive_2 := fun _ _ _ => Nat)
    (fun _ _ _ ih => ih + 1) (fun _ _ => 0) (fun _ _ _ ih => ih + 1) t

/-- `rfl` forces iota through the model recursor at the indices. -/
theorem ma_example :
    MA.size (α := Nat) (f := Nat.succ)
      (.mk 3 Nat.zero (.step 3 Nat.zero (.mk 4 (Nat.succ Nat.zero) (.nil 4 _)))) = 3 :=
  rfl

def mb_example : MB Nat Nat.succ 3 Nat.zero := .nil 3 Nat.zero

/- Shape 2: the index domain `FamW Nat` — a stuck application. -/
mutual
inductive MC : FamW Nat → Type where
  | mk : (g : FamW Nat) → MD (fun n => !(g n)) → MC g
inductive MD : FamW Nat → Type where
  | nil : (g : FamW Nat) → MD g
  | step : (g : FamW Nat) → MC (fun n => !(g n)) → MD g
end

def mc_example : MC (fun n => Nat.blt 0 n) := .mk _ (.nil _)

/- Shape 3: the universe-polymorphic twin. -/
mutual
inductive MU (α : id (Type u)) (f : α → α) : α → Prop where
  | mk : (a : α) → MV α f (f a) → MU α f a
inductive MV (α : id (Type u)) (f : α → α) : α → Prop where
  | refl : (a : α) → MV α f a
  | step : (a : α) → MU α f (f a) → MV α f a
end

theorem mu_example {α : id (Type u)} (f : α → α) (a : α) : MU α f a :=
  .mk a (.refl (f a))

/- Shape 4: the same two domains on NESTED blocks (through `List`).

   Their indices are CLOSED (`IdxW`, `FamW Nat`) — a nested block whose
   index DOMAIN mentions a parameter is a separate, older gap of the
   nested rung, unrelated to the sort ceiling: it rejects the generated
   `_impl.rec` and does so already for a domain whose sort is plain
   (`inductive NB (α : Type) (a₀ : α) : α → Type` nesting through
   `List`), see the DESIGN record's finding. -/
inductive NT : IdxW → Type where
  | leaf : (i : IdxW) → NT i
  | node : (i : IdxW) → List (NT Nat.zero) → NT (Nat.succ i)

def nt_example : NT (Nat.succ Nat.zero) := .node Nat.zero [.leaf Nat.zero]

inductive NU : FamW Nat → Type where
  | leaf : (g : FamW Nat) → NU g
  | node : (g : FamW Nat) → List (NU (fun _ => true)) → NU (fun n => !(g n))

def nu_example : NU (fun n => !Nat.blt 0 n) :=
  .node (fun n => Nat.blt 0 n) [.leaf _, .leaf _]

end IdxSort
