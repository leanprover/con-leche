module

public import ConLeche.Verify.Driver.Copies
public import ConLeche.Verify.Driver.Clashes
import ConLeche.Verify.Driver.Reach

/-!
# The routes' facts about one worker

What the routes of the composition (task #501, `Routes.lean`) need of one accepted worker,
model-free:

* `readNames_needsGo` — the reach's memoized walk lists every name an expression reads;
* `first_none_of_ownNames` — no name of a module's private view is loaded (freshness);
* `first_of_at` — a copy the name index records makes its name loaded;
* `homeView_copy`, `spotOf_level` — a view's copy, and a loaded copy, is a copy on the snapshot
  at a level a load reads;
* `workerClash_kinds` — a clash's copies are theorems or axioms, all unsafe or none (Lean's
  merge rule, `subsumesF`);
* `copy_own'` — `copy_own` at every name but the tolerated axiom's, `Quot.sound` included (its
  pinned constant is the copy's statement where its home accepted it), and the statement's type
  does not read its own name.
-/

public section

namespace ConLeche.Driver

open ConLeche ConLeche.Modular ConLeche.Frontend ConLeche.Frontend.Olean ConLeche.Cached

/-- `Expr.needs` is `Expr.readNames`. -/
theorem needs_eq_readNames (e : Expr) : e.needs = e.readNames := by
  induction e with
  | lit l => cases l <;> rfl
  | fvar _ _ ih => simp only [Expr.needs, Expr.readNames, ih]
  | app f a ihf iha => simp only [Expr.needs, Expr.readNames, ihf, iha]
  | lam t b iht ihb => simp only [Expr.needs, Expr.readNames, iht, ihb]
  | forallE t b iht ihb => simp only [Expr.needs, Expr.readNames, iht, ihb]
  | letE t v b iht ihv ihb => simp only [Expr.needs, Expr.readNames, iht, ihv, ihb]
  | proj s i e ih => simp only [Expr.needs, Expr.readNames, ih]
  | _ => rfl

/-- **The memoized walk from nothing lists every name an expression reads.** -/
theorem readNames_needsGo {e : Expr} {n : Name} (h : n ∈ e.readNames) :
    n ∈ (needsGo {} #[] e).2 := by
  have hi : NeedsInv (({} : Std.HashSet Expr), (#[] : Array Name)) := fun e he => by simp at he
  exact (needsGo_spec e {} #[] hi).2.2 n (by rw [needs_eq_readNames]; exact h)

variable {sp : SearchPath} {fs : FS}

/-- **No name of a module's private view is loaded** (the worker's freshness). -/
theorem first_none_of_ownNames {M : Name} {jobs : Nat} {w : WorkerRead}
    (hw : WorkerFacts sp fs M jobs w) {n : Name} (hn : (ownNames w.home).contains n = true) :
    w.reads.index.first[n]? = none := by
  sorry

/-- **A copy the name index records makes its name loaded.** -/
theorem first_of_at {M : Name} {jobs : Nat} {w : WorkerRead} (hw : WorkerFacts sp fs M jobs w)
    {cp : Copy} {q : NamePosition} (hq : w.reads.index.at cp = some q) :
    (w.reads.index.first[q.name]?).isSome = true := by
  obtain ⟨_, _, hr⟩ := hw.reads
  obtain ⟨-, -, hmore, hall, -, -⟩ := workerIndex_copies hr
  rcases hall cp q hq with h | h
  · rw [h]; rfl
  · obtain ⟨-, cp₀, hf, -⟩ := hmore _ _ h
    rw [hf]; rfl

/-- **A loaded copy is at a level a load reads.** -/
theorem spotOf_level (wr : WorkerReads) (cp : Copy) (q : NamePosition) :
    (spotOf wr cp q).part.level ≠ .server := by
  simp only [spotOf, LoadFlags.level]
  split <;> decide

/-- **A view's copy of `y`** is a copy on the snapshot, of `y`, at a level a load reads. -/
theorem homeView_copy {h y : Name} {v : Std.HashMap Name Spot} {s : Spot}
    (hv : HomeView sp fs h v) (hs : v[y]? = some s) :
    CopyAt sp fs s ∧ s.part.level ≠ .server ∧ s.pos.name = y := by
  sorry

/-- **A clash's copies are theorems or axioms, all unsafe or none**: Lean's merge rule
(`subsumesF`) passed on it. -/
theorem workerClash_kinds {m : Name} {jobs : Nat} {wr : WorkerReads} {hs hs' : HS}
    (h : (workerReads (.ofPath sp) m jobs : ModelIO _) fs hs (.ok (.ok wr)) hs')
    {cl : Clash} (hcl : cl ∈ wr.clashes.toList) {e₁ e₂ : Copy × ConstantVal × CKindF Name Unit}
    (h₁ : e₁ ∈ cl.copies.toList) (h₂ : e₂ ∈ cl.copies.toList) :
    e₁.2.2.skipped = e₂.2.2.skipped ∧ (e₁.2.2.tag = 0 ∨ e₁.2.2.tag = 2) := by
  sorry

/-- **A copy's constant in its module's own environment** (`copy_own`, at `Quot.sound` too): a
copy of `M`'s part, at a level a load reads, of a statement kind, not filtered out, at no
`sorryAx`, has in `M`'s own environment a statement-kind constant of the copy's statement, a
theorem where the copy or the private constant behind it is one; and the statement's type does
not read its own name. -/
theorem copy_own' {mode : CheckMode} {M : Name} {jobs : Nat}
    {w : WorkerRead} (hw : WorkerFacts sp fs M jobs w) (hrun : OwnRun mode sp fs M w)
    {s : Spot} (hmod : s.part.mod = M) (hs : CopyAt sp fs s) (hl : s.part.level ≠ .server)
    {r : Region} (hr : PartRegion sp fs s.part r) {cv : ConstantVal} {k : CKindF Name Unit}
    (hst : StmtSkel r s.pos.loc cv k) (hsk0 : s.pos.skipped = false) (htag : k.tag < 4)
    (hsy : cv.name ≠ sorryAxName) :
    ∃ ci, (ownEnvOf sp fs M w).find? cv.name = some ci ∧ ci.toConstantVal = cv ∧
      ci.isStmtKind = true ∧
      ((k.tag = 2 ∨ ∃ q : Spot, CopyAt sp fs q ∧ q.part = ⟨M, .private⟩ ∧
          q.pos.name = s.pos.name ∧ q.pos.tag = 2) → ∃ cv', ci = .thmInfo cv') ∧
      cv.name ∉ cv.type.readNames := by
  sorry

end ConLeche.Driver
