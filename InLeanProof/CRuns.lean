module

public import ConLeche.Cached.CheckerC
public import ConLeche.Verify.Cached.Grind
public import ConLeche.Verify.BridgeDecl

/-!
# A cached stage, run in step with its specification (task #451, lane indlock)

InLean's inductive stages are related to master's CACHED stages (`checkBlockIndsC`, …,
`ConLeche/Cached/Ind*.lean`), so that a change of a cached stage breaks InLean's proof and the
twin follows it.  A cached stage's run cannot be produced from InLean's: the cached core's memos
are not InLean's, so where InLean's core answers, the cached core at another memo state may run
out of fuel.  The relation therefore keeps the core abstract: `CRuns c p b a` reads the cached
computation `c` step by step, in step with the fueled specification `p`, every cached core call
paired with the fueled operation at the index's environment (`CoreTwin`), every other step a
state-free answer of `c` beside a run of `p`.  Its consequence is the specification's run
(`CRuns.runs`), which is what the declaration step consumes; the cached side is the code the proof
walks.

The pairs are master's own: `sharedOpsC mode fe` against `fueledOpsM mode` at `fe.env`
(master's `checkBlockDomsAtC_eq`, `checkBlockIndsC_eq`, … relate the two at the same pairing), and
`flushC`, which the specification does not run.
-/

public section

namespace InLeanProof

open ConLeche ConLeche.Cached

/-- **A cached core call and its fueled twin**: the four operations of `sharedOpsC mode fe` (the
calls the cached stages make, `coreKnotI mode false fe checkFuel`), against `fueledOpsM mode` at
the index's environment. -/
inductive CoreTwin (mode : CheckMode) (fe : FEnv) : {α : Type} → CheckCM α → FueledM α → Prop
  | infer (d : Nat) (e : Expr) :
      CoreTwin mode fe ((coreKnotI mode false fe checkFuel).infer d e)
        ((fueledOpsM mode).inferType fe.env d e)
  | whnf (d : Nat) (e : Expr) :
      CoreTwin mode fe ((coreKnotI mode false fe checkFuel).whnf d e)
        ((fueledOpsM mode).whnf fe.env d e)
  | defeq (d : Nat) (a b : Expr) :
      CoreTwin mode fe ((coreKnotI mode false fe checkFuel).defeq d a b)
        ((fueledOpsM mode).isDefEq fe.env d a b)
  | sort (d : Nat) (e : Expr) :
      CoreTwin mode fe (ensureSortI (coreKnotI mode false fe checkFuel) d e)
        ((fueledOpsM mode).ensureSort fe.env d e)

/-- **The cached computation `c` answers `b` in step with the fueled `p` answering `a`.**  A
state-free answer of `c` beside a run of `p` (`ret`: the pure steps, the `Option` unwraps, the
guards that pass); a core call beside its twin's run (`core`); a bind of two steps (`bind`); and
a flush, which the specification does not run (`flush`). -/
inductive CRuns (mode : CheckMode) : {β α : Type} → CheckCM β → FueledM α → β → α → Prop
  | ret {β α : Type} {c : CheckCM β} {p : FueledM α} {b : β} {a : α} :
      (∀ s, c s = .ok (b, s)) → Runs p a → CRuns mode c p b a
  | core {α : Type} {fe : FEnv} {c : CheckCM α} {p : FueledM α} {a : α} :
      CoreTwin mode fe c p → Runs p a → CRuns mode c p a a
  | bind {β α β' α' : Type} {x : CheckCM β} {px : FueledM α} {f : β → CheckCM β'}
      {pf : α → FueledM α'} {b : β} {a : α} {b' : β'} {a' : α'} :
      CRuns mode x px b a → CRuns mode (f b) (pf a) b' a' → CRuns mode (x >>= f) (px >>= pf) b' a'
  | flush {β α : Type} {f : Unit → CheckCM β} {p : FueledM α} {b : β} {a : α} :
      CRuns mode (f ()) p b a → CRuns mode (flushC >>= f) p b a

namespace CRuns

variable {mode : CheckMode}

/-- **The specification's run**: what the cached side was read in step with. -/
theorem runs {β α : Type} {c : CheckCM β} {p : FueledM α} {b : β} {a : α}
    (h : CRuns mode c p b a) : Runs p a := by
  induction h with
  | ret _ hp => exact hp
  | core _ hp => exact hp
  | bind _ _ hx hf => exact Runs.bind hx hf
  | flush _ ih => exact ih

/-- A `pure` beside a `pure`. -/
theorem pure' {β α : Type} (b : β) (a : α) :
    CRuns mode (pure b : CheckCM β) (pure a : FueledM α) b a :=
  .ret (fun _ => rfl) (Runs.pure a)

/-- A cached core call beside its twin, at the index's environment. -/
theorem defeq {fe : FEnv} {d : Nat} {a b : Expr} {r : Bool}
    (h : Runs ((fueledOpsM mode).isDefEq fe.env d a b) r) :
    CRuns mode ((coreKnotI mode false fe checkFuel).defeq d a b)
      ((fueledOpsM mode).isDefEq fe.env d a b) r r :=
  .core (.defeq d a b) h

theorem infer {fe : FEnv} {d : Nat} {e r : Expr}
    (h : Runs ((fueledOpsM mode).inferType fe.env d e) r) :
    CRuns mode ((coreKnotI mode false fe checkFuel).infer d e)
      ((fueledOpsM mode).inferType fe.env d e) r r :=
  .core (.infer d e) h

theorem whnf {fe : FEnv} {d : Nat} {e r : Expr}
    (h : Runs ((fueledOpsM mode).whnf fe.env d e) r) :
    CRuns mode ((coreKnotI mode false fe checkFuel).whnf d e)
      ((fueledOpsM mode).whnf fe.env d e) r r :=
  .core (.whnf d e) h

theorem sort {fe : FEnv} {d : Nat} {e : Expr} {u : Level}
    (h : Runs ((fueledOpsM mode).ensureSort fe.env d e) u) :
    CRuns mode (ensureSortI (coreKnotI mode false fe checkFuel) d e)
      ((fueledOpsM mode).ensureSort fe.env d e) u u :=
  .core (.sort d e) h

/-- An `Option` unwrap beside an unwrap of the same answer (the cached walk read as the
specification's by master's equation at the use). -/
theorem unwrap {α : Type} {o : Option α} {o' : Option α} {e e' : CheckError} {a : α}
    (h : o = some a) (h' : o' = some a) :
    CRuns mode (unwrapOr o e : CheckCM α) (unwrapOr o' e' : FueledM α) a a := by
  subst h h'
  exact pure' a a

end CRuns

end InLeanProof
