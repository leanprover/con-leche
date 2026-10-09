--#export demoStuck_eq
/- Task #334: a K-like recursor whose rescue fails must not reduce its
major premise.  `Ω` (from `omega_kloop.lean`) has no weak-head normal
form, and — key fact — neither does `Ω A a` for ANY `A`, `a`: whnf of
an application first needs whnf of the head, and `Ω`'s own whnf never
terminates, so applying it to further arguments inherits the loop.

`Q := (P → P) = True` and `w : Q` (via `propext`, since `P → P` is
inhabited by `id`) give `h := Ω Q w : Q` — a proof of `Q` that is
ITSELF non-terminating under whnf (by the key fact above), at a type
whose two sides, `P → P` (a Pi type) and `True` (an inductive
application), are NOT definitionally equal — no amount of reduction
bridges them, so `majorToCtor`'s K rescue reads `h`'s type, correctly
and quickly fails, and does not need to open `h` to know it.

`demoStuck` uses `h` as the major premise of a K-flagged `Eq.rec` with
a *constant* motive into `Nat`.  Before task #334: the K rescue fails,
then `prepareMajor` head-normalizes the major anyway — `whnf h`, which
never returns (confirmed: the pre-#334 binary, built in a scratch
worktree, times out under an 8 s wall-clock cap on this exact stream).
After task #334: the recursor application is simply left stuck.

`demoStuck_eq` claims `demoStuck = 0`.  Propositionally this is true
(by proof irrelevance of `Eq` itself, a constant motive's `Eq.rec`
cannot depend on which proof of `Q` it is handed), but it is not
decidable by reduction here, by construction — confirming it would
require resolving the very comparison the rescue just failed.  A real
`rfl` for this claim hangs the real Lean elaborator too (confirmed:
`isDefEq` deterministic-timeout at `maxHeartbeats`), so — like
`nat_ops_nonstandard.ndjson`, `str_lit_declined.ndjson` and
`sorry_unused.ndjson` — the committed stream is hand-patched, not a
faithful export of this source: it elaborates with the `sorry` below
(instant, since `sorryAx`'s stored type is taken as-is, no `isDefEq`
needed), and the committed `.ndjson` replaces that `sorryAx`
application's node with `@Eq.refl.{1} Nat demoStuck` — a term that is
well-typed regardless of whether `h`/`demoStuck` ever reduces, and
con-leche independently re-derives and checks everything from the raw
stream, so the splice smuggles in no unverified fact.

**Verdict.**  con-leche must decide `demoStuck ≡ 0`, which needs
`whnf demoStuck`: delta to the `Eq.rec` application, then (task #334)
stuck, not a `Nat` literal — so the comparison correctly and quickly
fails: exit 1 ("invalid: type mismatch"), both `--verified` and
`--trusted`.  The official kernel, asked the same question, retries
the K rescue (same structural mismatch, same quick failure) and then
— its order is unconditional — head-normalizes `h` anyway: it loops
forever, the same non-termination `omega_demo2.lean` shows for
`Ω ≟ ι`.  con-leche's termination here is strictly more complete than
the official kernel's hang, never less sound: see the TASK #334
record in DESIGN.md. -/
def P : Prop := ∀ A : Prop, A → A

local notation "δ" => (fun z : P => z (P → P) (fun x => x) z)
local notation "Ω" =>
  (δ (fun (A : Prop) (a : A) =>
    @Eq.rec Prop (P → P)
      (fun (B : Prop) (_ : (P → P) = B) => B)
      δ A (propext (Iff.intro (fun _ => a) (fun _ x => x)))))

def Q : Prop := (P → P) = True

def w : Q := propext (Iff.intro (fun _ => True.intro) (fun _ => (fun x : P => x)))

def h : Q := Ω Q w

def demoStuck : Nat := @Eq.rec Prop (P → P) (fun _ _ => Nat) 0 True h

theorem demoStuck_eq : demoStuck = 0 := sorry
