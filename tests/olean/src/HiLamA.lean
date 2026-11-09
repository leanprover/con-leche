module
-- Guards task #409 (the BlockModelSelfDualPOmegaPlus pattern): private
-- definitions exported with their values (`groupLift`) whose values are
-- λs passing a private-only theorem (`relations_liftable`) as a proof
-- argument, read by two exposed definitions.  The bodies differ in the
-- non-proof argument only: with `hlEq (n + 0)` in `hlQ`, Lean's kernel
-- itself would infer the proofs' types (proof irrelevance) and reject.
public section
@[expose] def hlG (n : Nat) (_h : n = n) : Nat := n + 1
private theorem hlEq (n : Nat) : n = n := rfl
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
private def hlP : Nat → Nat := fun n => hlG n (hlEq n)
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
private def hlQ : Nat → Nat := fun n => hlG (n + 0) (hlEq n)
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[expose] def hlF : Nat → Nat := hlP
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[expose] def hlF2 : Nat → Nat := hlQ
end
