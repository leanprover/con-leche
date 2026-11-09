module
-- Guards task #415: H privately imports TeqP1; teqN's equation lemma
-- (exported under H's private prefix) reads teq.
import TeqP1
public def teqN : Nat := (fun (_ : (1 : Nat) + 1 = 2) => 0) teq
public theorem teqN_zero : teqN = 0 := by
  rw [teqN]
