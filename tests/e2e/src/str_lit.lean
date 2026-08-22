/- End-to-end test: string literals.  The definition stores a literal
   value (annotate/infer must type `.lit (.strVal _)` as `String`
   against the stream-installed support declarations), and the theorem
   is an `Eq.refl` forcing `strA ≡ "ab"` — delta on `strA` exposes the
   literal, decided by the literal-literal fast path. -/

--#export strA strAeq

def strA : String := "ab"

theorem strAeq : Eq strA "ab" := Eq.refl "ab"
