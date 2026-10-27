module

public import ConLeche.Kernel.BVUnsat
meta import ConLeche.Kernel.BVUnsat

public section

/-!
# The `bv_decide` gate's reader and recognition (task #368)

The formula reader (`readNat`, `readLogical`, …) on small hand-built
terms, the closedness test of `unfold?`, the spine recognition
`bvUnsatSpine`, the native-axiom names, and the gate's refusal where the
pinned closure is absent.  The native `verifyBVExpr` run is not
exercised here (`scripts/bv-decide-check.sh` runs it on a real stream).
-/

namespace ConLecheTests.BVUnsat

open ConLeche ConLeche.BVUnsat

/-- No stored constants. -/
def noFind : Name → Option ConstantInfo := fun _ => none
def noProj : Name → Nat → Option ProjEntry := fun _ _ => none

def lit (n : Nat) : Expr := .lit (.natVal n)
def ofNatE (n m : Nat) : Expr :=
  .app (.app (.app (.const ofNatN [.zero]) (.const natN [])) (lit n))
    (.app (.const instOfNatNatN []) (lit m))

/-! ## Numerals -/

#guard readNat (lit 7) == some 7
#guard readNat (ofNatE 8 8) == some 8
-- the instance's numeral must be the numeral's own
#guard readNat (ofNatE 8 9) == none
#guard readNat (.const natN []) == none

/-! ## Formulas -/

def predT : Expr := .const (nmL ["Std", "Tactic", "BVDecide", "BVPred"]) []

/-- `BoolExpr.const true`. -/
def constTrue : Expr :=
  Expr.mkAppN (.const beConstN []) [predT, .const boolTrueN []]

#guard match readLogical noFind 10 constTrue with
  | some (.const true) => true
  | _ => false

/-- `BVExpr.var 8 3`. -/
def var83 : Expr := Expr.mkAppN (.const exVarN []) [lit 8, lit 3]

/-- `BVPred.bin (var 8 3) eq (var 8 3)`, as a literal of the formula. -/
def eqPred : Expr :=
  Expr.mkAppN (.const predBinN []) [lit 8, var83,
    .const (nmL ["Std", "Tactic", "BVDecide", "BVBinPred", "eq"]) [], var83]

def litEq : Expr := Expr.mkAppN (.const beLiteralN []) [predT, eqPred]

#guard match readLogical noFind 10 litEq with
  | some (.literal (.bin (w := 8) (.var 3) .eq (.var 3))) => true
  | _ => false

-- `not` and `gate` recurse
#guard match readLogical noFind 10
    (Expr.mkAppN (.const beGateN []) [predT,
      .const (nmL ["Std", "Tactic", "BVDecide", "Gate", "and"]) [],
      Expr.mkAppN (.const beNotN []) [predT, constTrue], litEq]) with
  | some (.gate .and (.not (.const true)) (.literal _)) => true
  | _ => false

-- a width mismatch does not read
#guard (readLogical noFind 10 (Expr.mkAppN (.const beLiteralN []) [predT,
    Expr.mkAppN (.const predBinN []) [lit 8, var83,
      .const (nmL ["Std", "Tactic", "BVDecide", "BVBinPred", "eq"]) [],
      Expr.mkAppN (.const exVarN []) [lit 4, lit 3]]])).isNone

-- the fuel bounds the reading
#guard (readLogical noFind 0 constTrue).isNone

/-! ## Definitions unfold only to closed values -/

def defOf (v : Expr) : ConstantInfo :=
  .defnInfo { name := nmL ["aux"], levelParams := [], type := predT } v .opaque

def findAux (v : Expr) : Name → Option ConstantInfo :=
  fun n => if n == nmL ["aux"] then some (defOf v) else none

#guard match readLogical (findAux constTrue) 10 (.const (nmL ["aux"]) []) with
  | some (.const true) => true
  | _ => false

-- a value with a loose bound variable is not unfolded
#guard (unfold? (findAux (.bvar 0)) (.const (nmL ["aux"]) [])).isNone

/-! ## Recognition -/

#guard (bvUnsatSpine (.const unsatThmName []) [constTrue, lit 0, lit 1]).isSome
#guard (bvUnsatSpine (.const unsatThmName []) [constTrue, lit 0]).isNone
#guard (bvUnsatSpine (.const unsatThmName [.zero]) [constTrue, lit 0, lit 1]).isNone
#guard (bvUnsatSpine (.const bvUnsatName []) [constTrue, lit 0, lit 1]).isNone

#guard isBVNativeAxName (nmL ["thm", "_native", "bv_decide", "ax_1_5"])
#guard !isBVNativeAxName (nmL ["thm", "_native", "bv_decide", "cert"])
#guard !isBVNativeAxName (nmL ["thm", "bv_decide", "ax_1_5"])

/-! ## The gate refuses without the pinned closure -/

#guard !pinsOk noFind noProj
#guard !bvUnsatOk noFind noProj constTrue (.lit (.strVal ""))
#guard !bvUnsatHit noFind noProj
  (.app (.app (.const unsatThmName []) constTrue) (.lit (.strVal ""))) (.const (nmL ["ax"]) [])

end ConLecheTests.BVUnsat
