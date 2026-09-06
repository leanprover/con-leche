import Lech

/-!
Regression tests for the canonical zero-ness datum (task #161 P5
candidate, `Lech/Kernel/ZeroSet.lean` + `Lech/Verify/ZeroSet.lean`).
Nothing in the checker consumes the module yet, so these guards are
what would notice the canonicalizer, the name order, or the mirrored
operations drifting.
-/

namespace LechTests.ZeroSet

open Lech

private def a : Name := .str .anonymous "a"
private def b : Name := .str .anonymous "b"
private def c : Name := .str .anonymous "c"
private def n1 : Name := .num .anonymous 1
private def ab : Name := .str a "b"

/-! ## The name order is a strict total order (spot checks) -/

#guard Name.blt a b
#guard !Name.blt b a
#guard !Name.blt a a
-- constructor order: anonymous < str < num
#guard Name.blt .anonymous a
#guard Name.blt a n1
-- prefix first, then payload
#guard Name.blt a ab
#guard Name.cmp ab ab == .eq

/-! ## `ofList` canonicalizes: sorts and deduplicates -/

#guard (Lech.ZeroSet.ofList [c, a, b, a]).names == [a, b, c]
#guard (Lech.ZeroSet.ofList []).names == []
#guard (Lech.ZeroSet.ofList [a, a, a]).names == [a]

/-! ## The operations -/

#guard ((Lech.ZeroSet.ofList [a, c]).union (Lech.ZeroSet.ofList [b, c])).names
  == [a, b, c]
#guard (Lech.ZeroSet.singleton b).union (Lech.ZeroSet.singleton a)
  == Lech.ZeroSet.ofList [a, b]
#guard (Lech.ZeroSet.ofList [a, b]).mem b
#guard !(Lech.ZeroSet.ofList [a, b]).mem c
#guard (Lech.ZeroSet.ofList [a]).subset (Lech.ZeroSet.ofList [a, b])
#guard !(Lech.ZeroSet.ofList [a, c]).subset (Lech.ZeroSet.ofList [a, b])
#guard Lech.ZeroSet.empty.isEmpty

/-! ## Canonicity: equal members ⇒ equal values (`==` decides the
predicate, no containment test) -/

#guard Lech.ZeroSet.ofList [a, b] == Lech.ZeroSet.ofList [b, a, b]
#guard ZPropWhen.equiv (.ifAllZero (Lech.ZeroSet.ofList [a, b]))
  (.ifAllZero (Lech.ZeroSet.ofList [b, a]))
#guard !ZPropWhen.equiv (.ifAllZero (Lech.ZeroSet.ofList [a]))
  (.ifAllZero (Lech.ZeroSet.ofList [a, b]))
#guard !ZPropWhen.equiv .never (.ifAllZero Lech.ZeroSet.empty)
-- and hashing sees the canonical form, so equal data hash equally
#guard hash (Lech.ZeroSet.ofList [a, b]) == hash (Lech.ZeroSet.ofList [b, a])

/-! ## The readout and the pushforward -/

#guard Level.zeronessOfZ .zero == .ifAllZero Lech.ZeroSet.empty
#guard Level.zeronessOfZ (.succ (.param a)) == .never
#guard Level.zeronessOfZ (.max (.param b) (.imax (.param c) (.param a)))
  == .ifAllZero (Lech.ZeroSet.ofList [a, b])
#guard Level.zeronessOfZ (.max (.param a) (.succ .zero)) == .never

-- `substPW_self`: instantiating at the declaration's own parameters is
-- the identity (the law the free+normalizing hybrid falsified).
#guard Level.substPWZ [a, b] [.param a, .param b]
  (.ifAllZero (Lech.ZeroSet.ofList [a, b]))
  == .ifAllZero (Lech.ZeroSet.ofList [a, b])
-- a parameter substituted by a `succ` level makes the datum `never`
#guard Level.substPWZ [a] [.succ .zero]
  (.ifAllZero (Lech.ZeroSet.ofList [a, b])) == .never
-- and by another parameter: renaming, canonically
#guard Level.substPWZ [a] [.param c]
  (.ifAllZero (Lech.ZeroSet.ofList [a, b]))
  == .ifAllZero (Lech.ZeroSet.ofList [b, c])

/-! ## The bridge to the landed free representation -/

#guard ZPropWhen.ofFree (.ifAllZero [b, a, b])
  == ZPropWhen.ofFree (.ifAllZero [a, b])
#guard ZPropWhen.ofFree
    (ZPropWhen.ifAllZero (Lech.ZeroSet.ofList [a, b])).toFree
  == (ZPropWhen.ifAllZero (Lech.ZeroSet.ofList [a, b]))
#guard (ZPropWhen.ofFree (Level.zeronessOf (.max (.param b) (.param a))))
  == Level.zeronessOfZ (.max (.param b) (.param a))
-- the free side needs `equiv` where the canonical side has `==`
#guard PropWhen.equiv (.ifAllZero [a, b]) (.ifAllZero [b, a, a])
#guard !((PropWhen.ifAllZero [a, b]) == (PropWhen.ifAllZero [b, a, a]))

end LechTests.ZeroSet
