module
-- Guards task #502: M loads UfH and UfT, and uses UfH's hz.  Compiled against a stand-in UfT
-- (build.sh).
public import UfH
public import UfT
theorem m : True := by have := @hz; trivial
