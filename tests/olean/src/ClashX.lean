module
prelude
-- Guards task #464: a stand-in for ClashB under another name (tests/olean.sh puts ClashB's
-- files in its place, a pair Lean's own import refuses).
public import Tiny
public section
def clashX : T := T.b
end
