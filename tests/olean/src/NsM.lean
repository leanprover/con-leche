module
-- (task #421) reads only NsH's nested type formers: the worker presents
-- each block whole (generate-only), its generated recursors reading the
-- containers' constructors (List.cons, Array.mk, Option.some, NsBox.two,
-- NsRose.node, ...), which no record of NsM reads.
import NsH
theorem nsL (x : NsL) : x = x := rfl
theorem nsA (x : NsA) : x = x := rfl
theorem nsO (x : NsO) : x = x := rfl
theorem nsU (x : NsU) : x = x := rfl
theorem nsR (x : NsR) : x = x := rfl
theorem nsP (x : NsP) : x = x := rfl
theorem nsD (x : NsD) : x = x := rfl
theorem nsM1 (x : NsM1) : x = x := rfl
theorem nsM2 (x : NsM2) : x = x := rfl
