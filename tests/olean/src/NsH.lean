module
-- (task #421) nested inductive blocks, through List, Array, Option, a
-- user container (NsC's NsBox), a nested user container (NsRose), a pair
-- in a list (List (Nat × NsP)), and a
-- mutual block nested through Option and Array.  A worker for NsM
-- presents them in NsH's restricted unit, installed generate-only: the
-- generated recursors (and their auxiliary ones) read the containers'
-- constructors, which the reach must hold.
public import NsC
-- a recursive field through a definition: the positivity check unfolds
-- NsFun, so the generated recursor's inductive hypothesis reads Nat,
-- which only NsFun's value names (not NsD's declared types)
@[expose] public def NsFun (α : Type) : Type := Nat → α
public inductive NsD : Type where
  | leaf : NsD
  | mk : NsFun NsD → NsD
public inductive NsL : Type where
  | mk : List NsL → NsL
public inductive NsA : Type where
  | mk : Array NsA → NsA
public inductive NsO : Type where
  | leaf : NsO
  | mk : Option NsO → NsO
public inductive NsU : Type where
  | mk : NsBox NsU → NsU
public inductive NsR : Type where
  | mk : NsRose NsR → NsR
public inductive NsP : Type where
  | mk : List (Nat × NsP) → NsP
mutual
public inductive NsM1 : Type where
  | mk : List NsM2 → NsM1
public inductive NsM2 : Type where
  | leaf : NsM2
  | mk : Option NsM1 → Array NsM2 → NsM2
end
