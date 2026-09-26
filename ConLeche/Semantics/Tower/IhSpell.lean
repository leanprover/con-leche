module

import ConLeche.Semantics.Tower.SumRecCase
public import ConLeche.Semantics.Tower.FixFamI
public import ConLeche.Semantics.Tower.SumRec

@[expose] public section

/-!
# The ih spellings (tasks #188, #202)

The `AnnotTerm` spellings shared by the P tier's readings of the kernel's
generated recursor rules and the semantic recursor body: the recursive
positions, a field's index expressions and telescope moved to an ih
frame (`ihIdxAt`, `ihIdxAtM`, `ihTeleAtR`), the ih application under a
field's telescope (`ihAppAVb`, generic in the elimination bit and in
the number of extra binders between the fields and the minors), and
the squash regime's recursor body (`sqFixBodyAV`, task #202 A2): the
(only) minor at the fields read off the indices (`srcAV`) with the ih
applications, as a β-redex over the constructor's field telescope.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]


/-! ## The ih frame -/

/-- Field `i`'s index expression (read at the field's own frame: the
parameters, the `i` earlier fields) moved under all `nF` fields, `l`
ih binders below them and `o` extras between the parameters and the
fields — `structIdxAt`'s reading. -/
def ihIdxAt (nF o i l : Nat) (E : AnnotTerm) : AnnotTerm :=
  (E.liftN (nF - i + l) 0).liftN o (nF + l)

/-- `structIdxAt nF o i l m`'s reading: field `i`'s expression sitting
under `m` binders of the field's own telescope, moved as `ihIdxAt`
moves it (task #202). -/
def ihIdxAtM (nF o i l m : Nat) (E : AnnotTerm) : AnnotTerm :=
  (E.liftN (nF - i + l) m).liftN o (nF + l + m)

/-- `structTeleAt`'s reading: field `i`'s telescope (its entries read
at the field's own frame, binder `k` under `k` earlier telescope
binders) moved to the ih binder's frame. -/
def ihTeleAtGo (nF o i l : Nat) : Nat → List (Nat × Nat × AnnotTerm) → List (Nat × Nat × AnnotTerm)
  | _, [] => []
  | k, d :: tl => (d.1, d.2.1, ihIdxAtM nF o i l k d.2.2) :: ihTeleAtGo nF o i l (k + 1) tl

/-- The whole telescope moved (binder `k` under `k` earlier ones). -/
def ihTeleAtR (nF o i l : Nat) (tl : List (Nat × Nat × AnnotTerm)) : List (Nat × Nat × AnnotTerm) :=
  ihTeleAtGo nF o i l 0 tl

@[simp] theorem ihTeleAtR_nil (nF o i l : Nat) : ihTeleAtR nF o i l [] = [] := rfl

theorem mem_ihTeleAtGo {nF o i l : Nat} :
    ∀ {k : Nat} {tl : List (Nat × Nat × AnnotTerm)} {d : Nat × Nat × AnnotTerm},
      d ∈ ihTeleAtGo nF o i l k tl → ∃ d' ∈ tl, d.2.1 = d'.2.1
  | _, [], _, h => nomatch h
  | k, d' :: tl, d, h => by
    simp only [ihTeleAtGo, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨d', List.mem_cons_self, rfl⟩
    · obtain ⟨d'', hd'', he⟩ := mem_ihTeleAtGo h
      exact ⟨d'', List.mem_cons_of_mem _ hd'', he⟩


/-! ## The squash regime's body -/

/-- The source of field `j` among the constructor's index expressions:
the first index position whose expression is the field's variable
(`none` when the field is not an index — a `Prop` field under the
subsingleton criterion). -/
def srcOfEs (Es : List AnnotTerm) (nF j : Nat) : Option Nat :=
  (List.range Es.length).find? fun l =>
    match Es.getD l default with
    | .bvar k => k = nF - 1 - j
    | _ => false

/-- The sources of all `nF` fields. -/
def srcList (Es : List AnnotTerm) (nF : Nat) : List (Option Nat) :=
  (List.range nF).map (srcOfEs Es nF)


end ConLeche.Semantics
