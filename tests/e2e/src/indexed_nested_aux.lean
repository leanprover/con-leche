--#export TV.size_example

/- End-to-end test: an *indexed* nested-auxiliary recursor — the shape
   `RecRuleFire`'s certification deliberately excludes (`.nested` is
   certified only at `majorIdx = rulePrefix`; index premises between
   the prefix and the major leave the rule `.inert`, and a *matched*
   inert rule positively declines at fire time).  `TV` nests through
   the indexed family `Vec`, so `TV.rec_1`'s type is
   `∀ … prefix … {n : Nat} (t : Vec (TV α) n), motive_2 n t` —
   `majorIdx = rulePrefix + 1`.  `TV.size`'s below/brecOn machinery
   only typechecks when the auxiliary rules fire, and `size_example`'s
   rfl forces them on concrete majors, so the stream currently pins
   the limitation as a positive decline (exit 2); it flips to accept
   when the indexed nested-aux certification lands (user ruling
   2026-08-24: this limitation gets a fix regardless of streams
   needing it).  No known stream exercises the shape (the full
   Mathlib census found zero indexed nested-aux rules). -/

inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons {n : Nat} : α → Vec α n → Vec α (n + 1)

inductive TV (α : Type) where
  | node : α → {n : Nat} → Vec (TV α) n → TV α

mutual
  def TV.size {α : Type} : TV α → Nat
    | .node _ v => TV.sizeVec v + 1
  def TV.sizeVec {α : Type} : {n : Nat} → Vec (TV α) n → Nat
    | _, .nil => 0
    | _, .cons t v => t.size + TV.sizeVec v
end

theorem TV.size_example :
    Eq (TV.node true (.cons (.node false .nil) .nil) : TV Bool).size 2 :=
  rfl
