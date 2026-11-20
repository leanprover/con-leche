module

public import ConLeche.Cached.Justify

/-!
# The input's record mates, read

`recordMates ds` maps every name an inductive block of `ds` declares to (at least) every name that
block declares.
-/

public section

namespace ConLeche.Cached

open ConLeche

private theorem inner_mono (ns : Array Name) :
    ∀ (bl : List ConstantInfo) (m : Std.HashMap Name (Array Name)) (k x : Name),
      x ∈ m.getD k #[] →
        x ∈ (bl.foldl (fun m b => m.insert b.name (m.getD b.name #[] ++ ns)) m).getD k #[]
  | [], _, _, _, h => h
  | b :: bl, m, k, x, h => by
    simp only [List.foldl_cons]
    refine inner_mono ns bl _ k x ?_
    rw [Std.HashMap.getD_insert]
    split
    · next he =>
      have : b.name = k := eq_of_beq he
      subst this
      exact Array.mem_append_left _ h
    · exact h

private theorem inner_spec (ns : Array Name) :
    ∀ (bl : List ConstantInfo) (m : Std.HashMap Name (Array Name)) (b : ConstantInfo), b ∈ bl →
      ∀ x ∈ ns, x ∈ (bl.foldl (fun m b => m.insert b.name (m.getD b.name #[] ++ ns)) m).getD
        b.name #[]
  | [], _, _, h, _, _ => absurd h List.not_mem_nil
  | b' :: bl, m, b, hb, x, hx => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hb with rfl | hb
    · refine inner_mono ns bl _ _ x ?_
      rw [Std.HashMap.getD_insert, beq_self_eq_true]
      exact Array.mem_append_right _ hx
    · exact inner_spec ns bl _ b hb x hx

private def step (m : Std.HashMap Name (Array Name)) (d : Declaration) :
    Std.HashMap Name (Array Name) :=
  match d with
  | .indDecl block _ =>
    let ns := (block.map (·.name)).toArray
    block.foldl (fun m b => m.insert b.name (m.getD b.name #[] ++ ns)) m
  | _ => m

private theorem step_mono (m : Std.HashMap Name (Array Name)) (d : Declaration) (k x : Name)
    (h : x ∈ m.getD k #[]) : x ∈ (step m d).getD k #[] := by
  cases d with
  | indDecl block nP => exact inner_mono _ block m k x h
  | _ => exact h

private theorem fold_mono :
    ∀ (ds : List Declaration) (m : Std.HashMap Name (Array Name)) (k x : Name),
      x ∈ m.getD k #[] → x ∈ (ds.foldl step m).getD k #[]
  | [], _, _, _, h => h
  | d :: ds, m, k, x, h => fold_mono ds _ k x (step_mono m d k x h)

private theorem fold_spec :
    ∀ (ds : List Declaration) (m : Std.HashMap Name (Array Name)) {block : List ConstantInfo}
      {nP : Nat}, Declaration.indDecl block nP ∈ ds → ∀ b ∈ block, ∀ b' ∈ block,
        b'.name ∈ (ds.foldl step m).getD b.name #[]
  | [], _, _, _, h, _, _, _, _ => absurd h List.not_mem_nil
  | d :: ds, m, block, nP, h, b, hb, b', hb' => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · refine fold_mono ds _ _ _ ?_
      exact inner_spec _ block m b hb _ (by simpa using ⟨b', hb', rfl⟩)
    · exact fold_spec ds _ h b hb b' hb'

/-- **Two names one block of the input declares are each other's mates.** -/
theorem recordMates_spec {ds : Array Declaration} {block : List ConstantInfo} {nP : Nat}
    (h : Declaration.indDecl block nP ∈ ds.toList) {b b' : ConstantInfo} (hb : b ∈ block)
    (hb' : b' ∈ block) : b'.name ∈ (recordMates ds).getD b.name #[] := by
  have he : recordMates ds = ds.toList.foldl step {} := by
    unfold recordMates; rw [← Array.foldl_toList]; rfl
  rw [he]
  exact fold_spec _ _ h b hb b' hb'

end ConLeche.Cached
