--#export W'.depth_sup AccC.ex

/- End-to-end fixture (task #208; inductive audit #206, A9 / §2 "probed
   and clean"): reflexive blocks — a `Type`-valued W-shape with a
   large eliminator, and an `Acc` clone (one constructor, `Prop`, large
   eliminator by the subsingleton criterion).  Both install natively
   and the stream accepts.  (The name is historical: the class was
   once left to an external tool.)

   official: 0.  con-leche: 0 (both modes).
   Probe of record: _tmp/indaudit/probes/P/ReflexiveTool.lean. -/
inductive W'
  | sup (f : Nat → W')

inductive AccC (r : Nat → Nat → Prop) : Nat → Prop
  | intro (x : Nat) (h : ∀ y, r y x → AccC r y) : AccC r x

noncomputable def W'.depth : W' → Nat := fun w => W'.rec (fun _ ih => ih 0 + 1) w

theorem W'.depth_sup (f : Nat → W') : W'.depth (W'.sup f) = W'.depth (f 0) + 1 := rfl

noncomputable def AccC.ex {r : Nat → Nat → Prop} {x : Nat} (h : AccC r x) : Nat :=
  AccC.rec (motive := fun _ _ => Nat) (fun _ _ _ => 0) h
