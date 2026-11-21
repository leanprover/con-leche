module

public import ConLeche.Frontend.Olean.Group
public import ConLeche.Verify.Frontend.Olean.Emit

/-!
# One inductive group's record, the same on any emitter

Task #440.  The stream reader's builder reads a block's record (`.ind ts cts rs`) only through
the emitter's tables (`Emit.nm`, `Emit.ex`), and what it builds of the block depends only on what
the indices stand for: `declOfF_ind_same`, where two records resolve to the same constants
(`TyRes`, `CtorRes`, `RecRes`), whatever indices either uses, their records are equal.  The
builder's verdict is characterised by `validateIndF_inr` (its constructors are the block's,
looked up by name, in the order the types list them).

`Emit.block_res`: the record `Emit.block` pushes resolves, on the emitter's tables, to the block's
constants of each kind, in order.  `emitLoop_inds`: every `inductive` record of the emission walk
is a block of the merge (`BlockOf`: the members, constructors and recursors the walk takes at an
inductive type).  `blockRecs_mergedOfList`: the recursors a merged list lists under `x` are its
first constants of each name that are recursors of a block listing `x`, in the list's order.

`home_group`: where the merge's blocks agree, an inductive type of the merge has its block's
record among the emission's declarations; `groupRecord_res`: a group's record built alone
(`groupRecord`); `block_same`: two block records built from the same constants are one record.
-/

public section

namespace ConLeche.Frontend.Olean

open ConLeche ConLeche.Frontend

/-! ## Lists related pointwise -/

/-- Two lists related pointwise. -/
inductive Forall₂ {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Forall₂ R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} : R a b → Forall₂ R as bs →
      Forall₂ R (a :: as) (b :: bs)

theorem Forall₂.imp {α β : Type} {R S : α → β → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {xs : List α} {ys : List β}, Forall₂ R xs ys → Forall₂ S xs ys
  | _, _, .nil => .nil
  | _, _, .cons a t => .cons (h _ _ a) (Forall₂.imp h t)

theorem Forall₂.imp_map {α β γ : Type} {R : α → β → Prop} {S : α → γ → Prop} {g : β → γ}
    (h : ∀ a b, R a b → S a (g b)) :
    ∀ {xs : List α} {ys : List β}, Forall₂ R xs ys → Forall₂ S xs (ys.map g)
  | _, _, .nil => .nil
  | _, _, .cons a t => .cons (h _ _ a) (Forall₂.imp_map h t)

theorem Forall₂.append {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β} {xs' : List α} {ys' : List β}, Forall₂ R xs ys → Forall₂ R xs' ys' →
      Forall₂ R (xs ++ xs') (ys ++ ys')
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons a t, h => .cons a (Forall₂.append t h)

theorem Forall₂.mem_left {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, Forall₂ R xs ys → ∀ x ∈ xs, ∃ y ∈ ys, R x y
  | _, _, .nil, _, hx => by cases hx
  | _, _, .cons h t, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨_, List.mem_cons_self, h⟩
    · obtain ⟨y, hy, hr⟩ := Forall₂.mem_left t x hx
      exact ⟨y, List.mem_cons_of_mem _ hy, hr⟩

theorem Forall₂.mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, Forall₂ R xs ys → ∀ y ∈ ys, ∃ x ∈ xs, R x y
  | _, _, .nil, _, hy => by cases hy
  | _, _, .cons h t, y, hy => by
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨_, List.mem_cons_self, h⟩
    · obtain ⟨x, hx, hr⟩ := Forall₂.mem_right t y hy
      exact ⟨x, List.mem_cons_of_mem _ hx, hr⟩

theorem forall₂_meet {α β γ : Type} {R : α → γ → Prop} {R' : β → γ → Prop}
    {xs : List α} {ys : List β} {L : List γ} (h1 : Forall₂ R xs L) (h2 : Forall₂ R' ys L) :
    Forall₂ (fun x y => ∃ c, R x c ∧ R' y c) xs ys := by
  induction h1 generalizing ys with
  | nil => cases h2; exact .nil
  | cons ha _ ih => cases h2 with
    | cons hb t2 => exact .cons ⟨_, ha, hb⟩ (ih t2)

theorem forall₂_meet_left {α β γ : Type} {R : γ → α → Prop} {R' : γ → β → Prop}
    {L : List γ} {xs : List α} {ys : List β} (h1 : Forall₂ R L xs) (h2 : Forall₂ R' L ys) :
    Forall₂ (fun x y => ∃ c, R c x ∧ R' c y) xs ys := by
  induction h1 generalizing ys with
  | nil => cases h2; exact .nil
  | cons ha _ ih => cases h2 with
    | cons hb t2 => exact .cons ⟨_, ha, hb⟩ (ih t2)

theorem forall₂_comp {α β γ : Type} {R : α → β → Prop} {S : β → γ → Prop}
    {xs : List α} {ys : List β} {zs : List γ} (h1 : Forall₂ R xs ys) (h2 : Forall₂ S ys zs) :
    Forall₂ (fun x z => ∃ y, R x y ∧ S y z) xs zs := by
  induction h1 generalizing zs with
  | nil => cases h2; exact .nil
  | cons ha _ ih => cases h2 with
    | cons hb t2 => exact .cons ⟨_, ha, hb⟩ (ih t2)

theorem forall₂_of_getElem {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β} (hl : ys.length = xs.length),
      (∀ (j : Nat) (hj : j < xs.length), R xs[j] (ys[j]'(hl ▸ hj))) → Forall₂ R xs ys
  | [], [], _, _ => .nil
  | x :: xs, y :: ys, hl, h =>
    .cons (h 0 (by simp)) (forall₂_of_getElem (by simpa using hl) (fun j hj => h (j + 1) (by simpa using hj)))
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem getElem?_forall₂ {α β : Type} {S : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, Forall₂ S xs ys → ∀ k : Nat,
      (xs[k]? = none ∧ ys[k]? = none) ∨ ∃ a b, xs[k]? = some a ∧ ys[k]? = some b ∧ S a b
  | [], [], .nil, k => .inl ⟨rfl, rfl⟩
  | x :: xs, y :: ys, .cons h t, 0 => .inr ⟨x, y, rfl, rfl, h⟩
  | x :: xs, y :: ys, .cons h t, k + 1 => by simpa using getElem?_forall₂ t k

theorem map_forall₂ {α β δ : Type} {f : α → δ} {g : β → δ} {S : α → β → Prop}
    (hS : ∀ a b, S a b → f a = g b) :
    ∀ {xs : List α} {ys : List β}, Forall₂ S xs ys → xs.map f = ys.map g
  | [], [], .nil => rfl
  | x :: xs, y :: ys, .cons h t => by rw [List.map_cons, List.map_cons, hS x y h, map_forall₂ hS t]

theorem filterMap_forall₂ {α β γ : Type} {R : α → β → Prop} {f : α → Option γ} {g : β → Option γ} :
    ∀ {xs : List α} {ys : List β}, Forall₂ R xs ys → (∀ x y, x ∈ xs → y ∈ ys → R x y → f x = g y) →
      xs.filterMap f = ys.filterMap g
  | [], [], .nil, _ => rfl
  | x :: xs, y :: ys, .cons hr t, h => by
    simp only [List.filterMap_cons, h x y List.mem_cons_self List.mem_cons_self hr,
      filterMap_forall₂ t (fun a b ha hb => h a b (List.mem_cons_of_mem _ ha) (List.mem_cons_of_mem _ hb))]

theorem mapM_forall₂ {ε α β γ : Type} {F : α → Except ε γ} {G : β → Except ε γ} {S : α → β → Prop}
    (hS : ∀ a b, S a b → F a = G b) :
    ∀ {xs : List α} {ys : List β}, Forall₂ S xs ys → xs.mapM F = ys.mapM G
  | [], [], .nil => rfl
  | x :: xs, y :: ys, .cons h t => by
    simp only [List.mapM_cons, hS x y h, mapM_forall₂ hS t]

theorem mapM_res {ε α γ δ : Type} {F : α → Except ε δ} {G : γ → δ} {R : α → γ → Prop}
    (hR : ∀ a c, R a c → F a = .ok (G c)) :
    ∀ {xs : List α} {L : List γ}, Forall₂ R xs L → xs.mapM F = .ok (L.map G)
  | [], [], .nil => rfl
  | x :: xs, c :: L, .cons h t => by
    simp [List.mapM_cons, hR x c h, mapM_res hR t, bind, Except.bind, pure, Except.pure]

theorem mapM_ok_length {ε α β : Type} {f : α → Except ε β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys → ys.length = xs.length
  | [], ys, h => by simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  | x :: xs, ys, h => by
    simp only [List.mapM_cons, bind, Except.bind] at h
    cases hx : f x with
    | error e => rw [hx] at h; cases h
    | ok y =>
      rw [hx] at h
      simp only at h
      cases hxs : xs.mapM f with
      | error e => rw [hxs] at h; cases h
      | ok zs =>
        rw [hxs] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp [mapM_ok_length hxs]

theorem mapM_some_forall₂ {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → Forall₂ (fun x y => f x = some y) xs ys
  | [], ys, h => by simp only [List.mapM_nil, pure, Option.some.injEq] at h; subst h; exact .nil
  | x :: xs, ys, h => by
    simp only [List.mapM_cons, bind, Option.bind] at h
    cases hx : f x with
    | none => rw [hx] at h; cases h
    | some y =>
      rw [hx] at h
      simp only at h
      cases hxs : xs.mapM f with
      | none => rw [hxs] at h; cases h
      | some zs =>
        rw [hxs] at h
        simp only [pure, Option.some.injEq] at h
        subst h
        exact .cons hx (mapM_some_forall₂ hxs)

theorem mapM_filterMap {α β γ : Type} {f : α → Option β} (g : β → Option γ) :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys →
      ys.filterMap g = xs.filterMap (fun x => (f x).bind g)
  | [], ys, h => by simp only [List.mapM_nil, pure, Option.some.injEq] at h; subst h; rfl
  | x :: xs, ys, h => by
    have h2 := mapM_some_forall₂ h
    cases h2 with
    | cons hx t =>
      rename_i y ys'
      have hxs : xs.mapM f = some ys' := by
        simp only [List.mapM_cons, bind, Option.bind, hx] at h
        cases hxs : xs.mapM f with
        | none => rw [hxs] at h; cases h
        | some zs => rw [hxs] at h; simp only [pure, Option.some.injEq, List.cons.injEq] at h; rw [h.2]
      simp only [List.filterMap_cons, hx, Option.bind_some, mapM_filterMap g hxs]

theorem mapM_append_inv {α β : Type} {f : α → Option β} :
    ∀ {xs xs' : List α} {ys : List β}, (xs ++ xs').mapM f = some ys →
      ∃ y1 y2, xs.mapM f = some y1 ∧ xs'.mapM f = some y2 ∧ ys = y1 ++ y2
  | [], xs', ys, h => ⟨[], ys, rfl, by simpa using h, rfl⟩
  | x :: xs, xs', ys, h => by
    have h2 := mapM_some_forall₂ h
    cases h2 with
    | cons hx t =>
      rename_i y ys'
      have hxs : (xs ++ xs').mapM f = some ys' := by
        simp only [List.cons_append, List.mapM_cons, bind, Option.bind, hx] at h
        cases hxs : (xs ++ xs').mapM f with
        | none => rw [hxs] at h; cases h
        | some zs => rw [hxs] at h; simp only [pure, Option.some.injEq, List.cons.injEq] at h; rw [h.2]
      obtain ⟨y1, y2, h1, h2, rfl⟩ := mapM_append_inv hxs
      refine ⟨y :: y1, y2, ?_, h2, rfl⟩
      simp [List.mapM_cons, hx, h1, bind, Option.bind, pure]

theorem bind_ok_inv {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- **A loop with an early exit, in `Except`**: where every step either goes on with the state
`g` makes or stops with an exit value `Bad` says something of, the loop's result is the fold of
`g`, or such an exit. -/
theorem forIn_char {α β τ ε : Type} (Bad : β → Prop) (g : α → τ → τ)
    {f : α → Option β × τ → Except ε (ForInStep (Option β × τ))} :
    ∀ (xs : List α), (∀ x ∈ xs, ∀ t r, f x (none, t) = .ok r →
      r = .yield (none, g x t) ∨ ∃ b t', Bad b ∧ r = .done (some b, t')) →
    ∀ t res, forIn xs (none, t) f = .ok res →
      res = (none, xs.foldl (fun t x => g x t) t) ∨ ∃ b t', Bad b ∧ res = (some b, t')
  | [], _, t, res, h => by
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at h
    exact .inl (by simp [h])
  | x :: xs, hf, t, res, h => by
    simp only [List.forIn_cons, bind, Except.bind] at h
    cases hx : f x (none, t) with
    | error e => rw [hx] at h; cases h
    | ok r =>
      rw [hx] at h
      rcases hf x List.mem_cons_self t r hx with rfl | ⟨b, t', hb, rfl⟩
      · simp only at h
        rcases forIn_char Bad g xs (fun y hy => hf y (List.mem_cons_of_mem _ hy)) _ res h with h1 | h1
        · exact .inl (by simpa using h1)
        · exact .inr h1
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        exact .inr ⟨b, t', hb, h.symm⟩

theorem nodup_map_inj {α β : Type} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {a b : α}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => by cases ha
  | x :: l, hnd, a, b, ha, hb, hab => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.1 ha with ha' | ha' <;> rcases List.mem_cons.1 hb with hb' | hb'
    · rw [ha', hb']
    · subst ha'; exact absurd (hab ▸ List.mem_map_of_mem hb') hnd.1
    · subst hb'; exact absurd (hab.symm ▸ List.mem_map_of_mem ha') hnd.1
    · exact nodup_map_inj hnd.2 ha' hb' hab

theorem filter_filter_map {α β : Type} (p q : α → Bool) (f : α → β) :
    ∀ l : List α, ((l.filter p).filter q).map f = l.filterMap (fun x => if p x && q x then some (f x) else none)
  | [] => rfl
  | x :: l => by
    have ih := filter_filter_map p q f l
    cases hp : p x <;> cases hq : q x <;>
      simp only [List.filter_cons, hp, hq, Bool.false_eq_true, ↓reduceIte, Bool.and_self,
        Bool.and_false, Bool.false_and, List.map_cons, List.filterMap_cons, ih]

theorem filterMap_filter_map {α β γ : Type} (p : α → Bool) (g : α → β) (G : β → Option γ) :
    ∀ l : List α, ((l.filter p).map g).filterMap G = l.filterMap (fun x => if p x then G (g x) else none)
  | [] => rfl
  | x :: l => by
    simp only [List.filter_cons, List.filterMap_cons]
    by_cases hp : p x = true
    · simp only [hp, ↓reduceIte, List.map_cons, List.filterMap_cons, filterMap_filter_map p g G l]
    · simp only [hp, Bool.false_eq_true, ↓reduceIte, filterMap_filter_map p g G l]


/-! ## The builder's verdict on a block -/

/-- The constructor a name stands for in a block's records. -/
@[expose] def ctorAt (ctorNames : List Name) (cts : List IndCtorRec) (n : Name) : Option IndCtorRec :=
  ((ctorNames.foldl (fun (mi : Std.HashMap Name Nat × Nat) n => (mi.1.insert n mi.2, mi.2 + 1))
    ({}, 0)).1[n]?).bind (cts.toArray[·]?)

theorem ctorFold_spec (f : Name → Option (IndCtorRec × Name)) :
    ∀ (ns : List Name) (t : Array (IndCtorRec × Name)) (j : Nat),
    (ns.foldl (fun (aj : Array (IndCtorRec × Name) × Nat) n => (match f n with
      | some c => aj.1.push c | none => aj.1, aj.2 + 1)) (t, j)).1 = t ++ (ns.filterMap f).toArray
  | [], t, j => by simp
  | n :: ns, t, j => by
    simp only [List.foldl_cons, List.filterMap_cons]
    cases f n with
    | none => exact ctorFold_spec f ns t (j + 1)
    | some c =>
      simp only
      rw [ctorFold_spec f ns (t.push c) (j + 1)]
      simp

theorem zipFold_spec {α β : Type} (g : α → List β) : ∀ (xs : List α) (t : Array β),
    (xs.foldl (fun t x => t ++ (g x).toArray) t).toList = t.toList ++ xs.flatMap g
  | [], t => by simp
  | x :: xs, t => by
    simp only [List.foldl_cons, List.flatMap_cons]
    rw [zipFold_spec g xs _]
    simp

/-- The constructor records a block lists, each with the type that lists it, in the block's
order. -/
@[expose] def ctorsListed (ctorNames : List Name) (cts : List IndCtorRec)
    (tyNames : List Name) (listed : List (List Name)) : List (IndCtorRec × Name) :=
  (tyNames.zip listed).flatMap fun tn => (tn.2.filterMap (ctorAt ctorNames cts)).map (·, tn.1)

/-- **The builder's verdict on a block that it accepts**: no type unsafe, the parameter count the
first type's, and the constructor records the ones the types list, looked up by name, in the
types' order, each with the type that lists it. -/
theorem validateIndF_inr {nm : Nat → M Name} {lv : Nat → M Level} {ex : Nat → M Expr} {tys cts rcs cts1 nPd}
  (h : validateIndF nm lv ex tys cts rcs = .ok (.inr (cts1, nPd))) :
    tys.any (·.isUnsafe) = false ∧ nPd = (tys.map (·.numParams)).head?.getD 0 ∧
      ∃ tyNames listed ctorNames, tys.mapM (fun t => nm t.cv.name) = .ok tyNames ∧
      tys.mapM (fun t => t.ctors.mapM nm) = .ok listed ∧ cts.mapM (fun c => nm c.cv.name) = .ok ctorNames ∧
      cts1 = ctorsListed ctorNames cts tyNames listed := by
  unfold validateIndF at h
  cases hu : tys.any (·.isUnsafe)
  rotate_left
  · simp only [hu, ite_true, pure, Except.pure] at h; cases h
  simp only [hu, Bool.false_eq_true, ite_false] at h
  cases hp : ((tys.map (·.numParams)).all fun x => x == (tys.map (·.numParams)).head?.getD 0)
  · simp only [hp, Bool.false_eq_true, ite_false, pure, Except.pure] at h; cases h
  simp only [hp, ite_true] at h
  obtain ⟨tyNames, h1, h⟩ := bind_ok_inv h
  obtain ⟨tyTypes, h2, h⟩ := bind_ok_inv h
  obtain ⟨listed, h3, h⟩ := bind_ok_inv h
  obtain ⟨ctorNames, h4, h⟩ := bind_ok_inv h
  by_cases hn : listed.flatten.Nodup
  rotate_left
  · simp only [hn, ↓reduceIte, pure, Except.pure] at h; cases h
  simp only [hn, ↓reduceIte] at h
  cases hl : (listed.flatten.length == cts.length)
  · simp only [hl, Bool.false_eq_true, ite_false, pure, Except.pure] at h; cases h
  simp only [hl, ite_true] at h
  obtain ⟨s, hs, h⟩ := bind_ok_inv h
  have hc := forIn_char (fun b => ∃ v, b = Sum.inl v)
    (fun (tn : Name × List Name) (arr : Array (IndCtorRec × Name)) =>
      arr ++ ((tn.2.filterMap (ctorAt ctorNames cts)).map (·, tn.1)).toArray) _ (by
      intro x hx t r hr
      obtain ⟨s', hs', hr⟩ := bind_ok_inv hr
      have hi := forIn_char (fun b => ∃ v, b = Sum.inl v)
        (fun (n : Name) (aj : Array (IndCtorRec × Name) × Nat) =>
          (match (ctorAt ctorNames cts n).map (·, x.1) with
          | some c => aj.1.push c | none => aj.1, aj.2 + 1)) _ (by
          intro n hn' t r hr
          simp only [bind, Except.bind, pure, Except.pure] at hr
          have hg : ∀ (k : Nat) (c : IndCtorRec), (ctorNames.foldl (fun (mi : Std.HashMap Name Nat × Nat) n =>
              (mi.1.insert n mi.2, mi.2 + 1)) ({}, 0)).1[n]? = some k → cts.toArray[k]? = some c →
              ctorAt ctorNames cts n = some c := by
            intro k c h1 h2; simp only [ctorAt, h1, Option.bind_some, h2]
          split at hr
          · rename_i k hk
            split at hr
            · rename_i c hc
              have hcc := hg k c hk hc
              rw [hcc, Option.map_some]
              repeat' split at hr
              all_goals first
                | (cases hr; done)
                | (cases hr; exact .inr ⟨_, _, ⟨_, rfl⟩, rfl⟩)
                | (cases hr; exact .inl rfl)
            · cases hr; exact .inr ⟨_, _, ⟨_, rfl⟩, rfl⟩
          · cases hr; exact .inr ⟨_, _, ⟨_, rfl⟩, rfl⟩
          ) _ _ hs'
      rcases hi with rfl | ⟨b, t', hb, rfl⟩
      · simp only [pure, Except.pure, Except.ok.injEq] at hr
        subst hr
        exact .inl (by
          rw [List.map_filterMap]
          rw [ctorFold_spec (fun n => (ctorAt ctorNames cts n).map (·, x.1))])
      · simp only [pure, Except.pure, Except.ok.injEq] at hr
        subst hr
        exact .inr ⟨b, _, hb, rfl⟩) _ _ hs
  rcases hc with rfl | ⟨b, t', ⟨v, rfl⟩, rfl⟩
  rotate_left
  · simp only [pure, Except.pure, Except.ok.injEq] at h; cases h
  simp only at h
  obtain ⟨s2, hs2, h⟩ := bind_ok_inv h
  have hc2 := forIn_char (fun b => ∃ v, b = Sum.inl v) (fun (_ : IndRecRec) (_ : Unit) => ()) _ (by
    intro x hx t r hr
    simp only [bind, Except.bind, pure, Except.pure] at hr
    repeat' split at hr
    all_goals first
      | (cases hr; done)
      | (cases hr; exact .inr ⟨_, _, ⟨_, rfl⟩, rfl⟩)
      | (cases hr; exact .inl rfl)
      | skip
    rename_i v hloop o a ha
    have hn2 := forIn_char (fun b => ∃ v, b = Sum.inl v) (fun (_ : Name × Expr) (_ : Unit) => ()) _ (by
      intro y hy t r hr
      repeat' split at hr
      all_goals first
        | (cases hr; done)
        | (cases hr; exact .inr ⟨_, _, ⟨_, rfl⟩, rfl⟩)
        | (cases hr; exact .inl rfl)) _ _ hloop
    rcases hn2 with rfl | ⟨b, t', hb, rfl⟩
    · cases ha
    · cases ha; cases hr; exact .inr ⟨_, _, hb, rfl⟩) _ _ hs2
  rcases hc2 with rfl | ⟨b, t', ⟨v, rfl⟩, rfl⟩
  rotate_left
  · simp only [pure, Except.pure, Except.ok.injEq] at h; cases h
  simp only [pure, Except.pure, Except.ok.injEq, Sum.inr.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨rfl, rfl, tyNames, listed, ctorNames, h1, h3, h4, ?_⟩
  rw [zipFold_spec]
  simp [ctorsListed]

/-- A block's record that builds is of no unsafe type. -/
theorem declOfF_ind_safe {nm : Nat → M Name} {lv : Nat → M Level} {ex : Nat → M Expr}
    {ts : List IndTypeRec} {cts : List IndCtorRec} {rs : List IndRecRec} {d : Declaration}
    (hd : declOfF nm lv ex (.ind ts cts rs) = .ok (.inl d)) : ts.any (·.isUnsafe) = false := by
  simp only [declOfF, bind, Except.bind] at hd
  cases hv : validateIndF nm lv ex ts cts rs with
  | error e => rw [hv] at hd; cases hd
  | ok v =>
    rw [hv] at hd
    rcases v with v | ⟨cts1, nPd⟩
    · simp [pure, Except.pure] at hd
    · exact (validateIndF_inr hv).1

/-! ## What a block's records resolve to -/

/-- A record's name, level parameters and type, resolved. -/
@[expose] def CvRes (nm : Nat → M Name) (ex : Nat → M Expr) (cv : CVRec) (c : CEntryF Name Expr) : Prop :=
  nm cv.name = .ok c.name ∧ cv.levelParams.mapM nm = .ok c.levelParams ∧ ex cv.type = .ok c.type

/-- An inductive type's record, resolved. -/
@[expose] def TyRes (nm : Nat → M Name) (ex : Nat → M Expr) (t : IndTypeRec) (c : CEntryF Name Expr) : Prop :=
  CvRes nm ex t.cv c ∧ ∃ ni all cs nn ir irf,
    c.kind = .induct t.numParams ni all cs nn ir t.isUnsafe irf ∧ t.ctors.mapM nm = .ok cs

/-- A constructor's record, resolved. -/
@[expose] def CtorRes (nm : Nat → M Name) (ex : Nat → M Expr) (t : IndCtorRec) (c : CEntryF Name Expr) : Prop :=
  CvRes nm ex t.cv c ∧ ∃ ind cidx iu, c.kind = .ctor ind cidx t.numParams t.numFields iu

/-- A recursor rule's record, resolved. -/
@[expose] def RuleRes (nm : Nat → M Name) (ex : Nat → M Expr) (ru : RuleRec) (x : Name × Nat × Expr) : Prop :=
  nm ru.ctor = .ok x.1 ∧ ru.nfields = x.2.1 ∧ ex ru.rhs = .ok x.2.2

/-- A recursor's record, resolved. -/
@[expose] def RecRes (nm : Nat → M Name) (ex : Nat → M Expr) (t : IndRecRec) (c : CEntryF Name Expr) : Prop :=
  CvRes nm ex t.cv c ∧ ∃ all rules,
    c.kind = .recur all t.numParams t.numIndices t.numMotives t.numMinors rules t.k t.isUnsafe ∧
    Forall₂ (RuleRes nm ex) t.rules rules

theorem cvOfF_res {nm : Nat → M Name} {lv : Nat → M Level} {ex : Nat → M Expr} {cv : CVRec}
    {c : CEntryF Name Expr} (h : CvRes nm ex cv c) :
    cvOfF nm lv ex cv = .ok ⟨c.name, c.levelParams, c.type⟩ := by
  obtain ⟨h1, h2, h3⟩ := h
  simp [cvOfF, h1, h2, h3, bind, Except.bind, pure, Except.pure]

theorem filterMap_ctorAt {S : IndCtorRec → IndCtorRec → Prop} (ns : List Name) {cts cts' : List IndCtorRec}
    (h : Forall₂ S cts cts') :
    Forall₂ S (ns.filterMap (ctorAt ctorNames cts)) (ns.filterMap (ctorAt ctorNames cts')) := by
  induction ns with
  | nil => exact .nil
  | cons n ns ih =>
    simp only [List.filterMap_cons, ctorAt]
    cases (ctorNames.foldl (fun (mi : Std.HashMap Name Nat × Nat) n => (mi.1.insert n mi.2, mi.2 + 1))
      ({}, 0)).1[n]? with
    | none => exact ih
    | some k =>
      simp only [Option.bind_some, List.getElem?_toArray]
      rcases getElem?_forall₂ h k with ⟨h1, h2⟩ | ⟨a, b, h1, h2, hab⟩
      · rw [h1, h2]; exact ih
      · rw [h1, h2]; exact .cons hab ih

theorem forall₂_map_pair {α : Type} {S : IndCtorRec → IndCtorRec → Prop} (T : α) :
    ∀ {xs ys : List IndCtorRec}, Forall₂ S xs ys →
      Forall₂ (fun a b => S a.1 b.1 ∧ a.2 = b.2) (xs.map (·, T)) (ys.map (·, T))
  | _, _, .nil => .nil
  | _, _, .cons hab t => .cons ⟨hab, rfl⟩ (forall₂_map_pair T t)

theorem ctorsListed_forall₂ {S : IndCtorRec → IndCtorRec → Prop} {cts cts' : List IndCtorRec}
    (h : Forall₂ S cts cts') : ∀ (tns : List (Name × List Name)),
    Forall₂ (fun a b => S a.1 b.1 ∧ a.2 = b.2)
      (tns.flatMap fun tn => (tn.2.filterMap (ctorAt ctorNames cts)).map (·, tn.1))
      (tns.flatMap fun tn => (tn.2.filterMap (ctorAt ctorNames cts')).map (·, tn.1))
  | [] => .nil
  | tn :: tns => by
    simp only [List.flatMap_cons]
    exact Forall₂.append
      (forall₂_map_pair tn.1 (filterMap_ctorAt (ctorNames := ctorNames) tn.2 h))
      (ctorsListed_forall₂ h tns)

/-- **A block's record is the same on two emitters' tables** where both resolve to the same
constants, whatever indices each uses: the builder's verdict and record depend only on what the
indices stand for. -/
theorem declOfF_ind_same {nm nm' : Nat → M Name} {lv lv' : Nat → M Level} {ex ex' : Nat → M Expr}
    {ts ts' : List IndTypeRec} {cts cts' : List IndCtorRec} {rs rs' : List IndRecRec}
    {L1 L2 L3 : List (CEntryF Name Expr)}
    (ht : Forall₂ (TyRes nm ex) ts L1) (ht' : Forall₂ (TyRes nm' ex') ts' L1)
    (hc : Forall₂ (CtorRes nm ex) cts L2) (hc' : Forall₂ (CtorRes nm' ex') cts' L2)
    (hr : Forall₂ (RecRes nm ex) rs L3) (hr' : Forall₂ (RecRes nm' ex') rs' L3)
    {d d' : Declaration}
    (hd : declOfF nm lv ex (.ind ts cts rs) = .ok (.inl d))
    (hd' : declOfF nm' lv' ex' (.ind ts' cts' rs') = .ok (.inl d')) : d = d' := by
  simp only [declOfF, bind, Except.bind] at hd hd'
  cases hv : validateIndF nm lv ex ts cts rs with
  | error e => rw [hv] at hd; cases hd
  | ok v =>
  cases hv' : validateIndF nm' lv' ex' ts' cts' rs' with
  | error e => rw [hv'] at hd'; cases hd'
  | ok v' =>
  rw [hv] at hd; rw [hv'] at hd'
  rcases v with v | ⟨cts1, nPd⟩
  · simp [pure, Except.pure] at hd
  rcases v' with v' | ⟨cts1', nPd'⟩
  · simp [pure, Except.pure] at hd'
  simp only at hd hd'
  obtain ⟨-, hP, tyN, listed, cn, htn, hl, hcn, rfl⟩ := validateIndF_inr hv
  obtain ⟨-, hP', tyN', listed', cn', htn', hl', hcn', rfl⟩ := validateIndF_inr hv'
  have e0 : tyN = tyN' := by
    rw [mapM_res (F := fun (t : IndTypeRec) => nm t.cv.name) (G := CEntryF.name)
      (fun t c (h : TyRes nm ex t c) => h.1.1) ht] at htn
    rw [mapM_res (F := fun (t : IndTypeRec) => nm' t.cv.name) (G := CEntryF.name)
      (fun t c (h : TyRes nm' ex' t c) => h.1.1) ht'] at htn'
    cases htn; cases htn'; rfl
  have kc : ∀ {nm : Nat → M Name} {ex : Nat → M Expr} (t : IndTypeRec) (c : CEntryF Name Expr), TyRes nm ex t c →
      t.ctors.mapM nm = .ok (match c.kind with | .induct _ _ _ cs .. => cs | _ => []) := by
    intro nm ex t c ⟨_, ni, all, cs, nn, ir, irf, hk, hm⟩
    rw [hk]; exact hm
  have e1 : listed = listed' := by
    rw [mapM_res (F := fun (t : IndTypeRec) => t.ctors.mapM nm) (fun t c h => kc t c h) ht] at hl
    rw [mapM_res (F := fun (t : IndTypeRec) => t.ctors.mapM nm') (fun t c h => kc t c h) ht'] at hl'
    cases hl; cases hl'; rfl
  have e2 : cn = cn' := by
    rw [mapM_res (F := fun (c : IndCtorRec) => nm c.cv.name) (G := CEntryF.name) (fun t c (h : CtorRes nm ex t c) => h.1.1) hc] at hcn
    rw [mapM_res (F := fun (c : IndCtorRec) => nm' c.cv.name) (G := CEntryF.name) (fun t c (h : CtorRes nm' ex' t c) => h.1.1) hc'] at hcn'
    cases hcn; cases hcn'; rfl
  have e3 : nPd = nPd' := by
    rw [hP, hP', map_forall₂ (S := fun x y => ∃ c, TyRes nm ex x c ∧ TyRes nm' ex' y c)
      (fun a b ⟨c, ⟨_, ni, all, cs, nn, ir, irf, hk, _⟩, ⟨_, ni', all', cs', nn', ir', irf', hk', _⟩⟩ => by
        rw [hk] at hk'; exact (CKindF.induct.inj hk').1) (forall₂_meet ht ht')]
  subst e0 e1 e2 e3
  have hcc : Forall₂ _ (ctorsListed cn cts tyN listed) (ctorsListed cn cts' tyN listed) :=
    ctorsListed_forall₂ (ctorNames := cn) (forall₂_meet hc hc') (tyN.zip listed)
  cases hb : indBlockOfF nm lv ex ts (ctorsListed cn cts tyN listed) rs nPd with
  | error e => rw [hb] at hd; cases hd
  | ok b =>
  cases hb' : indBlockOfF nm' lv' ex' ts' (ctorsListed cn cts' tyN listed) rs' nPd with
  | error e => rw [hb'] at hd'; cases hd'
  | ok b' =>
  rw [hb] at hd; rw [hb'] at hd'
  simp only [pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at hd hd'
  subst hd hd'
  rw [← Except.ok.injEq, ← hb, ← hb']
  unfold indBlockOfF
  rw [mapM_forall₂ (G := fun t => do pure (ConstantInfo.indInfo (← cvOfF nm' lv' ex' t.cv) {}))
      (fun a b ⟨c, h1, h2⟩ => by rw [cvOfF_res h1.1, cvOfF_res h2.1]) (forall₂_meet ht ht'),
    mapM_forall₂ (G := fun (c, T) => do
        pure (ConstantInfo.ctorInfo (← cvOfF nm' lv' ex' c.cv) c.numParams c.numFields T))
      (fun ⟨ca, Ta⟩ ⟨cb, Tb⟩ ⟨⟨c, h1, h2⟩, hT⟩ => by
        dsimp only at hT ⊢
        obtain ⟨g1, ind, cidx, iu, hk⟩ := h1
        obtain ⟨g2, ind', cidx', iu', hk'⟩ := h2
        rw [hk] at hk'
        obtain ⟨-, -, e1, e2, -⟩ := CKindF.ctor.inj hk'
        rw [cvOfF_res g1, cvOfF_res g2, e1, e2, hT]) hcc,
    mapM_forall₂ (G := fun r => do
        let rules ← r.rules.mapM (ruleOfF nm' lv' ex')
        pure (ConstantInfo.recInfo (← cvOfF nm' lv' ex' r.cv)
          (r.numParams + r.numMotives + r.numMinors + r.numIndices)
          (r.numParams + r.numMotives + r.numMinors) r.k rules))
      (fun a b ⟨c, h1, h2⟩ => by
        obtain ⟨g1, all, rules, hk, hru⟩ := h1
        obtain ⟨g2, all', rules', hk', hru'⟩ := h2
        rw [hk] at hk'
        obtain ⟨-, e1, e2, e3, e4, rfl, e6, -⟩ := CKindF.recur.inj hk'
        rw [mapM_forall₂ (G := ruleOfF nm' lv' ex') (fun x y ⟨z, ⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩⟩ => by
          simp [ruleOfF, a1, a3, b1, b3, a2, b2]) (forall₂_meet hru hru'), cvOfF_res g1, cvOfF_res g2,
          e1, e2, e3, e4, e6]) (forall₂_meet hr hr')]

/-! ## A block's records on an emitter's tables -/

/-- An inductive type's record on the tables. -/
@[expose] def IndTyOf (em : Emit) (t : IndTypeRec) (c : CEntry) : Prop :=
  CvOf em t.cv c ∧ ∃ ni all cs nn ir irf,
    c.kind = .induct t.numParams ni all cs nn ir t.isUnsafe irf ∧ t.ctors.map (em.names[·]?) = cs.map some

/-- A constructor's record on the tables. -/
@[expose] def IndCtorOf (em : Emit) (t : IndCtorRec) (c : CEntry) : Prop :=
  CvOf em t.cv c ∧ ∃ ind cidx iu, c.kind = .ctor ind cidx t.numParams t.numFields iu

/-- A recursor rule's record on the tables. -/
@[expose] def RuleOf (em : Emit) (ru : RuleRec) (x : Name × Nat × Expr) : Prop :=
  em.names[ru.ctor]? = some x.1 ∧ ru.nfields = x.2.1 ∧ em.exprs[ru.rhs]? = some x.2.2

/-- A recursor's record on the tables. -/
@[expose] def IndRecOf (em : Emit) (t : IndRecRec) (c : CEntry) : Prop :=
  CvOf em t.cv c ∧ ∃ all rules,
    c.kind = .recur all t.numParams t.numIndices t.numMotives t.numMinors rules t.k t.isUnsafe ∧
    Forall₂ (RuleOf em) t.rules rules

theorem names_map_mono {a b : Emit} (h : Emit.Sub a b) {l : List Nat} {ns : List Name}
    (hl : l.map (a.names[·]?) = ns.map some) : l.map (b.names[·]?) = ns.map some := by
  rw [← hl]
  apply List.map_congr_left
  intro i hi
  have : a.names[i]? ∈ l.map (a.names[·]?) := List.mem_map_of_mem hi
  rw [hl] at this
  obtain ⟨n, -, hn⟩ := List.mem_map.mp this
  rw [← hn]
  exact h.names i n hn.symm

theorem IndTyOf.mono {a b : Emit} (h : Emit.Sub a b) {t : IndTypeRec} {c : CEntry} :
    IndTyOf a t c → IndTyOf b t c
  | ⟨h1, ni, all, cs, nn, ir, irf, h2, h3⟩ => ⟨h1.mono h, ni, all, cs, nn, ir, irf, h2, names_map_mono h h3⟩

theorem IndCtorOf.mono {a b : Emit} (h : Emit.Sub a b) {t : IndCtorRec} {c : CEntry} :
    IndCtorOf a t c → IndCtorOf b t c
  | ⟨h1, h2⟩ => ⟨h1.mono h, h2⟩

theorem RuleOf.mono {a b : Emit} (h : Emit.Sub a b) {ru : RuleRec} {x : Name × Nat × Expr} :
    RuleOf a ru x → RuleOf b ru x
  | ⟨h1, h2, h3⟩ => ⟨h.names _ _ h1, h2, h.exprs _ _ h3⟩

theorem IndRecOf.mono {a b : Emit} (h : Emit.Sub a b) {t : IndRecRec} {c : CEntry} :
    IndRecOf a t c → IndRecOf b t c
  | ⟨h1, all, rules, h2, h3⟩ => ⟨h1.mono h, all, rules, h2, Forall₂.imp (fun _ _ => RuleOf.mono h) h3⟩

theorem IndTyOf.res {em : Emit} {t : IndTypeRec} {c : CEntry} (h : IndTyOf em t c) :
    TyRes em.nm em.ex t c.toCEntryF := by
  obtain ⟨⟨h1, h2, h3⟩, ni, all, cs, nn, ir, irf, h4, h5⟩ := h
  exact ⟨⟨by simp [Emit.nm, h1, pure, Except.pure], mapM_nm h2, by simp [Emit.ex, h3, pure, Except.pure]⟩,
    ni, all, cs, nn, ir, irf, h4, mapM_nm h5⟩

theorem IndCtorOf.res {em : Emit} {t : IndCtorRec} {c : CEntry} (h : IndCtorOf em t c) :
    CtorRes em.nm em.ex t c.toCEntryF := by
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := h
  exact ⟨⟨by simp [Emit.nm, h1, pure, Except.pure], mapM_nm h2, by simp [Emit.ex, h3, pure, Except.pure]⟩, h4⟩

theorem IndRecOf.res {em : Emit} {t : IndRecRec} {c : CEntry} (h : IndRecOf em t c) :
    RecRes em.nm em.ex t c.toCEntryF := by
  obtain ⟨⟨h1, h2, h3⟩, all, rules, h4, h5⟩ := h
  exact ⟨⟨by simp [Emit.nm, h1, pure, Except.pure], mapM_nm h2, by simp [Emit.ex, h3, pure, Except.pure]⟩,
    all, rules, h4, Forall₂.imp (fun ru x ⟨a1, a2, a3⟩ =>
      ⟨by simp [Emit.nm, a1, pure, Except.pure], a2, by simp [Emit.ex, a3, pure, Except.pure]⟩) h5⟩

theorem tys_res {em : Emit} {ts : List IndTypeRec} {L : List CEntry} (h : Forall₂ (IndTyOf em) ts L) :
    Forall₂ (TyRes em.nm em.ex) ts (L.map (·.toCEntryF)) :=
  Forall₂.imp_map (R := IndTyOf em) (fun _ _ q => IndTyOf.res q) h

theorem ctors_res {em : Emit} {ts : List IndCtorRec} {L : List CEntry} (h : Forall₂ (IndCtorOf em) ts L) :
    Forall₂ (CtorRes em.nm em.ex) ts (L.map (·.toCEntryF)) :=
  Forall₂.imp_map (R := IndCtorOf em) (fun _ _ q => IndCtorOf.res q) h

theorem recs_res {em : Emit} {ts : List IndRecRec} {L : List CEntry} (h : Forall₂ (IndRecOf em) ts L) :
    Forall₂ (RecRes em.nm em.ex) ts (L.map (·.toCEntryF)) :=
  Forall₂.imp_map (R := IndRecOf em) (fun _ _ q => IndRecOf.res q) h

/-- A fold that adds to the tables, pushing one item for each element `p` keeps. -/
theorem fold_rel {α β : Type} {Q : Emit → α → β → Prop}
    (hQ : ∀ {a b : Emit} {x : α} {c : β}, Emit.Sub a b → Q a x c → Q b x c) (p : β → Bool)
    {f : Emit × Array α → β → Emit × Array α}
    (hf : ∀ st acc c, Emit.Sub st (f (st, acc) c).1 ∧ (f (st, acc) c).1.out = st.out ∧
      (if p c then ∃ x, (f (st, acc) c).2 = acc.push x ∧ Q (f (st, acc) c).1 x c
       else (f (st, acc) c).2 = acc)) :
    ∀ (l : List β) (st : Emit) (acc : Array α) (L0 : List β), Forall₂ (Q st) acc.toList L0 →
      Emit.Sub st (l.foldl f (st, acc)).1 ∧ (l.foldl f (st, acc)).1.out = st.out ∧
      Forall₂ (Q (l.foldl f (st, acc)).1) (l.foldl f (st, acc)).2.toList (L0 ++ l.filter p)
  | [], st, acc, L0, h => ⟨Emit.Sub.refl _, rfl, by simpa using h⟩
  | c :: l, st, acc, L0, h => by
    simp only [List.foldl_cons]
    obtain ⟨h1, h2, h3⟩ := hf st acc c
    generalize hx : f (st, acc) c = x at h1 h2 h3
    obtain ⟨x1, x2⟩ := x
    simp only at h1 h2 h3 ⊢
    have hacc : Forall₂ (Q x1) x2.toList (L0 ++ (if p c then [c] else [])) := by
      by_cases hp : p c = true
      · simp only [hp, ↓reduceIte] at h3 ⊢
        obtain ⟨y, hy, hq⟩ := h3
        rw [hy, Array.toList_push]
        exact Forall₂.append (Forall₂.imp (fun _ _ => hQ h1) h) (.cons hq .nil)
      · simp only [hp, Bool.false_eq_true, ↓reduceIte, List.append_nil] at h3 ⊢
        rw [h3]
        exact Forall₂.imp (fun _ _ => hQ h1) h
    obtain ⟨g1, g2, g3⟩ := fold_rel (Q := Q) hQ p hf l x1 x2 _ hacc
    refine ⟨h1.trans g1, g2.trans h2, ?_⟩
    rw [List.filter_cons]
    by_cases hp : p c = true
    · simpa [hp] using g3
    · simpa [hp] using g3

theorem Emit.names'_map (st : Emit) (ns : List Name) :
    (st.names' ns).2.map ((st.names' ns).1.names[·]?) = ns.map some := by
  have := (names_fold ns st #[]).2.2.2
  simpa [Emit.names'] using this

theorem ruleStep_rel (rules : List (Name × Nat × Expr)) (st : Emit) :
    Emit.Sub st (rules.foldl Emit.ruleStep (st, #[])).1 ∧
      (rules.foldl Emit.ruleStep (st, #[])).1.out = st.out ∧
      Forall₂ (RuleOf (rules.foldl Emit.ruleStep (st, #[])).1)
        (rules.foldl Emit.ruleStep (st, #[])).2.toList rules := by
  have := fold_rel (Q := fun em ru x => RuleOf em ru x) (fun h hr => hr.mono h) (fun _ => true)
    (f := Emit.ruleStep) (by
      intro st acc x
      obtain ⟨cn, nf, rhs⟩ := x
      obtain ⟨h1, h2, -, h4⟩ := Emit.name_spec st cn
      obtain ⟨g1, g2, -, g4⟩ := Emit.expr_spec (st.name cn).1 rhs
      exact ⟨h1.trans g1, g4.trans h4, ⟨_, rfl, g1.names _ _ h2, rfl, g2⟩⟩) rules st #[] [] .nil
  have hf : rules.filter (fun _ => true) = rules := List.filter_eq_self.2 (fun _ _ => rfl)
  rw [hf, List.nil_append] at this
  exact this

/-- **The record `Emit.block` pushes** resolves, on the emitter's tables, to the block's types,
constructors and recursors, those of each kind in their order. -/
theorem Emit.block_res (st : Emit) (tys ctors recs : List CEntry) :
    ∃ ts cts rs, (st.block tys ctors recs).out = st.out.push (.ind ts cts rs) ∧
      Emit.Sub st (st.block tys ctors recs) ∧
      Forall₂ (IndTyOf (st.block tys ctors recs)) ts (tys.filter (·.kind.tag == 5)) ∧
      Forall₂ (IndCtorOf (st.block tys ctors recs)) cts (ctors.filter (·.kind.tag == 6)) ∧
      Forall₂ (IndRecOf (st.block tys ctors recs)) rs (recs.filter (·.kind.tag == 7)) := by
  have F1 := fold_rel (Q := IndTyOf) (fun h q => q.mono h) (·.kind.tag == 5) (f := Emit.tyStep) (by
    intro st acc c
    unfold Emit.tyStep
    cases hk : c.kind with
    | induct np ni all cs nn ir iu irf =>
      obtain ⟨h1, h2, -, h4⟩ := Emit.cv_spec st c
      obtain ⟨g1, -, g4⟩ := Emit.names'_spec (st.cv c).1 cs
      refine ⟨h1.trans g1, g4.trans h4, ?_⟩
      simp only [CKindF.tag, beq_self_eq_true, ↓reduceIte]
      exact ⟨_, rfl, h2.mono g1, ni, all, cs, nn, ir, irf, hk, Emit.names'_map _ _⟩
    | _ => exact ⟨Emit.Sub.refl _, rfl, by simp [CKindF.tag]⟩) tys st #[] [] .nil
  generalize hX1 : tys.foldl Emit.tyStep (st, #[]) = X1 at F1
  obtain ⟨a1, a2, a3⟩ := F1
  have F2 := fold_rel (Q := IndCtorOf) (fun h q => q.mono h) (·.kind.tag == 6) (f := Emit.ctorStep) (by
    intro st acc c
    unfold Emit.ctorStep
    cases hk : c.kind with
    | ctor ind cidx np nf iu =>
      obtain ⟨h1, h2, -, h4⟩ := Emit.cv_spec st c
      obtain ⟨g1, -, -, g4⟩ := Emit.name_spec (st.cv c).1 ind
      refine ⟨h1.trans g1, g4.trans h4, ?_⟩
      simp only [CKindF.tag, beq_self_eq_true, ↓reduceIte]
      exact ⟨_, rfl, h2.mono g1, ind, cidx, iu, hk⟩
    | _ => exact ⟨Emit.Sub.refl _, rfl, by simp [CKindF.tag]⟩) ctors X1.1 #[] [] .nil
  generalize hX2 : ctors.foldl Emit.ctorStep (X1.1, #[]) = X2 at F2
  obtain ⟨b1, b2, b3⟩ := F2
  have F3 := fold_rel (Q := IndRecOf) (fun h q => q.mono h) (·.kind.tag == 7) (f := Emit.recStep) (by
    intro st acc c
    unfold Emit.recStep
    cases hk : c.kind with
    | recur all np ni nmo nmi rules k iu =>
      obtain ⟨h1, h2, -, h4⟩ := Emit.cv_spec st c
      obtain ⟨g1, g4, g5⟩ := ruleStep_rel rules (st.cv c).1
      refine ⟨h1.trans g1, g4.trans h4, ?_⟩
      simp only [CKindF.tag, beq_self_eq_true, ↓reduceIte]
      exact ⟨_, rfl, h2.mono g1, all, rules, hk, g5⟩
    | _ => exact ⟨Emit.Sub.refl _, rfl, by simp [CKindF.tag]⟩) recs X2.1 #[] [] .nil
  generalize hX3 : recs.foldl Emit.recStep (X2.1, #[]) = X3 at F3
  obtain ⟨c1, c2, c3⟩ := F3
  have hb : st.block tys ctors recs = X3.1.push (.ind X1.2.toList X2.2.toList X3.2.toList) := by
    subst hX3 hX2 hX1
    rfl
  obtain ⟨p1, -, p3⟩ := Emit.push_spec X3.1 (.ind X1.2.toList X2.2.toList X3.2.toList)
  rw [hb]
  refine ⟨_, _, _, by rw [p3, c2, b2, a2], ((a1.trans b1).trans c1).trans p1,
    Forall₂.imp (fun _ _ (q : IndTyOf _ _ _) => (q.mono (b1.trans c1)).mono p1) (by simpa using a3),
    Forall₂.imp (fun _ _ (q : IndCtorOf _ _ _) => (q.mono c1).mono p1) (by simpa using b3),
    Forall₂.imp (fun _ _ (q : IndRecOf _ _ _) => q.mono p1) (by simpa using c3)⟩

theorem filter_toF (k : Nat) {l l' : List CEntry} (h : l.map (·.toCEntryF) = l'.map (·.toCEntryF)) :
    (l.filter (·.kind.tag == k)).map (·.toCEntryF) = (l'.filter (·.kind.tag == k)).map (·.toCEntryF) := by
  have e : ∀ m : List CEntry, (m.filter (·.kind.tag == k)).map (·.toCEntryF) =
      (m.map (·.toCEntryF)).filter (·.kind.tag == k) := by
    intro m; rw [List.filter_map]; rfl
  rw [e, e, h]

/-- **Two block records built from the same constants are the same record**, whatever tables
either emitter's indices point into. -/
theorem block_same {E G : Emit} {tysH ctorsH recsH tysR ctorsR recsR : List CEntry}
    {ts cts rs ts' cts' rs'} {p d : Declaration}
    (hp : declOfF E.nm E.lv E.ex (.ind ts cts rs) = .ok (.inl p))
    (h1 : Forall₂ (IndTyOf E) ts (tysH.filter (·.kind.tag == 5)))
    (h2 : Forall₂ (IndCtorOf E) cts (ctorsH.filter (·.kind.tag == 6)))
    (h3 : Forall₂ (IndRecOf E) rs (recsH.filter (·.kind.tag == 7)))
    (hd : declOfF G.nm G.lv G.ex (.ind ts' cts' rs') = .ok (.inl d))
    (g1 : Forall₂ (IndTyOf G) ts' (tysR.filter (·.kind.tag == 5)))
    (g2 : Forall₂ (IndCtorOf G) cts' (ctorsR.filter (·.kind.tag == 6)))
    (g3 : Forall₂ (IndRecOf G) rs' (recsR.filter (·.kind.tag == 7)))
    (e1 : tysH.map (·.toCEntryF) = tysR.map (·.toCEntryF))
    (e2 : ctorsH.map (·.toCEntryF) = ctorsR.map (·.toCEntryF))
    (e3 : recsH.map (·.toCEntryF) = recsR.map (·.toCEntryF)) : p = d := by
  refine declOfF_ind_same (L1 := (tysH.filter (·.kind.tag == 5)).map (·.toCEntryF))
    (L2 := (ctorsH.filter (·.kind.tag == 6)).map (·.toCEntryF))
    (L3 := (recsH.filter (·.kind.tag == 7)).map (·.toCEntryF))
    (tys_res h1) (by rw [filter_toF 5 e1]; exact tys_res g1)
    (ctors_res h2) (by rw [filter_toF 6 e2]; exact ctors_res g2)
    (recs_res h3) (by rw [filter_toF 7 e3]; exact recs_res g3) hp hd

/-! ## The walk's blocks -/

/-- **A block of the merge**: the members, constructors and recursors the walk takes at its
inductive type `n0`. -/
@[expose] def BlockOf (mg : Merged) (recMap : Std.HashMap Name (Array Name)) (tys ctors recs : List CEntry) :
    Prop :=
  ∃ n0 c0 np ni all cs nn ir iu irf, mg.map[n0]? = some c0 ∧
    c0.kind = .induct np ni all cs nn ir iu irf ∧ tys = blockTys mg all ∧
    ctors = blockCtors mg tys ∧ recs = blockRecs mg recMap n0

/-- **An `inductive` record is a block's**, on the tables. -/
@[expose] def IndOk (mg : Merged) (recMap : Std.HashMap Name (Array Name)) (em : Emit) : DeclRec → Prop
  | .ind ts cts rs => ∃ tys ctors recs, BlockOf mg recMap tys ctors recs ∧
      Forall₂ (IndTyOf em) ts (tys.filter (·.kind.tag == 5)) ∧
      Forall₂ (IndCtorOf em) cts (ctors.filter (·.kind.tag == 6)) ∧
      Forall₂ (IndRecOf em) rs (recs.filter (·.kind.tag == 7))
  | _ => True

theorem IndOk.mono {mg : Merged} {recMap : Std.HashMap Name (Array Name)} {a b : Emit}
    (h : Emit.Sub a b) : ∀ {r : DeclRec}, IndOk mg recMap a r → IndOk mg recMap b r
  | .ind _ _ _, ⟨tys, ctors, recs, hB, h1, h2, h3⟩ => ⟨tys, ctors, recs, hB,
      Forall₂.imp (fun _ _ (q : IndTyOf _ _ _) => q.mono h) h1,
      Forall₂.imp (fun _ _ (q : IndCtorOf _ _ _) => q.mono h) h2,
      Forall₂.imp (fun _ _ (q : IndRecOf _ _ _) => q.mono h) h3⟩
  | .ax _ _, _ => trivial
  | .defn _ _ _ _, _ => trivial
  | .thm _ _, _ => trivial
  | .opaq _ _ _, _ => trivial
  | .quot _ _, _ => trivial

/-- A stack item's block is the merge's. -/
@[expose] def WorkBlock (mg : Merged) (recMap : Std.HashMap Name (Array Name)) : Work → Prop
  | .block tys ctors recs => BlockOf mg recMap tys ctors recs
  | _ => True

theorem Emit.one_ind (mg : Merged) (recMap : Std.HashMap Name (Array Name)) (st : Emit) (c : CEntry)
    (ho : ∀ r ∈ st.out, IndOk mg recMap st r) : ∀ r ∈ (st.one c).out, IndOk mg recMap (st.one c) r := by
  obtain ⟨h1, -, h3, -⟩ := Emit.one_spec st c
  intro r hr
  rcases h3 r hr with h | h
  · exact (ho r h).mono h1
  · cases r with
    | ind _ _ _ => exact h.elim
    | _ => trivial

theorem Emit.ones_ind (mg : Merged) (recMap : Std.HashMap Name (Array Name)) (cs : List CEntry) :
    ∀ (st : Emit), (∀ r ∈ st.out, IndOk mg recMap st r) →
      ∀ r ∈ (cs.foldl Emit.one st).out, IndOk mg recMap (cs.foldl Emit.one st) r := by
  induction cs with
  | nil => intro st h; exact h
  | cons c cs ih => intro st h; exact ih _ (Emit.one_ind mg recMap st c h)

/-- **Every `inductive` record of the walk is a block of the merge**, on the final tables. -/
theorem emitLoop_inds (mg : Merged) (recMap : Std.HashMap Name (Array Name)) (stack : List Work)
    (st : Emit) : (∀ w ∈ stack, WorkBlock mg recMap w) → (∀ r ∈ st.out, IndOk mg recMap st r) →
    ∀ r ∈ (emitLoop mg recMap stack st).out, IndOk mg recMap (emitLoop mg recMap stack st) r := by
  have marked : ∀ {s0 s1 : Emit}, Emit.Sub s0 s1 → s1.out = s0.out →
      (∀ r ∈ s0.out, IndOk mg recMap s0 r) → ∀ r ∈ s1.out, IndOk mg recMap s1 r := by
    intro s0 s1 hs ho h r hr
    rw [ho] at hr
    exact (h r hr).mono hs
  have usesB : ∀ {cs : List CEntry} {rest : List Work}, (∀ w ∈ rest, WorkBlock mg recMap w) →
      ∀ w ∈ Work.usesOf cs ++ rest, WorkBlock mg recMap w := by
    intro cs rest h w hw
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨c, -, hw⟩ := List.mem_flatMap.mp hw
      obtain ⟨_, -, rfl⟩ := List.mem_map.mp hw
      trivial
    · exact h w hw
  fun_induction emitLoop mg recMap stack st
  all_goals intro hw ho
  case case1 st => exact ho
  case case2 st c rest ih =>
    exact ih (fun w hm => hw w (List.mem_cons_of_mem _ hm)) (Emit.one_ind mg recMap st c ho)
  case case3 st cs rest ih =>
    exact ih (fun w hm => hw w (List.mem_cons_of_mem _ hm)) (Emit.ones_ind mg recMap cs st ho)
  case case4 st ts cs rs rest ih =>
    refine ih (fun w hm => hw w (List.mem_cons_of_mem _ hm)) ?_
    obtain ⟨ts', cts', rs', hout, hS, h1, h2, h3⟩ := Emit.block_res st ts cs rs
    intro r hr
    rw [hout] at hr
    rcases Array.mem_push.mp hr with hr | rfl
    · exact (ho r hr).mono hS
    · exact ⟨ts, cs, rs, hw _ List.mem_cons_self, h1, h2, h3⟩
  case case5 st n rest hv ih => exact ih (fun w hm => hw w (List.mem_cons_of_mem _ hm)) ho
  case case6 st n rest hv hc ih => exact ih (fun w hm => hw w (List.mem_cons_of_mem _ hm)) ho
  case case7 st n rest hv c hc hs ih => exact ih (fun w hm => hw w (List.mem_cons_of_mem _ hm)) ho
  case case8 s0 n rest hv c hc hs s1 _ hk ih =>
    obtain ⟨m1, m2, -, -⟩ := Emit.mark_spec s0 n
    refine ih (usesB fun w hm => ?_) (marked m1 m2 ho)
    rcases List.mem_cons.mp hm with rfl | hm
    · trivial
    · exact hw w (List.mem_cons_of_mem _ hm)
  case case9 s0 n rest hv c hc hs s1 _ _ _ hk ih =>
    obtain ⟨m1, m2, -, -⟩ := Emit.mark_spec s0 n
    refine ih (usesB fun w hm => ?_) (marked m1 m2 ho)
    rcases List.mem_cons.mp hm with rfl | hm
    · trivial
    · exact hw w (List.mem_cons_of_mem _ hm)
  case case10 s0 n rest hv c hc hs s1 _ _ hk ih =>
    obtain ⟨m1, m2, -, -⟩ := Emit.mark_spec s0 n
    refine ih (usesB fun w hm => ?_) (marked m1 m2 ho)
    rcases List.mem_cons.mp hm with rfl | hm
    · trivial
    · exact hw w (List.mem_cons_of_mem _ hm)
  case case11 s0 n rest hv c hc hs s1 _ _ hk ih =>
    obtain ⟨m1, m2, -, -⟩ := Emit.mark_spec s0 n
    refine ih (usesB fun w hm => ?_) (marked m1 m2 ho)
    rcases List.mem_cons.mp hm with rfl | hm
    · trivial
    · exact hw w (List.mem_cons_of_mem _ hm)
  case case12 s0 n rest hv c hc hs s1 _ hk qs s2 ih =>
    obtain ⟨m1, m2, -, -⟩ := Emit.mark_spec s0 n
    obtain ⟨q1, q2, -⟩ := Emit.marks_spec qs s1
    refine ih (fun w hm => ?_) (marked (m1.trans q1) (q2.trans m2) ho)
    rcases List.mem_cons.mp hm with rfl | hm
    · trivial
    rcases List.mem_cons.mp hm with rfl | hm
    · trivial
    · exact hw w (List.mem_cons_of_mem _ hm)
  case case13 s0 n rest hv c hc hs s1 _ _ _ _ _ hk ih =>
    obtain ⟨m1, m2, -, -⟩ := Emit.mark_spec s0 n
    refine ih (fun w hm => ?_) (marked m1 m2 ho)
    rcases List.mem_cons.mp hm with rfl | hm
    · trivial
    · exact hw w (List.mem_cons_of_mem _ hm)
  case case14 s0 n rest hv c hc hs s1 all _ _ _ _ _ _ _ hk ih =>
    obtain ⟨m1, m2, -, -⟩ := Emit.mark_spec s0 n
    refine ih (fun w hm => ?_) (marked m1 m2 ho)
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨_, -, rfl⟩ := List.mem_map.mp hm
      trivial
    · exact hw w (List.mem_cons_of_mem _ hm)
  case case15 s0 n rest hv c hc hs s1 np ni all cs nn ir iu irf hk tys cts recs s2 ih =>
    obtain ⟨m1, m2, -, -⟩ := Emit.mark_spec s0 n
    obtain ⟨q1, q2, -⟩ := Emit.marks_spec (tys ++ cts ++ recs) s1
    refine ih (usesB fun w hm => ?_) (marked (m1.trans q1) (q2.trans m2) ho)
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨n, c, np, ni, all, cs, nn, ir, iu, irf, hc, hk, rfl, rfl, rfl⟩
    · exact hw w (List.mem_cons_of_mem _ hm)

/-! ## A merge's recursors, in its order -/

/-- A recursor whose block lists `x`. -/
@[expose] def recUnder (x : Name) (c : CEntry) : Bool :=
  match c.kind with
  | .recur all .. => all.contains x
  | _ => false

theorem recMapAdd_list (n i k : Name) (m : Std.HashMap Name (Array Name)) :
    (((recMapAdd n m i)[k]?).getD #[]).toList = ((m[k]?).getD #[]).toList ++
      (if i == k && !((m[k]?).getD #[]).contains n then [n] else []) := by
  unfold recMapAdd
  rw [Std.HashMap.getElem?_alter]
  by_cases hik : i = k
  · subst hik
    simp only [beq_self_eq_true, ↓reduceIte, Bool.true_and]
    cases hm : m[i]? with
    | none => simp
    | some a =>
      simp only [Option.getD_some]
      split <;> simp_all
  · have : (i == k) = false := by simpa using hik
    simp [this]

theorem recMapAdds_list (n k : Name) (all : List Name) : ∀ m : Std.HashMap Name (Array Name),
    (((all.foldl (recMapAdd n) m)[k]?).getD #[]).toList = ((m[k]?).getD #[]).toList ++
      (if all.contains k && !((m[k]?).getD #[]).contains n then [n] else []) := by
  induction all with
  | nil => intro m; simp
  | cons i all ih =>
    intro m
    simp only [List.foldl_cons, ih, recMapAdd_list]
    by_cases hik : i = k
    · subst hik
      have hc : (((recMapAdd n m i)[i]?).getD #[]).contains n = true := by
        rw [Array.contains_iff_mem]
        exact (recMapAdd_mem n i i n m).2 (.inr ⟨rfl, rfl⟩)
      rw [hc]
      simp
    · have h1 : (i == k) = false := by simpa using hik
      have h2 : ((recMapAdd n m i)[k]?).getD #[] = (m[k]?).getD #[] := by
        unfold recMapAdd; rw [Std.HashMap.getElem?_alter]; simp [h1]
      have : (k == i) = false := beq_eq_false_iff_ne.2 (fun h => hik h.symm)
      simp only [h1, h2, List.contains_cons, this, Bool.false_or, Bool.false_and, Bool.false_eq_true,
        ↓reduceIte, List.append_nil]

/-- **The recursors listed under `x`**: the merge's recursors whose block lists `x`, in the
merge's order. -/
theorem recMapOf_list (mg : Merged) (x : Name) :
    ∀ (l : List Name) (m : Std.HashMap Name (Array Name)), l.Nodup →
      (∀ k ∈ l, ¬ k ∈ ((m[x]?).getD #[]).toList) →
      (((l.foldl (recMapStep mg) m)[x]?).getD #[]).toList = ((m[x]?).getD #[]).toList ++
        l.filter (fun k => (mg.map[k]?).any (recUnder x))
  | [], m, _, _ => by simp
  | k :: l, m, hnd, hm => by
    simp only [List.foldl_cons, List.filter_cons]
    have hnd' := (List.nodup_cons.1 hnd)
    have step : (((recMapStep mg m k)[x]?).getD #[]).toList = ((m[x]?).getD #[]).toList ++
        (if (mg.map[k]?).any (recUnder x) then [k] else []) := by
      unfold recMapStep
      cases hc : mg.map[k]? with
      | none => simp
      | some c =>
        simp only [Option.map_some, Option.any_some]
        unfold recUnder
        rcases c with ⟨⟨cn, cl, ct, ck⟩, cu⟩
        cases ck with
        | recur all np ni nmo nmi rules kk iu =>
          simp only
          rw [recMapAdds_list]
          have hk : ¬ k ∈ (m[x]?).getD #[] := by
            have := hm k List.mem_cons_self
            simpa using this
          simp [hk]
        | _ => simp
    rw [recMapOf_list mg x l _ hnd'.2 (fun k' hk' h => by
      rw [step] at h
      rcases List.mem_append.1 h with h | h
      · exact hm k' (List.mem_cons_of_mem _ hk') h
      · split at h
        · simp at h; subst h; exact hnd'.1 hk'
        · simp at h), step]
    split <;> simp

/-- The constants of a list, each name's first. -/
@[expose] def firstsGo : List CEntry → List CEntry → List CEntry
  | acc, [] => acc
  | acc, c :: cs => firstsGo (if acc.any (·.name == c.name) then acc else acc ++ [c]) cs

theorem find?_isSome_any {F : List CEntry} {k : Name} :
    (F.find? (·.name == k)).isSome = F.any (·.name == k) := by
  induction F with
  | nil => rfl
  | cons c F ih => simp only [List.find?_cons, List.any_cons]; split <;> simp_all

/-- **`mergedOfList` is its list's first constants of each name**, in order. -/
theorem mergedOfList_firsts : ∀ (cs : List CEntry) (mg : Merged) (acc : List CEntry),
    mg.order.toList = acc.map (·.name) → (∀ k, mg.map[k]? = acc.find? (·.name == k)) →
    (cs.foldl (fun mg c =>
        if mg.map.contains c.name then mg
        else { map := mg.map.insert c.name c, order := mg.order.push c.name }) mg).order.toList =
      (firstsGo acc cs).map (·.name) ∧
    ∀ k, (cs.foldl (fun mg c =>
        if mg.map.contains c.name then mg
        else { map := mg.map.insert c.name c, order := mg.order.push c.name }) mg).map[k]? =
      (firstsGo acc cs).find? (·.name == k)
  | [], mg, acc, h1, h2 => ⟨h1, h2⟩
  | c :: cs, mg, acc, h1, h2 => by
    simp only [List.foldl_cons, firstsGo]
    have hc : mg.map.contains c.name = acc.any (·.name == c.name) := by
      rw [Std.HashMap.contains_eq_isSome_getElem?, h2, find?_isSome_any]
    rw [hc]
    split
    · exact mergedOfList_firsts cs mg acc h1 h2
    · rename_i hn
      apply mergedOfList_firsts
      · simp [h1]
      · intro k
        rw [Std.HashMap.getElem?_insert, List.find?_append]
        split
        · rename_i he
          have : acc.find? (·.name == k) = none := by
            rw [List.find?_eq_none]
            intro x hx hxk
            apply hn
            rw [List.any_eq_true]
            exact ⟨x, hx, by rw [eq_of_beq he]; exact hxk⟩
          simp [this, he]
        · rename_i he
          rw [h2]
          cases acc.find? (·.name == k) with
          | some _ => rfl
          | none => simp [he]

theorem firstsGo_nodup : ∀ (cs acc : List CEntry), (acc.map (·.name)).Nodup →
    ((firstsGo acc cs).map (·.name)).Nodup
  | [], acc, h => h
  | c :: cs, acc, h => by
    simp only [firstsGo]
    apply firstsGo_nodup
    split
    · exact h
    · rename_i hn
      rw [List.map_append, List.nodup_append]
      refine ⟨h, by simp, ?_⟩
      intro a ha b hb
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
      subst hb
      intro he
      subst he
      obtain ⟨x, hx, hxe⟩ := List.mem_map.1 ha
      exact hn (List.any_eq_true.2 ⟨x, hx, by simp [hxe]⟩)

/-- A list, distinct in its names: its first constants are itself. -/
theorem firstsGo_nodup_eq : ∀ (cs acc : List CEntry), ((acc ++ cs).map (·.name)).Nodup →
    firstsGo acc cs = acc ++ cs
  | [], acc, _ => by simp [firstsGo]
  | c :: cs, acc, h => by
    simp only [firstsGo]
    have hn : acc.any (·.name == c.name) = false := by
      rw [Bool.eq_false_iff]
      intro ha
      obtain ⟨x, hx, hxc⟩ := List.any_eq_true.1 ha
      rw [List.map_append, List.nodup_append] at h
      exact h.2.2 _ (List.mem_map_of_mem hx) _ (List.mem_map_of_mem (List.mem_cons_self (a := c)))
        (eq_of_beq hxc)
    simp only [hn, Bool.false_eq_true, ↓reduceIte]
    rw [firstsGo_nodup_eq cs (acc ++ [c]) (by simpa using h)]
    simp

/-- Where constants of one name are one constant, keeping some of them commutes with taking
each name's first. -/
theorem firstsGo_filter (p : CEntry → Bool) : ∀ (cs acc : List CEntry),
    (∀ a ∈ acc ++ cs, ∀ b ∈ acc ++ cs, a.name = b.name → a = b) →
    (firstsGo acc cs).filter p = firstsGo (acc.filter p) (cs.filter p)
  | [], acc, _ => by simp [firstsGo]
  | c :: cs, acc, h => by
    simp only [firstsGo, List.filter_cons]
    have h' : ∀ acc', (∀ x ∈ acc', x ∈ acc ++ [c]) →
        ∀ a ∈ acc' ++ cs, ∀ b ∈ acc' ++ cs, a.name = b.name → a = b := by
      intro acc' hacc a ha b hb hab
      have mem : ∀ x ∈ acc' ++ cs, x ∈ acc ++ c :: cs := by
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · rcases List.mem_append.1 (hacc x hx) with hx | hx
          · exact List.mem_append_left _ hx
          · simp at hx; subst hx; simp
        · simp [hx]
      exact h a (mem a ha) b (mem b hb) hab
    by_cases ha : acc.any (·.name == c.name) = true
    · simp only [ha, ↓reduceIte]
      rw [firstsGo_filter p cs acc (h' acc (fun x hx => List.mem_append_left _ hx))]
      split
      · rename_i hp
        obtain ⟨x, hx, hxc⟩ := List.any_eq_true.1 ha
        have : x = c := h x (List.mem_append_left _ hx) c (by simp) (eq_of_beq hxc)
        subst this
        have : (acc.filter p).any (·.name == x.name) = true :=
          List.any_eq_true.2 ⟨x, List.mem_filter.2 ⟨hx, hp⟩, by simp⟩
        simp only [firstsGo, this, ↓reduceIte]
      · rfl
    · simp only [ha, Bool.false_eq_true, ↓reduceIte]
      rw [firstsGo_filter p cs (acc ++ [c]) (h' (acc ++ [c]) (fun x hx => hx))]
      have hf : (acc.filter p).any (·.name == c.name) = false := by
        rw [Bool.eq_false_iff]
        intro hx
        obtain ⟨x, hx, hxc⟩ := List.any_eq_true.1 hx
        exact ha (List.any_eq_true.2 ⟨x, (List.mem_filter.1 hx).1, hxc⟩)
      split
      · rename_i hp
        simp only [firstsGo, hf, Bool.false_eq_true, ↓reduceIte, List.filter_append, List.filter_cons,
          hp, List.filter_nil]
      · rename_i hp
        simp [List.filter_append, hp]

theorem find?_self {F : List CEntry} (hF : (F.map (·.name)).Nodup) {c : CEntry} (hc : c ∈ F) :
    F.find? (·.name == c.name) = some c := by
  induction F with
  | nil => cases hc
  | cons d F ih =>
    simp only [List.map_cons, List.nodup_cons] at hF
    rcases List.mem_cons.1 hc with rfl | hc
    · simp
    · have : (d.name == c.name) = false := by
        rw [beq_eq_false_iff_ne]
        intro he
        exact hF.1 (he ▸ List.mem_map_of_mem hc)
      simp [this, ih hF.2 hc]

theorem filter_find? (P : CEntry → Bool) : ∀ (F : List CEntry), (F.map (·.name)).Nodup →
    ((F.map (·.name)).filter (fun k => (F.find? (·.name == k)).any P)).filterMap
      (fun k => F.find? (·.name == k)) = F.filter P := by
  intro F hF
  have key : ∀ (G : List CEntry), (∀ c ∈ G, c ∈ F) →
      ((G.map (·.name)).filter (fun k => (F.find? (·.name == k)).any P)).filterMap
        (fun k => F.find? (·.name == k)) = G.filter P := by
    intro G hG
    induction G with
    | nil => rfl
    | cons c G ih =>
      have hc := find?_self hF (hG c List.mem_cons_self)
      simp only [List.map_cons, List.filter_cons, hc, Option.any_some]
      split
      · rename_i hp
        simp only [List.filterMap_cons, hc, ih (fun x hx => hG x (List.mem_cons_of_mem _ hx))]
      · rename_i hp
        simp only [ih (fun x hx => hG x (List.mem_cons_of_mem _ hx))]
  exact key F (fun _ h => h)

/-- **A merged list's block recursors**: its first constants of each name that are recursors of
a block listing `x`, in order. -/
theorem blockRecs_mergedOfList (L : List CEntry) (x : Name) :
    blockRecs (mergedOfList L) (recMapOf (mergedOfList L)) x = (firstsGo [] L).filter (recUnder x) := by
  obtain ⟨ho, hm⟩ := mergedOfList_firsts L {} [] (by simp) (by simp)
  have hnd := firstsGo_nodup L [] (by simp)
  have ho' : (mergedOfList L).order.toList = (firstsGo [] L).map (·.name) := ho
  have hm' : ∀ k, (mergedOfList L).map[k]? = (firstsGo [] L).find? (·.name == k) := hm
  unfold blockRecs recMapOf
  rw [← Array.foldl_toList, recMapOf_list _ x _ {} (ho' ▸ hnd) (by simp)]
  simp only [Std.HashMap.getElem?_empty, Option.getD_none, List.nil_append, ho', hm']
  exact filter_find? _ _ hnd

/-- A merge's block recursors under `x`, by its order. -/
theorem blockRecs_order (mg : Merged) (hnd : mg.order.toList.Nodup) (x : Name) :
    blockRecs mg (recMapOf mg) x =
      (mg.order.toList.filter (fun k => (mg.map[k]?).any (recUnder x))).filterMap (mg.map[·]?) := by
  unfold blockRecs recMapOf
  rw [← Array.foldl_toList, recMapOf_list _ x _ {} hnd (by simp)]
  simp

/-- Under two members of one block, a merge whose blocks agree lists the same recursors. -/
theorem blockRecs_member {mg : Merged} (hG : BlocksGood mg) (hnd : mg.order.toList.Nodup)
    {n n0 : Name} {c c0 : CEntry} {all cs cs0 : List Name} (hc : mg.map[n]? = some c)
    (hi : IsInd c all cs) (hc0 : mg.map[n0]? = some c0) (hi0 : IsInd c0 all cs0) :
    blockRecs mg (recMapOf mg) n0 = blockRecs mg (recMapOf mg) n := by
  rw [blockRecs_order mg hnd, blockRecs_order mg hnd]
  congr 1
  apply List.filter_congr
  intro k _
  cases hk : mg.map[k]? with
  | none => rfl
  | some e =>
    simp only [Option.any_some, recUnder]
    cases hek : e.kind with
    | recur all' np ni nmo nmi rules kk iu =>
      simp only
      obtain ⟨t, rest, m, csm, rfl, hm, him, -⟩ := hG.recur hk ⟨_, _, _, _, _, _, _, hek⟩
      have hall := (hG.ind hm him).2.1
      have side : ∀ {y : Name} {cy : CEntry} {csy : List Name}, mg.map[y]? = some cy → IsInd cy all csy →
          y ∈ t :: rest → t :: rest = all := by
        intro y cy csy hy hiy hmem
        obtain ⟨m', cs', hm', hi', -⟩ := hall y hmem
        rw [hy] at hm'; cases hm'
        exact (IsInd.unique hi' hiy).1
      have hn : n ∈ all := (hG.ind hc hi).1
      have hn0 : n0 ∈ all := (hG.ind hc0 hi0).1
      apply Bool.eq_iff_iff.2
      simp only [List.contains_iff_mem]
      constructor
      · intro h; rw [side hc0 hi0 h]; exact hn
      · intro h; rw [side hc hi h]; exact hn0
    | _ => rfl

theorem firstsGo_prefix : ∀ (L acc : List CEntry), ∃ rest, firstsGo acc L = acc ++ rest
  | [], acc => ⟨[], by simp [firstsGo]⟩
  | c :: L, acc => by
    simp only [firstsGo]
    split
    · exact firstsGo_prefix L acc
    · obtain ⟨rest, h⟩ := firstsGo_prefix L (acc ++ [c])
      exact ⟨c :: rest, by simp [h]⟩

/-- A merged list's first constant is held under its name. -/
theorem mergedOfList_head (c : CEntry) (L : List CEntry) :
    (mergedOfList (c :: L)).map[c.name]? = some c := by
  obtain ⟨-, hm⟩ := mergedOfList_firsts (c :: L) {} [] (by simp) (by simp)
  have : (mergedOfList (c :: L)).map[c.name]? = (firstsGo [] (c :: L)).find? (·.name == c.name) :=
    hm c.name
  rw [this]
  simp only [firstsGo, List.any_nil, Bool.false_eq_true, ↓reduceIte, List.nil_append]
  obtain ⟨rest, hr⟩ := firstsGo_prefix L [c]
  rw [hr]
  simp


/-! ## A group in its home's emission, and read alone -/

/-- **The home's emission holds the record of each of its groups**: an inductive type `n` of the
merge, not filtered out, has its block's record among the declarations, built from the block's
members, constructors and recursors as the merge holds them. -/
theorem home_group {mg : Merged} (hG : BlocksGood mg)
    (hN : ∀ (n : Name) (c : CEntry), mg.map[n]? = some c → c.name = n)
    (hO : ∀ n, n ∈ mg.order ↔ mg.map.contains n = true) (hnd : mg.order.toList.Nodup)
    {ds : Array Declaration} (hd : declsOf (emitAll mg mg.order) = .ok ds)
    {n : Name} {c : CEntry} {all cs : List Name} (hc : mg.map[n]? = some c) (hi : IsInd c all cs)
    (hsk : c.skipped = false) :
    ∃ p ∈ ds, ∃ ts cts rs,
      declOfF (emitAll mg mg.order).nm (emitAll mg mg.order).lv (emitAll mg mg.order).ex
        (.ind ts cts rs) = .ok (.inl p) ∧
      Forall₂ (IndTyOf (emitAll mg mg.order)) ts ((blockTys mg all).filter (·.kind.tag == 5)) ∧
      Forall₂ (IndCtorOf (emitAll mg mg.order)) cts
        ((blockCtors mg (blockTys mg all)).filter (·.kind.tag == 6)) ∧
      Forall₂ (IndRecOf (emitAll mg mg.order)) rs
        ((blockRecs mg (recMapOf mg) n).filter (·.kind.tag == 7)) := by
  have hmemo : n ∈ mg.order := (hO n).2 (by rw [Std.HashMap.contains_eq_isSome_getElem?, hc]; rfl)
  obtain ⟨hfrom, hvis⟩ := emitAll_spec hN mg.order
  obtain ⟨r, hr, hdec⟩ := emitAll_covers hG hN hO mg.order (hvis n hmemo c hc hsk) hc hsk
  have hinds : ∀ r ∈ (emitAll mg mg.order).out, IndOk mg (recMapOf mg) (emitAll mg mg.order) r :=
    emitLoop_inds mg (recMapOf mg) (mg.order.toList.map Work.visit) {} (fun w hw => by
      obtain ⟨_, -, rfl⟩ := List.mem_map.mp hw; trivial) (fun r hr => by simp at hr)
  obtain ⟨p, hp, hpd⟩ := (declsOf_spec hd).1 r hr
  have hcn : c.name = n := hN n c hc
  obtain ⟨np, ni, nn, ir, iu, irf, hk⟩ := hi
  have notOne : ∀ {c' : CEntry}, Stored mg c' → c'.name = n → c' = c := by
    intro c' hs hn'
    unfold Stored at hs
    rw [hn', hc] at hs
    exact (Option.some.inj hs).symm
  cases r with
  | ind ts cts rs =>
    obtain ⟨tys, ctors, recs, ⟨n0, c0, np0, ni0, all0, cs0, nn0, ir0, iu0, irf0, hc0, hk0, rfl, rfl, rfl⟩,
      h1, h2, h3⟩ := hinds _ hr
    -- `n` is a member of the block
    have hn0 : n ∈ all0 := by
      rcases hdec with ⟨t, ht, htn⟩ | ⟨t, ht, htn⟩ | ⟨t, ht, htn⟩
      · obtain ⟨x, hx, hxr⟩ := Forall₂.mem_left h1 t ht
        have hxn : x.name = n := by rw [← Option.some.inj (hxr.1.1.symm.trans htn)]
        obtain ⟨y, hy, hyx⟩ := List.mem_filterMap.1 (List.mem_filter.1 hx).1
        rw [← hN y x hyx, hxn] at hy
        exact hy
      · obtain ⟨x, hx, hxr⟩ := Forall₂.mem_left h2 t ht
        have hxn : x.name = n := by rw [← Option.some.inj (hxr.1.1.symm.trans htn)]
        obtain ⟨tt, -, hx'⟩ := List.mem_flatMap.1 (List.mem_filter.1 hx).1
        split at hx'
        · obtain ⟨y, -, hyx⟩ := List.mem_filterMap.1 hx'
          have := notOne (by unfold Stored; rw [hN y x hyx]; exact hyx) hxn
          subst this
          have h6 := (List.mem_filter.1 hx).2
          simp [hk, CKindF.tag] at h6
        · cases hx'
      · obtain ⟨x, hx, hxr⟩ := Forall₂.mem_left h3 t ht
        have hxn : x.name = n := by rw [← Option.some.inj (hxr.1.1.symm.trans htn)]
        obtain ⟨y, -, hyx⟩ := List.mem_filterMap.1 (List.mem_filter.1 hx).1
        have := notOne (by unfold Stored; rw [hN y x hyx]; exact hyx) hxn
        subst this
        have h7 := (List.mem_filter.1 hx).2
        simp [hk, CKindF.tag] at h7
    obtain ⟨m, cs', hm, him, -⟩ := (hG.ind hc0 ⟨_, _, _, _, _, _, hk0⟩).2.1 n hn0
    rw [hc] at hm; cases hm
    obtain ⟨rfl, -⟩ := IsInd.unique him ⟨_, _, _, _, _, _, hk⟩
    refine ⟨p, hpd, ts, cts, rs, hp, h1, h2, ?_⟩
    rwa [blockRecs_member hG hnd hc ⟨_, _, _, _, _, _, hk⟩ hc0 ⟨_, _, _, _, _, _, hk0⟩] at h3
  | _ =>
    obtain ⟨c', hs, hR⟩ := hfrom _ hr
    first
    | (obtain ⟨⟨hn1, -, -⟩, hk'⟩ := hR
       have := notOne hs (Option.some.inj (hn1.symm.trans hdec))
       subst this
       rw [hk] at hk'; cases hk'; done)
    | (obtain ⟨⟨hn1, -, -⟩, v, -, hk'⟩ := hR
       have := notOne hs (Option.some.inj (hn1.symm.trans hdec))
       subst this
       rw [hk] at hk'; cases hk'; done)
    | (obtain ⟨⟨hn1, -, -⟩, v, al, -, hk'⟩ := hR
       have := notOne hs (Option.some.inj (hn1.symm.trans hdec))
       subst this
       rw [hk] at hk'; cases hk'; done)

/-- **One group's record, on the fresh emitter's tables**: built from the group's members,
constructors and recursors as `groupParts` takes them. -/
theorem groupRecord_res {mg : Merged} {n : Name} {d : Declaration} (h : groupRecord mg n = .ok d) :
    ∃ tys ctors recs ts cts rs, groupParts mg n = some (tys, ctors, recs) ∧
      declOfF (groupEmit tys ctors recs).nm (groupEmit tys ctors recs).lv
        (groupEmit tys ctors recs).ex (.ind ts cts rs) = .ok (.inl d) ∧
      Forall₂ (IndTyOf (groupEmit tys ctors recs)) ts (tys.filter (·.kind.tag == 5)) ∧
      Forall₂ (IndCtorOf (groupEmit tys ctors recs)) cts (ctors.filter (·.kind.tag == 6)) ∧
      Forall₂ (IndRecOf (groupEmit tys ctors recs)) rs (recs.filter (·.kind.tag == 7)) := by
  unfold groupRecord at h
  split at h
  · cases h
  · rename_i tys ctors recs hp
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i ds hds
        have hd : d ∈ ds := by
          split at h
          · rename_i d' hd'
            split at h
            · cases h; exact Array.mem_of_getElem? hd'
            · cases h
          · cases h
        obtain ⟨r, hr', hdr⟩ := (declsOf_spec hds).2 d hd
        obtain ⟨ts, cts, rs, hout, -, h1, h2, h3⟩ := Emit.block_res {} tys ctors recs
        have hr0 : r = .ind ts cts rs := by
          have : r ∈ (({} : Emit).out.push (.ind ts cts rs)) := by
            simpa [groupEmit, hout] using hr'
          simpa using this
        subst hr0
        exact ⟨tys, ctors, recs, ts, cts, rs, hp, hdr, h1, h2, h3⟩

end ConLeche.Frontend.Olean
