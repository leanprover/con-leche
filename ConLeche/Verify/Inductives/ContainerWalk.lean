module

public import ConLeche.Kernel.Inductives.NestedParts
public import ConLeche.Verify.Inductives.StructRec
import ConLeche.Verify.InferLemmas

public section

/-!
# The container's motive walk on the generated recursor types (task #279 M-B′ step 3a)

`containerInfo?` (`Kernel/Inductives/NestedParts.lean`) recovers a
container's `all` group from the MOTIVE BINDERS of its stored recursor:
`containerMembersGo` walks the binders below the parameters and takes
the maximal prefix whose domains are real members' motives
(`containerMotiveMember?`: `∀ ı⃗ (t : C p⃗ ı⃗), Sort ℓ` with `C` a stored
inductive applied to the parameter spine and its own index variables).

This file proves what that walk returns on the recursor types the two
native generators produce — `structRecTyR` (the fixpoint route) and
`mutualRecTy` (the mutual route): the block's member names in order,
in ANY environment that stores the members.  The walk stops at the
first minor premise, whose domain ends in an application of the
motive rather than a sort, so nothing past the members is read; that
is why the result does not depend on which OTHER constants the
environment holds — the fact the datum clause `RecReadAt`
(`Model/IndRep.lean`) records, quantified over the environment, and
the alignment `IndRep.containerInfo?_eq`
(`Model/Inductives/ContainerRead.lean`) consumes.

A block WITHOUT constructors is not covered (there is no minor to stop
at, and an index binder of the sort-valued shape can extend the walk);
`RecReadAt` is only ever live under `rules ≠ []`, so no clause claims
it there.
-/

namespace ConLeche

/-! ## `stripPis`, `replacePisPw` and `piBinders` -/

/-- A stripped telescope has exactly `n` binders. -/
theorem stripPis_length : ∀ (n : Nat) {e : Expr} {bs : List (Expr × BinderMeta)} {body : Expr},
    e.stripPis n = some (bs, body) → bs.length = n
  | 0, _, bs, _, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; rfl
  | n + 1, e, bs, body, h => by
    match e, h with
    | .forallE ty b m, h =>
      simp only [Expr.stripPis] at h
      cases hs : b.stripPis n with
      | none => rw [hs] at h; exact nomatch h
      | some q =>
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [List.length_cons]
        rw [stripPis_length n hs]

/-- `piBinders` past a stripped prefix: the prefix's binders, then the
body's leading binders, ending where the body's telescope ends. -/
theorem piBinders_of_stripPis : ∀ (n : Nat) {e : Expr} {bs : List (Expr × BinderMeta)} {body : Expr},
    e.stripPis n = some (bs, body) → e.piBinders = (bs ++ body.piBinders.1, body.piBinders.2)
  | 0, e, bs, body, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | n + 1, e, bs, body, h => by
    match e, h with
    | .forallE ty b m, h =>
      simp only [Expr.stripPis] at h
      cases hs : b.stripPis n with
      | none => rw [hs] at h; exact nomatch h
      | some q =>
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Expr.piBinders]
        rw [piBinders_of_stripPis n hs]
        rfl

/-- A successful `replacePisPw` strips as many binders. -/
theorem replacePisPw_some_stripPis {pw : PropWhen} :
    ∀ (n : Nat) {e b r : Expr}, Expr.replacePisPw pw n e b = some r →
      ∃ (bs : List (Expr × BinderMeta)) (body : Expr), e.stripPis n = some (bs, body)
  | 0, e, _, _, _ => ⟨[], e, rfl⟩
  | n + 1, e, b, r, h => by
    match e, h with
    | .forallE ty rest m, h =>
      simp only [Expr.replacePisPw, Option.map_eq_some_iff] at h
      obtain ⟨r', hr', rfl⟩ := h
      obtain ⟨bs, body, hs⟩ := replacePisPw_some_stripPis n hr'
      exact ⟨(ty, m) :: bs, body, by simp only [Expr.stripPis, hs, Option.map_some]⟩

/-- `piBinders` of a `replacePisPw` result: `n` binders, then the new
body's leading binders, ending where the new body's telescope ends. -/
theorem piBinders_replacePisPw {pw : PropWhen} {n : Nat} {e b r : Expr}
    (h : Expr.replacePisPw pw n e b = some r) :
    ∃ bs : List (Expr × BinderMeta), bs.length = n ∧
      r.piBinders = (bs ++ b.piBinders.1, b.piBinders.2) := by
  obtain ⟨bs, body, hs⟩ := replacePisPw_some_stripPis n h
  have hr := replacePisPw_stripPis n h hs
  refine ⟨_, ?_, piBinders_of_stripPis n hr⟩
  rw [List.length_map]
  exact stripPis_length n hs

/-! ## `containerMotiveMember?` on a motive and on a minor -/

/-- The result of the walk on a domain whose leading telescope does not
end in a sort: no member. -/
theorem containerMotiveMember?_of_not_sort {env : Env} {nP i : Nat} {dom : Expr}
    (h : ∀ u : Level, dom.piBinders.2 ≠ .sort u) :
    containerMotiveMember? env nP i dom = none := by
  unfold containerMotiveMember?
  rcases hp : dom.piBinders with ⟨bs, res⟩
  rw [hp] at h
  cases res with
  | sort u => exact absurd rfl (h u)
  | _ => rfl

/-- **A real member's motive is recognised** (in any environment
storing the member): the motive `∀ ı⃗ (t : T p⃗ ı⃗), Sort ℓ` as both
generators spell it — `replacePisPw .never nIdx itele` over the
family at the parameter spine `i` motives below the parameters
(`structFamI T lps nP nIdx i 0`; `structMotiveTyI` is the `i = 0`
case, `mutualMotiveTy` the general one). -/
theorem containerMotiveMember?_motive {env : Env} {nP nIdx i : Nat} {T : Name}
    {lps : List Name} {ℓ : Level} {itele mty : Expr}
    (h : Expr.replacePisPw .never nIdx itele
      (.forallE (structFamI T lps nP nIdx i 0) (.sort ℓ) ⟨.never⟩) = some mty)
    {cv : ConstantVal} {caps : IndCaps} (hT : env.find? T = some (.indInfo cv caps)) :
    containerMotiveMember? env nP i mty = some T := by
  obtain ⟨bs, hlen, hpi⟩ := piBinders_replacePisPw h
  have hpi' : mty.piBinders = (bs ++ [(structFamI T lps nP nIdx i 0, ⟨.never⟩)], .sort ℓ) := by
    rw [hpi]; rfl
  unfold containerMotiveMember?
  rw [hpi']
  simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, List.length_append,
    List.length_singleton, hlen, Nat.add_sub_cancel]
  unfold structFamI
  rw [Expr.getAppFn_mkAppN, Expr.getAppArgs_mkAppN]
  simp only [Expr.getAppFn, Expr.getAppArgs, List.nil_append, List.length_append]
  have hall1 : (List.range nP).all (fun j =>
      (structPsAt (0 + i + nIdx) nP ++ structPsAt 0 nIdx)[j]?
        == some (Expr.bvar (nIdx + i + nP - 1 - j))) = true := by
    rw [List.all_eq_true]
    intro j hj
    rw [List.mem_range] at hj
    rw [List.getElem?_append_left (by simp [structPsAt, hj]), beq_iff_eq]
    simp only [structPsAt, List.getElem?_map, List.getElem?_range hj, Option.map_some,
      Option.some.injEq, Expr.bvar.injEq]
    omega
  have hall2 : (List.range nIdx).all (fun l =>
      (structPsAt (0 + i + nIdx) nP ++ structPsAt 0 nIdx)[nP + l]?
        == some (Expr.bvar (nIdx - 1 - l))) = true := by
    rw [List.all_eq_true]
    intro l hl
    rw [List.mem_range] at hl
    rw [List.getElem?_append_right (by simp [structPsAt]), beq_iff_eq]
    simp only [structPsAt, List.length_map, List.length_range, Nat.add_sub_cancel_left,
      List.getElem?_map, List.getElem?_range hl, Option.map_some, Option.some.injEq,
      Expr.bvar.injEq]
    omega
  rw [hall1, hall2, hT]
  simp [structPsAt]

/-! ## The walk -/

/-- The walk stops at a binder: the domain at position `j` is no
member's motive (or there is no binder). -/
def WalkStopsAt (env : Env) (nP j : Nat) (rest : Expr) : Prop :=
  ∀ dom body m, rest = .forallE dom body m → containerMotiveMember? env nP j dom = none

/-- The walk on a body that is not a `∀`, or whose first binder stops
it, is empty. -/
theorem containerMembersGo_stop {env : Env} {nP j fuel : Nat} {rest : Expr}
    (hs : WalkStopsAt env nP j rest) : containerMembersGo env nP fuel j rest = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases rest with
    | forallE dom body m =>
      simp only [containerMembersGo]
      rw [hs dom body m rfl]
    | _ => rfl

/-- **The walk over the mutual generator's motives** returns the
formers' names, in order, in any environment storing them — provided
the walk stops right after them. -/
theorem containerMembersGo_mutualMotivesPis {env : Env} {lps : List Name} {nP : Nat} {ℓ : Level}
    {pw : PropWhen} :
    ∀ (formers : List MutualFormer) (i fuel : Nat) {rest r : Expr},
      mutualMotivesPis lps nP ℓ pw formers i rest = some r →
      formers.length < fuel →
      (∀ f ∈ formers, ∃ (cv : ConstantVal) (caps : IndCaps),
        env.find? f.name = some (.indInfo cv caps)) →
      WalkStopsAt env nP (i + formers.length) rest →
      containerMembersGo env nP fuel i r = formers.map (·.name)
  | [], i, fuel, rest, r, h, _, _, hs => by
    simp only [mutualMotivesPis, Option.some.injEq] at h
    subst h
    simp only [List.length_nil, Nat.add_zero] at hs
    exact containerMembersGo_stop hs
  | f :: fs, i, fuel, rest, r, h, hfuel, hst, hs => by
    simp only [mutualMotivesPis, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨mty, hmty, r', hr', rfl⟩ := h
    cases fuel with
    | zero => exact absurd hfuel (Nat.not_lt_zero _)
    | succ fuel =>
      obtain ⟨cv, caps, hf⟩ := hst f List.mem_cons_self
      -- the motive is recognised
      have hrec : containerMotiveMember? env nP i mty = some f.name := by
        unfold mutualMotiveTy at hmty
        simp only [Option.bind_eq_some_iff] at hmty
        obtain ⟨q, -, hq⟩ := hmty
        exact containerMotiveMember?_motive hq hf
      simp only [containerMembersGo, hrec, List.map_cons]
      congr 1
      refine containerMembersGo_mutualMotivesPis fs (i + 1) fuel hr'
        (by simp only [List.length_cons] at hfuel; omega)
        (fun g hg => hst g (List.mem_cons_of_mem _ hg)) ?_
      rw [show i + 1 + fs.length = i + (f :: fs).length from by simp only [List.length_cons]; omega]
      exact hs

/-- A mutual minor premise ends in an application of the motive: the
walk stops at it. -/
theorem mutualMinorTy_stops {env : Env} {lps : List Name} {nP o j : Nat} {pw : PropWhen}
    {c : MutualCtor4} {mty : Expr} (h : mutualMinorTy lps nP o pw c = some mty) :
    containerMotiveMember? env nP j mty = none := by
  unfold mutualMinorTy at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨q, -, r, -, hr⟩ := h
  obtain ⟨bs, -, hpi⟩ := piBinders_replacePisPw hr
  refine containerMotiveMember?_of_not_sort fun u => ?_
  rw [hpi]
  simp only
  rw [piBinders_mutualIhPis, Expr.mkAppN_append_one]
  simp [Expr.liftLooseBVars, Expr.piBinders]
where
  piBinders_mutualIhPis {nF o : Nat} {pw : PropWhen}
      {teleOf : Nat → List (Expr × BinderMeta)} {idxOf : Nat → List Expr} :
      ∀ (is : List (Nat × Nat)) (l : Nat) (body : Expr),
        (mutualIhPis nF o pw teleOf idxOf is l body).piBinders.2 = body.piBinders.2
    | [], _, _ => rfl
    | (i, m') :: is, l, body => by
      simp only [mutualIhPis, Expr.piBinders]
      exact piBinders_mutualIhPis is (l + 1) body

/-- A fixpoint-route minor premise ends in an application of the
motive: the walk stops at it. -/
theorem structMinorTyR_stops {env : Env} {C : Name} {lps : List Name} {nP nF o j : Nat}
    {pw : PropWhen} {cty : Expr} {recIdx : List Nat} {mty : Expr}
    (h : structMinorTyR C lps nP nF o pw cty recIdx = some mty) :
    containerMotiveMember? env nP j mty = none := by
  unfold structMinorTyR at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨q, -, r, -, hr⟩ := h
  obtain ⟨bs, -, hpi⟩ := piBinders_replacePisPw hr
  refine containerMotiveMember?_of_not_sort fun u => ?_
  rw [hpi]
  simp only
  rw [piBinders_structIhPis, Expr.mkAppN_append_one]
  simp [Expr.liftLooseBVars, Expr.piBinders]
where
  piBinders_structIhPis {nF o : Nat} {pw : PropWhen}
      {teleOf : Nat → List (Expr × BinderMeta)} {idxOf : Nat → List Expr} :
      ∀ (is : List Nat) (l : Nat) (body : Expr),
        (structIhPis nF o pw teleOf idxOf is l body).piBinders.2 = body.piBinders.2
    | [], _, _ => rfl
    | i :: is, l, body => by
      simp only [structIhPis, Expr.piBinders]
      exact piBinders_structIhPis is (l + 1) body

/-! ## The two generators -/

/-- **`mutualRecTy`'s motive walk**: at a block with a constructor, the
stored recursor type strips its parameters to a body whose walk, in
any environment storing the formers and with fuel past the motives,
is the formers' names in order. -/
theorem mutualRecTy_containerMembers {lps : List Name} {elim : Name} {large : Bool} {nP : Nat}
    {formers : List MutualFormer} {ctors : List MutualCtor4} {m : Nat} {recTy : Expr}
    (h : mutualRecTy lps elim large nP formers ctors m = some recTy) (hne : ctors ≠ []) :
    ∃ (bs : List (Expr × BinderMeta)) (body : Expr), recTy.stripPis nP = some (bs, body) ∧
      ∀ (env : Env) (fuel : Nat), formers.length < fuel →
        (∀ f ∈ formers, ∃ (cv : ConstantVal) (caps : IndCaps),
          env.find? f.name = some (.indInfo cv caps)) →
        containerMembersGo env nP fuel 0 body = formers.map (·.name) := by
  unfold mutualRecTy at h
  simp only at h
  split at h
  · rename_i f f₀ hf hf₀
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨q, -, major, -, minors, hminors, motives, hmotives, hrec⟩ := h
    obtain ⟨bs₀, body₀, hs₀⟩ := replacePisPw_some_stripPis nP hrec
    refine ⟨_, motives, replacePisPw_stripPis nP hrec hs₀, fun env fuel hfuel hst => ?_⟩
    refine containerMembersGo_mutualMotivesPis formers 0 fuel hmotives hfuel hst ?_
    -- the walk stops at the first minor
    intro dom body mm hminors'
    match ctors, hne, hminors with
    | c :: cs, _, hminors =>
      simp only [mutualMinorsPis, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hminors
      obtain ⟨mty, hmty, rest, -, rfl⟩ := hminors
      obtain ⟨rfl, -, -⟩ := Expr.forallE.inj hminors'
      exact mutualMinorTy_stops hmty
  · exact nomatch h

/-- **`structRecTyR`'s motive walk**: at a block with a constructor, the
stored recursor type strips its parameters to a body whose walk, in
any environment storing the former and with fuel past the one motive,
is `[T]`. -/
theorem structRecTyR_containerMembers {T : Name} {lps : List Name} {elim : Name} {large : Bool}
    {nP nIdx : Nat} {tty : Expr} {ctors : List (Name × Nat × Expr × List Nat)} {recTy : Expr}
    (h : structRecTyR T lps elim large nP nIdx tty ctors = some recTy) (hne : ctors ≠ []) :
    ∃ (bs : List (Expr × BinderMeta)) (body : Expr), recTy.stripPis nP = some (bs, body) ∧
      ∀ (env : Env) (fuel : Nat), 1 < fuel →
        (∃ (cv : ConstantVal) (caps : IndCaps), env.find? T = some (.indInfo cv caps)) →
        containerMembersGo env nP fuel 0 body = [T] := by
  unfold structRecTyR at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨q, -, motiveTy, hmot, major, -, minors, hminors, hrec⟩ := h
  obtain ⟨bs₀, body₀, hs₀⟩ := replacePisPw_some_stripPis nP hrec
  refine ⟨_, _, replacePisPw_stripPis nP hrec hs₀, fun env fuel hfuel hst => ?_⟩
  obtain ⟨cv, caps, hT⟩ := hst
  have hrec' : containerMotiveMember? env nP 0 motiveTy = some T :=
    containerMotiveMember?_motive hmot hT
  match fuel, hfuel with
  | fuel + 2, _ =>
    simp only [containerMembersGo, hrec']
    congr 1
    refine containerMembersGo_stop fun dom body mm hminors' => ?_
    match ctors, hne, hminors with
    | (C, nF, cty, recIdx) :: cs, _, hminors =>
      simp only [structMinorsPisR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hminors
      obtain ⟨mty, hmty, rest, -, rfl⟩ := hminors
      obtain ⟨rfl, -, -⟩ := Expr.forallE.inj hminors'
      exact structMinorTyR_stops hmty

end ConLeche
