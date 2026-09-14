module

public import ConLeche.Verify.Inductives.NestedWalk
public import ConLeche.Verify.Inductives.NestedLeaves
public import ConLeche.Verify.Inductives.NestedRestore

public section

/-!
# What the elimination's terms MENTION (task #308)

`NestedWalk.lean` carries the no-aux-mention invariant
(`MentionInv`/`elimNested_mentionInv`: every pin's components mention
only `ok` constants, given the containers' and the block's own do);
nothing instantiated it.  This module supplies the instance the model
lane needs — `ok n := "n resolves before the block, or n is one of the
block's OWN members"` — and the two bridges around it:

* **the containers are `ok`** (`containersMentionOnly_of_wf`): a
  container's member is a stored inductive and its constructors are
  stored constructors, whose types resolve in `env` (`EnvWF`);
* **the block's own annotated formers and constructors are `ok`**:
  `checkConstantVal` asks `constsResolve` of the ANNOTATED type, at
  `env` for a former and at `nestedFormerEnv fmsA env` for a
  constructor (`FormerFront.resolve`), and a lookup there is a lookup
  below or a former's name (`nestedFormerEnv_find?`);
* **blind vs annotated** (`Expr.mentionsConstE_of_mentionsConst`): a
  mention of a name that no `fvar` annotation of the term mentions is
  a mention the restore's node step can see.

The conclusion (`elimNested_pinsMentionOnly`) is what discharges the
model lane's `PinsMentionMember` and `ContainerCtorsNoAux`: a
component of a pin is never a COPY's name (copies are minted fresh,
and they are not the block's own members), so the occurrence test that
made the walk fire found a REAL member.
-/

namespace ConLeche

/-! ## `MentionsOnly`, weakened and read off `constsResolve` -/

theorem Expr.MentionsOnly.mono {ok ok' : Name → Prop} {e : Expr}
    (h : Expr.MentionsOnly ok e) (hm : ∀ n, ok n → ok' n) : Expr.MentionsOnly ok' e :=
  fun T hT => hm T (h T hT)

/-- A resolving term mentions only constants the environment carries. -/
theorem Expr.mentionsOnly_of_constsResolve {env : Env} {e : Expr}
    (h : e.constsResolve env = true) :
    Expr.MentionsOnly (fun n => (env.find? n).isSome = true) e :=
  fun _ hT => Expr.find?_isSome_of_mentionsConst e h hT

/-! ## The containers -/

/-- **The containers' names and stored constructors resolve before the
block** (`EnvWF`): `containerInfo?` reads stored constants only. -/
theorem containersMentionOnly_of_wf {env : Env} (hwf : EnvWF env) :
    ContainersMentionOnly env (fun n => (env.find? n).isSome = true) := by
  intro I ci hci J hJ
  obtain ⟨⟨cvC, caps, hfC, -, -⟩, hctors⟩ := containerInfo?_stored hci J hJ
  refine ⟨show (env.find? J.name).isSome = true by rw [hfC]; rfl, fun c hc => ?_⟩
  obtain ⟨cvc, nPc, nF, hfc, hty⟩ := hctors c hc
  rw [hty]
  exact Expr.mentionsOnly_of_constsResolve (hwf _ (List.mem_of_find?_eq_some hfc)).2.2.1

/-- `ContainersMentionOnly` weakens. -/
theorem ContainersMentionOnly.mono {env : Env} {ok ok' : Name → Prop}
    (h : ContainersMentionOnly env ok) (hm : ∀ n, ok n → ok' n) :
    ContainersMentionOnly env ok' := by
  intro I ci hci J hJ
  obtain ⟨hn, hc⟩ := h I ci hci J hJ
  exact ⟨hm _ hn, fun c hcm => (hc c hcm).mono hm⟩

/-! ## Blind vs annotated -/

/-- **A mention no annotation carries is a BLIND mention**: when every
`fvar` leaf's annotation is free of `T`, `mentionsConst` and
`mentionsConstE` agree at `T` (the direction the blind side lacks;
`Expr.mentionsConst_of_mentionsConstE` is the other one). -/
theorem Expr.mentionsConstE_of_mentionsConst {T : Name} :
    ∀ e : Expr, (∀ l ∈ e.fvarLeaves, Expr.mentionsConst T l.2 = false) →
      e.mentionsConst T = true → e.mentionsConstE T = true
  | .bvar _, _, h => nomatch h
  | .sort _, _, h => nomatch h
  | .lit _, _, h => nomatch h
  | .const _ _, _, h => h
  | .fvar idx ty, hl, h => by
    have := hl (idx, ty) (by simp [Expr.fvarLeaves])
    simp only [Expr.mentionsConst] at h
    rw [h] at this
    exact nomatch this
  | .app f a, hl, h => by
    simp only [Expr.mentionsConst, Bool.or_eq_true] at h
    simp only [Expr.mentionsConstE, Bool.or_eq_true]
    have hlf : ∀ l ∈ f.fvarLeaves, Expr.mentionsConst T l.2 = false :=
      fun l hlm => hl l (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inl hlm)
    have hla : ∀ l ∈ a.fvarLeaves, Expr.mentionsConst T l.2 = false :=
      fun l hlm => hl l (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inr hlm)
    exact h.elim (fun h => Or.inl (mentionsConstE_of_mentionsConst f hlf h))
      (fun h => Or.inr (mentionsConstE_of_mentionsConst a hla h))
  | .lam ty b _, hl, h => by
    simp only [Expr.mentionsConst, Bool.or_eq_true] at h
    simp only [Expr.mentionsConstE, Bool.or_eq_true]
    have hlf : ∀ l ∈ ty.fvarLeaves, Expr.mentionsConst T l.2 = false :=
      fun l hlm => hl l (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inl hlm)
    have hla : ∀ l ∈ b.fvarLeaves, Expr.mentionsConst T l.2 = false :=
      fun l hlm => hl l (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inr hlm)
    exact h.elim (fun h => Or.inl (mentionsConstE_of_mentionsConst ty hlf h))
      (fun h => Or.inr (mentionsConstE_of_mentionsConst b hla h))
  | .forallE ty b _, hl, h => by
    simp only [Expr.mentionsConst, Bool.or_eq_true] at h
    simp only [Expr.mentionsConstE, Bool.or_eq_true]
    have hlf : ∀ l ∈ ty.fvarLeaves, Expr.mentionsConst T l.2 = false :=
      fun l hlm => hl l (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inl hlm)
    have hla : ∀ l ∈ b.fvarLeaves, Expr.mentionsConst T l.2 = false :=
      fun l hlm => hl l (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inr hlm)
    exact h.elim (fun h => Or.inl (mentionsConstE_of_mentionsConst ty hlf h))
      (fun h => Or.inr (mentionsConstE_of_mentionsConst b hla h))
  | .letE ty v b, hl, h => by
    simp only [Expr.mentionsConst, Bool.or_eq_true] at h
    simp only [Expr.mentionsConstE, Bool.or_eq_true]
    have hlt : ∀ l ∈ ty.fvarLeaves, Expr.mentionsConst T l.2 = false := fun l hlm =>
      hl l (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inl (Or.inl hlm))
    have hlv : ∀ l ∈ v.fvarLeaves, Expr.mentionsConst T l.2 = false := fun l hlm =>
      hl l (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inl (Or.inr hlm))
    have hlb : ∀ l ∈ b.fvarLeaves, Expr.mentionsConst T l.2 = false := fun l hlm =>
      hl l (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inr hlm)
    rcases h with (h | h) | h
    · exact Or.inl (Or.inl (mentionsConstE_of_mentionsConst ty hlt h))
    · exact Or.inl (Or.inr (mentionsConstE_of_mentionsConst v hlv h))
    · exact Or.inr (mentionsConstE_of_mentionsConst b hlb h)
  | .proj s i x, hl, h => by
    simp only [Expr.mentionsConst, Bool.or_eq_true] at h
    simp only [Expr.mentionsConstE, Bool.or_eq_true]
    exact h.elim Or.inl (fun h => Or.inr (mentionsConstE_of_mentionsConst x
      (fun l hlm => hl l (by simpa [Expr.fvarLeaves] using hlm)) h))

/-! ## The block's own types, as the elimination takes them -/

/-- The block's own types as `elimNested` takes them (K.12: built from
the ANNOTATED formers and constructors): member `mIdx`'s annotated
former with its own annotated constructors. -/
theorem nestedTypes0_getElem? (p : NestedParts) (fmsA ctorsA : List ConstantVal) (t : Nat) :
    (nestedTypes0 p fmsA ctorsA)[t]? = (fmsA[t]?).map fun cvT =>
      (⟨cvT.name, cvT.type,
        (p.ctors.zip ctorsA).filterMap fun (c, cvCa) =>
          if c.member == t then some (cvCa.name, cvCa.type, c.nF) else none⟩ : AuxType) := by
  unfold nestedTypes0
  rw [List.getElem?_map, List.getElem?_zipIdx]
  cases fmsA[t]? with
  | none => rfl
  | some q => simp

/-- The block's own types are as many as its annotated formers. -/
theorem nestedTypes0_length (p : NestedParts) (fmsA ctorsA : List ConstantVal) :
    (nestedTypes0 p fmsA ctorsA).length = fmsA.length := by
  simp [nestedTypes0]

/-- … and they are named by them. -/
theorem nestedTypes0_names (p : NestedParts) (fmsA ctorsA : List ConstantVal) :
    (nestedTypes0 p fmsA ctorsA).map (·.name) = fmsA.map (·.name) := by
  refine List.ext_getElem? fun t => ?_
  rw [List.getElem?_map, List.getElem?_map, nestedTypes0_getElem?]
  cases fmsA[t]? with
  | none => rfl
  | some q => rfl

/-! ## The instance -/

variable {mode : CheckMode}

/-- **The pins' components mention only pre-block constants and the
block's own members** (task #308): `elimNested_mentionInv` at
`ok n := (env.find? n).isSome ∨ n ∈ the block's own member names`.
Every constant the elimination can put into a pin comes from a
container's stored constructor (which resolves in `env`) or from the
block's own annotated constructors (which resolve at the formers'
environment) — never from a COPY, which is minted fresh. -/
theorem elimNested_pinsMentionOnly {F : Nat} {env : Env} {p : NestedParts}
    {fmsA ctorsA : List ConstantVal} {st : ElimState} (hwf : EnvWF env)
    (hannF : nestedAnnotFormers (m := CheckM) (fueledOps mode F) env p.nP p.formers = .ok fmsA)
    (hannC : nestedAnnotCtors (m := CheckM) (fueledOps mode F) (nestedFormerEnv fmsA env)
      p.ctors = .ok ctorsA)
    (helim : elimNested env p.nP p.lps (nestedTypes0 p fmsA ctorsA) = .ok st) :
    (∀ t₀ ∈ (nestedTypes0 p fmsA ctorsA).head?, t₀.type.constsResolve env = true) ∧
    ∀ q ∈ st.pins, Expr.MentionsOnly
      (fun n => (env.find? n).isSome = true ∨ n ∈ fmsA.map (·.name)) q.pin := by
  -- the first annotated former's type resolves before the block
  have hhead : ∀ t₀ ∈ (nestedTypes0 p fmsA ctorsA).head?, t₀.type.constsResolve env = true := by
    intro t₀ ht₀
    rw [List.head?_eq_getElem?, nestedTypes0_getElem?] at ht₀
    obtain ⟨cvT, hcvT, rfl⟩ := Option.map_eq_some_iff.mp (Option.mem_def.mp ht₀)
    obtain ⟨cv, nIdx, -, hff⟩ := (nestedAnnotFormers_inv hannF).2 0 cvT hcvT
    exact hff.resolve
  refine ⟨hhead, ?_⟩
  -- the containers
  have hcm : ContainersMentionOnly env
      (fun n => (env.find? n).isSome = true ∨ n ∈ fmsA.map (·.name)) :=
    (containersMentionOnly_of_wf hwf).mono (fun _ h => Or.inl h)
  -- the block's own annotated constructors
  have hty : ∀ t ∈ nestedTypes0 p fmsA ctorsA, ∀ c ∈ t.ctors,
      Expr.MentionsOnly (fun n => (env.find? n).isSome = true ∨ n ∈ fmsA.map (·.name)) c.2.1 := by
    intro t ht c hc
    obtain ⟨i, hi⟩ := List.getElem?_of_mem ht
    rw [nestedTypes0_getElem?] at hi
    obtain ⟨cvT, -, rfl⟩ := Option.map_eq_some_iff.mp hi
    simp only at hc
    obtain ⟨⟨c₀, cvCa⟩, hmem, hf⟩ := List.mem_filterMap.mp hc
    simp only at hf
    split at hf
    · obtain rfl := Option.some.inj hf
      obtain ⟨j, hj⟩ := List.getElem?_of_mem (List.of_mem_zip hmem).2
      obtain ⟨c', -, hcheck⟩ := (nestedAnnotCtors_inv hannC).2 j cvCa hj
      refine (Expr.mentionsOnly_of_constsResolve
        (FormerFront.of_checkConstantVal (mode := mode) hcheck).resolve).mono fun n hn => ?_
      obtain ⟨cN, hcN⟩ := Option.isSome_iff_exists.mp hn
      exact nestedFormerEnv_find? hcN
    · exact nomatch hf
  -- the first former's type
  have ht₀ : ∀ t₀ ∈ (nestedTypes0 p fmsA ctorsA).head?,
      Expr.MentionsOnly (fun n => (env.find? n).isSome = true ∨ n ∈ fmsA.map (·.name)) t₀.type := by
    intro t₀ hmem
    exact (Expr.mentionsOnly_of_constsResolve (hhead t₀ hmem)).mono (fun _ hn => Or.inl hn)
  exact elimNested_mentionInv hcm helim hty ht₀

end ConLeche
