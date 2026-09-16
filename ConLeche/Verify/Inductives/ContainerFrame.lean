module

public import ConLeche.Kernel.Inductives.NestedParts
import ConLeche.Verify.EnvWF
public import ConLeche.Verify.EnvPreds
import ConLeche.Verify.Inductives.NestedCopyGlue

public section

/-!
# The container's block under an environment extension (task #315)

`containerInfo?` (`ConLeche/Kernel/Inductives/NestedParts.lean`) reads
the stored block of an inductive `I` off the environment.  The nested
route installs constants while it runs, so the model tier needs to know
when that reading is STABLE: an old container's block must be the same
block at the extended environment.

The environment enters `containerInfo?` only through `find?` results of
the three *inductive* kinds — `indInfo` (the formers), `recInfo` (the
recursors) and `ctorInfo` (the constructors of the recursors' rules) —
and only at the names `I`, `I.rec`, the rules' constructors, the member
names the motive walk reads off `I.rec`'s type, and those members' own
`.rec` and rule constructors.  Two frames follow.

* **A non-inductive extension changes nothing**
  (`containerInfo?_ext_nonInd`, `containerInfo?_cons_nonInd`): every new
  constant is of another kind, so no lookup the reading makes can see
  it.
* **An inductive extension changes nothing OFF the new names**
  (`containerInfo?_ext_ind`): the new constants are the names `N`, fresh
  at the old environment; a container `I ∉ N` reads the same block,
  because every name its reading touches is itself off `N` — the
  recursors by the `.rec` naming discipline, the rules' constructors
  because the old environment stores them (`RecCtorsStored`), and the
  members because the old recursor's type resolves there (`EnvWF`).

Both come from one congruence lemma (`containerInfo?_congr`): the two
environments need only agree at the names off `N`, and the closure
facts are exactly the four hypotheses above.
-/

namespace ConLeche

/-! ## (A) The agreement the reading needs -/

/-- **What two environments must share at a name** for
`containerInfo?` to read it the same way: the three inductive kinds.
Every other constant is invisible to the reading — it matches on those
three and treats anything else as absent. -/
private def KindAgree (env₁ env₂ : Env) (n : Name) : Prop :=
  (∀ cv caps, env₂.find? n = some (.indInfo cv caps) ↔ env₁.find? n = some (.indInfo cv caps)) ∧
  (∀ cv mI rP rules, env₂.find? n = some (.recInfo cv mI rP rules) ↔
    env₁.find? n = some (.recInfo cv mI rP rules)) ∧
  (∀ cv nP nF, env₂.find? n = some (.ctorInfo cv nP nF) ↔
    env₁.find? n = some (.ctorInfo cv nP nF))

/-! ## (B) The syntactic lemmas the motive walk rests on -/

/-- A spine's head constant is mentioned by the spine. -/
private theorem mentionsConst_of_getAppFn {C : Name} {us : List Level} :
    ∀ (e : Expr), e.getAppFn = .const C us → e.mentionsConst C = true := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro h
    simp only [Expr.getAppFn] at h
    simp [Expr.mentionsConst, ihf h]
  | const n us' =>
    intro h
    simp only [Expr.getAppFn, Expr.const.injEq] at h
    simp [Expr.mentionsConst, h.1]
  | _ => intro h; simp [Expr.getAppFn] at h

/-- A `∀`-binder's domain is mentioned by the telescope. -/
private theorem mentionsConst_piBinders {C : Name} :
    ∀ (e : Expr) (b : Expr) (m : BinderMeta), (b, m) ∈ e.piBinders.1 →
      b.mentionsConst C = true → e.mentionsConst C = true := by
  intro e
  induction e with
  | forallE ty body mb ihty ihb =>
    intro b m hmem hb
    simp only [Expr.piBinders, List.mem_cons, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | hmem
    · simp [Expr.mentionsConst, hb]
    · simp [Expr.mentionsConst, ihb b m hmem hb]
  | _ => intro b m hmem _; simp [Expr.piBinders] at hmem

/-- A stripped telescope's body is mentioned by the whole. -/
private theorem mentionsConst_stripPis {C : Name} :
    ∀ (n : Nat) {e : Expr} {bs : List (Expr × BinderMeta)} {body : Expr},
      e.stripPis n = some (bs, body) → body.mentionsConst C = true →
      e.mentionsConst C = true := by
  intro n
  induction n with
  | zero =>
    intro e bs body h hb
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    exact h.2 ▸ hb
  | succ n ih =>
    intro e bs body h hb
    match e with
    | .forallE ty b m =>
      simp only [Expr.stripPis] at h
      cases hs : b.stripPis n with
      | none => rw [hs] at h; exact nomatch h
      | some r =>
        obtain ⟨bs₀, body₀⟩ := r
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        simp [Expr.mentionsConst, ih hs hb]

/-- A motive binder's member is mentioned by the binder's domain: it is
the head of the major premise, which is one of the domain's own
`∀`-binders. -/
private theorem mentionsConst_of_containerMotiveMember? {env : Env} {nP i : Nat} {dom : Expr}
    {C : Name} (h : containerMotiveMember? env nP i dom = some C) :
    dom.mentionsConst C = true := by
  unfold containerMotiveMember? at h
  cases hpb : dom.piBinders with
  | mk bs res =>
    rw [hpb] at h
    dsimp only at h
    cases res with
    | sort u =>
      cases hgl : bs.getLast? with
      | none => rw [hgl] at h; exact nomatch h
      | some p =>
        obtain ⟨major, mm⟩ := p
        rw [hgl] at h
        dsimp only at h
        cases hfn : major.getAppFn with
        | const C' us =>
          rw [hfn] at h
          dsimp only at h
          have hC' : C' = C := by
            split at h <;> (try split at h) <;>
              first
                | exact Option.some.inj h
                | exact nomatch h
          subst hC'
          refine mentionsConst_piBinders dom major mm ?_ (mentionsConst_of_getAppFn major hfn)
          rw [hpb]
          exact List.mem_of_getLast? hgl
        | _ => rw [hfn] at h; exact nomatch h
    | _ => exact nomatch h

/-! ## (C) The motive walk is a congruence -/

/-- One motive binder is read the same at two environments that agree
at the constants its domain mentions. -/
private theorem containerMotiveMember?_congr {env₁ env₂ : Env} {nP i : Nat} (dom : Expr)
    (hag : ∀ C : Name, dom.mentionsConst C = true → KindAgree env₁ env₂ C) :
    containerMotiveMember? env₂ nP i dom = containerMotiveMember? env₁ nP i dom := by
  unfold containerMotiveMember?
  cases hpb : dom.piBinders with
  | mk bs res =>
    dsimp only
    cases res with
    | sort u =>
      dsimp only
      cases hgl : bs.getLast? with
      | none => dsimp only
      | some p =>
        obtain ⟨major, mm⟩ := p
        dsimp only
        cases hfn : major.getAppFn with
        | const C us =>
          dsimp only
          have hk : KindAgree env₁ env₂ C :=
            hag C (mentionsConst_piBinders dom major mm
              (by rw [hpb]; exact List.mem_of_getLast? hgl)
              (mentionsConst_of_getAppFn major hfn))
          cases h2 : env₂.find? C with
          | none =>
            cases h1 : env₁.find? C with
            | none => rfl
            | some c1 =>
              cases c1 <;>
                first
                  | rfl
                  | exact absurd ((hk.1 _ _).mpr h1) (by simp [h2])
          | some c2 =>
            cases c2 with
            | indInfo cv caps => rw [(hk.1 cv caps).mp h2]
            | _ =>
              cases h1 : env₁.find? C with
              | none => rfl
              | some c1 =>
                cases c1 <;>
                  first
                    | rfl
                    | exact absurd ((hk.1 _ _).mpr h1) (by simp [h2])
        | _ => dsimp only
    | _ => rfl

/-- The whole motive walk is a congruence. -/
private theorem containerMembersGo_congr {env₁ env₂ : Env} {nP : Nat} :
    ∀ (fuel i : Nat) (e : Expr),
      (∀ C : Name, e.mentionsConst C = true → KindAgree env₁ env₂ C) →
      containerMembersGo env₂ nP fuel i e = containerMembersGo env₁ nP fuel i e := by
  intro fuel
  induction fuel with
  | zero => intro i e _; rfl
  | succ fuel ih =>
    intro i e hag
    match e with
    | .forallE dom body m =>
      simp only [containerMembersGo]
      rw [containerMotiveMember?_congr dom
        (fun C hC => hag C (by simp [Expr.mentionsConst, hC]))]
      cases hm : containerMotiveMember? env₁ nP i dom with
      | none => rfl
      | some C =>
        simp only
        rw [ih (i + 1) body (fun C' hC' => hag C' (by simp [Expr.mentionsConst, hC']))]
    | .bvar .. | .sort .. | .lit .. | .const .. | .fvar .. | .app .. | .lam .. | .letE ..
    | .proj .. => rfl

/-- Every name the walk returns is mentioned by the expression it
walks. -/
private theorem mem_containerMembersGo_mentions {env : Env} {nP : Nat} {C : Name} :
    ∀ (fuel i : Nat) (e : Expr), C ∈ containerMembersGo env nP fuel i e →
      e.mentionsConst C = true := by
  intro fuel
  induction fuel with
  | zero => intro i e h; simp [containerMembersGo] at h
  | succ fuel ih =>
    intro i e h
    match e with
    | .forallE dom body m =>
      simp only [containerMembersGo] at h
      cases hm : containerMotiveMember? env nP i dom with
      | none => rw [hm] at h; simp at h
      | some C' =>
        rw [hm] at h
        simp only [List.mem_cons] at h
        rcases h with rfl | h
        · simp [Expr.mentionsConst, mentionsConst_of_containerMotiveMember? hm]
        · simp [Expr.mentionsConst, ih (i + 1) body h]
    | .bvar .. | .sort .. | .lit .. | .const .. | .fvar .. | .app .. | .lam .. | .letE ..
    | .proj .. => simp [containerMembersGo] at h

/-- A `mapM` in `Option` at two pointwise-equal functions. -/
private theorem mapM_option_congr {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.mapM f = l.mapM g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.mapM_cons, h a (by simp)]
    cases g a with
    | none => rfl
    | some b =>
      simp only [bind, Option.bind]
      rw [mapM_option_congr (l := l) (fun x hx => h x (by simp [hx]))]


/-- Two `Option` binds, at equal scrutinees and pointwise-equal
continuations. -/
private theorem option_bind_congr {α β : Type} {a₂ a₁ : Option α} {f₂ f₁ : α → Option β}
    (ha : a₂ = a₁) (hf : ∀ x, f₂ x = f₁ x) : a₂.bind f₂ = a₁.bind f₁ := by
  subst ha
  cases a₂ with
  | none => rfl
  | some x => exact hf x

/-- The three readings `containerInfo?` makes of a lookup, as
functions of an OPAQUE continuation: a former (`indBind`), a recursor
(`recBind`) and a constructor record (`ctorView`).  Naming them is what
lets the lookups' case analysis be done once, against a continuation
the kernel never has to look inside — the frame's proof term would
otherwise carry a copy of the container's whole body per constant
kind. -/
private def indBind {β : Type} (o : Option ConstantInfo)
    (f : ConstantVal → IndCaps → Option β) : Option β :=
  o.bind fun c => match c with | .indInfo cv caps => f cv caps | _ => none

@[inherit_doc indBind]
private def recBind {β : Type} (o : Option ConstantInfo)
    (f : ConstantVal → Nat → Nat → List RecRule → Option β) : Option β :=
  o.bind fun c => match c with | .recInfo cv mI rP rules => f cv mI rP rules | _ => none

@[inherit_doc indBind]
private def ctorView {β : Type} (o : Option ConstantInfo)
    (f : ConstantVal → Nat → Nat → Option β) : Option β :=
  match o with | some (.ctorInfo cv nP nF) => f cv nP nF | _ => none

/-- **A FORMER LOOKUP, FRAMED**: two lookups that agree on formers read
the same, at continuations that agree where they are used. -/
private theorem indBind_congr {β : Type} {o₂ o₁ : Option ConstantInfo}
    {f₂ f₁ : ConstantVal → IndCaps → Option β}
    (h : ∀ cv caps, o₂ = some (.indInfo cv caps) ↔ o₁ = some (.indInfo cv caps))
    (hf : ∀ cv caps, o₁ = some (.indInfo cv caps) → f₂ cv caps = f₁ cv caps) :
    indBind o₂ f₂ = indBind o₁ f₁ := by
  unfold indBind
  cases h2 : o₂ with
  | none =>
    cases h1 : o₁ with
    | none => rfl
    | some c1 =>
      cases c1 <;> first | rfl | exact absurd ((h _ _).mpr h1) (by simp [h2])
  | some c2 =>
    cases c2 with
    | indInfo cv caps =>
      have h1 := (h cv caps).mp h2
      rw [h1]
      exact hf cv caps h1
    | _ =>
      cases h1 : o₁ with
      | none => rfl
      | some c1 =>
        cases c1 <;> first | rfl | exact absurd ((h _ _).mpr h1) (by simp [h2])

/-- **A RECURSOR LOOKUP, FRAMED** (the twin of `indBind_congr`). -/
private theorem recBind_congr {β : Type} {o₂ o₁ : Option ConstantInfo}
    {f₂ f₁ : ConstantVal → Nat → Nat → List RecRule → Option β}
    (h : ∀ cv mI rP rules, o₂ = some (.recInfo cv mI rP rules) ↔
      o₁ = some (.recInfo cv mI rP rules))
    (hf : ∀ cv mI rP rules, o₁ = some (.recInfo cv mI rP rules) →
      f₂ cv mI rP rules = f₁ cv mI rP rules) :
    recBind o₂ f₂ = recBind o₁ f₁ := by
  unfold recBind
  cases h2 : o₂ with
  | none =>
    cases h1 : o₁ with
    | none => rfl
    | some c1 =>
      cases c1 <;> first | rfl | exact absurd ((h _ _ _ _).mpr h1) (by simp [h2])
  | some c2 =>
    cases c2 with
    | recInfo cv mI rP rules =>
      have h1 := (h cv mI rP rules).mp h2
      rw [h1]
      exact hf cv mI rP rules h1
    | _ =>
      cases h1 : o₁ with
      | none => rfl
      | some c1 =>
        cases c1 <;> first | rfl | exact absurd ((h _ _ _ _).mpr h1) (by simp [h2])

/-- **A CONSTRUCTOR LOOKUP, FRAMED**: the constructor records are read
by a match on the lookup itself, not through the `Option` bind. -/
private theorem ctorView_congr {β : Type} {o₂ o₁ : Option ConstantInfo}
    {f₂ f₁ : ConstantVal → Nat → Nat → Option β}
    (h : ∀ cv nP nF, o₂ = some (.ctorInfo cv nP nF) ↔ o₁ = some (.ctorInfo cv nP nF))
    (hf : ∀ cv nP nF, o₁ = some (.ctorInfo cv nP nF) → f₂ cv nP nF = f₁ cv nP nF) :
    ctorView o₂ f₂ = ctorView o₁ f₁ := by
  unfold ctorView
  cases h2 : o₂ with
  | none =>
    cases h1 : o₁ with
    | none => rfl
    | some c1 =>
      cases c1 <;> first | rfl | exact absurd ((h _ _ _).mpr h1) (by simp [h2])
  | some c2 =>
    cases c2 with
    | ctorInfo cv nP nF =>
      have h1 := (h cv nP nF).mp h2
      rw [h1]
      exact hf cv nP nF h1
    | _ =>
      cases h1 : o₁ with
      | none => rfl
      | some c1 =>
        cases c1 <;> first | rfl | exact absurd ((h _ _ _).mpr h1) (by simp [h2])

/-- **THE CONTAINER'S BLOCK IS READ THE SAME AT TWO ENVIRONMENTS THAT
AGREE OFF `N`** (task #315).  `N` is the extension's new names: they are
fresh at `env₁` (`hfresh`), the two environments store the same
constant at every name off `N` as far as the three inductive kinds go
(`hoff`), a NEW recursor belongs to a new container (`hrecOff`), the
old environment stores its recursors' rule constructors (`hctorOff`)
and resolves the constants its recursor types mention (`hmenOff`).
Then a container off `N` reads the same block at both. -/
private theorem containerInfo?_congr {env₁ env₂ : Env} {N : List Name}
    (hfresh : ∀ n ∈ N, env₁.find? n = none)
    (hoff : ∀ n : Name, n ∉ N → KindAgree env₁ env₂ n)
    (hrecOff : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      n ∉ N → env₂.find? (n.str "rec") = some (.recInfo cv mI rP rules) → n.str "rec" ∉ N)
    (hctorOff : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      env₁.find? n = some (.recInfo cv mI rP rules) → ∀ r ∈ rules, RecRule.ctor r ∉ N)
    (hmenOff : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      env₁.find? n = some (.recInfo cv mI rP rules) →
      ∀ C : Name, cv.type.mentionsConst C = true → C ∉ N)
    {I : Name} (hI : I ∉ N) :
    containerInfo? env₂ I = containerInfo? env₁ I := by
  -- the recursors agree wherever the container's own name is off `N`
  have hrecAgree : ∀ (n : Name), n ∉ N → ∀ cv mI rP rules,
      (env₂.find? (n.str "rec") = some (.recInfo cv mI rP rules) ↔
        env₁.find? (n.str "rec") = some (.recInfo cv mI rP rules)) := by
    intro n hn cv mI rP rules
    constructor
    · intro h2
      exact ((hoff _ (hrecOff n cv mI rP rules hn h2)).2.1 cv mI rP rules).mp h2
    · intro h1
      by_cases hmem : n.str "rec" ∈ N
      · rw [hfresh _ hmem] at h1; exact nomatch h1
      · exact ((hoff _ hmem).2.1 cv mI rP rules).mpr h1
  unfold containerInfo?
  by_cases hq : (I == quotName) = true
  · simp only [if_pos hq]
  simp only [if_neg hq, bind]
  -- the container's former and recursor
  refine indBind_congr (fun cv caps => (hoff I hI).1 cv caps) (fun cvT _ _ => ?_)
  refine recBind_congr (hrecAgree I hI) (fun cvR mI rP rules h1R => ?_)
  by_cases hle : rP ≤ mI
  case neg => simp only [if_neg hle]
  simp only [if_pos hle]
  refine option_bind_congr ?_ (fun nP => ?_)
  · -- the parameter count, off a constructor record
    cases hh : rules.head? with
    | none => rfl
    | some r =>
      dsimp only
      exact ctorView_congr
        (fun cv nP nF => (hoff _ (hctorOff _ _ _ _ _ h1R r (List.mem_of_mem_head? hh))).2.2
          cv nP nF)
        (fun _ _ _ _ => rfl)
  · -- the members, at a generic parameter count
    cases hsp : cvR.type.stripPis nP with
    | none => rfl
    | some bb =>
      obtain ⟨bs, body⟩ := bb
      simp only [Option.bind]
      have hagBody : ∀ C : Name, body.mentionsConst C = true → KindAgree env₁ env₂ C :=
        fun C hC => hoff C (hmenOff _ cvR mI rP rules h1R C (mentionsConst_stripPis nP hsp hC))
      rw [containerMembersGo_congr (rP + 1) 0 body hagBody]
      by_cases hnames : ((containerMembersGo env₁ nP (rP + 1) 0 body).contains I &&
          decide (containerMembersGo env₁ nP (rP + 1) 0 body).Nodup) = true
      case neg => simp only [if_neg hnames]
      simp only [if_pos hnames]
      refine option_bind_congr (mapM_option_congr ?_) (fun _ => rfl)
      intro C hCmem
      have hCN : C ∉ N := hmenOff _ cvR mI rP rules h1R C
        (mentionsConst_stripPis nP hsp (mem_containerMembersGo_mentions (rP + 1) 0 body hCmem))
      refine indBind_congr (fun cv caps => (hoff C hCN).1 cv caps) (fun cvC _ _ => ?_)
      refine recBind_congr (hrecAgree C hCN) (fun _ _ rPc rulesC h1CR => ?_)
      by_cases hcond : (rPc == rP && cvC.levelParams == cvT.levelParams) = true
      case neg => simp only [if_neg hcond]
      simp only [if_pos hcond]
      refine option_bind_congr (mapM_option_congr ?_) (fun _ => rfl)
      intro r hrmem
      exact ctorView_congr
        (fun cv nPc nF => (hoff _ (hctorOff _ _ _ _ _ h1CR r hrmem)).2.2 cv nPc nF)
        (fun _ _ _ _ => rfl)

/-! ## (E) The two frames -/

/-- **`containerInfo?` frame at a non-inductive extension**: it reads the
environment only through `find?` results of inductive kind (`indInfo`,
`recInfo`, `ctorInfo`), so an extension whose every new constant is of
another kind changes nothing. -/
theorem containerInfo?_ext_nonInd {env₁ env₂ : Env}
    (hext : ∀ (n : Name) (c : ConstantInfo), env₁.find? n = some c → env₂.find? n = some c)
    (hnew : ∀ (n : Name) (c : ConstantInfo), env₂.find? n = some c →
      env₁.find? n = some c ∨
        ((∀ cv caps, c ≠ .indInfo cv caps) ∧ (∀ cv mI rP rules, c ≠ .recInfo cv mI rP rules) ∧
          (∀ cv nP nF, c ≠ .ctorInfo cv nP nF)))
    (I : Name) : containerInfo? env₂ I = containerInfo? env₁ I := by
  refine containerInfo?_congr (N := []) (fun n hn => absurd hn (by simp)) (fun n _ => ?_)
    (fun _ _ _ _ _ _ _ => by simp) (fun _ _ _ _ _ _ _ _ => by simp)
    (fun _ _ _ _ _ _ _ _ => by simp) (by simp)
  refine ⟨fun cv caps => ⟨fun h => ?_, hext n _⟩, fun cv mI rP rules => ⟨fun h => ?_, hext n _⟩,
    fun cv nP nF => ⟨fun h => ?_, hext n _⟩⟩
  · rcases hnew n _ h with h' | ⟨hi, -, -⟩
    · exact h'
    · exact absurd rfl (hi cv caps)
  · rcases hnew n _ h with h' | ⟨-, hr, -⟩
    · exact h'
    · exact absurd rfl (hr cv mI rP rules)
  · rcases hnew n _ h with h' | ⟨-, -, hc⟩
    · exact h'
    · exact absurd rfl (hc cv nP nF)

/-- The frame at one fresh cons of a non-inductive kind. -/
theorem containerInfo?_cons_nonInd {env : Env} {c₀ : ConstantInfo}
    (hfresh : env.find? c₀.name = none)
    (hkind : (∀ cv caps, c₀ ≠ .indInfo cv caps) ∧ (∀ cv mI rP rules, c₀ ≠ .recInfo cv mI rP rules) ∧
      (∀ cv nP nF, c₀ ≠ .ctorInfo cv nP nF))
    (I : Name) : containerInfo? ⟨c₀ :: env.consts⟩ I = containerInfo? env I := by
  refine containerInfo?_ext_nonInd (fun n c h => Env.find?_cons_of_fresh hfresh h)
    (fun n c h => ?_) I
  rw [Env.find?_cons] at h
  split at h
  · obtain rfl := Option.some.inj h
    exact Or.inr hkind
  · exact Or.inl h

/-- **`containerInfo?` frame at an inductive extension, off the new names**:
an old container's block is read the same at the extended environment,
provided the new constants are exactly the names `N`, fresh at `env₁`,
every NEW recursor is named `T.rec` for a new `T`, and the old
environment is well-formed with its recursors' rule constructors stored. -/
theorem containerInfo?_ext_ind {env₁ env₂ : Env} {N : List Name}
    (hext : ∀ (n : Name) (c : ConstantInfo), env₁.find? n = some c → env₂.find? n = some c)
    (hnew : ∀ (n : Name) (c : ConstantInfo), env₂.find? n = some c → env₁.find? n = some c ∨ n ∈ N)
    (hfresh : ∀ n ∈ N, env₁.find? n = none)
    (hrecN : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      env₂.find? (n.str "rec") = some (.recInfo cv mI rP rules) → n.str "rec" ∈ N → n ∈ N)
    (hwf : EnvWF env₁) (hrc : RecCtorsStored env₁)
    {I : Name} (hI : I ∉ N) {ci : ContainerInfo} :
    containerInfo? env₂ I = some ci → containerInfo? env₁ I = some ci := by
  have hcongr : containerInfo? env₂ I = containerInfo? env₁ I := by
    refine containerInfo?_congr hfresh (fun n hn => ?_)
      (fun n cv mI rP rules hn h2 hmem => hn (hrecN n cv mI rP rules h2 hmem)) (fun n cv mI rP
        rules h1 r hr hmem => ?_) (fun n cv mI rP rules h1 C hC hmem => ?_) hI
    · exact ⟨fun cv caps => ⟨fun h2 => (hnew n _ h2).resolve_right hn, hext n _⟩,
        fun cv mI rP rules => ⟨fun h2 => (hnew n _ h2).resolve_right hn, hext n _⟩,
        fun cv nP nF => ⟨fun h2 => (hnew n _ h2).resolve_right hn, hext n _⟩⟩
    · obtain ⟨⟨cvj, cnP, cnF, hf⟩, -, -⟩ := hrc n cv mI rP rules h1 r hr
      rw [hfresh _ hmem] at hf
      exact nomatch hf
    · have hres : cv.type.constsResolve env₁ = true :=
        (hwf _ (List.mem_of_find?_eq_some h1)).2.2.1
      have hsome := mentionsConst_of_constsResolve cv.type hres hC
      rw [hfresh _ hmem] at hsome
      simp at hsome
  intro h
  rw [← hcongr]
  exact h

end ConLeche
