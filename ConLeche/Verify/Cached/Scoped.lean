module

public import ConLeche.Modular
public import ConLeche.Semantics.DeclRun
public import ConLeche.Semantics.Inductives.DeclBlock
public import ConLeche.Verify.Inductives.GenRecRun
import ConLeche.Semantics.DeclWF
import ConLeche.Verify.Cached.JustifyBridge
import ConLeche.Verify.Cached.DeclPushes
import ConLeche.Verify.Cached.BlockPushes
import ConLeche.Verify.Extend.Inversions
import ConLeche.Verify.Inductives.BlockShapeInv

/-!
# Accepted environments are read-scoped (task #619)

Every environment an accepting declaration fold reaches is **read-scoped** (`Scoped`): what each
stored constant's laws read is stored (`EntryScoped`: its type's names, a definition's value's, a
recursor's rules' right-hand sides, constructors and nested pins, a type former's block members,
the names its fast path reads, `pinFootprint`), and each stored projection table's constructor and
bodies' names are stored.  `declsRun_scoped` carries it along the run, model-free.

What each record adds reads only stored names:

* the terms (types, values, right-hand sides, nested pins, table bodies) resolve, by the
  environment's well-formedness (`checkDecl_envWF`, the justification route's `ConstantValRun`);
* a recursor's rules name the constructors of the class its major is: a member's constructors are
  installed by the same record, an outside class's are stored constructors of the environment the
  classes are checked at (`targetCtorsOf`, `nestContainer_mem`);
* a former's block members and a table's constructor are names the same record installs;
* a pinned name's footprint: a certified `Nat` operation's install guard (`natOpGuard`) stores its
  dependencies, the `Nat` basis and, where it reads `Bool`, `Bool`'s constructors (whose stored
  type names `Bool`); a compiler-trust opaque's install stores its element type (`reduceElemOk`);
  no other record takes such a name (`checkConstantVal`, `justifiable`), so its footprint is empty.

Old constants stay read-scoped: a step only adds constants and tables, so what was stored stays
stored.
-/

public section

namespace ConLeche.Cached

open ConLeche ConLeche.Semantics ConLeche.Modular ConLeche.Verify

variable {pins : List NatOpPinSet}

/-! ## Read-scoped environments -/

/-- **A read-scoped environment**: every stored constant's laws read stored names
(`EntryScoped`), and every stored projection table's constructor and bodies do. -/
@[expose] def Scoped (E : Env) : Prop :=
  (∀ c ∈ E.consts, EntryScoped E c) ∧
  ∀ t ∈ E.tables, (E.find? t.ctor).isSome = true ∧ ∀ b ∈ t.bodies.toList, b.constsResolve E = true

/-- The empty environment is read-scoped. -/
theorem Scoped.empty : Scoped Env.empty :=
  ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩

theorem find?_isSome_iff_mem {E : Env} {n : Name} :
    (E.find? n).isSome = true ↔ ∃ c ∈ E.consts, c.name = n := by
  unfold Env.find?
  rw [List.find?_isSome]
  simp

theorem find?_isSome_of_mem {E : Env} {c : ConstantInfo} (h : c ∈ E.consts) :
    (E.find? c.name).isSome = true :=
  find?_isSome_iff_mem.mpr ⟨c, h, rfl⟩

theorem find?_isSome_of_sub {E E₂ : Env} (h : ∀ c ∈ E.consts, c ∈ E₂.consts) {n : Name}
    (hn : (E.find? n).isSome = true) : (E₂.find? n).isSome = true := by
  obtain ⟨c, hc, rfl⟩ := find?_isSome_iff_mem.mp hn
  exact find?_isSome_of_mem (h c hc)

/-- What a constant reads stays stored as the environment grows. -/
theorem EntryScoped.mono {E E₂ : Env} {c : ConstantInfo}
    (hf : ∀ n, (E.find? n).isSome = true → (E₂.find? n).isSome = true)
    (h : EntryScoped E c) : EntryScoped E₂ c := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hr := fun {e : Expr} (he : e.constsResolve E = true) => Expr.constsResolve_of_find hf he
  refine ⟨hr h1, fun cv v hh he => hr (h2 cv v hh he), fun cv mI rP isK rules he r hrr => ?_,
    fun cv caps he m hm => hf _ (h4 cv caps he m hm), fun d hd => hf _ (h5 d hd)⟩
  obtain ⟨a, b, c'⟩ := h3 cv mI rP isK rules he r hrr
  exact ⟨hr a, hf _ b, fun lvls ps hfire q hq => hr (c' lvls ps hfire q hq)⟩

/-- **A stored constant of a well-formed environment is read-scoped** once its rules' constructors,
its block members and its footprint are stored: its terms resolve (`ConstWF`). -/
theorem entryScoped_of {E : Env} {c : ConstantInfo} (hwf : EnvWF E) (hc : c ∈ E.consts)
    (hctor : ∀ cv mI rP isK rules, c = .recInfo cv mI rP isK rules → ∀ r ∈ rules,
      (E.find? r.ctor).isSome = true)
    (hall : ∀ cv caps, c = .indInfo cv caps → ∀ m ∈ caps.all, (E.find? m).isSome = true)
    (hfp : ∀ d ∈ pinFootprint c.toConstantVal.name, (E.find? d).isSome = true) :
    EntryScoped E c := by
  obtain ⟨-, -, h3, -, h5, h6⟩ := hwf.consts c hc
  refine ⟨h3, fun cv v hh he => (h5 cv v hh he).2.2.1, fun cv mI rP isK rules he r hr => ?_,
    hall, hfp⟩
  obtain ⟨-, -, hrr, -, hn⟩ := h6 cv mI rP isK rules he r hr
  exact ⟨hrr, hctor cv mI rP isK rules he r hr,
    fun lvls ps hf q hq => ((hn lvls ps hf).2.2.1 q hq).2.2.1⟩

/-- **A step that adds read-scoped constants and tables keeps the environment read-scoped.** -/
theorem Scoped.extend {E E₂ : Env} (hS : Scoped E) (hwf : EnvWF E₂)
    {new : List ConstantInfo} {newQ : List ProjTable}
    (hc : E₂.consts = new ++ E.consts) (ht : E₂.tables = newQ ++ E.tables)
    (hnew : ∀ c ∈ new, EntryScoped E₂ c)
    (hnewQ : ∀ t ∈ newQ, (E₂.find? t.ctor).isSome = true) : Scoped E₂ := by
  have hsub : ∀ c ∈ E.consts, c ∈ E₂.consts := fun c h => by
    rw [hc]; exact List.mem_append_right _ h
  have hf : ∀ n, (E.find? n).isSome = true → (E₂.find? n).isSome = true :=
    fun _ h => find?_isSome_of_sub hsub h
  refine ⟨fun c h => ?_, fun t h => ⟨?_, fun b hb => ?_⟩⟩
  · rw [hc] at h
    rcases List.mem_append.mp h with h | h
    · exact hnew c h
    · exact EntryScoped.mono hf (hS.1 c h)
  · have h' := h
    rw [ht] at h'
    rcases List.mem_append.mp h' with h' | h'
    · exact hnewQ t h'
    · exact hf _ (hS.2 t h').1
  · obtain ⟨-, -, hb'⟩ := hwf.tables t h
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hb
    rw [Array.getElem?_toList] at hi
    exact (hb' i b hi).2.2.1

/-- One constant consed. -/
theorem Scoped.cons {E : Env} {c : ConstantInfo} (hS : Scoped E)
    (hwf : EnvWF ⟨c :: E.consts, E.tables⟩) (hc : EntryScoped ⟨c :: E.consts, E.tables⟩ c) :
    Scoped ⟨c :: E.consts, E.tables⟩ :=
  hS.extend hwf (new := [c]) (newQ := []) rfl rfl
    (fun c' h => by rw [List.mem_singleton.mp h]; exact hc) (fun _ h => nomatch h)

/-- One constant consed, from its own facts. -/
theorem Scoped.cons_of {E : Env} {c : ConstantInfo} (hS : Scoped E)
    (hwf : EnvWF ⟨c :: E.consts, E.tables⟩)
    (hctor : ∀ cv mI rP isK rules, c = .recInfo cv mI rP isK rules → ∀ r ∈ rules,
      (Env.find? ⟨c :: E.consts, E.tables⟩ r.ctor).isSome = true)
    (hall : ∀ cv caps, c = .indInfo cv caps → ∀ m ∈ caps.all,
      (Env.find? ⟨c :: E.consts, E.tables⟩ m).isSome = true)
    (hfp : ∀ d ∈ pinFootprint c.toConstantVal.name,
      (Env.find? ⟨c :: E.consts, E.tables⟩ d).isSome = true) :
    Scoped ⟨c :: E.consts, E.tables⟩ :=
  hS.cons hwf (entryScoped_of hwf List.mem_cons_self hctor hall hfp)

/-! ## The footprint of a pinned name -/

/-- A name that is neither a certified operation's nor a compiler-trust operation's reads nothing
on a fast path. -/
theorem pinFootprint_nil {n : Name} (h1 : natOpName n = false)
    (h2 : reduceOpNames.contains n = false) : pinFootprint n = [] := by
  simp only [natOpName, Bool.or_eq_false_iff] at h1
  simp only [pinFootprint, h1.1, h1.2, h2, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
    List.append_nil]

/-- A constant whose name takes no pin reads nothing on a fast path. -/
theorem footprint_of_nil {E : Env} {n : Name} (h1 : natOpName n = false)
    (h2 : reduceOpNames.contains n = false) :
    ∀ d ∈ pinFootprint n, (E.find? d).isSome = true := by
  rw [pinFootprint_nil h1 h2]
  exact fun _ h => nomatch h

theorem natIndOk_isSome {o : Option ConstantInfo} (h : natIndOk o = true) : o.isSome = true := by
  cases o with
  | none => exact nomatch h
  | some _ => rfl

theorem natZeroOk_isSome {o : Option ConstantInfo} (h : natZeroOk o = true) :
    o.isSome = true := by
  cases o with
  | none => exact nomatch h
  | some _ => rfl

theorem natSuccOk_isSome {o : Option ConstantInfo} (h : natSuccOk o = true) :
    o.isSome = true := by
  cases o with
  | none => exact nomatch h
  | some _ => rfl

/-- `Bool.true`, stored as the guard reads it: at the type `Bool`. -/
theorem natOpGuard_boolTrue {E : Env} {c : Name} (h : natOpGuard E c = true)
    (hc : (c = natBeqName || c = natBleName || natDivModNames.contains c) = true) :
    ∃ ci, E.find? boolTrueName = some ci ∧ ci.toConstantVal.type = .const boolName [] := by
  unfold natOpGuard at h
  simp only [hc, ↓reduceIte, Bool.and_eq_true] at h
  obtain ⟨-, hT, -⟩ := h
  revert hT
  split
  · next ci heq =>
    intro hh
    simp only [Bool.and_eq_true, beq_iff_eq] at hh
    exact ⟨ci, heq, hh.2⟩
  · intro hh; exact nomatch hh

/-- **A certified operation's install guard stores its footprint.** -/
theorem natOpGuard_footprint {E : Env} (hwf : EnvWF E) {c : Name} (h : natOpGuard E c = true)
    (hred : reduceOpNames.contains c = false) :
    ∀ d ∈ pinFootprint c, (E.find? d).isSome = true := by
  obtain ⟨hlit, hdeps, hbool⟩ := natOpGuard_inv h
  simp only [natLitSupported, Bool.and_eq_true] at hlit
  obtain ⟨⟨hN, hZ⟩, hS⟩ := hlit
  intro d hd
  simp only [pinFootprint, hred, Bool.false_eq_true, ↓reduceIte, List.append_nil] at hd
  split at hd
  · rcases List.mem_append.mp hd with hd | hd
    · rcases List.mem_append.mp hd with hd | hd
      · exact hdeps d hd
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl
        · exact natIndOk_isSome hN
        · exact natZeroOk_isSome hZ
        · exact natSuccOk_isSome hS
    · split at hd
      · next hc =>
        have hc' : (c = natBeqName || c = natBleName || natDivModNames.contains c) = true := by
          simpa using hc
        obtain ⟨⟨ciT, hT, -⟩, ⟨ciF, hF, -⟩⟩ := hbool (by simpa [or_assoc] using hc')
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl
        · obtain ⟨ci, hci, hty⟩ := natOpGuard_boolTrue h hc'
          have hr := (hwf.consts ci (Env.find?_mem hci)).2.2.1
          rw [hty] at hr
          simpa [Expr.constsResolve] using hr
        · rw [hT]; rfl
        · rw [hF]; rfl
      · exact nomatch hd
  · exact nomatch hd

/-- **A compiler-trust opaque's install guard stores its element type.** -/
theorem reduceElemOk_isSome {E : Env} {c : Name} (h : reduceElemOk E c = true) :
    (E.find? (reduceElemName c)).isSome = true := by
  unfold reduceElemOk at h
  unfold reduceElemName
  split at h
  · simp only [‹c = reduceNatName›, ↓reduceIte]
    revert h; split
    · next heq => intro _; rw [heq]; rfl
    · intro h; exact nomatch h
  · simp only [‹¬c = reduceNatName›, ↓reduceIte]
    revert h; split
    · next heq => intro _; rw [heq]; rfl
    · intro h; exact nomatch h

/-- The compiler-trust names are no certified operation's. -/
theorem natOpName_of_reduce {c : Name} (h : reduceOpNames.contains c = true) :
    natOpName c = false := by
  simp only [reduceOpNames, List.contains_cons, List.contains_nil, Bool.or_false,
    Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | rfl <;> decide

/-- The certified operations' names are no compiler-trust name. -/
theorem reduce_of_natOpName {c : Name} (h : natOpName c = true) :
    reduceOpNames.contains c = false := by
  cases hr : reduceOpNames.contains c with
  | false => rfl
  | true => rw [natOpName_of_reduce hr] at h; exact nomatch h

/-! ## The checks that keep a name off the pins -/

/-- Only an opaque constant takes a compiler-trust name. -/
theorem checkConstantVal_reduce_false {mode : CheckMode} {F : Nat} {env : Env} {cv : ConstantVal}
    {a c : Bool} (h : checkConstantVal (fueledOps mode F) env cv a false c = .ok ()) :
    reduceOpNames.contains cv.name = false := by
  cases hn : reduceOpNames.contains cv.name with
  | false => rfl
  | true =>
    exfalso
    simp only [checkConstantVal, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    by_cases hfind : (env.find? cv.name).isSome = true
    · simp [hfind] at h
    by_cases hop : (natOpName cv.name && !a) = true
    · simp only [hfind, Bool.false_eq_true, ↓reduceIte] at h
      rw [ite_eq_left hop] at h
      exact nomatch h
    simp only [hfind, hop, Bool.false_eq_true, ↓reduceIte] at h
    have hred : (reduceOpNames.contains cv.name && !false) = true := by rw [hn]; rfl
    rw [ite_eq_left hred] at h
    exact nomatch h

/-- `checkConstantValF` at its defaults keeps a name off both pins. -/
theorem checkConstantValF_names {mode : CheckMode} {F : Nat} {fe : FEnv} {cv : ConstantVal}
    (h : checkConstantValF (fueledOps mode F) fe cv = .ok ()) :
    natOpName cv.name = false ∧ reduceOpNames.contains cv.name = false := by
  simp only [checkConstantValF, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  by_cases hfind : (fe.find? cv.name).isSome = true
  · simp [hfind] at h
  by_cases hop : (natOpName cv.name && !false) = true
  · simp only [hfind, Bool.false_eq_true, ↓reduceIte] at h
    rw [ite_eq_left hop] at h
    exact nomatch h
  by_cases hred : (reduceOpNames.contains cv.name && !false) = true
  · simp only [hfind, hop, Bool.false_eq_true, ↓reduceIte] at h
    rw [ite_eq_left hred] at h
    exact nomatch h
  simp only [Bool.not_false, Bool.and_true, Bool.not_eq_true] at hop hred
  exact ⟨hop, hred⟩

/-- `checkConstantVal` at its defaults keeps a name off both pins. -/
theorem checkConstantVal_names {mode : CheckMode} {F : Nat} {env : Env} {cv : ConstantVal}
    (h : checkConstantVal (fueledOps mode F) env cv = .ok ()) :
    natOpName cv.name = false ∧ reduceOpNames.contains cv.name = false :=
  ⟨checkConstantVal_opName_false h, checkConstantVal_reduce_false h⟩

/-- A definition's record passed its constant check. -/
theorem checkDeclKind_defn_ccv {F : Nat} {env env₂ : Env} {cv : ConstantVal} {v : Expr}
    {hint : ReducibilityHint}
    (h : checkDeclKind (fueledOps .verified F) pins env (.defnDecl cv v hint) = .ok env₂) :
    checkConstantVal (fueledOps .verified F) env cv true = .ok () := by
  simp only [checkDeclKind, Bind.bind, Except.bind] at h
  cases hccv : checkConstantVal (fueledOps .verified F) env cv true with
  | error e => rw [hccv] at h; exact nomatch h
  | ok u => rfl

/-- A theorem's record passed its constant check. -/
theorem checkDeclKind_thm_ccv {F : Nat} {env env₂ : Env} {cv : ConstantVal} {v : Expr}
    (h : checkDeclKind (fueledOps .verified F) pins env (.thmDecl cv v) = .ok env₂) :
    checkConstantVal (fueledOps .verified F) env cv = .ok () := by
  simp only [checkDeclKind, Bind.bind, Except.bind] at h
  cases hccv : checkConstantVal (fueledOps .verified F) env cv with
  | error e => rw [hccv] at h; exact nomatch h
  | ok u => rfl

/-- An axiom's record other than `Quot.sound`'s passed its constant check. -/
theorem checkDeclKind_axiom_ccv {F : Nat} {env env₂ : Env} {cv : ConstantVal}
    (h : checkDeclKind (fueledOps .verified F) pins env (.axiomDecl cv) = .ok env₂)
    (hqs : cv.name ≠ quotSoundName) :
    checkConstantVal (fueledOps .verified F) env cv false false true = .ok () := by
  simp only [checkDeclKind, Bind.bind, Except.bind] at h
  rw [ite_eq_right hqs] at h
  cases hccv : checkConstantVal (fueledOps .verified F) env cv false false true with
  | error e => rw [hccv] at h; exact nomatch h
  | ok u => rfl

/-- A statement a solution justifies takes no pinned name. -/
theorem justifiable_names {pd : Declaration} {cv : ConstantVal} (h : justifiable pd = some cv) :
    natOpName cv.name = false ∧ reduceOpNames.contains cv.name = false := by
  cases pd with
  | axiomDecl c =>
    simp only [justifiable] at h
    split at h
    · exact nomatch h
    · next hn =>
      obtain rfl := Option.some.inj h
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hn
      exact ⟨hn.1.2, hn.2⟩
  | _ => simp [justifiable] at h

/-! ## The quotient package's records -/

theorem quotPin_names (k : QuotKind) :
    natOpName (quotPin k).toConstantVal.name = false ∧
      reduceOpNames.contains (quotPin k).toConstantVal.name = false := by
  cases k <;> decide

/-- **A quotient record keeps the environment read-scoped**: its pin is no recursor, `Quot` lists
no block member, and no slot takes a pinned name. -/
theorem declQuotRun_scoped {env env₂ : Env} {k : QuotKind} {cv : ConstantVal}
    (hS : Scoped env) (hwf : EnvWF env₂) (h : DeclQuotRun env k cv env₂) : Scoped env₂ := by
  obtain ⟨-, hp, -, -, rfl⟩ := h
  -- `Quot.lift`'s and `Quot.ind`'s rules fire at `Quot.mk`, stored before them
  have hM : (k = .lift ∨ k = .ind) →
      (Env.find? ⟨quotAt k cv :: env.consts, env.tables⟩ quotMkName).isSome = true := by
    intro hk
    have hm : (env.find? quotMkName).isSome = true := by
      rcases hk with rfl | rfl <;>
        simp only [quotPredsOk, Bool.and_eq_true] at hp <;> exact hp.2
    exact find?_isSome_of_sub (fun c hc => List.mem_cons_of_mem _ hc) hm
  refine hS.cons_of hwf (fun cv' mI rP isK rules he => ?_) (fun cv' caps he => ?_) ?_
  · have he' := he
    unfold quotAt at he'
    generalize quotLifted k cv = b at he'
    cases k <;> cases b <;> first
      | (change ConstantInfo.recInfo _ _ _ _ _ = _ at he'
         injection he' with _ _ _ _ e5
         subst e5
         intro r hr
         simp only [List.map_cons, List.map_nil, List.mem_singleton] at hr
         subst hr
         first | exact hM (.inl rfl) | exact hM (.inr rfl))
      | exact nomatch he'
  · have he' := he
    unfold quotAt at he'
    generalize quotLifted k cv = b at he'
    cases k <;> cases b <;> first
      | (change ConstantInfo.indInfo _ _ = _ at he'
         injection he' with _ e2
         subst e2
         intro m hm
         exact nomatch hm)
      | exact nomatch he'
  · rw [show (quotAt k cv).toConstantVal.name = (quotPin k).toConstantVal.name from quotAt_name k cv]
    exact footprint_of_nil (quotPin_names k).1 (quotPin_names k).2

/-! ## The value and axiom kinds -/

/-- **A definition's record keeps the environment read-scoped.** -/
theorem declDefn_scoped {F : Nat} {env env₂ : Env} {cv : ConstantVal} {value : Expr}
    {hint : ReducibilityHint} (hS : Scoped env) (hwf : EnvWF env₂)
    (hccv : checkConstantVal (fueledOps .verified F) env cv true = .ok ())
    (h : DeclDefnRun F env cv value hint env₂) : Scoped env₂ := by
  obtain ⟨type', value', -, -, rfl, hnat, hdm⟩ := h
  refine hS.cons_of hwf (fun _ _ _ _ _ he => nomatch he) (fun _ _ he => nomatch he) ?_
  show ∀ d ∈ pinFootprint cv.name, _
  have hred := checkConstantVal_reduce_false hccv
  cases hn : natOpNames.contains cv.name with
  | true => exact natOpGuard_footprint hwf (hnat hn).1 hred
  | false =>
    cases hd : natDivModNames.contains cv.name with
    | true =>
      have hg := (hdm hd).1
      simp only [divModEnvGuard, Bool.and_eq_true] at hg
      exact natOpGuard_footprint hwf hg.1.1.1.1 hred
    | false => exact footprint_of_nil (by simp only [natOpName, hn, hd, Bool.or_self]) hred

/-- **A theorem's record keeps the environment read-scoped.** -/
theorem declThm_scoped {F : Nat} {env env₂ : Env} {cv : ConstantVal} {value : Expr}
    (hS : Scoped env) (hwf : EnvWF env₂)
    (hccv : checkConstantVal (fueledOps .verified F) env cv = .ok ())
    (h : DeclThmRun F env cv value env₂) : Scoped env₂ := by
  obtain ⟨hop, type', value', -, -, -, rfl⟩ := h
  refine hS.cons_of hwf (fun _ _ _ _ _ he => nomatch he) (fun _ _ he => nomatch he) ?_
  show ∀ d ∈ pinFootprint cv.name, _
  exact footprint_of_nil hop (checkConstantVal_reduce_false hccv)

/-- **An opaque constant's record keeps the environment read-scoped**: at a compiler-trust name its
install stores the element type. -/
theorem declOpaque_scoped {F : Nat} {env env₂ : Env} {cv : ConstantVal} {value : Expr}
    (hS : Scoped env) (hwf : EnvWF env₂) (h : DeclOpaqueRun F env cv value env₂) :
    Scoped env₂ := by
  obtain ⟨hop, type', value', -, -, rfl, hred⟩ := h
  refine hS.cons_of hwf (fun _ _ _ _ _ he => nomatch he) (fun _ _ he => nomatch he) ?_
  show ∀ d ∈ pinFootprint cv.name, _
  cases hr : reduceOpNames.contains cv.name with
  | false => exact footprint_of_nil hop hr
  | true =>
    have he := reduceElemOk_isSome (hred hr).2.1
    simp only [natOpName, Bool.or_eq_false_iff] at hop
    intro d hd
    simp only [pinFootprint, hop.1, hop.2, hr, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
      List.nil_append, List.mem_singleton] at hd
    subst hd
    exact find?_isSome_of_sub (fun c hc => List.mem_cons_of_mem _ hc) he

/-- **An axiom's record keeps the environment read-scoped.** -/
theorem declAxiom_scoped {F : Nat} {env env₂ : Env} {cv : ConstantVal}
    (hS : Scoped env) (hwf : EnvWF env₂)
    (hccv : cv.name ≠ quotSoundName →
      checkConstantVal (fueledOps .verified F) env cv false false true = .ok ())
    (h : DeclAxiomRun F env cv env₂) : Scoped env₂ := by
  rcases h with ⟨-, hq⟩ | ⟨hqs, type', hop, -, harm⟩
  · exact declQuotRun_scoped hS hwf hq
  have hfp := footprint_of_nil (E := env₂) hop (checkConstantVal_reduce_false (hccv hqs))
  have hax : env₂ = ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ :: env.consts, env.tables⟩ →
      Scoped env₂ := by
    rintro rfl
    exact hS.cons_of hwf (fun _ _ _ _ _ he => nomatch he) (fun _ _ he => nomatch he) hfp
  rcases harm with ⟨-, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ | ⟨-, -, -, -, -, -, -, rfl⟩
  · exact hax he
  · exact hax he
  · exact hax he
  · exact hS

/-! ## One record -/

/-! ## The inductive block's record -/

theorem fst_mem_of_mem_zipIdx {α : Type} : ∀ {l : List α} {i : Nat} {x : α × Nat},
    x ∈ l.zipIdx i → x.1 ∈ l
  | [], _, _, h => nomatch h
  | a :: l, i, x, h => by
    simp only [List.zipIdx_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (fst_mem_of_mem_zipIdx h)

theorem mem_zipIdx_of_mem {α : Type} : ∀ {l : List α} {i : Nat} {a : α},
    a ∈ l → ∃ k, (a, k) ∈ l.zipIdx i
  | [], _, _, h => nomatch h
  | b :: l, i, a, h => by
    simp only [List.zipIdx_cons, List.mem_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨i, .inl rfl⟩
    · obtain ⟨k, hk⟩ := mem_zipIdx_of_mem (i := i + 1) h
      exact ⟨k, .inr hk⟩

/-- A former's block members are the block's member names. -/
theorem blockCapsAt_all (p : BlockShape) (i : Nat) (isRec : Bool) :
    (blockCapsAt p i isRec).all = p.memberNames := by
  unfold blockCapsAt
  split <;> rfl

/-- A structure-like member's constructor is one of its constructors. -/
theorem structCtor?_mem {ms : MemberShape} {c : ConstantVal × Nat} (h : ms.structCtor? = some c) :
    c ∈ ms.ctors := by
  unfold MemberShape.structCtor? at h
  split at h
  · next c' hc =>
    split at h
    · obtain rfl := Option.some.inj h
      rw [hc]; exact List.mem_singleton_self _
    · exact nomatch h
  · exact nomatch h

/-- **A projection table's constructor is its member's.** -/
theorem blockTables_ctor (p : BlockShape) :
    ∀ (L : List MemberShape) (Q : List ProjTable), blockTables p L = some Q →
      ∀ t ∈ Q, ∃ ms ∈ L, ∃ c ∈ ms.ctors, t.ctor = c.1.name
  | [], Q, h, t, ht => by
    simp only [blockTables, Option.some.injEq] at h
    subst h; exact nomatch ht
  | ms :: rest, Q, h, t, ht => by
    simp only [blockTables] at h
    split at h
    · next c hc =>
      obtain ⟨bodies, -, hb⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨Q', hQ', rfl⟩ := Option.map_eq_some_iff.mp hb
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨ms, List.mem_cons_self, c, structCtor?_mem hc, rfl⟩
      · obtain ⟨ms', h1, h2⟩ := blockTables_ctor p rest Q' hQ' t ht
        exact ⟨ms', List.mem_cons_of_mem _ h1, h2⟩
    · obtain ⟨ms', h1, h2⟩ := blockTables_ctor p rest Q h t ht
      exact ⟨ms', List.mem_cons_of_mem _ h1, h2⟩

/-- A stored rule fires at one of its class's constructors. -/
theorem sumRules_ctor : ∀ {cs : List (ConstantVal × Nat)} {rhss : List Expr} {r : RecRule},
    r ∈ sumRules cs rhss → ∃ x ∈ cs, r.ctor = x.1.name
  | c :: cs, rhs :: rhss, r, h => by
    simp only [sumRules, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨c, List.mem_cons_self, rfl⟩
    · obtain ⟨x, hx, he⟩ := sumRules_ctor h
      exact ⟨x, List.mem_cons_of_mem _ hx, he⟩
  | [], _, _, h => by simp [sumRules] at h
  | _ :: _, [], _, h => by simp [sumRules] at h

theorem generatedRules_ctor {rP : Nat} {M : TargetMajor} {rhss : List Expr} {r : RecRule}
    (h : r ∈ generatedRules rP M rhss) : ∃ x ∈ M.ctors, r.ctor = x.1.name := by
  unfold generatedRules at h
  split at h
  · obtain ⟨r', hr', rfl⟩ := List.mem_map.mp h
    obtain ⟨x, hx, he⟩ := sumRules_ctor hr'
    exact ⟨x, hx, he⟩
  · exact sumRules_ctor h

/-- The generated recursors' records, one per stored recursor. -/
theorem mem_blockRecInfosTF {p : BlockShape} :
    ∀ {m : Nat} {L : List (ConstantVal × TargetMajor × List Expr)} {c : ConstantInfo},
      c ∈ blockRecInfosTF p m L → ∃ t ∈ L, ∃ k,
        c = .recInfo t.1 (p.majorIdxAt k) (p.rulePrefixAt k) (recKExpected p t.2.1)
          (generatedRules (p.rulePrefixAt k) t.2.1 t.2.2)
  | _, [], _, h => nomatch h
  | m, t :: L, c, h => by
    simp only [blockRecInfosTF, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨t, List.mem_cons_self, m, rfl⟩
    · obtain ⟨t', ht', k, he⟩ := mem_blockRecInfosTF h
      exact ⟨t', List.mem_cons_of_mem _ ht', k, he⟩

/-- The stream's recursor records, checked as constants. -/
theorem classStreamRecs_checked {mode : CheckMode} {F : Nat} {fe : FEnv} :
    ∀ {recs : List RecShape} {cvs : List ConstantVal},
      classStreamRecs (fueledOps mode F) fe recs = .ok cvs →
      ∀ rc ∈ recs, checkConstantValF (fueledOps mode F) fe rc.cvR = .ok ()
  | [], _, _, _, h => nomatch h
  | rc :: rcs, cvs, h, rc', hrc => by
    unfold classStreamRecs at h
    obtain ⟨u, hu, h⟩ := exceptBind_ok h
    obtain ⟨cvs', hcvs, -⟩ := exceptBind_ok h
    rcases List.mem_cons.mp hrc with rfl | hrc
    · cases u; exact hu
    · exact classStreamRecs_checked hcvs rc' hrc

/-- **A class's constructors**: a member's, or stored constructors of the environment the class
is checked at. -/
theorem classMajor_ctors {F : Nat} {env₁ : Env} {p : BlockShape} {pfvs : List Expr}
    {key : ClassKey} {M : TargetMajor}
    (C : ClassMajorRun .verified F (mkFEnv env₁) p pfvs key M) :
    ∀ x ∈ M.ctors, (∃ ms ∈ p.members, x ∈ ms.ctors) ∨ (env₁.find? x.1.name).isSome = true := by
  cases C.major with
  | member I t ms hfn ht hms hpar nfs =>
    intro x hx
    exact .inl ⟨ms, List.mem_of_getElem? hms, hx⟩
  | outside I us nPc nIdx ctors sI hfn ht hnq hctors hdsLen hdsSc hment hinst hsort nfs =>
    intro x hx
    unfold targetCtorsOf at hctors
    obtain ⟨n, nPc', T, hn⟩ := nestContainer_mem hctors x hx
    have hn' : env₁.find? n = some (.ctorInfo x.1 nPc' x.2 T) := by
      rw [← mkFEnv_find? env₁ n]; exact hn
    have hname := Env.find?_name hn'
    right
    rw [show x.1.name = n from hname, hn']
    rfl

/-- **The classes' constructors**: every constructor a generated recursor's class carries is a
member's, or stored at the formers' environment. -/
theorem genRecCheck_out_ctors {F : Nat} {env₁ : Env} {fe : FEnv} {p : BlockShape}
    {nestedBit : Bool} {params : List Expr} {tbl : List NestCtorNf} {rd : ClassRead}
    {Ms₀ : List TargetMajor} {block : List ConstantInfo}
    {out : List (ConstantVal × TargetMajor × List Expr)}
    (hcls : checkBlockClasses (fueledOps .verified F) (mkFEnv env₁) p params = .ok (rd, Ms₀))
    (h : genRecCheck (fueledOps .verified F) fe p nestedBit params tbl rd Ms₀ block = .ok out) :
    ∀ g ∈ out, ∀ x ∈ g.2.1.ctors,
      (∃ ms ∈ p.members, x ∈ ms.ctors) ∨ (env₁.find? x.1.name).isSome = true := by
  obtain ⟨S⟩ := genRecCheck_run h
  obtain ⟨C⟩ := checkBlockClasses_run hcls
  obtain ⟨hlenK, hallK⟩ := classMajors_run C.hMs
  obtain ⟨hlenN, hallN⟩ := classesNfs_run S.hMs
  obtain ⟨hlenO, hallO⟩ := classRecsRulesOk_run S.hrules
  intro g hg x hx
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hg
  have hil : i < out.length := (List.getElem?_eq_some_iff.mp hi).1
  rw [hlenO] at hil
  obtain ⟨rhss, ho, -⟩ := hallO i S.cvGs[i] rd.recCls[i]
    (List.getElem?_eq_getElem (by omega)) (List.getElem?_eq_getElem (by omega))
  rw [hi] at ho
  obtain rfl := Option.some.inj ho
  change x ∈ (S.Ms.getD rd.recCls[i] default).ctors at hx
  generalize rd.recCls[i] = c at hx
  rw [List.getD_eq_getElem?_getD] at hx
  cases hMc : S.Ms[c]? with
  | none => rw [hMc] at hx; exact nomatch hx
  | some M =>
    rw [hMc] at hx
    have hc : c < Ms₀.length := by
      rw [← hlenN]; exact (List.getElem?_eq_some_iff.mp hMc).1
    obtain ⟨nfs, hM, -⟩ := hallN c Ms₀[c] (List.getElem?_eq_getElem hc)
    rw [hMc] at hM
    obtain rfl := Option.some.inj hM
    obtain ⟨M', hM', ⟨R⟩⟩ := hallK c C.keys[c] (List.getElem?_eq_getElem (by omega))
    rw [List.getElem?_eq_getElem hc] at hM'
    obtain rfl := Option.some.inj hM'
    exact classMajor_ctors R x hx

/-- **An inductive block's record keeps the environment read-scoped.** -/
theorem blockRun_scoped {F : Nat} {env env₂ : Env} {block : List ConstantInfo} {p₀ : BlockShape}
    (hS : Scoped env) (hwf : EnvWF env₂) (h : BlockRun F env block p₀ env₂) : Scoped env₂ := by
  obtain ⟨ms, -, hall, -, hR⟩ := h
  obtain ⟨-, -, -, isRec, env₁, p₁, sortsss, ctx, holes, rd, Ms₀, kinds, nfs, pos, st, isorts, out,
    Q, hInd, hCtors, hctx, hcls, -, -, -, -, hRec, -, hSR, hQ, -, henv₂⟩ := hR
  have hmem₁ : p₁.members = ms := checkBlockInds_members hInd
  obtain ⟨-, -, -, -, -, -, -, henv₁, -, -, -⟩ := checkBlockInds_shape hInd
  have hRec' : genRecCheck (fueledOps .verified F)
      (mkFEnv (consBlockCtors p₁.nP p₁.ctorGroups env₁)) p₁ (blockNestedBit p₁ kinds)
      ctx.params st.ctorNfs.toList rd Ms₀ block = .ok out := hRec
  obtain ⟨S⟩ := genRecCheck_run hRec'
  -- the three lists of new constants
  let FM : List ConstantInfo := ((ms.map (·.declared)).zipIdx 0).map fun x =>
    ConstantInfo.indInfo x.1 (blockCapsAt p₁ x.2 isRec)
  let CT : List ConstantInfo := p₁.ctorGroups.flatMap fun g =>
    g.2.map fun c => ConstantInfo.ctorInfo c.1 p₁.nP c.2 g.1
  let RI : List ConstantInfo := blockRecInfosTF p₁ 0 (streamRecs p₁.recs out)
  have hc₁ : env₁.consts = FM.reverse ++ env.consts := by
    rw [henv₁, consBlockInds_consts']
  have hc₂ : env₂.consts = (RI.reverse ++ CT.reverse ++ FM.reverse) ++ env.consts := by
    rw [henv₂]
    simp only [Env.pushDelta, List.reverse_nil, List.nil_append, consBlockRecsT_eq_infos,
      consBlockCtors_eq, hc₁, List.append_assoc]
    rfl
  have ht₂ : env₂.tables = Q.reverse ++ env.tables := by
    rw [henv₂]
    simp only [Env.pushDelta, consBlockRecsT_eq_infos, consBlockCtors_eq, henv₁,
      consBlockInds_consts']
  have hsub₁ : ∀ c ∈ env₁.consts, c ∈ env₂.consts := by
    intro c hc
    rw [hc₁] at hc
    rw [hc₂]
    rcases List.mem_append.mp hc with hc | hc <;> simp [hc]
  have hstored : ∀ c ∈ RI ++ CT ++ FM, (env₂.find? c.name).isSome = true := by
    intro c hc
    refine find?_isSome_of_mem ?_
    rw [hc₂]
    apply List.mem_append_left
    simp only [List.mem_append, List.mem_reverse] at hc ⊢
    exact hc
  -- the members' constructors and formers are stored
  have hctorS : ∀ ms' ∈ p₁.members, ∀ x ∈ ms'.ctors, (env₂.find? x.1.name).isSome = true := by
    intro ms' hms' x hx
    refine hstored (.ctorInfo x.1 p₁.nP x.2 ms'.cvT.name) ?_
    refine List.mem_append_left _ (List.mem_append_right _ ?_)
    refine List.mem_flatMap.mpr ⟨(ms'.cvT.name, ms'.ctors), ?_, List.mem_map_of_mem hx⟩
    exact List.mem_map_of_mem hms'
  have hformerS : ∀ m ∈ ms, (env₂.find? m.declared.name).isSome = true := by
    intro m hm
    obtain ⟨k, hk⟩ := mem_zipIdx_of_mem (i := 0) (List.mem_map_of_mem (f := (·.declared)) hm)
    exact hstored (.indInfo m.declared (blockCapsAt p₁ k isRec))
      (List.mem_append_right _ (List.mem_map_of_mem (f := fun x : ConstantVal × Nat =>
        ConstantInfo.indInfo x.1 (blockCapsAt p₁ x.2 isRec)) hk))
  -- the names off the pins
  have hchk := checkBlockInds_checked hInd
  refine hS.extend hwf (new := RI.reverse ++ CT.reverse ++ FM.reverse) (newQ := Q.reverse)
    hc₂ ht₂ (fun c hc => ?_) (fun t ht => ?_)
  · have hcm : c ∈ env₂.consts := by rw [hc₂]; exact List.mem_append_left _ hc
    simp only [List.mem_append, List.mem_reverse] at hc
    rcases hc with (hc | hc) | hc
    · -- a recursor: its rules fire at its class's constructors
      obtain ⟨t, htm, k, rfl⟩ := mem_blockRecInfosTF hc
      obtain ⟨g, hg, hname, -, hmaj⟩ := mem_streamRecs htm
      refine entryScoped_of hwf hcm (fun cv mI rP isK rules he r hr => ?_)
        (fun _ _ he => nomatch he) ?_
      · obtain ⟨-, -, -, -, rfl⟩ := ConstantInfo.recInfo.inj he
        obtain ⟨x, hx, hrx⟩ := generatedRules_ctor hr
        rw [hrx]
        rw [hmaj] at hx
        rcases genRecCheck_out_ctors hcls hRec' g hg x hx with ⟨ms', hms', hx'⟩ | hx'
        · exact hctorS ms' hms' x hx'
        · obtain ⟨c', hc', hn⟩ := find?_isSome_iff_mem.mp hx'
          exact find?_isSome_iff_mem.mpr ⟨c', hsub₁ c' hc', hn⟩
      · show ∀ d ∈ pinFootprint t.1.name, _
        obtain ⟨hlenC, hcv⟩ := genRecCheck_outCv hRec'
        obtain ⟨i, hi⟩ := List.getElem?_of_mem hg
        have hil : i < p₁.recs.length := by
          rw [← hlenC]; exact (List.getElem?_eq_some_iff.mp hi).1
        have hrc := List.getElem?_eq_getElem hil
        have he := hcv i _ g hrc hi
        obtain ⟨h1, h2⟩ := checkConstantValF_names
          (classStreamRecs_checked S.hcvRis _ (List.getElem_mem hil))
        rw [hname, he]
        exact footprint_of_nil h1 h2
    · -- a constructor
      obtain ⟨gr, hgr, hc⟩ := List.mem_flatMap.mp hc
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
      obtain ⟨ms', hms', rfl⟩ := List.mem_map.mp hgr
      refine entryScoped_of hwf hcm (fun _ _ _ _ _ he => nomatch he) (fun _ _ he => nomatch he) ?_
      show ∀ d ∈ pinFootprint x.1.name, _
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hms'
      obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
      obtain ⟨-, hrun⟩ := hCtors
      obtain ⟨sortss, -, -, -, hcs⟩ := hrun i ms' hi
      obtain ⟨-, sorts, -, ⟨-, hccv⟩, -⟩ := hcs j x x hj hj
      obtain ⟨h1, h2⟩ := checkConstantVal_names hccv
      exact footprint_of_nil h1 h2
    · -- a former: its block members are the formers
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hc
      have hy' := fst_mem_of_mem_zipIdx hy
      obtain ⟨m, hm, hmy⟩ := List.mem_map.mp hy'
      refine entryScoped_of hwf hcm (fun _ _ _ _ _ he => nomatch he)
        (fun cv caps he n hn => ?_) ?_
      · obtain ⟨-, rfl⟩ := ConstantInfo.indInfo.inj he
        rw [blockCapsAt_all, BlockShape.memberNames, hmem₁] at hn
        obtain ⟨m', hm', rfl⟩ := List.mem_map.mp hn
        rw [(hall m' hm').name]
        exact hformerS m' hm'
      · show ∀ d ∈ pinFootprint y.1.name, _
        obtain ⟨h1, h2⟩ := checkConstantVal_names (hchk m hm)
        rw [← hmy, ← (hall m hm).name]
        exact footprint_of_nil h1 h2
  · -- a table: its constructor is its member's
    obtain ⟨ms', hms', x, hx, he⟩ := blockTables_ctor p₁ p₁.projMembers Q hQ t (List.mem_reverse.mp ht)
    have hms' := mem_projMembers hms'
    rw [he]
    exact hctorS ms' hms' x hx

/-- **An accepted declaration keeps the environment read-scoped.** -/
theorem checkDecl_scoped {F : Nat} {env env₂ : Env} {d : Declaration} (henv : EnvWF env)
    (hS : Scoped env) (h : checkDecl .verified (fueledOps .verified F) pins env d = .ok env₂) :
    Scoped env₂ := by
  have hwf := checkDecl_envWF henv h
  obtain ⟨-, hR⟩ := checkDeclRun_ofEnvFactsK h
  obtain ⟨hk, -⟩ := checkDecl_inv h
  cases d with
  | defnDecl cv value hint => exact declDefn_scoped hS hwf (checkDeclKind_defn_ccv hk) hR
  | thmDecl cv value => exact declThm_scoped hS hwf (checkDeclKind_thm_ccv hk) hR
  | opaqueDecl cv value => exact declOpaque_scoped hS hwf hR
  | axiomDecl cv => exact declAxiom_scoped hS hwf (checkDeclKind_axiom_ccv hk) hR
  | quotDecl k cv => exact declQuotRun_scoped hS hwf hR
  | indDecl block nP =>
    change DeclIndRunDispatchK F env block nP env₂ at hR
    unfold DeclIndRunDispatchK at hR
    split at hR
    · exact blockRun_scoped hS hwf hR
    · exact hR.elim

/-! ## The fold -/

/-- **Every environment an accepting run reaches is read-scoped**, from a read-scoped,
well-formed start: each record's cached check is a pure `checkDecl` run (`checkDeclStepC_run`), or
the justification route's axiom, whose statement takes no pinned name (`justifiable`). -/
theorem declsRun_scoped {maxNatSize : Nat} {J : Option Solution} {ds : List Declaration}
    {p q : Nat × FEnv} (hrun : DeclsRun .verified pins maxNatSize J ds p q) :
    p.2 = mkFEnv p.2.env → EnvWF p.2.env → Scoped p.2.env → Scoped q.2.env := by
  induction hrun with
  | nil p => exact fun _ _ hS => hS
  | @cons pd ds p p₁ q hstep rest ih =>
    intro hfe hw hS
    have hw₁ := declsRun_envWF (DeclsRun.cons hstep (DeclsRun.nil p₁)) hfe hw
    obtain ⟨fe₁, s₁, rfl, hstepC⟩ := declStep_ok hstep
    rw [hfe] at hstepC
    have hown : ∀ {s' : CState},
        checkDeclStepC .verified pins (mkFEnv p.2.env) pd { maxNatSize := maxNatSize }
          = .ok (fe₁, s') → Scoped q.2.env := by
      intro s' hC
      obtain ⟨-, hfe₁, F, hF⟩ := checkDeclStepC_run hw (CSOKF.fresh _) hC
      exact ih hfe₁ hw₁ (checkDecl_scoped hw hS hF)
    cases hj : justifiable pd with
    | none =>
      rw [checkRecordC_own .verified J _ hj] at hstepC
      exact hown hstepC
    | some cv =>
      cases J with
      | none => exact hown hstepC
      | some J =>
        -- the justification route: the statement pushed as an axiom
        obtain ⟨-, hfe₁, -, -, -⟩ := checkRecordC_justified_run hw hj (CSOKF.fresh _) hstepC
        subst hfe₁
        rw [mkFEnv_env] at hw₁
        refine ih (by rw [mkFEnv_env]) hw₁ ?_
        obtain ⟨hop, hred⟩ := justifiable_names hj
        exact hS.cons_of hw₁ (fun _ _ _ _ _ he => nomatch he) (fun _ _ he => nomatch he)
          (footprint_of_nil hop hred)

end ConLeche.Cached
