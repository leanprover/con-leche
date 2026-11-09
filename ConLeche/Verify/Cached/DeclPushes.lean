module

public import ConLeche.Cached.Decls
import ConLeche.Verify.Cached.BlockOverlay
import ConLeche.Verify.Cached.WalkersC

public section

/-!
# Every accepting step pushes what its declaration says

The fold's step, at every mode, returns the environment with the declaration's constants and tables
pushed (`checkDeclC_pushes`, `declConstants`, `declTables`), whatever the checks in between did.  So
the environment an accepted stream ends in is a function of the stream (`checkDecls_env`), and two
modes that both accept it end in the same one (`checkDecls_agree`).

Nothing here reasons about the cores: the proofs read only what an action returns (`Yields`).  The
freshness facts the fresh-chain proof uses (`ConLeche/Verify/Cached/PushChain.lean`) are of the same
kind and live here too.
-/

namespace ConLeche.Cached

open ConLeche

variable {pins : List NatOpPinSet}

/-! ## The kit: final-value reasoning for `CheckCM`

`CheckCM = StateT CState (Except CheckError)`.  The floor reads only
the *returned* environment, never the state, so the whole monadic
discipline it needs is: "`P` holds of every value this action can
return".  The bind rule then carries **no** hypothesis on the bound
action — which is what makes the long `do` blocks of the checks
collapse to their final `pure`. -/

/-- `P` holds of every value the action can return. -/
@[expose] def Yields {α : Type} (m : CheckCM α) (P : α → Prop) : Prop :=
  ∀ s a s', m s = .ok (a, s') → P a

theorem Yields.mono {α : Type} {m : CheckCM α} {P Q : α → Prop}
    (h : Yields m P) (hPQ : ∀ a, P a → Q a) : Yields m Q :=
  fun s a s' hr => hPQ a (h s a s' hr)

theorem Yields.pure {α : Type} {a : α} {P : α → Prop} (h : P a) :
    Yields (Pure.pure (f := CheckCM) a) P := by
  intro s b s' hr
  simp only [Pure.pure, StateT.pure, Except.pure] at hr
  cases hr; exact h

/-- A fact that does not read the value holds of every value. -/
theorem Yields.const {α : Type} {m : CheckCM α} {Q : Prop} (h : Q) : Yields m (fun _ => Q) :=
  fun _ _ _ _ => h

theorem Yields.ofThrow {α : Type} {e : CheckError} {P : α → Prop} :
    Yields (throw e : CheckCM α) P := by
  intro s a s' hr; cases hr

/-- The bind rule that carries **no** hypothesis on the bound action:
the property is about the returned value only, so the long guard
chains of the drivers collapse to their final `pure`. -/
theorem Yields.bind {α β : Type} {m : CheckCM α} {f : α → CheckCM β}
    {P : β → Prop} (h : ∀ a, Yields (f a) P) : Yields (m >>= f) P := by
  intro s b s' hr
  have hs : (m >>= f) s = (m s).bind (fun v => f v.1 v.2) := rfl
  cases hm : m s with
  | error e => rw [hs, hm] at hr; cases hr
  | ok v =>
    rw [hs, hm] at hr
    exact h v.1 v.2 b s' hr

/-- The bind rule that *uses* the bound action's own rule. -/
theorem Yields.bind' {α β : Type} {m : CheckCM α} {f : α → CheckCM β}
    {Q : α → Prop} {P : β → Prop} (hm : Yields m Q)
    (h : ∀ a, Q a → Yields (f a) P) : Yields (m >>= f) P := by
  intro s b s' hr
  have hs : (m >>= f) s = (m s).bind (fun v => f v.1 v.2) := rfl
  cases hm' : m s with
  | error e => rw [hs, hm'] at hr; cases hr
  | ok v =>
    rw [hs, hm'] at hr
    exact h v.1 (hm s v.1 v.2 hm') v.2 b s' hr

/-- Do-notation elaborates its guards through *join points*
(`have __do_jp := …`).  A `have` is a non-dependent `let`, which the clause walker's rules see
through by zeta at reducible transparency; so the walker does not try this rule (stated over that `let`,
its conclusion zeta-reduces to `?f ?v`), and only the explicit top-level steps name it. -/
theorem Yields.letFun {α β : Type} {v : β} {f : β → CheckCM α}
    {P : α → Prop} (h : Yields (f v) P) : Yields (have x := v; f x) P := h

/-- A guard's failure branch, closed without descending into the join
point it calls (which is what keeps the walk linear). -/
theorem Yields.ofThrowBind {α β : Type} {e : CheckError} {f : α → CheckCM β}
    {P : β → Prop} : Yields ((throw e : CheckCM α) >>= f) P := by
  intro s b s' hr; cases hr

theorem Yields.ofDecCases {α : Type} {c : Prop} {d : Decidable c}
    {a : ¬c → CheckCM α} {b : c → CheckCM α} {P : α → Prop}
    (ha : ∀ h, Yields (a h) P) (hb : ∀ h, Yields (b h) P) :
    Yields (@dite _ c d b a) P := by
  by_cases h : c
  · rw [dite_eq_left h]; exact hb h
  · rw [dite_eq_right h]; exact ha h

/-- The clause walker: step past join points and guards to the `pure`
leaves of a driver clause.

**Every `apply` runs `with_reducible`.**  At default transparency the
rules unify *vacuously* — `Bind.bind ?m ?f` and
`pure ?a` all unfold far enough to match an arbitrary action, which
makes the walk loop instead of descending.  At reducible transparency
each rule matches exactly its own head, so the walk is deterministic
and linear in the clause. -/
syntax "yields_step" : tactic
macro_rules
  | `(tactic| yields_step) => `(tactic|
      first
        | with_reducible exact Yields.ofThrowBind
        | ((with_reducible apply Yields.bind); intro)
        | with_reducible exact Yields.ofThrow
        | ((with_reducible apply Yields.ofDecCases) <;> intro)
        | split
        | dsimp only [])

syntax "yields" : tactic
macro_rules
  | `(tactic| yields) =>
      `(tactic| all_goals (first | (yields_step; yields) | skip))

/-- One join-point step (`with_reducible`, as above). -/
syntax "ylet" : tactic
macro_rules
  | `(tactic| ylet) => `(tactic| with_reducible apply Yields.letFun)

/-- One uninformative bind step (`with_reducible`, as above). -/
syntax "ybind" : tactic
macro_rules
  | `(tactic| ybind) => `(tactic| (with_reducible apply Yields.bind); intro)

/-- The fold rule, with an abstraction `R` of the accumulator: if each
step takes `R b c` to `R b' (g c a)`, the fold takes it to
`R b' (l.foldl g c)`.  This is the shape both drivers' folds have —
the *specification* accumulator `c` is a pure function of the stream,
which is exactly how the two drivers are compared. -/
theorem Yields.foldlM_rel {α β γ : Type} {R : β → γ → Prop}
    {f : β → α → CheckCM β} {g : γ → α → γ}
    (hf : ∀ b a c, R b c → Yields (f b a) (fun b' => R b' (g c a))) :
    ∀ (l : List α) (b : β) (c : γ), R b c →
      Yields (l.foldlM f b) (fun b' => R b' (l.foldl g c))
  | [], b, c, h => by
      simp only [List.foldlM_nil, List.foldl_nil]
      exact Yields.pure h
  | a :: l, b, c, h => by
      simp only [List.foldlM_cons, List.foldl_cons]
      exact Yields.bind' (hf b a c h) fun b' hb' =>
        Yields.foldlM_rel hf l b' (g c a) hb'

/-! ## The install stages -/

/-- The record a definition's value check returns is the definition
itself, at the checked constant and hint. -/
theorem checkDefnValCI_shape (mode : CheckMode) (fe : FEnv) (cv : ConstantVal)
    (value : Expr) (hint : ReducibilityHint) :
    Yields (checkDefnValCI mode fe cv value hint)
      (fun ci => ci = .defnInfo cv value hint) := by
  unfold checkDefnValCI
  yields
  all_goals exact Yields.pure rfl

/-- The record a theorem's value check returns is its statement. -/
theorem checkThmValCI_shape (mode : CheckMode) (fe : FEnv) (cv : ConstantVal)
    (value : Expr) :
    Yields (checkThmValCI mode fe cv value) (fun ci => ci = .thmInfo cv) := by
  unfold checkThmValCI
  yields
  all_goals exact Yields.pure rfl

/-- The record an opaque's value check returns is the axiom at the
checked constant. -/
theorem checkOpaqueValCI_shape (mode : CheckMode) (fe : FEnv) (cv : ConstantVal)
    (value : Expr) :
    Yields (checkOpaqueValCI mode fe cv value) (fun ci => ci = .axiomInfo cv) := by
  unfold checkOpaqueValCI
  yields
  all_goals exact Yields.pure rfl

/-! ## The per-member stages' skeletons

Every stage's install decision is the block's own or a freshness
check; the stored constants' names are the block's (`checkConstantValF`
keeps the name). -/

/-! ## The constructor list's skeleton

The stored constructors' names and field counts are the block's
(`checkConstantValF` keeps the name, the stage keeps the count). -/

/-- The former's telescope stage keeps the former. -/
theorem checkSumTele_name (n : Nat) (cvTa₀ : ConstantVal) :
    Yields (checkSumTele n cvTa₀) (fun r => r.1.name = cvTa₀.name) := by
  unfold checkSumTele
  split
  · exact Yields.pure rfl
  · exact Yields.ofThrow

/-! ### Freshness of the stored names -/

theorem checkConstantValF_fresh (ops : CheckerOps CheckCM) (fe : FEnv)
    (cv : ConstantVal) :
    Yields (checkConstantValF ops fe cv)
      (fun _ => fe.find? cv.name = none) := by
  unfold checkConstantValF
  yields
  all_goals exact Yields.pure (Option.not_isSome_iff_eq_none.mp (by assumption))

theorem checkSumCtorF_fresh (ops : CheckerOps CheckCM) (fe₀ fe : FEnv)
    (T : Name) (lps : List Name) (nP nIdx : Nat) (rs : Level) (isProp large : Bool)
    (cvC : ConstantVal) (nF : Nat) (cvTa : ConstantVal) :
    Yields (checkSumCtorF ops fe₀ fe T lps nP nIdx rs isProp large cvC nF cvTa)
      (fun _ => fe.find? cvC.name = none) := by
  unfold checkSumCtorF
  refine Yields.bind' (checkConstantValF_fresh ops fe cvC) fun _ hfr => ?_
  exact Yields.const hfr

theorem checkSumCtorsF_fresh (ops : CheckerOps CheckCM) (fe₀ fe : FEnv)
    (T : Name) (lps : List Name) (nP nIdx : Nat) (rs : Level) (isProp large : Bool)
    (cvTa : ConstantVal) :
    ∀ (cs : List (ConstantVal × Nat)),
      Yields (checkSumCtorsF ops fe₀ fe T lps nP nIdx rs isProp large cvTa cs)
        (fun _ => ∀ c ∈ cs, fe.find? c.1.name = none)
  | [] => Yields.pure fun _ hc => nomatch hc
  | c :: cs => by
    unfold checkSumCtorsF
    refine Yields.bind' (checkSumCtorF_fresh ops fe₀ fe T lps nP nIdx rs isProp
      large c.1 c.2 cvTa) fun _ hfr => ?_
    refine (checkSumCtorsF_fresh ops fe₀ fe T lps nP nIdx rs isProp large cvTa cs).mono ?_
    intro _ hfrs d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hfr
    · exact hfrs d hd

/-! ### The block install at k members

The k-ary install's skeleton is `blockSkels` of the RECOGNISED record,
read off the stages' names and counts: the formers keep their names,
the constructors theirs and their field counts, every recursor its
record's name with its TARGET member's constructors as its rules, and
a structure-like member its table.  The recursor stage is read at its
CHECK. -/

theorem Yields.and {α : Type} {m : CheckCM α} {P Q : α → Prop}
    (hP : Yields m P) (hQ : Yields m Q) : Yields m (fun a => P a ∧ Q a) :=
  fun s a s' hr => ⟨hP s a s' hr, hQ s a s' hr⟩

theorem checkBlockTeleF_fresh (ops : CheckerOps CheckCM) (fe : FEnv) (nP : Nat)
    (ms : MemberShape) :
    Yields (checkBlockTeleF ops fe nP ms)
      (fun r => r.1.name = ms.cvT.name ∧ fe.find? ms.cvT.name = none) := by
  unfold checkBlockTeleF
  refine Yields.bind' (checkConstantValF_fresh ops fe ms.cvT) fun _ hfr => ?_
  refine Yields.bind' (checkSumTele_name _ ms.cvT) fun r hn' => ?_
  obtain ⟨cvTa, s⟩ := r
  change cvTa.name = ms.cvT.name at hn'
  yields
  all_goals exact Yields.pure ⟨hn', hfr⟩

theorem checkBlockTelesF_fresh (ops : CheckerOps CheckCM) (fe : FEnv) (nP : Nat) :
    ∀ mss : List MemberShape,
      Yields (checkBlockTelesF ops fe nP mss)
        (fun rs => rs.map (·.1.name) = mss.map (·.cvT.name) ∧
          ∀ ms ∈ mss, fe.find? ms.cvT.name = none)
  | [] => Yields.pure ⟨rfl, fun _ h => nomatch h⟩
  | ms :: rest => by
    unfold checkBlockTelesF
    refine Yields.bind' (checkBlockTeleF_fresh ops fe nP ms) fun r hr => ?_
    refine Yields.bind' (checkBlockTelesF_fresh ops fe nP rest) fun rs hrs => ?_
    refine Yields.pure ⟨by simp [hr.1, hrs.1], ?_⟩
    intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hr.2
    · exact hrs.2 m hm

/-- The formers' stage: the record the shape completed (the sort read),
the environment the formers' conses build, the formers' names, and
their freshness at the block's own index. -/
theorem checkBlockIndsF_fresh (ops : CheckerOps CheckCM) (fe : FEnv) (p : BlockShape)
    (isRec : Bool) :
    Yields (checkBlockIndsF ops fe p isRec)
      (fun r => (∃ s, r.2 = p.withSort s) ∧
        r.1 = consBlockIndsF r.2 isRec (p.members.map (·.declared)) 0 fe ∧
        ∀ ms ∈ p.members, fe.find? ms.cvT.name = none) := by
  unfold checkBlockIndsF
  split
  · exact Yields.ofThrow
  · next ms0 rest hm =>
    refine Yields.bind' (checkBlockTeleF_fresh ops fe p.nP ms0) fun r0 h0 => ?_
    obtain ⟨cvTa0, s0⟩ := r0
    refine Yields.bind' (checkBlockTelesF_fresh ops fe p.nP rest) fun cvs hcvs => ?_
    refine Yields.bind fun _ => ?_
    refine Yields.pure ⟨⟨s0, rfl⟩, rfl, ?_⟩
    · rw [hm]
      intro m hmm
      rcases List.mem_cons.mp hmm with rfl | hmm
      · exact h0.2
      · exact hcvs.2 m hmm

/-- `consSumCtorsF` is a left fold: over an append it is the two conses
in turn. -/
theorem consSumCtorsF_append (nP : Nat) :
    ∀ (a b : List (ConstantVal × Nat)) (fe : FEnv),
      consSumCtorsF nP (a ++ b) fe = consSumCtorsF nP b (consSumCtorsF nP a fe)
  | [], _, _ => rfl
  | _ :: a, b, _ => consSumCtorsF_append nP a b _

/-- The members' constructors, consed member by member, are the
whole block's constructors consed in block order. -/
theorem consBlockCtorsF_flatten (nP : Nat) :
    ∀ (memberCtors : List (List (ConstantVal × Nat))) (fe : FEnv),
      consBlockCtorsF nP memberCtors fe = consSumCtorsF nP memberCtors.flatten fe
  | [], _ => rfl
  | ctorList :: rest, fe => by
    rw [consBlockCtorsF, List.flatten_cons, consSumCtorsF_append]
    exact consBlockCtorsF_flatten nP rest _

/-- The constructors' stage: every declared name fresh at the environment the stage runs at. -/
theorem checkBlockCtorsF_fresh (ops : CheckerOps CheckCM) (fe₀ fe : FEnv) (p : BlockShape) :
    ∀ l : List MemberShape,
      Yields (checkBlockCtorsF ops fe₀ fe p l)
        (fun _ => ∀ ms ∈ l, ∀ c ∈ ms.ctors, fe.find? c.1.name = none)
  | [] => Yields.pure fun _ h => nomatch h
  | ms :: rest => by
    unfold checkBlockCtorsF
    refine Yields.bind' (checkSumCtorsF_fresh ops fe₀ fe ms.cvT.name p.lps p.nP ms.nIdx p.resSort
      p.isProp p.large ms.cvT ms.ctors) fun _ hfr => ?_
    refine (checkBlockCtorsF_fresh ops fe₀ fe p rest).mono ?_
    intro _ hfr' ms' hms' c hc
    rcases List.mem_cons.mp hms' with rfl | hms'
    · exact hfr c hc
    · exact hfr' ms' hms' c hc

theorem Yields.unwrapOr {α : Type} {o : Option α} {e : CheckError} :
    Yields (unwrapOr o e : CheckCM α) (fun a => o = some a) := by
  cases o with
  | none => exact Yields.ofThrow
  | some a => exact Yields.pure rfl

/-! ### The generated recursor stage at the skeleton level

The recursor stage is `genRecCheck` (`ConLeche/Kernel/Inductives/GenRec.lean`). -/

/-- A generated constant checked: fresh at the stage's index. -/
theorem classConstOk_fresh (ops : CheckerOps CheckCM) (fe : FEnv) (cv : ConstantVal) :
    Yields (classConstOk ops fe cv)
      (fun _ => fe.find? cv.name = none) := by
  unfold classConstOk
  yields
  all_goals exact Yields.pure (Option.not_isSome_iff_eq_none.mp (by assumption))

/-- One recursor's generated type: stored under the record's name, fresh
at the stage's index. -/
theorem classRecTyOk_name (ops : CheckerOps CheckCM) (fe : FEnv) (g : ClassGen) (k : Nat)
    (rc : RecShape) (cvRi : ConstantVal) (c : Nat) :
    Yields (classRecTyOk ops fe g k rc cvRi c)
      (fun cvG => cvG.name = rc.cvR.name ∧ fe.find? rc.cvR.name = none) := by
  unfold classRecTyOk
  dsimp only
  split
  case isFalse => exact Yields.ofThrowBind
  split
  case isFalse => exact Yields.ofThrowBind
  refine Yields.bind fun gty => ?_
  refine Yields.bind' (Q := fun _ => fe.find? rc.cvR.name = none) ?_ fun _ hcv =>
    Yields.pure ⟨rfl, hcv⟩
  refine Yields.bind' (classConstOk_fresh ops fe _) fun _ hcv => ?_
  yields
  all_goals first | exact Yields.ofThrow | exact Yields.pure hcv

/-- Every recursor's generated type, against the records: one per
record, in order, under its name; the classes cover the records. -/
theorem classRecTysOk_names (ops : CheckerOps CheckCM) (fe : FEnv) (g : ClassGen) (k : Nat) :
    ∀ (recs : List RecShape) (cvs : List ConstantVal) (cs : List Nat),
      Yields (classRecTysOk ops fe g k recs cvs cs)
        (fun xs => xs.length = recs.length ∧ recs.length ≤ cs.length ∧
          ∀ (j : Nat) (rc : RecShape), recs[j]? = some rc →
            ∃ x, xs[j]? = some x ∧ x.name = rc.cvR.name ∧ fe.find? rc.cvR.name = none)
  | [], _, _ => by
    unfold classRecTysOk
    exact Yields.pure ⟨rfl, Nat.zero_le _, fun _ _ h => nomatch h⟩
  | _ :: _, [], _ => by unfold classRecTysOk; exact Yields.ofThrow
  | _ :: _, _ :: _, [] => by unfold classRecTysOk; exact Yields.ofThrow
  | rc :: rcs, cvRi :: cvs, c :: cs => by
    unfold classRecTysOk
    refine Yields.bind' (classRecTyOk_name ops fe g k rc cvRi c) fun x hx => ?_
    refine Yields.bind' (classRecTysOk_names ops fe g k rcs cvs cs) fun xs hxs => ?_
    refine Yields.pure ⟨by simp [hxs.1], by simp [hxs.2.1], fun j rc' hj => ?_⟩
    cases j with
    | zero =>
      obtain rfl : rc = rc' := by simpa using hj
      exact ⟨x, rfl, hx⟩
    | succ j => simpa using hxs.2.2 j rc' (by simpa using hj)

/-- Every recursor's generated rules: the generated constants kept, in
order. -/
theorem classRecsRulesOk_fst (ops : CheckerOps CheckCM) (w : StructWalkers) (feT feR : FEnv)
    (g : ClassGen) (recOf : Nat → Option Name) :
    ∀ (cvGs : List ConstantVal) (cs : List Nat), cvGs.length ≤ cs.length →
      Yields (classRecsRulesOk ops w feT feR g recOf cvGs cs)
        (fun out => out.map (·.1) = cvGs)
  | [], _, _ => by unfold classRecsRulesOk; exact Yields.pure rfl
  | _ :: _, [], h => by simp at h
  | cvG :: cvs, c :: cs, h => by
    unfold classRecsRulesOk
    refine Yields.bind fun _ => ?_
    refine Yields.bind' (classRecsRulesOk_fst ops w feT feR g recOf cvs cs
      (by simpa using h)) fun xs hxs => ?_
    exact Yields.pure (by simp [hxs])

/-- **The generated stage at the skeleton level**: one stored recursor
per record, in order, under the record's name (fresh at the stage's
index), the family's names distinct. -/
theorem genRecCheck_names (so : ShadowOps CheckCM) (fe : FEnv)
    (p : BlockShape) (nestedBit : Bool) (params : List Expr) (tbl : List NestCtorNf)
    (rd : ClassRead) (Ms₀ : List TargetMajor)
    (block : List ConstantInfo) :
    Yields (genRecCheck so fe p nestedBit params tbl rd Ms₀ block)
      (fun out => (p.recs.map (·.cvR.name)).Nodup ∧ out.length = p.recs.length ∧
        ∀ (j : Nat) (rc : RecShape), p.recs[j]? = some rc →
          ∃ o, out[j]? = some o ∧ o.1.name = rc.cvR.name ∧ fe.find? rc.cvR.name = none) := by
  unfold genRecCheck
  refine Yields.bind' (Q := fun _ => (p.recs.map (·.cvR.name)).Nodup) ?_ fun _ hnd => ?_
  · unfold targetRecPins
    dsimp only
    by_cases h1 : blockRecLpsOk p = true
    case neg => rw [ite_eq_right h1]; exact Yields.ofThrow
    rw [ite_eq_left h1]
    by_cases h2 : blockRecNamesUnreserved p = true
    case neg => rw [ite_eq_right h2]; exact Yields.ofThrow
    rw [ite_eq_left h2]
    split
    case isFalse => exact Yields.ofThrow
    split
    case isFalse => exact Yields.ofThrow
    by_cases h5 : (p.recs.map (·.cvR.name)).Nodup
    case neg => rw [ite_eq_right h5]; exact Yields.ofThrow
    rw [ite_eq_left h5]
    split
    · split
      · exact Yields.pure h5
      · exact Yields.ofThrow
    · exact Yields.ofThrow
  refine Yields.bind fun cvRis => ?_
  by_cases h2 : 0 < p.k
  case neg => simp only [h2, ite_false]; exact Yields.ofThrowBind
  simp only [h2, ite_true]
  by_cases h3 : (p.large && !blockLargeElimAllowed p (nestedBit || Ms₀.any fun x =>
      x.member.isNone)) = true
  case pos => simp only [h3, ite_true]; exact Yields.ofThrowBind
  simp only [h3]
  refine Yields.bind fun Ms => ?_
  refine Yields.bind fun ctors => ?_
  split
  case isFalse => exact Yields.ofThrowBind
  refine Yields.bind fun formerTysC => ?_
  refine Yields.bind fun pre => ?_
  refine Yields.bind' (classRecTysOk_names _ fe _ p.k p.recs cvRis _) fun cvGs hG => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.bind' (classRecsRulesOk_fst _ _ fe _ _ _ cvGs _ (by omega))
    fun out hout => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.pure ?_
  have hlen : out.length = cvGs.length := by simpa using congrArg List.length hout
  refine ⟨hnd, by rw [hlen, hG.1], fun j rc hj => ?_⟩
  obtain ⟨x, hx, hname, hfr⟩ := hG.2.2 j rc hj
  have hj' : j < out.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.mp hx).1
  refine ⟨out[j], List.getElem?_eq_getElem hj', ?_, hfr⟩
  have := congrArg (·[j]?) hout
  simp only [List.getElem?_map, List.getElem?_eq_getElem hj', hx, Option.map_some,
    Option.some.injEq] at this
  rw [this]; exact hname

/-- Two members alike but for the former their check reads. -/
@[expose] def SameMember (a b : MemberShape) : Prop :=
  b.cvT.name = a.cvT.name ∧ b.declared = a.declared ∧ b.nIdx = a.nIdx ∧ b.ctors = a.ctors

/-- Two lists of members alike but for the formers their check reads. -/
inductive SameMembers : List MemberShape → List MemberShape → Prop where
  | nil : SameMembers [] []
  | cons {a b : MemberShape} {as bs : List MemberShape} :
      SameMember a b → SameMembers as bs → SameMembers (a :: as) (b :: bs)

/-- A reduced member is the member at another telescope. -/
theorem reduceMemberS_same (mode : CheckMode) (fe : FEnv) (ms : MemberShape) (nP : Nat) :
    Yields (reduceMemberS mode fe ms nP) (SameMember ms) := by
  unfold reduceMemberS
  split
  · split
    · exact Yields.ofThrow
    refine Yields.bind fun _ => ?_
    refine Yields.bind' (Q := fun cvR => cvR.name = ms.cvT.name) ?_ fun cvR hc => ?_
    · unfold reducedFormerC
      refine Yields.bind fun _ => ?_
      exact Yields.pure rfl
    · refine Yields.bind fun _ => ?_
      split <;> first | exact Yields.ofThrow | exact Yields.pure ⟨hc, rfl, rfl, rfl⟩
  · exact Yields.pure ⟨rfl, rfl, rfl, rfl⟩

/-- The reduced members are the members at other telescopes. -/
theorem reduceMembersS_same (mode : CheckMode) (fe : FEnv) (nP : Nat) :
    ∀ l : List MemberShape, Yields (reduceMembersS mode fe nP l) (SameMembers l)
  | [] => Yields.pure .nil
  | ms :: rest => by
    unfold reduceMembersS
    refine Yields.bind fun _ => ?_
    refine Yields.bind' (reduceMemberS_same mode fe ms nP) fun ms' h₁ => ?_
    refine Yields.bind' (reduceMembersS_same mode fe nP rest) fun rest' h₂ => ?_
    exact Yields.pure (.cons h₁ h₂)

/-- What a reduction keeps of members the recogniser read at their declared formers. -/
theorem sameMembers_names : ∀ {a b : List MemberShape}, SameMembers a b →
    (∀ m ∈ a, m.declared = m.cvT) →
    b.map (·.cvT.name) = a.map (·.cvT.name) ∧ b.map (·.declared.name) = b.map (·.cvT.name) ∧
      b.map (·.ctors) = a.map (·.ctors)
  | _, _, .nil, _ => ⟨rfl, rfl, rfl⟩
  | _, _, .cons h₁ hs, hd => by
    obtain ⟨e₁, e₂, e₃⟩ := sameMembers_names hs (fun m hm => hd m (List.mem_cons_of_mem _ hm))
    have hy := hd _ List.mem_cons_self
    obtain ⟨n, d, -, c⟩ := h₁
    simp only [List.map_cons, e₁, e₂, e₃, n, d, c, hy, and_self]

/-! ### The tolerated-axiom branch

`sorryAx` is the one axiom the checker tolerates as a declaration, and
none of the pinned axiom guards can fire on it — so at `.axiomDecl` the
*push-or-not* decision is a function of the header name alone, in both
drivers. -/

theorem tolerated_not_std (fe : FEnv) (cv : ConstantVal)
    (ht : cv.name = sorryAxName) :
    stdAxiomOkF fe cv = false := by
  rw [stdAxiomOkF, ite_eq_right, ite_eq_right] <;> rw [ht] <;> decide

theorem tolerated_ne_trust {n : Name}
    (ht : n = sorryAxName) : n ≠ trustCompilerName := by
  rw [ht]; decide

theorem tolerated_ne_ofReduce {n : Name}
    (ht : n = sorryAxName) :
    ¬(n = ofReduceNatName ∨ n = ofReduceBoolName) := by
  rw [ht]; decide

theorem tolerated_ne_std {n : Name}
    (ht : n = sorryAxName) :
    ¬(n = propextName ∨ n = choiceName) := by
  rw [ht]; decide

/-! ### The cached certified declaration clause -/

/-! ## The floor

The fold checks every record by `checkDeclStepC` (`checkDecls`, `ConLeche/Cached/Decls.lean`), so
`declConstants` computes the environment at *every* mode.  Hence: whenever two modes both
**accept**, they hold the same constants, in the same order, with
the same skeletons — and in particular the same names and the same
count.

Scope, stated exactly: these are **accept-verdict** statements.  The
trusted config's purpose is to reject less, and the recorded
trusted-mode divergences are decline/accept divergences, untouched
here. -/

/-! ### The direct-parse entry points (#171) -/

/-! ## What a record pushes -/

theorem pushAll_env_consts :
    ∀ (L : List ConstantInfo) (fe : FEnv),
      (FEnv.pushAll L fe).env.consts = L.reverse ++ fe.env.consts
  | [], _ => rfl
  | ci :: L, fe => by
    show (FEnv.pushAll L (fe.push ci)).env.consts = _
    rw [pushAll_env_consts L (fe.push ci)]
    simp [FEnv.push]

theorem pushAll_env_tables :
    ∀ (L : List ConstantInfo) (fe : FEnv), (FEnv.pushAll L fe).env.tables = fe.env.tables
  | [], _ => rfl
  | ci :: L, fe => pushAll_env_tables L (fe.push ci)

theorem pushTables_env :
    ∀ (Q : List ProjTable) (fe : FEnv),
      (FEnv.pushTables Q fe).env = ⟨fe.env.consts, Q.reverse ++ fe.env.tables⟩
  | [], _ => rfl
  | t :: Q, fe => by
    show (FEnv.pushTables Q (fe.pushTable t)).env = _
    rw [pushTables_env Q (fe.pushTable t)]
    simp [FEnv.pushTable]

theorem pushDelta_env (L : List ConstantInfo) (Q : List ProjTable) (fe : FEnv) :
    (FEnv.pushDelta L Q fe).env = fe.env.pushDelta L Q := by
  unfold FEnv.pushDelta Env.pushDelta
  rw [pushTables_env, pushAll_env_consts, pushAll_env_tables]

/-- A canonical index stays canonical across a declaration's pushes. -/
theorem pushDelta_mkFEnv (L : List ConstantInfo) (Q : List ProjTable) (env : Env) :
    FEnv.pushDelta L Q (mkFEnv env) = mkFEnv (env.pushDelta L Q) := by
  have hA : ∀ (L : List ConstantInfo) (env : Env),
      FEnv.pushAll L (mkFEnv env) = mkFEnv ⟨L.reverse ++ env.consts, env.tables⟩ := by
    intro L
    induction L with
    | nil => intro env; rfl
    | cons ci L ih =>
      intro env
      show FEnv.pushAll L (mkFEnv ⟨ci :: env.consts, env.tables⟩) = _
      refine (ih _).trans ?_
      simp
  have hQ : ∀ (Q : List ProjTable) (env : Env),
      FEnv.pushTables Q (mkFEnv env) = mkFEnv ⟨env.consts, Q.reverse ++ env.tables⟩ := by
    intro Q
    induction Q with
    | nil => intro env; rfl
    | cons t Q ih =>
      intro env
      show FEnv.pushTables Q ((mkFEnv env).pushTable t) = _
      refine (ih ⟨env.consts, t :: env.tables⟩).trans ?_
      simp
  unfold FEnv.pushDelta Env.pushDelta
  rw [hA, hQ]

theorem checkQuotRecordC_pushes (fe : FEnv) (k : QuotKind) (cv : ConstantVal) :
    Yields (checkQuotRecordC fe k cv) (· = fe.push (quotAt k cv)) := by
  unfold checkQuotRecordC installBasisDeclF
  yields
  all_goals exact Yields.pure rfl

theorem checkBlockKS_pushes (mode : CheckMode) (fe : FEnv) (block : List ConstantInfo)
    (p : BlockShape) :
    Yields (checkBlockKS mode fe block p)
      (· = FEnv.pushDelta (blockConstants p) ((blockTables p p.members).getD []) fe) := by
  unfold checkBlockKS
  rw [blockTablesC_eq, blockConstantsC_eq]
  cases blockTables p p.members <;> simp only [unwrapOr, Option.getD, pure_bind] <;> yields
  all_goals first | exact Yields.pure rfl | exact Yields.ofThrow

/-- **A declaration's own checks push what it installs**, at every mode. -/
theorem checkDeclKindC_pushes (mode : CheckMode) (fe : FEnv) (pd : Declaration) :
    Yields (checkDeclKindC mode pins fe pd)
      (· = FEnv.pushDelta (declConstants pd) (declTables pd) fe) := by
  unfold checkDeclKindC
  cases pd with
  | defnDecl cv value hint =>
    simp only []
    ybind
    refine Yields.bind' (checkDefnValCI_shape mode fe cv value hint) fun ci hci => ?_
    subst hci
    yields
    all_goals exact Yields.pure rfl
  | thmDecl cv value =>
    simp only []
    ybind
    refine Yields.bind' (checkThmValCI_shape mode fe cv value) fun ci hci => ?_
    subst hci
    exact Yields.pure rfl
  | opaqueDecl cv value =>
    simp only []
    ybind
    refine Yields.bind' (checkOpaqueValCI_shape mode fe cv value) fun ci hci => ?_
    subst hci
    yields
    all_goals exact Yields.pure rfl
  | axiomDecl cv =>
    simp only []
    by_cases hqs : cv.name = quotSoundName
    · rw [ite_eq_left hqs]
      simp only [declConstants, ite_eq_left hqs, declTables]
      exact checkQuotRecordC_pushes fe .sound cv
    · rw [ite_eq_right hqs]
      simp only [declConstants, ite_eq_right hqs, declTables]
      ybind
      by_cases ht : cv.name = sorryAxName
      · rw [ite_eq_left ht,
          ite_eq_right (by rw [tolerated_not_std fe cv ht]; exact Bool.false_ne_true),
          ite_eq_right (tolerated_ne_trust ht), ite_eq_right (tolerated_ne_ofReduce ht),
          ite_eq_right (tolerated_ne_std ht), ite_eq_left ht]
        exact Yields.pure rfl
      · rw [ite_eq_right ht]
        yields
        all_goals first
          | exact Yields.pure rfl
          | exact absurd (by assumption) ht
  | quotDecl k cv => exact checkQuotRecordC_pushes fe k cv
  | indDecl block nP =>
    simp only [declConstants, declTables]
    unfold checkIndDeclC
    split
    · cases hbp : readBlock nP block with
      | error e => exact Yields.ofThrow
      | ok p => exact checkBlockKS_pushes mode fe block p
    · exact Yields.ofThrow

/-- **An accepting step pushes what the declaration installs**, at every mode. -/
theorem checkDeclC_pushes (mode : CheckMode) (fe : FEnv) (pd : Declaration) :
    Yields (checkDeclC mode pins fe pd) (· = FEnv.pushDelta (declConstants pd) (declTables pd) fe) := by
  unfold checkDeclC
  refine Yields.bind' (checkDeclKindC_pushes mode fe pd) fun fe₂ h => ?_
  subst h
  yields
  all_goals exact Yields.pure rfl

theorem checkDeclStepC_pushes (mode : CheckMode) (fe : FEnv) (pd : Declaration) :
    Yields (checkDeclStepC mode pins fe pd)
      (· = FEnv.pushDelta (declConstants pd) (declTables pd) fe) := by
  unfold checkDeclStepC
  ybind
  exact checkDeclC_pushes mode fe pd

/-! ## The environment of an accepted stream -/

/-- **The environment a stream denotes**: every record's constants and tables, in order. -/
@[expose] def streamEnv (ds : List Declaration) (env : Env := Env.empty) : Env :=
  ds.foldl (fun e pd => e.pushDelta (declConstants pd) (declTables pd)) env

theorem declsRun_env (mode : CheckMode) {ds : List Declaration}
    {p q : Nat × FEnv} (h : DeclsRun mode pins ds p q) :
    q.2.env = streamEnv ds p.2.env := by
  induction h with
  | nil p => rfl
  | @cons pd ds p p₁ q hstep rest ih =>
    obtain ⟨fe₁, s₁, rfl, hstepC⟩ := declStep_ok hstep
    have h₁ := checkDeclStepC_pushes (pins := pins) mode p.2 pd {} fe₁ s₁ hstepC
    rw [ih]
    simp only at h₁
    rw [h₁, pushDelta_env]
    rfl

/-- **An accepted stream's environment is a function of the stream**, at every mode. -/
theorem checkDecls_env {mode : CheckMode} {ds : Array Declaration} {env : Env}
    (h : checkDecls mode pins ds = .ok env) : env = streamEnv ds.toList := by
  obtain ⟨n, fe, r, rfl⟩ := checkDecls_run mode h
  exact declsRun_env mode r

/-- **Two modes that both accept a stream end in the same environment.** -/
theorem checkDecls_agree {μ₁ μ₂ : CheckMode} {ds : Array Declaration} {env₁ env₂ : Env}
    (h₁ : checkDecls μ₁ pins ds = .ok env₁) (h₂ : checkDecls μ₂ pins ds = .ok env₂) :
    env₁ = env₂ :=
  (checkDecls_env h₁).trans (checkDecls_env h₂).symm

end ConLeche.Cached
