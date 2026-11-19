module

public import ConLeche.Model.Sidecar.Rename
public import ConLeche.Model.Modular.Restrict
import ConLeche.Verify.Driver.Reach
import ConLeche.Model.Modular.Proofs
import ConLeche.Model.Modular.Valid

public section

/-!
# A shared record's step

A record of the input all of whose constants are shared with the sidecar (`Shared`) is given the
renamed sidecar model's leaves: the environment after it is a context (`CtxRead`) read from two
sources, the environment before it (its own names, read as themselves) and the renamed sidecar
(the record's names, read on the shared names stored so far).  `ctxModel` then gives the
environment after the record a covered model whose leaves are the earlier model's on the earlier
names and the sidecar model's on the record's.
-/

namespace ConLeche.Model.Sidecar

open ConLeche ConLeche.Cached ConLeche.Model ConLeche.Model.Modular ConLeche.Verify

universe w

/-! ## What a constant's laws read, among the justification's names -/

theorem constsAll_of_needs {p : Name → Prop} :
    ∀ {e : Expr}, (∀ n ∈ e.needs, p n) → Expr.constsAll p e
  | .bvar _, _ | .sort _, _ => trivial
  | .lit (.natVal _), h => by
    simp only [Expr.needs, litNeeds, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at h
    exact h
  | .lit (.strVal _), h => by
    simp only [Expr.needs, litNeeds, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at h
    exact h
  | .const n _, h => h n (by simp [Expr.needs])
  | .fvar _ ty, h => constsAll_of_needs (e := ty) (by simpa [Expr.needs] using h)
  | .app f a, h => by
    simp only [Expr.needs, List.mem_append] at h
    exact ⟨constsAll_of_needs fun n hn => h n (.inl hn), constsAll_of_needs fun n hn => h n (.inr hn)⟩
  | .lam ty b, h => by
    simp only [Expr.needs, List.mem_append] at h
    exact ⟨constsAll_of_needs fun n hn => h n (.inl hn), constsAll_of_needs fun n hn => h n (.inr hn)⟩
  | .forallE ty b, h => by
    simp only [Expr.needs, List.mem_append] at h
    exact ⟨constsAll_of_needs fun n hn => h n (.inl hn), constsAll_of_needs fun n hn => h n (.inr hn)⟩
  | .letE ty v b, h => by
    simp only [Expr.needs, List.mem_append] at h
    exact ⟨constsAll_of_needs fun n hn => h n (.inl (.inl hn)),
      constsAll_of_needs fun n hn => h n (.inl (.inr hn)),
      constsAll_of_needs fun n hn => h n (.inr hn)⟩
  | .proj s _ e, h => by
    simp only [Expr.needs, List.mem_cons] at h
    exact ⟨h s (.inl rfl), constsAll_of_needs fun n hn => h n (.inr hn)⟩

private theorem covers_all {acc : Array Name} {e : Expr} (h : Driver.Covers acc e) :
    Expr.constsAll (· ∈ acc) e :=
  constsAll_of_needs h

/-- **`entryNeeds` covers what a constant's laws read**, its table's included. -/
private theorem entryNeeds_spec (mates : Std.HashMap Name (Array Name)) (findT : Name → Option ProjTable)
    (ci : ConstantInfo) :
    Driver.ConstCovered (entryNeeds mates findT ci) ci ∧
    (∀ t, findT ci.toConstantVal.name = some t →
      Driver.TableCovered (entryNeeds mates findT ci) t) ∧
    (∀ cv caps, ci = .indInfo cv caps → ∀ x ∈ caps.ctors, x ∈ entryNeeds mates findT ci) ∧
    (∀ x ∈ mates.getD ci.toConstantVal.name #[], x ∈ entryNeeds mates findT ci) := by
  have h0 : Driver.NeedsInv (({} : Std.HashSet Expr), (#[] : Array Name)) := fun k hk => by
    simp at hk
  obtain ⟨⟨h1, -⟩, hc⟩ := NeedsSt.const_spec h0 ci
  -- the former's names
  obtain ⟨x2, hx2, hi2, hg2, hct⟩ : ∃ x2 : NeedsSt,
      x2 = (match ci with
        | .indInfo _ caps => (NeedsSt.const ({}, #[]) ci).names
            (caps.ctors ++ caps.all.map (fun m : Name => m.str "rec"))
        | _ => NeedsSt.const ({}, #[]) ci) ∧
      Driver.NeedsInv x2 ∧ (∀ n ∈ (NeedsSt.const ({}, #[]) ci).2, n ∈ x2.2) ∧
      (∀ cv caps, ci = .indInfo cv caps → ∀ x ∈ caps.ctors, x ∈ x2.2) := by
    cases ci with
    | indInfo cv caps =>
      obtain ⟨a, b, c⟩ := NeedsSt.names_spec h1 (caps.ctors ++ caps.all.map (fun m : Name => m.str "rec"))
      refine ⟨_, rfl, a, b, fun cv' caps' he x hx => ?_⟩
      cases he
      exact c x (List.mem_append_left _ hx)
    | _ => exact ⟨_, rfl, h1, fun _ h => h, fun _ _ he => nomatch he⟩
  obtain ⟨hi3, hg3, hm3⟩ := NeedsSt.names_spec hi2 (mates.getD ci.toConstantVal.name #[]).toList
  have hdef : entryNeeds mates findT ci =
      (match findT ci.toConstantVal.name with
        | some t => ((x2.names (mates.getD ci.toConstantVal.name #[]).toList).table t).2
        | none => (x2.names (mates.getD ci.toConstantVal.name #[]).toList).2) := by
    rw [hx2]; unfold entryNeeds; cases ci <;> rfl
  have hgrow : ∀ n ∈ (x2.names (mates.getD ci.toConstantVal.name #[]).toList).2,
      n ∈ entryNeeds mates findT ci := by
    intro n hn
    rw [hdef]
    split
    · next t _ => exact (NeedsSt.table_spec hi3 t).1.2 n hn
    · exact hn
  have hall : ∀ n ∈ (NeedsSt.const ({}, #[]) ci).2, n ∈ entryNeeds mates findT ci :=
    fun n hn => hgrow n (hg3 n (hg2 n hn))
  refine ⟨hc.mono hall, fun t ht => ?_, fun cv caps he x hx => hgrow x (hg3 x (hct cv caps he x hx)),
    fun x hx => hgrow x (hm3 x (Array.mem_toList_iff.mpr hx))⟩
  rw [hdef, ht]
  exact (NeedsSt.table_spec hi3 t).2

/-- **What a constant's laws read, it follows** (`EntryScopedP` over `entryNeeds`). -/
theorem entryScoped_needs (mates : Std.HashMap Name (Array Name)) {C : Env} {n : Name}
    {ci : ConstantInfo} (hn : ci.toConstantVal.name = n) :
    EntryScopedP (fun d => d ∈ entryNeeds mates C.findTable? ci) C n ci := by
  obtain ⟨⟨c1, c2, c3, c4, c5⟩, ht, -, -⟩ := entryNeeds_spec mates C.findTable? ci
  refine ⟨covers_all c1, fun cv v hh he => covers_all (c2 cv v hh he),
    fun cv mI rP isK rules he r hr => ?_, fun cv caps he => ⟨c4 cv caps he, fun t htt => ?_⟩,
    fun d hd => c5 d (hn ▸ hd)⟩
  · obtain ⟨r1, r2, r3⟩ := c3 cv mI rP isK rules he r hr
    exact ⟨covers_all r1, r2, fun lvls pins hf q hq => covers_all (r3 lvls pins hf q hq)⟩
  · obtain ⟨t1, t2, t3⟩ := ht t (hn ▸ htt)
    exact ⟨t2, fun b hb => covers_all (t3 b hb)⟩

/-- A former's constructors are among what it follows. -/
theorem entryNeeds_ctor (mates : Std.HashMap Name (Array Name)) (findT : Name → Option ProjTable)
    {cv : ConstantVal} {caps : IndCaps} {x : Name} (hx : x ∈ caps.ctors) :
    x ∈ entryNeeds mates findT (.indInfo cv caps) :=
  (entryNeeds_spec mates findT _).2.2.1 cv caps rfl x hx

/-- A constant's record mates are among what it follows. -/
theorem entryNeeds_mates (mates : Std.HashMap Name (Array Name)) (findT : Name → Option ProjTable)
    {ci : ConstantInfo} {x : Name} (hx : x ∈ mates.getD ci.toConstantVal.name #[]) :
    x ∈ entryNeeds mates findT ci :=
  (entryNeeds_spec mates findT ci).2.2.2 x hx

theorem tableBeqP_eq {a b : Option ProjTable} (h : tableBeqP a b = true) : a = b := by
  cases a <;> cases b <;> simp_all [tableBeqP]
  rename_i x y
  simp only [ProjTable.beqP, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  cases x; cases y; simp_all


theorem renS_of_not_stmt (Ef : Env) {c : ConstantInfo} (h : c.isStmtKind = false) :
    renS Ef c = c := by
  unfold renS
  split
  · rw [h]; rfl
  · rfl

/-! ## The step -/

variable {V : Type w} [SetTheory V]

/-- The two sources of a shared record's step: the environment before it (`true`) and the
renamed sidecar (`false`). -/
@[expose] def srcEnv (E S : Env) : Bool → Env
  | true => E
  | false => S

/-- The sources' models. -/
noncomputable def srcModel {E S : Env} (mp : EnvModelM V E) (mS : EnvModelM V S) :
    (b : Bool) → EnvModelM V (srcEnv E S b)
  | true => mp
  | false => mS

theorem srcModel_acval {E S : Env} (mp : EnvModelM V E) (mS : EnvModelM V S) (b : Bool) :
    (srcModel mp mS b).base2.acval = if b then mp.base2.acval else mS.base2.acval := by
  cases b <;> rfl

open Classical in
/-- **The shared part of the sidecar stored in `C`.** -/
noncomputable def sharedPart (Sh : Name → Prop) (C S : Env) : Env :=
  ⟨S.consts.filter fun c => decide (Sh c.toConstantVal.name) && (C.find? c.toConstantVal.name).isSome,
    []⟩

open Classical in
theorem sharedPart_find_eq (Sh : Name → Prop) (C S : Env) (d : Name) :
    (sharedPart Sh C S).find? d =
      if (decide (Sh d) && (C.find? d).isSome) = true then S.find? d else none := by
  classical
  exact find?_filter_name (l := S.consts) (t := S.tables)
    (q := fun x => decide (Sh x) && (C.find? x).isSome) (n := d)

theorem sharedPart_find_some {Sh : Name → Prop} {C S : Env} {d : Name} {ci : ConstantInfo}
    (h : (sharedPart Sh C S).find? d = some ci) :
    S.find? d = some ci ∧ Sh d ∧ (C.find? d).isSome = true := by
  classical
  rw [sharedPart_find_eq] at h
  split at h
  · next hc =>
    simp only [Bool.and_eq_true] at hc
    exact ⟨h, of_decide_eq_true hc.1, hc.2⟩
  · exact nomatch h

theorem sharedPart_find_of {Sh : Name → Prop} {C S : Env} {d : Name} (hs : Sh d)
    (hc : (C.find? d).isSome = true) : (sharedPart Sh C S).find? d = S.find? d := by
  classical
  have hq : (decide (Sh d) && (C.find? d).isSome) = true := by
    simp only [Bool.and_eq_true]; exact ⟨decide_eq_true hs, hc⟩
  rw [sharedPart_find_eq]
  simp only [hq, ↓reduceIte]

theorem srcModel_cover {E S : Env} {mp : EnvModelM V E} {mS : EnvModelM V S}
    (h1 : LfpCover mp []) (h2 : LfpCover mS []) : ∀ b, LfpCover (srcModel mp mS b) []
  | true => h1
  | false => h2

theorem srcEnv_nat {E S : Env} (h1 : NatFacts E) (h2 : NatFacts S) : ∀ b, NatFacts (srcEnv E S b)
  | true => h1
  | false => h2

/-- **A shared record's step** (see the module docstring). -/
theorem sharedStep {JS : Sidecar} {Ef envS E C : Env} (hJ : JS.idx = mkFEnv envS)
    (mp : EnvModelM V E) (hcov : LfpCover mp []) (hN : NatFacts E)
    (mS : EnvModelM V (renEnv Ef envS)) (hcovS : LfpCover mS []) (hNS : NatFacts (renEnv Ef envS))
    (hagree : ∀ x, (E.find? x).isSome = true → Shared JS Ef x →
      mp.base2.acval x = mS.base2.acval x)
    (hEC : ∀ x ci, E.find? x = some ci → C.find? x = some ci)
    (hECt : ∀ x, (E.find? x).isSome = true → C.findTable? x = E.findTable? x)
    (hCF : ∀ x ci, C.find? x = some ci → Ef.find? x = some ci)
    (hCFt : ∀ x, (C.find? x).isSome = true → Ef.findTable? x = C.findTable? x)
    (hnew : ∀ x, (C.find? x).isSome = true → (E.find? x).isSome = false → Shared JS Ef x)
    (hnd : NodupNames C)
    (hscE : ∀ n ci, E.find? n = some ci →
      EntryScopedP (fun d => (E.find? d).isSome = true) E n ci)
    (hscC : ∀ n ci, C.find? n = some ci →
      EntryScopedP (fun d => (C.find? d).isSome = true) C n ci)
    (hctE : ∀ d cv caps, E.find? d = some (.indInfo cv caps) → ∀ x ∈ caps.ctors,
      (E.find? x).isSome = true)
    (hctC : ∀ d cv caps, C.find? d = some (.indInfo cv caps) → ∀ x ∈ caps.ctors,
      (C.find? x).isSome = true)
    (htC : ∀ t ∈ C.tables, C.findTable? t.structName = some t ∧
      ∃ cv caps, C.find? t.structName = some (.indInfo cv caps))
    (htE : ∀ t ∈ E.tables, E.findTable? t.structName = some t ∧
      ∃ cv caps, E.find? t.structName = some (.indInfo cv caps))
    (htS : ∀ t ∈ envS.tables, envS.findTable? t.structName = some t ∧
      ∃ cv caps, envS.find? t.structName = some (.indInfo cv caps)) :
    ∃ mp' : EnvModelM V C, LfpCover mp' [] ∧ NatFacts C ∧
      (∀ x, (E.find? x).isSome = true → mp'.base2.acval x = mp.base2.acval x) ∧
      (∀ x, (C.find? x).isSome = true → (E.find? x).isSome = false →
        mp'.base2.acval x = mS.base2.acval x) := by
  classical
  -- the pieces
  let Sh := Shared JS Ef
  let S' := renEnv Ef envS
  let RS := sharedPart Sh C S'
  let old : Name → Bool := fun n => (E.find? n).isSome
  let E' : Name → Env := fun n => srcEnv E S' (old n)
  let R : Name → Env := fun n => srcEnv E RS (old n)
  let aC : Name → (Name → Nat) → Term.Term := fun d =>
    if old d then mp.base2.acval d else mS.base2.acval d
  have hEold : ∀ {n}, old n = true → E' n = E ∧ R n = E := fun h => by
    simp [E', R, h, srcEnv]
  have hEnew : ∀ {n}, old n = false → E' n = S' ∧ R n = RS := fun h => by
    simp [E', R, h, srcEnv]
  have hold : ∀ n, old n = true ∨ old n = false := fun n => by cases old n <;> simp
  -- a shared name's copies
  have hfS : ∀ x, Sh x → ∃ ci ci', Ef.find? x = some ci ∧ S'.find? x = some ci' ∧
      Refines ci ci' ∧ (reduceOpNames.contains x = true → ci' = ci) :=
    fun x hx => refines_ren hJ ((shared_closed JS Ef x hx).1)
  have hRS : ∀ d, (RS.find? d).isSome = true ↔ Sh d ∧ (C.find? d).isSome = true := by
    intro d
    constructor
    · intro h
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h
      exact (sharedPart_find_some hc).2
    · intro h
      rw [sharedPart_find_of h.1 h.2]
      obtain ⟨_, _, -, h2, -⟩ := hfS d h.1
      rw [h2]; rfl
  have hRSf : ∀ d ci, RS.find? d = some ci → S'.find? d = some ci ∧ (C.find? d).isSome = true :=
    fun d ci h => ⟨(sharedPart_find_some h).1, (sharedPart_find_some h).2.2⟩
  have hCsome : ∀ {x ci}, C.find? x = some ci → (C.find? x).isSome = true := fun h => by
    rw [h]; rfl
  have hEsome : ∀ {x ci}, E.find? x = some ci → (E.find? x).isSome = true := fun h => by
    rw [h]; rfl
  -- an old name's entry is the earlier one
  have hEfind : ∀ {x ci}, (E.find? x).isSome = true → C.find? x = some ci → E.find? x = some ci := by
    intro x ci hx hc
    obtain ⟨c, hc'⟩ := Option.isSome_iff_exists.mp hx
    rw [hEC x c hc'] at hc
    rw [hc', hc]
  -- reading a shared name stored in `C`
  have hscS : ∀ d ci, Sh d → C.find? d = some ci →
      EntryScopedP (fun y => (RS.find? y).isSome = true) C d ci := by
    intro d ci hsh hf
    have hfE : Ef.find? d = some ci := hCF d ci hf
    have hnm : ci.toConstantVal.name = d := by rw [cv_name_eq]; exact Env.find?_name hf
    have h1 := entryScoped_needs JS.mates (C := C) hnm
    have hcl := (shared_closed JS Ef d hsh).2 ci hfE
    have hT : C.findTable? ci.toConstantVal.name = Ef.findTable? ci.toConstantVal.name := by
      rw [hnm]; exact (hCFt d (hCsome hf)).symm
    rw [entryNeeds_congr hT] at h1
    have h2 := EntryScopedP.and (EntryScopedP.mono h1 fun y hy => hcl y hy) (hscC d ci hf)
    exact EntryScopedP.mono h2 fun y hy => (hRS y).mpr hy
  have hsc : ∀ n, (C.find? n).isSome = true → ∀ d ci, ((R n).find? d).isSome = true →
      C.find? d = some ci → EntryScopedP (fun y => ((R n).find? y).isSome = true) C d ci := by
    intro n hn d ci hd hf
    rcases hold n with ho | ho
    · obtain ⟨-, hR⟩ := hEold ho
      rw [hR] at hd ⊢
      have hfE := hEfind hd hf
      exact EntryScopedP.congrC (hscE d ci hfE) fun t ht => by rw [← hECt d hd]; exact ht
    · obtain ⟨-, hR⟩ := hEnew ho
      rw [hR] at hd ⊢
      exact hscS d ci ((hRS d).mp hd).1 hf
  have hself : ∀ n, (C.find? n).isSome = true → ((R n).find? n).isSome = true := by
    intro n hn
    rcases hold n with ho | ho
    · rw [(hEold ho).2]; exact ho
    · rw [(hEnew ho).2]; exact (hRS n).mpr ⟨hnew n hn ho, hn⟩
  have hread : CtxRead C E' R :=
    { nodup := hnd
      entry := by
        intro n ci hf
        rcases hold n with ho | ho
        · rw [(hEold ho).1]; exact ⟨ci, hEfind ho hf, .inl rfl⟩
        · rw [(hEnew ho).1]
          obtain ⟨ci₀, ci', h1, h2, h3, -⟩ := hfS n (hnew n (hCsome hf) ho)
          rw [hCF n ci hf] at h1
          obtain rfl := Option.some.inj h1
          exact ⟨ci', h2, h3⟩
      R_sub := by
        intro n d ci h
        rcases hold n with ho | ho
        · obtain ⟨h1, h2⟩ := hEold ho
          rw [h2] at h; rw [h1]
          exact ⟨h, hCsome (hEC d ci h)⟩
        · obtain ⟨h1, h2⟩ := hEnew ho
          rw [h2] at h; rw [h1]
          exact hRSf d ci h
      self := hself
      alike := by
        intro n d hn hd
        rcases hold n with ho | ho
        · obtain ⟨h1, h2⟩ := hEold ho
          rw [h2] at hd; rw [h1]
          obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hd
          exact ⟨c, c, hEC d c hc, hc, .inl rfl⟩
        · obtain ⟨h1, h2⟩ := hEnew ho
          rw [h2] at hd; rw [h1]
          obtain ⟨hsh, hCd⟩ := (hRS d).mp hd
          obtain ⟨ciC, hC⟩ := Option.isSome_iff_exists.mp hCd
          obtain ⟨ci₀, ci', g1, g2, g3, -⟩ := hfS d hsh
          rw [hCF d ciC hC] at g1
          obtain rfl := Option.some.inj g1
          exact ⟨ciC, ci', hC, g2, g3.alike⟩
      table := by
        intro n d hn hd
        rcases hold n with ho | ho
        · obtain ⟨h1, h2⟩ := hEold ho
          rw [h2] at hd; rw [h1]
          exact hECt d hd
        · obtain ⟨h1, h2⟩ := hEnew ho
          rw [h2] at hd; rw [h1]
          obtain ⟨hsh, hCd⟩ := (hRS d).mp hd
          obtain ⟨-, -, -, -, -, ht⟩ := (shared_closed JS Ef d hsh).1
          rw [← hCFt d hCd, tableBeqP_eq ht, hJ, mkFEnv_findTable?, renEnv_findTable]
      scope := fun n ci hf => hsc n (hCsome hf) n ci (hself n (hCsome hf)) hf
      ctors := by
        intro n d cv caps hn hd hfd x hx
        rcases hold n with ho | ho
        · rw [(hEold ho).2] at hd ⊢
          exact hctE d cv caps (hEfind hd hfd) x hx
        · rw [(hEnew ho).2] at hd ⊢
          obtain ⟨hsh, -⟩ := (hRS d).mp hd
          have hcl := (shared_closed JS Ef d hsh).2 _ (hCF d _ hfd) x
            (entryNeeds_ctor JS.mates Ef.findTable? hx)
          exact (hRS x).mpr ⟨hcl, hctC d cv caps hfd x hx⟩
      deep := fun n d ci hn hd hfd _ => hsc n hn d ci hd hfd
      reduce := by
        intro n ci hf hr
        rcases hold n with ho | ho
        · rw [(hEold ho).1]; exact hEfind ho hf
        · rw [(hEnew ho).1]
          obtain ⟨ci₀, ci', h1, h2, -, h4⟩ := hfS n (hnew n (hCsome hf) ho)
          rw [hCF n ci hf] at h1
          obtain rfl := Option.some.inj h1
          rw [h2, h4 (List.elem_iff.mpr hr)]
      tables_mem := htC
      tables_src := by
        intro n t ht
        rcases hold n with ho | ho
        · rw [(hEold ho).1] at ht ⊢; exact htE t ht
        · rw [(hEnew ho).1] at ht ⊢
          obtain ⟨h1, cv, caps, h2⟩ := htS t ht
          refine ⟨by rw [renEnv_findTable]; exact h1, cv, caps, ?_⟩
          rw [renEnv_find, h2]
          simp only [Option.map_some]
          rw [renS_of_not_stmt Ef rfl] }
  have hm : ∀ n, (srcModel mp mS (old n)).base2.acval =
      if old n then mp.base2.acval else mS.base2.acval := fun n => srcModel_acval mp mS _
  obtain ⟨mp', hcov', hN', hleaf'⟩ := ctxModel (aC := aC) hread (fun n => srcModel mp mS (old n))
    (fun n => srcModel_cover hcov hcovS (old n)) (fun n => srcEnv_nat hN hNS (old n))
    (by
      intro n hn d hd
      rw [hm n]
      rcases hold n with ho | ho
      · rw [(hEold ho).2] at hd
        have hdo : old d = true := hd
        simp only [aC, ho, hdo, ↓reduceIte]
      · rw [(hEnew ho).2] at hd
        obtain ⟨hsh, -⟩ := (hRS d).mp hd
        simp only [aC, ho]
        by_cases hdo : old d = true
        · simp only [hdo, ↓reduceIte, Bool.false_eq_true]; exact hagree d hdo hsh
        · simp only [hdo, ↓reduceIte, Bool.false_eq_true])
    (fun n ψ => by
      simp only [aC]; split
      · exact mp.base2.cval_closed n ψ
      · exact mS.base2.cval_closed n ψ)
    (fun n ψ ρ => by
      simp only [aC]; split
      · exact mp.base2.acval_wellDenoted n ψ ρ
      · exact mS.base2.acval_wellDenoted n ψ ρ)
  refine ⟨mp', hcov', hN', fun x hx => ?_, fun x hx hxo => ?_⟩
  · obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hx
    rw [hleaf' x (hCsome (hEC x c hc))]
    simp only [aC, old, hx, ↓reduceIte]
  · rw [hleaf' x hx]
    simp only [aC, old, hxo, Bool.false_eq_true, ↓reduceIte]

end ConLeche.Model.Sidecar
