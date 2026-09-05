import Setlec.SetP.IndConsP

/-!
# The P step at a tower-entry cons (task #175 W4c, P3 module 4, part 2)

`declStepPM_of_tower_cons`: the install kit at a head that is a
tower-backed projection entry.  The head's crossing condition is the
`NoProjEnv` of the prefix at the entry's slot (`BitConsCross`), the
head data is `TowerHead`, and the one row the transports cannot
supply — the head's own `TowerEntryLawP` — is the install's
(`towerOkP_cons_tower`).  The `NoProjEnv` bookkeeping the direct
install needs is here too: the pre-block environment lacks the
structure altogether (`noProjEnv_of_fresh`), and each block constant
is consed with its own pieces' `NoProjAt` (`NoProjEnv.cons`).
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (Env Expr Name Level ConstantInfo ConstantVal RecRule ProjEntry
  natName natZeroName natSuccName eqName)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## `NoProjEnv` bookkeeping -/

/-- A well-formed environment that does not store `T` has no `.proj T _`
node anywhere: every stored piece resolves in it. -/
theorem noProjEnv_of_fresh (hwf : Setlec.EnvWF env) {T : Name}
    (hT : env.find? T = none) (i : Nat) : NoProjEnv env T i where
  type c hc := Setlec.Expr.noProjAt_of_constsResolve hT _ (hwf c hc).2.2.1
  defn cv v hint hc :=
    Setlec.Expr.noProjAt_of_constsResolve hT _
      ((hwf _ hc).2.2.2.2.1 cv v hint rfl).2.2.1
  thm cv v hc :=
    Setlec.Expr.noProjAt_of_constsResolve hT _
      ((hwf _ hc).2.2.2.2.2.2 cv v rfl).2.2.1
  rule cv mI rP rules hc r hr := by
    obtain ⟨-, -, -, -, -, hrec, -⟩ := hwf _ hc
    obtain ⟨-, -, hres, -, hnest⟩ := hrec cv mI rP rules rfl r hr
    refine ⟨Setlec.Expr.noProjAt_of_constsResolve hT _ hres, ?_⟩
    intro lvls pins hn pin hp
    obtain ⟨-, -, hpins, -⟩ := hnest lvls pins hn
    exact Setlec.Expr.noProjAt_of_constsResolve hT _ (hpins pin hp).2.2.1

/-- The head's pieces, for a cons step of `NoProjEnv`. -/
structure NoProjHead (c₀ : ConstantInfo) (T : Name) (i : Nat) : Prop where
  type : Expr.NoProjAt T i c₀.toConstantVal.type
  defn : ∀ (cv : ConstantVal) (v : Expr) (hint : Setlec.ReducibilityHint),
    c₀ = .defnInfo cv v hint → Expr.NoProjAt T i v
  thm : ∀ (cv : ConstantVal) (v : Expr), c₀ = .thmInfo cv v →
    Expr.NoProjAt T i v
  rule : ∀ (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
    c₀ = .recInfo cv mI rP rules →
    ∀ r ∈ rules, Expr.NoProjAt T i (RecRule.rhs r) ∧
      ∀ lvls pins, RecRule.fire r = .nested lvls pins →
        ∀ pin ∈ pins, Expr.NoProjAt T i pin

/-- A head with no value or rule pieces (an inductive, a constructor,
a table entry): only its type is asked. -/
theorem NoProjHead.ofType {c₀ : ConstantInfo} {T : Name} {i : Nat}
    (hty : Expr.NoProjAt T i c₀.toConstantVal.type)
    (hnotdefn : ∀ cv v hint, c₀ ≠ .defnInfo cv v hint)
    (hnotthm : ∀ cv v, c₀ ≠ .thmInfo cv v)
    (hnotrec : ∀ cv mI rP rules, c₀ ≠ .recInfo cv mI rP rules) :
    NoProjHead c₀ T i :=
  ⟨hty, fun cv v hint h => absurd h (hnotdefn cv v hint),
    fun cv v h => absurd h (hnotthm cv v),
    fun cv mI rP rules h => absurd h (hnotrec cv mI rP rules)⟩

theorem NoProjEnv.cons {T : Name} {i : Nat} (h : NoProjEnv env T i)
    {c₀ : ConstantInfo} (hh : NoProjHead c₀ T i) :
    NoProjEnv ⟨c₀ :: env.consts⟩ T i where
  type c hc := by
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hh.type
    · exact h.type c hc
  defn cv v hint hc := by
    rcases List.mem_cons.mp hc with heq | hc
    · exact hh.defn cv v hint heq.symm
    · exact h.defn cv v hint hc
  thm cv v hc := by
    rcases List.mem_cons.mp hc with heq | hc
    · exact hh.thm cv v heq.symm
    · exact h.thm cv v hc
  rule cv mI rP rules hc := by
    rcases List.mem_cons.mp hc with heq | hc
    · exact hh.rule cv mI rP rules heq.symm
    · exact h.rule cv mI rP rules hc

/-! ## The kit -/

/-- **The P step at a tower-entry cons.**  The head is a native,
tower-backed entry at a non-reserved projection-function name; its
slot is mentioned by no stored piece; its head data holds at the
extension; and its own projection law is supplied.  Everything else
transports as at any fresh cons. -/
theorem declStepPM_of_tower_cons (mp : EnvS2PM V μ env)
    {entry : ProjEntry} {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? (ConstantInfo.projInfo entry).name = none)
    (hnres : Setlec.reservedBasisNames.contains
      (ConstantInfo.projInfo entry).name = false)
    (htw : entry.tower = true)
    (hwf : Setlec.EnvWF ⟨.projInfo entry :: env.consts⟩)
    (hvclosed : ∀ ψ : Name → Nat, VExpr.Closed ((A ψ).erase))
    (hnp : NoProjEnv env entry.structName entry.idx)
    (hhead : Setlec.TowerHead ⟨.projInfo entry :: env.consts⟩ entry)
    (hAclosed : ∀ (ψ : Name → Nat) (k : Nat), (A ψ).liftN 1 k = A ψ)
    (hAparams : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ (ConstantInfo.projInfo entry).toConstantVal.levelParams,
        ψ₁ p = ψ₂ p) → A ψ₁ = A ψ₂)
    (hAok : ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOk2 V ρ (A ψ))
    (hAvalid : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      AnnotValidV V ρ (A ψ))
    (htyReads : ∀ ψ : Name → Nat,
      ∃ ta : AVExpr,
        denoteP (acvalWith mp.base2.acval
            (ConstantInfo.projInfo entry).name A)
          ⟨.projInfo entry :: env.consts⟩ ψ 0
          (ConstantInfo.projInfo entry).toConstantVal.type = some ta)
    (htyOk : ∀ (ψ : Name → Nat) (ta : AVExpr),
      denoteP (acvalWith mp.base2.acval
            (ConstantInfo.projInfo entry).name A)
          ⟨.projInfo entry :: env.consts⟩ ψ 0
          (ConstantInfo.projInfo entry).toConstantVal.type = some ta →
      ∀ ρ : Nat → V, AnnotOkP V ρ ta)
    (hlaw : ∀ m₂ : EnvS2Core V ⟨.projInfo entry :: env.consts⟩,
      m₂.acval = acvalWith mp.base2.acval
        (ConstantInfo.projInfo entry).name A →
      ∀ φ : Name → Nat,
        TowerEntryLawP m₂ φ entry.structName entry.idx entry) :
    ∃ mp' : EnvS2PM V μ ⟨.projInfo entry :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval
        (ConstantInfo.projInfo entry).name A := by
  have hh : ConsHeadP env (.projInfo entry) A :=
    ⟨hwf, hvclosed,
      fun hres => absurd hres (by rw [hnres]; exact fun h => nomatch h),
      fun e2 heq _ htf => by
        obtain rfl := ConstantInfo.projInfo.inj heq
        exact absurd (htf.symm.trans htw) (by decide),
      fun _ e2 heq _ => by
        obtain rfl := ConstantInfo.projInfo.inj heq
        exact hhead.1,
      fun e2 heq _ => by
        obtain rfl := ConstantInfo.projInfo.inj heq
        exact hnp,
      fun e2 heq _ => by
        obtain rfl := ConstantInfo.projInfo.inj heq
        exact hhead,
      fun _ _ _ _ heq => nomatch heq⟩
  refine declStepPM_of_cons_guarded mp (c₀ := .projInfo entry) (A := A) hfresh hh
    hAclosed hAparams hAok hAvalid htyReads htyOk
    (fun hnt => by simp [ConstantInfo.isTowerEntry, htw] at hnt)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- `hvalReads`: an entry is neither a definition nor a theorem
    intro _ψ cv2 value2 hmem
    rcases hmem with ⟨hint2, hdt⟩ | hdt <;> exact nomatch hdt
  · -- `nat_heads`: the three guard names are reserved, this one is not
    exact fun φ => natHeadsP_cons_offNat mp
      (ne_of_notReserved hnres reserved_natName)
      (ne_of_notReserved hnres reserved_natZeroName)
      (ne_of_notReserved hnres reserved_natSuccName) _ rfl φ
  · exact fun φ => natOpsP_cons_fresh mp (mp.nat_ops φ) hfresh
      (hntc := hh.projTower) (Or.inl fun _ _ _ h => nomatch h) _ rfl
  · exact fun φ => divModP_cons_fresh (mp.div_mod φ) hfresh
      (Or.inl fun _ _ _ h => nomatch h) _ rfl
  · exact eqLawP_cons_fresh mp.eq_lawP
      (fun h => ne_of_notReserved hnres reserved_eqName h.symm) _ rfl
  · exact capsOkP_cons_fresh mp mp.caps_ok hfresh hh.projTower
      (fun _ _ h => nomatch h) (fun _ _ _ h => nomatch h)
      (fun _ _ _ _ h => nomatch h) _ rfl
  · exact fun φ => recRulesP_cons_fresh mp hfresh hh.projTower
      (fun _ _ _ _ h => nomatch h) _ rfl φ
  · exact reduceOpsP_cons_fresh mp.reduce_ops hfresh
      (Or.inl fun _ h => nomatch h) _ rfl
  · exact fun φ => towerOkP_cons_tower mp hfresh hh.projTower _ rfl
      (hlaw _ rfl) φ

/-- **The P step at an inert projection-table entry** (task #175 W4c
P3 module 7, `directInertEntry`): a non-native, non-tower entry of
type `Sort 1` holding an unadmitted slot.  Its leaf is `Sort 0` (a
member of its type's reading); it types no node and fires no
reduction, so no law is owed — every environment law crosses the
fresh cons as at any inert constant. -/
theorem declStepPM_of_inert_cons (mp : EnvS2PM V μ env)
    {entry : ProjEntry}
    (hfresh : env.find? (ConstantInfo.projInfo entry).name = none)
    (hnres : Setlec.reservedBasisNames.contains
      (ConstantInfo.projInfo entry).name = false)
    (hTres : Setlec.reservedBasisNames.contains entry.structName = false)
    (htw : entry.tower = false) (hnat : entry.native = false)
    (hty : entry.ty = .sort (.succ .zero))
    (hwf : Setlec.EnvWF ⟨.projInfo entry :: env.consts⟩) :
    ∃ mp' : EnvS2PM V μ ⟨.projInfo entry :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval
        (ConstantInfo.projInfo entry).name (fun _ => .sort 0) := by
  have hh : ConsHeadP env (.projInfo entry) (fun _ => .sort 0) :=
    ⟨hwf, fun _ => trivial,
      fun hres => absurd hres (by rw [hnres]; exact fun h => nomatch h),
      fun e2 heq hn _ => by
        obtain rfl := ConstantInfo.projInfo.inj heq
        exact absurd (hn.symm.trans hnat) (by decide),
      fun i e2 heq hname => by
        obtain rfl := ConstantInfo.projInfo.inj heq
        exfalso
        have h1 : projFnName entry.structName entry.idx = projFnName Setlec.psigmaName i :=
          hname
        have h2 := (Setlec.projFnName_inj h1).1
        exact ne_of_notReserved hTres reserved_psigmaName h2,
      ConsCrossEnv.ofNtc (fun e2 heq => by
        obtain rfl := ConstantInfo.projInfo.inj heq
        exact htw),
      fun e2 heq htw' => by
        obtain rfl := ConstantInfo.projInfo.inj heq
        exact absurd (htw.symm.trans htw') (by decide),
      fun _ _ _ _ heq => nomatch heq⟩
  have hreads : ∀ ψ : Name → Nat,
      denoteP (acvalWith mp.base2.acval (ConstantInfo.projInfo entry).name (fun _ => .sort 0))
        ⟨.projInfo entry :: env.consts⟩ ψ 0 (ConstantInfo.projInfo entry).toConstantVal.type
        = some (.sort 1) := by
    intro ψ
    show denoteP _ _ ψ 0 entry.ty = _
    rw [hty, denoteP_sort]
    rfl
  refine declStepPM_of_cons_guarded mp (c₀ := .projInfo entry) (A := fun _ => .sort 0) hfresh hh
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => by rw [AnnotOk2_sort]; trivial)
    (fun _ _ => by rw [AnnotValidV_sort]; trivial)
    (fun ψ => ⟨_, hreads ψ⟩)
    (fun ψ ta hta ρ => by
      obtain rfl := Option.some.inj ((hreads ψ).symm.trans hta)
      exact ⟨by rw [AnnotOk2_sort]; trivial, by rw [AnnotValidV_sort]; trivial⟩)
    (fun _ ψ ta hta ρ => by
      obtain rfl := Option.some.inj ((hreads ψ).symm.trans hta)
      exact interp2_sort_mem V ρ 0)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro _ψ cv2 value2 hmem
    rcases hmem with ⟨hint2, hdt⟩ | hdt <;> exact nomatch hdt
  · exact fun φ => natHeadsP_cons_offNat mp
      (ne_of_notReserved hnres reserved_natName)
      (ne_of_notReserved hnres reserved_natZeroName)
      (ne_of_notReserved hnres reserved_natSuccName) _ rfl φ
  · exact fun φ => natOpsP_cons_fresh mp (mp.nat_ops φ) hfresh
      (hntc := hh.projTower) (Or.inl fun _ _ _ h => nomatch h) _ rfl
  · exact fun φ => divModP_cons_fresh (mp.div_mod φ) hfresh
      (Or.inl fun _ _ _ h => nomatch h) _ rfl
  · exact eqLawP_cons_fresh mp.eq_lawP
      (fun h => ne_of_notReserved hnres reserved_eqName h.symm) _ rfl
  · exact capsOkP_cons_fresh mp mp.caps_ok hfresh hh.projTower
      (fun _ _ h => nomatch h) (fun _ _ _ h => nomatch h)
      (fun _ _ _ _ h => nomatch h) _ rfl
  · exact fun φ => recRulesP_cons_fresh mp hfresh hh.projTower
      (fun _ _ _ _ h => nomatch h) _ rfl φ
  · exact reduceOpsP_cons_fresh mp.reduce_ops hfresh
      (Or.inl fun _ h => nomatch h) _ rfl
  · exact fun φ => towerOkP_cons_fresh mp hfresh hh.projTower
      (fun e2 heq => by obtain rfl := ConstantInfo.projInfo.inj heq; exact htw) _ rfl φ

end Setlec.SetR.Interp2
