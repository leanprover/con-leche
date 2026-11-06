module

public import ConLeche.Model.Modular.RestrictAgree
import ConLeche.Model.StreamConsts

public section

/-!
# A context's carrier and its constant-level laws, read from its sources

The second part of `ctxModel` (`Model/Modular/Restrict.lean`): the context's `EnvModel` at the
leaves `aC` (`CtxSrc.base`), and the laws keyed on one stored constant — its type's reading and
membership, a definition's value, the `Nat` heads, `Eq`, the compiler-trust opaques, the
structure capabilities and the η families' closure.  Each is read off the law of its source, at
the constant's own source `E n`: what the law reads is read alike there (`CtxRead.scope`,
`CtxRead.deep`), so it reads alike (`CtxSrc.denote_eq`).
-/

namespace ConLeche.Model.Modular

open ConLeche ConLeche.Modular ConLeche.Model ConLeche.Verify ConLeche.Semantics
open ConLeche.Term SetTheory

universe w

/-! ## Refinement -/

theorem Refines.cv {ci ci' : ConstantInfo} (h : Refines ci ci') :
    ci.toConstantVal = ci'.toConstantVal := h.alike.cv

/-- A definition or theorem: the kinds a context may present as a statement. -/
@[expose] def _root_.ConLeche.ConstantInfo.isDT : ConstantInfo → Bool
  | .defnInfo .. | .thmInfo .. => true
  | _ => false

/-- **A copy refining a constant that is no definition or theorem is that constant.** -/
theorem Refines.eq_of_isDT {ci ci' : ConstantInfo} (h : Refines ci ci') (hk : ci'.isDT = false) :
    ci = ci' := by
  rcases h with h | ⟨rfl, h⟩
  · exact h
  · cases ci' <;> simp_all [ConstantInfo.isStmtKind, ConstantInfo.isDT] <;> rfl

theorem atLps_isDT (ci : ConstantInfo) (ps : List Name) : (ci.atLps ps).isDT = ci.isDT := by
  cases ci <;> rfl

theorem pinnedInfo_isDT : ∀ n ∈ reservedBasisNames, (pinnedInfo n).isDT = false := by decide

/-- A literal's shape carries to a refining copy. -/
theorem litShapeOk_refines {ci ci' : ConstantInfo} (h : Refines ci ci')
    (hs : litShapeOk ci' = true) : litShapeOk ci = true := by
  rcases h with rfl | ⟨rfl, hk⟩
  · exact hs
  · rw [← hs]
    cases ci' <;> simp only [ConstantInfo.isStmtKind, Bool.false_eq_true] at hk <;>
      simp only [litShapeOk, ConstantInfo.name, ConstantInfo.toConstantVal, natIndOk, natZeroOk,
        natSuccOk, stringTyOk, stringOfListTyOk, listTyOk, listNilTyOk, listConsTyOk, charTyOk,
        charOfNatTyOk] <;> rfl

theorem NestedRead.mono {p q : Expr → Bool} {lps : List Name} {tyA : Expr} {mI rP cnP : Nat}
    {lvls : List Level} {pins : List Expr} (h : NestedRead p lps tyA mI rP cnP lvls pins)
    (hq : ∀ pin ∈ pins, q pin = true) : NestedRead q lps tyA mI rP cnP lvls pins := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, fun pin hp => ⟨(h3 pin hp).1, (h3 pin hp).2.1, hq pin hp, (h3 pin hp).2.2.2⟩, h4⟩

namespace CtxSrc

variable {V : Type w} [SetTheory V] {C : Env} {E R : Name → Env}
  {aC : Name → (Name → Nat) → Term} (S : CtxSrc V C E R aC)
include S

/-! ## Reading off the part read alike -/

/-- What a stored constant's laws read is read alike. -/
theorem scopeR {n : Name} {ci : ConstantInfo} (hf : C.find? n = some ci) :
    EntryScopedP (fun d => ((R n).find? d).isSome = true) C n ci := S.read.scope n ci hf

omit [SetTheory V] S in
theorem resR {n : Name} {e : Expr} (h : Expr.constsAll (fun d => ((R n).find? d).isSome = true) e) :
    e.constsResolve (R n) = true := (Expr.constsResolve_iff (R n)).mpr h

theorem resC {n : Name} {e : Expr} (h : e.constsResolve (R n) = true) :
    e.constsResolve C = true :=
  Expr.constsResolve_of_find (fun _ hd => S.storedC hd) h

theorem resE {n : Name} {e : Expr} (h : e.constsResolve (R n) = true) :
    e.constsResolve (E n) = true :=
  Expr.constsResolve_of_find (fun _ hd => S.storedE hd) h

/-- A term read alike, at an instantiation of its levels, reads alike. -/
theorem denote_inst {n : Name} (hn : (C.find? n).isSome = true) {e : Expr}
    (h : e.constsResolve (R n) = true) (ψ : Name → Nat) (d : Nat) (ks : List Name)
    (us : List Level) :
    denote aC C ψ d (e.instantiateLevelParams ks us)
      = denote (S.m n).base2.acval (E n) ψ d (e.instantiateLevelParams ks us) :=
  S.denote_eq hn ψ d _ (by rw [Expr.constsResolve_instantiateLevelParams]; exact h)

/-- An inductive kind read alike: its type is read alike. -/
theorem deepType {n d : Name} (hn : (C.find? n).isSome = true) (hd : ((R n).find? d).isSome = true)
    {ci : ConstantInfo} (hf : C.find? d = some ci) (hk : ci.isIndKind = true) :
    ci.toConstantVal.type.constsResolve (R n) = true :=
  resR (S.read.deep n d ci hn hd hf hk).1

/-- A stored constant, with its source's copy and that copy's well-formedness. -/
theorem srcWF {n : Name} {ci : ConstantInfo} (hf : C.find? n = some ci) :
    ∃ ci', (E n).find? n = some ci' ∧ Refines ci ci' ∧ ConstWF (E n) ci' := by
  obtain ⟨ci', hf', hr⟩ := S.src hf
  exact ⟨ci', hf', hr, (S.m n).base2.wf.consts _ (Env.find?_mem hf')⟩

/-- A stored constant's type reads as its source's. -/
theorem type_eq {n : Name} {ci ci' : ConstantInfo} (hf : C.find? n = some ci)
    (hr : Refines ci ci') (ψ : Name → Nat) (d : Nat) :
    denote aC C ψ d ci.toConstantVal.type
      = denote (S.m n).base2.acval (E n) ψ d ci'.toConstantVal.type := by
  rw [← hr.cv]
  exact S.denote_eq (isSome_of hf) ψ d _ (resR (S.scopeR hf).1)

/-- ... at an instantiation of its levels. -/
theorem type_eq_inst {n : Name} {ci ci' : ConstantInfo} (hf : C.find? n = some ci)
    (hr : Refines ci ci') (ψ : Name → Nat) (d : Nat) (ks : List Name) (us : List Level) :
    denote aC C ψ d (ci.toConstantVal.type.instantiateLevelParams ks us)
      = denote (S.m n).base2.acval (E n) ψ d
          (ci'.toConstantVal.type.instantiateLevelParams ks us) := by
  rw [← hr.cv]
  exact S.denote_inst (isSome_of hf) (resR (S.scopeR hf).1) ψ d ks us

/-- A stored constant's leaf is its source's. -/
theorem leafSelf {n : Name} {ci : ConstantInfo} (hf : C.find? n = some ci) :
    aC n = (S.m n).base2.acval n := S.leaf n (isSome_of hf) n (S.selfR hf)

/-- A stored reserved name is its source's constant. -/
theorem src_reserved {n : Name} {ci : ConstantInfo} (hf : C.find? n = some ci)
    (hres : reservedBasisNames.contains n = true) : (E n).find? n = some ci := by
  obtain ⟨ci', hf', hr⟩ := S.src hf
  have hpin := ((S.m n).base2.basis_pinned n ci' hf' hres).1.1
  have hk : ci'.isDT = false := by
    rw [hpin, atLps_isDT]; exact pinnedInfo_isDT n (List.contains_iff_mem.mp hres)
  rw [hf', hr.eq_of_isDT hk]

/-! ## The carrier -/

theorem nodup : NodupNames C := S.read.nodup

theorem find_of_mem {c : ConstantInfo} (hc : c ∈ C.consts) : C.find? c.name = some c :=
  ConLeche.Cached.find?_of_mem_nodup S.nodup hc

/-- **The context is well formed.** -/
theorem wf : EnvWF C := by
  refine ⟨fun c hc => ?_, fun c hc => ?_, fun t ht => ?_⟩
  · have hf := S.find_of_mem hc
    obtain ⟨ci', hf', hr, hwf'⟩ := S.srcWF hf
    have hsc := S.scopeR hf
    obtain ⟨h1, h2, -, h4, hdef, hrec⟩ := hwf'
    refine ⟨by rw [hr.cv]; exact h1, by rw [hr.cv]; exact h2, S.resC (resR hsc.1),
      by rw [hr.cv]; exact h4, fun cv v hint he => ?_, fun cv mI rP isK rules he r hrr => ?_⟩
    · have he' : ci' = .defnInfo cv v hint := by
        have := S.src_eq hf (by rw [he]; exact fun _ h => nomatch h)
        rw [hf'] at this; exact (Option.some.inj this).trans he
      obtain ⟨a, b, -, d⟩ := hdef cv v hint he'
      exact ⟨a, b, S.resC (resR (hsc.2.1 cv v hint he)), d⟩
    · have he' : ci' = .recInfo cv mI rP isK rules := by
        have := S.src_ind hf (by rw [he]; rfl)
        rw [hf'] at this; exact (Option.some.inj this).trans he
      obtain ⟨a, b, -, d, e⟩ := hrec cv mI rP isK rules he' r hrr
      obtain ⟨hrh, -, hpins⟩ := hsc.2.2.1 cv mI rP isK rules he r hrr
      exact ⟨a, b, S.resC (resR hrh), d, fun lvls pins hn =>
        NestedRead.mono (e lvls pins hn) fun pin hp => S.resC (resR (hpins lvls pins hn pin hp))⟩
  · have hf := S.find_of_mem hc
    obtain ⟨ci', hf', hr⟩ := S.src hf
    exact litShapeOk_refines hr ((S.m c.name).base2.wf.shapes _ (Env.find?_mem hf'))
  · obtain ⟨hft, cv, caps, hfT⟩ := S.read.tables_mem t ht
    have hT := isSome_of hfT
    have htE : (E t.structName).findTable? t.structName = some t := by
      rw [← S.table_eq hT (S.selfR hfT)]; exact hft
    obtain ⟨-, hsize, hbodies⟩ := (S.m t.structName).base2.wf.table htE
    refine ⟨hT, hsize, fun i b hb => ?_⟩
    obtain ⟨a, b', -, d⟩ := hbodies i b hb
    obtain ⟨-, -, -, hind, -⟩ := S.scopeR hfT
    exact ⟨a, b', S.resC (resR (((hind cv caps rfl).2.2 t hft).2 b
      (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hb)))), d⟩

/-- **The basis pins hold in the context.** -/
theorem basis_pinned : BasisPinnedTT C aC := by
  intro n ci hf hres
  have hE := S.src_reserved hf hres
  obtain ⟨h1, h2, h3⟩ := (S.m n).base2.basis_pinned n ci hE hres
  refine ⟨h1, fun cv mI rP isK rules hci rl hrl hp cvj cnP cnF hfc us hus => ?_, fun t ψ hp => ?_⟩
  · have hcR := ((S.scopeR hf).2.2.1 cv mI rP isK rules hci rl hrl).2.1
    exact h2 cv mI rP isK rules hci rl hrl hp cvj cnP cnF
      (S.findE (isSome_of hf) hcR hfc rfl) us hus
  · rw [S.leafSelf hf]; exact h3 t ψ hp

/-- **The context's tables are its sources'**, entry by entry. -/
theorem proj_ok : ProjOkT C := by
  intro T tbl ht i hi
  obtain ⟨-, hsn, hT⟩ := Env.findTable?_mem ht
  have hR := S.read.self T hT
  have htE : (E T).findTable? T = some tbl := by rw [← S.table_eq hT hR]; exact ht
  obtain ⟨r1, r2, r3, r4, ⟨cvT, capsT, hfT, hlpT⟩, ⟨cvC, hfC, hlpC, hstrip⟩⟩ :=
    (S.m T).base2.proj_ok T tbl htE i hi
  have hsnT : (tbl.entry i).structName = T := hsn
  rw [hsnT] at hfT
  have hfTC := S.findC hT hR hfT rfl
  obtain ⟨-, -, -, hind, -⟩ := S.scopeR hfTC
  have hcR : ((R T).find? tbl.ctor).isSome = true := ((hind cvT capsT rfl).2.2 tbl ht).1
  refine ⟨r1, r2, r3, r4, ⟨cvT, capsT, by rw [hsnT]; exact hfTC, hlpT⟩,
    ⟨cvC, S.findC hT hcR hfC rfl, hlpC, hstrip⟩⟩

/-- **The rules' constructors are stored in the context.** -/
theorem rec_ctors : RecCtorsStored C := by
  intro n cv mI rP isK rules hf r hr
  have hE := S.src_ind hf rfl
  obtain ⟨cvj, cnP, cnF, hfc⟩ := (S.m n).base2.rec_ctors n cv mI rP isK rules hE r hr
  have hcR := ((S.scopeR hf).2.2.1 cv mI rP isK rules rfl r hr).2.1
  exact ⟨cvj, cnP, cnF, S.findC (isSome_of hf) hcR hfc rfl⟩

theorem acval_params : ∀ (n : Name) (ci : ConstantInfo), C.find? n = some ci →
    ∀ ψ₁ ψ₂ : Name → Nat, (∀ p ∈ ci.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
      aC n ψ₁ = aC n ψ₂ := by
  intro n ci hf ψ₁ ψ₂ hp
  obtain ⟨ci', hf', hr⟩ := S.src hf
  rw [S.leafSelf hf]
  exact (S.m n).base2.acval_params n ci' hf' ψ₁ ψ₂ (by rw [← hr.cv]; exact hp)

/-- **The context's carrier.** -/
@[expose] def base : EnvModel V C where
  wf := S.wf
  acval := aC
  cval_closed := S.closed
  basis_pinned := S.basis_pinned
  proj_ok := S.proj_ok
  rec_ctors := S.rec_ctors
  acval_params := S.acval_params
  acval_wellDenoted := S.wd

theorem base_acval : S.base.acval = aC := rfl

/-! ## The constant-level laws -/

theorem type_reads : ∀ c ∈ C.consts, ∀ ψ : Name → Nat,
    ∃ ta : Term, denote S.base.acval C ψ 0 c.toConstantVal.type = some ta := by
  intro c hc ψ
  have hf := S.find_of_mem hc
  obtain ⟨ci', hf', hr⟩ := S.src hf
  rw [base_acval, S.type_eq hf hr ψ 0]
  exact (S.m c.name).type_reads ci' (Env.find?_mem hf') ψ

theorem type_wellDenotedTy : ∀ c ∈ C.consts, ∀ (ψ : Name → Nat) (ta : Term),
    denote S.base.acval C ψ 0 c.toConstantVal.type = some ta →
    ∀ ρ : Nat → V, WellDenotedTy V ρ ta := by
  intro c hc ψ ta hta
  have hf := S.find_of_mem hc
  obtain ⟨ci', hf', hr⟩ := S.src hf
  rw [base_acval, S.type_eq hf hr ψ 0] at hta
  exact (S.m c.name).type_wellDenotedTy ci' (Env.find?_mem hf') ψ ta hta

theorem mem_type : ∀ c ∈ C.consts, ∀ (ψ : Name → Nat) (ta : Term),
    denote S.base.acval C ψ 0 c.toConstantVal.type = some ta →
    ∀ ρ : Nat → V, interp V ρ (S.base.acval c.name ψ) ∈ˢ interp V ρ ta := by
  intro c hc ψ ta hta ρ
  have hf := S.find_of_mem hc
  obtain ⟨ci', hf', hr⟩ := S.src hf
  rw [base_acval, S.type_eq hf hr ψ 0] at hta
  rw [base_acval, S.leafSelf hf]
  have := (S.m c.name).mem_type ci' (Env.find?_mem hf') ψ ta hta ρ
  rwa [Env.find?_name hf'] at this

theorem defn_reads : AcvalDefnInst S.base := by
  intro ψ cv value ⟨hint, hmem⟩
  have hf := S.find_of_mem hmem
  have hE := S.src_eq hf fun _ h => nomatch h
  have hname : (ConstantInfo.defnInfo cv value hint).name = cv.name := rfl
  rw [hname] at hf hE
  obtain ⟨t, ht, hlr⟩ := (S.m cv.name).defn_reads ψ cv value ⟨hint, Env.find?_mem hE⟩
  refine ⟨t, ?_, ?_⟩
  · rw [base_acval, S.denote_eq (isSome_of hf) ψ 0 _
      (resR ((S.scopeR hf).2.1 cv value hint rfl))]
    exact ht
  · rw [base_acval, S.leafSelf hf]
    exact hlr

omit [SetTheory V] S in
theorem pin_nat (ψ : Name → Nat) : pinnedStructT natName ψ = some (.const .nat []) := by
  simp [pinnedStructT]

omit [SetTheory V] S in
theorem pin_natZero (ψ : Name → Nat) :
    pinnedStructT natZeroName ψ = some (.const .natZero []) := by
  simp (decide := true) [pinnedStructT]

omit [SetTheory V] S in
theorem pin_natSucc (ψ : Name → Nat) :
    pinnedStructT natSuccName ψ = some (.const .natSucc []) := by
  simp (decide := true) [pinnedStructT]

theorem nat_heads (φ : Name → Nat) : NatHeads S.base φ := by
  intro hs ρ
  obtain ⟨cvN, capsN, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, -⟩ := natLitSupported_inv hs
  -- the source of `Nat` stores the trio, at their shapes
  have hEN := S.src_reserved hfN (by decide)
  have htrio := (S.nat natName).trio (.inl (by rw [hEN]; rfl))
  have hsE : natLitSupported (E natName) = true :=
    natLitSupported_of_shapes
      (fun _ c hc => (S.m natName).base2.wf.shapes _ (Env.find?_mem hc))
      (by simp only [natLitStored, Bool.and_eq_true]; exact ⟨⟨htrio.1, htrio.2.1⟩, htrio.2.2⟩)
  have h := (S.m natName).nat_heads φ hsE ρ
  obtain ⟨ciZ, hEZ⟩ := Option.isSome_iff_exists.mp htrio.2.1
  obtain ⟨ciS, hES⟩ := Option.isSome_iff_exists.mp htrio.2.2
  have e1 : S.base.acval natName (Level.substFn φ [] []) = .const .nat [] :=
    S.base.acval_pinned_free hfN (by decide) (pin_nat)
  have e2 : S.base.acval natZeroName (Level.substFn φ [] []) = .const .natZero [] :=
    S.base.acval_pinned_free hfZ (by decide) (pin_natZero)
  have e3 : S.base.acval natSuccName (Level.substFn φ [] []) = .const .natSucc [] :=
    S.base.acval_pinned_free hfS (by decide) (pin_natSucc)
  have f1 : (S.m natName).base2.acval natName (Level.substFn φ [] []) = .const .nat [] :=
    (S.m natName).base2.acval_pinned_free hEN (by decide) (pin_nat)
  have f2 : (S.m natName).base2.acval natZeroName (Level.substFn φ [] []) = .const .natZero [] :=
    (S.m natName).base2.acval_pinned_free hEZ (by decide) (pin_natZero)
  have f3 : (S.m natName).base2.acval natSuccName (Level.substFn φ [] []) = .const .natSucc [] :=
    (S.m natName).base2.acval_pinned_free hES (by decide) (pin_natSucc)
  rw [f1, f2, f3] at h
  rw [e1, e2, e3]
  exact h

theorem eq_law : EqLaw S.base := by
  intro ci p hf hl ψ
  have hE := S.src_reserved hf (by decide)
  have h := (S.m eqName).eq_law ci p hE hl ψ
  rw [base_acval, S.leafSelf hf]
  exact h

theorem reduce_ops : ReduceOps S.base := by
  intro c hc cv hf hpin
  have hE := S.red c _ hf hc
  obtain ⟨hel, hlaw⟩ := (S.m c).reduce_ops c hc cv hE hpin
  have helR : ((R c).find? (reduceElemName c)).isSome = true :=
    (S.scopeR hf).2.2.2.2 _ (by
      simp only [reduceOpNames, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> decide)
  refine ⟨S.storedC helR, fun ψ ρ x hx => ?_⟩
  rw [base_acval, S.leaf c (isSome_of hf) _ helR] at hx
  rw [base_acval, S.leafSelf hf]
  exact hlaw ψ ρ x hx

theorem caps_ok : CapsOk S.base := by
  refine ⟨fun T cvT caps hf he hr hst φ' us hus => ?_, fun T cvT caps hf hu hr φ' us hus => ?_⟩
  · have hT := isSome_of hf
    have hE := S.src_ind hf rfl
    obtain ⟨hres, ⟨cvC, cnP, cnF, hfC⟩, hfl⟩ := hst
    have hR := ((S.scopeR hf).2.2.2.1 cvT caps rfl).2.1 he
    have hfCE := S.findE hT hR hfC rfl
    obtain ⟨hlaw, hcoh⟩ :=
      (S.m T).caps_ok.1 T cvT caps hE he hr ⟨hres, ⟨cvC, cnP, cnF, hfCE⟩, hfl⟩ φ' us hus
    refine ⟨fun ρ ts x hlen hfit hmem => ?_, ?_⟩
    · rw [base_acval, S.leafSelf hf] at hfit hmem
      rw [base_acval, S.leaf T hT _ hR]
      exact hlaw ρ ts x hlen hfit hmem
    · refine hcoh.transport (fun cvC' nPc nFc h₂ => S.findE hT hR h₂ rfl)
        (fun cvC' nPc nFc TCa h hTCa => ?_) (by rw [base_acval, S.leafSelf hf]) (fun _ _ _ => rfl)
      have hfC' := S.findC hT hR h rfl
      exact (S.denote_inst hT (S.deepType hT hR hfC' rfl) φ' 0 _ us).trans hTCa
  · have hT := isSome_of hf
    have hE := S.src_ind hf rfl
    have hlaw := (S.m T).caps_ok.2 T cvT caps hE hu hr φ' us hus
    intro ρ ts x y hlen hfit hx hy
    rw [base_acval, S.leafSelf hf] at hfit hx hy
    exact hlaw ρ ts x y hlen hfit hx hy

/-- **The context's η families are closed.** -/
theorem etaClosed : EtaFamiliesClosed C := by
  intro T cvT caps hf he hr
  have hT := isSome_of hf
  obtain ⟨cvC, hfC⟩ := S.eta T T cvT caps (S.src_ind hf rfl) he hr
  have hR := ((S.scopeR hf).2.2.2.1 cvT caps rfl).2.1 he
  exact ⟨cvC, S.findC hT hR hfC rfl⟩

end CtxSrc

end ConLeche.Model.Modular
