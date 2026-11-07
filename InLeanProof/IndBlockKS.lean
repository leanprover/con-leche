module

public import InLeanProof.IndDecl
public import ConLeche.Verify.Cached.BridgeCS4
import all Lean.Declaration

/-!
# O7: the recognised block's job against master's (task #451, lane O7)

`blockKSSimI_of`: `BlockKSSimI` (InLean's `checkBlockKS` accepting means master's
pure `checkBlock` accepts the translated block) from the job's stages, the
script of master's `checkBlockKS_run` (`Verify/Cached/GenRecC.lean`): the two
name guards and official's `is_rec` (`blockIsRec_tr`) at the translation, the
members' reduction (`reduceMembersSimI_of`, from one member's,
`ReduceMemberSimI`), and the pass with the stages after it (`PassTailSimI`,
named).

**Why the pass and the tail are one hypothesis.**  Master's `checkBlockKS_run`
splits them at `BlockPass Env`.  InLean's `BlockPass` carries the extended
environment (`FEnv`, the formers pushed as Lean entries), the canonical
parameter variables (interned free variables, read at the state), the class
reading, the classes and the positivity table; relating it to master's needs a
translation of each (`ClassRead`, `TargetMajor`, `NestCtorNf`,
`NestFieldKind`) and the environment relation at the formers' push.  Stated
together, the hypothesis needs none of them.
-/

set_option experimental.vcgen true

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached
open scoped Lean.Order

/-! ## Closed terms read under any table -/

theorem trE_of_okC (fv : FVarId → Option ConLeche.Expr) :
    ∀ {e : Lean.Expr}, okC e = true → trE fv e = trC e := by
  intro e
  induction e with
  | fvar id => intro h; simp [okC, okE] at h
  | app f a ihf iha =>
    intro h; simp only [okC, okE, Bool.and_eq_true] at h
    simp only [trE, trC] at ihf iha ⊢; rw [ihf h.1, iha h.2]
  | lam _ t b _ iht ihb =>
    intro h; simp only [okC, okE, Bool.and_eq_true] at h
    simp only [trE, trC] at iht ihb ⊢; rw [iht h.1, ihb h.2]
  | forallE _ t b _ iht ihb =>
    intro h; simp only [okC, okE, Bool.and_eq_true] at h
    simp only [trE, trC] at iht ihb ⊢; rw [iht h.1, ihb h.2]
  | letE _ t v b _ iht ihv ihb =>
    intro h; simp only [okC, okE, Bool.and_eq_true] at h
    simp only [trE, trC] at iht ihv ihb ⊢; rw [iht h.1.1, ihv h.1.2, ihb h.2]
  | mdata _ x ih => intro h; simp only [okC, okE] at h; simp only [trE, trC] at ih ⊢; rw [ih h]
  | proj _ _ x ih => intro h; simp only [okC, okE] at h; simp only [trE, trC] at ih ⊢; rw [ih h]
  | _ => intro _; rfl

/-- A closed term with a reading reads the same at every state. -/
theorem TrS_of_okC (s : InLean.CState) {e : Lean.Expr} (h : okC e = true) : TrS s e = trC e :=
  trE_of_okC _ h

/-! ## Official's `is_rec` at the translation -/

/-- `EO.any` at a predicate that picks a member's constant or projection is
master's `mentionsAnyConst` on the closed translation. -/
theorem anySpec_mentions (names : List Lean.Name) (p : Lean.Expr → Bool)
    (hc : ∀ n us, p (.const n us) = names.contains n)
    (hp : ∀ s i e, p (.proj s i e) = names.contains s)
    (ho : ∀ x, (∀ n us, x ≠ .const n us) → (∀ s i e, x ≠ .proj s i e) → p x = false) :
    ∀ (e : Lean.Expr) (k : Nat),
      anySpec (fun x _ => if p x then some true else none) e k =
        ConLeche.Expr.mentionsAnyConst (names.map toName) (trC e) := by
  intro e
  induction e with
  | const n us =>
    intro k
    simp only [anySpec, hc, trC, trE, ConLeche.Expr.mentionsAnyConst, contains_map_toName]
    cases names.contains n <;> rfl
  | proj s i x ih =>
    intro k
    simp only [anySpec, hp, trC, trE, ConLeche.Expr.mentionsAnyConst, contains_map_toName]
    rw [show trE (fun _ => none) x = trC x from rfl, ← ih k]
    cases names.contains s <;> rfl
  | app f a ihf iha =>
    intro k
    simp only [anySpec, ho (.app f a) (by simp) (by simp), Bool.false_eq_true, ↓reduceIte,
      Option.getD_none, ihf, iha]
    rfl
  | lam _ t b _ iht ihb =>
    intro k
    simp only [anySpec, ho (.lam _ t b _) (by simp) (by simp), Bool.false_eq_true, ↓reduceIte,
      Option.getD_none, iht, ihb]
    rfl
  | forallE _ t b _ iht ihb =>
    intro k
    simp only [anySpec, ho (.forallE _ t b _) (by simp) (by simp), Bool.false_eq_true, ↓reduceIte,
      Option.getD_none, iht, ihb]
    rfl
  | letE _ t v b _ iht ihv ihb =>
    intro k
    simp only [anySpec, ho (.letE _ t v b _) (by simp) (by simp), Bool.false_eq_true, ↓reduceIte,
      Option.getD_none, iht, ihv, ihb]
    rfl
  | mdata m x ih =>
    intro k
    simp only [anySpec, ho (.mdata m x) (by simp) (by simp), Bool.false_eq_true, ↓reduceIte,
      Option.getD_none, ih]
    rfl
  | bvar i => intro k; simp [anySpec, ho (.bvar i), trC, trE, ConLeche.Expr.mentionsAnyConst]
  | fvar i => intro k; simp [anySpec, ho (.fvar i), trC, trE, ConLeche.Expr.mentionsAnyConst]
  | mvar i => intro k; simp [anySpec, ho (.mvar i), trC, trE, ConLeche.Expr.mentionsAnyConst]
  | sort u => intro k; simp [anySpec, ho (.sort u), trC, trE, ConLeche.Expr.mentionsAnyConst]
  | lit l => intro k; simp [anySpec, ho (.lit l), trC, trE, ConLeche.Expr.mentionsAnyConst]

theorem piDomsMentionAny_tr (names : List Lean.Name) : ∀ (e : Lean.Expr),
    ConLeche.Expr.piDomsMentionAny (names.map toName) (trC e) = InLean.piDomsMentionAny names e
  | .forallE _ ty b _ => by
    simp only [InLean.piDomsMentionAny, EO.any, anyNode_fresh]
    rw [anySpec_mentions names _ (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun x h1 h2 => by cases x <;> simp_all)]
    simp only [trC, trE, ConLeche.Expr.piDomsMentionAny]
    rw [show trE (fun _ => none) b = trC b from rfl, piDomsMentionAny_tr names b]
  | .mdata _ e => by simp only [InLean.piDomsMentionAny]; exact piDomsMentionAny_tr names e
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ _ _
  | .letE _ _ _ _ _ | .lit _ | .proj _ _ _ => by
    simp [InLean.piDomsMentionAny, ConLeche.Expr.piDomsMentionAny, trC, trE]

theorem trShape_memberNames (p : InLean.BlockShape) :
    (trShape p).memberNames = p.memberNames.map toName := by
  simp [trShape, ConLeche.BlockShape.memberNames, InLean.BlockShape.memberNames, trMember]

/-- **Official's `is_rec`** at the translation. -/
theorem blockIsRec_tr (p : InLean.BlockShape) :
    ConLeche.blockIsRec (trShape p) = InLean.blockIsRec p := by
  unfold ConLeche.blockIsRec InLean.blockIsRec
  rw [trShape_memberNames]
  simp only [trShape, List.any_map, Function.comp_def, trMember, trCtor, trCV_type,
    piDomsMentionAny_tr]

/-! ## The name guards -/

theorem namesNodup_iff : ∀ (l : List Lean.Name), InLean.namesNodup l = true ↔ (l.map toName).Nodup
  | [] => by simp [InLean.namesNodup]
  | n :: l => by
    simp only [InLean.namesNodup, Bool.and_eq_true, Bool.not_eq_true', List.map_cons,
      List.nodup_cons, namesNodup_iff l]
    rw [← contains_map_toName, List.contains_eq_mem]
    simp

theorem trShape_allCtorNames (p : InLean.BlockShape) :
    (trShape p).allCtors.map (·.1.name) = (p.allCtors.map (·.1.name)).map toName := by
  simp only [trShape, ConLeche.BlockShape.allCtors, InLean.BlockShape.allCtors, List.map_flatten,
    List.map_map]
  congr 1
  apply List.map_congr_left
  intro ms _
  simp [trMember, trCtor]

theorem boolTrueName_tr : toName InLean.boolTrueName = ConLeche.boolTrueName := rfl
theorem boolFalseName_tr : toName InLean.boolFalseName = ConLeche.boolFalseName := rfl

/-! ## The stages, named -/

/-- A member whose terms have a closed reading. -/
@[expose] def MemberOk (ms : InLean.MemberShape) : Prop :=
  okC ms.cvT.type = true ∧ okC ms.declared.type = true ∧ ∀ c ∈ ms.ctors, okC c.1.type = true

/-- **One member's reduction** (`reduceMemberS_spec`'s twin): from the invariant
at `L`, InLean's `reduceMemberS` at `fe` answers master's `reduceMember` at the
translation. -/
@[expose] def ReduceMemberSimI : Prop :=
  ∀ (fe : InLean.FEnv) (L : ConLeche.Env) (nP : Nat) (ms ms' : InLean.MemberShape)
    (s₀ s' : InLean.CState),
    JobEnvI fe L → CSOKI .verified false L s₀ → MemberOk ms →
    InLean.reduceMemberS .verified fe ms nP s₀ = .ok (ms', s') →
    CSOKI .verified false L s' ∧ MemberOk ms' ∧
      Runs (ConLeche.reduceMember (ConLeche.fueledOpsM .verified) L (trMember ms) nP) (trMember ms')

/-- **The pass and the stages after it** (`checkBlockPassS_run` and
`checkBlockTailS_run` together, see the module docstring): from the residue,
InLean's pass at `fe` followed by its tail on the block is master's pure pass at
`L` on the translated shape, followed by master's tail on the translated block. -/
@[expose] def PassTailSimI : Prop :=
  ∀ (fe : InLean.FEnv) (L : ConLeche.Env) (block : List Lean.ConstantInfo) (p₀ : InLean.BlockShape)
    (isRec : Bool) (s₀ s' : InLean.CState),
    JobEnvI fe L → CSOKI .verified false L s₀ → (∀ ci ∈ block, CIRange ci) →
    (∀ ci ∈ block, isBlockKind ci = true ∧ okC ci.toConstantVal.type = true) →
    (∀ ms ∈ p₀.members, MemberOk ms) →
    (do let q ← InLean.checkBlockPassS .verified fe p₀ isRec; InLean.checkBlockTailS .verified block q)
      s₀ = .ok ((), s') →
    CSOKIF s' ∧ ∃ F q, ConLeche.checkBlockPass (ConLeche.fueledOps .verified F) L (trShape p₀) isRec
        = .ok q ∧ ConLeche.checkBlockTail (ConLeche.fueledOps .verified F) (block.map trCI) q = .ok ()

/-- **The members' reduction** (`reduceMembersS_run`'s twin), from one member's. -/
theorem reduceMembersSimI_of (hR : ReduceMemberSimI) {fe : InLean.FEnv} {L : ConLeche.Env}
    (hJ : JobEnvI fe L) {nP : Nat} :
    ∀ {l l' : List InLean.MemberShape} {s₀ s' : InLean.CState}, CSOKIF s₀ →
      (∀ ms ∈ l, MemberOk ms) →
      InLean.reduceMembersS .verified fe nP l s₀ = .ok (l', s') →
      CSOKIF s' ∧ (∀ ms ∈ l', MemberOk ms) ∧
        ∃ F, ConLeche.reduceMembers (ConLeche.fueledOps .verified F) L nP (l.map trMember) =
          .ok (l'.map trMember)
  | [], l', s₀, s', hs, _, h => by
    obtain ⟨rfl, rfl⟩ := pureI_ok h
    exact ⟨hs, by simp, 0, rfl⟩
  | ms :: rest, l', s₀, s', hs, hok, h => by
    unfold InLean.reduceMembersS at h
    obtain ⟨u0, sA, hfl0, h⟩ := bindI_ok h
    rw [flushI_run] at hfl0
    injection hfl0 with hfl0
    obtain rfl : s₀.flushed = sA := congrArg Prod.snd hfl0
    obtain ⟨m', s₁, hm, h⟩ := bindI_ok h
    obtain ⟨hs₁, hok₁, F₁, hF₁⟩ := hR fe L nP ms m' s₀.flushed s₁ hJ
      (flushI_csoki hs .verified false L) (hok ms List.mem_cons_self) hm
    obtain ⟨r', s₂, hr, h⟩ := bindI_ok h
    obtain ⟨hs₂, hokr, F₂, hF₂⟩ := reduceMembersSimI_of hR hJ hs₁.residue
      (fun m hm => hok m (List.mem_cons_of_mem _ hm)) hr
    obtain ⟨rfl, rfl⟩ := pureI_ok h
    refine ⟨hs₂, ?_, max F₁ F₂, ?_⟩
    · intro m hm
      rcases List.mem_cons.1 hm with rfl | hm
      · exact hok₁
      · exact hokr m hm
    have g₁ : ConLeche.reduceMember (ConLeche.fueledOps .verified (max F₁ F₂)) L (trMember ms) nP =
        .ok (trMember m') := by
      rw [← ConLeche.reduceMember_datF]; exact FueledM.up (Nat.le_max_left _ _) hF₁
    have g₂ : ConLeche.reduceMembers (ConLeche.fueledOps .verified (max F₁ F₂)) L nP
        (rest.map trMember) = .ok (r'.map trMember) := by
      rw [← ConLeche.reduceMembers_datF]
      exact FueledM.up (Nat.le_max_right _ _) (by rw [ConLeche.reduceMembers_datF]; exact hF₂)
    simp only [List.map_cons]
    unfold ConLeche.reduceMembers
    simp only [Bind.bind, Except.bind, g₁, g₂]
    rfl

theorem trShape_withMembers (p : InLean.BlockShape) (ms : List InLean.MemberShape) :
    trShape { p with members := ms } = { trShape p with members := ms.map trMember } := rfl

/-! ## A recognised shape's members have a closed reading -/

theorem blockSplitRecs_sub : ∀ {block : List Lean.ConstantInfo} {rs}, InLean.blockSplitRecs block = some rs →
    ∀ r ∈ rs, ∃ ci ∈ block, ci.toConstantVal = r.1
  | [], rs, h => by simp [InLean.blockSplitRecs] at h; subst h; simp
  | .recInfo v :: rest, rs, h => by
    simp only [InLean.blockSplitRecs, Option.map_eq_some_iff] at h
    obtain ⟨rs', h1, rfl⟩ := h
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · exact ⟨_, List.mem_cons_self, rfl⟩
    · obtain ⟨ci, hci, he⟩ := blockSplitRecs_sub h1 r hr
      exact ⟨ci, List.mem_cons_of_mem _ hci, he⟩
  | .inductInfo _ :: _, _, h | .ctorInfo _ :: _, _, h | .axiomInfo _ :: _, _, h
  | .defnInfo _ :: _, _, h | .thmInfo _ :: _, _, h | .opaqueInfo _ :: _, _, h
  | .quotInfo _ :: _, _, h => by simp [InLean.blockSplitRecs] at h

theorem blockSplitCtors_sub : ∀ {block : List Lean.ConstantInfo} {cs rs},
    InLean.blockSplitCtors block = some (cs, rs) → ∀ c ∈ cs, ∃ ci ∈ block, ci.toConstantVal = c.1
  | .ctorInfo v :: rest, cs, rs, h => by
    simp only [InLean.blockSplitCtors, Option.map_eq_some_iff] at h
    obtain ⟨q, h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨_, List.mem_cons_self, rfl⟩
    · obtain ⟨ci, hci, he⟩ := blockSplitCtors_sub h1 c hc
      exact ⟨ci, List.mem_cons_of_mem _ hci, he⟩
  | [], cs, rs, h | .recInfo _ :: _, cs, rs, h | .inductInfo _ :: _, cs, rs, h
  | .axiomInfo _ :: _, cs, rs, h | .defnInfo _ :: _, cs, rs, h | .thmInfo _ :: _, cs, rs, h
  | .opaqueInfo _ :: _, cs, rs, h | .quotInfo _ :: _, cs, rs, h => by
    unfold InLean.blockSplitCtors at h
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨_, _, rfl, _⟩ := h
    simp

theorem blockSplit_sub : ∀ {block : List Lean.ConstantInfo} {cvTs cs rs},
    InLean.blockSplit block = some (cvTs, cs, rs) →
    (∀ c ∈ cvTs, ∃ ci ∈ block, ci.toConstantVal = c) ∧ (∀ c ∈ cs, ∃ ci ∈ block, ci.toConstantVal = c.1)
  | .inductInfo v :: rest, cvTs, cs, rs, h => by
    simp only [InLean.blockSplit, Option.map_eq_some_iff] at h
    obtain ⟨q, h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, h3⟩ := h2
    obtain ⟨q1, q2, q3⟩ := q
    simp only [Prod.mk.injEq] at h3
    obtain ⟨rfl, rfl⟩ := h3
    obtain ⟨ih1, ih2⟩ := blockSplit_sub h1
    refine ⟨fun c hc => ?_, fun c hc => ?_⟩
    · rcases List.mem_cons.1 hc with rfl | hc
      · exact ⟨_, List.mem_cons_self, rfl⟩
      · obtain ⟨ci, hci, he⟩ := ih1 c hc
        exact ⟨ci, List.mem_cons_of_mem _ hci, he⟩
    · obtain ⟨ci, hci, he⟩ := ih2 c hc
      exact ⟨ci, List.mem_cons_of_mem _ hci, he⟩
  | [], cvTs, cs, rs, h | .recInfo _ :: _, cvTs, cs, rs, h | .ctorInfo _ :: _, cvTs, cs, rs, h
  | .axiomInfo _ :: _, cvTs, cs, rs, h | .defnInfo _ :: _, cvTs, cs, rs, h
  | .thmInfo _ :: _, cvTs, cs, rs, h | .opaqueInfo _ :: _, cvTs, cs, rs, h
  | .quotInfo _ :: _, cvTs, cs, rs, h => by
    unfold InLean.blockSplit at h
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨q, h1, rfl, rfl, rfl⟩ := h
    exact ⟨by simp, blockSplitCtors_sub h1⟩

theorem blockGroups_sub (names lps : List Lean.Name) (nP k : Nat)
    (cs : List (Lean.ConstantVal × Nat)) :
    ∀ g ∈ InLean.blockGroups names lps nP k cs, ∀ c ∈ g, c ∈ cs := by
  unfold InLean.blockGroups
  split
  · intro g hg c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg; exact hc
  · intro g hg c hc
    obtain ⟨m, _, rfl⟩ := List.mem_map.1 hg
    exact (List.mem_filter.1 hc).1

theorem members_ok {cvTs : List Lean.ConstantVal} {nIdxs : List Nat}
    {groups : List (List (Lean.ConstantVal × Nat))}
    (hT : ∀ c ∈ cvTs, okC c.type = true) (hG : ∀ g ∈ groups, ∀ c ∈ g, okC c.1.type = true) :
    ∀ ms ∈ ((cvTs.zip nIdxs).zip groups).map
      (fun a => ({ cvT := a.1.1, declared := a.1.1, nIdx := a.1.2, ctors := a.2 } :
        InLean.MemberShape)), MemberOk ms := by
  intro ms hms
  obtain ⟨⟨⟨c, n⟩, g⟩, ha, rfl⟩ := List.mem_map.1 hms
  have h1 := List.of_mem_zip ha
  have h2 := List.of_mem_zip h1.1
  exact ⟨hT c h2.1, hT c h2.1, fun x hx => hG g h1.2 x hx⟩

/-- **A recognised shape's members have a closed reading**, given the block's
types have one. -/
theorem blockShape?_memberOk {nP : Nat} {block : List Lean.ConstantInfo} {p : InLean.BlockShape}
    (hk : ∀ ci ∈ block, isBlockKind ci = true ∧ okC ci.toConstantVal.type = true)
    (h : InLean.blockShape? nP block = some p) : ∀ ms ∈ p.members, MemberOk ms := by
  cases hsp : InLean.blockSplit block with
  | none =>
    unfold InLean.blockShape? at h; rw [hsp] at h; cases h
  | some q =>
    obtain ⟨cvTs, cs, rs⟩ := q
    obtain ⟨h1, h2⟩ := blockSplit_sub hsp
    have hT : ∀ c ∈ cvTs, okC c.type = true := fun c hc => by
      obtain ⟨ci, hci, rfl⟩ := h1 c hc; exact (hk ci hci).2
    have hC : ∀ c ∈ cs, okC c.1.type = true := fun c hc => by
      obtain ⟨ci, hci, he⟩ := h2 c hc; rw [← he]; exact (hk ci hci).2
    have hG : ∀ (names lps : List Lean.Name) (k : Nat),
        ∀ g ∈ InLean.blockGroups names lps nP k (cs.map fun c => (c.1, c.2.2)), ∀ c ∈ g,
          okC c.1.type = true := by
      intro names lps k g hg c hc
      obtain ⟨c', hc', rfl⟩ := List.mem_map.1 (blockGroups_sub _ _ _ _ _ g hg c hc)
      exact hC c' hc'
    unfold InLean.blockShape? at h
    rw [hsp] at h
    cases cvTs with
    | nil => cases h
    | cons cvT0 tl =>
      cases rs with
      | nil => cases h
      | cons r0 rtl =>
        obtain ⟨cvR0, r0b⟩ := r0
        simp only at h
        cases hc : InLean.blockMemberCounts? nP (cvT0 :: tl).length cs.length
            ((cvT0 :: tl).map (·.name)) ((cvR0, r0b) :: rtl) 0 (cvT0 :: tl) with
        | none => rw [hc] at h; cases h
        | some nIdxs =>
          rw [hc] at h
          simp only at h
          split at h
          · revert h
            repeat' split
            all_goals intro h
            all_goals first
              | (cases h; done)
              | (simp only [Option.some.injEq] at h; subst h; exact members_ok hT (hG _ _ _))
          · cases h

/-- **The recognised block's job** (`checkBlockKS_run`'s twin) from the
members' reduction and the pass with its tail, given that a recognised
shape's members have a closed reading (`hMO`). -/
theorem blockKSSimI_of (hR : ReduceMemberSimI) (hPT : PassTailSimI)
    (hMO : ∀ nP block p, (∀ ci ∈ block, isBlockKind ci = true ∧ okC ci.toConstantVal.type = true) →
      InLean.blockShape? nP block = some p → ∀ ms ∈ p.members, MemberOk ms) : BlockKSSimI := by
  intro fe L block nP p s₀ s' hJ hs hr hk hsh h
  unfold InLean.checkBlockKS at h
  by_cases hnd : (InLean.namesNodup (p.allCtors.map (·.1.name)) &&
      InLean.namesNodup p.memberNames) = true
  case neg =>
    rw [ite_eq_right (by simpa using hnd)] at h
    obtain ⟨_, _, h1, _⟩ := bindI_ok h
    exact (throwI_ok h1).elim
  rw [ite_eq_left (by simpa using hnd)] at h
  simp only at h
  by_cases hbool : (!p.memberNames.contains InLean.boolTrueName &&
      !p.memberNames.contains InLean.boolFalseName) = true
  case neg =>
    rw [ite_eq_right (by simpa using hbool)] at h
    obtain ⟨_, _, h1, _⟩ := bindI_ok h
    exact (throwI_ok h1).elim
  rw [ite_eq_left (by simpa using hbool)] at h
  try simp only at h
  obtain ⟨ms, s₁, hms, h⟩ := bindI_ok h
  obtain ⟨hs₁, hokms, F₁, hF₁⟩ := reduceMembersSimI_of hR hJ hs (hMO nP block p hk hsh) hms
  obtain ⟨u0, sC, hfl, h⟩ := bindI_ok h
  rw [flushI_run] at hfl
  injection hfl with hfl
  obtain rfl : s₁.flushed = sC := congrArg Prod.snd hfl
  obtain ⟨hs', F₂, q, hP, hT⟩ := hPT fe L block { p with members := ms } (InLean.blockIsRec p)
    s₁.flushed s' hJ (flushI_csoki hs₁ .verified false L) hr hk hokms h
  refine ⟨hs', max F₁ F₂,
    L.pushDelta (ConLeche.blockConstants (trShape p)) (ConLeche.blockTables (trShape p) (trShape p).members),
    ?_⟩
  simp only [Bool.and_eq_true] at hnd hbool
  have hnd' : ((trShape p).allCtors.map (·.1.name)).Nodup ∧ (trShape p).memberNames.Nodup := by
    rw [trShape_allCtorNames, trShape_memberNames]
    exact ⟨(namesNodup_iff _).1 hnd.1, (namesNodup_iff _).1 hnd.2⟩
  have hbool' : ConLeche.boolTrueName ∉ (trShape p).memberNames ∧
      ConLeche.boolFalseName ∉ (trShape p).memberNames := by
    rw [trShape_memberNames, ← boolTrueName_tr, ← boolFalseName_tr]
    simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at hbool
    exact ⟨fun h => hbool.1 (List.mem_map.1 h |>.elim fun a ha => toName_inj ha.2 ▸ ha.1),
      fun h => hbool.2 (List.mem_map.1 h |>.elim fun a ha => toName_inj ha.2 ▸ ha.1)⟩
  have g₁ : ConLeche.reduceMembers (ConLeche.fueledOps .verified (max F₁ F₂)) L (trShape p).nP
      (trShape p).members = .ok (ms.map trMember) := by
    rw [← ConLeche.reduceMembers_datF]
    exact FueledM.up (Nat.le_max_left _ _) (by rw [ConLeche.reduceMembers_datF]; exact hF₁)
  have g₂ : ConLeche.checkBlockPass (ConLeche.fueledOps .verified (max F₁ F₂)) L
      { trShape p with members := ms.map trMember } (ConLeche.blockIsRec (trShape p)) = .ok q := by
    rw [blockIsRec_tr, ← trShape_withMembers, ← ConLeche.checkBlockPass_datF]
    exact FueledM.up (Nat.le_max_right _ _) (by rw [ConLeche.checkBlockPass_datF]; exact hP)
  have g₃ : ConLeche.checkBlockTail (ConLeche.fueledOps .verified (max F₁ F₂)) (block.map trCI) q =
      .ok () := by
    rw [← ConLeche.checkBlockTail_datF]
    exact FueledM.up (Nat.le_max_right _ _) (by rw [ConLeche.checkBlockTail_datF]; exact hT)
  unfold ConLeche.checkBlock
  simp only [hnd', hbool', and_self, ↓reduceIte, Bind.bind, Except.bind, g₁, g₂, g₃]
  rfl

end InLeanProof
