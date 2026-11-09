module

public import ConLeche.Verify.Inductives.DirectInv
public import ConLeche.Verify.Inductives.PositivityInv
import ConLeche.Verify.Inductives.NestContInv
import ConLeche.Kernel.Inductives.BlockTail

public section

/-!
# The uniform install's stage runs, inverted at k members

Each stage of `checkBlock` (`ConLeche/Kernel/Inductives/BlockInstall.lean`)
read back as the facts the semantic and model tiers consume; the
per-member stages the block's loops call (`checkSumCtors_inv`) are
inverted in `DirectInv.lean`:

* **the formers** (`checkBlockTele_shape`, `checkBlockTeles_inv`,
  `checkBlockDomsAt_inv`, `checkBlockAgree_inv`,
  `checkBlockInds_shape`): the constant check and official's telescope
  loop per member, then — from member 1 on — official's two agreements
  (the parameter domains definitionally member 0's, the result sorts
  `Level.isEquiv`), and the k formers consed at once
  (`consBlockInds`), which is the environment every constructor is
  checked at;
* **the constructors** (`checkBlockCtors_inv`): `checkSumCtors` at
  every member, at that environment;
* **the pass** (`checkBlockPass_inv`), whose last stage is the
  positivity function's run (inverted in `PositivityInv.lean`);
* **the tail** (`checkBlockIdxSorts_inv`, `checkBlockTail_inv`).

The recursor stage stays OPAQUE here — `checkBlockTail_inv` exposes it
as `checkBlockRec … = .ok rs`; its run is read in `RecCheckRun.lean`.
-/

-- the `simp only` sets below are written for robustness against the
-- normal forms of the two sides, and several entries fire on one side only
set_option linter.unusedSimpArgs false

namespace ConLeche

variable {mode : CheckMode}

local syntax "close_throw" : tactic
local macro_rules
  | `(tactic| close_throw) =>
    `(tactic| first
        | (exfalso; exact structThrow_ne_ok (by assumption))
        | (exfalso; exact structThrow_ne_ok
            (by simpa [bind, Except.bind] using ‹_›)))

/-! ## Stage 1: the members' type formers -/

/-- One member's former, inverted, without the environment cons — at
k members nothing is consed before every former has been checked
(official's `declare_inductive_types`). -/
theorem checkBlockTele_shape {env : Env} {nP : Nat} {ms : MemberShape}
    {cvTa : ConstantVal} {s : Level} {F : Nat}
    (h : checkBlockTele (fueledOps mode F) env nP ms = .ok (cvTa, s)) :
    ∃ cvT : ConstantVal,
      cvT.name = ms.cvT.name ∧ cvT.levelParams = ms.cvT.levelParams ∧
      cvTa = cvT ∧ checkConstantVal (fueledOps mode F) env cvT = .ok () ∧
      ∃ bs, cvTa.type.stripPis (nP + ms.nIdx) = some (bs, .sort s) := by
  unfold checkBlockTele at h
  obtain ⟨u₀, hccv₀, h⟩ := exceptBind_ok h
  cases u₀
  try simp only at h
  obtain ⟨q, htele, h⟩ := exceptBind_ok h
  obtain ⟨cvTa', s'⟩ := q
  try simp only at h
  obtain ⟨r, hr, h⟩ := exceptBind_ok h
  obtain ⟨bs, tbody⟩ := r
  have hr' := unwrapOr_ok hr
  try simp only at h
  by_cases hc : (tbody == Expr.sort s') = true
  · rw [ite_eq_left hc] at h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hstrip : cvTa'.type.stripPis (nP + ms.nIdx) = some (bs, Expr.sort s') := by
      rw [hr', beq_iff_eq.mp hc]
    obtain ⟨rfl, -⟩ := checkSumTele_shape htele
    exact ⟨ms.cvT, rfl, rfl, rfl, hccv₀, bs, hstrip⟩
  · rw [ite_eq_right hc] at h
    close_throw

/-- The members' formers, positionally. -/
theorem checkBlockTeles_inv {env : Env} {nP : Nat} {F : Nat} :
    ∀ {mss : List MemberShape} {cvs : List (ConstantVal × Level)},
      checkBlockTeles (fueledOps mode F) env nP mss = .ok cvs →
      cvs.length = mss.length ∧
      ∀ (i : Nat) (ms : MemberShape), mss[i]? = some ms →
        ∃ q, cvs[i]? = some q ∧ checkBlockTele (fueledOps mode F) env nP ms = .ok q
  | [], cvs, h => by
    simp only [checkBlockTeles, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun i ms hms => by simp at hms⟩
  | ms :: rest, cvs, h => by
    unfold checkBlockTeles at h
    obtain ⟨q, hq, h⟩ := exceptBind_ok h
    try simp only at h
    obtain ⟨qs, hqs, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hlen, hall⟩ := checkBlockTeles_inv hqs
    refine ⟨by simp [hlen], ?_⟩
    intro i ms' hms'
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hms'
      subst hms'
      exact ⟨q, rfl, hq⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hms' ⊢
      exact hall i ms' hms'

/-- The parameter-domain agreement, positionally: every one of the
`nP` domains is definitionally member 0's. -/
theorem checkBlockDomsAt_inv {env : Env} {off : Nat} {fvs doms : List Expr} {F : Nat} :
    ∀ {j : Nat}, checkBlockDomsAt (fueledOps mode F) env off fvs doms j = .ok () →
      ∀ i, i < j → ∃ a b, fvs[i]? = some a ∧ doms[i]? = some b ∧
        isDefEqCore mode false env F (off + i) (Expr.fvarTypeD a) b = .ok true
  | 0, _ => fun i hi => absurd hi (Nat.not_lt_zero i)
  | j + 1, h => by
    unfold checkBlockDomsAt at h
    obtain ⟨a, ha, h⟩ := exceptBind_ok h
    have ha' := unwrapOr_ok ha
    try simp only at h
    obtain ⟨b, hb, h⟩ := exceptBind_ok h
    have hb' := unwrapOr_ok hb
    try simp only at h
    obtain ⟨bb, hbb, h⟩ := exceptBind_ok h
    cases bb with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      close_throw
    | true =>
    rw [ite_eq_left rfl] at h
    try simp only at h
    intro i hi
    rcases Nat.lt_or_ge i j with hij | hij
    · exact checkBlockDomsAt_inv h i hij
    · obtain rfl : i = j := by omega
      exact ⟨a, b, ha', hb', hbb⟩

/-- **Official's two agreements between the members**, inverted: every
member from 1 on opens to as many parameter binders as member 0, each
definitionally member 0's, and carries a result sort `Level.isEquiv` to
member 0's. -/
theorem checkBlockAgree_inv {env : Env} {nP : Nat} {cvTa0 : ConstantVal} {s0 : Level}
    {F : Nat} :
    ∀ {cvs : List (ConstantVal × Level)},
      checkBlockAgree (fueledOps mode F) env nP cvTa0 s0 cvs = .ok () →
      ∀ q ∈ cvs, (Level.isEquiv q.2 s0 == some true) = true ∧
        ∃ tfvs0 trest0 tfvs trest,
          openPisAtFvars nP cvTa0.type 0 = some (tfvs0, trest0) ∧
          openPisAtFvars nP q.1.type 0 = some (tfvs, trest) ∧
          tfvs.length = tfvs0.length ∧
          checkBlockDomsAt (fueledOps mode F) env 0 tfvs
            (tfvs0.map Expr.fvarTypeD) nP = .ok ()
  | [], _ => fun q hq => by simp at hq
  | (cvTa, s) :: rest, h => by
    unfold checkBlockAgree at h
    obtain ⟨q0, hq0, h⟩ := exceptBind_ok h
    have hq0' := unwrapOr_ok hq0
    obtain ⟨tfvs0, trest0⟩ := q0
    try simp only at h
    obtain ⟨q1, hq1, h⟩ := exceptBind_ok h
    have hq1' := unwrapOr_ok hq1
    obtain ⟨tfvs, trest⟩ := q1
    try simp only at h
    by_cases hl : (tfvs.length == tfvs0.length) = true
    case neg => rw [ite_eq_right hl] at h; close_throw
    rw [ite_eq_left hl] at h
    try simp only at h
    obtain ⟨u, hdoms, h⟩ := exceptBind_ok h
    try simp only at h
    obtain ⟨b, hb, h⟩ := exceptBind_ok h
    cases ho : Level.isEquiv s s0 with
    | none => rw [ho] at hb; exact nomatch hb
    | some b' =>
    rw [ho] at hb
    obtain rfl : b' = b := Except.ok.inj hb
    cases b' with
    | false => close_throw
    | true =>
    have hs : (Level.isEquiv s s0 == some true) = true := by simp [ho]
    try simp only [ite_true] at h
    intro q hq
    simp only [List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact ⟨hs, tfvs0, trest0, tfvs, trest, hq0', hq1', beq_iff_eq.mp hl,
        by cases u; exact hdoms⟩
    · exact checkBlockAgree_inv h q hq

/-- **Stage 1's shape**: member 0's former, the rest of the members'
formers, official's two agreements against member 0, the record
completed with member 0's result sort, and the k formers consed at
once — the environment every constructor is then checked at. -/
theorem checkBlockInds_shape {env envI : Env} {p : BlockShape} {isRec : Bool}
    {p₁ : BlockShape} {F : Nat}
    (h : checkBlockInds (fueledOps mode F) env p isRec = .ok (envI, p₁)) :
    ∃ (ms0 : MemberShape) (rest : List MemberShape) (cvTa0 : ConstantVal) (s0 : Level)
      (cvs : List (ConstantVal × Level)),
      p.members = ms0 :: rest ∧
      p₁ = p.withSort s0 ∧
      envI = consBlockInds p₁ isRec (p.members.map (·.declared)) 0 env ∧
      checkBlockTele (fueledOps mode F) env p.nP ms0 = .ok (cvTa0, s0) ∧
      checkBlockTeles (fueledOps mode F) env p.nP rest = .ok cvs ∧
      checkBlockAgree (fueledOps mode F) env p.nP cvTa0 s0 cvs = .ok () := by
  unfold checkBlockInds at h
  cases hm : p.members with
  | nil => rw [hm] at h; close_throw
  | cons ms0 rest =>
  rw [hm] at h
  try simp only at h
  obtain ⟨q, hq, h⟩ := exceptBind_ok h
  obtain ⟨cvTa0, s0⟩ := q
  try simp only at h
  obtain ⟨cvs, hcvs, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨u, hagree, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨ms0, rest, cvTa0, s0, cvs, rfl, rfl, rfl, hq, hcvs, by cases u; exact hagree⟩

/-- **A member under check, against what the stream declares**: its former at its telescope is
the declared one where that shows a telescope, else the declared one's reduct, the declared type
checked and the two compared. -/
structure MemberAt (F : Nat) (env : Env) (nP : Nat) (m : MemberShape) : Prop where
  name : m.cvT.name = m.declared.name
  lps : m.cvT.levelParams = m.declared.levelParams
  how : (formerDefHeaded m.declared = false ∧ m.cvT = m.declared) ∨
    (formerDefHeaded m.declared = true ∧ declinedAtDefinition.contains m.declared.name = false ∧
      checkConstantVal (fueledOps .verified F) env m.declared = .ok () ∧
      (fueledOps .verified F).isDefEq env 0 m.declared.type m.cvT.type = .ok true ∧
      reducedFormer (fueledOps .verified F) env m.declared (nP + m.nIdx) = .ok m.cvT)

/-- A member's reduction, inverted: the recogniser's member, at its telescope. -/
theorem reduceMember_inv {F : Nat} {env : Env} {nP : Nat} {m₀ m : MemberShape}
    (hd₀ : m₀.declared = m₀.cvT)
    (h : reduceMember (m := CheckM) (fueledOps .verified F) env m₀ nP = .ok m) :
    MemberAt F env nP m ∧ m.declared = m₀.declared ∧ m.nIdx = m₀.nIdx ∧ m.ctors = m₀.ctors := by
  unfold reduceMember at h
  by_cases hd : formerDefHeaded m₀.cvT = true
  · rw [ite_eq_left hd] at h
    by_cases hg : declinedAtDefinition.contains m₀.cvT.name = true
    · rw [ite_eq_left hg] at h
      exact nomatch h
    rw [ite_eq_right hg] at h
    obtain ⟨u₁, h₁, h⟩ := exceptBind_ok h
    cases u₁
    obtain ⟨cvR, hR, h⟩ := exceptBind_ok h
    obtain ⟨b, hb, h⟩ := exceptBind_ok h
    cases b with
    | false => simp [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at h
    | true =>
      simp only [pure, Except.pure, Except.ok.injEq, ↓reduceIte] at h
      subst h
      have hrf := reducedFormer_cv hR
      refine ⟨⟨?_, ?_, .inr ?_⟩, rfl, rfl, rfl⟩
      · show cvR.name = m₀.declared.name
        rw [hd₀, hrf]
      · show cvR.levelParams = m₀.declared.levelParams
        rw [hd₀, hrf]
      · show formerDefHeaded m₀.declared = true ∧ declinedAtDefinition.contains m₀.declared.name = false ∧
          checkConstantVal (fueledOps .verified F) env m₀.declared = .ok () ∧
          (fueledOps .verified F).isDefEq env 0 m₀.declared.type cvR.type = .ok true ∧
          reducedFormer (fueledOps .verified F) env m₀.declared (nP + m₀.nIdx) = .ok cvR
        rw [hd₀]
        exact ⟨hd, by simpa using hg, h₁, hb, hR⟩
  · rw [ite_eq_right hd] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨⟨by rw [hd₀], by rw [hd₀], .inl ⟨?_, hd₀.symm⟩⟩, rfl, rfl, rfl⟩
    rw [hd₀]; simpa using hd

/-- The members' reduction, inverted. -/
theorem reduceMembers_inv {F : Nat} {env : Env} {nP : Nat} :
    ∀ {l l' : List MemberShape}, (∀ m ∈ l, m.declared = m.cvT) →
      reduceMembers (m := CheckM) (fueledOps .verified F) env nP l = .ok l' →
      (∀ m ∈ l', MemberAt F env nP m) ∧ l'.map (·.declared) = l.map (·.declared) ∧
        l'.map (·.cvT.name) = l.map (·.cvT.name) ∧ l'.map (·.nIdx) = l.map (·.nIdx) ∧
        l'.map (·.ctors) = l.map (·.ctors)
  | [], l', _, h => by
    simp only [reduceMembers, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp
  | m₀ :: rest, l', hd, h => by
    unfold reduceMembers at h
    obtain ⟨m', hm', h⟩ := exceptBind_ok h
    obtain ⟨r', hr', h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have hd₀ := hd m₀ List.mem_cons_self
    obtain ⟨ha, h₁, h₃, h₄⟩ := reduceMember_inv hd₀ hm'
    obtain ⟨hall, e₁, e₂, e₃, e₄⟩ := reduceMembers_inv (fun m hm => hd m (List.mem_cons_of_mem _ hm)) hr'
    refine ⟨fun m hm => ?_, by simp [h₁, e₁], ?_, by simp [h₃, e₃], by simp [h₄, e₄]⟩
    · rcases List.mem_cons.mp hm with rfl | hm
      · exact ha
      · exact hall m hm
    · simp only [List.map_cons, e₂, List.cons.injEq, and_true]
      rw [ha.name, h₁, hd₀]

/-- The checked formers are the members' telescopes, and the shape keeps the members. -/
theorem checkBlockInds_members {env envI : Env} {p : BlockShape} {isRec : Bool}
    {p₁ : BlockShape} {F : Nat}
    (h : checkBlockInds (fueledOps mode F) env p isRec = .ok (envI, p₁)) :
    p₁.members = p.members := by
  obtain ⟨ms0, rest, cvTa0, s0, cvs, hm, rfl, -, hq, hcvs, -⟩ := checkBlockInds_shape h
  rfl

/-- The checked teles are the members' formers. -/
theorem checkBlockInds_teles {env : Env} {p : BlockShape} {F : Nat}
    {ms0 : MemberShape} {rest : List MemberShape} {cvTa0 : ConstantVal} {s0 : Level}
    {cvs : List (ConstantVal × Level)} (hm : p.members = ms0 :: rest)
    (hq : checkBlockTele (fueledOps mode F) env p.nP ms0 = .ok (cvTa0, s0))
    (hcvs : checkBlockTeles (fueledOps mode F) env p.nP rest = .ok cvs) :
    cvTa0 :: cvs.map (·.1) = p.formers := by
  have hone : ∀ {ms : MemberShape} {x : ConstantVal × Level},
      checkBlockTele (fueledOps mode F) env p.nP ms = .ok x → x.1 = ms.cvT := by
    intro ms x hx
    obtain ⟨cv, s⟩ := x
    unfold checkBlockTele at hx
    obtain ⟨_, -, hx⟩ := exceptBind_ok hx
    obtain ⟨q, htele, hx⟩ := exceptBind_ok hx
    obtain ⟨cvTa', s'⟩ := q
    obtain ⟨r, -, hx⟩ := exceptBind_ok hx
    obtain ⟨rfl, -⟩ := checkSumTele_shape htele
    obtain ⟨bs, tbody⟩ := r
    try simp only at hx
    by_cases hc : (tbody == Expr.sort s') = true
    · rw [ite_eq_left hc] at hx
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hx
      exact hx.1.symm
    · rw [ite_eq_right hc] at hx
      close_throw
  have hall : ∀ {l : List MemberShape} {xs : List (ConstantVal × Level)},
      checkBlockTeles (fueledOps mode F) env p.nP l = .ok xs → xs.map (·.1) = l.map (·.cvT) := by
    intro l
    induction l with
    | nil => intro xs hx; simp only [checkBlockTeles, pure, Except.pure, Except.ok.injEq] at hx; subst hx; rfl
    | cons ms l ih =>
      intro xs hx
      unfold checkBlockTeles at hx
      obtain ⟨y, hy, hx⟩ := exceptBind_ok hx
      obtain ⟨ys, hys, hx⟩ := exceptBind_ok hx
      simp only [pure, Except.pure, Except.ok.injEq] at hx
      subst hx
      simp [hone hy, ih hys]
  show _ = p.members.map _
  rw [hm]
  have h0 : cvTa0 = ms0.cvT := hone hq
  simp [h0, hall hcvs]

/-- Every member's telescope was checked as a constant. -/
theorem checkBlockInds_checked {env envI : Env} {p : BlockShape} {isRec : Bool}
    {p₁ : BlockShape} {F : Nat}
    (h : checkBlockInds (fueledOps mode F) env p isRec = .ok (envI, p₁)) :
    ∀ ms ∈ p.members, checkConstantVal (fueledOps mode F) env ms.cvT = .ok () := by
  obtain ⟨ms0, rest, cvTa0, s0, cvs, hm, -, -, hq, hcvs, -⟩ := checkBlockInds_shape h
  have hone : ∀ {ms : MemberShape} {x : ConstantVal × Level},
      checkBlockTele (fueledOps mode F) env p.nP ms = .ok x →
      checkConstantVal (fueledOps mode F) env ms.cvT = .ok () := by
    intro ms x hx
    unfold checkBlockTele at hx
    obtain ⟨u, hu, -⟩ := exceptBind_ok hx
    cases u
    exact hu
  have hall : ∀ {l : List MemberShape} {xs : List (ConstantVal × Level)},
      checkBlockTeles (fueledOps mode F) env p.nP l = .ok xs →
      ∀ ms ∈ l, checkConstantVal (fueledOps mode F) env ms.cvT = .ok () := by
    intro l
    induction l with
    | nil => intro _ _ _ hm; exact nomatch hm
    | cons ms l ih =>
      intro xs hx m hm
      unfold checkBlockTeles at hx
      obtain ⟨y, hy, hx⟩ := exceptBind_ok hx
      obtain ⟨ys, hys, -⟩ := exceptBind_ok hx
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hone hy
      · exact ih hys m hm
  intro m hmm
  rw [hm] at hmm
  rcases List.mem_cons.mp hmm with rfl | hmm
  · exact hone hq
  · exact hall hcvs m hmm

/-! ## Stage 1b: the constructors, per member -/

/-- **What an accepting constructor stage establishes**, positionally: the sum route's
constructor loop at the member's own name and index count, at the
BLOCK's level parameters, parameter count, result sort and
elimination data, with the constructors' fields' sorts. -/
abbrev BlockCtorsRun (mode : CheckMode) (F : Nat) (env₀ env : Env) (q : BlockShape)
    (l : List MemberShape) (sortsss : List (List (List Level))) : Prop :=
  sortsss.length = l.length ∧
  ∀ (i : Nat) (ms : MemberShape), l[i]? = some ms →
    ∃ sortss, sortsss[i]? = some sortss ∧
      SumCtorsRun mode F env₀ env ms.cvT.name q.lps q.nP ms.nIdx
        q.resSort q.isProp q.large ms.cvT ms.ctors ms.ctors sortss

/-- **Every member's constructors**, positionally. -/
theorem checkBlockCtors_inv {env₀ env : Env} {q : BlockShape} {F : Nat} :
    ∀ {l : List MemberShape},
      checkBlockCtors (fueledOps mode F) env₀ env q l = .ok () →
      ∃ sortsss, BlockCtorsRun mode F env₀ env q l sortsss
  | [], _ => ⟨[], rfl, fun i ms hmc => by simp at hmc⟩
  | ms :: rest, h => by
    unfold checkBlockCtors at h
    obtain ⟨u, hr, h⟩ := exceptBind_ok h
    cases u
    obtain ⟨sortss, hS⟩ := checkSumCtors_inv hr
    obtain ⟨restS, hlenS, hall⟩ := checkBlockCtors_inv h
    refine ⟨sortss :: restS, by simp [hlenS], ?_⟩
    intro i mc hmc
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hmc
      subst hmc
      exact ⟨sortss, rfl, hS⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hmc ⊢
      exact hall i mc hmc

/-! ## The pass -/

/-- **One pass's shape at k members**: the k formers' run at the record at the verdict `isRec`,
the constructors' runs per member at the environment holding ALL the
formers, the walk's context, the classes (`checkBlockClasses`), the
positivity function's run on the stored constructors (the root frame),
the walk of the outside classes from its state, and the record
completed. -/
theorem checkBlockPass_inv {env : Env} {p₀ : BlockShape} {isRec : Bool}
    {q : BlockPass Env} {F : Nat}
    (h : checkBlockPass (fueledOps mode F) env p₀ isRec = .ok q) :
    ∃ (sortsss : List (List (List Level))) (nfs : List (List Expr)) (ctx : NestCtx)
      (holes : List Expr) (pos st : NestState),
      checkBlockInds (fueledOps mode F) env p₀ isRec = .ok (q.env₁, q.p) ∧
      BlockCtorsRun mode F q.env₁ q.env₁ q.p q.p.members sortsss ∧
      blockNestCtx (m := CheckM) q.p q.env₁.find? = .ok (ctx, holes) ∧
      checkBlockClasses (fueledOps mode F) (mkFEnv q.env₁) q.p
        ctx.params = .ok (q.rd, q.cls) ∧
      PositivityRun (fueledOps mode F) q.env₁ q.env₁.find? q.p q.kinds nfs pos ∧
      nestSeeds (fueledOps mode F) q.env₁ ctx (classSeeds ctx holes q.cls) pos = .ok st ∧
      q.params = ctx.params ∧ q.tbl = st.ctorNfs := by
  unfold checkBlockPass at h
  obtain ⟨r₁, hInd, h⟩ := exceptBind_ok h
  obtain ⟨env₁, p₁⟩ := r₁
  try simp only at h
  obtain ⟨u, hCtors, h⟩ := exceptBind_ok h
  cases u
  obtain ⟨sortsss, hCtors⟩ := checkBlockCtors_inv hCtors
  obtain ⟨⟨ctx, holes⟩, hctx, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨⟨rd, Ms⟩, hcls, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨⟨outs, pos⟩, hK, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨st, hst, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨sortsss, outs.map (·.map (·.2)), ctx, holes, pos, st, hInd, hCtors, hctx, hcls,
    ⟨outs, hK, rfl, rfl⟩, hst, rfl, rfl⟩

/-! ## Stage 2: the tail -/

/-- **What an accepting index-sorts stage establishes**, positionally: every member's index binders'
sorts. -/
abbrev BlockIdxSortsRun (mode : CheckMode) (F : Nat) (env₁ : Env) (q : BlockShape)
    (l : List MemberShape) (isorts : List (List Level)) : Prop :=
  isorts.length = l.length ∧
  ∀ (i : Nat) (ms : MemberShape), l[i]? = some ms →
    ∃ is tfvs trest, isorts[i]? = some is ∧
      openPisAtFvars (q.nP + ms.nIdx) ms.cvT.type 0 = some (tfvs, trest) ∧
      FieldSorts mode F env₁ true false q.resSort q.nP (tfvs.drop q.nP) [] ms.nIdx is

/-- Every member's index binders' sorts, positionally. -/
theorem checkBlockIdxSorts_inv {env₁ : Env} {q : BlockShape} {F : Nat} :
    ∀ {l : List MemberShape},
      checkBlockIdxSorts (fueledOps mode F) env₁ q l = .ok () →
      ∃ isorts, BlockIdxSortsRun mode F env₁ q l isorts
  | [], _ => ⟨[], rfl, fun i mc hmc => by simp at hmc⟩
  | ms :: rest, h => by
    unfold checkBlockIdxSorts at h
    obtain ⟨tq, htq, h⟩ := exceptBind_ok h
    have htq' := unwrapOr_ok htq
    obtain ⟨tfvs, trest⟩ := tq
    try simp only at h
    obtain ⟨u, his, h⟩ := exceptBind_ok h
    cases u
    obtain ⟨is, his⟩ := checkStructFieldSortsI_inv his
    obtain ⟨rest', hlen, hall⟩ := checkBlockIdxSorts_inv h
    refine ⟨is :: rest', by simp [hlen], ?_⟩
    intro i mc hmc
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hmc
      subst hmc
      exact ⟨is, tfvs, trest, rfl, htq', his⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hmc ⊢
      exact hall i mc hmc

/-! ## The install after the pass -/

/-- The tables' stage, inverted: each table's checks passed. -/
theorem checkBlockTables_inv {env : Env} :
    ∀ {Q : List ProjTable}, checkBlockTables (m := CheckM) env Q = .ok () →
      ∀ t ∈ Q, checkStructProjTable (m := CheckM) t env = .ok ()
  | [], _, _, ht => nomatch ht
  | _ :: _, h, t', ht => by
    unfold checkBlockTables at h
    obtain ⟨u, hu, h⟩ := exceptBind_ok h
    rcases List.mem_cons.mp ht with rfl | ht'
    · cases u
      exact hu
    · exact checkBlockTables_inv h t' ht'

/-! ## The install does not read the telescope a former was reduced to -/

theorem getD_map_congr {α β : Type} [Inhabited α] {f : α → β} {l l' : List α} (h : l.map f = l'.map f)
    (i : Nat) : f (l.getD i default) = f (l'.getD i default) := by
  have hi := congrArg (·[i]?) h
  simp only [List.getElem?_map] at hi
  simp only [List.getD_eq_getElem?_getD]
  cases h₁ : l[i]? <;> cases h₂ : l'[i]? <;> simp_all

theorem blockCapsAt_congr {p q : BlockShape} (hnP : p.nP = q.nP)
    (hnm : p.memberNames = q.memberNames)
    (hc : p.members.map (·.ctors) = q.members.map (·.ctors))
    (hi : p.members.map (·.nIdx) = q.members.map (·.nIdx)) (mi : Nat) (isRec : Bool) :
    blockCapsAt p mi isRec = blockCapsAt q mi isRec := by
  unfold blockCapsAt
  rw [getD_map_congr hc mi, getD_map_congr hi mi, hnP, hnm]

theorem blockRecs_congr {p q : BlockShape} (hk : p.k = q.k) :
    ∀ l : List RecShape, blockRecs p l = blockRecs q l
  | [] => rfl
  | rc :: rest => by
    have hf : recFire p rc = recFire q rc := by
      unfold recFire
      rw [hk]
    simp only [blockRecs, hf, blockRecs_congr hk rest]

theorem blockTables_congr {p q : BlockShape} (hnP : p.nP = q.nP) (hlps : p.lps = q.lps) :
    ∀ {l l' : List MemberShape}, l.map (·.declared) = l'.map (·.declared) →
      l.map (·.ctors) = l'.map (·.ctors) → l.map (·.nIdx) = l'.map (·.nIdx) →
      blockTables p l = blockTables q l'
  | [], [], _, _, _ => rfl
  | [], _ :: _, h, _, _ => nomatch h
  | _ :: _, [], h, _, _ => nomatch h
  | a :: l, b :: l', hd, hc, hi => by
    simp only [List.map_cons, List.cons.injEq] at hd hc hi
    have hs : a.structCtor? = b.structCtor? := by
      unfold MemberShape.structCtor?
      rw [hc.1, hi.1]
    simp only [blockTables, hs, hd.1, hnP, hlps, blockTables_congr hnP hlps hd.2 hc.2 hi.2]

/-- **What a reduction of its formers leaves of a block's install**: nothing changes. -/
theorem blockInstall_reduced {F : Nat} {env : Env} {p₀ : BlockShape} {ms : List MemberShape}
    (hd : ∀ m ∈ p₀.members, m.declared = m.cvT)
    (h : reduceMembers (m := CheckM) (fueledOps .verified F) env p₀.nP p₀.members = .ok ms) :
    blockConstants { p₀ with members := ms } = blockConstants p₀ ∧
    blockTables ({ p₀ with members := ms } : BlockShape) ms
      = blockTables p₀ p₀.members := by
  obtain ⟨hAt, hdecl, hname, hidx, hctors⟩ := reduceMembers_inv hd h
  have hnm : ({ p₀ with members := ms } : BlockShape).memberNames = p₀.memberNames := hname
  have hcaps : ∀ i r, blockCapsAt ({ p₀ with members := ms } : BlockShape) i r
      = blockCapsAt p₀ i r := fun i r =>
    blockCapsAt_congr (p := ({ p₀ with members := ms } : BlockShape))
      (q := p₀) rfl hnm hctors hidx i r
  have hlen : ms.length = p₀.members.length := by
    simpa using congrArg List.length hdecl
  have hrec : blockIsRec ({ p₀ with members := ms } : BlockShape) = blockIsRec p₀ := by
    unfold blockIsRec
    show (ms.any _) = (p₀.members.any _)
    rw [hnm]
    have e : ∀ (l : List MemberShape) (g : List (ConstantVal × Nat) → Bool),
        l.any (fun m => g m.ctors) = (l.map (·.ctors)).any g := by
      intro l g; induction l <;> simp_all
    exact (e ms fun cs => cs.any fun c => Expr.piDomsMentionAny p₀.memberNames c.1.type).trans
      (by rw [hctors]; exact (e p₀.members _).symm)
  have hall : ({ p₀ with members := ms } : BlockShape).allCtors
      = p₀.allCtors := by
    show (ms.map (·.ctors)).flatten = (p₀.members.map (·.ctors)).flatten
    rw [hctors]
  have hlps : ({ p₀ with members := ms } : BlockShape).lps = p₀.lps := by
    show (ms.head?.map (·.cvT.levelParams)).getD [] = (p₀.members.head?.map (·.cvT.levelParams)).getD []
    cases hm : ms with
    | nil =>
      rw [hm] at hlen
      cases hp : p₀.members with
      | nil => rfl
      | cons _ _ => simp [hp] at hlen
    | cons a as =>
      cases hp : p₀.members with
      | nil => simp [hm, hp] at hlen
      | cons b bs =>
        rw [hm, hp] at hdecl
        simp only [List.map_cons, List.cons.injEq] at hdecl
        show a.cvT.levelParams = b.cvT.levelParams
        rw [(hAt a (by rw [hm]; exact List.mem_cons_self)).lps, hdecl.1,
          hd b (by rw [hp]; exact List.mem_cons_self)]
  refine ⟨?_, blockTables_congr (p := ({ p₀ with members := ms } : BlockShape))
    (q := p₀) rfl hlps hdecl hctors hidx⟩
  unfold blockConstants blockFormers blockCtors
  simp only [hrec, hall, hcaps]
  rw [blockRecs_congr (p := ({ p₀ with members := ms } : BlockShape))
    (q := p₀) hlen]
  show ((ms.map (·.declared)).zipIdx.map _) ++ _ ++ _ =
    ((p₀.members.map (·.declared)).zipIdx.map _) ++ _ ++ _
  rw [hdecl]

/-- **The tail, inverted**: every member's index binders' sorts, the
constructors consed,
the RECURSOR STAGE — left opaque, as `checkBlockRec … = .ok out` — the
stored recursors against the generated ones at the generated install
(`streamRecsCheck`, task #431), the stored recursors consed
with their rules at their majors, and the projection tables. -/
theorem checkBlockTail_inv {block : List ConstantInfo} {q : BlockPass Env} {Q : List ProjTable}
    {F : Nat} (h : checkBlockTail (m := CheckM) (fueledOps mode F) block q Q = .ok ()) :
    ∃ (isorts : List (List Level))
      (out : List (ConstantVal × TargetMajor × List Expr)),
      BlockIdxSortsRun mode F q.env₁ q.p q.p.members isorts ∧
      checkBlockRec (fueledOps mode F) (consBlockCtors q.p.nP q.p.memberCtors q.env₁)
        q.p (blockNestedBit q.p q.kinds) q.params q.tbl.toList q.rd q.cls block = .ok out ∧
      streamKCheck (m := CheckM) q.p q.p.recs out = .ok () ∧
      streamRecsCheck (m := CheckM) (fueledOps mode F) .plain
        (mkFEnv (consBlockRecsT q.p 0 out (consBlockCtors q.p.nP q.p.memberCtors q.env₁))) q.p.recs out
        = .ok () ∧
      checkBlockTables (m := CheckM) (consBlockCtors q.p.nP q.p.memberCtors q.env₁) Q
        = .ok () := by
  rw [checkBlockTail] at h
  simp only [bind, Except.bind] at h
  cases hsorts : checkBlockIdxSorts (m := CheckM) (fueledOps mode F) q.env₁ q.p
      q.p.members with
  | error e => rw [hsorts] at h; exact nomatch h
  | ok u =>
  cases u
  rw [hsorts] at h
  dsimp only at h
  obtain ⟨isorts, hIs⟩ := checkBlockIdxSorts_inv hsorts
  cases hRec : checkBlockRec (m := CheckM) (fueledOps mode F)
      (consBlockCtors q.p.nP q.p.memberCtors q.env₁) q.p
      (blockNestedBit q.p q.kinds) q.params q.tbl.toList q.rd q.cls block with
  | error e => rw [hRec] at h; exact nomatch h
  | ok out =>
  rw [hRec] at h
  dsimp only at h
  cases hK : streamKCheck (m := CheckM) q.p q.p.recs out with
  | error e => rw [hK] at h; exact nomatch h
  | ok uK =>
  cases uK
  rw [hK] at h
  dsimp only at h
  cases hS : streamRecsCheck (m := CheckM) (fueledOps mode F) .plain
      (mkFEnv (consBlockRecsT q.p 0 out (consBlockCtors q.p.nP q.p.memberCtors q.env₁))) q.p.recs out with
  | error e => rw [hS] at h; exact nomatch h
  | ok u =>
  cases u
  rw [hS] at h
  dsimp only at h
  exact ⟨isorts, out, hIs, rfl, hK, hS, h⟩

end ConLeche
