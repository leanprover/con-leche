module

public import ConLeche.Verify.Inductives.DirectInv
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

/-- A member's former stands as declared. -/
theorem checkBlockTele_former {env : Env} {nP : Nat} {ms : MemberShape}
    {cvTa : ConstantVal} {s : Level} {F : Nat}
    (h : checkBlockTele (fueledOps mode F) env nP ms = .ok (cvTa, s)) : cvTa = ms.cvT := by
  unfold checkBlockTele at h
  obtain ⟨u₀, -, h⟩ := exceptBind_ok h
  cases u₀
  try simp only at h
  obtain ⟨q, htele, h⟩ := exceptBind_ok h
  obtain ⟨cvTa', s'⟩ := q
  obtain ⟨rfl, -⟩ := checkSumTele_shape htele
  try simp only at h
  obtain ⟨r, hr, h⟩ := exceptBind_ok h
  obtain ⟨bs, tbody⟩ := r
  try simp only at h
  by_cases hc : (tbody == Expr.sort s') = true
  · rw [ite_eq_left hc] at h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.1.symm
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
theorem checkBlockInds_shape {env envI : Env} {p : BlockParts} {isRec : Bool}
    {cvTas : List ConstantVal} {p₁ : BlockShape} {F : Nat}
    (h : checkBlockInds (fueledOps mode F) env p isRec = .ok (envI, cvTas, p₁)) :
    ∃ (ms0 : MemberShape) (rest : List MemberShape) (cvTa0 : ConstantVal) (s0 : Level)
      (cvs : List (ConstantVal × Level)),
      p.members = ms0 :: rest ∧
      cvTas = cvTa0 :: cvs.map (·.1) ∧
      p₁ = p.toBlockShape.withSort s0 ∧
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
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨ms0, rest, cvTa0, s0, cvs, rfl, rfl, rfl, rfl, hq, hcvs, by cases u; exact hagree⟩

/-- **A member under check, against what the stream declares**: its former at its telescope is
the declared one where that shows a telescope, else the declared one's reduct, the declared type
checked and the two compared. -/
structure MemberAt (F : Nat) (env : Env) (nP : Nat) (m : MemberShape) : Prop where
  name : m.cvT.name = m.declared.name
  lps : m.cvT.levelParams = m.declared.levelParams
  how : (formerDefHeaded m.declared = false ∧ m.cvT = m.declared) ∨
    (formerDefHeaded m.declared = true ∧ litGuardFamilies.contains m.declared.name = false ∧
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
    by_cases hg : litGuardFamilies.contains m₀.cvT.name = true
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
      have hrf := (reducedFormer_closed hR).1
      refine ⟨⟨?_, ?_, .inr ?_⟩, rfl, rfl, rfl⟩
      · show cvR.name = m₀.declared.name
        rw [hd₀, hrf]
      · show cvR.levelParams = m₀.declared.levelParams
        rw [hd₀, hrf]
      · show formerDefHeaded m₀.declared = true ∧ litGuardFamilies.contains m₀.declared.name = false ∧
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
theorem checkBlockInds_members {env envI : Env} {p : BlockParts} {isRec : Bool}
    {cvTas : List ConstantVal} {p₁ : BlockShape} {F : Nat}
    (h : checkBlockInds (fueledOps mode F) env p isRec = .ok (envI, cvTas, p₁)) :
    cvTas = p.members.map (·.cvT) ∧ p₁.members = p.members := by
  obtain ⟨ms0, rest, cvTa0, s0, cvs, hm, rfl, rfl, -, hq, hcvs, -⟩ := checkBlockInds_shape h
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
  refine ⟨?_, rfl⟩
  rw [hm]
  have h0 : cvTa0 = ms0.cvT := hone hq
  simp [h0, hall hcvs]

/-- Every member's telescope was checked as a constant. -/
theorem checkBlockInds_checked {env envI : Env} {p : BlockParts} {isRec : Bool}
    {cvTas : List ConstantVal} {p₁ : BlockShape} {F : Nat}
    (h : checkBlockInds (fueledOps mode F) env p isRec = .ok (envI, cvTas, p₁)) :
    ∀ ms ∈ p.members, checkConstantVal (fueledOps mode F) env ms.cvT = .ok () := by
  obtain ⟨ms0, rest, cvTa0, s0, cvs, hm, -, -, -, hq, hcvs, -⟩ := checkBlockInds_shape h
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

/-- The checked formers are one per member. -/
theorem checkBlockInds_length {env envI : Env} {p : BlockParts} {isRec : Bool}
    {cvTas : List ConstantVal} {p₁ : BlockShape} {F : Nat}
    (h : checkBlockInds (fueledOps mode F) env p isRec = .ok (envI, cvTas, p₁)) :
    cvTas.length = p.k := by
  obtain ⟨ms0, rest, cvTa0, s0, cvs, hm, rfl, -, -, -, hcvs, -⟩ := checkBlockInds_shape h
  obtain ⟨hlen, -⟩ := checkBlockTeles_inv hcvs
  simp [BlockShape.k, hm, hlen]

/-! ## Stage 1b: the constructors, per member -/

/-- **Every member's constructors**, positionally: the sum route's
constructor loop at the member's own name and index count, at the
BLOCK's level parameters, parameter count, result sort and
elimination data (deviation D-e: official's
`Level.isEquiv` agreement makes the universe bound and the
subsingleton criterion the same test for every member). -/
theorem checkBlockCtors_inv {env₀ env : Env} {q : BlockShape} {F : Nat} :
    ∀ {l : List (MemberShape × ConstantVal)} {ctorsAs : List (List (ConstantVal × Nat))}
      {sortsss : List (List (List Level))},
      checkBlockCtors (fueledOps mode F) env₀ env q l = .ok (ctorsAs, sortsss) →
      ctorsAs.length = l.length ∧ sortsss.length = l.length ∧
      ∀ (i : Nat) (mc : MemberShape × ConstantVal), l[i]? = some mc →
        ∃ ctorsA sortss, ctorsAs[i]? = some ctorsA ∧ sortsss[i]? = some sortss ∧
          checkSumCtors (fueledOps mode F) env₀ env mc.1.cvT.name q.lps q.nP mc.1.nIdx
            q.resSort q.isProp q.large mc.2 mc.1.ctors = .ok (ctorsA, sortss)
  | [], ctorsAs, sortsss, h => by
    simp only [checkBlockCtors, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, fun i mc hmc => by simp at hmc⟩
  | (ms, cvTa) :: rest, ctorsAs, sortsss, h => by
    unfold checkBlockCtors at h
    obtain ⟨r, hr, h⟩ := exceptBind_ok h
    obtain ⟨ctorsA, sortss⟩ := r
    try simp only at h
    obtain ⟨r', hr', h⟩ := exceptBind_ok h
    obtain ⟨restC, restS⟩ := r'
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hlen, hlenS, hall⟩ := checkBlockCtors_inv hr'
    refine ⟨by simp [hlen], by simp [hlenS], ?_⟩
    intro i mc hmc
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hmc
      subst hmc
      exact ⟨ctorsA, sortss, rfl, rfl, hr⟩
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
theorem checkBlockPass_inv {env : Env} {p₀ : BlockParts} {isRec : Bool}
    {q : BlockPass Env} {F : Nat}
    (h : checkBlockPass (fueledOps mode F) env p₀ isRec = .ok q) :
    ∃ (p₁ : BlockShape) (ctx : NestCtx) (holes : List Expr) (pos st : NestState),
      checkBlockInds (fueledOps mode F) env p₀ isRec = .ok (q.env₁, q.cvTas, p₁) ∧
      checkBlockCtors (fueledOps mode F) q.env₁ q.env₁ (p₀.complete p₁).toBlockShape
        ((p₀.complete p₁).members.zip q.cvTas) = .ok (q.ctorsAs, q.sortsss) ∧
      blockNestCtx (m := CheckM) (p₀.complete p₁).toBlockShape q.cvTas q.env₁.find?
        = .ok (ctx, holes) ∧
      checkBlockClasses (fueledOps mode F) (mkFEnv q.env₁) (p₀.complete p₁).toBlockShape
        ctx.params q.ctorsAs = .ok (q.rd, q.cls) ∧
      checkBlockPositivity (m := CheckM) (fueledOps mode F) q.env₁ q.env₁.find?
        (p₀.complete p₁) q.cvTas q.ctorsAs = .ok (q.kinds, q.nfs, pos) ∧
      nestSeeds (fueledOps mode F) q.env₁ ctx (classSeeds ctx holes q.cls) pos = .ok st ∧
      q.params = ctx.params ∧ q.tbl = st.ctorNfs ∧
      q.p = p₀.complete p₁ := by
  unfold checkBlockPass at h
  obtain ⟨r₁, hInd, h⟩ := exceptBind_ok h
  obtain ⟨env₁, cvTas, p₁⟩ := r₁
  try simp only at h
  obtain ⟨r₂, hCtors, h⟩ := exceptBind_ok h
  obtain ⟨ctorsAs, sortsss⟩ := r₂
  try simp only at h
  obtain ⟨⟨ctx, holes⟩, hctx, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨⟨rd, Ms⟩, hcls, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨⟨kinds, nfs, pos⟩, hK, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨st, hst, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨p₁, ctx, holes, pos, st, hInd, hCtors, hctx, hcls, hK, hst, rfl, rfl, rfl⟩

/-! ## Stage 2: the tail -/

/-- Every member's index binders' sorts, positionally. -/
theorem checkBlockIdxSorts_inv {env₁ : Env} {q : BlockShape} {F : Nat} :
    ∀ {l : List (MemberShape × ConstantVal)} {isorts : List (List Level)},
      checkBlockIdxSorts (fueledOps mode F) env₁ q l = .ok isorts →
      isorts.length = l.length ∧
      ∀ (i : Nat) (mc : MemberShape × ConstantVal), l[i]? = some mc →
        ∃ is tfvs trest, isorts[i]? = some is ∧
          openPisAtFvars (q.nP + mc.1.nIdx) mc.2.type 0 = some (tfvs, trest) ∧
          checkStructFieldSortsI (fueledOps mode F) env₁ true false q.resSort q.nP
            (tfvs.drop q.nP) [] mc.1.nIdx = .ok is
  | [], isorts, h => by
    simp only [checkBlockIdxSorts, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun i mc hmc => by simp at hmc⟩
  | (ms, cvTa) :: rest, isorts, h => by
    unfold checkBlockIdxSorts at h
    obtain ⟨tq, htq, h⟩ := exceptBind_ok h
    have htq' := unwrapOr_ok htq
    obtain ⟨tfvs, trest⟩ := tq
    try simp only at h
    obtain ⟨is, his, h⟩ := exceptBind_ok h
    try simp only at h
    obtain ⟨rest', hrest, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hlen, hall⟩ := checkBlockIdxSorts_inv hrest
    refine ⟨by simp [hlen], ?_⟩
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

/-- **The tail, inverted**: every member's index binders' sorts, the
constructors consed,
the RECURSOR STAGE — left opaque, as `checkBlockRec … = .ok out` — the
stored recursors against the generated ones at the generated install
(`storedRecsCheck`, task #431), the stored recursors consed
with their rules at their majors, and the projection tables. -/
theorem checkBlockTail_inv {env₂ : Env} {block : List ConstantInfo} {q : BlockPass Env}
    {F : Nat}
    (h : checkBlockTail (m := CheckM) (fueledOps mode F) block q = .ok env₂) :
    ∃ (isorts : List (List Level))
      (out : List (ConstantVal × TargetMajor × List Expr)),
      checkBlockIdxSorts (fueledOps mode F) q.env₁ q.p.toBlockShape
        (q.p.members.zip q.cvTas) = .ok isorts ∧
      checkBlockRec (fueledOps mode F) (consBlockCtors q.p.nP q.ctorsAs q.env₁)
        q.p (blockNestedBit q.p.toBlockShape q.kinds) q.params q.tbl.toList q.rd q.cls block
          q.cvTas = .ok out ∧
      storedRecsCheck (m := CheckM) (fueledOps mode F) .plain
        (mkFEnv (consBlockRecsT q.p.toBlockShape 0 out (consBlockCtors q.p.nP q.ctorsAs q.env₁))) q.p.recs out
        = .ok () ∧
      checkBlockTables (m := CheckM) q.p.toBlockShape
        (q.p.members.zip (q.ctorsAs.zip q.sortsss))
        (consBlockRecsT q.p.toBlockShape 0
          (storedOut q.p.recs out) (consBlockCtors q.p.nP q.ctorsAs q.env₁)) = .ok env₂ := by
  rw [checkBlockTail] at h
  simp only [bind, Except.bind] at h
  try simp only [bind, Except.bind] at h
  cases hsorts : checkBlockIdxSorts (m := CheckM) (fueledOps mode F) q.env₁ q.p.toBlockShape
      (q.p.members.zip q.cvTas) with
  | error e => rw [hsorts] at h; exact nomatch h
  | ok isorts =>
  rw [hsorts] at h
  dsimp only at h
  cases hRec : checkBlockRec (m := CheckM) (fueledOps mode F)
      (consBlockCtors q.p.nP q.ctorsAs q.env₁) q.p
      (blockNestedBit q.p.toBlockShape q.kinds) q.params q.tbl.toList q.rd q.cls block
      q.cvTas with
  | error e => rw [hRec] at h; exact nomatch h
  | ok out =>
  rw [hRec] at h
  dsimp only at h
  cases hK : storedKCheck (m := CheckM) q.p.toBlockShape q.p.recs out with
  | error e => rw [hK] at h; exact nomatch h
  | ok uK =>
  rw [hK] at h
  dsimp only at h
  cases hS : storedRecsCheck (m := CheckM) (fueledOps mode F) .plain
      (mkFEnv (consBlockRecsT q.p.toBlockShape 0 out (consBlockCtors q.p.nP q.ctorsAs q.env₁))) q.p.recs out with
  | error e => rw [hS] at h; exact nomatch h
  | ok u =>
  cases u
  rw [hS] at h
  dsimp only at h
  exact ⟨isorts, out, rfl, rfl, hS, h⟩

end ConLeche
