module

public import ConLeche.Verify.Ground.SimStep
import ConLeche.Verify.Ground.SimStep1
public import ConLeche.Verify.Ground.SimBridge
public import ConLeche.Verify.EnvWF
import ConLeche.Verify.Ground.Keys
import ConLeche.Verify.Ground.SimExt
import ConLeche.Verify.Ground.SimFrames
import ConLeche.Verify.Ground.SimStep3
import ConLeche.Verify.Ground.SimStep1P
import ConLeche.Verify.Ground.Step1
import ConLeche.Verify.Ground.Step1I

public section

/-!
# The step simulation, mode 1: the ι frame (task #423 soundness, layer (d), item 2(c))

The frame's entries are related recursor entries (`FsRel.iotaTop`), the
returned constructor's related constructor entries: one rule list, one
offset of the rule found (`findRule_rel` over the rows' name ids), the rule
rows' words one (`RowOK.rel`; the case-3 flag by `LookAgree.case3`).  The
right-hand side's compile comes in four combinations, as the δ compile of
mode 3: `I1` says the dispatch reaches the compile test, `run_iota_comp`
is the compile's stutter, `sim_mode1i'` takes the paths where both sides
have the code or the dispatch stops earlier.
-/

namespace ConLeche.Verify.Ground

open ConLeche

/-- The rule row the ι frame's dispatch finds. -/
@[expose] def iotaRi (s : MS) : Nat :=
  g4FindRule s.P.rNid s.P.kB[s.val[g4X4 s.x + 1]!]! s.P.kD[s.fs[s.fs.size - 4]!]! s.P.kC[s.fs[s.fs.size - 4]!]!

/-- **The ι frame's dispatch reaches the right-hand side's test**: a
constructor value whose rule is found, of the rule's arity, outside case 3. -/
@[expose] def I1 (s : MS) : Prop :=
  s.val[g4X4 s.x]! = 1 ∧ s.P.kTag[s.val[g4X4 s.x + 1]!]! = 1 ∧
    iotaRi s ≠ s.P.kC[s.fs[s.fs.size - 4]!]! + s.P.kD[s.fs[s.fs.size - 4]!]! ∧
    s.val[g4X4 s.x + 3]! = s.P.rCP[iotaRi s]! + s.P.rNF[iotaRi s]! ∧ s.P.rC3[iotaRi s]! = 0

/-- The rule compile's program: the right-hand side compiled, its node
stored on the row. -/
@[expose] def compRule (f : Name → Option ConstantInfo) (p : Name → Nat → Option ProjEntry) (P : G4Prog)
    (ri : Nat) (t : Expr) : G4Prog :=
  { (g4Comp f p P t).2 with ruleCode := (g4Comp f p P t).2.ruleCode.set! ri ((g4Comp f p P t).1 + 1) }

/-- **The rule compile on both sides keeps lock-step**: both store rule `d`
of recursors of one key. -/
theorem CodeSame.iota {fA fB : Name → Option ConstantInfo} {pA pB : Name → Nat → Option ProjEntry}
    {PA PB : G4Prog} (hcs : CodeSame PA PB) (hIA : Inv fA pA PA) (hIB : Inv fB pB PB) {kA kB : Nat}
    {c : Name} {lps lps' : List Name} {us : List Level} {mI rP bA nA mI' rP' bB nB : Nat}
    {isK isEta isK' isEta' : Bool}
    (hiA : PA.kInfo[kA]? = some (.recr c lps us mI rP bA nA isK isEta))
    (hiB : PB.kInfo[kB]? = some (.recr c lps' us mI' rP' bB nB isK' isEta')) {d : Nat} (hdA : d < nA)
    (hdB : d < nB) {riA riB : Nat} (eA : riA = bA + d) (eB : riB = bB + d) (tA tB : Expr) :
    CodeSame (compRule fA pA PA riA tA) (compRule fB pB PB riB tB) := by
  subst eA eB
  have cA := g4Comp_spec fA pA PA tA hIA
  have cB := g4Comp_spec fB pB PB tB hIB
  unfold compRule
  generalize g4Comp fA pA PA tA = rA at cA ⊢
  generalize g4Comp fB pB PB tB = rB at cB ⊢
  obtain ⟨oA, QA⟩ := rA
  obtain ⟨oB, QB⟩ := rB
  obtain ⟨hIA1, hxA, -⟩ := cA
  obtain ⟨hIB1, hxB, -⟩ := cB
  have hq := hcs.ext hIA.toTabInv hIB.toTabInv hxA hxB
  have qA := hxA.kInfo_some hiA
  have qB := hxB.kInfo_some hiB
  have hrA : bA + d < QA.ruleCode.size := by
    rw [hIA1.szs.2.1.1]
    exact hIA1.toTabInv.rows_lt ⟨_, _, _, _, _, _, _, _, _, qA, Nat.le_add_right _ _, by omega⟩
  have hrB : bB + d < QB.ruleCode.size := by
    rw [hIB1.szs.2.1.1]
    exact hIB1.toTabInv.rows_lt ⟨_, _, _, _, _, _, _, _, _, qB, Nat.le_add_right _ _, by omega⟩
  refine ⟨fun κ => hq.1 κ, fun κ d' => ?_⟩
  dsimp only
  rw [ruleK_set hIB1.toTabInv qB hdB hrB (Nat.succ_ne_zero _), ruleK_set hIA1.toTabInv qA hdA hrA
    (Nat.succ_ne_zero _), hq.2 κ d']

/-- **The rule compile's program** keeps the invariant, grows the program,
keeps the site, and stores the right-hand side. -/
theorem compRule_spec {f : Name → Option ConstantInfo} {p : Name → Nat → Option ProjEntry} {P : G4Prog}
    (hI : Inv f p P) {k ri : Nat} {c : Name} {lps : List Name} {us : List Level} {mI rP base nr : Nat}
    {isK isEta : Bool} (hi : P.kInfo[k]? = some (.recr c lps us mI rP base nr isK isEta))
    (hb₁ : base ≤ ri) (hb₂ : ri < base + nr) :
    Inv f p (compRule f p P ri ((P.rules[ri]!).rhs.instantiateLevelParams lps us)) ∧
      ExtR P (compRule f p P ri ((P.rules[ri]!).rhs.instantiateLevelParams lps us)) ∧
      (compRule f p P ri ((P.rules[ri]!).rhs.instantiateLevelParams lps us)).site = P.site ∧
      (compRule f p P ri ((P.rules[ri]!).rhs.instantiateLevelParams lps us)).ruleCode[ri]! ≠ 0 := by
  have hcomp := g4Comp_spec f p P ((P.rules[ri]!).rhs.instantiateLevelParams lps us) hI
  unfold compRule
  generalize g4Comp f p P ((P.rules[ri]!).rhs.instantiateLevelParams lps us) = r at hcomp ⊢
  obtain ⟨o, P1⟩ := r
  obtain ⟨hI1, hx1, hc1⟩ := hcomp
  dsimp only at hI1 hx1 hc1 ⊢
  have hrl : ri < P.rules.size := by
    have := hI.rows_lt (P := P) ⟨_, _, _, _, _, _, _, _, _, hi, hb₁, hb₂⟩; omega
  have hrr : (P1.rules[ri]!) = (P.rules[ri]!) := by
    simp only [getElem!_def, (rowR_eq (hx1.toExtR.row ri hrl)).1]
  have hrs : ri < P1.ruleCode.size := by
    rw [hI1.szs.2.1.1]; exact Nat.lt_of_lt_of_le hrl hx1.toExtR.rulesSize
  refine ⟨hI1.setRuleCode (hx1.toExtR.kInfo_some hi) hb₁ hb₂ (by rw [hrr]; exact hc1),
    hx1.toExtR.trans (ExtR.codes P1 P1.kCode _), hx1.site, ?_⟩
  rw [get!_of_some (set!_get?_self hrs)]; omega

/-- Mode 1 reads neither `pc` nor `env`. -/
theorem g4Run_mode1_regs (f : Name → Option ConstantInfo) (p : Name → Nat → Option ProjEntry) (P : G4Prog)
    (cel val ev fs argA slots mem mH : Array Nat) (pc env x st : Nat) :
    ∀ n, g4Run f p n P cel val ev fs argA slots mem mH 1 pc env x st =
      g4Run f p n P cel val ev fs argA slots mem mH 1 0 0 x st
  | 0 => by rw [g4Run.eq_1, g4Run.eq_1]
  | n + 1 => by
    rw [g4Run.eq_7 f p P cel val ev fs argA slots mem mH 1 pc env x st n (by decide) (by decide)
      (by decide) (by decide), g4Run.eq_7 f p P cel val ev fs argA slots mem mH 1 0 0 x st n (by decide)
      (by decide) (by decide) (by decide)]

/-- **The rule compile**, one step on either side. -/
theorem run_iota_comp {f : Name → Option ConstantInfo} {p : Name → Nat → Option ProjEntry} {s : MS}
    (hm : s.mode = 1) (hn : 0 < s.fs.size) (ht : s.fs[s.fs.size - 1]! &&& 15 = 3) (hI : I1 s)
    (hrc : s.P.ruleCode[iotaRi s]! = 0) {c : Name} {lps : List Name} {us : List Level}
    {mI rP base nr : Nat} {isK isEta : Bool}
    (hi : s.P.kInfo[s.fs[s.fs.size - 4]!]? = some (.recr c lps us mI rP base nr isK isEta)) (n : Nat) :
    s.run f p (n + 1) =
      ({ s with P := compRule f p s.P (iotaRi s) ((s.P.rules[iotaRi s]!).rhs.instantiateLevelParams lps us) } :
        MS).run f p n := by
  obtain ⟨h1, hkc, hne, hcl, hc3⟩ := hI
  have h0 : (s.fs.size == 0) = false := by simpa using Nat.pos_iff_ne_zero.mp hn
  have hi' := getElem!_of_getElem? hi
  unfold MS.run
  dsimp only
  rw [hm]
  conv => rhs; rw [g4Run_mode1_regs]
  rw [g4Run.eq_7 f p s.P s.cel s.val s.ev s.fs s.argA s.slots s.mem s.mH 1 s.pc s.env s.x s.st n
    (by decide) (by decide) (by decide) (by decide)]
  unfold iotaRi at hne hcl hc3 hrc ⊢
  dsimp only
  simp only [h0, Bool.false_eq_true, ↓reduceIte, ht, h1, hkc, bne_self_eq_false, Bool.false_or, hne, hcl,
    hc3, hrc, hi', beq_self_eq_true, beq_iff_eq]
  rfl

section
variable {j : Nat} {N : Name → Prop} {env : Env} {f₂ : Name → Option ConstantInfo}
  {p₂ : Name → Nat → Option ProjEntry} {t₀ : Expr} {n : Nat}

/-- **The ι frame's words at a constructor**: related recursor entries of
one rule list, one offset of the rule found, the rule row's words one, its
right-hand side's code of one term where compiled. -/
theorem MRel.iotaW (hag : LookAgree N env.find? env.findProj? f₂ p₂) {sA sB : MS}
    (hr : MRel j N env.find? env.findProj? f₂ p₂ sA sB) {kA kB kcA kcB : Nat}
    (hk : ERel N sA.P sB.P kA kB) (hkc : ERel N sA.P sB.P kcA kcB)
    (h2 : sA.P.kTag[kA]? = some 2) (h1 : sA.P.kTag[kcA]! = 1) :
    ∃ (c : Name) (lps : List Name) (us : List Level) (mI rP bA bB : Nat) (isK isEta : Bool)
      (rules : List RecRule) (d : Nat),
      sA.P.kInfo[kA]? = some (.recr c lps us mI rP bA rules.length isK isEta) ∧
      sB.P.kInfo[kB]? = some (.recr c lps us mI rP bB rules.length isK isEta) ∧
      sA.P.kC[kA]! = bA ∧ sB.P.kC[kB]! = bB ∧ sA.P.kD[kA]! = rules.length ∧
      sB.P.kD[kB]! = rules.length ∧ sA.P.kB[kA]! = rP ∧ sB.P.kB[kB]! = rP ∧ sB.P.kTag[kcB]! = 1 ∧
      d ≤ rules.length ∧
      g4FindRule sA.P.rNid sA.P.kB[kcA]! rules.length bA = bA + d ∧
      g4FindRule sB.P.rNid sB.P.kB[kcB]! rules.length bB = bB + d ∧
      ∀ hd : d < rules.length, NamesIn N (rules[d].rhs.instantiateLevelParams lps us) ∧
        sA.P.rules[bA + d]? = sB.P.rules[bB + d]? ∧ sA.P.rNF[bA + d]? = sB.P.rNF[bB + d]? ∧
        sA.P.rCP[bA + d]? = sB.P.rCP[bB + d]? ∧ sA.P.rC3[bA + d]? = sB.P.rC3[bB + d]? ∧
        (sA.P.rules[bA + d]!).rhs = rules[d].rhs ∧
        CodeOK env.find? env.findProj? sA.P sA.P.ruleCode[bA + d]! (rules[d].rhs.instantiateLevelParams lps us) ∧
        CodeOK f₂ p₂ sB.P sB.P.ruleCode[bB + d]! (rules[d].rhs.instantiateLevelParams lps us) := by
  have hkl : kA < sA.P.kInfo.size := by obtain ⟨iA, -, hi, -⟩ := hk.1; exact lt_of_some hi
  obtain ⟨c, lps, us, mI, rP, bA, nr, isK, isEta, hi, -, -⟩ := recEntry hr.invA hkl h2
  have hNc : N c := hk.2 _ hi
  have hf : env.find? c = f₂ c := (hag.find c hNc).symm
  obtain ⟨bB, hiB, -, -, -, -, eBA, eBB, eCA, eCB, eDA, eDB, -⟩ :=
    hk.1.recW hr.invA hr.invB hi hf (hag.kfab c us hNc).symm
  obtain ⟨bB', cv, rules, hiB', hfc, hnr, hrows⟩ := hk.1.recRows hr.invA hr.invB hi hf
  rw [hiB] at hiB'
  obtain rfl : bB = bB' := by cases hiB'; rfl
  subst hnr
  have hcl : kcA < sA.P.kInfo.size := by obtain ⟨iA, -, hi', -⟩ := hkc.1; exact lt_of_some hi'
  obtain ⟨cc, cus, nP, nF, hci, -⟩ := (hr.invA.ents _ hcl).tag1 hcl
    (by rw [some_of_lt (by rw [hr.invA.sizes]; exact hcl), h1])
  obtain ⟨-, -, hB1, -, -, iA, iB, eiA, eiB, hni⟩ :=
    hkc.1.ctorW hr.invA hr.invB hci (hag.find cc (hkc.2 _ hci)).symm
  have hrow : ∀ j (hj : j < rules.length), _ := fun j hj => by
    obtain ⟨hNr, -, hT⟩ := hag.rules c cv mI rP isK rules hNc hfc rules[j] (List.getElem_mem hj)
    exact RowOK.rel (hrows j hj).1 (hrows j hj).2 (hag.find _ hNr).symm (hag.case3 hNr hT isK lps us)
  obtain ⟨d, eFA, eFB⟩ := findRule_rel sA.P.rNid sB.P.rNid iA iB rules.length bA bB fun j hj => by
    obtain ⟨-, -, -, -, ⟨jA, jB, ejA, ejB, hnj⟩, -⟩ := hrow j hj
    rw [get!_of_some ejA, get!_of_some ejB]
    exact NidRel.iff hr.invA.nidOK hr.invB.nidOK hnj hni
  have hd : d ≤ rules.length := by
    rcases findRule_spec sA.P.rNid iA rules.length bA with ⟨e, -⟩ | ⟨j, hj, e, -⟩ <;> omega
  refine ⟨c, lps, us, mI, rP, bA, bB, isK, isEta, rules, d, hi, hiB, get!_of_some eCA, get!_of_some eCB,
    get!_of_some eDA, get!_of_some eDB, get!_of_some eBA, get!_of_some eBB, get!_of_some hB1, hd,
    by rw [get!_of_some eiA]; exact eFA, by rw [get!_of_some eiB]; exact eFB, fun hd' => ?_⟩
  obtain ⟨e1, e2, e3, e4, -, wA, wB, ewA, ewB, cA, cB⟩ := hrow d hd'
  have hN := (hag.rules c cv mI rP isK rules hNc hfc rules[d] (List.getElem_mem hd')).2.1
  refine ⟨hN.instLP lps us, e1, e2, e3, e4, ?_, by rw [get!_of_some ewA]; exact cA,
    by rw [get!_of_some ewB]; exact cB⟩
  rw [getElem!_of_getElem? (hrows d hd').1.1]

/-- **Mode 1 at an ι frame**, where the dispatch stops before the
right-hand side's test, or both sides have its code. -/
theorem sim_mode1i' (hwf : EnvWF env) (hag : LookAgree N env.find? env.findProj? f₂ p₂)
    (hsN : strLitStored env = true → StrNames N) (ih : SimAt j N env f₂ p₂ t₀ n)
    {sA sB : MS} {oc : Nat → Expr} {fl : List Fr}
    (h : MInv env t₀ oc sA fl) (hR : RunOK env sA.P) (hr : MRel j N env.find? env.findProj? f₂ p₂ sA sB)
    (hm : sA.mode = 1) (hn : 0 < sA.fs.size) (ht : sA.fs[sA.fs.size - 1]! &&& 15 = 3)
    (hc : ¬I1 sA ∨ (sA.P.ruleCode[iotaRi sA]! ≠ 0 ∧ sB.P.ruleCode[iotaRi sB]! ≠ 0)) {m : Nat}
    (hmn : (j = 0 ∧ m = n + 1) ∨ (j = 1 ∧ 2 * n + 1 ≤ m)) :
    OutRel j N env f₂ p₂ (sA.run env.find? env.findProj? (n + 1)) (sB.run f₂ p₂ m) := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hmB : sB.mode = 1 := by rw [hr.mode, hm]
  have hg := hr.regs
  simp only [RegRel, hm] at hg
  obtain ⟨he, hx, hpc⟩ := hg
  have hxl := (h.val1 hm).1
  have hv4 : sA.val.size % 4 = 0 := h.store.valSz
  have hstop : ∀ g, OutRel j N env f₂ p₂ (.stop g sA.st) (.stop g sB.st) :=
    fun g => .inr (.inl ⟨_, _, rfl, by rw [hr.st]⟩)
  obtain ⟨fl', hfl, -, -⟩ := FS.top_iota' h.stack hn ht
  obtain ⟨-, -, -, h2k, -⟩ : FrOK sA.P sA.argA sA.N
      (.iota sA.fs[sA.fs.size - 4]! sA.fs[sA.fs.size - 3]! sA.fs[sA.fs.size - 2]!) :=
    h.frames _ (by rw [hfl]; exact List.mem_cons_self ..)
  obtain ⟨hk, e3, -, hpopF⟩ := hr.fs.iotaTop hn ht
  obtain ⟨w0, w2, w3, hw⟩ := hr.valW hxl
  have hpop : ∃ fl', MInv env t₀ oc { sA with fs := g4PopN sA.fs 4, mode := 1, pc := 0, env := 0, x := 0 } fl' :=
    step_iota_pop h hm hn ht
  have hpopR : MRel j N env.find? env.findProj? f₂ p₂
      { sA with fs := g4PopN sA.fs 4, mode := 1, pc := 0, env := 0, x := 0 }
      { sB with fs := g4PopN sB.fs 4, mode := 1, pc := 0, env := 0, x := 0 } :=
    { hr with
      fs := hpopF
      mode := rfl
      regs := ⟨rfl, rfl, rfl⟩ }
  unfold MS.run
  rw [hm, g4Run.eq_7 env.find? env.findProj? sA.P sA.cel sA.val sA.ev sA.fs sA.argA sA.slots sA.mem sA.mH 1
    sA.pc sA.env sA.x sA.st n (by decide) (by decide) (by decide) (by decide), hmB,
    g4Run.eq_7 f₂ p₂ sB.P sB.cel sB.val sB.ev sB.fs sB.argA sB.slots sB.mem sB.mH 1
    sB.pc sB.env sB.x sB.st m (by decide) (by decide) (by decide) (by decide)]
  rw [hr.fs.1, hx, hr.fs.top hn]
  split
  next h0 => simp only [beq_iff_eq] at h0; omega
  next =>
  split
  next ht' => rw [ht] at ht'; cases ht'
  next ht' => rw [ht] at ht'; cases ht'
  rotate_left
  next ht' => rw [ht] at ht'; cases ht'
  next ht' => rw [ht] at ht'; cases ht'
  next _ _ h3 _ _ => exact absurd ht h3
  dsimp only
  rw [e3, w0]
  split
  next hv =>
    -- a literal major
    rw [hv] at hw
    obtain ⟨hw', hNN⟩ : sB.val[g4X4 sA.x + 1]! = sA.val[g4X4 sA.x + 1]! ∧ NatN N := hw
    rw [hr.natOk hNN, hw']
    split
    next => exact hstop _
    next hok =>
    have hok' : sA.P.natOk = true := by simpa using hok
    split
    next h0 =>
      have h' := step_iota_zero hR h hm hv hok' h0
      rw [hr.val.1]
      refine ih.app (sB := { sB with
          val := (((sB.val.push 1).push sB.P.kZero).push 0).push 0
          mode := 1
          pc := 0
          env := 0
          x := sA.val.size >>> 2 }) h' hR ?_ (m := m) (by omega)
      exact { hr with
        val := hr.val.push hv4 1 0 0 _ _ (hr.kZero.2 hNN.2.1)
        mode := rfl
        regs := ⟨rfl, rfl, rfl⟩ }
    next mm hm1 =>
      obtain ⟨oc', h'⟩ := step_iota_succ hR h hm hv hok' hm1
      rw [hr.val.1, hr.cel.1, hr.argA]
      refine ih.app (sB := { sB with
          cel := (((sB.cel.push ((sA.val.size >>> 2) + 2)).push 0).push 0).push 0
          val := (((((((sB.val.push 2).push mm).push 0).push 0).push 1).push sB.P.kSucc).push
            sA.argA.size).push 1
          argA := sA.argA.push (sA.cel.size >>> 2)
          mode := 1
          pc := 0
          env := 0
          x := (sA.val.size >>> 2) + 1 }) h' hR ?_ (m := m) (by omega)
      exact { hr with
        cel := hr.cel.push h.store.celSz _ 0 0 0 0 (fun h => absurd h (by omega))
        val := (hr.val.push hv4 2 0 0 _ _ ⟨rfl, hNN⟩).push (by simp; omega) 1 sA.argA.size 1 _ _
          (hr.kSucc.2 hNN.2.2)
        argA := rfl
        memoA := hr.memoA.argA (Pre.push _ _)
        memoB := (hr.argA ▸ hr.memoB : MemoTab sB.mem sA.argA sB.mH).argA (Pre.push _ _)
        mode := rfl
        regs := ⟨rfl, rfl, rfl⟩ }
  next hv =>
    -- a string major
    rw [hv] at hw
    obtain ⟨⟨s, hsA, hsB⟩, hsN'⟩ :=
      (hw : StrRel sA.P sB.P sA.val[g4X4 sA.x + 1]! sB.val[g4X4 sA.x + 1]! ∧ StrNames N)
    rw [hr.strOk hsN']
    split
    next => exact hstop _
    next hok =>
    have hok' : sA.P.strOk = true := by simpa using hok
    have h' := step_iota_str hR h hm hv hok'
    rw [getElem!_of_getElem? hsA] at h'
    rw [getElem!_of_getElem? hsA, getElem!_of_getElem? hsB]
    obtain ⟨hr', hxA, hxB, hR', hT⟩ := hr.compStr hsN hR hok' s
    refine ih.app (sB := { sB with
        P := (g4Comp f₂ p₂ sB.P (strLitToConstructor s)).2
        mode := 0
        pc := (g4Comp f₂ p₂ sB.P (strLitToConstructor s)).1
        env := 0
        x := 0 }) h' hR' ?_ (m := m) (by omega)
    exact { hr' with
      mode := rfl
      regs := ⟨rfl, rfl, hT⟩ }
  next hv =>
    -- a constructor major
    rw [hv] at hw
    have hkc : ERel N sA.P sB.P sA.val[g4X4 sA.x + 1]! sB.val[g4X4 sA.x + 1]! := hw
    rw [hr.tagEq hag hkc]
    by_cases h1 : sA.P.kTag[sA.val[g4X4 sA.x + 1]!]! = 1
    rotate_left
    · have h1' : (sA.P.kTag[sA.val[g4X4 sA.x + 1]!]! != 1) = true := by simpa using h1
      simp only [h1', Bool.true_or, ↓reduceIte]
      exact hstop _
    obtain ⟨c, lps, us, mI, rP, bA, bB, isK, isEta, rules, d, hiA, hiB, eCA, eCB, eDA, eDB, eBA, eBB, -, hd,
      eFA, eFB, hrow⟩ := hr.iotaW hag hk hkc h2k h1
    have hriA : iotaRi sA = bA + d := by unfold iotaRi; rw [eDA, eCA]; exact eFA
    have hriB : iotaRi sB = bB + d := by unfold iotaRi; rw [hr.fs.1, hx, eDB, eCB]; exact eFB
    have hri' : g4FindRule sA.P.rNid sA.P.kB[sA.val[g4X4 sA.x + 1]!]! sA.P.kD[sA.fs[sA.fs.size - 4]!]!
        sA.P.kC[sA.fs[sA.fs.size - 4]!]! = bA + d := by rw [eDA, eCA]; exact eFA
    rw [eCA, eCB, eDA, eDB, eFA, eFB, h1]
    by_cases hdn : d = rules.length
    · subst hdn
      simp only [bne_self_eq_false, beq_self_eq_true, Bool.false_or, ↓reduceIte]
      exact hstop _
    have hne : (bA + d == bA + rules.length) = false := by simp only [beq_eq_false_iff_ne]; omega
    have hneB : (bB + d == bB + rules.length) = false := by simp only [beq_eq_false_iff_ne]; omega
    simp only [bne_self_eq_false, Bool.false_or, hne, hneB, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨hN, -, e2, e3', e4, -, cA, cB⟩ := hrow (by omega)
    rw [← get!_congr2 e2, ← get!_congr2 e3', w3, ← get!_congr2 e4, w2, ← hk.1.name]
    split
    next => exact hstop _
    next hcl =>
    split
    next => exact hstop _
    next hc3 =>
    have hcl' : sA.val[g4X4 sA.x + 3]! = sA.P.rCP[bA + d]! + sA.P.rNF[bA + d]! := by simpa using hcl
    have hc3' : sA.P.rC3[bA + d]! = 0 := by simpa using hc3
    have hne' : bA + d ≠ sA.P.kC[sA.fs[sA.fs.size - 4]!]! + sA.P.kD[sA.fs[sA.fs.size - 4]!]! := by
      rw [eCA, eDA]; omega
    rcases hc with hc | ⟨hcA, hcB⟩
    · exact absurd ⟨hv, h1, by rw [hriA]; exact hne', by rw [hriA]; exact hcl', by rw [hriA]; exact hc3'⟩ hc
    rw [hriA] at hcA
    rw [hriB] at hcB
    have hcA' : (sA.P.ruleCode[bA + d]! == 0) = false := by simpa using hcA
    have hcB' : (sB.P.ruleCode[bB + d]! == 0) = false := by simpa using hcB
    simp only [hcA', hcB', Bool.false_eq_true, ↓reduceIte]
    rcases cA with h0 | ⟨oA, eoA, compA⟩
    · exact absurd h0 hcA
    rcases cB with h0 | ⟨oB, eoB, compB⟩
    · exact absurd h0 hcB
    have hT : TRel N env.find? env.findProj? f₂ p₂ sA.P sB.P oA oB := TRel.ofComp hN compA compB
    rw [eoA, eoB, Nat.add_sub_cancel, Nat.add_sub_cancel, eBA, eBB, hT.tag hag, hr.argA, hr.ev]
    have hframes : OutRel j N env f₂ p₂
        (g4Run env.find? env.findProj? n sA.P sA.cel sA.val sA.ev
          (g4PushArgs sA.argA sA.fs[sA.fs.size - 3]!
            (g4PushArgs sA.argA (sA.val[g4X4 sA.x + 2]! + sA.P.rCP[bA + d]!) (g4PopN sA.fs 4)
              sA.P.rNF[bA + d]!) rP) sA.argA sA.slots sA.mem sA.mH 0 oA 0 0 sA.st)
        (g4Run f₂ p₂ m sB.P sB.cel sB.val sA.ev
          (g4PushArgs sA.argA sA.fs[sA.fs.size - 3]!
            (g4PushArgs sA.argA (sA.val[g4X4 sA.x + 2]! + sA.P.rCP[bA + d]!) (g4PopN sB.fs 4)
              sA.P.rNF[bA + d]!) rP) sA.argA sB.slots sB.mem sB.mH 0 oB 0 0 sB.st) := by
      obtain ⟨fl', h'⟩ := step_iota_frames hwf h hm hn ht hv rfl h1 hri' hne' hcl' hc3' (by rw [eoA]; omega)
      rw [eoA, Nat.add_sub_cancel, eBA] at h'
      refine ih.app (sB := { sB with
          fs := g4PushArgs sA.argA sA.fs[sA.fs.size - 3]!
            (g4PushArgs sA.argA (sA.val[g4X4 sA.x + 2]! + sA.P.rCP[bA + d]!) (g4PopN sB.fs 4)
              sA.P.rNF[bA + d]!) rP
          ev := sA.ev
          argA := sA.argA
          mode := 0
          pc := oB
          env := 0
          x := 0 }) h' hR ?_ (m := m) (by omega)
      exact { hr with
        fs := FsRel.pushArgs _ _ _ (FsRel.pushArgs _ _ _ hpopF)
        ev := rfl
        argA := rfl
        memoB := (hr.argA ▸ hr.memoB : MemoTab sB.mem sA.argA sB.mH)
        mode := rfl
        regs := ⟨rfl, rfl, hT⟩ }
    by_cases hl : sA.P.code[oA]! = 2
    · rw [hT.lamTn hl]
      split
      next hb =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hb
        obtain ⟨fl', h'⟩ := step_iota_bind hwf h hm hn ht hv rfl h1 hri' hne' hcl' hc3' (by rw [eoA]; omega)
          (by rw [eoA, Nat.add_sub_cancel]; exact hb.1) (by rw [eoA, Nat.add_sub_cancel, eBA]; exact hb.2)
        rw [eoA, Nat.add_sub_cancel, eBA] at h'
        have hT' := hT.lamBody hl (k := sA.P.code[oA + 2]!) (Nat.le_refl _)
        simp only [beq_self_eq_true, ↓reduceIte] at hT'
        refine ih.app (sB := { sB with
            ev := _
            fs := g4PopN sB.fs 4
            argA := sA.argA
            mode := 0
            pc := sB.P.code[oB + 3]!
            env := _
            x := 0 }) h' hR ?_ (m := m) (by omega)
        exact { hr with
          ev := rfl
          fs := hpopF
          argA := rfl
          memoB := (hr.argA ▸ hr.memoB : MemoTab sB.mem sA.argA sB.mH)
          mode := rfl
          regs := ⟨rfl, rfl, hT'⟩ }
      next => exact hframes
    · have hl' : (sA.P.code[oA]! == 2) = false := by simpa using hl
      simp only [hl', Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      exact hframes
  next hv =>
    -- a neutral major
    have hkl : sA.fs[sA.fs.size - 4]! < sA.P.kInfo.size := by
      obtain ⟨iA, -, hi, -⟩ := hk.1; exact lt_of_some hi
    obtain ⟨c, lps, us, mI, rP, bA, nr, isK, isEta, hi, -, -⟩ := recEntry hr.invA hkl h2k
    have hNc : N c := hk.2 _ hi
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, fA, fB, eEA, eEB, -⟩ :=
      hk.1.recW hr.invA hr.invB hi (hag.find c hNc).symm (hag.kfab c us hNc).symm
    have hp1 : sB.P.kE[sB.fs[sA.fs.size - 4]!]! % 2 = sA.P.kE[sA.fs[sA.fs.size - 4]!]! % 2 := by
      rw [get!_of_some eEA, get!_of_some eEB]; cases isK <;> cases isEta <;> simp <;> omega
    have hp2 : sB.P.kE[sB.fs[sA.fs.size - 4]!]! / 2 % 2 = sA.P.kE[sA.fs[sA.fs.size - 4]!]! / 2 % 2 := by
      rw [get!_of_some eEA, get!_of_some eEB]; cases isK <;> cases isEta <;> simp <;> omega
    rw [hp1, hp2, ← hk.1.name]
    split
    next => exact hstop _
    next =>
    split
    next => exact hstop _
    next =>
    obtain ⟨fl', h'⟩ := hpop
    exact ih.app h' hR hpopR (m := m) (by omega)
  next =>
    obtain ⟨fl', h'⟩ := hpop
    exact ih.app h' hR hpopR (m := m) (by omega)

/-- The ι frame's rule row on the other side: the dispatch reaches the test
there too, at the related row. -/
theorem MRel.iotaI1 (hag : LookAgree N env.find? env.findProj? f₂ p₂) {sA sB : MS} {oc : Nat → Expr}
    {fl : List Fr} (h : MInv env t₀ oc sA fl) (hr : MRel j N env.find? env.findProj? f₂ p₂ sA sB)
    (hm : sA.mode = 1) (hn : 0 < sA.fs.size) (ht : sA.fs[sA.fs.size - 1]! &&& 15 = 3) (hI : I1 sA) :
    ∃ (c : Name) (lps : List Name) (us : List Level) (mI rP bA bB nr : Nat) (isK isEta : Bool) (d : Nat),
      sA.P.kInfo[sA.fs[sA.fs.size - 4]!]? = some (.recr c lps us mI rP bA nr isK isEta) ∧
      sB.P.kInfo[sB.fs[sB.fs.size - 4]!]? = some (.recr c lps us mI rP bB nr isK isEta) ∧
      iotaRi sA = bA + d ∧ iotaRi sB = bB + d ∧ d < nr ∧ I1 sB := by
  obtain ⟨hv, h1, hne, hcl, hc3⟩ := hI
  have hg := hr.regs
  simp only [RegRel, hm] at hg
  obtain ⟨-, hx, -⟩ := hg
  obtain ⟨fl', hfl, -, -⟩ := FS.top_iota' h.stack hn ht
  obtain ⟨-, -, -, h2k, -⟩ : FrOK sA.P sA.argA sA.N
      (.iota sA.fs[sA.fs.size - 4]! sA.fs[sA.fs.size - 3]! sA.fs[sA.fs.size - 2]!) :=
    h.frames _ (by rw [hfl]; exact List.mem_cons_self ..)
  obtain ⟨hk, -, -, -⟩ := hr.fs.iotaTop hn ht
  obtain ⟨w0, -, w3, hw⟩ := hr.valW (h.val1 hm).1
  rw [hv] at hw
  obtain ⟨c, lps, us, mI, rP, bA, bB, isK, isEta, rules, d, hiA, hiB, eCA, eCB, eDA, eDB, -, -, hB1, -,
    eFA, eFB, hrow⟩ := hr.iotaW hag hk hw h2k h1
  have hriA : iotaRi sA = bA + d := by unfold iotaRi; rw [eDA, eCA]; exact eFA
  have hriB : iotaRi sB = bB + d := by unfold iotaRi; rw [hr.fs.1, hx, eDB, eCB]; exact eFB
  have hdl : d < rules.length := by
    have hd : d ≠ rules.length := fun e => hne (by rw [hriA, eCA, eDA, e])
    have := (findRule_spec sA.P.rNid sA.P.kB[sA.val[g4X4 sA.x + 1]!]! rules.length bA)
    rcases this with ⟨e, -⟩ | ⟨j, hj, e, -⟩ <;> rw [eFA] at e <;> omega
  obtain ⟨-, -, e2, e3, e4, -, -, -⟩ := hrow hdl
  refine ⟨c, lps, us, mI, rP, bA, bB, rules.length, isK, isEta, d, hiA, by rw [hr.fs.1]; exact hiB, hriA, hriB,
    hdl, by rw [hx, w0]; exact hv, by rw [hx]; exact hB1, ?_, ?_, ?_⟩
  · rw [hriB, hr.fs.1, eCB, eDB]; omega
  · rw [hriB, hx, w3, ← get!_congr2 e2, ← get!_congr2 e3]; rw [hriA] at hcl; exact hcl
  · rw [hriB, ← get!_congr2 e4]; rw [hriA] at hc3; exact hc3

/-- **Mode 1 at an ι frame**: the right-hand side's compile in its four
combinations, as the δ compile of mode 3. -/
theorem sim_mode1i (hwf : EnvWF env) (hag : LookAgree N env.find? env.findProj? f₂ p₂)
    (hsN : strLitStored env = true → StrNames N) (ih : SimAt j N env f₂ p₂ t₀ n)
    {sA sB : MS} {oc : Nat → Expr} {fl : List Fr}
    (h : MInv env t₀ oc sA fl) (hR : RunOK env sA.P) (hr : MRel j N env.find? env.findProj? f₂ p₂ sA sB)
    (hm : sA.mode = 1) (hn : 0 < sA.fs.size) (ht : sA.fs[sA.fs.size - 1]! &&& 15 = 3) {m : Nat}
    (hmn : (j = 0 ∧ m = n + 1) ∨ (j = 1 ∧ 2 * (n + 1) ≤ m)) :
    OutRel j N env f₂ p₂ (sA.run env.find? env.findProj? (n + 1)) (sB.run f₂ p₂ m) := by
  by_cases hI : I1 sA
  rotate_left
  · exact sim_mode1i' hwf hag hsN ih h hR hr hm hn ht (.inl hI) (by omega)
  have hmB : sB.mode = 1 := by rw [hr.mode, hm]
  have hnB : 0 < sB.fs.size := by rw [hr.fs.1]; exact hn
  have htB : sB.fs[sB.fs.size - 1]! &&& 15 = 3 := by rw [hr.fs.1, hr.fs.top hn]; exact ht
  obtain ⟨c, lps, us, mI, rP, bA, bB, nr, isK, isEta, d, hiA, hiB, hriA, hriB, hdl, hIB⟩ :=
    hr.iotaI1 hag h hm hn ht hI
  obtain ⟨hv, h1, hne, hcl, hc3⟩ := hI
  by_cases hcA : sA.P.ruleCode[iotaRi sA]! = 0 <;> by_cases hcB : sB.P.ruleCode[iotaRi sB]! = 0
  · -- both compile
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [run_iota_comp hm hn ht ⟨hv, h1, hne, hcl, hc3⟩ hcA hiA, run_iota_comp hmB hnB htB hIB hcB hiB]
    obtain ⟨hIA', hxA, hsA, -⟩ := compRule_spec h.store.prog hiA (ri := iotaRi sA) (by omega) (by omega)
    obtain ⟨hIB', hxB, hsB, -⟩ := compRule_spec hr.invB hiB (ri := iotaRi sB) (by omega) (by omega)
    have h' := step_iota_compile hwf h hm hn ht hv rfl h1 rfl hne hcl hc3 (getElem!_of_getElem? hiA)
    exact ih _ _ _ _ h' (hR.ext hxA hsA) (hr.ext hxA hxB hIA' hIB' hsA hsB fun h0 =>
      (hr.code h0).iota h.store.prog hr.invB hiA hiB hdl hdl hriA hriB _ _) m (fuel_t hmn)
  · -- A compiles a right-hand side B has: B takes no step (not in lock-step)
    rcases hmn with ⟨rfl, -⟩ | ⟨rfl, hmn⟩
    · rw [hriA] at hcA; rw [hriB] at hcB
      exact absurd ((CodeSame.rule_iff (hr.code rfl) hr.invA.toCompInv hr.invB.toCompInv hiA hiB hdl hdl).1 hcA) hcB
    rw [run_iota_comp hm hn ht ⟨hv, h1, hne, hcl, hc3⟩ hcA hiA]
    obtain ⟨hIA', hxA, hsA, -⟩ := compRule_spec h.store.prog hiA (ri := iotaRi sA) (by omega) (by omega)
    have h' := step_iota_compile hwf h hm hn ht hv rfl h1 rfl hne hcl hc3 (getElem!_of_getElem? hiA)
    exact ih _ sB _ _ h' (hR.ext hxA hsA) (hr.ext hxA (ExtR.refl _) hIA' hr.invB hsA rfl
      fun h0 => absurd h0 (by decide)) m (.inr ⟨rfl, by omega⟩)
  · -- B compiles a right-hand side A has, then takes A's step (not in lock-step)
    rcases hmn with ⟨rfl, -⟩ | ⟨rfl, hmn⟩
    · rw [hriA] at hcA; rw [hriB] at hcB
      exact absurd ((CodeSame.rule_iff (hr.code rfl) hr.invA.toCompInv hr.invB.toCompInv hiA hiB hdl hdl).2 hcB) hcA
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [run_iota_comp hmB hnB htB hIB hcB hiB]
    obtain ⟨hIB', hxB, hsB, hcB'⟩ := compRule_spec hr.invB hiB (ri := iotaRi sB) (by omega) (by omega)
    have hr' := hr.ext (ExtR.refl _) hxB hr.invA hIB' rfl hsB fun h0 => absurd h0 (by decide)
    obtain ⟨c', lps', us', mI', rP', bA', bB', nr', isK', isEta', d', hiA', hiB', hriA', hriB', -, -⟩ :=
      hr'.iotaI1 hag h hm hn ht ⟨hv, h1, hne, hcl, hc3⟩
    have e1 : d' = d := by
      rw [hiA] at hiA'; cases hiA'
      have := hriA'.symm.trans hriA; omega
    have e2 : bB' = bB := by
      rw [hxB.kInfo_some hiB] at hiB'; cases hiB'; rfl
    refine sim_mode1i' hwf hag hsN ih h hR hr' hm hn ht (.inr ⟨hcA, ?_⟩) (.inr ⟨rfl, by omega⟩)
    rw [hriB', e1, e2, ← hriB]; exact hcB'
  · exact sim_mode1i' hwf hag hsN ih h hR hr hm hn ht (.inr ⟨hcA, hcB⟩) (by omega)

end

end ConLeche.Verify.Ground
