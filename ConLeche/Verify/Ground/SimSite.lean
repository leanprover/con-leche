module

public import ConLeche.Verify.Ground.Site
import ConLeche.Verify.Ground.Keys
import ConLeche.Verify.Ground.Memo
import ConLeche.Verify.Ground.Step1N
public import ConLeche.Verify.Ground.SimState
import ConLeche.Verify.Ground.SimRun
import ConLeche.Verify.Ground.Step1I
import ConLeche.Verify.Ground.SimStep1

public section

/-!
# The kept program against a fresh one (task #423 soundness, layer (d), item 2(d))

A site run on the declaration's kept program and one on a fresh program
answer alike, unless the kept run is out of budget: the two pre-states are
related (`siteMS_rel`: the site entries by key, the kept slots all stale
below the epoch), and the simulation (`sim_run`, one lookup on both sides,
`N` everything) relates the runs once the fresh one has `2 n + 1` steps for
the kept one's `n`.  Only the answer and the state count are compared; the
step count differs by the fresh run's compiles.
-/

namespace ConLeche.Verify.Ground

open ConLeche

/-- The machine a site run starts: the compiled term's node `o`, the
program's slot array set aside. -/
@[expose] def siteMS (P : G4Prog) (o : Nat) : MS :=
  ⟨{ P with slotA := #[] }, #[2, 0, 0, 0], #[5, 0, 0, 0], #[], #[], #[], P.slotA, #[], Array.replicate 1024 0,
    0, o, 0, 0, 0⟩

/-- An entry read back as a constant is that constant's entry. -/
theorem ent_key {P : G4Prog} {k : Nat} (hk : k < P.kInfo.size) {c : Name} {us : List Level}
    (he : entryTerm P k = .const c us) : ∃ i, P.kInfo[k]? = some i ∧ infoKey i = (c, us) := by
  unfold entryTerm at he
  rw [Array.getElem?_eq_getElem hk] at he ⊢
  refine ⟨_, rfl, ?_⟩
  dsimp only at he
  rw [infoTerm_key] at he
  cases he; rfl

/-- Two entries read back as one constant are related. -/
theorem ent_rel {PA PB : G4Prog} {kA kB : Nat} {c : Name} {us : List Level}
    (hA : kA < PA.kInfo.size ∧ entryTerm PA kA = .const c us)
    (hB : kB < PB.kInfo.size ∧ entryTerm PB kB = .const c us) :
    ERel (fun _ => True) PA PB kA kB := by
  obtain ⟨iA, h₁, e₁⟩ := ent_key hA.1 hA.2
  obtain ⟨iB, h₂, e₂⟩ := ent_key hB.1 hB.2
  exact ⟨⟨iA, iB, h₁, h₂, e₁.trans e₂.symm⟩, fun _ _ => trivial⟩

/-- **The site set-up's flags** are the call's. -/
theorem setup_flags (find? : Name → Option ConstantInfo) (findProj? : Name → Nat → Option ProjEntry)
    {natOk strOk : Bool} {maxNat : Nat} {P₀ : G4Prog}
    (hP₀ : P₀.kTag.size = 0 ∨ P₀.flags = (natOk, strOk, maxNat)) :
    (g4Setup find? findProj? natOk strOk maxNat P₀).flags = (natOk, strOk, maxNat) := by
  unfold g4Setup
  split
  · dsimp only
    have h₀ := Inv.fresh (find? := find?) (findProj? := findProj?) natOk strOk maxNat
    obtain ⟨hI₁, hx₁, -⟩ := g4Resolve_spec find? findProj? _ boolTrueName [] h₀
    generalize g4Resolve find? findProj? ({ natOk := natOk, strOk := strOk, maxNat := maxNat } : G4Prog)
      boolTrueName [] = q₁ at hI₁ hx₁ ⊢
    obtain ⟨kT, P₁⟩ := q₁
    obtain ⟨hI₂, hx₂, -⟩ := g4Resolve_spec find? findProj? P₁ boolFalseName [] hI₁
    generalize g4Resolve find? findProj? P₁ boolFalseName [] = q₂ at hI₂ hx₂ ⊢
    obtain ⟨kF, P₂⟩ := q₂
    obtain ⟨hI₃, hx₃, -⟩ := g4Resolve_spec find? findProj? P₂ natZeroName [] hI₂
    generalize g4Resolve find? findProj? P₂ natZeroName [] = q₃ at hI₃ hx₃ ⊢
    obtain ⟨kZ, P₃⟩ := q₃
    obtain ⟨-, hx₄, -⟩ := g4Resolve_spec find? findProj? P₃ natSuccName [] hI₃
    generalize g4Resolve find? findProj? P₃ natSuccName [] = q₄ at hx₄ ⊢
    obtain ⟨kS, P₄⟩ := q₄
    dsimp only at *
    exact (((hx₁.trans hx₂).trans hx₃).trans hx₄).toExtR.flags
  · rename_i h
    rcases hP₀ with h0 | hf
    · simp [h0] at h
    · exact hf

/-- No slot of a program at or below its epoch reads as set. -/
theorem SlotRel.stale {PA PB : G4Prog} {sa sb : Array Nat} (hA : ∀ i, i < sa.size → sa[i]! ≤ PA.epBase)
    (hB : ∀ i, i < sb.size → sb[i]! ≤ PB.epBase) : SlotRel PA PB sa sb :=
  ⟨fun slA slB _ _ _ _ _ => by rw [slotGet_old hA, slotGet_old hB],
    fun slA h => absurd (slotGet_old hA slA) h, fun slB h => absurd (slotGet_old hB slB) h⟩

section
variable {env : Env}

/-- **The two site pre-states are related**: two programs a run can start
from, of one set of flags, with the term compiled on each. -/
theorem siteMS_rel {PA PB : G4Prog} (hKA : KeptOK env PA) (hKB : KeptOK env PB)
    (hf : PB.flags = PA.flags) (e : Expr) :
    MRel (fun _ => True) env.find? env.findProj? env.find? env.findProj?
      (siteMS (g4Comp env.find? env.findProj? PA e).2 (g4Comp env.find? env.findProj? PA e).1)
      (siteMS (g4Comp env.find? env.findProj? PB e).2 (g4Comp env.find? env.findProj? PB e).1) := by
  have cA := g4Comp_spec env.find? env.findProj? PA e hKA.inv
  have cB := g4Comp_spec env.find? env.findProj? PB e hKB.inv
  generalize g4Comp env.find? env.findProj? PA e = rA at cA ⊢
  generalize g4Comp env.find? env.findProj? PB e = rB at cB ⊢
  obtain ⟨oA, QA⟩ := rA
  obtain ⟨oB, QB⟩ := rB
  obtain ⟨hIA, hxA, hcA⟩ := cA
  obtain ⟨hIB, hxB, hcB⟩ := cB
  dsimp only at *
  obtain ⟨tA, fA, zA, sA', -, slA⟩ := hxA.site_eqs
  obtain ⟨tB, fB, zB, sB', -, slB⟩ := hxB.site_eqs
  have eA := hxA.toExtR.flagsEq
  have eB := hxB.toExtR.flagsEq
  simp only [G4Prog.flags, Prod.mk.injEq] at hf
  have yA := ExtR.setSite QA QA.kTrue QA.kFalse QA.kZero QA.kSucc QA.epBase #[]
  have yB := ExtR.setSite QB QB.kTrue QB.kFalse QB.kZero QB.kSucc QB.epBase #[]
  have rA := (hKA.run.ext hxA.toExtR hxA.site).epoch QA.epBase #[]
  have rB := (hKB.run.ext hxB.toExtR hxB.site).epoch QB.epBase #[]
  have hepA : ∀ i, i < QA.slotA.size → QA.slotA[i]! ≤ QA.epBase := by
    have := hxA.site_eqs.2.2.2.2.1; rw [slA, this]; exact hKA.epoch
  have hepB : ∀ i, i < QB.slotA.size → QB.slotA[i]! ≤ QB.epBase := by
    have := hxB.site_eqs.2.2.2.2.1; rw [slB, this]; exact hKB.epoch
  exact {
    invA := hIA.setSite QA.kTrue QA.kFalse QA.kZero QA.kSucc QA.epBase #[]
    invB := hIB.setSite QB.kTrue QB.kFalse QB.kZero QB.kSucc QB.epBase #[]
    natOk := by show QB.natOk = QA.natOk; rw [eA.1, eB.1, hf.1]
    strOk := by show QB.strOk = QA.strOk; rw [eA.2.1, eB.2.1, hf.2.1]
    maxNat := by show QB.maxNat = QA.maxNat; rw [eA.2.2, eB.2.2, hf.2.2]
    kTrue := ent_rel rA.tru rB.tru
    kFalse := ent_rel rA.fls rB.fls
    kZero := ent_rel rA.zero rB.zero
    kSucc := ent_rel rA.succ rB.succ
    cel := ⟨rfl, fun c hc => by
      have : c = 0 := by simp [siteMS] at hc; omega
      subst this; exact ⟨rfl, fun h => by simp [siteMS] at h⟩⟩
    val := ⟨rfl, fun v hv => by
      have : v = 0 := by simp [siteMS] at hv; omega
      subst this; exact ⟨rfl, rfl, rfl, by simp [siteMS, ValW]⟩⟩
    ev := rfl
    argA := rfl
    fs := ⟨rfl, .nil⟩
    mem := ⟨rfl, fun r hr => by simp [siteMS] at hr⟩
    memoA := MemoTab.fresh _ (by decide)
    memoB := MemoTab.fresh _ (by decide)
    slots := SlotRel.stale hepA hepB
    mode := rfl
    st := rfl
    regs := ⟨rfl, rfl, TRel.ofComp (NamesIn.univ e) (hcA.extR yA) (hcB.extR yB)⟩ }

/-- **The site's start has the invariant** (`site_run`'s first steps). -/
theorem siteMS_minv {P : G4Prog} (hK : KeptOK env P) {e : Expr} (he : e.looseBVarsBounded 0 = true) :
    MInv env e (fun _ => bot)
      (siteMS (g4Comp env.find? env.findProj? P e).2 (g4Comp env.find? env.findProj? P e).1) [] ∧
      RunOK env (siteMS (g4Comp env.find? env.findProj? P e).2 (g4Comp env.find? env.findProj? P e).1).P := by
  have h₁ := (preMS_minv hK e).enterCompiled (fs := #[]) (fl' := []) .nil (fun _ h => (nomatch h)) he
    (ERed.refl : K env e (preMS P).P (preMS P).argA (fun _ => bot) [] e)
  have hc := g4Comp_spec env.find? env.findProj? P e hK.inv
  change MInv env e (fun _ => bot) { preMS P with
    P := (g4Comp env.find? env.findProj? P e).2, fs := #[], mode := 0,
    pc := (g4Comp env.find? env.findProj? P e).1, env := 0, x := 0 } [] at h₁
  generalize g4Comp env.find? env.findProj? P e = r at hc h₁ ⊢
  obtain ⟨o, P₂⟩ := r
  obtain ⟨hI₂, hx₂, -⟩ := hc
  dsimp only at hI₂ hx₂ h₁ ⊢
  obtain ⟨-, -, -, -, -, hsa⟩ := hx₂.site_eqs
  have h₂ := h₁.withProg0 rfl (hI₂.setSite P₂.kTrue P₂.kFalse P₂.kZero P₂.kSucc P₂.epBase #[])
    (ExtR.setSite P₂ P₂.kTrue P₂.kFalse P₂.kZero P₂.kSucc P₂.epBase #[]) rfl
  refine ⟨?_, (hK.run.ext hx₂.toExtR hx₂.site).epoch P₂.epBase #[]⟩
  unfold siteMS
  rw [hsa]
  exact h₂

/-- **The kept program against a fresh one** (item 2(d)): unless the kept
run is out of budget, a site run on the fresh program with `2 n + 1` steps
for the kept one's `n` gives the same answer and state count. -/
theorem ground4_fresh (hwf : EnvWF env) {natOk strOk : Bool} {maxNat F : Nat} {P₀ : G4Prog}
    (hnat : natOk = true → natLitStored env = true) (hstr : strOk = true → strLitStored env = true)
    (hP₀ : P₀.kTag.size = 0 ∨ (KeptOK env P₀ ∧ P₀.flags = (natOk, strOk, maxNat))) {e : Expr}
    (he : e.looseBVarsBounded 0 = true)
    (hb : (ground4BoolCoreF env.find? env.findProj? natOk strOk maxNat F P₀ e).1.1 ≠
      .error (.decline "ground evaluation did not finish within its step budget")) :
    (ground4BoolCoreF env.find? env.findProj? natOk strOk maxNat (2 * F + 1) {} e).1.1 =
        (ground4BoolCoreF env.find? env.findProj? natOk strOk maxNat F P₀ e).1.1 ∧
      (ground4BoolCoreF env.find? env.findProj? natOk strOk maxNat (2 * F + 1) {} e).1.2.1 =
        (ground4BoolCoreF env.find? env.findProj? natOk strOk maxNat F P₀ e).1.2.1 := by
  have hKA := setup_kept (maxNat := maxNat) hnat hstr (hP₀.imp id (·.1))
  have hKB := setup_kept (maxNat := maxNat) (P₀ := {}) hnat hstr (.inl rfl)
  have hfA := setup_flags env.find? env.findProj? (hP₀.imp id (·.2))
  have hfB := setup_flags env.find? env.findProj? (P₀ := {}) (natOk := natOk) (strOk := strOk)
    (maxNat := maxNat) (.inl rfl)
  unfold ground4BoolCoreF at hb ⊢
  generalize g4Setup env.find? env.findProj? natOk strOk maxNat P₀ = PA at hKA hfA hb ⊢
  generalize g4Setup env.find? env.findProj? natOk strOk maxNat {} = PB at hKB hfB ⊢
  dsimp only at hb ⊢
  have hr := siteMS_rel hKA hKB (hfB.trans hfA.symm) e
  obtain ⟨h₂, hR₂⟩ := siteMS_minv hKA he
  have hsim := sim_run hwf (LookAgree.univ _ _) (fun _ => ⟨trivial, trivial, trivial, trivial, trivial⟩) e F
    _ _ _ _ h₂ hR₂ hr (2 * F + 1) (by omega)
  generalize g4Comp env.find? env.findProj? PA e = rA at hsim hb ⊢
  generalize g4Comp env.find? env.findProj? PB e = rB at hsim ⊢
  obtain ⟨oA, QA⟩ := rA
  obtain ⟨oB, QB⟩ := rB
  unfold MS.run siteMS at hsim
  dsimp only at hsim hb ⊢
  generalize g4Run env.find? env.findProj? F { QA with slotA := #[] } #[2, 0, 0, 0] #[5, 0, 0, 0] #[] #[] #[]
    QA.slotA #[] (Array.replicate 1024 0) 0 oA 0 0 0 = outA at hsim hb ⊢
  generalize g4Run env.find? env.findProj? (2 * F + 1) { QB with slotA := #[] } #[2, 0, 0, 0] #[5, 0, 0, 0]
    #[] #[] #[] QB.slotA #[] (Array.replicate 1024 0) 0 oB 0 0 0 = outB at hsim ⊢
  rcases hsim with ⟨st, rfl⟩ | ⟨g, st, rfl, rfl⟩ | ⟨sA, sB, lA, lB, hr', hm1, -, hv, rfl, rfl⟩
  · exact absurd rfl hb
  · cases g <;> exact ⟨rfl, rfl⟩
  · dsimp only
    have hg := hr'.regs
    simp only [RegRel, hm1] at hg
    obtain ⟨-, hx, -⟩ := hg
    rw [hx, hr'.st]
    have hcond : (sB.val[g4X4 sA.x]! == 1 && sB.val[g4X4 sA.x + 3]! == 0 &&
        sB.val[g4X4 sA.x + 1]! == sB.P.kTrue) =
        (sA.val[g4X4 sA.x]! == 1 && sA.val[g4X4 sA.x + 3]! == 0 && sA.val[g4X4 sA.x + 1]! == sA.P.kTrue) := by
      obtain ⟨w0, -, w3, hw⟩ := hr'.valW hv
      rw [w0, w3]
      by_cases h1 : sA.val[g4X4 sA.x]! = 1
      · rw [h1] at hw
        have hk : ERel (fun _ => True) sA.P sB.P sA.val[g4X4 sA.x + 1]! sB.val[g4X4 sA.x + 1]! := hw
        rw [ent_beq hr'.invA.toCompInv hr'.invB.toCompInv hk hr'.kTrue]
      · have h1' : (sA.val[g4X4 sA.x]! == 1) = false := by simpa using h1
        simp only [h1', Bool.false_and]
    rw [hcond]
    split <;> exact ⟨rfl, rfl⟩

end

end ConLeche.Verify.Ground
