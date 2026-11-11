module

public import ConLeche.Verify.Ground.Step1N
public import ConLeche.Verify.EnvWF
import ConLeche.Verify.Ground.Sound
import ConLeche.Verify.Ground.Step1
import ConLeche.Verify.Ground.Step1I

public section

/-!
# The site: `ground4BoolCoreF` (task #423 soundness, layer (c))

The site sets the program up (fresh, or the one an earlier run of the
declaration kept), compiles the term, and runs the machine from the empty
stack.  A run that answers `true` ends at the constructor `Bool.true` with
no argument, so the term reduces to `Bool.true` (`ground4_true`); the
program the site keeps for the next run is again one the next run can start
from (`ground4_kept`).

`KeptOK` is what a kept program carries: the table invariant, the run's
flag facts, and the slot epoch above every slot entry (an earlier run's cell
never reads as a current one).
-/

namespace ConLeche.Verify.Ground

open ConLeche ConLeche.Cached ConLeche.Rules

/-- **A program a run can start from.** -/
structure KeptOK (env : Env) (P : G4Prog) : Prop where
  inv : Inv env.find? env.findProj? P
  run : RunOK env P
  epoch : ∀ i, i < P.slotA.size → P.slotA[i]! ≤ P.epBase

/-- A slot array at or below the epoch holds no current cell. -/
theorem slotGet_old {slots : Array Nat} {ep : Nat} (h : ∀ i, i < slots.size → slots[i]! ≤ ep)
    (sl : Nat) : g4SlotGet slots ep sl = 0 := by
  unfold g4SlotGet
  split
  · rename_i hs
    have := h sl hs
    simp only
    split <;> omega
  · rfl

section
variable {find? : Name → Option ConstantInfo} {findProj? : Name → Nat → Option ProjEntry}

/-- The program with the site's words set. -/
@[expose] def _root_.ConLeche.Cached.G4Prog.setSite (P : G4Prog) (kT kF kZ kS ep : Nat)
    (sa : Array Nat) : G4Prog :=
  { P with kTrue := kT, kFalse := kF, kZero := kZ, kSucc := kS, epBase := ep, slotA := sa }

/-- Setting the site's words is growth (both ways). -/
theorem ExtR.setSite (P : G4Prog) (kT kF kZ kS ep : Nat) (sa : Array Nat) :
    ExtR P (P.setSite kT kF kZ kS ep sa) :=
  ⟨fun _ _ => rfl, Nat.le_refl _, fun _ _ => rfl, Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ h => h, fun _ _ => rfl, fun _ _ => rfl, Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ h => h, rfl⟩

theorem ExtR.setSite_back (P : G4Prog) (kT kF kZ kS ep : Nat) (sa : Array Nat) :
    ExtR (P.setSite kT kF kZ kS ep sa) P :=
  ⟨fun _ _ => rfl, Nat.le_refl _, fun _ _ => rfl, Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ h => h, fun _ _ => rfl, fun _ _ => rfl, Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ h => h, rfl⟩

/-- **The invariant reads none of the site's words.** -/
theorem Inv.setSite {P : G4Prog} (hI : Inv find? findProj? P) (kT kF kZ kS ep : Nat)
    (sa : Array Nat) : Inv find? findProj? (P.setSite kT kF kZ kS ep sa) where
  szs := hI.szs
  sizes := hI.sizes
  kSlotSize := hI.kSlotSize
  kMap := hI.kMap
  closed a' o h := by
    obtain ⟨s, sl, h₁, h₂, h₃, h₄⟩ := hI.closed a' o h
    exact ⟨s, sl, h₁, h₂.ext (ExtR.setSite P kT kF kZ kS ep sa), h₃, h₄⟩
  slots := by
    obtain ⟨σ, hσ⟩ := hI.slots
    exact ⟨σ, fun sl t h => hσ sl t (h.ext (ExtR.setSite_back P kT kF kZ kS ep sa))⟩
  ents k hk := by
    have hx := ExtR.setSite P kT kF kZ kS ep sa
    exact (hI.ents k hk).extR hx hk rfl
      (fun _ _ _ _ _ _ _ _ _ hi' i _ hi₁ hr => hr.extR hx (hI.rows_lt ⟨_, _, _, _, _, _, _, _, _,
        hi', Nat.le_add_right _ _, by omega⟩) rfl)
  prjs q hq := (hI.prjs q hq).ext (ExtR.setSite P kT kF kZ kS ep sa) hq
  nidOK := hI.nidOK
  rowsDisj k k' r h h' := hI.rowsDisj k k' r h h'

/-- The flag facts across a new epoch (the basis entries kept). -/
theorem RunOK.epoch {env : Env} {P : G4Prog} (h : RunOK env P) (ep : Nat) (sa : Array Nat) :
    RunOK env (P.setSite P.kTrue P.kFalse P.kZero P.kSucc ep sa) :=
  ⟨h.nat, h.str, h.zero, h.succ, h.tru, h.fls⟩

end

section
variable {env : Env}

/-- The machine before the site term is compiled: the bottom cell and the
bottom value, no frame, the bottom value returned. -/
@[expose] def preMS (P : G4Prog) : MS :=
  ⟨P, #[2, 0, 0, 0], #[5, 0, 0, 0], #[], #[], #[], P.slotA, #[], Array.replicate 1024 0, 1, 0, 0, 0, 0⟩

/-- The pre-state has the invariant, at the empty stack (the bottom value is
an erased reduct of anything). -/
theorem preMS_minv {P : G4Prog} (hK : KeptOK env P) (t₀ : Expr) :
    MInv env t₀ (fun _ => bot) (preMS P) [] := by
  have hN : (preMS P).N = 1 := by simp [preMS, MS.N]
  have hst : SInv env (fun _ => bot) (preMS P) :=
    { prog := hK.inv
      celSz := by simp [preMS]
      valSz := by simp [preMS]
      evSz := by simp [preMS]
      memSz := by simp [preMS]
      cell0 := by rw [hN]; exact Nat.one_pos
      oc0 := rfl
      val0 := by simp [preMS]
      closed := fun _ _ => rfl
      cells := fun c hc => by
        obtain rfl : c = 0 := by rw [hN] at hc; omega
        unfold CellOK
        simp only [preMS]
        exact ⟨bot, .other (by simp), .refl⟩
      valRef := fun c hc _ => by
        obtain rfl : c = 0 := by rw [hN] at hc; omega
        simp [preMS]
      evRef := fun i h => absurd h (by simp [preMS])
      argRef := fun j h => absurd h (by simp [preMS])
      slotsOK := fun sl h => absurd (slotGet_old hK.epoch sl) h
      memo := fun r h => absurd h (by simp [preMS]) }
  refine ⟨hst, .nil, fun _ h => (nomatch h), ?_⟩
  show 0 < (preMS P).val.size / 4 ∧ ∃ t, ValDen P (preMS P).val #[] #[] (fun _ => bot) 0 t ∧
    K env t₀ P #[] (fun _ => bot) [] t
  exact ⟨by simp [preMS], bot, .other (by simp [preMS]), .forget .refl (.bot t₀)⟩

/-- Evaluation under a grown program. -/
theorem MInv.withProg0 {t₀ : Expr} {oc : Nat → Expr} {s : MS} {fl : List Fr}
    (h : MInv env t₀ oc s fl) (hm : s.mode = 0) {P' : G4Prog}
    (hI : Inv env.find? env.findProj? P') (hx : ExtR s.P P') (hep : P'.epBase = s.P.epBase) :
    MInv env t₀ oc { s with P := P' } fl := by
  refine ⟨h.store.grow (s' := { s with P := P' }) hI hx hep (Pre.refl _) h.store.celSz (Pre.refl _)
    h.store.valSz (Pre.refl _) h.store.evSz (Pre.refl _) rfl rfl (Agree.refl _ _) h.store.evRef
    h.store.argRef (fun c h₁ h₂ => absurd h₂ (by simp only [MS.N] at h₁ ⊢; omega)), h.stack,
    h.frames.grow hx (Pre.refl _) (Nat.le_refl _), ?_⟩
  have hf := h.focus
  simp only [Focus, hm] at hf ⊢
  obtain ⟨u, hu, hK⟩ := hf
  exact ⟨u, hu.pre hx (Pre.refl _), K.grow env t₀ oc hx (Pre.refl _) fl h.frames hK⟩

end

section
variable {env : Env}

/-- The compiler keeps the site's words. -/
theorem Ext.site_eqs {P P' : G4Prog} (hx : Ext P P') :
    P'.kTrue = P.kTrue ∧ P'.kFalse = P.kFalse ∧ P'.kZero = P.kZero ∧ P'.kSucc = P.kSucc ∧
      P'.epBase = P.epBase ∧ P'.slotA = P.slotA := by
  have := hx.site; simp only [G4Prog.site, Prod.mk.injEq] at this; exact this

/-- **One site run**: from a program a run can start from, the compiled
site term's run that finishes keeps a program the next run can start from,
and its `Bool.true` answer is a reduction of the term to `Bool.true`. -/
theorem site_run (hwf : EnvWF env) {P : G4Prog} (hK : KeptOK env P) {e : Expr}
    (he : e.looseBVarsBounded 0 = true) {fuel v : Nat} {val : Array Nat} {P' : G4Prog}
    {sl : Array Nat} {cells st left : Nat}
    (hrun : g4Run env.find? env.findProj? fuel
      { (g4Comp env.find? env.findProj? g4CompFuel P e).2 with slotA := #[] } #[2, 0, 0, 0]
      #[5, 0, 0, 0] #[] #[] #[] (g4Comp env.find? env.findProj? g4CompFuel P e).2.slotA #[]
      (Array.replicate 1024 0) 0 (g4Comp env.find? env.findProj? g4CompFuel P e).1 0 0 0 =
        .done v val P' sl cells st left) :
    KeptOK env { P' with slotA := sl, epBase := P'.epBase + cells } ∧
    ((val[g4X4 v]! == 1 && val[g4X4 v + 3]! == 0 && val[g4X4 v + 1]! == P'.kTrue) = true →
      ∀ d, Red env d e (.const boolTrueName [])) := by
  -- compile the term at the pre-state
  have h₁ := (preMS_minv hK e).enterCompiled (fs := #[]) (fl' := []) .nil (fun _ h => (nomatch h)) he
    (ERed.refl : K env e (preMS P).P (preMS P).argA (fun _ => bot) [] e)
  have hc := (g4Comp_spec env.find? env.findProj? g4CompFuel).1 P e hK.inv
  change MInv env e (fun _ => bot) { preMS P with
    P := (g4Comp env.find? env.findProj? g4CompFuel P e).2, fs := #[], mode := 0,
    pc := (g4Comp env.find? env.findProj? g4CompFuel P e).1, env := 0, x := 0 } [] at h₁
  generalize g4Comp env.find? env.findProj? g4CompFuel P e = r at hc hrun h₁
  obtain ⟨o, P₂⟩ := r
  obtain ⟨hI₂, hx₂, -⟩ := hc
  dsimp only at hI₂ hx₂ hrun h₁
  obtain ⟨-, -, -, -, -, hsa⟩ := hx₂.site_eqs
  rw [hsa] at hrun
  -- set the slot array aside, as the site does
  have h₂ := h₁.withProg0 rfl (hI₂.setSite P₂.kTrue P₂.kFalse P₂.kZero P₂.kSucc P₂.epBase #[])
    (ExtR.setSite P₂ P₂.kTrue P₂.kFalse P₂.kZero P₂.kSucc P₂.epBase #[]) rfl
  have hR₂ := (hK.run.ext hx₂.toExtR hx₂.site).epoch P₂.epBase #[]
  obtain ⟨s', oc', hM, hR', hm', hxv, hval, hP, hsl, hcel⟩ :=
    run_sound hwf e fuel _ _ _ h₂ hR₂ (by exact hrun)
  subst hxv hval hP hsl hcel
  refine ⟨⟨hM.store.prog.setSite _ _ _ _ _ _, hR'.epoch _ _, fun i hi => ?_⟩, fun hcond d => ?_⟩
  · have h := hM.store.slotsOK i
    have hN : s'.N = s'.cel.size >>> 2 := by simp [MS.N, Nat.shiftRight_eq_div_pow]
    unfold g4SlotGet at h
    simp only [hi, ↓reduceIte] at h
    show s'.slots[i]! ≤ s'.P.epBase + (s'.cel.size >>> 2)
    split at h
    · have := (h (by omega)).1; omega
    · omega
  · simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    obtain ⟨⟨h1, h0⟩, hkt⟩ := hcond
    have hf := hM.focus
    simp only [Focus, hm'] at hf
    obtain ⟨-, t, hv, hKt⟩ := hf
    rw [g4X4_eq] at h1 h0 hkt
    obtain ⟨-, -, rfl⟩ := hv.inv1 h1
    rw [h0, hkt, span_zero, List.map_nil, hR'.tru.2] at hKt
    exact ERed.lift_const hKt (Approx.refl e)
end

section
variable {env : Env}

/-- A resolved constant's entry, under growth. -/
theorem resolved_entry {P P' : G4Prog} (hx : ExtR P P') {k : Nat} {info : G4Info} {c : Name}
    {us : List Level} (hi : P.kInfo[k]? = some info) (ha : Approx (infoTerm info) (.const c us)) :
    k < P'.kInfo.size ∧ entryTerm P' k = .const c us := by
  have hk : k < P.kInfo.size := lt_of_some hi
  refine ⟨Nat.lt_of_lt_of_le hk hx.kInfoSize, ?_⟩
  unfold entryTerm
  rw [hx.kInfo k hk, hi]
  cases info <;> exact (Approx.const_inv ha).symm

/-- **The program a run starts from** is one it can start from. -/
theorem setup_kept {natOk strOk : Bool} {maxNat : Nat} {P₀ : G4Prog}
    (hnat : natOk = true → natLitStored env = true) (hstr : strOk = true → strLitStored env = true)
    (hP₀ : P₀.kTag.size = 0 ∨ KeptOK env P₀) :
    KeptOK env (g4Setup env.find? env.findProj? natOk strOk maxNat P₀) := by
  unfold g4Setup
  split
  · dsimp only
    have h₀ := Inv.fresh (find? := env.find?) (findProj? := env.findProj?) natOk strOk maxNat
    obtain ⟨hI₁, hx₁, -, i₁, hi₁, ha₁⟩ := g4Resolve_spec env.find? env.findProj? _ boolTrueName [] h₀
    generalize g4Resolve env.find? env.findProj? ({ natOk := natOk, strOk := strOk, maxNat := maxNat } : G4Prog)
      boolTrueName [] = q₁ at hI₁ hx₁ hi₁ ha₁ ⊢
    obtain ⟨kT, P₁⟩ := q₁
    obtain ⟨hI₂, hx₂, -, i₂, hi₂, ha₂⟩ := g4Resolve_spec env.find? env.findProj? P₁ boolFalseName [] hI₁
    generalize g4Resolve env.find? env.findProj? P₁ boolFalseName [] = q₂ at hI₂ hx₂ hi₂ ha₂ ⊢
    obtain ⟨kF, P₂⟩ := q₂
    obtain ⟨hI₃, hx₃, -, i₃, hi₃, ha₃⟩ := g4Resolve_spec env.find? env.findProj? P₂ natZeroName [] hI₂
    generalize g4Resolve env.find? env.findProj? P₂ natZeroName [] = q₃ at hI₃ hx₃ hi₃ ha₃ ⊢
    obtain ⟨kZ, P₃⟩ := q₃
    obtain ⟨hI₄, hx₄, -, i₄, hi₄, ha₄⟩ := g4Resolve_spec env.find? env.findProj? P₃ natSuccName [] hI₃
    generalize g4Resolve env.find? env.findProj? P₃ natSuccName [] = q₄ at hI₄ hx₄ hi₄ ha₄ ⊢
    obtain ⟨kS, P₄⟩ := q₄
    dsimp only at *
    have hx₁₄ := ((hx₁.trans hx₂).trans hx₃).trans hx₄
    have hx₂₄ := (hx₂.trans hx₃).trans hx₄
    have hx₃₄ := hx₃.trans hx₄
    obtain ⟨e₁, e₂, -⟩ := hx₁₄.toExtR.flagsEq
    obtain ⟨-, -, -, -, -, hsa⟩ := hx₁₄.site_eqs
    refine ⟨hI₄.setSite kT kF kZ kS P₄.epBase P₄.slotA, ⟨fun h => hnat (e₁.symm.trans h),
      fun h => hstr (e₂.symm.trans h), resolved_entry hx₄.toExtR hi₃ ha₃,
      resolved_entry (ExtR.refl _) hi₄ ha₄, resolved_entry hx₂₄.toExtR hi₁ ha₁,
      resolved_entry hx₃₄.toExtR hi₂ ha₂⟩, fun i hi => ?_⟩
    simp only [hsa] at hi
    exact absurd hi (by simp)
  · rename_i h
    rcases hP₀ with h0 | hK
    · simp [h0] at h
    · exact hK

end

section
variable {env : Env}

/-- **The site is sound**: from a kept program the site can use (or none),
the program it keeps is one the next run can use (or none), and its `true`
is a reduction of the term to `Bool.true`. -/
theorem ground4_site (hwf : EnvWF env) {natOk strOk : Bool} {maxNat fuel : Nat} {P₀ : G4Prog}
    (hnat : natOk = true → natLitStored env = true) (hstr : strOk = true → strLitStored env = true)
    (hP₀ : P₀.kTag.size = 0 ∨ KeptOK env P₀) {e : Expr} (he : e.looseBVarsBounded 0 = true) :
    ((ground4BoolCoreF env.find? env.findProj? natOk strOk maxNat fuel P₀ e).2.kTag.size = 0 ∨
      KeptOK env (ground4BoolCoreF env.find? env.findProj? natOk strOk maxNat fuel P₀ e).2) ∧
    ((ground4BoolCoreF env.find? env.findProj? natOk strOk maxNat fuel P₀ e).1.1 = .ok true →
      ∀ d, Red env d e (.const boolTrueName [])) := by
  have hK := setup_kept (maxNat := maxNat) hnat hstr hP₀
  unfold ground4BoolCoreF
  generalize g4Setup env.find? env.findProj? natOk strOk maxNat P₀ = P at hK ⊢
  dsimp only
  split
  next v val P' sl cells st left hrun =>
    obtain ⟨hK', htrue⟩ := site_run hwf hK he hrun
    split
    next hc => exact ⟨.inr hK', fun _ => htrue hc⟩
    next => exact ⟨.inr hK', fun h => by cases h⟩
  next => exact ⟨.inl rfl, fun h => by cases h⟩
  next => exact ⟨.inl rfl, fun h => by cases h⟩

end

end ConLeche.Verify.Ground
