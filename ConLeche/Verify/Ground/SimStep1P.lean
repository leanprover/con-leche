module

public import ConLeche.Verify.Ground.SimStep
import ConLeche.Verify.Ground.SimStep1
public import ConLeche.Verify.Ground.SimBridge
import ConLeche.Verify.Ground.Keys
import ConLeche.Verify.Ground.SimExt
import ConLeche.Verify.Ground.SimStep3
import ConLeche.Verify.Ground.Step1
import ConLeche.Verify.Ground.Step1I

public section

/-!
# The step simulation, mode 1: the projection frame (task #423 soundness, layer (d), item 2(c))

The frame's row words are `PiRel`-related (`FsRel.projTop`): no row on both
sides, or rows of one content, whose words are one (`PrjRel.words`) but for
the name id, related like the constructor's (`NidRel.iff`).  So the
engine's shape test is one Bool on both sides.  A string is compiled on
both sides (`StrNames` puts its names in `N`).
-/

namespace ConLeche.Verify.Ground

open ConLeche

section
variable {j : Nat} {N : Name → Prop} {env : Env} {f₂ : Name → Option ConstantInfo}
  {p₂ : Name → Nat → Option ProjEntry} {mx : Option Nat} {t₀ : Expr} {n : Nat}

/-- Related entries have one tag. -/
theorem MRel.tagEq (hag : LookAgree N env.find? env.findProj? f₂ p₂) {sA sB : MS}
    (hr : MRel j N env.find? env.findProj? f₂ p₂ sA sB) {kA kB : Nat} (hk : ERel N sA.P sB.P kA kB) :
    sB.P.kTag[kB]! = sA.P.kTag[kA]! :=
  get!_congr2 (EntRel.tag hr.invA hr.invB hk.1 (hr.natOkAt hag hk)
    (fun iA hi => (hag.find _ (hk.2 iA hi)).symm)).symm

/-- One name-id test on both sides. -/
theorem nid_beq {PA PB : G4Prog} (hA : NidOK PA) (hB : NidOK PB) {iA iB jA jB : Nat}
    (hi : NidRel PA PB iA iB) (hj : NidRel PA PB jA jB) : (iB == jB) = (iA == jA) := by
  have e := NidRel.iff hA hB hi hj
  by_cases h : iA = jA
  · rw [e.mp h, h, beq_self_eq_true, beq_self_eq_true]
  · rw [beq_false_of_ne h, beq_false_of_ne (fun h' => h (e.mpr h'))]

/-- **A string compiled on both sides**: the grown relation, the new nodes
related. -/
theorem MRel.compStr (hsN : strLitStored env = true → StrNames N) {sA sB : MS}
    (hR : RunOK env sA.P) (hr : MRel j N env.find? env.findProj? f₂ p₂ sA sB) (hok : sA.P.strOk = true)
    (s : String) :
    let rA := g4Comp env.find? env.findProj? sA.P (strLitToConstructor s)
    let rB := g4Comp f₂ p₂ sB.P (strLitToConstructor s)
    MRel j N env.find? env.findProj? f₂ p₂ { sA with P := rA.2 } { sB with P := rB.2 } ∧
      ExtR sA.P rA.2 ∧ ExtR sB.P rB.2 ∧ RunOK env rA.2 ∧
      TRel N env.find? env.findProj? f₂ p₂ rA.2 rB.2 rA.1 rB.1 := by
  intro rA rB
  have cA := g4Comp_spec env.find? env.findProj? sA.P (strLitToConstructor s) hr.invA
  have cB := g4Comp_spec f₂ p₂ sB.P (strLitToConstructor s) hr.invB
  exact ⟨hr.ext cA.2.1.toExtR cB.2.1.toExtR cA.1 cB.1 cA.2.1.site cB.2.1.site
      (fun h0 => (hr.code h0).ext hr.invA.toTabInv hr.invB.toTabInv cA.2.1 cB.2.1), cA.2.1.toExtR,
    cB.2.1.toExtR, hR.ext cA.2.1.toExtR cA.2.1.site,
    TRel.ofComp (NamesIn.strLit (hsN (hR.str.symm.trans hok)) s) cA.2.2 cB.2.2⟩

/-- **Mode 1 at a projection frame.** -/
theorem sim_mode1p (hag : LookAgree N env.find? env.findProj? f₂ p₂)
    (hsN : strLitStored env = true → StrNames N) (ih : SimAt j N env f₂ p₂ mx t₀ n)
    {sA sB : MS} {oc : Nat → Expr} {fl : List Fr}
    (h : MInv env t₀ oc sA fl) (hR : RunOK env sA.P) (hr : MRel j N env.find? env.findProj? f₂ p₂ sA sB)
    (hm : sA.mode = 1) (hn : 0 < sA.fs.size) (ht : sA.fs[sA.fs.size - 1]! &&& 15 = 4) {m : Nat}
    (hmn : (j = 0 ∧ m = n + 1) ∨ (j = 1 ∧ 2 * n + 1 ≤ m)) :
    OutRel j N env f₂ p₂ (sA.run env.find? env.findProj? mx (n + 1)) (sB.run f₂ p₂ mx m) := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hmB : sB.mode = 1 := by rw [hr.mode, hm]
  have hg := hr.regs
  simp only [RegRel, hm] at hg
  obtain ⟨he, hx, hpc⟩ := hg
  have hxl := (h.val1 hm).1
  unfold MS.run
  rw [hm, g4Run.eq_7 env.find? env.findProj? mx sA.P sA.cel sA.val sA.ev sA.fs sA.argA sA.slots sA.mem sA.mH 1
    sA.pc sA.env sA.x sA.st n (by decide) (by decide) (by decide) (by decide), hmB,
    g4Run.eq_7 f₂ p₂ mx sB.P sB.cel sB.val sB.ev sB.fs sB.argA sB.slots sB.mem sB.mH 1
    sB.pc sB.env sB.x sB.st m (by decide) (by decide) (by decide) (by decide)]
  rw [hr.fs.1, hx, hr.fs.top hn]
  obtain ⟨w0, w2, w3, hw⟩ := hr.valW hxl
  obtain ⟨hpi, hpop⟩ := hr.fs.projTop hn ht
  split
  next h0 => simp only [beq_iff_eq] at h0; omega
  next =>
  split
  next ht' => rw [ht] at ht'; cases ht'
  next ht' => rw [ht] at ht'; cases ht'
  next ht' => rw [ht] at ht'; cases ht'
  rotate_left
  next ht' => rw [ht] at ht'; cases ht'
  next _ _ _ h4 _ => exact absurd ht h4
  dsimp only
  rcases hpi with ⟨e0, e0'⟩ | ⟨qA, qB, eA, eB, hq⟩
  · rw [e0, e0']
    simp only [beq_self_eq_true, ↓reduceIte]
    obtain ⟨fl', h'⟩ := step_proj_pop h hm hn ht
    refine ih.app (sB := { sB with fs := sB.fs.pop.pop, mode := 1, pc := 0, env := 0, x := 0 }) h' hR ?_
      (m := m) (by omega)
    exact { hr with
      fs := hpop
      mode := rfl
      regs := ⟨rfl, rfl, rfl⟩ }
  have hpi' : sA.fs[sA.fs.size - 2]! ≠ 0 := by rw [eA]; omega
  rw [eA, eB]
  simp only [Nat.add_one_ne_zero, beq_iff_eq, ↓reduceIte, Nat.add_sub_cancel]
  rw [w0]
  split
  next hv =>
    rw [hv] at hw
    have hk : ERel N sA.P sB.P sA.val[g4X4 sA.x + 1]! sB.val[g4X4 sA.x + 1]! := hw
    obtain ⟨p₁, p₂', p₃, p₄, p₅, jA, jB, ejA, ejB, hj⟩ := PrjRel.words hr.invA.toTabInv hr.invB.toTabInv hq
    rw [hr.tagEq hag hk, w3, w2, hr.argA, ← get!_congr2 p₁, ← get!_congr2 p₂', ← get!_congr2 p₃,
      ← get!_congr2 p₄, ← get!_congr2 p₅, get!_of_some ejB]
    by_cases h1 : sA.P.kTag[sA.val[g4X4 sA.x + 1]!]! = 1
    · obtain ⟨iA, -, hiA, -, -⟩ := hk.1
      have hkl : sA.val[g4X4 sA.x + 1]! < sA.P.kInfo.size := lt_of_some hiA
      obtain ⟨c, us, nP, nF, hi, -⟩ := (hr.invA.ents _ hkl).tag1 hkl
        (by rw [some_of_lt (by rw [hr.invA.sizes]; exact hkl), h1])
      obtain ⟨hiB, -, -, ea, ed, iA', iB', eiA, eiB, hn'⟩ :=
        hk.1.ctorW hr.invA hr.invB hi (hag.find c (hk.2 _ hi)).symm
      rw [← get!_congr2 ea, ← get!_congr2 ed, get!_of_some eiB, getElem!_of_getElem? hiB,
        nid_beq hr.invA.nidOK hr.invB.nidOK hn' hj, ← get!_of_some eiA, ← get!_of_some ejA,
        getElem!_of_getElem? hi]
      dsimp only
      simp only [Bool.or_true, Bool.and_true]
      split
      next hc =>
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
        obtain ⟨⟨⟨⟨⟨hc1, hc2⟩, hc3⟩, hc4⟩, hc5⟩, hc6⟩ := hc
        obtain ⟨fl', h'⟩ := step_proj_ctor h hm hn ht hpi' hv hc1 (by rw [eA]; exact hc2)
          (by rw [eA]; exact hc3) (by rw [eA]; exact hc4) hc5 (by rw [eA]; exact hc6)
        rw [eA, Nat.add_sub_cancel] at h'
        refine ih.app (sB := { sB with
            fs := sB.fs.pop.pop
            argA := sA.argA
            mode := 2
            pc := 0
            env := 0
            x := sA.argA[sA.val[g4X4 sA.x + 2]! + sA.P.pNP[qA]! + sA.P.pIdx[qA]!]! }) h' hR ?_
          (m := m) (by omega)
        exact { hr with
          fs := hpop
          argA := rfl
          memoB := (hr.argA ▸ hr.memoB : MemoTab sB.mem sA.argA sB.mH)
          mode := rfl
          regs := ⟨rfl, rfl, rfl⟩ }
      next => exact .inr (.inl ⟨_, _, rfl, by rw [hr.st]⟩)
    · have h1' : (sA.P.kTag[sA.val[g4X4 sA.x + 1]!]! == 1) = false := by simpa using h1
      simp only [h1', Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      exact .inr (.inl ⟨_, _, rfl, by rw [hr.st]⟩)
  next hv =>
    rw [hv] at hw
    obtain ⟨⟨s, hsA, hsB⟩, hsN'⟩ :=
      (hw : StrRel sA.P sB.P sA.val[g4X4 sA.x + 1]! sB.val[g4X4 sA.x + 1]! ∧ StrNames N)
    rw [hr.strOk hsN']
    split
    next => exact .inr (.inl ⟨_, _, rfl, by rw [hr.st]⟩)
    next hok =>
    have hok' : sA.P.strOk = true := by simpa using hok
    obtain ⟨fl', h'⟩ := step_proj_str hR h hm hn ht hv hok'
    rw [getElem!_of_getElem? hsA, eA] at h'
    rw [getElem!_of_getElem? hsA, getElem!_of_getElem? hsB]
    obtain ⟨hr', hxA, hxB, hR', hT⟩ := hr.compStr hsN hR hok' s
    refine ih.app (sB := { sB with
        P := (g4Comp f₂ p₂ sB.P (strLitToConstructor s)).2
        fs := (sB.fs.pop.pop.push (qB + 1)).push 4
        mode := 0
        pc := (g4Comp f₂ p₂ sB.P (strLitToConstructor s)).1
        env := 0
        x := 0 }) h' hR' ?_ (m := m) (by omega)
    exact { hr' with
      fs := (hpop.ext hxA hxB).pushProj (.inr ⟨qA, qB, rfl, rfl, hq.ext hxA hxB⟩)
      mode := rfl
      regs := ⟨rfl, rfl, hT⟩ }
  next =>
    obtain ⟨fl', h'⟩ := step_proj_pop h hm hn ht
    refine ih.app (sB := { sB with fs := sB.fs.pop.pop, mode := 1, pc := 0, env := 0, x := 0 }) h' hR ?_
      (m := m) (by omega)
    exact { hr with
      fs := hpop
      mode := rfl
      regs := ⟨rfl, rfl, rfl⟩ }

end

end ConLeche.Verify.Ground
