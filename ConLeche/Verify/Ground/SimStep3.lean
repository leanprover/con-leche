module

public import ConLeche.Verify.Ground.SimBridge
public import ConLeche.Verify.Ground.SimStep
public import ConLeche.Verify.EnvWF
import ConLeche.Verify.Ground.SimExt
import ConLeche.Verify.Ground.SimMemo
import ConLeche.Verify.Ground.SimStep0
import ConLeche.Verify.Ground.Step3
import ConLeche.Verify.Ground.Keys
import ConLeche.Verify.Ground.Sound

public section

/-!
# The step simulation, mode 3 (task #423 soundness, layer (d), item 2(c))

Dispatching a constant entry.  The two entries are of one key, so the tag,
arity and words agree (`EntRel.*W`); the argument cells on top are one
(`FsRel.args`), so the memo answers agree (`memoFind_rel`).  The one place
the runs part is a definition's body: compiled on first use, so A may
compile where B has the body (B takes no step), B where A has it (B takes
two steps: its compile, then A's step, `sim_delta_body`), or both.
-/

namespace ConLeche.Verify.Ground

open ConLeche

section
variable {j : Nat} {N : Name → Prop} {env : Env} {f₂ : Name → Option ConstantInfo}
  {p₂ : Name → Nat → Option ProjEntry} {t₀ : Expr} {n : Nat}

theorem get!_congr2 {a b : Array Nat} {i j : Nat} (h : a[i]? = b[j]?) : a[i]! = b[j]! := by
  rw [getElem!_def, getElem!_def, h]

/-- **The dispatch's words** on both sides: one `pc`, related entries, one tag. -/
theorem MRel.dispatch (hag : LookAgree N env.find? env.findProj? f₂ p₂) {sA sB : MS}
    (hr : MRel j N env.find? env.findProj? f₂ p₂ sA sB) (hm : sA.mode = 3) :
    sB.pc = sA.pc ∧ ERel N sA.P sB.P sA.x sB.x ∧ sB.P.kTag[sB.x]! = sA.P.kTag[sA.x]! := by
  have hg := hr.regs
  simp only [RegRel, hm] at hg
  obtain ⟨-, hpc, hE⟩ := hg
  refine ⟨hpc, hE, get!_congr2 (EntRel.tag hr.invA hr.invB hE.1 (hr.natOkAt hag hE)
    (fun iA hi => (hag.find _ (hE.2 iA hi)).symm)).symm⟩

/-- A K word names the one rule's constructor, a constructor with no fields. -/
theorem kfabKey_some {f : Name → Option ConstantInfo} {c : Name} {us : List Level} {key : Name × List Level}
    (h : kfabKey f c us = some key) :
    ∃ cv mI rP rl cvj nP, f c = some (.recInfo cv mI rP true [rl]) ∧ key.1 = rl.ctor ∧
      f rl.ctor = some (.ctorInfo cvj nP 0) := by
  unfold kfabKey at h
  split at h
  next cv mI rP rl hc =>
    split at h
    · split at h
      next cvj nP hj =>
        split at h
        · cases h; exact ⟨cv, mI, rP, rl, cvj, nP, hc, rfl, hj⟩
        · cases h
      · cases h
    · cases h
  · cases h

/-- **The K constructor's entries** of two related recursor entries: none on
both sides, or related, of one arity. -/
theorem kfab_rel (hag : LookAgree N env.find? env.findProj? f₂ p₂) {PA PB : G4Prog}
    (hIA : Inv env.find? env.findProj? PA) (hIB : Inv f₂ p₂ PB) {c : Name} {us : List Level} {fA fB : Nat}
    (hN : N c) (hA : KfabKey env.find? PA c us fA) (hB : KfabKey f₂ PB c us fB) :
    (fA = 0 ∧ fB = 0) ∨ ∃ cA cB, fA = cA + 1 ∧ fB = cB + 1 ∧ ERel N PA PB cA cB ∧
      PA.kArity[cA]? = PB.kArity[cB]? := by
  rcases KfabKey.rel hA hB (.inr (hag.kfab c us hN).symm) with h0 | ⟨cA, cB, rfl, rfl, hr⟩
  · exact .inl h0
  refine .inr ⟨cA, cB, rfl, rfl, ⟨hr, fun iA hi => ?_⟩, ?_⟩ <;>
    rcases hA with ⟨-, h⟩ | ⟨key, kc, info, hk, hkc, hkI, hik⟩
  · cases h
  · obtain rfl : kc = cA := by omega
    rw [hi] at hkI; obtain rfl := Option.some.inj hkI
    obtain ⟨cv, mI, rP, rl, cvj, nP, hc, hkey, -⟩ := kfabKey_some hk
    rw [hik, hkey]
    exact (hag.rules c cv mI rP true [rl] hN hc rl (List.mem_singleton_self _)).1
  · cases h
  · obtain rfl : kc = cA := by omega
    obtain ⟨cv, mI, rP, rl, cvj, nP, hc, hkey, hj⟩ := kfabKey_some hk
    have hNj : N rl.ctor := (hag.rules c cv mI rP true [rl] hN hc rl (List.mem_singleton_self _)).1
    have e := EntRel.arity_ctor hIA hIB hr (cv := cvj) (nP := nP) (nF := 0) (fun iA hi => by
      rw [hkI] at hi; obtain rfl := Option.some.inj hi
      rw [hik, hkey, hag.find _ hNj]; exact ⟨hj, hj⟩)
    rw [e.1, e.2]

/-- **One memo answer** at the argument cells on top, on both sides. -/
theorem MRel.memoFind {sA sB : MS} (hr : MRel j N env.find? env.findProj? f₂ p₂ sA sB)
    (hE : ERel N sA.P sB.P sA.x sB.x) {k : Nat} (hk : k ≤ g4CountArgs sA.fs sA.fs.size 0) :
    g4MemoFind sB.mem sB.mH sB.fs sB.argA sB.x k sB.mH.size
        (g4Slot (g4Hash sB.fs sB.x k 0 (UInt64.ofNat sB.x)) sB.mH.size) =
      g4MemoFind sA.mem sA.mH sA.fs sA.argA sA.x k sA.mH.size
        (g4Slot (g4Hash sA.fs sA.x k 0 (UInt64.ofNat sA.x)) sA.mH.size) := by
  obtain ⟨-, htop, -⟩ := hr.fs.args
  rw [hash_congr _ _ 0 _ (htop.mono hk).at, memoFind_congr _ _ _ _ _ (htop.mono hk), hr.argA]
  exact memoFind_rel hr.invA.toCompInv hr.invB.toCompInv hr.mem hr.memoA (hr.argA ▸ hr.memoB) hE _

/-- **A memo miss** keeps the table: the record is new. -/
theorem memoTab_miss {mem mH fs argA : Array Nat} {k n c : Nat} (ht : MemoTab mem argA mH)
    (h0 : g4MemoFind mem mH fs argA k n mH.size (g4Slot (g4Hash fs k n 0 (UInt64.ofNat k)) mH.size) = 0)
    (hc : c ≠ 0) :
    MemoTab ((((mem.push k).push argA.size).push n).push c) (g4CopyArgs fs argA n 0)
      (g4MemoIns ((((mem.push k).push argA.size).push n).push c) (g4CopyArgs fs argA n 0) mH
        (mem.size >>> 2) (g4Hash fs k n 0 (UInt64.ofNat k))) := by
  obtain ⟨hsz, hpre, hcp⟩ := copyArgs_spec fs n 0 argA
  rw [shr2_eq]
  exact ht.ins (memoFind_zero ht h0) hc hpre hsz (fun i hi => by simpa using hcp i hi)

/-- **Collecting the arguments** into a constructor or partial-application
value (`w0` = 1 or 4), on both sides. -/
theorem sim_collect (ih : SimAt j N env f₂ p₂ t₀ n) {sA sB : MS} {oc : Nat → Expr} {fl : List Fr}
    (h : MInv env t₀ oc sA fl) (hR : RunOK env sA.P) (hr : MRel j N env.find? env.findProj? f₂ p₂ sA sB)
    (hm : sA.mode = 3) (hE : ERel N sA.P sB.P sA.x sB.x) {w0 : Nat} (hw : w0 = 1 ∨ w0 = 4) {m : Nat}
    (hmn : (j = 0 ∧ m = n) ∨ (j = 1 ∧ 2 * n ≤ m)) :
    OutRel j N env f₂ p₂
      (g4Run env.find? env.findProj? n sA.P sA.cel
        ((((sA.val.push w0).push sA.x).push sA.argA.size).push (g4CountArgs sA.fs sA.fs.size 0)) sA.ev
        (g4PopN sA.fs (g4CountArgs sA.fs sA.fs.size 0)) (g4CopyArgs sA.fs sA.argA (g4CountArgs sA.fs sA.fs.size 0) 0)
        sA.slots sA.mem sA.mH 1 0 0 (sA.val.size >>> 2) sA.st)
      (g4Run f₂ p₂ m sB.P sB.cel
        ((((sB.val.push w0).push sB.x).push sB.argA.size).push (g4CountArgs sA.fs sA.fs.size 0)) sB.ev
        (g4PopN sB.fs (g4CountArgs sA.fs sA.fs.size 0)) (g4CopyArgs sB.fs sB.argA (g4CountArgs sA.fs sA.fs.size 0) 0)
        sB.slots sB.mem sB.mH 1 0 0 (sB.val.size >>> 2) sB.st) := by
  obtain ⟨-, htop, hpop⟩ := hr.fs.args
  obtain ⟨fl', h'⟩ := step_collect h hm hw
  rw [hr.argA, hr.val.1, copyArgs_congr _ 0 _ htop.at]
  refine ih.app (sB := { sB with
      val := (((sB.val.push w0).push sB.x).push sA.argA.size).push (g4CountArgs sA.fs sA.fs.size 0),
      fs := g4PopN sB.fs (g4CountArgs sA.fs sA.fs.size 0),
      argA := g4CopyArgs sA.fs sA.argA (g4CountArgs sA.fs sA.fs.size 0) 0,
      mode := 1, pc := 0, env := 0, x := sA.val.size >>> 2 }) h' hR ?_ hmn
  exact { hr with
    val := hr.val.push h.store.valSz w0 _ _ _ _ (by rcases hw with rfl | rfl <;> exact hE)
    argA := rfl
    memoA := hr.memoA.argA (copyArgs_spec _ _ _ _).2.1
    memoB := (hr.argA ▸ hr.memoB : MemoTab sB.mem sA.argA sB.mH).argA (copyArgs_spec _ _ _ _).2.1
    fs := hpop _ (Nat.le_refl _)
    mode := rfl
    regs := ⟨rfl, rfl, rfl⟩ }

/-- The dispatch reaches a definition's body (`δ`): not a constructor,
recursor or neutral entry, and not an accelerated operation on two or fewer
arguments. -/
@[expose] def D3 (s : MS) : Prop :=
  (if s.pc == 1 then 0 else s.P.kTag[s.x]!) ≠ 1 ∧ (if s.pc == 1 then 0 else s.P.kTag[s.x]!) ≠ 2 ∧
    (if s.pc == 1 then 0 else s.P.kTag[s.x]!) ≠ 5 ∧
    ((if s.pc == 1 then 0 else s.P.kTag[s.x]!) == 3 && g4CountArgs s.fs s.fs.size 0 == 2) = false ∧
    ((if s.pc == 1 then 0 else s.P.kTag[s.x]!) == 3 && decide (g4CountArgs s.fs s.fs.size 0 < 2)) = false

/-- **Mode 3** away from a definition's body. -/
theorem sim_mode3n (hag : LookAgree N env.find? env.findProj? f₂ p₂)
    (ih : SimAt j N env f₂ p₂ t₀ n)
    {sA sB : MS} {oc : Nat → Expr} {fl : List Fr}
    (h : MInv env t₀ oc sA fl) (hR : RunOK env sA.P) (hr : MRel j N env.find? env.findProj? f₂ p₂ sA sB)
    (hm : sA.mode = 3) (hD : ¬D3 sA) {m : Nat} (hmn : (j = 0 ∧ m = n + 1) ∨ (j = 1 ∧ 2 * n + 1 ≤ m)) :
    OutRel j N env f₂ p₂ (sA.run env.find? env.findProj? (n + 1)) (sB.run f₂ p₂ m) := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hmB : sB.mode = 3 := by rw [hr.mode, hm]
  obtain ⟨hpc, hE, htg⟩ := hr.dispatch hag hm
  obtain ⟨hcnt, htop, hpop⟩ := hr.fs.args
  unfold MS.run
  rw [hm, hmB, g4Run.eq_6, g4Run.eq_6, hpc, htg]
  generalize hd : (if (sA.pc == 1) = true then 0 else sA.P.kTag[sA.x]!) = d
  split
  next =>
    dsimp only
    rw [hcnt]
    exact sim_collect ih h hR hr hm hE (.inl rfl) (by omega)
  next ht =>
    have hk : sA.x < sA.P.kInfo.size := by
      have hf := h.focus; simp only [Focus, hm] at hf; exact hf.1
    have hts : sA.P.kTag.size = sA.P.kInfo.size := h.store.prog.sizes
    have ht2 : sA.P.kTag[sA.x]? = some 2 := by
      split at hd
      · exact absurd hd (by decide)
      · rw [← hd]; exact some_of_lt (by omega)
    obtain ⟨c, lps, us, mI, rP, base, nr, isK, isEta, hinfo, -⟩ := (h.store.prog.ents sA.x hk).tag2 hk ht2
    have hNc : N c := hE.2 _ hinfo
    obtain ⟨bB, hinfoB, -, -, aA, aB, -⟩ :=
      hE.1.recW hr.invA hr.invB hinfo (hag.find c hNc).symm (hag.kfab c us hNc).symm
    obtain ⟨fA, eA, kA⟩ := hr.invA.kfab _ _ _ _ _ _ _ _ _ _ hinfo
    obtain ⟨fB, eB, kB⟩ := hr.invB.kfab _ _ _ _ _ _ _ _ _ _ hinfoB
    have hfab := kfab_rel hag hr.invA hr.invB hNc kA kB
    have hb : (if isK then 1 else 0) + (if isEta then 2 else 0) ≤ 3 := by split <;> split <;> omega
    rw [get!_of_some eA] at *
    rw [get!_of_some eB]
    generalize (if isK then 1 else 0) + (if isEta then 2 else 0) = b at hb eA eB ⊢
    have hmIA : sA.P.kArity[sA.x]? = some mI := aA
    rw [get!_of_some aA, get!_of_some aB]
    dsimp only
    by_cases hlt : g4CountArgs sA.fs sA.fs.size 0 < mI + 1
    · rw [ite_eq_left hlt, ite_eq_left (show g4CountArgs sB.fs sB.fs.size 0 < mI + 1 by rw [hcnt]; exact hlt)]
      rw [hcnt]
      exact sim_collect ih h hR hr hm hE (.inr rfl) (fuel_s hmn)
    rw [ite_eq_right hlt, ite_eq_right (show ¬g4CountArgs sB.fs sB.fs.size 0 < mI + 1 by rw [hcnt]; exact hlt)]
    have hle : mI + 1 ≤ g4CountArgs sA.fs sA.fs.size 0 := by omega
    rw [hr.memoFind hE hle]
    split
    next hhitA =>
      have hhit : (g4MemoFind sA.mem sA.mH sA.fs sA.argA sA.x (mI + 1) sA.mH.size
          (g4Slot (g4Hash sA.fs sA.x (mI + 1) 0 (UInt64.ofNat sA.x)) sA.mH.size) != 0) = true := by
        simpa using hhitA
      obtain ⟨fl', h'⟩ := step_memo_hit h hm (n := mI + 1) (by omega) hle (by simpa using hhit)
      refine ih.app (sB := { sB with
          fs := g4PopN sB.fs (mI + 1)
          mode := 2
          pc := 0
          env := 0
          x := g4MemoFind sA.mem sA.mH sA.fs sA.argA sA.x (mI + 1) sA.mH.size
            (g4Slot (g4Hash sA.fs sA.x (mI + 1) 0 (UInt64.ofNat sA.x)) sA.mH.size) })
        h' hR ?_ (fuel_s hmn)
      exact { hr with
        fs := hpop _ hle
        mode := rfl
        regs := ⟨rfl, rfl, rfl⟩ }
    next hhitA =>
    have hhit : ¬(g4MemoFind sA.mem sA.mH sA.fs sA.argA sA.x (mI + 1) sA.mH.size
        (g4Slot (g4Hash sA.fs sA.x (mI + 1) 0 (UInt64.ofNat sA.x)) sA.mH.size) != 0) = true := by
      simpa using hhitA
    have h0 : g4MemoFind sA.mem sA.mH sA.fs sA.argA sA.x (mI + 1) sA.mH.size
        (g4Slot (g4Hash sA.fs sA.x (mI + 1) 0 (UInt64.ofNat sA.x)) sA.mH.size) = 0 := by simpa using hhit
    have h0B := (hr.memoFind hE hle).trans h0
    rw [hash_congr _ _ 0 _ (htop.mono hle).at, hr.argA, copyArgs_congr _ 0 _ (htop.mono hle).at,
      hr.cel.1, hr.mem.1]
    have hc0 : sA.cel.size >>> 2 ≠ 0 := by rw [shr2_eq]; exact Nat.pos_iff_ne_zero.mp h.store.cell0
    have mA := memoTab_miss hr.memoA h0 hc0
    have mB := memoTab_miss (hr.argA ▸ hr.memoB : MemoTab sB.mem sA.argA sB.mH) (fs := sA.fs) (k := sB.x)
      (n := mI + 1) (by
        have e := h0B
        rw [hash_congr _ _ 0 _ (htop.mono hle).at, memoFind_congr _ _ _ _ _ (htop.mono hle), hr.argA] at e
        exact e) hc0
    rw [hr.mem.1] at mB
    have hfs := ((hpop _ hle).pushOne (g4Tag (sA.cel.size >>> 2) 2) (.inr (.inl (tag_and _ 2 (by omega))))).pushIota
      hE sA.argA.size (mI + 1)
    have hmem := hr.mem.push h.store.memSz hE sA.argA.size (mI + 1) (sA.cel.size >>> 2)
    have hcel := hr.cel.push h.store.celSz 1 0 0 0 0 (fun h => absurd h (by decide))
    rcases hfab with ⟨rfl, rfl⟩ | ⟨cA, cB, rfl, rfl, hcR, har⟩
    · simp only [show ¬b + 4 * 0 ≥ 4 by omega, ↓reduceIte]
      obtain ⟨oc', fl', h'⟩ := step_rec_miss h hm ht2 hmIA hle (g4MemoIns
        ((((sA.mem.push sA.x).push sA.argA.size).push (mI + 1)).push (sA.cel.size >>> 2))
        (g4CopyArgs sA.fs sA.argA (mI + 1) 0) sA.mH (sA.mem.size >>> 2)
        (g4Hash sA.fs sA.x (mI + 1) 0 (UInt64.ofNat sA.x)))
      refine ih.app (sB := { sB with
          cel := (((sB.cel.push 1).push 0).push 0).push 0
          fs := (((((g4PopN sB.fs (mI + 1)).push (g4Tag (sA.cel.size >>> 2) 2)).push sB.x).push
            sA.argA.size).push (mI + 1)).push 3
          argA := g4CopyArgs sA.fs sA.argA (mI + 1) 0
          mem := (((sB.mem.push sB.x).push sA.argA.size).push (mI + 1)).push (sA.cel.size >>> 2)
          mH := g4MemoIns ((((sB.mem.push sB.x).push sA.argA.size).push (mI + 1)).push (sA.cel.size >>> 2))
            (g4CopyArgs sA.fs sA.argA (mI + 1) 0) sB.mH (sA.mem.size >>> 2)
            (g4Hash sA.fs sB.x (mI + 1) 0 (UInt64.ofNat sB.x))
          mode := 2
          pc := 0
          env := 0
          x := (g4CopyArgs sA.fs sA.argA (mI + 1) 0)[sA.argA.size + mI]! })
        h' hR ?_ (by omega)
      exact { hr with
        cel := hcel
        argA := rfl
        fs := hfs
        mem := hmem
        memoA := mA
        memoB := mB
        mode := rfl
        regs := ⟨rfl, rfl, rfl⟩ }
    · simp only [show b + 4 * (cA + 1) ≥ 4 by omega, show b + 4 * (cB + 1) ≥ 4 by omega, ↓reduceIte]
      have eA4 : sA.P.kE[sA.x]! = b + 4 * (cA + 1) := get!_of_some eA
      obtain ⟨oc', fl', h'⟩ := step_rec_K h hm ht2 hmIA hle (by rw [eA4]; omega) (g4MemoIns
        ((((sA.mem.push sA.x).push sA.argA.size).push (mI + 1)).push (sA.cel.size >>> 2))
        (g4CopyArgs sA.fs sA.argA (mI + 1) 0) sA.mH (sA.mem.size >>> 2)
        (g4Hash sA.fs sA.x (mI + 1) 0 (UInt64.ofNat sA.x)))
      rw [eA4, show (b + 4 * (cA + 1)) / 4 - 1 = cA by omega] at h'
      rw [show (b + 4 * (cA + 1)) / 4 - 1 = cA by omega, show (b + 4 * (cB + 1)) / 4 - 1 = cB by omega,
        get!_congr2 har.symm, hr.val.1]
      refine ih.app (sB := { sB with
          cel := (((sB.cel.push 1).push 0).push 0).push 0
          val := (((sB.val.push 1).push cB).push sA.argA.size).push sA.P.kArity[cA]!
          fs := (((((g4PopN sB.fs (mI + 1)).push (g4Tag (sA.cel.size >>> 2) 2)).push sB.x).push
            sA.argA.size).push (mI + 1)).push 3
          argA := g4CopyArgs sA.fs sA.argA (mI + 1) 0
          mem := (((sB.mem.push sB.x).push sA.argA.size).push (mI + 1)).push (sA.cel.size >>> 2)
          mH := g4MemoIns ((((sB.mem.push sB.x).push sA.argA.size).push (mI + 1)).push (sA.cel.size >>> 2))
            (g4CopyArgs sA.fs sA.argA (mI + 1) 0) sB.mH (sA.mem.size >>> 2)
            (g4Hash sA.fs sB.x (mI + 1) 0 (UInt64.ofNat sB.x))
          mode := 1
          pc := 0
          env := 0
          x := sA.val.size >>> 2 })
        h' hR ?_ (by omega)
      exact { hr with
        cel := hcel
        val := hr.val.push h.store.valSz 1 _ _ _ _ hcR
        argA := rfl
        fs := hfs
        mem := hmem
        memoA := mA
        memoB := mB
        mode := rfl
        regs := ⟨rfl, rfl, rfl⟩ }
  next =>
    obtain ⟨fl', h'⟩ := step_neutral_entry h hm
    dsimp only
    rw [hcnt]
    refine ih.app (sB := { sB with
        fs := g4PopN sB.fs (g4CountArgs sA.fs sA.fs.size 0)
        mode := 1
        pc := 0
        env := 0
        x := 0 }) h' hR ?_ (by omega)
    exact { hr with
      fs := hpop _ (Nat.le_refl _)
      mode := rfl
      regs := ⟨rfl, rfl, rfl⟩ }
  next h1 h2 h5 =>
    dsimp only
    rw [hcnt]
    split
    next hc =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      have h3 : sA.P.kTag[sA.x]! = 3 := by
        split at hd
        · omega
        · omega
      obtain ⟨fl', h'⟩ := step_natop_push h hm h3 hc.2
      rw [htop 0 (by omega), htop 1 (by omega)]
      refine ih.app (sB := { sB with
          fs := ((((g4PopN sB.fs 2).push sB.x).push (g4ArgAt sA.fs 0)).push (g4ArgAt sA.fs 1)).push 5
          mode := 2
          pc := 0
          env := 0
          x := g4ArgAt sA.fs 0 }) h' hR ?_ (by omega)
      exact { hr with
        fs := (hpop 2 (by omega)).pushNatA hE _ _
        mode := rfl
        regs := ⟨rfl, rfl, rfl⟩ }
    next hc =>
      split
      next =>
        exact sim_collect ih h hR hr hm hE (.inr rfl) (by omega)
      next hc' =>
        refine absurd ⟨?_, ?_, ?_, ?_, ?_⟩ hD <;> simp only [hd] <;> simp_all


/-- The δ compile's program: the body compiled, its node stored on the entry. -/
@[expose] def compDef (f : Name → Option ConstantInfo) (p : Name → Nat → Option ProjEntry) (P : G4Prog)
    (k : Nat) (t : Expr) : G4Prog :=
  { (g4Comp f p P t).2 with kCode := (g4Comp f p P t).2.kCode.set! k ((g4Comp f p P t).1 + 1) }

/-- **The δ compile's program** keeps the invariant, grows the program, keeps
the site, and stores a body. -/
theorem compDef_spec {f : Name → Option ConstantInfo} {p : Name → Nat → Option ProjEntry} {P : G4Prog}
    {k : Nat} {c : Name} {lps : List Name} {us : List Level} {v : Expr} (hI : Inv f p P)
    (hi : P.kInfo[k]? = some (.defn c lps us v)) :
    Inv f p (compDef f p P k (v.instantiateLevelParams lps us)) ∧
      ExtR P (compDef f p P k (v.instantiateLevelParams lps us)) ∧
      (compDef f p P k (v.instantiateLevelParams lps us)).site = P.site ∧
      (compDef f p P k (v.instantiateLevelParams lps us)).kCode[k]! ≠ 0 := by
  have hcomp := g4Comp_spec f p P (v.instantiateLevelParams lps us) hI
  unfold compDef
  generalize g4Comp f p P (v.instantiateLevelParams lps us) = r at hcomp ⊢
  obtain ⟨o, P1⟩ := r
  obtain ⟨hI1, hx1, hc⟩ := hcomp
  have hk1 : k < P1.kCode.size := by
    rw [hI1.szs.1.1]; exact Nat.lt_of_lt_of_le (lt_of_some hi) hx1.kInfoSize
  refine ⟨hI1.setKCode (hx1.kInfo_some hi) hc, hx1.toExtR.trans (ExtR.codes P1 _ P1.ruleCode),
    hx1.site, ?_⟩
  dsimp only
  rw [get!_of_some (set!_get?_self hk1)]; omega

/-- **The δ compile on both sides keeps lock-step**: both store the body of
one key. -/
theorem CodeSame.delta {fA fB : Name → Option ConstantInfo} {pA pB : Name → Nat → Option ProjEntry}
    {PA PB : G4Prog} (hcs : CodeSame PA PB) (hIA : Inv fA pA PA) (hIB : Inv fB pB PB) {kA kB : Nat}
    {iA iB : G4Info} (hiA : PA.kInfo[kA]? = some iA) (hiB : PB.kInfo[kB]? = some iB)
    (hk : infoKey iA = infoKey iB) (tA tB : Expr) :
    CodeSame (compDef fA pA PA kA tA) (compDef fB pB PB kB tB) := by
  have cA := g4Comp_spec fA pA PA tA hIA
  have cB := g4Comp_spec fB pB PB tB hIB
  unfold compDef
  generalize g4Comp fA pA PA tA = rA at cA ⊢
  generalize g4Comp fB pB PB tB = rB at cB ⊢
  obtain ⟨oA, QA⟩ := rA
  obtain ⟨oB, QB⟩ := rB
  obtain ⟨hIA1, hxA, -⟩ := cA
  obtain ⟨hIB1, hxB, -⟩ := cB
  have hq := hcs.ext hIA.toTabInv hIB.toTabInv hxA hxB
  have hkA : kA < QA.kCode.size := by
    rw [hIA1.szs.1.1]; exact Nat.lt_of_lt_of_le (lt_of_some hiA) hxA.kInfoSize
  have hkB : kB < QB.kCode.size := by
    rw [hIB1.szs.1.1]; exact Nat.lt_of_lt_of_le (lt_of_some hiB) hxB.kInfoSize
  refine ⟨fun κ => ?_, fun κ d => hq.2 κ d⟩
  dsimp only
  rw [codeK_set hkB (Nat.succ_ne_zero _) (hxB.kInfo_some hiB),
    codeK_set hkA (Nat.succ_ne_zero _) (hxA.kInfo_some hiA), hq.1 κ, hk]

/-- **The δ compile**, one step on either side. -/
theorem run_D3_comp {f : Name → Option ConstantInfo} {p : Name → Nat → Option ProjEntry} {s : MS}
    (hm : s.mode = 3) (hD : D3 s) (hc : s.P.kCode[s.x]! = 0) {c : Name} {lps : List Name}
    {us : List Level} {v : Expr} (hi : s.P.kInfo[s.x]? = some (.defn c lps us v)) (n : Nat) :
    s.run f p (n + 1) =
      ({ s with P := compDef f p s.P s.x (v.instantiateLevelParams lps us) } : MS).run f p n := by
  obtain ⟨h1, h2, h5, hn2, hl2⟩ := hD
  have hi' : s.P.kInfo[s.x]! = .defn c lps us v := by simp [getElem!_def, hi]
  unfold MS.run
  rw [hm, g4Run.eq_6]
  generalize (if (s.pc == 1) = true then 0 else s.P.kTag[s.x]!) = d at h1 h2 h5 hn2 hl2 ⊢
  split
  · exact absurd rfl h1
  · exact absurd rfl h2
  · exact absurd rfl h5
  dsimp only
  simp only [hn2, hl2, Bool.false_eq_true, ↓reduceIte, hc, beq_self_eq_true, hi']
  rfl

/-- A definition entry of `keyInfo` reads a definition. -/
theorem keyInfo_defn {f : Name → Option ConstantInfo} {c c' : Name} {us us' : List Level} {lps : List Name}
    {v : Expr} (h : keyInfo f c us = .defn c' lps us' v) :
    ∃ cv hs, f c = some (.defnInfo cv v hs) := by
  unfold keyInfo at h
  split at h
  · split at h
    · cases h
    · cases h; exact ⟨_, _, ‹_›⟩
  all_goals (try split at h) <;> cases h

/-- A dispatch at tag 0 or 3 is at a definition entry. -/
theorem defn_of_tag03 {f : Name → Option ConstantInfo} {p : Name → Nat → Option ProjEntry} {P : G4Prog}
    (hI : Inv f p P) {k : Nat} (hk : k < P.kInfo.size) (ht : P.kTag[k]? = some 0 ∨ P.kTag[k]? = some 3) :
    ∃ c lps us v, P.kInfo[k]? = some (.defn c lps us v) := by
  have he := hI.ents k hk
  unfold EntOK at he
  split at he
  · rcases ht with ht | ht <;> rw [ht] at he <;> cases he
  · exact ⟨_, _, _, _, ‹_›⟩
  · have h1 := he.2.1
    rcases ht with ht | ht <;> rw [ht] at h1 <;> cases h1
  · obtain ⟨-, -, -, -, -, -, ht', -⟩ := he
    rcases ht with ht | ht <;> rw [ht] at ht' <;> cases ht'
  · rename_i hn; rw [Array.getElem?_eq_getElem hk] at hn; cases hn


/-- **Mode 3 at a body both sides have**: one step each. -/
theorem sim_mode3b (hwf : EnvWF env) (hag : LookAgree N env.find? env.findProj? f₂ p₂)
    (ih : SimAt j N env f₂ p₂ t₀ n) {sA sB : MS} {oc : Nat → Expr} {fl : List Fr}
    (h : MInv env t₀ oc sA fl) (hR : RunOK env sA.P) (hr : MRel j N env.find? env.findProj? f₂ p₂ sA sB)
    (hm : sA.mode = 3) (hD : D3 sA) (hcA : sA.P.kCode[sA.x]! ≠ 0) (hcB : sB.P.kCode[sB.x]! ≠ 0) {m : Nat}
    (hmn : (j = 0 ∧ m = n + 1) ∨ (j = 1 ∧ 2 * n + 1 ≤ m)) :
    OutRel j N env f₂ p₂ (sA.run env.find? env.findProj? (n + 1)) (sB.run f₂ p₂ m) := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hmB : sB.mode = 3 := by rw [hr.mode, hm]
  obtain ⟨hpc, hE, htg⟩ := hr.dispatch hag hm
  obtain ⟨hcnt, htop, hpop⟩ := hr.fs.args
  have hk : sA.x < sA.P.kInfo.size := by
    have hf := h.focus; simp only [Focus, hm] at hf; exact hf.1
  have h03 := h.tag03 hm rfl ⟨hD.1, hD.2.1, hD.2.2.1⟩
  obtain ⟨c, lps, us, v, hi⟩ := defn_of_tag03 h.store.prog hk h03
  have hNc : N c := hE.2 _ hi
  obtain ⟨-, -, -, wA, wB, ewA, ewB, cA, cB⟩ :=
    hE.1.defnW hr.invA hr.invB hi (hag.find c hNc).symm (hr.natOkAt hag hE c _ _ _ hi)
  have hki := hr.invA.kind _ _ hi
  simp only [G4Info.unbased, infoKey] at hki
  obtain ⟨cv, hs, hfc⟩ := keyInfo_defn hki.symm
  have hN := (hag.defVal c cv v hs hNc hfc).instLP lps us
  have hcA0 := hcA
  rw [get!_of_some ewA] at hcA0
  have hcB0 := hcB
  rw [get!_of_some ewB] at hcB0
  rcases cA with h0 | ⟨oA, rfl, cA⟩
  · exact absurd h0 hcA0
  rcases cB with h0 | ⟨oB, rfl, cB⟩
  · exact absurd h0 hcB0
  have hT : TRel N env.find? env.findProj? f₂ p₂ sA.P sB.P oA oB := TRel.ofComp hN cA cB
  unfold MS.run
  rw [hm, hmB, g4Run.eq_6, g4Run.eq_6, hpc, htg]
  obtain ⟨h1, h2, h5, hn2, hl2⟩ := hD
  generalize (if (sA.pc == 1) = true then 0 else sA.P.kTag[sA.x]!) = d at h1 h2 h5 hn2 hl2 ⊢
  split
  · exact absurd rfl h1
  · exact absurd rfl h2
  · exact absurd rfl h5
  dsimp only
  rw [hcnt]
  simp only [hn2, hl2, Bool.false_eq_true, ↓reduceIte, beq_iff_eq, hcA, hcB]
  rw [get!_of_some ewA, get!_of_some ewB, Nat.add_sub_cancel, Nat.add_sub_cancel]
  by_cases hna : g4CountArgs sA.fs sA.fs.size 0 > 0
  · simp only [hna, ↓reduceIte]
    rw [hr.memoFind hE (Nat.le_refl _)]
    split
    next hhitA =>
      have hhit : (g4MemoFind sA.mem sA.mH sA.fs sA.argA sA.x (g4CountArgs sA.fs sA.fs.size 0) sA.mH.size
          (g4Slot (g4Hash sA.fs sA.x (g4CountArgs sA.fs sA.fs.size 0) 0 (UInt64.ofNat sA.x)) sA.mH.size)
          != 0) = true := by
        simpa using hhitA
      obtain ⟨fl', h'⟩ := step_memo_hit h hm (n := g4CountArgs sA.fs sA.fs.size 0) hna (Nat.le_refl _)
        (by simpa using hhit)
      refine ih.app (sB := { sB with
          fs := g4PopN sB.fs (g4CountArgs sA.fs sA.fs.size 0)
          mode := 2
          pc := 0
          env := 0
          x := g4MemoFind sA.mem sA.mH sA.fs sA.argA sA.x (g4CountArgs sA.fs sA.fs.size 0) sA.mH.size
            (g4Slot (g4Hash sA.fs sA.x (g4CountArgs sA.fs sA.fs.size 0) 0 (UInt64.ofNat sA.x)) sA.mH.size) })
        h' hR ?_ (by omega)
      exact { hr with
        fs := hpop _ (Nat.le_refl _)
        mode := rfl
        regs := ⟨rfl, rfl, rfl⟩ }
    next hhitA =>
    have h0 : g4MemoFind sA.mem sA.mH sA.fs sA.argA sA.x (g4CountArgs sA.fs sA.fs.size 0) sA.mH.size
        (g4Slot (g4Hash sA.fs sA.x (g4CountArgs sA.fs sA.fs.size 0) 0 (UInt64.ofNat sA.x)) sA.mH.size)
        = 0 := by simpa using hhitA
    have h0B := (hr.memoFind hE (Nat.le_refl _)).trans h0
    rw [hash_congr _ _ 0 _ htop.at, hr.argA, copyArgs_congr _ 0 _ htop.at, hr.cel.1, hr.mem.1]
    have hc0 : sA.cel.size >>> 2 ≠ 0 := by rw [shr2_eq]; exact Nat.pos_iff_ne_zero.mp h.store.cell0
    have mA := memoTab_miss hr.memoA h0 hc0
    have mB := memoTab_miss (hr.argA ▸ hr.memoB : MemoTab sB.mem sA.argA sB.mH) (fs := sA.fs) (k := sB.x)
      (n := g4CountArgs sA.fs sA.fs.size 0) (by
        have e := h0B
        rw [hash_congr _ _ 0 _ htop.at, memoFind_congr _ _ _ _ _ htop, hr.argA] at e
        exact e) hc0
    rw [hr.mem.1] at mB
    obtain ⟨oc', fl', h'⟩ := step_delta_miss hwf h hm h03 hcA (g4MemoIns
      ((((sA.mem.push sA.x).push sA.argA.size).push (g4CountArgs sA.fs sA.fs.size 0)).push (sA.cel.size >>> 2))
      (g4CopyArgs sA.fs sA.argA (g4CountArgs sA.fs sA.fs.size 0) 0) sA.mH (sA.mem.size >>> 2)
      (g4Hash sA.fs sA.x (g4CountArgs sA.fs sA.fs.size 0) 0 (UInt64.ofNat sA.x)))
    rw [get!_of_some ewA, Nat.add_sub_cancel] at h'
    refine ih.app (sB := { sB with
        cel := (((sB.cel.push 1).push 0).push 0).push 0
        fs := g4PushArgs (g4CopyArgs sA.fs sA.argA (g4CountArgs sA.fs sA.fs.size 0) 0) sA.argA.size
          ((g4PopN sB.fs (g4CountArgs sA.fs sA.fs.size 0)).push (g4Tag (sA.cel.size >>> 2) 2))
          (g4CountArgs sA.fs sA.fs.size 0)
        argA := g4CopyArgs sA.fs sA.argA (g4CountArgs sA.fs sA.fs.size 0) 0
        mem := (((sB.mem.push sB.x).push sA.argA.size).push (g4CountArgs sA.fs sA.fs.size 0)).push
          (sA.cel.size >>> 2)
        mH := g4MemoIns ((((sB.mem.push sB.x).push sA.argA.size).push (g4CountArgs sA.fs sA.fs.size 0)).push
            (sA.cel.size >>> 2))
          (g4CopyArgs sA.fs sA.argA (g4CountArgs sA.fs sA.fs.size 0) 0) sB.mH (sA.mem.size >>> 2)
          (g4Hash sA.fs sB.x (g4CountArgs sA.fs sA.fs.size 0) 0 (UInt64.ofNat sB.x))
        mode := 0
        pc := oB
        env := 0
        x := 0 })
      h' hR ?_ (by omega)
    exact { hr with
      cel := hr.cel.push h.store.celSz 1 0 0 0 0 (fun h => absurd h (by decide))
      argA := rfl
      fs := FsRel.pushArgs _ _ _ ((hpop _ (Nat.le_refl _)).pushOne _ (.inr (.inl (tag_and _ 2 (by omega)))))
      mem := hr.mem.push h.store.memSz hE sA.argA.size _ (sA.cel.size >>> 2)
      memoA := mA
      memoB := mB
      mode := rfl
      regs := ⟨rfl, rfl, hT⟩ }
  · simp only [hna, ↓reduceIte]
    have h' := step_delta_body hwf h hm h03 hcA
    rw [get!_of_some ewA, Nat.add_sub_cancel] at h'
    refine ih.app (sB := { sB with mode := 0, pc := oB, env := 0, x := 0 }) h' hR ?_ (by omega)
    exact { hr with
      mode := rfl
      regs := ⟨rfl, rfl, hT⟩ }

/-- **Mode 3**, dispatching a constant entry. -/
theorem sim_mode3 (hwf : EnvWF env) (hag : LookAgree N env.find? env.findProj? f₂ p₂)
    (ih : SimAt j N env f₂ p₂ t₀ n) {sA sB : MS} {oc : Nat → Expr} {fl : List Fr}
    (h : MInv env t₀ oc sA fl) (hR : RunOK env sA.P) (hr : MRel j N env.find? env.findProj? f₂ p₂ sA sB)
    (hm : sA.mode = 3) {m : Nat} (hmn : (j = 0 ∧ m = n + 1) ∨ (j = 1 ∧ 2 * (n + 1) ≤ m)) :
    OutRel j N env f₂ p₂ (sA.run env.find? env.findProj? (n + 1)) (sB.run f₂ p₂ m) := by
  rcases Classical.em (D3 sA) with hD | hD
  rotate_left
  · exact sim_mode3n hag ih h hR hr hm hD (by omega)
  have hmB : sB.mode = 3 := by rw [hr.mode, hm]
  obtain ⟨hpc, hE, htg⟩ := hr.dispatch hag hm
  obtain ⟨hcnt, -, -⟩ := hr.fs.args
  have hDB : D3 sB := by unfold D3 at hD ⊢; rw [hpc, htg, hcnt]; exact hD
  have hk : sA.x < sA.P.kInfo.size := by
    have hf := h.focus; simp only [Focus, hm] at hf; exact hf.1
  obtain ⟨c, lps, us, v, hi⟩ := defn_of_tag03 h.store.prog hk (h.tag03 hm rfl ⟨hD.1, hD.2.1, hD.2.2.1⟩)
  have hNc : N c := hE.2 _ hi
  obtain ⟨hiB, -⟩ := hE.1.defn hr.invA hr.invB hi (hag.find c hNc).symm
  have hi' : sA.P.kInfo[sA.x]! = .defn c lps us v := by simp [getElem!_def, hi]
  by_cases hcA : sA.P.kCode[sA.x]! = 0 <;> by_cases hcB : sB.P.kCode[sB.x]! = 0
  · -- both compile
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [run_D3_comp hm hD hcA hi, run_D3_comp hmB hDB hcB hiB]
    obtain ⟨hIA', hxA, hsA, -⟩ := compDef_spec h.store.prog hi
    obtain ⟨hIB', hxB, hsB, -⟩ := compDef_spec hr.invB hiB
    exact ih _ _ _ _ (step_delta_compile h hm hi') (hR.ext hxA hsA)
      (hr.ext hxA hxB hIA' hIB' hsA hsB fun h0 =>
        (hr.code h0).delta h.store.prog hr.invB hi hiB rfl _ _) m (fuel_t hmn)
  · -- A compiles a body B has: B takes no step (not in lock-step)
    rcases hmn with ⟨rfl, -⟩ | ⟨rfl, hmn⟩
    · exact absurd ((CodeSame.code_iff (hr.code rfl) hr.invA.toCompInv hr.invB.toCompInv hi hiB rfl).1 hcA) hcB
    rw [run_D3_comp hm hD hcA hi]
    obtain ⟨hIA', hxA, hsA, -⟩ := compDef_spec h.store.prog hi
    exact ih _ sB _ _ (step_delta_compile h hm hi') (hR.ext hxA hsA)
      (hr.ext hxA (ExtR.refl _) hIA' hr.invB hsA rfl fun h0 => absurd h0 (by decide)) m (.inr ⟨rfl, by omega⟩)
  · -- B compiles a body A has, then takes A's step (not in lock-step)
    rcases hmn with ⟨rfl, -⟩ | ⟨rfl, hmn⟩
    · exact absurd ((CodeSame.code_iff (hr.code rfl) hr.invA.toCompInv hr.invB.toCompInv hi hiB rfl).2 hcB) hcA
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [run_D3_comp hmB hDB hcB hiB]
    obtain ⟨hIB', hxB, hsB, hcB'⟩ := compDef_spec hr.invB hiB
    exact sim_mode3b hwf hag ih h hR
      (hr.ext (ExtR.refl _) hxB hr.invA hIB' rfl hsB fun h0 => absurd h0 (by decide)) hm hD hcA hcB'
      (.inr ⟨rfl, by omega⟩)
  · exact sim_mode3b hwf hag ih h hR hr hm hD hcA hcB (by omega)

end

end ConLeche.Verify.Ground
