module

public import ConLeche.Driver.CheckPool
public import ConLeche.Verify.Cached.LazyInstall

/-!
# Phase B of the lazy parse: each theorem's value, built in its check (task #329)

The lazy parse (`ConLeche/Driver/LazyParse.lean`) hands the install
records whose theorem values are placeholders (`ph vid hint`) and a
store their values are built from.  The install never reads a theorem's
value (`ConLeche/Verify/Cached/LazyInstall.lean`), so the installed
index is the serial records' index; each theorem's pending check is
run here on its value, built from the store by the check task itself
(`buildVal`, with a memo of its own) and dropped after the check.  The
built value is the serial parse's (`buildVal_sound`), so the check is
the serial record's check: `lazy_checkDecls` turns every record's check
into an accept of the fold on the serial records.
-/

@[expose] public section

namespace ConLeche.Driver

open ConLeche ConLeche.Frontend ConLeche.Cached

/-- A placeholder value and a serial value: the placeholder's index is
bound to it in the serial state `G`. -/
def PhRel (G : StateD) (w' w : Expr) : Prop :=
  ∃ vid hint, w' = ph vid hint ∧ G.exprs.get? vid = some w

theorem DRel.dr {G : StateD} {d' d : Declaration} (h : DRel G d' d) : DR (PhRel G) d' d := by
  cases d with
  | thmDecl cv w =>
    obtain ⟨vid, hint, rfl, hw⟩ := h
    exact ⟨_, rfl, vid, hint, rfl, hw⟩
  | _ => exact h

theorem Pw.dr {G : StateD} :
    ∀ {a b : List Declaration}, Pw (DRel G) a b → Pw (DR (PhRel G)) a b
  | [], [], _ => trivial
  | _ :: _, _ :: _, h => ⟨DRel.dr h.1, Pw.dr h.2⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- What a lazy record's check establishes: for every serial state the
store is the parse of, the record is checked at every serial check
related to it. -/
def LazyChecked {mode : CheckMode} {ds : List Declaration} (S : LStore)
    (e : InstalledEnv mode natOpPinSets ds) (k : Nat) : Prop :=
  ∀ G, SHolds G S → StoreOK G S.chunks → LChecked mode (PhRel G) e k

/-- A pending check with another value. -/
@[inline] def _root_.ConLeche.Cached.PendingCheck.withJv (pc : PendingCheck) (v : Expr) :
    PendingCheck :=
  { pc with vg := { pc.vg with jv := v } }

/-- **Record `k`'s lazy check**: a theorem's value built from the store,
then the record's check on it; another record's check as it is. -/
def lazyCheckRecord {mode : CheckMode} {ds : List Declaration} (S : LStore)
    (e : InstalledEnv mode natOpPinSets ds) (k : Nat) (hk : k < e.pend.size) :
    RecResultQ (LazyChecked S e) :=
  let pc := e.pend[k]
  if hkind : pc.vg.kind = .thm then
    match hid : phId? pc.vg.jv with
    | none => .error (.internal s!"theorem {pc.vg.cvA.name}: its value is not a placeholder", pc.pos)
    | some vid =>
      match hb : buildVal S vid (phHint pc.vg.jv) with
      | none => .error (.internal s!"theorem {pc.vg.cvA.name}: its value did not build", pc.pos)
      | some v =>
        match hc : checkPending mode e.fe (pc.withJv v) {} with
        | .ok ((), s') => .ok ⟨k, fun G hh hs _ pc₂ hrel => by
            obtain ⟨⟨k₂, cv₂, jv₂⟩, pos₂, vis₂⟩ := pc₂
            obtain ⟨hpos, hvis, hkd, hcv, hthm, -⟩ := hrel
            simp only at hpos hvis hkd hcv hthm
            obtain ⟨vid', hint', hph, hw⟩ := hthm (hkd ▸ hkind)
            have hvid : vid' = vid := by
              rw [hph] at hid; simp [phId?, ph] at hid; exact hid
            subst hvid
            have hv := buildVal_sound hh hs hb
            rw [hv] at hw; cases hw
            have : (⟨⟨k₂, cv₂, v⟩, pos₂, vis₂⟩ : PendingCheck) = pc.withJv v := by
              simp only [PendingCheck.withJv, pc, hpos, hvis, hkd, hcv]
            exact ⟨s', this ▸ hc⟩⟩
        | .error err => .error (err, pc.pos)
  else
    match hc : checkPending mode e.fe pc {} with
    | .ok ((), s') => .ok ⟨k, fun G _ _ _ pc₂ hrel => by
        obtain ⟨⟨k₂, cv₂, jv₂⟩, pos₂, vis₂⟩ := pc₂
        obtain ⟨hpos, hvis, hkd, hcv, -, hval⟩ := hrel
        simp only at hpos hvis hkd hcv hval
        have hjv := hval (hkd ▸ hkind)
        have : (⟨⟨k₂, cv₂, jv₂⟩, pos₂, vis₂⟩ : PendingCheck) = pc := by
          simp only [pc, ← hpos, ← hvis, ← hkd, ← hcv, ← hjv]
        exact ⟨s', this ▸ hc⟩⟩
    | .error err => .error (err, pc.pos)

end ConLeche.Driver
