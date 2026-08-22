import Setlec.Verify.IExprOps
import Setlec.Verify.Level

/-!
# Faithfulness of the interned level operations (task #62)

Pure commutation lemmas for the arena-level level operations of
`Setlec/Kernel/IExpr.lean` and `Setlec/Kernel/CoreI.lean`: `combiningLI`,
`simplifyLIGo`, `isNonZeroLIGo`, `internLevelSubst(s)`, and the fueled
comparison twins (`leqCoreLI` … `isEquivListLI`).  Each mirrors its
`Setlec.Level` counterpart under the level denotation `denoteL`; the
monadic wrappers' effect lemmas (`Setlec/Verify/SimI.lean`) consume
these.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

open EStore

/-! ## Node-shape inversions under `denoteL` -/

/-- The stored node determines the denotation's head. -/
theorem denoteL_head {st : EStore} {u : LIdx} {n : LNode} {l : Level}
    (hl : st.denoteL u = some l) (hn : st.lnodes[u]? = some n) :
    denoteLNode st.denoteL n = some l := by
  obtain ⟨n', hn', -, hd⟩ := denoteL_some_inv hl
  rw [hn] at hn'
  cases hn'
  exact hd

/-- A `zero` denotation exposes a `zero` node. -/
theorem denoteL_zero_node {st : EStore} {u : LIdx}
    (hl : st.denoteL u = some .zero) : st.lnodes[u]? = some .zero := by
  obtain ⟨n, hn, -, hd⟩ := denoteL_some_inv hl
  rw [denoteLNode_zero_inv hd] at hn
  exact hn

/-- A `param` denotation exposes a `param` node. -/
theorem denoteL_param_node {st : EStore} {u : LIdx} {p : Name}
    (hl : st.denoteL u = some (.param p)) :
    st.lnodes[u]? = some (.param p) := by
  obtain ⟨n, hn, -, hd⟩ := denoteL_some_inv hl
  rw [denoteLNode_param_inv hd] at hn
  exact hn

/-- A `succ` denotation exposes a `succ` node. -/
theorem denoteL_succ_node {st : EStore} {u : LIdx} {x : Level}
    (hl : st.denoteL u = some (.succ x)) :
    ∃ l, st.lnodes[u]? = some (.succ l) ∧ st.denoteL l = some x := by
  obtain ⟨n, hn, -, hd⟩ := denoteL_some_inv hl
  obtain ⟨l, rfl, hx⟩ := denoteLNode_succ_inv hd
  exact ⟨l, hn, hx⟩

/-- A `max` denotation exposes a `max` node. -/
theorem denoteL_max_node {st : EStore} {u : LIdx} {x y : Level}
    (hl : st.denoteL u = some (.max x y)) :
    ∃ a b, st.lnodes[u]? = some (.max a b) ∧
      st.denoteL a = some x ∧ st.denoteL b = some y := by
  obtain ⟨n, hn, -, hd⟩ := denoteL_some_inv hl
  obtain ⟨a, b, rfl, hx, hy⟩ := denoteLNode_max_inv hd
  exact ⟨a, b, hn, hx, hy⟩

/-- An `imax` denotation exposes an `imax` node. -/
theorem denoteL_imax_node {st : EStore} {u : LIdx} {x y : Level}
    (hl : st.denoteL u = some (.imax x y)) :
    ∃ a b, st.lnodes[u]? = some (.imax a b) ∧
      st.denoteL a = some x ∧ st.denoteL b = some y := by
  obtain ⟨n, hn, -, hd⟩ := denoteL_some_inv hl
  obtain ⟨a, b, rfl, hx, hy⟩ := denoteLNode_imax_inv hd
  exact ⟨a, b, hn, hx, hy⟩

/-! ## `combiningLI` -/

theorem combiningLI_spec {st : EStore} (hwf : st.WF) :
    ∀ {a : LIdx} {b : LIdx} {la lb : Level} {r : LIdx} {st' : EStore},
      st.denoteL a = some la → st.denoteL b = some lb →
      st.combiningLI a b = (r, st') →
      st'.WF ∧ Ext st st' ∧ st'.denoteL r = some (Level.combining la lb) := by
  intro a
  induction a using Nat.strongRecOn with
  | _ a ih =>
    intro b la lb r st' ha hb hgo
    obtain ⟨na, hna, hca, hda⟩ := denoteL_some_inv ha
    obtain ⟨nb, hnb, hcb, hdb⟩ := denoteL_some_inv hb
    unfold combiningLI at hgo
    rw [hna, hnb] at hgo
    have hmax : ∀ {r₀ : LIdx} {st₀ : EStore},
        st.internL (.max a b) = (r₀, st₀) →
        st₀.WF ∧ Ext st st₀ ∧ st₀.denoteL r₀ = some (.max la lb) := by
      intro r₀ st₀ hI
      obtain ⟨hwf₁, hext₁, hden₁⟩ := internL_step (n := .max a b) hwf
        (by
          simp only [LNode.children, List.mem_cons, List.not_mem_nil, or_false]
          rintro c (rfl | rfl)
          · exact denoteL_lt_size ha
          · exact denoteL_lt_size hb)
        (a := .max la lb) (by rw [denoteLNode, ha, hb]; rfl)
      rw [hI] at hwf₁ hext₁ hden₁
      exact ⟨hwf₁, hext₁, hden₁⟩
    cases na with
    | zero =>
      rw [denoteLNode] at hda
      cases hda
      cases nb <;>
        · dsimp only at hgo
          cases hgo
          exact ⟨hwf, Ext.refl st, by simpa [Level.combining] using hb⟩
    | param ap =>
      rw [denoteLNode] at hda
      cases hda
      cases nb with
      | zero =>
        rw [denoteLNode] at hdb
        cases hdb
        dsimp only at hgo
        cases hgo
        exact ⟨hwf, Ext.refl st, by simpa [Level.combining] using ha⟩
      | param bp =>
        rw [denoteLNode] at hdb
        cases hdb
        dsimp only at hgo
        obtain ⟨hwf₁, hext₁, hden₁⟩ := hmax hgo
        exact ⟨hwf₁, hext₁, by simpa [Level.combining] using hden₁⟩
      | succ bl =>
        rw [denoteLNode, Option.map_eq_some_iff] at hdb
        obtain ⟨bx, hbx, rfl⟩ := hdb
        dsimp only at hgo
        obtain ⟨hwf₁, hext₁, hden₁⟩ := hmax hgo
        exact ⟨hwf₁, hext₁, by simpa [Level.combining] using hden₁⟩
      | max bx' by' =>
        rw [denoteLNode, Option.bind_eq_some_iff] at hdb
        obtain ⟨bx, hbx, hdb⟩ := hdb
        rw [Option.map_eq_some_iff] at hdb
        obtain ⟨by2, hby2, rfl⟩ := hdb
        dsimp only at hgo
        obtain ⟨hwf₁, hext₁, hden₁⟩ := hmax hgo
        exact ⟨hwf₁, hext₁, by simpa [Level.combining] using hden₁⟩
      | imax bx' by' =>
        rw [denoteLNode, Option.bind_eq_some_iff] at hdb
        obtain ⟨bx, hbx, hdb⟩ := hdb
        rw [Option.map_eq_some_iff] at hdb
        obtain ⟨by2, hby2, rfl⟩ := hdb
        dsimp only at hgo
        obtain ⟨hwf₁, hext₁, hden₁⟩ := hmax hgo
        exact ⟨hwf₁, hext₁, by simpa [Level.combining] using hden₁⟩
    | succ al =>
      rw [denoteLNode, Option.map_eq_some_iff] at hda
      obtain ⟨ax, hax, rfl⟩ := hda
      cases nb with
      | zero =>
        rw [denoteLNode] at hdb
        cases hdb
        dsimp only at hgo
        cases hgo
        exact ⟨hwf, Ext.refl st, by simpa [Level.combining] using ha⟩
      | param bp =>
        rw [denoteLNode] at hdb
        cases hdb
        dsimp only at hgo
        obtain ⟨hwf₁, hext₁, hden₁⟩ := hmax hgo
        exact ⟨hwf₁, hext₁, by simpa [Level.combining] using hden₁⟩
      | succ bl =>
        rw [denoteLNode, Option.map_eq_some_iff] at hdb
        obtain ⟨bx, hbx, rfl⟩ := hdb
        have hlt : al < a := hca al (by simp [LNode.children])
        dsimp only at hgo
        rw [dif_pos hlt] at hgo
        rcases hcomb : st.combiningLI al bl with ⟨c, st₁⟩
        rw [hcomb] at hgo
        obtain ⟨hwf₁, hext₁, hden₁⟩ := ih al hlt hax hbx hcomb
        obtain ⟨hwf₂, hext₂, hden₂⟩ := internL_step (n := .succ c) hwf₁
          (by simpa [LNode.children] using denoteL_lt_size hden₁)
          (a := .succ (Level.combining ax bx))
          (by rw [denoteLNode, hden₁]; rfl)
        rw [hgo] at hwf₂ hext₂ hden₂
        exact ⟨hwf₂, hext₁.trans hext₂,
          by simpa [Level.combining] using hden₂⟩
      | max bx' by' =>
        rw [denoteLNode, Option.bind_eq_some_iff] at hdb
        obtain ⟨bx, hbx, hdb⟩ := hdb
        rw [Option.map_eq_some_iff] at hdb
        obtain ⟨by2, hby2, rfl⟩ := hdb
        dsimp only at hgo
        obtain ⟨hwf₁, hext₁, hden₁⟩ := hmax hgo
        exact ⟨hwf₁, hext₁, by simpa [Level.combining] using hden₁⟩
      | imax bx' by' =>
        rw [denoteLNode, Option.bind_eq_some_iff] at hdb
        obtain ⟨bx, hbx, hdb⟩ := hdb
        rw [Option.map_eq_some_iff] at hdb
        obtain ⟨by2, hby2, rfl⟩ := hdb
        dsimp only at hgo
        obtain ⟨hwf₁, hext₁, hden₁⟩ := hmax hgo
        exact ⟨hwf₁, hext₁, by simpa [Level.combining] using hden₁⟩
    | max ax' ay' =>
      rw [denoteLNode, Option.bind_eq_some_iff] at hda
      obtain ⟨ax, hax, hda⟩ := hda
      rw [Option.map_eq_some_iff] at hda
      obtain ⟨ay2, hay2, rfl⟩ := hda
      cases nb with
      | zero =>
        rw [denoteLNode] at hdb
        cases hdb
        dsimp only at hgo
        cases hgo
        exact ⟨hwf, Ext.refl st, by simpa [Level.combining] using ha⟩
      | param bp =>
        rw [denoteLNode] at hdb
        cases hdb
        dsimp only at hgo
        obtain ⟨hwf₁, hext₁, hden₁⟩ := hmax hgo
        exact ⟨hwf₁, hext₁, by simpa [Level.combining] using hden₁⟩
      | succ bl =>
        rw [denoteLNode, Option.map_eq_some_iff] at hdb
        obtain ⟨bx, hbx, rfl⟩ := hdb
        dsimp only at hgo
        obtain ⟨hwf₁, hext₁, hden₁⟩ := hmax hgo
        exact ⟨hwf₁, hext₁, by simpa [Level.combining] using hden₁⟩
      | max bx' by' =>
        rw [denoteLNode, Option.bind_eq_some_iff] at hdb
        obtain ⟨bx, hbx, hdb⟩ := hdb
        rw [Option.map_eq_some_iff] at hdb
        obtain ⟨by2, hby2, rfl⟩ := hdb
        dsimp only at hgo
        obtain ⟨hwf₁, hext₁, hden₁⟩ := hmax hgo
        exact ⟨hwf₁, hext₁, by simpa [Level.combining] using hden₁⟩
      | imax bx' by' =>
        rw [denoteLNode, Option.bind_eq_some_iff] at hdb
        obtain ⟨bx, hbx, hdb⟩ := hdb
        rw [Option.map_eq_some_iff] at hdb
        obtain ⟨by2, hby2, rfl⟩ := hdb
        dsimp only at hgo
        obtain ⟨hwf₁, hext₁, hden₁⟩ := hmax hgo
        exact ⟨hwf₁, hext₁, by simpa [Level.combining] using hden₁⟩
    | imax ax' ay' =>
      rw [denoteLNode, Option.bind_eq_some_iff] at hda
      obtain ⟨ax, hax, hda⟩ := hda
      rw [Option.map_eq_some_iff] at hda
      obtain ⟨ay2, hay2, rfl⟩ := hda
      cases nb with
      | zero =>
        rw [denoteLNode] at hdb
        cases hdb
        dsimp only at hgo
        cases hgo
        exact ⟨hwf, Ext.refl st, by simpa [Level.combining] using ha⟩
      | param bp =>
        rw [denoteLNode] at hdb
        cases hdb
        dsimp only at hgo
        obtain ⟨hwf₁, hext₁, hden₁⟩ := hmax hgo
        exact ⟨hwf₁, hext₁, by simpa [Level.combining] using hden₁⟩
      | succ bl =>
        rw [denoteLNode, Option.map_eq_some_iff] at hdb
        obtain ⟨bx, hbx, rfl⟩ := hdb
        dsimp only at hgo
        obtain ⟨hwf₁, hext₁, hden₁⟩ := hmax hgo
        exact ⟨hwf₁, hext₁, by simpa [Level.combining] using hden₁⟩
      | max bx' by' =>
        rw [denoteLNode, Option.bind_eq_some_iff] at hdb
        obtain ⟨bx, hbx, hdb⟩ := hdb
        rw [Option.map_eq_some_iff] at hdb
        obtain ⟨by2, hby2, rfl⟩ := hdb
        dsimp only at hgo
        obtain ⟨hwf₁, hext₁, hden₁⟩ := hmax hgo
        exact ⟨hwf₁, hext₁, by simpa [Level.combining] using hden₁⟩
      | imax bx' by' =>
        rw [denoteLNode, Option.bind_eq_some_iff] at hdb
        obtain ⟨bx, hbx, hdb⟩ := hdb
        rw [Option.map_eq_some_iff] at hdb
        obtain ⟨by2, hby2, rfl⟩ := hdb
        dsimp only at hgo
        obtain ⟨hwf₁, hext₁, hden₁⟩ := hmax hgo
        exact ⟨hwf₁, hext₁, by simpa [Level.combining] using hden₁⟩

/-! ## `simplifyImax` -/

/-- The spec-level result shape of `simplifyImax` (a separate function
so the statement's match is non-dependent). -/
def simplifyImaxSpec (xls xrs : Level) : Level :=
  match xrs with
  | .zero => .zero
  | .succ m => Level.combining xls (.succ m)
  | m => .imax xls m

theorem simplifyImax_spec {st : EStore} {memo : LMemo}
    {ls rs ri : LIdx} {st' : EStore} {memo' : LMemo} {xls xrs : Level}
    (hwf : st.WF)
    (hls : st.denoteL ls = some xls) (hrs : st.denoteL rs = some xrs)
    (hgo : simplifyImax st memo ls rs = (ri, st', memo')) :
    st'.WF ∧ Ext st st' ∧ memo' = memo ∧
      st'.denoteL ri = some (simplifyImaxSpec xls xrs) := by
  unfold simplifyImax at hgo
  cases hrsn : st.lnodes[rs]? with
  | none =>
    obtain ⟨nrs, hnrs, -, -⟩ := denoteL_some_inv hrs
    rw [hrsn] at hnrs
    cases hnrs
  | some nrs =>
    rw [hrsn] at hgo
    cases nrs with
    | zero =>
      cases hgo
      have hz : xrs = Level.zero := by
        have := denoteL_head hrs hrsn
        simpa [denoteLNode] using this.symm
      subst hz
      exact ⟨hwf, Ext.refl st, rfl, by simpa [simplifyImaxSpec] using hrs⟩
    | succ z =>
      dsimp only at hgo
      rcases h₃ : st.combiningLI ls rs with ⟨c, st₁⟩
      rw [h₃] at hgo
      cases hgo
      obtain ⟨zx, hzx⟩ := denoteL_total hwf z
        (Nat.lt_trans
          (hwf.lchildren_lt _ _ hrsn z (by simp [LNode.children]))
          (Array.getElem?_eq_some_iff.mp hrsn).1)
      have hz : xrs = .succ zx := by
        have := denoteL_head hrs hrsn
        rw [denoteLNode, hzx] at this
        exact (Option.some.inj this).symm
      subst hz
      obtain ⟨hwf₁, hext₁, hden₁⟩ := combiningLI_spec hwf hls hrs h₃
      exact ⟨hwf₁, hext₁, rfl, by simpa [simplifyImaxSpec] using hden₁⟩
    | param p =>
      dsimp only at hgo
      rcases hI : st.internL (.imax ls rs) with ⟨c, st₁⟩
      rw [hI] at hgo
      cases hgo
      have hz : xrs = .param p := by
        have := denoteL_head hrs hrsn
        simpa [denoteLNode] using this.symm
      subst hz
      obtain ⟨hwf₁, hext₁, hden₁⟩ := internL_step (n := .imax ls rs) hwf
        (by
          simp only [LNode.children, List.mem_cons, List.not_mem_nil,
            or_false]
          rintro c (rfl | rfl)
          · exact denoteL_lt_size hls
          · exact denoteL_lt_size hrs)
        (a := .imax xls (.param p)) (by rw [denoteLNode, hls, hrs]; rfl)
      rw [hI] at hwf₁ hext₁ hden₁
      exact ⟨hwf₁, hext₁, rfl, by simpa [simplifyImaxSpec] using hden₁⟩
    | max a b =>
      dsimp only at hgo
      rcases hI : st.internL (.imax ls rs) with ⟨c, st₁⟩
      rw [hI] at hgo
      cases hgo
      obtain ⟨xx, yy, hz⟩ : ∃ xx yy, xrs = .max xx yy := by
        have := denoteL_head hrs hrsn
        rw [denoteLNode, Option.bind_eq_some_iff] at this
        obtain ⟨xx, -, this⟩ := this
        rw [Option.map_eq_some_iff] at this
        obtain ⟨yy, -, hres⟩ := this
        exact ⟨xx, yy, hres.symm⟩
      subst hz
      obtain ⟨hwf₁, hext₁, hden₁⟩ := internL_step (n := .imax ls rs) hwf
        (by
          simp only [LNode.children, List.mem_cons, List.not_mem_nil,
            or_false]
          rintro c (rfl | rfl)
          · exact denoteL_lt_size hls
          · exact denoteL_lt_size hrs)
        (a := .imax xls (.max xx yy)) (by rw [denoteLNode, hls, hrs]; rfl)
      rw [hI] at hwf₁ hext₁ hden₁
      exact ⟨hwf₁, hext₁, rfl, by simpa [simplifyImaxSpec] using hden₁⟩
    | imax a b =>
      dsimp only at hgo
      rcases hI : st.internL (.imax ls rs) with ⟨c, st₁⟩
      rw [hI] at hgo
      cases hgo
      obtain ⟨xx, yy, hz⟩ : ∃ xx yy, xrs = .imax xx yy := by
        have := denoteL_head hrs hrsn
        rw [denoteLNode, Option.bind_eq_some_iff] at this
        obtain ⟨xx, -, this⟩ := this
        rw [Option.map_eq_some_iff] at this
        obtain ⟨yy, -, hres⟩ := this
        exact ⟨xx, yy, hres.symm⟩
      subst hz
      obtain ⟨hwf₁, hext₁, hden₁⟩ := internL_step (n := .imax ls rs) hwf
        (by
          simp only [LNode.children, List.mem_cons, List.not_mem_nil,
            or_false]
          rintro c (rfl | rfl)
          · exact denoteL_lt_size hls
          · exact denoteL_lt_size hrs)
        (a := .imax xls (.imax xx yy)) (by rw [denoteLNode, hls, hrs]; rfl)
      rw [hI] at hwf₁ hext₁ hden₁
      exact ⟨hwf₁, hext₁, rfl, by simpa [simplifyImaxSpec] using hden₁⟩

/-! ## `simplifyLIGo` -/

theorem simplifyLIGo_spec :
    ∀ (u : LIdx) {st : EStore} {memo : LMemo} {r : LIdx}
      {st' : EStore} {memo' : LMemo},
      st.WF → LvlMemoInv st Level.simplify memo →
      simplifyLIGo st memo u = (r, st', memo') →
      st'.WF ∧ Ext st st' ∧ LvlMemoInv st' Level.simplify memo' ∧
        ∀ x, st.denoteL u = some x → st'.denoteL r = some x.simplify := by
  intro u
  induction u using Nat.strongRecOn with
  | _ u ih =>
    intro st memo r st' memo' hwf hinv hgo
    unfold simplifyLIGo at hgo
    split at hgo
    · rename_i hhit
      cases hgo
      exact ⟨hwf, Ext.refl st, hinv, (hinv _ _ hhit).2⟩
    · split at hgo
      · rename_i hnone
        cases hgo
        refine ⟨hwf, Ext.refl st, hinv, ?_⟩
        intro x hx
        obtain ⟨n, hn, -, -⟩ := denoteL_some_inv hx
        rw [hn] at hnone
        cases hnone
      · rename_i n hn
        have husz : u < st.lnodes.size := (Array.getElem?_eq_some_iff.mp hn).1
        have hcl := hwf.lchildren_lt u n hn
        have hde := denoteL_node hn hcl
        cases n with
        | zero =>
          dsimp only at hgo
          cases hgo
          have hx : st.denoteL u = some .zero := by rw [hde]; rfl
          have hcond : ∀ x, st.denoteL u = some x →
              st.denoteL u = some x.simplify := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simpa [Level.simplify] using hx
          exact ⟨hwf, Ext.refl st, hinv.insert husz hcond, hcond⟩
        | param p =>
          dsimp only at hgo
          cases hgo
          have hx : st.denoteL u = some (.param p) := by rw [hde]; rfl
          have hcond : ∀ x, st.denoteL u = some x →
              st.denoteL u = some x.simplify := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simpa [Level.simplify] using hx
          exact ⟨hwf, Ext.refl st, hinv.insert husz hcond, hcond⟩
        | succ l =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd (hcl l (by simp [LNode.children])) hguard
          case isTrue hguard =>
            rcases h₁ : simplifyLIGo st memo l with ⟨l', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : st₁.internL (.succ l') with ⟨ri, st₂⟩
            rw [h₂] at hgo
            cases hgo
            obtain ⟨xl, hl⟩ := denoteL_total hwf l (Nat.lt_trans hguard husz)
            have hx : st.denoteL u = some (.succ xl) := by
              rw [hde, denoteLNode, hl]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih l hguard hwf hinv h₁
            have hl₁ := hden₁ xl hl
            obtain ⟨hwf₂, hext₂, hden₂⟩ := internL_step (n := .succ l') hwf₁
              (by simpa [LNode.children] using denoteL_lt_size hl₁)
              (a := .succ xl.simplify) (by rw [denoteLNode, hl₁]; rfl)
            rw [h₂] at hwf₂ hext₂ hden₂
            have hextAll : Ext st st₂ := hext₁.trans hext₂
            have hcond : ∀ x, st.denoteL u = some x →
                st₂.denoteL ri = some x.simplify := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              simpa [Level.simplify] using hden₂
            refine ⟨hwf₂, hextAll, ?_, hcond⟩
            exact (hinv₁.mono hext₂).insert
              (Nat.lt_of_lt_of_le husz hextAll.lsize_le)
              (condL_transport hextAll husz hcond)
        | max l r' =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl l (by simp [LNode.children]),
              hcl r' (by simp [LNode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : simplifyLIGo st memo l with ⟨l', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : simplifyLIGo st₁ memo₁ r' with ⟨r₂, st₂, memo₂⟩
            rw [h₂] at hgo
            rcases h₃ : st₂.combiningLI l' r₂ with ⟨ri, st₃⟩
            rw [h₃] at hgo
            cases hgo
            obtain ⟨xl, hl⟩ := denoteL_total hwf l (Nat.lt_trans hguard.1 husz)
            obtain ⟨xr, hr⟩ := denoteL_total hwf r' (Nat.lt_trans hguard.2 husz)
            have hx : st.denoteL u = some (.max xl xr) := by
              rw [hde, denoteLNode, hl, hr]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih l hguard.1 hwf hinv h₁
            obtain ⟨hwf₂, hext₂, hinv₂, hden₂⟩ := ih r' hguard.2 hwf₁ hinv₁ h₂
            have hl₂ : st₂.denoteL l' = some xl.simplify :=
              denoteL_mono hext₂ (hden₁ xl hl)
            have hr₂ : st₂.denoteL r₂ = some xr.simplify :=
              hden₂ xr (denoteL_mono hext₁ hr)
            obtain ⟨hwf₃, hext₃, hden₃⟩ := combiningLI_spec hwf₂ hl₂ hr₂ h₃
            have hextAll : Ext st st₃ := hext₁.trans (hext₂.trans hext₃)
            have hcond : ∀ x, st.denoteL u = some x →
                st₃.denoteL ri = some x.simplify := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              simpa [Level.simplify] using hden₃
            refine ⟨hwf₃, hextAll, ?_, hcond⟩
            exact ((hinv₂.mono hext₃).insert
              (Nat.lt_of_lt_of_le husz hextAll.lsize_le)
              (condL_transport hextAll husz hcond))
        | imax l r' =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl l (by simp [LNode.children]),
              hcl r' (by simp [LNode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : simplifyLIGo st memo l with ⟨ls, st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : simplifyLIGo st₁ memo₁ r' with ⟨rs, st₂, memo₂⟩
            rw [h₂] at hgo
            obtain ⟨xl, hl⟩ := denoteL_total hwf l (Nat.lt_trans hguard.1 husz)
            obtain ⟨xr, hr⟩ := denoteL_total hwf r' (Nat.lt_trans hguard.2 husz)
            have hx : st.denoteL u = some (.imax xl xr) := by
              rw [hde, denoteLNode, hl, hr]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih l hguard.1 hwf hinv h₁
            obtain ⟨hwf₂, hext₂, hinv₂, hden₂⟩ := ih r' hguard.2 hwf₁ hinv₁ h₂
            have hls : st₂.denoteL ls = some xl.simplify :=
              denoteL_mono hext₂ (hden₁ xl hl)
            have hrs : st₂.denoteL rs = some xr.simplify :=
              hden₂ xr (denoteL_mono hext₁ hr)
            dsimp only at hgo
            -- the else path, shared by every non-collapsing left shape
            have hElse : ∀ {ri₀ : LIdx} {st₀ : EStore} {memo₀ : LMemo},
                simplifyImax st₂ memo₂ ls rs = (ri₀, st₀, memo₀) →
                xl.simplify ≠ Level.zero →
                xl.simplify ≠ Level.succ .zero →
                st₀.WF ∧ Ext st st₀ ∧
                  LvlMemoInv st₀ Level.simplify (memo₀.insert u ri₀) ∧
                  ∀ x, st.denoteL u = some x →
                    st₀.denoteL ri₀ = some x.simplify := by
              intro ri₀ st₀ memo₀ hSI hnz hnso
              obtain ⟨hwf₃, hext₃, rfl, hden₃⟩ :=
                simplifyImax_spec hwf₂ hls hrs hSI
              have hred : Level.simplify (.imax xl xr)
                  = simplifyImaxSpec xl.simplify xr.simplify := by
                simp only [Level.simplify]
                rw [if_neg (by simp [hnz, hnso])]
                cases hxr : xr.simplify <;> simp [simplifyImaxSpec]
              have hextAll : Ext st st₀ :=
                hext₁.trans (hext₂.trans hext₃)
              have hcond : ∀ x, st.denoteL u = some x →
                  st₀.denoteL ri₀ = some x.simplify := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                rw [hred]
                exact hden₃
              refine ⟨hwf₃, hextAll, ?_, hcond⟩
              exact ((hinv₂.mono hext₃).insert
                (Nat.lt_of_lt_of_le husz hextAll.lsize_le)
                (condL_transport hextAll husz hcond))
            -- the collapsing branch, shared by both collapse shapes
            have hColl : (xl.simplify = Level.zero ∨
                  xl.simplify = Level.succ .zero) →
                st₂.WF ∧ Ext st st₂ ∧
                  LvlMemoInv st₂ Level.simplify (memo₂.insert u rs) ∧
                  ∀ x, st.denoteL u = some x →
                    st₂.denoteL rs = some x.simplify := by
              intro hcoll
              have hred : Level.simplify (.imax xl xr) = xr.simplify := by
                simp only [Level.simplify]
                rcases hcoll with h | h <;> rw [if_pos (by simp [h])]
              have hextAll : Ext st st₂ := hext₁.trans hext₂
              have hcond : ∀ x, st.denoteL u = some x →
                  st₂.denoteL rs = some x.simplify := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                rw [hred]
                exact hrs
              refine ⟨hwf₂, hextAll, ?_, hcond⟩
              exact ((hinv₂).insert
                (Nat.lt_of_lt_of_le husz hextAll.lsize_le)
                (condL_transport hextAll husz hcond))
            cases hlsn : st₂.lnodes[ls]? with
            | none =>
              obtain ⟨nls, hnls, -, -⟩ := denoteL_some_inv hls
              rw [hlsn] at hnls
              cases hnls
            | some nls =>
              rw [hlsn] at hgo
              cases nls with
              | zero =>
                simp only [show ((some LNode.zero : Option LNode)
                    == some LNode.zero) = true from rfl, Bool.true_or,
                  reduceIte] at hgo
                cases hgo
                refine hColl (Or.inl ?_)
                have := denoteL_head hls hlsn
                simpa [denoteLNode] using this.symm
              | succ z =>
                obtain ⟨zx, hzx⟩ : ∃ zx, st₂.denoteL z = some zx := by
                  have := denoteL_head hls hlsn
                  rw [denoteLNode, Option.map_eq_some_iff] at this
                  obtain ⟨zx, hzx, -⟩ := this
                  exact ⟨zx, hzx⟩
                have hxls : xl.simplify = .succ zx := by
                  have := denoteL_head hls hlsn
                  rw [denoteLNode, hzx] at this
                  exact (Option.some.inj this).symm
                simp only [show ((some (LNode.succ z) : Option LNode)
                    == some LNode.zero) = false from rfl,
                  Bool.false_or] at hgo
                cases hzn : st₂.lnodes[z]? with
                | none =>
                  obtain ⟨nz, hnz', -, -⟩ := denoteL_some_inv hzx
                  rw [hzn] at hnz'
                  cases hnz'
                | some nz =>
                  rw [hzn] at hgo
                  cases nz with
                  | zero =>
                    simp only [show ((some LNode.zero : Option LNode)
                        == some LNode.zero) = true from rfl,
                      Bool.false_or, reduceIte] at hgo
                    cases hgo
                    refine hColl (Or.inr ?_)
                    have hzz : zx = Level.zero := by
                      have := denoteL_head hzx hzn
                      simpa [denoteLNode] using this.symm
                    rw [hxls, hzz]
                  | succ w =>
                    simp only [show ((some (LNode.succ w) : Option LNode)
                        == some LNode.zero) = false from rfl,
                      reduceIte] at hgo
                    rcases hSI : simplifyImax st₂ memo₂ ls rs
                      with ⟨ri₀, st₀, memo₀⟩
                    rw [hSI] at hgo
                    cases hgo
                    refine hElse hSI (by simp [hxls]) ?_
                    intro hcon
                    rw [hxls] at hcon
                    obtain ⟨rfl⟩ : zx = Level.zero := by
                      cases hcon; rfl
                    have := denoteL_head hzx hzn
                    rw [denoteLNode] at this
                    simp only [Option.map_eq_some_iff] at this
                    obtain ⟨q, -, hq⟩ := this
                    cases hq
                  | param q =>
                    simp only [show ((some (LNode.param q) : Option LNode)
                        == some LNode.zero) = false from rfl,
                      reduceIte] at hgo
                    rcases hSI : simplifyImax st₂ memo₂ ls rs
                      with ⟨ri₀, st₀, memo₀⟩
                    rw [hSI] at hgo
                    cases hgo
                    refine hElse hSI (by simp [hxls]) ?_
                    intro hcon
                    rw [hxls] at hcon
                    obtain ⟨rfl⟩ : zx = Level.zero := by
                      cases hcon; rfl
                    have := denoteL_head hzx hzn
                    rw [denoteLNode] at this
                    cases this
                  | max q1 q2 =>
                    simp only [show ((some (LNode.max q1 q2) : Option LNode)
                        == some LNode.zero) = false from rfl,
                      reduceIte] at hgo
                    rcases hSI : simplifyImax st₂ memo₂ ls rs
                      with ⟨ri₀, st₀, memo₀⟩
                    rw [hSI] at hgo
                    cases hgo
                    refine hElse hSI (by simp [hxls]) ?_
                    intro hcon
                    rw [hxls] at hcon
                    obtain ⟨rfl⟩ : zx = Level.zero := by
                      cases hcon; rfl
                    have := denoteL_head hzx hzn
                    rw [denoteLNode] at this
                    simp only [Option.bind_eq_some_iff,
                      Option.map_eq_some_iff] at this
                    obtain ⟨q, -, q', -, hq⟩ := this
                    cases hq
                  | imax q1 q2 =>
                    simp only [show ((some (LNode.imax q1 q2) : Option LNode)
                        == some LNode.zero) = false from rfl,
                      reduceIte] at hgo
                    rcases hSI : simplifyImax st₂ memo₂ ls rs
                      with ⟨ri₀, st₀, memo₀⟩
                    rw [hSI] at hgo
                    cases hgo
                    refine hElse hSI (by simp [hxls]) ?_
                    intro hcon
                    rw [hxls] at hcon
                    obtain ⟨rfl⟩ : zx = Level.zero := by
                      cases hcon; rfl
                    have := denoteL_head hzx hzn
                    rw [denoteLNode] at this
                    simp only [Option.bind_eq_some_iff,
                      Option.map_eq_some_iff] at this
                    obtain ⟨q, -, q', -, hq⟩ := this
                    cases hq
              | param p =>
                have hxls : xl.simplify = .param p := by
                  have := denoteL_head hls hlsn
                  simpa [denoteLNode] using this.symm
                simp only [show ((some (LNode.param p) : Option LNode)
                    == some LNode.zero) = false from rfl,
                  Bool.false_or, reduceIte] at hgo
                rcases hSI : simplifyImax st₂ memo₂ ls rs
                  with ⟨ri₀, st₀, memo₀⟩
                rw [hSI] at hgo
                cases hgo
                exact hElse hSI (by simp [hxls]) (by simp [hxls])
              | max a b =>
                obtain ⟨xx, yy, hxls⟩ : ∃ xx yy,
                    xl.simplify = .max xx yy := by
                  have := denoteL_head hls hlsn
                  rw [denoteLNode, Option.bind_eq_some_iff] at this
                  obtain ⟨xx, -, this⟩ := this
                  rw [Option.map_eq_some_iff] at this
                  obtain ⟨yy, -, hres⟩ := this
                  exact ⟨xx, yy, hres.symm⟩
                simp only [show ((some (LNode.max a b) : Option LNode)
                    == some LNode.zero) = false from rfl,
                  Bool.false_or, reduceIte] at hgo
                rcases hSI : simplifyImax st₂ memo₂ ls rs
                  with ⟨ri₀, st₀, memo₀⟩
                rw [hSI] at hgo
                cases hgo
                exact hElse hSI (by simp [hxls]) (by simp [hxls])
              | imax a b =>
                obtain ⟨xx, yy, hxls⟩ : ∃ xx yy,
                    xl.simplify = .imax xx yy := by
                  have := denoteL_head hls hlsn
                  rw [denoteLNode, Option.bind_eq_some_iff] at this
                  obtain ⟨xx, -, this⟩ := this
                  rw [Option.map_eq_some_iff] at this
                  obtain ⟨yy, -, hres⟩ := this
                  exact ⟨xx, yy, hres.symm⟩
                simp only [show ((some (LNode.imax a b) : Option LNode)
                    == some LNode.zero) = false from rfl,
                  Bool.false_or, reduceIte] at hgo
                rcases hSI : simplifyImax st₂ memo₂ ls rs
                  with ⟨ri₀, st₀, memo₀⟩
                rw [hSI] at hgo
                cases hgo
                exact hElse hSI (by simp [hxls]) (by simp [hxls])

/-! ## `isNonZeroLIGo` -/

/-- Invariant of a level→`Bool` memo implementing `g`. -/
def LvlQMemoInv (st : EStore) (g : Level → Bool)
    (memo : Std.HashMap LIdx Bool) : Prop :=
  ∀ u b, memo[u]? = some b → u < st.lnodes.size ∧
    ∀ x, st.denoteL u = some x → g x = b

theorem LvlQMemoInv.empty {st : EStore} {g : Level → Bool} :
    LvlQMemoInv st g {} := by
  intro u b h
  simp at h

theorem LvlQMemoInv.mono {st st' : EStore} {g : Level → Bool}
    {memo : Std.HashMap LIdx Bool} (hext : Ext st st')
    (h : LvlQMemoInv st g memo) : LvlQMemoInv st' g memo := by
  intro u b hb
  obtain ⟨hlt, hcond⟩ := h u b hb
  refine ⟨Nat.lt_of_lt_of_le hlt hext.lsize_le, ?_⟩
  intro x hx
  rw [hext.denoteL_eq_of_lt hlt] at hx
  exact hcond x hx

theorem LvlQMemoInv.insert {st : EStore} {g : Level → Bool}
    {memo : Std.HashMap LIdx Bool} {u : LIdx} {b : Bool}
    (h : LvlQMemoInv st g memo) (hlt : u < st.lnodes.size)
    (hcond : ∀ x, st.denoteL u = some x → g x = b) :
    LvlQMemoInv st g (memo.insert u b) := by
  intro u' b' hb'
  rw [Std.HashMap.getElem?_insert] at hb'
  by_cases hk : u = u'
  · subst hk
    rw [if_pos (by simp)] at hb'
    cases hb'
    exact ⟨hlt, hcond⟩
  · rw [if_neg (by simpa using hk)] at hb'
    exact h u' b' hb'

/-- Invariant of the `isEquiv` *result* cache (`IState.eqvC`): a
stored verdict is the spec verdict on the denotations of its key
pair (which the arena determines). -/
def EqvMemoInv (st : EStore)
    (memo : Std.HashMap (LIdx × LIdx) Bool) : Prop :=
  ∀ l r b, memo[(l, r)]? = some b →
    ∃ la ra, st.denoteL l = some la ∧ st.denoteL r = some ra ∧
      Level.isEquiv la ra = some b

theorem EqvMemoInv.empty {st : EStore} : EqvMemoInv st {} := by
  intro l r b h
  simp at h

theorem EqvMemoInv.mono {st st' : EStore}
    {memo : Std.HashMap (LIdx × LIdx) Bool} (hext : Ext st st')
    (h : EqvMemoInv st memo) : EqvMemoInv st' memo := by
  intro l r b hb
  obtain ⟨la, ra, hl, hr, he⟩ := h l r b hb
  exact ⟨la, ra, denoteL_mono hext hl, denoteL_mono hext hr, he⟩

theorem EqvMemoInv.insert {st : EStore}
    {memo : Std.HashMap (LIdx × LIdx) Bool} {l r : LIdx}
    {la ra : Level} {b : Bool} (h : EqvMemoInv st memo)
    (hl : st.denoteL l = some la) (hr : st.denoteL r = some ra)
    (he : Level.isEquiv la ra = some b) :
    EqvMemoInv st (memo.insert (l, r) b) := by
  intro l' r' b' hb'
  rw [Std.HashMap.getElem?_insert] at hb'
  by_cases hk : l = l' ∧ r = r'
  · obtain ⟨rfl, rfl⟩ := hk
    rw [if_pos (by simp)] at hb'
    cases hb'
    exact ⟨la, ra, hl, hr, he⟩
  · rw [if_neg (by simpa [Prod.ext_iff] using hk)] at hb'
    exact h l' r' b' hb'

theorem isNonZeroLIGo_spec {st : EStore} (hwf : st.WF) :
    ∀ (u : LIdx) {memo : Std.HashMap LIdx Bool} {b : Bool}
      {memo' : Std.HashMap LIdx Bool},
      LvlQMemoInv st Level.isNonZero memo →
      isNonZeroLIGo st memo u = (b, memo') →
      LvlQMemoInv st Level.isNonZero memo' ∧
        ∀ x, st.denoteL u = some x → x.isNonZero = b := by
  intro u
  induction u using Nat.strongRecOn with
  | _ u ih =>
    intro memo b memo' hinv hgo
    unfold isNonZeroLIGo at hgo
    split at hgo
    · rename_i hhit
      cases hgo
      exact ⟨hinv, (hinv _ _ hhit).2⟩
    · split at hgo
      · rename_i hnone
        cases hgo
        refine ⟨hinv, ?_⟩
        intro x hx
        obtain ⟨n, hn, -, -⟩ := denoteL_some_inv hx
        rw [hn] at hnone
        cases hnone
      · rename_i n hn
        have husz : u < st.lnodes.size := (Array.getElem?_eq_some_iff.mp hn).1
        have hcl := hwf.lchildren_lt u n hn
        have hde := denoteL_node hn hcl
        cases n with
        | zero =>
          dsimp only at hgo
          cases hgo
          have hcond : ∀ x, st.denoteL u = some x → x.isNonZero = false := by
            intro x hxx
            rw [hde] at hxx
            cases hxx
            rfl
          exact ⟨hinv.insert husz hcond, hcond⟩
        | param p =>
          dsimp only at hgo
          cases hgo
          have hcond : ∀ x, st.denoteL u = some x → x.isNonZero = false := by
            intro x hxx
            rw [hde] at hxx
            cases hxx
            rfl
          exact ⟨hinv.insert husz hcond, hcond⟩
        | succ l =>
          dsimp only at hgo
          cases hgo
          have hcond : ∀ x, st.denoteL u = some x → x.isNonZero = true := by
            intro x hxx
            rw [hde] at hxx
            rw [denoteLNode, Option.map_eq_some_iff] at hxx
            obtain ⟨y, -, rfl⟩ := hxx
            rfl
          exact ⟨hinv.insert husz hcond, hcond⟩
        | max a b' =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl a (by simp [LNode.children]),
              hcl b' (by simp [LNode.children])⟩ hguard
          case isTrue hguard =>
            obtain ⟨xa, hxa⟩ := denoteL_total hwf a
              (Nat.lt_trans hguard.1 husz)
            obtain ⟨xb, hxb⟩ := denoteL_total hwf b'
              (Nat.lt_trans hguard.2 husz)
            have hx : st.denoteL u = some (.max xa xb) := by
              rw [hde, denoteLNode, hxa, hxb]; rfl
            rcases h₁ : isNonZeroLIGo st memo a with ⟨ra, memo₁⟩
            rw [h₁] at hgo
            obtain ⟨hinv₁, hden₁⟩ := ih a hguard.1 hinv h₁
            have hra := hden₁ xa hxa
            cases hb : ra with
            | true =>
              rw [hb] at hgo
              dsimp only at hgo
              cases hgo
              have hcond : ∀ x, st.denoteL u = some x →
                  x.isNonZero = true := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                simp only [Level.isNonZero]
                rw [hra, hb, Bool.true_or]
              exact ⟨hinv₁.insert husz hcond, hcond⟩
            | false =>
              rw [hb] at hgo
              dsimp only at hgo
              rcases h₂ : isNonZeroLIGo st memo₁ b' with ⟨rb, memo₂⟩
              rw [h₂] at hgo
              cases hgo
              obtain ⟨hinv₂, hden₂⟩ := ih b' hguard.2 hinv₁ h₂
              have hrb := hden₂ xb hxb
              have hcond : ∀ x, st.denoteL u = some x →
                  x.isNonZero = rb := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                simp only [Level.isNonZero]
                rw [hra, hb, hrb, Bool.false_or]
              exact ⟨hinv₂.insert husz hcond, hcond⟩
        | imax a b' =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd (hcl b' (by simp [LNode.children])) hguard
          case isTrue hguard =>
            obtain ⟨xa, hxa⟩ := denoteL_total hwf a
              (Nat.lt_trans (hcl a (by simp [LNode.children])) husz)
            obtain ⟨xb, hxb⟩ := denoteL_total hwf b'
              (Nat.lt_trans hguard husz)
            have hx : st.denoteL u = some (.imax xa xb) := by
              rw [hde, denoteLNode, hxa, hxb]; rfl
            rcases h₂ : isNonZeroLIGo st memo b' with ⟨rb, memo₂⟩
            rw [h₂] at hgo
            cases hgo
            obtain ⟨hinv₂, hden₂⟩ := ih b' hguard hinv h₂
            have hrb := hden₂ xb hxb
            have hcond : ∀ x, st.denoteL u = some x →
                x.isNonZero = rb := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              simp only [Level.isNonZero]
              exact hrb
            exact ⟨hinv₂.insert husz hcond, hcond⟩

/-! ## `internLevelSubst` -/

theorem internLevelSubst_spec {ks : List Name} {us : List LIdx}
    {lus : List Level} :
    ∀ (l : Level) {st : EStore} {r : LIdx} {st' : EStore},
      st.WF → denoteLList st.denoteL us = some lus →
      st.internLevelSubst ks us l = (r, st') →
      st'.WF ∧ Ext st st' ∧
        st'.denoteL r = some (Level.subst ks lus l) := by
  intro l
  induction l with
  | zero =>
    intro st r st' hwf hus hgo
    unfold internLevelSubst at hgo
    obtain ⟨hwf₁, hext₁, hden₁⟩ := internL_step (n := .zero) hwf
      (by simp [LNode.children]) (a := .zero) rfl
    rw [hgo] at hwf₁ hext₁ hden₁
    exact ⟨hwf₁, hext₁, by simpa [Level.subst] using hden₁⟩
  | param n =>
    intro st r st' hwf hus hgo
    unfold internLevelSubst at hgo
    cases hv : substLGo? ks us n with
    | some v =>
      rw [hv] at hgo
      dsimp only at hgo
      cases hgo
      refine ⟨hwf, Ext.refl st, ?_⟩
      simpa [Level.subst] using (substLGo?_spec n hus).1 _ hv
    | none =>
      rw [hv] at hgo
      dsimp only at hgo
      obtain ⟨hwf₁, hext₁, hden₁⟩ := internL_step (n := .param n) hwf
        (by simp [LNode.children]) (a := .param n) rfl
      rw [hgo] at hwf₁ hext₁ hden₁
      refine ⟨hwf₁, hext₁, ?_⟩
      rw [Level.subst, (substLGo?_spec n hus).2 hv]
      exact hden₁
  | succ x ih =>
    intro st r st' hwf hus hgo
    unfold internLevelSubst at hgo
    rcases h₁ : st.internLevelSubst ks us x with ⟨x', st₁⟩
    rw [h₁] at hgo
    dsimp only at hgo
    obtain ⟨hwf₁, hext₁, hden₁⟩ := ih hwf hus h₁
    obtain ⟨hwf₂, hext₂, hden₂⟩ := internL_step (n := .succ x') hwf₁
      (by simpa [LNode.children] using denoteL_lt_size hden₁)
      (a := .succ (Level.subst ks lus x)) (by rw [denoteLNode, hden₁]; rfl)
    rw [hgo] at hwf₂ hext₂ hden₂
    exact ⟨hwf₂, hext₁.trans hext₂, by simpa [Level.subst] using hden₂⟩
  | max x y ihx ihy =>
    intro st r st' hwf hus hgo
    unfold internLevelSubst at hgo
    rcases h₁ : st.internLevelSubst ks us x with ⟨x', st₁⟩
    rw [h₁] at hgo
    dsimp only at hgo
    rcases h₂ : st₁.internLevelSubst ks us y with ⟨y', st₂⟩
    rw [h₂] at hgo
    dsimp only at hgo
    obtain ⟨hwf₁, hext₁, hden₁⟩ := ihx hwf hus h₁
    obtain ⟨hwf₂, hext₂, hden₂⟩ := ihy hwf₁ (denoteLList_mono hext₁ hus) h₂
    obtain ⟨hwf₃, hext₃, hden₃⟩ := internL_step (n := .max x' y') hwf₂
      (by
        simp only [LNode.children, List.mem_cons, List.not_mem_nil, or_false]
        rintro c (rfl | rfl)
        · exact denoteL_lt_size (denoteL_mono hext₂ hden₁)
        · exact denoteL_lt_size hden₂)
      (a := .max (Level.subst ks lus x) (Level.subst ks lus y))
      (by rw [denoteLNode, denoteL_mono hext₂ hden₁, hden₂]; rfl)
    rw [hgo] at hwf₃ hext₃ hden₃
    exact ⟨hwf₃, hext₁.trans (hext₂.trans hext₃),
      by simpa [Level.subst] using hden₃⟩
  | imax x y ihx ihy =>
    intro st r st' hwf hus hgo
    unfold internLevelSubst at hgo
    rcases h₁ : st.internLevelSubst ks us x with ⟨x', st₁⟩
    rw [h₁] at hgo
    dsimp only at hgo
    rcases h₂ : st₁.internLevelSubst ks us y with ⟨y', st₂⟩
    rw [h₂] at hgo
    dsimp only at hgo
    obtain ⟨hwf₁, hext₁, hden₁⟩ := ihx hwf hus h₁
    obtain ⟨hwf₂, hext₂, hden₂⟩ := ihy hwf₁ (denoteLList_mono hext₁ hus) h₂
    obtain ⟨hwf₃, hext₃, hden₃⟩ := internL_step (n := .imax x' y') hwf₂
      (by
        simp only [LNode.children, List.mem_cons, List.not_mem_nil, or_false]
        rintro c (rfl | rfl)
        · exact denoteL_lt_size (denoteL_mono hext₂ hden₁)
        · exact denoteL_lt_size hden₂)
      (a := .imax (Level.subst ks lus x) (Level.subst ks lus y))
      (by rw [denoteLNode, denoteL_mono hext₂ hden₁, hden₂]; rfl)
    rw [hgo] at hwf₃ hext₃ hden₃
    exact ⟨hwf₃, hext₁.trans (hext₂.trans hext₃),
      by simpa [Level.subst] using hden₃⟩

theorem internLevelSubsts_spec {ks : List Name} {us : List LIdx}
    {lus : List Level} :
    ∀ (ls : List Level) {st : EStore} {rs : List LIdx} {st' : EStore},
      st.WF → denoteLList st.denoteL us = some lus →
      st.internLevelSubsts ks us ls = (rs, st') →
      st'.WF ∧ Ext st st' ∧
        denoteLList st'.denoteL rs
          = some (ls.map (Level.subst ks lus)) := by
  intro ls
  induction ls with
  | nil =>
    intro st rs st' hwf hus hgo
    cases hgo
    exact ⟨hwf, Ext.refl st, rfl⟩
  | cons l ls ih =>
    intro st rs st' hwf hus hgo
    unfold internLevelSubsts at hgo
    rcases h₁ : st.internLevelSubst ks us l with ⟨r, st₁⟩
    rw [h₁] at hgo
    dsimp only at hgo
    rcases h₂ : st₁.internLevelSubsts ks us ls with ⟨rs', st₂⟩
    rw [h₂] at hgo
    dsimp only at hgo
    cases hgo
    obtain ⟨hwf₁, hext₁, hden₁⟩ := internLevelSubst_spec l hwf hus h₁
    obtain ⟨hwf₂, hext₂, hden₂⟩ := ih hwf₁ (denoteLList_mono hext₁ hus) h₂
    refine ⟨hwf₂, hext₁.trans hext₂, ?_⟩
    simp [denoteLList, denoteL_mono hext₂ hden₁, hden₂]

/-! ## The fueled comparison twins

Spec-side reduction equations for `Level.imaxRules` (per source arm,
with the earlier arms' non-firing supplied as shape hypotheses), then
the arena twins' faithfulness by induction on the fuel.
-/

private theorem imaxRules_param_left (fuel : Nat) (a : Level) (p : Name)
    (r : Level) (diff : Int) :
    Level.imaxRules fuel (.imax a (.param p)) r diff
      = Level.byCases fuel p (.imax a (.param p)) r diff := by
  cases r with
  | imax x y => cases y <;> simp [Level.imaxRules]
  | _ => simp [Level.imaxRules]

private theorem imaxRules_param_right (fuel : Nat) (l x : Level) (p : Name)
    (diff : Int) (h : ∀ a q, l ≠ .imax a (.param q)) :
    Level.imaxRules fuel l (.imax x (.param p)) diff
      = Level.byCases fuel p l (.imax x (.param p)) diff := by
  cases l with
  | imax a b =>
    cases b with
    | param q => exact absurd rfl (h a q)
    | _ => simp [Level.imaxRules]
  | _ => simp [Level.imaxRules]

private theorem imaxRules_imax_left (fuel : Nat) (a x y r : Level)
    (diff : Int) (h : ∀ w q, r ≠ .imax w (.param q)) :
    Level.imaxRules fuel (.imax a (.imax x y)) r diff
      = Level.leqCore fuel (.max (.imax a y) (.imax x y)) r diff := by
  cases r with
  | imax w z =>
    cases z with
    | param q => exact absurd rfl (h w q)
    | _ => simp [Level.imaxRules]
  | _ => simp [Level.imaxRules]

private theorem imaxRules_max_left (fuel : Nat) (a x y r : Level)
    (diff : Int) (h : ∀ w q, r ≠ .imax w (.param q)) :
    Level.imaxRules fuel (.imax a (.max x y)) r diff
      = Level.leqCore fuel
          (Level.simplify (.max (.imax a x) (.imax a y))) r diff := by
  cases r with
  | imax w z =>
    cases z with
    | param q => exact absurd rfl (h w q)
    | _ => simp [Level.imaxRules]
  | _ => simp [Level.imaxRules]

/-- The left side fires no arm: not an `imax` whose right component is
a parameter, `imax`, or `max`. -/
private def NoLeftArm (l : Level) : Prop :=
  ∀ a b, l = .imax a b →
    (∀ p, b ≠ .param p) ∧ (∀ x y, b ≠ .imax x y) ∧ (∀ x y, b ≠ .max x y)

private theorem imaxRules_imax_right (fuel : Nat) (l x j k : Level)
    (diff : Int) (hl : NoLeftArm l) :
    Level.imaxRules fuel l (.imax x (.imax j k)) diff
      = Level.leqCore fuel l (.max (.imax x k) (.imax j k)) diff := by
  cases l with
  | imax a b =>
    obtain ⟨h1, h2, h3⟩ := hl a b rfl
    cases b with
    | param q => exact absurd rfl (h1 q)
    | imax w z => exact absurd rfl (h2 w z)
    | max w z => exact absurd rfl (h3 w z)
    | _ => simp [Level.imaxRules]
  | _ => simp [Level.imaxRules]

private theorem imaxRules_max_right (fuel : Nat) (l x j k : Level)
    (diff : Int) (hl : NoLeftArm l) :
    Level.imaxRules fuel l (.imax x (.max j k)) diff
      = Level.leqCore fuel l
          (Level.simplify (.max (.imax x j) (.imax x k))) diff := by
  cases l with
  | imax a b =>
    obtain ⟨h1, h2, h3⟩ := hl a b rfl
    cases b with
    | param q => exact absurd rfl (h1 q)
    | imax w z => exact absurd rfl (h2 w z)
    | max w z => exact absurd rfl (h3 w z)
    | _ => simp [Level.imaxRules]
  | _ => simp [Level.imaxRules]

private theorem imaxRules_none (fuel : Nat) (l r : Level) (diff : Int)
    (hl : NoLeftArm l) (hr : NoLeftArm r)
    (hrp : ∀ x q, r ≠ .imax x (.param q)) :
    Level.imaxRules fuel l r diff = none := by
  cases l with
  | imax a b =>
    obtain ⟨h1, h2, h3⟩ := hl a b rfl
    cases b with
    | param q => exact absurd rfl (h1 q)
    | imax w z => exact absurd rfl (h2 w z)
    | max w z => exact absurd rfl (h3 w z)
    | zero =>
      cases r with
      | imax x y =>
        obtain ⟨g1, g2, g3⟩ := hr x y rfl
        cases y with
        | param q => exact absurd rfl (g1 q)
        | imax w z => exact absurd rfl (g2 w z)
        | max w z => exact absurd rfl (g3 w z)
        | _ => simp [Level.imaxRules]
      | _ => simp [Level.imaxRules]
    | succ w =>
      cases r with
      | imax x y =>
        obtain ⟨g1, g2, g3⟩ := hr x y rfl
        cases y with
        | param q => exact absurd rfl (g1 q)
        | imax w' z => exact absurd rfl (g2 w' z)
        | max w' z => exact absurd rfl (g3 w' z)
        | _ => simp [Level.imaxRules]
      | _ => simp [Level.imaxRules]
  | _ =>
    cases r with
    | imax x y =>
      obtain ⟨g1, g2, g3⟩ := hr x y rfl
      cases y with
      | param q => exact absurd rfl (g1 q)
      | imax w z => exact absurd rfl (g2 w z)
      | max w z => exact absurd rfl (g3 w z)
      | _ => simp [Level.imaxRules]
    | _ => simp [Level.imaxRules]

/-- `substLI` (fresh-memo wrapper) commutes with the denotation. -/
theorem substLI_spec {st : EStore} {ks : List Name} {us : List LIdx}
    {lus : List Level} {u : LIdx} {la : Level} {r : LIdx} {st' : EStore}
    (hwf : st.WF) (hus : denoteLList st.denoteL us = some lus)
    (hl : st.denoteL u = some la) (hgo : st.substLI ks us u = (r, st')) :
    st'.WF ∧ Ext st st' ∧ st'.denoteL r = some (Level.subst ks lus la) := by
  unfold substLI at hgo
  rcases h₁ : substLIGo ks us st {} u with ⟨r₁, st₁, memo₁⟩
  rw [h₁] at hgo
  cases hgo
  obtain ⟨hwf₁, hext₁, -, hden₁⟩ := substLIGo_spec u hwf hus LvlMemoInv.empty h₁
  exact ⟨hwf₁, hext₁, hden₁ la hl⟩

/-- The induction bundle: `leqCoreLI`'s faithfulness at a given fuel. -/
def LeqIH (fuel : Nat) : Prop :=
  ∀ {st : EStore} {memo : EStore.LMemo} {l r : LIdx} {diff : Int}
    {la ra : Level} {ob : Option Bool} {st' : EStore} {memo' : EStore.LMemo},
    st.WF → LvlMemoInv st Level.simplify memo →
    st.denoteL l = some la → st.denoteL r = some ra →
    leqCoreLI st memo fuel l r diff = (ob, st', memo') →
    st'.WF ∧ Ext st st' ∧ LvlMemoInv st' Level.simplify memo' ∧
      ob = Level.leqCore fuel la ra diff

private theorem byCasesLI_spec {fuel : Nat} (ihc : LeqIH fuel)
    {st : EStore} {memo : EStore.LMemo} {p : Name} {l r : LIdx}
    {diff : Int} {la ra : Level} {ob : Option Bool} {st' : EStore}
    {memo' : EStore.LMemo}
    (hwf : st.WF) (hinv : LvlMemoInv st Level.simplify memo)
    (hl : st.denoteL l = some la) (hr : st.denoteL r = some ra)
    (hgo : byCasesLI st memo fuel p l r diff = (ob, st', memo')) :
    st'.WF ∧ Ext st st' ∧ LvlMemoInv st' Level.simplify memo' ∧
      ob = Level.byCases fuel p la ra diff := by
  unfold byCasesLI at hgo
  rcases hz : st.internL .zero with ⟨z, stz⟩
  rw [hz] at hgo
  dsimp only at hgo
  obtain ⟨hwfz, hextz, hdenz⟩ := internL_step (n := .zero) hwf
    (by simp [LNode.children]) (a := .zero) rfl
  rw [hz] at hwfz hextz hdenz
  rcases hp : stz.internL (.param p) with ⟨pp, stp⟩
  rw [hp] at hgo
  dsimp only at hgo
  obtain ⟨hwfp, hextp, hdenp⟩ := internL_step (n := .param p) hwfz
    (by simp [LNode.children]) (a := .param p) rfl
  rw [hp] at hwfp hextp hdenp
  rcases hsp : stp.internL (.succ pp) with ⟨sp, stsp⟩
  rw [hsp] at hgo
  dsimp only at hgo
  obtain ⟨hwfsp, hextsp, hdensp⟩ := internL_step (n := .succ pp) hwfp
    (by simpa [LNode.children] using denoteL_lt_size hdenp)
    (a := .succ (.param p)) (by rw [denoteLNode, hdenp]; rfl)
  rw [hsp] at hwfsp hextsp hdensp
  -- accumulated denotation facts at stsp
  have hdz : stsp.denoteL z = some .zero :=
    denoteL_mono hextsp (denoteL_mono hextp hdenz)
  have husz : denoteLList stsp.denoteL [z] = some [Level.zero] := by
    simp [denoteLList, hdz]
  have hussp : denoteLList stsp.denoteL [sp]
      = some [Level.succ (.param p)] := by
    simp [denoteLList, hdensp]
  have hl' : stsp.denoteL l = some la :=
    denoteL_mono hextsp (denoteL_mono hextp (denoteL_mono hextz hl))
  have hr' : stsp.denoteL r = some ra :=
    denoteL_mono hextsp (denoteL_mono hextp (denoteL_mono hextz hr))
  have hinv' : LvlMemoInv stsp Level.simplify memo :=
    (hinv.mono hextz).mono hextp |>.mono hextsp
  -- l0
  rcases h1 : stsp.substLI [p] [z] l with ⟨l0', st1⟩
  rw [h1] at hgo
  dsimp only at hgo
  obtain ⟨hwf1, hext1, hden1⟩ := substLI_spec hwfsp husz hl' h1
  rcases h2 : simplifyLIGo st1 memo l0' with ⟨l0, st2, memo2⟩
  rw [h2] at hgo
  dsimp only at hgo
  obtain ⟨hwf2, hext2, hinv2, hden2⟩ :=
    simplifyLIGo_spec l0' hwf1 (hinv'.mono hext1) h2
  have hl0 : st2.denoteL l0
      = some (Level.simplify (Level.subst [p] [.zero] la)) :=
    hden2 _ hden1
  -- r0
  rcases h3 : st2.substLI [p] [z] r with ⟨r0', st3⟩
  rw [h3] at hgo
  dsimp only at hgo
  obtain ⟨hwf3, hext3, hden3⟩ := substLI_spec hwf2
    (denoteLList_mono (hext1.trans hext2) husz)
    (denoteL_mono (hext1.trans hext2) hr') h3
  rcases h4 : simplifyLIGo st3 memo2 r0' with ⟨r0, st4, memo4⟩
  rw [h4] at hgo
  dsimp only at hgo
  obtain ⟨hwf4, hext4, hinv4, hden4⟩ :=
    simplifyLIGo_spec r0' hwf3 (hinv2.mono hext3) h4
  have hr0 : st4.denoteL r0
      = some (Level.simplify (Level.subst [p] [.zero] ra)) :=
    hden4 _ hden3
  -- ls
  rcases h5 : st4.substLI [p] [sp] l with ⟨ls', st5⟩
  rw [h5] at hgo
  dsimp only at hgo
  obtain ⟨hwf5, hext5, hden5⟩ := substLI_spec hwf4
    (denoteLList_mono
      (((hext1.trans hext2).trans hext3).trans hext4) hussp)
    (denoteL_mono
      (((hext1.trans hext2).trans hext3).trans hext4) hl') h5
  rcases h6 : simplifyLIGo st5 memo4 ls' with ⟨lsI, st6, memo6⟩
  rw [h6] at hgo
  dsimp only at hgo
  obtain ⟨hwf6, hext6, hinv6, hden6⟩ :=
    simplifyLIGo_spec ls' hwf5 (hinv4.mono hext5) h6
  have hls : st6.denoteL lsI
      = some (Level.simplify
        (Level.subst [p] [.succ (.param p)] la)) :=
    hden6 _ hden5
  -- rs
  rcases h7 : st6.substLI [p] [sp] r with ⟨rs', st7⟩
  rw [h7] at hgo
  dsimp only at hgo
  obtain ⟨hwf7, hext7, hden7⟩ := substLI_spec hwf6
    (denoteLList_mono
      (((((hext1.trans hext2).trans hext3).trans hext4).trans
        hext5).trans hext6) hussp)
    (denoteL_mono
      (((((hext1.trans hext2).trans hext3).trans hext4).trans
        hext5).trans hext6) hr') h7
  rcases h8 : simplifyLIGo st7 memo6 rs' with ⟨rsI, st8, memo8⟩
  rw [h8] at hgo
  dsimp only at hgo
  obtain ⟨hwf8, hext8, hinv8, hden8⟩ :=
    simplifyLIGo_spec rs' hwf7 (hinv6.mono hext7) h8
  have hrs : st8.denoteL rsI
      = some (Level.simplify
        (Level.subst [p] [.succ (.param p)] ra)) :=
    hden8 _ hden7
  -- the two comparisons
  rcases h9 : leqCoreLI st8 memo8 fuel l0 r0 diff with ⟨ob1, st9, memo9⟩
  rw [h9] at hgo
  have hextTo8 : Ext st2 st8 :=
    ((((hext3.trans hext4).trans hext5).trans hext6).trans
      (hext7.trans hext8))
  obtain ⟨hwf9, hext9, hinv9, hob1⟩ := ihc hwf8 hinv8
    (denoteL_mono hextTo8 hl0)
    (denoteL_mono ((((hext5.trans hext6).trans hext7).trans hext8)) hr0)
    h9
  cases ob1 with
  | none =>
    dsimp only at hgo
    cases hgo
    refine ⟨hwf9, ?_, hinv9, ?_⟩
    · exact ((((((((((hextz.trans hextp).trans hextsp).trans
        hext1).trans hext2).trans hext3).trans hext4).trans
        hext5).trans hext6).trans (hext7.trans hext8)).trans hext9)
    · rw [Level.byCases, ← hob1]
      rfl
  | some b1 =>
    dsimp only at hgo
    rcases h10 : leqCoreLI st9 memo9 fuel lsI rsI diff
      with ⟨ob2, st10, memo10⟩
    rw [h10] at hgo
    obtain ⟨hwf10, hext10, hinv10, hob2⟩ := ihc hwf9 hinv9
      (denoteL_mono ((hext7.trans hext8).trans hext9) hls)
      (denoteL_mono hext9 hrs)
      h10
    cases ob2 with
    | none =>
      dsimp only at hgo
      cases hgo
      refine ⟨hwf10, ?_, hinv10, ?_⟩
      · exact ((((((((((hextz.trans hextp).trans hextsp).trans
          hext1).trans hext2).trans hext3).trans hext4).trans
          hext5).trans hext6).trans (hext7.trans hext8)).trans
          (hext9.trans hext10))
      · rw [Level.byCases, ← hob1, ← hob2]
        rfl
    | some b2 =>
      dsimp only at hgo
      cases hgo
      refine ⟨hwf10, ?_, hinv10, ?_⟩
      · exact ((((((((((hextz.trans hextp).trans hextsp).trans
          hext1).trans hext2).trans hext3).trans hext4).trans
          hext5).trans hext6).trans (hext7.trans hext8)).trans
          (hext9.trans hext10))
      · rw [Level.byCases, ← hob1, ← hob2]
        rfl

/-- Spec shape of the right-`imax` distribution helper. -/
private def imaxRightSpec (fuel : Nat) (la xx yy : Level) (diff : Int) :
    Option Bool :=
  match yy with
  | .imax j k => Level.leqCore fuel la (.max (.imax xx k) (.imax j k)) diff
  | .max j k => Level.leqCore fuel la
      (Level.simplify (.max (.imax xx j) (.imax xx k))) diff
  | _ => none

private theorem imaxRulesRightLI_spec {fuel : Nat} (ihc : LeqIH fuel)
    {st : EStore} {memo : EStore.LMemo} {l x y : LIdx} {diff : Int}
    {la xx yy : Level} {ob : Option Bool} {st' : EStore}
    {memo' : EStore.LMemo}
    (hwf : st.WF) (hinv : LvlMemoInv st Level.simplify memo)
    (hl : st.denoteL l = some la)
    (hx : st.denoteL x = some xx) (hy : st.denoteL y = some yy)
    (hgo : imaxRulesRightLI st memo fuel l diff x y = (ob, st', memo')) :
    st'.WF ∧ Ext st st' ∧ LvlMemoInv st' Level.simplify memo' ∧
      ob = imaxRightSpec fuel la xx yy diff := by
  obtain ⟨ny, hyn, hyc, hyd⟩ := denoteL_some_inv hy
  unfold imaxRulesRightLI at hgo
  rw [hyn] at hgo
  cases ny with
  | zero =>
    rw [denoteLNode] at hyd
    cases hyd
    cases hgo
    exact ⟨hwf, Ext.refl st, hinv, rfl⟩
  | param q =>
    rw [denoteLNode] at hyd
    cases hyd
    cases hgo
    exact ⟨hwf, Ext.refl st, hinv, rfl⟩
  | succ w =>
    rw [denoteLNode, Option.map_eq_some_iff] at hyd
    obtain ⟨wx, hwx, rfl⟩ := hyd
    cases hgo
    exact ⟨hwf, Ext.refl st, hinv, rfl⟩
  | imax j k =>
    rw [denoteLNode, Option.bind_eq_some_iff] at hyd
    obtain ⟨jx, hjx, hyd⟩ := hyd
    rw [Option.map_eq_some_iff] at hyd
    obtain ⟨kx, hkx, rfl⟩ := hyd
    dsimp only at hgo
    rcases h1 : st.internL (.imax x k) with ⟨i1, st1⟩
    rw [h1] at hgo
    dsimp only at hgo
    obtain ⟨hwf1, hext1, hden1⟩ := internL_step (n := .imax x k) hwf
      (by
        simp only [LNode.children, List.mem_cons, List.not_mem_nil, or_false]
        rintro c (rfl | rfl)
        · exact denoteL_lt_size hx
        · exact denoteL_lt_size hkx)
      (a := .imax xx kx) (by rw [denoteLNode, hx, hkx]; rfl)
    rw [h1] at hwf1 hext1 hden1
    rcases h2 : st1.internL (.imax j k) with ⟨i2, st2⟩
    rw [h2] at hgo
    dsimp only at hgo
    obtain ⟨hwf2, hext2, hden2⟩ := internL_step (n := .imax j k) hwf1
      (by
        simp only [LNode.children, List.mem_cons, List.not_mem_nil, or_false]
        rintro c (rfl | rfl)
        · exact denoteL_lt_size (denoteL_mono hext1 hjx)
        · exact denoteL_lt_size (denoteL_mono hext1 hkx))
      (a := .imax jx kx)
      (by rw [denoteLNode, denoteL_mono hext1 hjx,
        denoteL_mono hext1 hkx]; rfl)
    rw [h2] at hwf2 hext2 hden2
    rcases h3 : st2.internL (.max i1 i2) with ⟨m, st3⟩
    rw [h3] at hgo
    dsimp only at hgo
    obtain ⟨hwf3, hext3, hden3⟩ := internL_step (n := .max i1 i2) hwf2
      (by
        simp only [LNode.children, List.mem_cons, List.not_mem_nil, or_false]
        rintro c (rfl | rfl)
        · exact denoteL_lt_size (denoteL_mono hext2 hden1)
        · exact denoteL_lt_size hden2)
      (a := .max (.imax xx kx) (.imax jx kx))
      (by rw [denoteLNode, denoteL_mono hext2 hden1, hden2]; rfl)
    rw [h3] at hwf3 hext3 hden3
    obtain ⟨hwf4, hext4, hinv4, hob⟩ := ihc hwf3
      (((hinv.mono hext1).mono hext2).mono hext3)
      (denoteL_mono hext3 (denoteL_mono hext2 (denoteL_mono hext1 hl)))
      hden3 hgo
    exact ⟨hwf4, ((hext1.trans hext2).trans hext3).trans hext4, hinv4, hob⟩
  | max j k =>
    rw [denoteLNode, Option.bind_eq_some_iff] at hyd
    obtain ⟨jx, hjx, hyd⟩ := hyd
    rw [Option.map_eq_some_iff] at hyd
    obtain ⟨kx, hkx, rfl⟩ := hyd
    dsimp only at hgo
    rcases h1 : st.internL (.imax x j) with ⟨i1, st1⟩
    rw [h1] at hgo
    dsimp only at hgo
    obtain ⟨hwf1, hext1, hden1⟩ := internL_step (n := .imax x j) hwf
      (by
        simp only [LNode.children, List.mem_cons, List.not_mem_nil, or_false]
        rintro c (rfl | rfl)
        · exact denoteL_lt_size hx
        · exact denoteL_lt_size hjx)
      (a := .imax xx jx) (by rw [denoteLNode, hx, hjx]; rfl)
    rw [h1] at hwf1 hext1 hden1
    rcases h2 : st1.internL (.imax x k) with ⟨i2, st2⟩
    rw [h2] at hgo
    dsimp only at hgo
    obtain ⟨hwf2, hext2, hden2⟩ := internL_step (n := .imax x k) hwf1
      (by
        simp only [LNode.children, List.mem_cons, List.not_mem_nil, or_false]
        rintro c (rfl | rfl)
        · exact denoteL_lt_size (denoteL_mono hext1 hx)
        · exact denoteL_lt_size (denoteL_mono hext1 hkx))
      (a := .imax xx kx)
      (by rw [denoteLNode, denoteL_mono hext1 hx,
        denoteL_mono hext1 hkx]; rfl)
    rw [h2] at hwf2 hext2 hden2
    rcases h3 : st2.internL (.max i1 i2) with ⟨m, st3⟩
    rw [h3] at hgo
    dsimp only at hgo
    obtain ⟨hwf3, hext3, hden3⟩ := internL_step (n := .max i1 i2) hwf2
      (by
        simp only [LNode.children, List.mem_cons, List.not_mem_nil, or_false]
        rintro c (rfl | rfl)
        · exact denoteL_lt_size (denoteL_mono hext2 hden1)
        · exact denoteL_lt_size hden2)
      (a := .max (.imax xx jx) (.imax xx kx))
      (by rw [denoteLNode, denoteL_mono hext2 hden1, hden2]; rfl)
    rw [h3] at hwf3 hext3 hden3
    rcases h4 : simplifyLIGo st3 memo m with ⟨ms, st4, memo4⟩
    rw [h4] at hgo
    dsimp only at hgo
    obtain ⟨hwf4, hext4, hinv4, hden4⟩ := simplifyLIGo_spec m hwf3
      (((hinv.mono hext1).mono hext2).mono hext3) h4
    have hms := hden4 _ hden3
    obtain ⟨hwf5, hext5, hinv5, hob⟩ := ihc hwf4 hinv4
      (denoteL_mono hext4 (denoteL_mono hext3
        (denoteL_mono hext2 (denoteL_mono hext1 hl))))
      hms hgo
    exact ⟨hwf5,
      (((hext1.trans hext2).trans hext3).trans hext4).trans hext5,
      hinv5, hob⟩

/-- Spec shape of the left-`imax` distribution helper. -/
private def imaxRestSpec (fuel : Nat) (xa xb ra : Level) (diff : Int) :
    Option Bool :=
  match xb with
  | .imax xx yy =>
    Level.leqCore fuel (.max (.imax xa yy) (.imax xx yy)) ra diff
  | .max xx yy =>
    Level.leqCore fuel
      (Level.simplify (.max (.imax xa xx) (.imax xa yy))) ra diff
  | _ =>
    match ra with
    | .imax xx yy => imaxRightSpec fuel (.imax xa xb) xx yy diff
    | _ => none

private theorem imaxRulesRestLI_spec {fuel : Nat} (ihc : LeqIH fuel)
    {st : EStore} {memo : EStore.LMemo} {l r a b : LIdx} {diff : Int}
    {xa xb ra : Level} {ob : Option Bool} {st' : EStore}
    {memo' : EStore.LMemo}
    (hwf : st.WF) (hinv : LvlMemoInv st Level.simplify memo)
    (hla : st.denoteL l = some (.imax xa xb))
    (ha : st.denoteL a = some xa) (hb : st.denoteL b = some xb)
    (hr : st.denoteL r = some ra)
    (hgo : imaxRulesRestLI st memo fuel l r diff a b = (ob, st', memo')) :
    st'.WF ∧ Ext st st' ∧ LvlMemoInv st' Level.simplify memo' ∧
      ob = imaxRestSpec fuel xa xb ra diff := by
  obtain ⟨nb, hbn, hbc, hbd⟩ := denoteL_some_inv hb
  unfold imaxRulesRestLI at hgo
  rw [hbn] at hgo
  cases nb with
  | imax x y =>
    rw [denoteLNode, Option.bind_eq_some_iff] at hbd
    obtain ⟨xx, hxx, hbd⟩ := hbd
    rw [Option.map_eq_some_iff] at hbd
    obtain ⟨yy, hyy, rfl⟩ := hbd
    dsimp only at hgo
    rcases h1 : st.internL (.imax a y) with ⟨i1, st1⟩
    rw [h1] at hgo
    dsimp only at hgo
    obtain ⟨hwf1, hext1, hden1⟩ := internL_step (n := .imax a y) hwf
      (by
        simp only [LNode.children, List.mem_cons, List.not_mem_nil, or_false]
        rintro c (rfl | rfl)
        · exact denoteL_lt_size ha
        · exact denoteL_lt_size hyy)
      (a := .imax xa yy) (by rw [denoteLNode, ha, hyy]; rfl)
    rw [h1] at hwf1 hext1 hden1
    rcases h2 : st1.internL (.imax x y) with ⟨i2, st2⟩
    rw [h2] at hgo
    dsimp only at hgo
    obtain ⟨hwf2, hext2, hden2⟩ := internL_step (n := .imax x y) hwf1
      (by
        simp only [LNode.children, List.mem_cons, List.not_mem_nil, or_false]
        rintro c (rfl | rfl)
        · exact denoteL_lt_size (denoteL_mono hext1 hxx)
        · exact denoteL_lt_size (denoteL_mono hext1 hyy))
      (a := .imax xx yy)
      (by rw [denoteLNode, denoteL_mono hext1 hxx,
        denoteL_mono hext1 hyy]; rfl)
    rw [h2] at hwf2 hext2 hden2
    rcases h3 : st2.internL (.max i1 i2) with ⟨m, st3⟩
    rw [h3] at hgo
    dsimp only at hgo
    obtain ⟨hwf3, hext3, hden3⟩ := internL_step (n := .max i1 i2) hwf2
      (by
        simp only [LNode.children, List.mem_cons, List.not_mem_nil, or_false]
        rintro c (rfl | rfl)
        · exact denoteL_lt_size (denoteL_mono hext2 hden1)
        · exact denoteL_lt_size hden2)
      (a := .max (.imax xa yy) (.imax xx yy))
      (by rw [denoteLNode, denoteL_mono hext2 hden1, hden2]; rfl)
    rw [h3] at hwf3 hext3 hden3
    obtain ⟨hwf4, hext4, hinv4, hob⟩ := ihc hwf3
      (((hinv.mono hext1).mono hext2).mono hext3)
      hden3
      (denoteL_mono hext3 (denoteL_mono hext2 (denoteL_mono hext1 hr)))
      hgo
    exact ⟨hwf4, ((hext1.trans hext2).trans hext3).trans hext4, hinv4, hob⟩
  | max x y =>
    rw [denoteLNode, Option.bind_eq_some_iff] at hbd
    obtain ⟨xx, hxx, hbd⟩ := hbd
    rw [Option.map_eq_some_iff] at hbd
    obtain ⟨yy, hyy, rfl⟩ := hbd
    dsimp only at hgo
    rcases h1 : st.internL (.imax a x) with ⟨i1, st1⟩
    rw [h1] at hgo
    dsimp only at hgo
    obtain ⟨hwf1, hext1, hden1⟩ := internL_step (n := .imax a x) hwf
      (by
        simp only [LNode.children, List.mem_cons, List.not_mem_nil, or_false]
        rintro c (rfl | rfl)
        · exact denoteL_lt_size ha
        · exact denoteL_lt_size hxx)
      (a := .imax xa xx) (by rw [denoteLNode, ha, hxx]; rfl)
    rw [h1] at hwf1 hext1 hden1
    rcases h2 : st1.internL (.imax a y) with ⟨i2, st2⟩
    rw [h2] at hgo
    dsimp only at hgo
    obtain ⟨hwf2, hext2, hden2⟩ := internL_step (n := .imax a y) hwf1
      (by
        simp only [LNode.children, List.mem_cons, List.not_mem_nil, or_false]
        rintro c (rfl | rfl)
        · exact denoteL_lt_size (denoteL_mono hext1 ha)
        · exact denoteL_lt_size (denoteL_mono hext1 hyy))
      (a := .imax xa yy)
      (by rw [denoteLNode, denoteL_mono hext1 ha,
        denoteL_mono hext1 hyy]; rfl)
    rw [h2] at hwf2 hext2 hden2
    rcases h3 : st2.internL (.max i1 i2) with ⟨m, st3⟩
    rw [h3] at hgo
    dsimp only at hgo
    obtain ⟨hwf3, hext3, hden3⟩ := internL_step (n := .max i1 i2) hwf2
      (by
        simp only [LNode.children, List.mem_cons, List.not_mem_nil, or_false]
        rintro c (rfl | rfl)
        · exact denoteL_lt_size (denoteL_mono hext2 hden1)
        · exact denoteL_lt_size hden2)
      (a := .max (.imax xa xx) (.imax xa yy))
      (by rw [denoteLNode, denoteL_mono hext2 hden1, hden2]; rfl)
    rw [h3] at hwf3 hext3 hden3
    rcases h4 : simplifyLIGo st3 memo m with ⟨ms, st4, memo4⟩
    rw [h4] at hgo
    dsimp only at hgo
    obtain ⟨hwf4, hext4, hinv4, hden4⟩ := simplifyLIGo_spec m hwf3
      (((hinv.mono hext1).mono hext2).mono hext3) h4
    have hms := hden4 _ hden3
    obtain ⟨hwf5, hext5, hinv5, hob⟩ := ihc hwf4 hinv4 hms
      (denoteL_mono hext4 (denoteL_mono hext3
        (denoteL_mono hext2 (denoteL_mono hext1 hr))))
      hgo
    exact ⟨hwf5,
      (((hext1.trans hext2).trans hext3).trans hext4).trans hext5,
      hinv5, hob⟩
  | zero =>
    rw [denoteLNode] at hbd
    cases hbd
    obtain ⟨nr, hrn, -, hrd⟩ := denoteL_some_inv hr
    rw [hrn] at hgo
    cases nr with
    | imax x' y' =>
      rw [denoteLNode, Option.bind_eq_some_iff] at hrd
      obtain ⟨xx, hxx, hrd⟩ := hrd
      rw [Option.map_eq_some_iff] at hrd
      obtain ⟨yy, hyy, rfl⟩ := hrd
      obtain ⟨hwf1, hext1, hinv1, hob⟩ :=
        imaxRulesRightLI_spec ihc hwf hinv hla hxx hyy hgo
      exact ⟨hwf1, hext1, hinv1, hob⟩
    | zero =>
      rw [denoteLNode] at hrd
      cases hrd
      cases hgo
      exact ⟨hwf, Ext.refl st, hinv, rfl⟩
    | param q =>
      rw [denoteLNode] at hrd
      cases hrd
      cases hgo
      exact ⟨hwf, Ext.refl st, hinv, rfl⟩
    | succ w =>
      rw [denoteLNode, Option.map_eq_some_iff] at hrd
      obtain ⟨wx, -, rfl⟩ := hrd
      cases hgo
      exact ⟨hwf, Ext.refl st, hinv, rfl⟩
    | max x' y' =>
      rw [denoteLNode, Option.bind_eq_some_iff] at hrd
      obtain ⟨xx, -, hrd⟩ := hrd
      rw [Option.map_eq_some_iff] at hrd
      obtain ⟨yy, -, rfl⟩ := hrd
      cases hgo
      exact ⟨hwf, Ext.refl st, hinv, rfl⟩
  | succ w =>
    rw [denoteLNode, Option.map_eq_some_iff] at hbd
    obtain ⟨wx, hwx, rfl⟩ := hbd
    obtain ⟨nr, hrn, -, hrd⟩ := denoteL_some_inv hr
    rw [hrn] at hgo
    cases nr with
    | imax x' y' =>
      rw [denoteLNode, Option.bind_eq_some_iff] at hrd
      obtain ⟨xx, hxx, hrd⟩ := hrd
      rw [Option.map_eq_some_iff] at hrd
      obtain ⟨yy, hyy, rfl⟩ := hrd
      obtain ⟨hwf1, hext1, hinv1, hob⟩ :=
        imaxRulesRightLI_spec ihc hwf hinv hla hxx hyy hgo
      exact ⟨hwf1, hext1, hinv1, hob⟩
    | zero =>
      rw [denoteLNode] at hrd
      cases hrd
      cases hgo
      exact ⟨hwf, Ext.refl st, hinv, rfl⟩
    | param q =>
      rw [denoteLNode] at hrd
      cases hrd
      cases hgo
      exact ⟨hwf, Ext.refl st, hinv, rfl⟩
    | succ w' =>
      rw [denoteLNode, Option.map_eq_some_iff] at hrd
      obtain ⟨wx', -, rfl⟩ := hrd
      cases hgo
      exact ⟨hwf, Ext.refl st, hinv, rfl⟩
    | max x' y' =>
      rw [denoteLNode, Option.bind_eq_some_iff] at hrd
      obtain ⟨xx, -, hrd⟩ := hrd
      rw [Option.map_eq_some_iff] at hrd
      obtain ⟨yy, -, rfl⟩ := hrd
      cases hgo
      exact ⟨hwf, Ext.refl st, hinv, rfl⟩
  | param q =>
    rw [denoteLNode] at hbd
    cases hbd
    obtain ⟨nr, hrn, -, hrd⟩ := denoteL_some_inv hr
    rw [hrn] at hgo
    cases nr with
    | imax x' y' =>
      rw [denoteLNode, Option.bind_eq_some_iff] at hrd
      obtain ⟨xx, hxx, hrd⟩ := hrd
      rw [Option.map_eq_some_iff] at hrd
      obtain ⟨yy, hyy, rfl⟩ := hrd
      obtain ⟨hwf1, hext1, hinv1, hob⟩ :=
        imaxRulesRightLI_spec ihc hwf hinv hla hxx hyy hgo
      exact ⟨hwf1, hext1, hinv1, hob⟩
    | zero =>
      rw [denoteLNode] at hrd
      cases hrd
      cases hgo
      exact ⟨hwf, Ext.refl st, hinv, rfl⟩
    | param q' =>
      rw [denoteLNode] at hrd
      cases hrd
      cases hgo
      exact ⟨hwf, Ext.refl st, hinv, rfl⟩
    | succ w' =>
      rw [denoteLNode, Option.map_eq_some_iff] at hrd
      obtain ⟨wx', -, rfl⟩ := hrd
      cases hgo
      exact ⟨hwf, Ext.refl st, hinv, rfl⟩
    | max x' y' =>
      rw [denoteLNode, Option.bind_eq_some_iff] at hrd
      obtain ⟨xx, -, hrd⟩ := hrd
      rw [Option.map_eq_some_iff] at hrd
      obtain ⟨yy, -, rfl⟩ := hrd
      cases hgo
      exact ⟨hwf, Ext.refl st, hinv, rfl⟩

/-- Convert `imaxRightSpec` to `Level.imaxRules` (the right side is an
`imax` whose second component is not a parameter; no left arm fires). -/
private theorem imaxRightSpec_eq {fuel : Nat} {la xx yy : Level}
    {diff : Int} (hla : NoLeftArm la) (hyy : ∀ p, yy ≠ .param p) :
    imaxRightSpec fuel la xx yy diff
      = Level.imaxRules fuel la (.imax xx yy) diff := by
  cases yy with
  | param p => exact absurd rfl (hyy p)
  | imax j k =>
    rw [imaxRules_imax_right fuel la xx j k diff hla]
    rfl
  | max j k =>
    rw [imaxRules_max_right fuel la xx j k diff hla]
    rfl
  | zero =>
    rw [imaxRules_none fuel la (.imax xx .zero) diff hla
      (by rintro a b hcon; cases hcon; refine ⟨fun p h => ?_, fun x y h => ?_, fun x y h => ?_⟩ <;> cases h)
      (by rintro x q hcon; cases hcon)]
    rfl
  | succ w =>
    rw [imaxRules_none fuel la (.imax xx (.succ w)) diff hla
      (by rintro a b hcon; cases hcon; refine ⟨fun p h => ?_, fun x y h => ?_, fun x y h => ?_⟩ <;> cases h)
      (by rintro x q hcon; cases hcon)]
    rfl

/-- Convert `imaxRestSpec` to `Level.imaxRules` (the left side is an
`imax` whose second component is not a parameter; the right side is
not an `imax`-with-parameter). -/
private theorem imaxRestSpec_eq {fuel : Nat} {xa xb ra : Level}
    {diff : Int} (hxb : ∀ p, xb ≠ .param p)
    (hnp : ∀ w q, ra ≠ .imax w (.param q)) :
    imaxRestSpec fuel xa xb ra diff
      = Level.imaxRules fuel (.imax xa xb) ra diff := by
  cases xb with
  | param p => exact absurd rfl (hxb p)
  | imax xx yy =>
    rw [imaxRules_imax_left fuel xa xx yy ra diff hnp]
    rfl
  | max xx yy =>
    rw [imaxRules_max_left fuel xa xx yy ra diff hnp]
    rfl
  | zero =>
    have hla : NoLeftArm (.imax xa .zero) := by
      rintro a b hcon; cases hcon
      refine ⟨fun p h => ?_, fun x y h => ?_, fun x y h => ?_⟩ <;> cases h
    cases ra with
    | imax xx yy =>
      have hyy : ∀ p, yy ≠ .param p := by
        intro p hcon
        exact hnp xx p (by rw [hcon])
      exact imaxRightSpec_eq hla hyy
    | zero =>
      rw [imaxRules_none fuel _ .zero diff hla
        (by rintro a b hcon; cases hcon) (by rintro x q hcon; cases hcon)]
      rfl
    | param q =>
      rw [imaxRules_none fuel _ (.param q) diff hla
        (by rintro a b hcon; cases hcon) (by rintro x q' hcon; cases hcon)]
      rfl
    | succ w =>
      rw [imaxRules_none fuel _ (.succ w) diff hla
        (by rintro a b hcon; cases hcon) (by rintro x q hcon; cases hcon)]
      rfl
    | max x y =>
      rw [imaxRules_none fuel _ (.max x y) diff hla
        (by rintro a b hcon; cases hcon) (by rintro x' q hcon; cases hcon)]
      rfl
  | succ w =>
    have hla : NoLeftArm (.imax xa (.succ w)) := by
      rintro a b hcon; cases hcon
      refine ⟨fun p h => ?_, fun x y h => ?_, fun x y h => ?_⟩ <;> cases h
    cases ra with
    | imax xx yy =>
      have hyy : ∀ p, yy ≠ .param p := by
        intro p hcon
        exact hnp xx p (by rw [hcon])
      exact imaxRightSpec_eq hla hyy
    | zero =>
      rw [imaxRules_none fuel _ .zero diff hla
        (by rintro a b hcon; cases hcon) (by rintro x q hcon; cases hcon)]
      rfl
    | param q =>
      rw [imaxRules_none fuel _ (.param q) diff hla
        (by rintro a b hcon; cases hcon) (by rintro x q' hcon; cases hcon)]
      rfl
    | succ w' =>
      rw [imaxRules_none fuel _ (.succ w') diff hla
        (by rintro a b hcon; cases hcon) (by rintro x q hcon; cases hcon)]
      rfl
    | max x y =>
      rw [imaxRules_none fuel _ (.max x y) diff hla
        (by rintro a b hcon; cases hcon) (by rintro x' q hcon; cases hcon)]
      rfl

private theorem imaxRulesLI_spec {fuel : Nat} (ihc : LeqIH fuel)
    {st : EStore} {memo : EStore.LMemo} {l r : LIdx} {diff : Int}
    {la ra : Level} {ob : Option Bool} {st' : EStore}
    {memo' : EStore.LMemo}
    (hwf : st.WF) (hinv : LvlMemoInv st Level.simplify memo)
    (hl : st.denoteL l = some la) (hr : st.denoteL r = some ra)
    (hgo : imaxRulesLI st memo fuel l r diff = (ob, st', memo')) :
    st'.WF ∧ Ext st st' ∧ LvlMemoInv st' Level.simplify memo' ∧
      ob = Level.imaxRules fuel la ra diff := by
  obtain ⟨nl, hln, hlc, hld⟩ := denoteL_some_inv hl
  unfold imaxRulesLI at hgo
  rw [hln] at hgo
  -- helpers about the right side
  have hRdecomp : ∀ {x' y' : LIdx}, st.lnodes[r]? = some (.imax x' y') →
      ∃ xx yy, st.denoteL x' = some xx ∧ st.denoteL y' = some yy ∧
        ra = .imax xx yy := by
    intro x' y' hrn
    have := denoteL_head hr hrn
    rw [denoteLNode, Option.bind_eq_some_iff] at this
    obtain ⟨xx, hxx, this⟩ := this
    rw [Option.map_eq_some_iff] at this
    obtain ⟨yy, hyy, hres⟩ := this
    exact ⟨xx, yy, hxx, hyy, hres.symm⟩
  have hRnoParam : ∀ {x' y' : LIdx},
      st.lnodes[r]? = some (.imax x' y') →
      (∀ p, st.lnodes[y']? ≠ some (.param p)) →
      ∀ w q, ra ≠ .imax w (.param q) := by
    intro x' y' hrn hnp w q hcon
    obtain ⟨a, b, hab, -, hb⟩ := denoteL_imax_node (hcon ▸ hr)
    rw [hrn] at hab
    cases hab
    exact hnp q (denoteL_param_node hb)
  have hRnotImax : (∀ x' y', st.lnodes[r]? ≠ some (.imax x' y')) →
      ∀ w q, ra ≠ .imax w (.param q) := by
    intro hno w q hcon
    obtain ⟨a', b', hab, -, -⟩ := denoteL_imax_node (hcon ▸ hr)
    exact hno a' b' hab
  -- the r-side dispatch shared by every non-param left component
  have hRSide : ∀ (cont : Unit),
      (∀ {ob₀ st₀ memo₀}, imaxRulesRestLI st memo fuel l r diff
          (0 : LIdx) (0 : LIdx) = (ob₀, st₀, memo₀) → True) → True :=
    fun _ _ => trivial
  clear hRSide
  cases nl with
  | imax a b =>
    dsimp only at hgo
    rw [denoteLNode, Option.bind_eq_some_iff] at hld
    obtain ⟨xa, hxa, hld⟩ := hld
    rw [Option.map_eq_some_iff] at hld
    obtain ⟨xb, hxb, rfl⟩ := hld
    obtain ⟨nb, hbn, -, hbd⟩ := denoteL_some_inv hxb
    rw [hbn] at hgo
    -- b's node determines whether arm 1 fires
    cases hnbp : nb with
    | param p =>
      rw [hnbp] at hgo hbd
      dsimp only at hgo
      have hxbp : xb = .param p := by
        rw [denoteLNode] at hbd
        exact (Option.some.inj hbd).symm
      subst hxbp
      obtain ⟨hwf1, hext1, hinv1, hob⟩ :=
        byCasesLI_spec ihc hwf hinv hl hr hgo
      refine ⟨hwf1, hext1, hinv1, ?_⟩
      rw [hob, imaxRules_param_left]
    | _ =>
      -- xb is not a parameter
      rw [hnbp] at hgo hbd
      dsimp only at hgo
      have hxbnp : ∀ q, xb ≠ .param q := by
        intro q hcon
        subst hcon
        first
        | (rw [denoteLNode] at hbd; cases hbd)
        | (rw [denoteLNode, Option.map_eq_some_iff] at hbd;
           obtain ⟨w', -, hres⟩ := hbd; cases hres)
        | (rw [denoteLNode, Option.bind_eq_some_iff] at hbd;
           obtain ⟨w', -, hbd⟩ := hbd;
           rw [Option.map_eq_some_iff] at hbd;
           obtain ⟨w'', -, hres⟩ := hbd; cases hres)
      subst hnbp
      cases hrn : st.lnodes[r]? with
      | some nr =>
        rw [hrn] at hgo
        cases nr with
        | imax x' y' =>
          dsimp only at hgo
          cases hyn : st.lnodes[y']? with
          | some ny =>
            rw [hyn] at hgo
            cases hnyp : ny with
            | param p =>
              rw [hnyp] at hgo
              dsimp only at hgo
              rw [hnyp] at hyn
              obtain ⟨xx, yy, hxx, hyy, hra⟩ := hRdecomp hrn
              have hyyp : yy = .param p := by
                have := denoteL_head hyy hyn
                simpa [denoteLNode] using this.symm
              subst hra
              subst hyyp
              obtain ⟨hwf1, hext1, hinv1, hob⟩ :=
                byCasesLI_spec ihc hwf hinv hl hr hgo
              refine ⟨hwf1, hext1, hinv1, ?_⟩
              rw [hob, imaxRules_param_right]
              intro a' q hcon
              cases hcon
              exact hxbnp q rfl
            | _ =>
              rw [hnyp] at hgo hyn
              dsimp only at hgo
              obtain ⟨hwf1, hext1, hinv1, hob⟩ :=
                imaxRulesRestLI_spec ihc hwf hinv hl hxa hxb hr hgo
              refine ⟨hwf1, hext1, hinv1, ?_⟩
              rw [hob, imaxRestSpec_eq hxbnp
                (hRnoParam hrn (by rw [hyn]; rintro p hcon; cases hcon))]
          | none =>
            obtain ⟨xx, yy, -, hyy, -⟩ := hRdecomp hrn
            obtain ⟨ny, hny, -, -⟩ := denoteL_some_inv hyy
            rw [hyn] at hny
            cases hny
        | _ =>
          dsimp only at hgo
          obtain ⟨hwf1, hext1, hinv1, hob⟩ :=
            imaxRulesRestLI_spec ihc hwf hinv hl hxa hxb hr hgo
          refine ⟨hwf1, hext1, hinv1, ?_⟩
          rw [hob, imaxRestSpec_eq hxbnp
            (hRnotImax (by rw [hrn]; rintro x' y' hcon; cases hcon))]
      | none =>
        obtain ⟨nr, hnr, -, -⟩ := denoteL_some_inv hr
        rw [hrn] at hnr
        cases hnr
  | _ =>
    -- the left side is not an imax
    dsimp only at hgo
    have hlaNoArm : NoLeftArm la := by
      intro a b hcon
      obtain ⟨a', b', hab, -, -⟩ := denoteL_imax_node (hcon ▸ hl)
      rw [hln] at hab
      cases hab
    have hlaNotImaxParam : ∀ a q, la ≠ .imax a (.param q) := by
      intro a q hcon
      obtain ⟨h1, -, -⟩ := hlaNoArm a (.param q) hcon
      exact h1 q rfl
    cases hrn : st.lnodes[r]? with
    | some nr =>
      rw [hrn] at hgo
      cases nr with
      | imax x' y' =>
        dsimp only at hgo
        cases hyn : st.lnodes[y']? with
        | some ny =>
          rw [hyn] at hgo
          cases hnyp : ny with
          | param p =>
            rw [hnyp] at hgo
            dsimp only at hgo
            rw [hnyp] at hyn
            obtain ⟨xx, yy, hxx, hyy, hra⟩ := hRdecomp hrn
            have hyyp : yy = .param p := by
              have := denoteL_head hyy hyn
              simpa [denoteLNode] using this.symm
            subst hra
            subst hyyp
            obtain ⟨hwf1, hext1, hinv1, hob⟩ :=
              byCasesLI_spec ihc hwf hinv hl hr hgo
            refine ⟨hwf1, hext1, hinv1, ?_⟩
            rw [hob, imaxRules_param_right fuel la xx p diff
              hlaNotImaxParam]
          | _ =>
            rw [hnyp] at hgo hyn
            dsimp only at hgo
            obtain ⟨xx, yy, hxx, hyy, hra⟩ := hRdecomp hrn
            subst hra
            obtain ⟨hwf1, hext1, hinv1, hob⟩ :=
              imaxRulesRightLI_spec ihc hwf hinv hl hxx hyy hgo
            refine ⟨hwf1, hext1, hinv1, ?_⟩
            rw [hob, imaxRightSpec_eq hlaNoArm (by
              intro p hcon
              subst hcon
              exact absurd (denoteL_param_node hyy) (by
                rw [hyn]; rintro hcon'; cases hcon'))]
        | none =>
          obtain ⟨xx, yy, -, hyy, -⟩ := hRdecomp hrn
          obtain ⟨ny, hny, -, -⟩ := denoteL_some_inv hyy
          rw [hyn] at hny
          cases hny
      | _ =>
        dsimp only at hgo
        cases hgo
        refine ⟨hwf, Ext.refl st, hinv, ?_⟩
        rw [imaxRules_none fuel la ra diff hlaNoArm ?_ ?_]
        · intro a b hcon
          obtain ⟨a', b', hab, -, -⟩ := denoteL_imax_node (hcon ▸ hr)
          rw [hrn] at hab
          cases hab
        · intro x q hcon
          obtain ⟨a', b', hab, -, -⟩ := denoteL_imax_node (hcon ▸ hr)
          rw [hrn] at hab
          cases hab
    | none =>
      obtain ⟨nr, hnr, -, -⟩ := denoteL_some_inv hr
      rw [hrn] at hnr
      cases hnr

private theorem leqRestLI_spec {fuel : Nat} (ihc : LeqIH fuel)
    {st : EStore} {memo : EStore.LMemo} {l r : LIdx} {diff : Int}
    {la ra : Level} {ob : Option Bool} {st' : EStore}
    {memo' : EStore.LMemo}
    (hwf : st.WF) (hinv : LvlMemoInv st Level.simplify memo)
    (hl : st.denoteL l = some la) (hr : st.denoteL r = some ra)
    (hgo : leqRestLI st memo fuel l r diff = (ob, st', memo')) :
    st'.WF ∧ Ext st st' ∧ LvlMemoInv st' Level.simplify memo' ∧
      ob = Level.rest fuel la ra diff := by
  obtain ⟨nl, hln, hlc, hld⟩ := denoteL_some_inv hl
  obtain ⟨nr, hrn, hrc, hrd⟩ := denoteL_some_inv hr
  unfold leqRestLI at hgo
  rw [hln, hrn] at hgo
  cases nl with
  | zero =>
    rw [denoteLNode] at hld
    cases hld
    cases nr with
    | zero =>
      rw [denoteLNode] at hrd
      cases hrd
      dsimp only at hgo
      obtain ⟨hwf1, hext1, hinv1, hob⟩ :=
        imaxRulesLI_spec ihc hwf hinv hl hr hgo
      refine ⟨hwf1, hext1, hinv1, ?_⟩
      rw [hob]
      simp [Level.rest]
    | param bp =>
      rw [denoteLNode] at hrd
      cases hrd
      dsimp only at hgo
      cases hgo
      exact ⟨hwf, Ext.refl st, hinv, by simp [Level.rest]⟩
    | succ bsl =>
      rw [denoteLNode, Option.map_eq_some_iff] at hrd
      obtain ⟨bsx, hbsx, rfl⟩ := hrd
      dsimp only at hgo
      obtain ⟨hwf1, hext1, hinv1, hob⟩ := ihc hwf hinv hl hbsx hgo
      refine ⟨hwf1, hext1, hinv1, ?_⟩
      rw [hob]
      simp [Level.rest]
    | max bx by2 =>
      rw [denoteLNode, Option.bind_eq_some_iff] at hrd
      obtain ⟨bxx, hbxx, hrd⟩ := hrd
      rw [Option.map_eq_some_iff] at hrd
      obtain ⟨byy, hbyy, rfl⟩ := hrd
      dsimp only at hgo
      rcases h1 : leqCoreLI st memo fuel l bx diff with ⟨ob1, st1, memo1⟩
      rw [h1] at hgo
      obtain ⟨hwf1, hext1, hinv1, hob1⟩ := ihc hwf hinv hl hbxx h1
      cases ob1 with
      | none =>
        dsimp only at hgo
        cases hgo
        refine ⟨hwf1, hext1, hinv1, ?_⟩
        simp [Level.rest, ← hob1]
      | some b1 =>
        dsimp only at hgo
        rcases h2 : leqCoreLI st1 memo1 fuel l by2 diff with ⟨ob2, st2, memo2⟩
        rw [h2] at hgo
        obtain ⟨hwf2, hext2, hinv2, hob2⟩ := ihc hwf1 hinv1
          (denoteL_mono hext1 hl) (denoteL_mono hext1 hbyy) h2
        cases ob2 with
        | none =>
          dsimp only at hgo
          cases hgo
          refine ⟨hwf2, hext1.trans hext2, hinv2, ?_⟩
          simp [Level.rest, ← hob1, ← hob2]
        | some b2 =>
          dsimp only at hgo
          cases hgo
          refine ⟨hwf2, hext1.trans hext2, hinv2, ?_⟩
          simp [Level.rest, ← hob1, ← hob2]
    | imax bx by2 =>
      rw [denoteLNode, Option.bind_eq_some_iff] at hrd
      obtain ⟨bxx, hbxx, hrd⟩ := hrd
      rw [Option.map_eq_some_iff] at hrd
      obtain ⟨byy, hbyy, rfl⟩ := hrd
      dsimp only at hgo
      obtain ⟨hwf1, hext1, hinv1, hob⟩ :=
        imaxRulesLI_spec ihc hwf hinv hl hr hgo
      refine ⟨hwf1, hext1, hinv1, ?_⟩
      rw [hob]
      simp [Level.rest]
  | param ap =>
    rw [denoteLNode] at hld
    cases hld
    cases nr with
    | zero =>
      rw [denoteLNode] at hrd
      cases hrd
      dsimp only at hgo
      cases hgo
      exact ⟨hwf, Ext.refl st, hinv, by simp [Level.rest]⟩
    | param bp =>
      rw [denoteLNode] at hrd
      cases hrd
      dsimp only at hgo
      cases hgo
      exact ⟨hwf, Ext.refl st, hinv, by simp [Level.rest]⟩
    | succ bsl =>
      rw [denoteLNode, Option.map_eq_some_iff] at hrd
      obtain ⟨bsx, hbsx, rfl⟩ := hrd
      dsimp only at hgo
      obtain ⟨hwf1, hext1, hinv1, hob⟩ := ihc hwf hinv hl hbsx hgo
      refine ⟨hwf1, hext1, hinv1, ?_⟩
      rw [hob]
      simp [Level.rest]
    | max bx by2 =>
      rw [denoteLNode, Option.bind_eq_some_iff] at hrd
      obtain ⟨bxx, hbxx, hrd⟩ := hrd
      rw [Option.map_eq_some_iff] at hrd
      obtain ⟨byy, hbyy, rfl⟩ := hrd
      dsimp only at hgo
      rcases h1 : leqCoreLI st memo fuel l bx diff with ⟨ob1, st1, memo1⟩
      rw [h1] at hgo
      obtain ⟨hwf1, hext1, hinv1, hob1⟩ := ihc hwf hinv hl hbxx h1
      cases ob1 with
      | none =>
        dsimp only at hgo
        cases hgo
        refine ⟨hwf1, hext1, hinv1, ?_⟩
        simp [Level.rest, ← hob1]
      | some b1 =>
        dsimp only at hgo
        rcases h2 : leqCoreLI st1 memo1 fuel l by2 diff with ⟨ob2, st2, memo2⟩
        rw [h2] at hgo
        obtain ⟨hwf2, hext2, hinv2, hob2⟩ := ihc hwf1 hinv1
          (denoteL_mono hext1 hl) (denoteL_mono hext1 hbyy) h2
        cases ob2 with
        | none =>
          dsimp only at hgo
          cases hgo
          refine ⟨hwf2, hext1.trans hext2, hinv2, ?_⟩
          simp [Level.rest, ← hob1, ← hob2]
        | some b2 =>
          dsimp only at hgo
          cases hgo
          refine ⟨hwf2, hext1.trans hext2, hinv2, ?_⟩
          simp [Level.rest, ← hob1, ← hob2]
    | imax bx by2 =>
      rw [denoteLNode, Option.bind_eq_some_iff] at hrd
      obtain ⟨bxx, hbxx, hrd⟩ := hrd
      rw [Option.map_eq_some_iff] at hrd
      obtain ⟨byy, hbyy, rfl⟩ := hrd
      dsimp only at hgo
      obtain ⟨hwf1, hext1, hinv1, hob⟩ :=
        imaxRulesLI_spec ihc hwf hinv hl hr hgo
      refine ⟨hwf1, hext1, hinv1, ?_⟩
      rw [hob]
      simp [Level.rest]
  | succ asl =>
    rw [denoteLNode, Option.map_eq_some_iff] at hld
    obtain ⟨asx, hasx, rfl⟩ := hld
    cases nr with
    | zero =>
      rw [denoteLNode] at hrd
      cases hrd
      dsimp only at hgo
      obtain ⟨hwf1, hext1, hinv1, hob⟩ := ihc hwf hinv hasx hr hgo
      refine ⟨hwf1, hext1, hinv1, ?_⟩
      rw [hob]
      simp [Level.rest]
    | param bp =>
      rw [denoteLNode] at hrd
      cases hrd
      dsimp only at hgo
      obtain ⟨hwf1, hext1, hinv1, hob⟩ := ihc hwf hinv hasx hr hgo
      refine ⟨hwf1, hext1, hinv1, ?_⟩
      rw [hob]
      simp [Level.rest]
    | succ bsl =>
      rw [denoteLNode, Option.map_eq_some_iff] at hrd
      obtain ⟨bsx, hbsx, rfl⟩ := hrd
      dsimp only at hgo
      obtain ⟨hwf1, hext1, hinv1, hob⟩ := ihc hwf hinv hasx hr hgo
      refine ⟨hwf1, hext1, hinv1, ?_⟩
      rw [hob]
      simp [Level.rest]
    | max bx by2 =>
      rw [denoteLNode, Option.bind_eq_some_iff] at hrd
      obtain ⟨bxx, hbxx, hrd⟩ := hrd
      rw [Option.map_eq_some_iff] at hrd
      obtain ⟨byy, hbyy, rfl⟩ := hrd
      dsimp only at hgo
      obtain ⟨hwf1, hext1, hinv1, hob⟩ := ihc hwf hinv hasx hr hgo
      refine ⟨hwf1, hext1, hinv1, ?_⟩
      rw [hob]
      simp [Level.rest]
    | imax bx by2 =>
      rw [denoteLNode, Option.bind_eq_some_iff] at hrd
      obtain ⟨bxx, hbxx, hrd⟩ := hrd
      rw [Option.map_eq_some_iff] at hrd
      obtain ⟨byy, hbyy, rfl⟩ := hrd
      dsimp only at hgo
      obtain ⟨hwf1, hext1, hinv1, hob⟩ := ihc hwf hinv hasx hr hgo
      refine ⟨hwf1, hext1, hinv1, ?_⟩
      rw [hob]
      simp [Level.rest]
  | max ax ay =>
    rw [denoteLNode, Option.bind_eq_some_iff] at hld
    obtain ⟨axx, haxx, hld⟩ := hld
    rw [Option.map_eq_some_iff] at hld
    obtain ⟨ayy, hayy, rfl⟩ := hld
    cases nr with
    | zero =>
      rw [denoteLNode] at hrd
      cases hrd
      dsimp only at hgo
      rcases h1 : leqCoreLI st memo fuel ax r diff with ⟨ob1, st1, memo1⟩
      rw [h1] at hgo
      obtain ⟨hwf1, hext1, hinv1, hob1⟩ := ihc hwf hinv haxx hr h1
      cases ob1 with
      | none =>
        dsimp only at hgo
        cases hgo
        refine ⟨hwf1, hext1, hinv1, ?_⟩
        simp [Level.rest, ← hob1]
      | some b1 =>
        dsimp only at hgo
        rcases h2 : leqCoreLI st1 memo1 fuel ay r diff with ⟨ob2, st2, memo2⟩
        rw [h2] at hgo
        obtain ⟨hwf2, hext2, hinv2, hob2⟩ := ihc hwf1 hinv1
          (denoteL_mono hext1 hayy) (denoteL_mono hext1 hr) h2
        cases ob2 with
        | none =>
          dsimp only at hgo
          cases hgo
          refine ⟨hwf2, hext1.trans hext2, hinv2, ?_⟩
          simp [Level.rest, ← hob1, ← hob2]
        | some b2 =>
          dsimp only at hgo
          cases hgo
          refine ⟨hwf2, hext1.trans hext2, hinv2, ?_⟩
          simp [Level.rest, ← hob1, ← hob2]
    | param bp =>
      rw [denoteLNode] at hrd
      cases hrd
      dsimp only at hgo
      rcases h1 : leqCoreLI st memo fuel ax r diff with ⟨ob1, st1, memo1⟩
      rw [h1] at hgo
      obtain ⟨hwf1, hext1, hinv1, hob1⟩ := ihc hwf hinv haxx hr h1
      cases ob1 with
      | none =>
        dsimp only at hgo
        cases hgo
        refine ⟨hwf1, hext1, hinv1, ?_⟩
        simp [Level.rest, ← hob1]
      | some b1 =>
        dsimp only at hgo
        rcases h2 : leqCoreLI st1 memo1 fuel ay r diff with ⟨ob2, st2, memo2⟩
        rw [h2] at hgo
        obtain ⟨hwf2, hext2, hinv2, hob2⟩ := ihc hwf1 hinv1
          (denoteL_mono hext1 hayy) (denoteL_mono hext1 hr) h2
        cases ob2 with
        | none =>
          dsimp only at hgo
          cases hgo
          refine ⟨hwf2, hext1.trans hext2, hinv2, ?_⟩
          simp [Level.rest, ← hob1, ← hob2]
        | some b2 =>
          dsimp only at hgo
          cases hgo
          refine ⟨hwf2, hext1.trans hext2, hinv2, ?_⟩
          simp [Level.rest, ← hob1, ← hob2]
    | succ bsl =>
      rw [denoteLNode, Option.map_eq_some_iff] at hrd
      obtain ⟨bsx, hbsx, rfl⟩ := hrd
      dsimp only at hgo
      obtain ⟨hwf1, hext1, hinv1, hob⟩ := ihc hwf hinv hl hbsx hgo
      refine ⟨hwf1, hext1, hinv1, ?_⟩
      rw [hob]
      simp [Level.rest]
    | max bx by2 =>
      rw [denoteLNode, Option.bind_eq_some_iff] at hrd
      obtain ⟨bxx, hbxx, hrd⟩ := hrd
      rw [Option.map_eq_some_iff] at hrd
      obtain ⟨byy, hbyy, rfl⟩ := hrd
      dsimp only at hgo
      rcases h1 : leqCoreLI st memo fuel ax r diff with ⟨ob1, st1, memo1⟩
      rw [h1] at hgo
      obtain ⟨hwf1, hext1, hinv1, hob1⟩ := ihc hwf hinv haxx hr h1
      cases ob1 with
      | none =>
        dsimp only at hgo
        cases hgo
        refine ⟨hwf1, hext1, hinv1, ?_⟩
        simp [Level.rest, ← hob1]
      | some b1 =>
        dsimp only at hgo
        rcases h2 : leqCoreLI st1 memo1 fuel ay r diff with ⟨ob2, st2, memo2⟩
        rw [h2] at hgo
        obtain ⟨hwf2, hext2, hinv2, hob2⟩ := ihc hwf1 hinv1
          (denoteL_mono hext1 hayy) (denoteL_mono hext1 hr) h2
        cases ob2 with
        | none =>
          dsimp only at hgo
          cases hgo
          refine ⟨hwf2, hext1.trans hext2, hinv2, ?_⟩
          simp [Level.rest, ← hob1, ← hob2]
        | some b2 =>
          dsimp only at hgo
          cases hgo
          refine ⟨hwf2, hext1.trans hext2, hinv2, ?_⟩
          simp [Level.rest, ← hob1, ← hob2]
    | imax bx by2 =>
      rw [denoteLNode, Option.bind_eq_some_iff] at hrd
      obtain ⟨bxx, hbxx, hrd⟩ := hrd
      rw [Option.map_eq_some_iff] at hrd
      obtain ⟨byy, hbyy, rfl⟩ := hrd
      dsimp only at hgo
      rcases h1 : leqCoreLI st memo fuel ax r diff with ⟨ob1, st1, memo1⟩
      rw [h1] at hgo
      obtain ⟨hwf1, hext1, hinv1, hob1⟩ := ihc hwf hinv haxx hr h1
      cases ob1 with
      | none =>
        dsimp only at hgo
        cases hgo
        refine ⟨hwf1, hext1, hinv1, ?_⟩
        simp [Level.rest, ← hob1]
      | some b1 =>
        dsimp only at hgo
        rcases h2 : leqCoreLI st1 memo1 fuel ay r diff with ⟨ob2, st2, memo2⟩
        rw [h2] at hgo
        obtain ⟨hwf2, hext2, hinv2, hob2⟩ := ihc hwf1 hinv1
          (denoteL_mono hext1 hayy) (denoteL_mono hext1 hr) h2
        cases ob2 with
        | none =>
          dsimp only at hgo
          cases hgo
          refine ⟨hwf2, hext1.trans hext2, hinv2, ?_⟩
          simp [Level.rest, ← hob1, ← hob2]
        | some b2 =>
          dsimp only at hgo
          cases hgo
          refine ⟨hwf2, hext1.trans hext2, hinv2, ?_⟩
          simp [Level.rest, ← hob1, ← hob2]
  | imax ax ay =>
    rw [denoteLNode, Option.bind_eq_some_iff] at hld
    obtain ⟨axx, haxx, hld⟩ := hld
    rw [Option.map_eq_some_iff] at hld
    obtain ⟨ayy, hayy, rfl⟩ := hld
    cases nr with
    | zero =>
      rw [denoteLNode] at hrd
      cases hrd
      dsimp only at hgo
      obtain ⟨hwf1, hext1, hinv1, hob⟩ :=
        imaxRulesLI_spec ihc hwf hinv hl hr hgo
      refine ⟨hwf1, hext1, hinv1, ?_⟩
      rw [hob]
      simp [Level.rest]
    | param bp =>
      rw [denoteLNode] at hrd
      cases hrd
      dsimp only at hgo
      obtain ⟨hwf1, hext1, hinv1, hob⟩ :=
        imaxRulesLI_spec ihc hwf hinv hl hr hgo
      refine ⟨hwf1, hext1, hinv1, ?_⟩
      rw [hob]
      simp [Level.rest]
    | succ bsl =>
      rw [denoteLNode, Option.map_eq_some_iff] at hrd
      obtain ⟨bsx, hbsx, rfl⟩ := hrd
      dsimp only at hgo
      obtain ⟨hwf1, hext1, hinv1, hob⟩ := ihc hwf hinv hl hbsx hgo
      refine ⟨hwf1, hext1, hinv1, ?_⟩
      rw [hob]
      simp [Level.rest]
    | max bx by2 =>
      rw [denoteLNode, Option.bind_eq_some_iff] at hrd
      obtain ⟨bxx, hbxx, hrd⟩ := hrd
      rw [Option.map_eq_some_iff] at hrd
      obtain ⟨byy, hbyy, rfl⟩ := hrd
      dsimp only at hgo
      obtain ⟨hwf1, hext1, hinv1, hob⟩ :=
        imaxRulesLI_spec ihc hwf hinv hl hr hgo
      refine ⟨hwf1, hext1, hinv1, ?_⟩
      rw [hob]
      simp [Level.rest]
    | imax bx by2 =>
      rw [denoteLNode, Option.bind_eq_some_iff] at hrd
      obtain ⟨bxx, hbxx, hrd⟩ := hrd
      rw [Option.map_eq_some_iff] at hrd
      obtain ⟨byy, hbyy, rfl⟩ := hrd
      dsimp only at hgo
      by_cases hids : (ax = bx && ay = by2 && decide (diff ≥ 0)) = true
      · rw [if_pos hids] at hgo
        cases hgo
        refine ⟨hwf, Ext.refl st, hinv, ?_⟩
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hids
        obtain ⟨⟨rfl, rfl⟩, hdge⟩ := hids
        have e1 : axx = bxx := by
          rw [haxx] at hbxx; exact Option.some.inj hbxx
        have e2 : ayy = byy := by
          rw [hayy] at hbyy; exact Option.some.inj hbyy
        subst e1; subst e2
        simp [Level.rest, hdge]
      · rw [if_neg hids] at hgo
        obtain ⟨hwf1, hext1, hinv1, hob⟩ :=
          imaxRulesLI_spec ihc hwf hinv hl hr hgo
        refine ⟨hwf1, hext1, hinv1, ?_⟩
        rw [hob]
        have hneq : ¬ (axx = bxx ∧ ayy = byy ∧ diff ≥ 0) := by
          rintro ⟨rfl, rfl, hdge⟩
          apply hids
          have e1 : ax = bx := denoteL_inj hwf haxx hbxx
          have e2 : ay = by2 := denoteL_inj hwf hayy hbyy
          subst e1; subst e2
          simp [hdge]
        simp only [Level.rest]
        rw [if_neg (by
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
          rintro ⟨⟨rfl, rfl⟩, hdge⟩
          exact hneq ⟨rfl, rfl, hdge⟩)]

/-- `leqCoreLI` is faithful at every fuel. -/
theorem leqCoreLI_spec : ∀ fuel, LeqIH fuel := by
  intro fuel
  induction fuel with
  | zero =>
    intro st memo l r diff la ra ob st' memo' hwf hinv hl hr hgo
    unfold leqCoreLI at hgo
    cases hgo
    exact ⟨hwf, Ext.refl st, hinv, by simp [Level.leqCore]⟩
  | succ fuel ih =>
    intro st memo l r diff la ra ob st' memo' hwf hinv hl hr hgo
    unfold leqCoreLI at hgo
    have hzl : (st.lnodes[l]? = some LNode.zero) ↔ (la = .zero) := by
      constructor
      · intro hn
        have := denoteL_head hl hn
        simpa [denoteLNode] using this.symm
      · rintro rfl
        exact denoteL_zero_node hl
    have hzr : (st.lnodes[r]? = some LNode.zero) ↔ (ra = .zero) := by
      constructor
      · intro hn
        have := denoteL_head hr hn
        simpa [denoteLNode] using this.symm
      · rintro rfl
        exact denoteL_zero_node hr
    by_cases h1 : la = .zero ∧ diff ≥ 0
    · rw [if_pos ⟨hzl.mpr h1.1, h1.2⟩] at hgo
      cases hgo
      refine ⟨hwf, Ext.refl st, hinv, ?_⟩
      rw [show Level.leqCore (fuel + 1) la ra diff =
        (if la = .zero ∧ diff ≥ 0 then some true
         else if ra = .zero ∧ diff < 0 then some false
         else Level.rest fuel la ra diff) from by
          simp [Level.leqCore]]
      rw [if_pos h1]
    · rw [if_neg (fun hc => h1 ⟨hzl.mp hc.1, hc.2⟩)] at hgo
      by_cases h2 : ra = .zero ∧ diff < 0
      · rw [if_pos ⟨hzr.mpr h2.1, h2.2⟩] at hgo
        cases hgo
        refine ⟨hwf, Ext.refl st, hinv, ?_⟩
        rw [show Level.leqCore (fuel + 1) la ra diff =
          (if la = .zero ∧ diff ≥ 0 then some true
           else if ra = .zero ∧ diff < 0 then some false
           else Level.rest fuel la ra diff) from by
            simp [Level.leqCore]]
        rw [if_neg h1, if_pos h2]
      · rw [if_neg (fun hc => h2 ⟨hzr.mp hc.1, hc.2⟩)] at hgo
        obtain ⟨hwf1, hext1, hinv1, hob⟩ :=
          leqRestLI_spec ih hwf hinv hl hr hgo
        refine ⟨hwf1, hext1, hinv1, ?_⟩
        rw [hob]
        rw [show Level.leqCore (fuel + 1) la ra diff =
          (if la = .zero ∧ diff ≥ 0 then some true
           else if ra = .zero ∧ diff < 0 then some false
           else Level.rest fuel la ra diff) from by
            simp [Level.leqCore]]
        rw [if_neg h1, if_neg h2]

/-- `leqLI` computes `Level.leq` under the denotation. -/
theorem leqLI_spec {st : EStore} {memo : EStore.LMemo} {l r : LIdx}
    {la ra : Level} {ob : Option Bool} {st' : EStore} {memo' : EStore.LMemo}
    (hwf : st.WF) (hinv : LvlMemoInv st Level.simplify memo)
    (hl : st.denoteL l = some la) (hr : st.denoteL r = some ra)
    (hgo : leqLI st memo l r = (ob, st', memo')) :
    st'.WF ∧ Ext st st' ∧ LvlMemoInv st' Level.simplify memo' ∧
      ob = Level.leq la ra := by
  unfold leqLI at hgo
  rcases h1 : simplifyLIGo st memo l with ⟨ls, st1, memo1⟩
  rw [h1] at hgo
  dsimp only at hgo
  obtain ⟨hwf1, hext1, hinv1, hden1⟩ := simplifyLIGo_spec l hwf hinv h1
  rcases h2 : simplifyLIGo st1 memo1 r with ⟨rs, st2, memo2⟩
  rw [h2] at hgo
  dsimp only at hgo
  obtain ⟨hwf2, hext2, hinv2, hden2⟩ := simplifyLIGo_spec r hwf1 hinv1 h2
  obtain ⟨hwf3, hext3, hinv3, hob⟩ := leqCoreLI_spec Level.defaultFuel
    hwf2 hinv2
    (denoteL_mono hext2 (hden1 la hl))
    (hden2 ra (denoteL_mono hext1 hr)) hgo
  exact ⟨hwf3, (hext1.trans hext2).trans hext3, hinv3, hob⟩

/-- `isEquivLI` computes `Level.isEquiv` under the denotation. -/
theorem isEquivLI_spec {st : EStore} {memo : EStore.LMemo} {l r : LIdx}
    {la ra : Level} {ob : Option Bool} {st' : EStore} {memo' : EStore.LMemo}
    (hwf : st.WF) (hinv : LvlMemoInv st Level.simplify memo)
    (hl : st.denoteL l = some la) (hr : st.denoteL r = some ra)
    (hgo : isEquivLI st memo l r = (ob, st', memo')) :
    st'.WF ∧ Ext st st' ∧ LvlMemoInv st' Level.simplify memo' ∧
      ob = Level.isEquiv la ra := by
  unfold isEquivLI at hgo
  rcases h1 : leqLI st memo l r with ⟨ob1, st1, memo1⟩
  rw [h1] at hgo
  obtain ⟨hwf1, hext1, hinv1, hob1⟩ := leqLI_spec hwf hinv hl hr h1
  cases ob1 with
  | none =>
    dsimp only at hgo
    cases hgo
    refine ⟨hwf1, hext1, hinv1, ?_⟩
    rw [Level.isEquiv, ← hob1]
    rfl
  | some b1 =>
    dsimp only at hgo
    rcases h2 : leqLI st1 memo1 r l with ⟨ob2, st2, memo2⟩
    rw [h2] at hgo
    obtain ⟨hwf2, hext2, hinv2, hob2⟩ := leqLI_spec hwf1 hinv1
      (denoteL_mono hext1 hr) (denoteL_mono hext1 hl) h2
    cases ob2 with
    | none =>
      dsimp only at hgo
      cases hgo
      refine ⟨hwf2, hext1.trans hext2, hinv2, ?_⟩
      rw [Level.isEquiv, ← hob1, ← hob2]
      rfl
    | some b2 =>
      dsimp only at hgo
      cases hgo
      refine ⟨hwf2, hext1.trans hext2, hinv2, ?_⟩
      rw [Level.isEquiv, ← hob1, ← hob2]
      rfl

/-- `isEquivListLI` computes `Level.isEquivList` under the denotation. -/
theorem isEquivListLI_spec :
    ∀ {ls rs : List LIdx} {st : EStore} {memo : EStore.LMemo}
      {las ras : List Level} {ob : Option Bool} {st' : EStore}
      {memo' : EStore.LMemo},
      st.WF → LvlMemoInv st Level.simplify memo →
      denoteLList st.denoteL ls = some las →
      denoteLList st.denoteL rs = some ras →
      isEquivListLI st memo ls rs = (ob, st', memo') →
      st'.WF ∧ Ext st st' ∧ LvlMemoInv st' Level.simplify memo' ∧
        ob = Level.isEquivList las ras := by
  intro ls
  induction ls with
  | nil =>
    intro rs st memo las ras ob st' memo' hwf hinv hls hrs hgo
    cases hls
    cases rs with
    | nil =>
      cases hrs
      cases hgo
      exact ⟨hwf, Ext.refl st, hinv, rfl⟩
    | cons r rs' =>
      simp only [denoteLList, Option.bind_eq_some_iff,
        Option.map_eq_some_iff] at hrs
      obtain ⟨x, -, xs, -, rfl⟩ := hrs
      cases hgo
      exact ⟨hwf, Ext.refl st, hinv, rfl⟩
  | cons l ls' ih =>
    intro rs st memo las ras ob st' memo' hwf hinv hls hrs hgo
    simp only [denoteLList, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at hls
    obtain ⟨x, hx, xs, hxs, rfl⟩ := hls
    cases rs with
    | nil =>
      cases hrs
      cases hgo
      exact ⟨hwf, Ext.refl st, hinv, rfl⟩
    | cons r rs' =>
      simp only [denoteLList, Option.bind_eq_some_iff,
        Option.map_eq_some_iff] at hrs
      obtain ⟨y, hy, ys, hys, rfl⟩ := hrs
      unfold isEquivListLI at hgo
      rcases h1 : isEquivLI st memo l r with ⟨ob1, st1, memo1⟩
      rw [h1] at hgo
      obtain ⟨hwf1, hext1, hinv1, hob1⟩ := isEquivLI_spec hwf hinv hx hy h1
      cases ob1 with
      | none =>
        dsimp only at hgo
        cases hgo
        refine ⟨hwf1, hext1, hinv1, ?_⟩
        rw [show Level.isEquivList (x :: xs) (y :: ys)
          = (do return (← Level.isEquiv x y)
              && (← Level.isEquivList xs ys) : Option Bool) from rfl,
          ← hob1]
        rfl
      | some b1 =>
        dsimp only at hgo
        rcases h2 : isEquivListLI st1 memo1 ls' rs' with ⟨ob2, st2, memo2⟩
        rw [h2] at hgo
        obtain ⟨hwf2, hext2, hinv2, hob2⟩ := ih hwf1 hinv1
          (denoteLList_mono hext1 hxs) (denoteLList_mono hext1 hys) h2
        cases ob2 with
        | none =>
          dsimp only at hgo
          cases hgo
          refine ⟨hwf2, hext1.trans hext2, hinv2, ?_⟩
          rw [show Level.isEquivList (x :: xs) (y :: ys)
            = (do return (← Level.isEquiv x y)
                && (← Level.isEquivList xs ys) : Option Bool) from rfl,
            ← hob1, ← hob2]
          rfl
        | some b2 =>
          dsimp only at hgo
          cases hgo
          refine ⟨hwf2, hext1.trans hext2, hinv2, ?_⟩
          rw [show Level.isEquivList (x :: xs) (y :: ys)
            = (do return (← Level.isEquiv x y)
                && (← Level.isEquivList xs ys) : Option Bool) from rfl,
            ← hob1, ← hob2]
          rfl

end Setlec
