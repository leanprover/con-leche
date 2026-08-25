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

theorem combiningLI_spec {st : EStore} (hwf : st.TWF) :
    ∀ {a : LIdx} {b : LIdx} {la lb : Level} {r : LIdx} {st' : EStore},
      st.denoteL a = some la → st.denoteL b = some lb →
      st.combiningLI a b = (r, st') →
      st'.TWF ∧ Ext st st' ∧ st'.denoteL r = some (Level.combining la lb) := by
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
        st₀.TWF ∧ Ext st st₀ ∧ st₀.denoteL r₀ = some (.max la lb) := by
      intro r₀ st₀ hI
      obtain ⟨hwf₁, hext₁, hden₁⟩ := internL_stepT (n := .max a b) hwf
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
        obtain ⟨hwf₂, hext₂, hden₂⟩ := internL_stepT (n := .succ c) hwf₁
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
    (hwf : st.TWF)
    (hls : st.denoteL ls = some xls) (hrs : st.denoteL rs = some xrs)
    (hgo : simplifyImax st memo ls rs = (ri, st', memo')) :
    st'.TWF ∧ Ext st st' ∧ memo' = memo ∧
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
      obtain ⟨hwf₁, hext₁, hden₁⟩ := internL_stepT (n := .imax ls rs) hwf
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
      obtain ⟨hwf₁, hext₁, hden₁⟩ := internL_stepT (n := .imax ls rs) hwf
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
      obtain ⟨hwf₁, hext₁, hden₁⟩ := internL_stepT (n := .imax ls rs) hwf
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
      st.TWF → LvlMemoInv st Level.simplify memo →
      simplifyLIGo st memo u = (r, st', memo') →
      st'.TWF ∧ Ext st st' ∧ LvlMemoInv st' Level.simplify memo' ∧
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
            obtain ⟨hwf₂, hext₂, hden₂⟩ := internL_stepT (n := .succ l') hwf₁
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
                st₀.TWF ∧ Ext st st₀ ∧
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
                st₂.TWF ∧ Ext st st₂ ∧
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

theorem isNonZeroLIGo_spec {st : EStore} (hwf : st.TWF) :
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
      st.TWF → denoteLList st.denoteL us = some lus →
      st.internLevelSubst ks us l = (r, st') →
      st'.TWF ∧ Ext st st' ∧
        st'.denoteL r = some (Level.subst ks lus l) := by
  intro l
  induction l with
  | zero =>
    intro st r st' hwf hus hgo
    unfold internLevelSubst at hgo
    obtain ⟨hwf₁, hext₁, hden₁⟩ := internL_stepT (n := .zero) hwf
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
      obtain ⟨hwf₁, hext₁, hden₁⟩ := internL_stepT (n := .param n) hwf
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
    obtain ⟨hwf₂, hext₂, hden₂⟩ := internL_stepT (n := .succ x') hwf₁
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
    obtain ⟨hwf₃, hext₃, hden₃⟩ := internL_stepT (n := .max x' y') hwf₂
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
    obtain ⟨hwf₃, hext₃, hden₃⟩ := internL_stepT (n := .imax x' y') hwf₂
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
      st.TWF → denoteLList st.denoteL us = some lus →
      st.internLevelSubsts ks us ls = (rs, st') →
      st'.TWF ∧ Ext st st' ∧
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

/-- `substLI` (fresh-memo wrapper) commutes with the denotation. -/
theorem substLI_spec {st : EStore} {ks : List Name} {us : List LIdx}
    {lus : List Level} {u : LIdx} {la : Level} {r : LIdx} {st' : EStore}
    (hwf : st.TWF) (hus : denoteLList st.denoteL us = some lus)
    (hl : st.denoteL u = some la) (hgo : st.substLI ks us u = (r, st')) :
    st'.TWF ∧ Ext st st' ∧ st'.denoteL r = some (Level.subst ks lus la) := by
  unfold substLI at hgo
  rcases h₁ : substLIGo ks us st {} u with ⟨r₁, st₁, memo₁⟩
  rw [h₁] at hgo
  cases hgo
  obtain ⟨hwf₁, hext₁, -, hden₁⟩ := substLIGo_spec u hwf hus LvlMemoInv.empty h₁
  exact ⟨hwf₁, hext₁, hden₁ la hl⟩

end Setlec
