import Setlec.Verify.ILevel
import Setlec.Kernel.CheckerS

/-!
# Parse-time interning: walker specs and store validation (task #78)

* Specs for the DAG-memoized syntactic walkers the parsed-index drivers
  run on raw and annotated input — `allLevelParamsDefinedI` (with its
  level-side walker) and the indexed `constsResolveFI` — against their
  `Expr`-level counterparts under the structural denotation.
* `wfB_wf` — the checker's one-time validation of the parse-produced
  store establishes canonicity (`EStore.WF`), from which every interned
  operation's faithfulness flows.
* The denotation of parsed declarations (`denoteCVP`/`denoteDeclP`) and
  its totality on in-range indices — the identification of a `DeclP`
  with the spec `Declaration` the consistency statements quantify over.
-/

namespace Setlec

open EStore Expr

/-! ## The level-parameter walkers -/

/-- The level-side walk agrees with `Level.allParamsDefined` (memo
invariant: `LvlQMemoInv` at the parameter predicate). -/
theorem lparamsDefinedLIGo_spec {st : EStore} (hwf : st.WF)
    {params : List Name} :
    ∀ (u : LIdx) {memo : Std.HashMap LIdx Bool} {b : Bool}
      {memo' : Std.HashMap LIdx Bool},
      LvlQMemoInv st (Level.allParamsDefined params) memo →
      lparamsDefinedLIGo st params memo u = (b, memo') →
      LvlQMemoInv st (Level.allParamsDefined params) memo' ∧
        ∀ x, st.denoteL u = some x → x.allParamsDefined params = b := by
  intro u
  induction u using Nat.strongRecOn with
  | _ u ih =>
    intro memo b memo' hinv hgo
    unfold lparamsDefinedLIGo at hgo
    split at hgo
    · -- param-free: trivially defined (task #87)
      rename_i hnp
      cases hgo
      refine ⟨hinv, ?_⟩
      intro x hx
      exact Level.allParamsDefined_of_not_hasParam
        (hwf.lhasParamD_false hx hnp)
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
        have husz : u < st.lnodes.size :=
          (Array.getElem?_eq_some_iff.mp hn).1
        have hcl := hwf.lchildren_lt u n hn
        have hde := denoteL_node hn hcl
        cases n with
        | zero =>
          dsimp only at hgo
          cases hgo
          have hcond : ∀ x, st.denoteL u = some x →
              x.allParamsDefined params = true := by
            intro x hxx
            rw [hde] at hxx
            cases hxx
            rfl
          exact ⟨hinv.insert husz hcond, hcond⟩
        | param p =>
          dsimp only at hgo
          cases hgo
          have hcond : ∀ x, st.denoteL u = some x →
              x.allParamsDefined params = params.contains p := by
            intro x hxx
            rw [hde] at hxx
            cases hxx
            rfl
          exact ⟨hinv.insert husz hcond, hcond⟩
        | succ l =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd (hcl l (by simp [LNode.children])) hguard
          case isTrue hguard =>
            obtain ⟨xl, hxl⟩ := denoteL_total hwf l
              (Nat.lt_trans hguard husz)
            have hx : st.denoteL u = some (.succ xl) := by
              rw [hde, denoteLNode, hxl]; rfl
            rcases h₁ : lparamsDefinedLIGo st params memo l with ⟨rl, memo₁⟩
            rw [h₁] at hgo
            cases hgo
            obtain ⟨hinv₁, hden₁⟩ := ih l hguard hinv h₁
            have hcond : ∀ x, st.denoteL u = some x →
                x.allParamsDefined params = rl := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              simpa [Level.allParamsDefined] using hden₁ xl hxl
            exact ⟨hinv₁.insert husz hcond, hcond⟩
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
            rcases h₁ : lparamsDefinedLIGo st params memo a with ⟨ra, memo₁⟩
            rw [h₁] at hgo
            obtain ⟨hinv₁, hden₁⟩ := ih a hguard.1 hinv h₁
            have hra := hden₁ xa hxa
            cases hb : ra with
            | true =>
              rw [hb] at hgo
              dsimp only at hgo
              rcases h₂ : lparamsDefinedLIGo st params memo₁ b'
                with ⟨rb, memo₂⟩
              rw [h₂] at hgo
              cases hgo
              obtain ⟨hinv₂, hden₂⟩ := ih b' hguard.2 hinv₁ h₂
              have hcond : ∀ x, st.denoteL u = some x →
                  x.allParamsDefined params = rb := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                simp only [Level.allParamsDefined]
                rw [hra, hb, ← hden₂ xb hxb, Bool.true_and]
              exact ⟨hinv₂.insert husz hcond, hcond⟩
            | false =>
              rw [hb] at hgo
              dsimp only at hgo
              cases hgo
              have hcond : ∀ x, st.denoteL u = some x →
                  x.allParamsDefined params = false := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                simp only [Level.allParamsDefined]
                rw [hra, hb, Bool.false_and]
              exact ⟨hinv₁.insert husz hcond, hcond⟩
        | imax a b' =>
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
            have hx : st.denoteL u = some (.imax xa xb) := by
              rw [hde, denoteLNode, hxa, hxb]; rfl
            rcases h₁ : lparamsDefinedLIGo st params memo a with ⟨ra, memo₁⟩
            rw [h₁] at hgo
            obtain ⟨hinv₁, hden₁⟩ := ih a hguard.1 hinv h₁
            have hra := hden₁ xa hxa
            cases hb : ra with
            | true =>
              rw [hb] at hgo
              dsimp only at hgo
              rcases h₂ : lparamsDefinedLIGo st params memo₁ b'
                with ⟨rb, memo₂⟩
              rw [h₂] at hgo
              cases hgo
              obtain ⟨hinv₂, hden₂⟩ := ih b' hguard.2 hinv₁ h₂
              have hcond : ∀ x, st.denoteL u = some x →
                  x.allParamsDefined params = rb := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                simp only [Level.allParamsDefined]
                rw [hra, hb, ← hden₂ xb hxb, Bool.true_and]
              exact ⟨hinv₂.insert husz hcond, hcond⟩
            | false =>
              rw [hb] at hgo
              dsimp only at hgo
              cases hgo
              have hcond : ∀ x, st.denoteL u = some x →
                  x.allParamsDefined params = false := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                simp only [Level.allParamsDefined]
                rw [hra, hb, Bool.false_and]
              exact ⟨hinv₁.insert husz hcond, hcond⟩

/-- The list version (a `const` node's levels). -/
theorem lparamsDefinedListLI_spec {st : EStore} (hwf : st.WF)
    {params : List Name} :
    ∀ (us : List LIdx) {memo : Std.HashMap LIdx Bool} {b : Bool}
      {memo' : Std.HashMap LIdx Bool} {ls : List Level},
      LvlQMemoInv st (Level.allParamsDefined params) memo →
      lparamsDefinedListLI st params memo us = (b, memo') →
      denoteLList st.denoteL us = some ls →
      LvlQMemoInv st (Level.allParamsDefined params) memo' ∧
        ls.all (Level.allParamsDefined params) = b
  | [], memo, b, memo', ls, hinv, hgo, hls => by
    cases hgo
    cases hls
    exact ⟨hinv, rfl⟩
  | u :: us, memo, b, memo', ls, hinv, hgo, hls => by
    unfold lparamsDefinedListLI at hgo
    rcases h₁ : lparamsDefinedLIGo st params memo u with ⟨r, memo₁⟩
    rw [h₁] at hgo
    obtain ⟨hinv₁, hden₁⟩ := lparamsDefinedLIGo_spec hwf u hinv h₁
    simp only [denoteLList] at hls
    cases hu : st.denoteL u with
    | none => rw [hu] at hls; cases hls
    | some l =>
      rw [hu] at hls
      dsimp only [Option.bind] at hls
      cases hrest : denoteLList st.denoteL us with
      | none => rw [hrest] at hls; cases hls
      | some ls' =>
        rw [hrest] at hls
        injection hls with hls
        subst hls
        have hr := hden₁ l hu
        cases hrb : r with
        | true =>
          rw [hrb] at hgo
          dsimp only at hgo
          obtain ⟨hinv₂, hall⟩ :=
            lparamsDefinedListLI_spec hwf us hinv₁ hgo hrest
          refine ⟨hinv₂, ?_⟩
          simp only [List.all_cons]
          rw [hr, hrb, hall, Bool.true_and]
        | false =>
          rw [hrb] at hgo
          dsimp only at hgo
          cases hgo
          refine ⟨hinv₁, ?_⟩
          simp only [List.all_cons]
          rw [hr, hrb, Bool.false_and]

/-! ## The expression walker: `allLevelParamsDefinedI` -/

/-- Combined memo invariant of the expression walk (level side plus
expression side). -/
def LPDInv (st : EStore) (params : List Name)
    (lmemo : Std.HashMap LIdx Bool) (memo : Std.HashMap EIdx Bool) :
    Prop :=
  LvlQMemoInv st (Level.allParamsDefined params) lmemo ∧
  QMemo0Inv st (Expr.allLevelParamsDefined params) memo

theorem allLevelParamsDefinedIGo_spec {st : EStore} (hwf : st.WF)
    {params : List Name} :
    ∀ (e : EIdx) {lmemo : Std.HashMap LIdx Bool}
      {memo : Std.HashMap EIdx Bool} {b : Bool}
      {lmemo' : Std.HashMap LIdx Bool} {memo' : Std.HashMap EIdx Bool},
      LPDInv st params lmemo memo →
      allLevelParamsDefinedIGo st params lmemo memo e =
        (b, lmemo', memo') →
      LPDInv st params lmemo' memo' ∧
        ∀ x, st.denote e = some x →
          x.allLevelParamsDefined params = b := by
  intro e
  induction e using Nat.strongRecOn with
  | _ e ih =>
    intro lmemo memo b lmemo' memo' hinv hgo
    unfold allLevelParamsDefinedIGo at hgo
    split at hgo
    · -- level-param-free: trivially defined (task #87)
      rename_i hnp
      cases hgo
      refine ⟨hinv, ?_⟩
      intro x hx
      exact Expr.allLevelParamsDefined_of_not_hasLevelParam
        (hwf.ehasParamD_false hx hnp)
    split at hgo
    · rename_i hhit
      cases hgo
      refine ⟨hinv, ?_⟩
      intro x hx
      exact (hinv.2 _ _ hhit x hx).symm
    · split at hgo
      · rename_i hnone
        cases hgo
        refine ⟨hinv, ?_⟩
        intro x hx
        obtain ⟨n, hn, -, -⟩ := denote_some_inv hx
        rw [hn] at hnone
        cases hnone
      · rename_i n hn
        have hesz : e < st.nodes.size :=
          (Array.getElem?_eq_some_iff.mp hn).1
        have hcl := hwf.children_lt e n hn
        have hlv := hwf.levels_lt e n hn
        have hde := denote_node hn hcl
        cases n with
        | bvar i =>
          dsimp only at hgo
          cases hgo
          have hcond : ∀ x, st.denote e = some x →
              x.allLevelParamsDefined params = true := by
            intro x hxx
            rw [hde] at hxx
            cases hxx
            rfl
          exact ⟨⟨hinv.1, hinv.2.insert (fun x hx => (hcond x hx).symm)⟩,
            hcond⟩
        | lit l =>
          dsimp only at hgo
          cases hgo
          have hcond : ∀ x, st.denote e = some x →
              x.allLevelParamsDefined params = true := by
            intro x hxx
            rw [hde] at hxx
            cases hxx
            rfl
          exact ⟨⟨hinv.1, hinv.2.insert (fun x hx => (hcond x hx).symm)⟩,
            hcond⟩
        | sort u =>
          dsimp only at hgo
          rcases h₁ : lparamsDefinedLIGo st params lmemo u with ⟨r, lmemo₁⟩
          rw [h₁] at hgo
          cases hgo
          obtain ⟨hinv₁, hden₁⟩ := lparamsDefinedLIGo_spec hwf u hinv.1 h₁
          obtain ⟨xu, hxu⟩ := denoteL_total hwf u
            (hlv u (by simp [ENode.levels]))
          have hx : st.denote e = some (.sort xu) := by
            rw [hde, denoteNode, hxu]; rfl
          have hcond : ∀ x, st.denote e = some x →
              x.allLevelParamsDefined params = r := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simpa [Expr.allLevelParamsDefined] using hden₁ xu hxu
          exact ⟨⟨hinv₁, hinv.2.insert (fun x hx => (hcond x hx).symm)⟩,
            hcond⟩
        | const nmᵢ us =>
          dsimp only at hgo
          rcases h₁ : lparamsDefinedListLI st params lmemo us with ⟨r, lmemo₁⟩
          rw [h₁] at hgo
          cases hgo
          obtain ⟨ls, hls⟩ := denoteLList_total hwf us
            (fun u hu => hlv u (by simp [ENode.levels, hu]))
          obtain ⟨hinv₁, hall⟩ :=
            lparamsDefinedListLI_spec hwf us hinv.1 h₁ hls
          obtain ⟨nm, hnmDen⟩ := denoteN_total hwf nmᵢ
            (hwf.names_lt e _ hn nmᵢ (by simp [ENode.names]))
          have hx : st.denote e = some (.const nm ls) := by
            rw [hde, denoteNode, hls, hnmDen]; rfl
          have hcond : ∀ x, st.denote e = some x →
              x.allLevelParamsDefined params = r := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simpa [Expr.allLevelParamsDefined] using hall
          exact ⟨⟨hinv₁, hinv.2.insert (fun x hx => (hcond x hx).symm)⟩,
            hcond⟩
        | fvar idx nmᵢ ty =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd (hcl ty (by simp [ENode.children])) hguard
          case isTrue hguard =>
            obtain ⟨xt, hxt⟩ := denote_total hwf ty
              (Nat.lt_trans hguard hesz)
            obtain ⟨nm, hnmDen⟩ := denoteN_total hwf nmᵢ
              (hwf.names_lt e _ hn nmᵢ (by simp [ENode.names]))
            have hx : st.denote e = some (.fvar idx nm xt) := by
              rw [hde, denoteNode, hxt, hnmDen]; rfl
            rcases h₁ : allLevelParamsDefinedIGo st params lmemo memo ty
              with ⟨rt, lmemo₁, memo₁⟩
            rw [h₁] at hgo
            cases hgo
            obtain ⟨hinv₁, hden₁⟩ := ih ty hguard hinv h₁
            have hcond : ∀ x, st.denote e = some x →
                x.allLevelParamsDefined params = rt := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              simpa [Expr.allLevelParamsDefined] using hden₁ xt hxt
            exact ⟨⟨hinv₁.1,
              hinv₁.2.insert (fun x hx => (hcond x hx).symm)⟩, hcond⟩
        | app f a =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl f (by simp [ENode.children]),
              hcl a (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            obtain ⟨xf, hxf⟩ := denote_total hwf f
              (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xa, hxa⟩ := denote_total hwf a
              (Nat.lt_trans hguard.2 hesz)
            have hx : st.denote e = some (.app xf xa) := by
              rw [hde, denoteNode, hxf, hxa]; rfl
            rcases h₁ : allLevelParamsDefinedIGo st params lmemo memo f
              with ⟨rf, lmemo₁, memo₁⟩
            rw [h₁] at hgo
            obtain ⟨hinv₁, hden₁⟩ := ih f hguard.1 hinv h₁
            have hrf := hden₁ xf hxf
            cases hb : rf with
            | true =>
              rw [hb] at hgo
              dsimp only at hgo
              rcases h₂ : allLevelParamsDefinedIGo st params lmemo₁ memo₁ a
                with ⟨ra, lmemo₂, memo₂⟩
              rw [h₂] at hgo
              cases hgo
              obtain ⟨hinv₂, hden₂⟩ := ih a hguard.2 hinv₁ h₂
              have hcond : ∀ x, st.denote e = some x →
                  x.allLevelParamsDefined params = ra := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                simp only [Expr.allLevelParamsDefined]
                rw [hrf, hb, ← hden₂ xa hxa, Bool.true_and]
              exact ⟨⟨hinv₂.1,
                hinv₂.2.insert (fun x hx => (hcond x hx).symm)⟩, hcond⟩
            | false =>
              rw [hb] at hgo
              dsimp only at hgo
              cases hgo
              have hcond : ∀ x, st.denote e = some x →
                  x.allLevelParamsDefined params = false := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                simp only [Expr.allLevelParamsDefined]
                rw [hrf, hb, Bool.false_and]
              exact ⟨⟨hinv₁.1,
                hinv₁.2.insert (fun x hx => (hcond x hx).symm)⟩, hcond⟩
        | letE nmᵢ ty val body =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl val (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            obtain ⟨xt, hxt⟩ := denote_total hwf ty
              (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xv, hxv⟩ := denote_total hwf val
              (Nat.lt_trans hguard.2.1 hesz)
            obtain ⟨xb, hxb⟩ := denote_total hwf body
              (Nat.lt_trans hguard.2.2 hesz)
            obtain ⟨nm, hnmDen⟩ := denoteN_total hwf nmᵢ
              (hwf.names_lt e _ hn nmᵢ (by simp [ENode.names]))
            have hx : st.denote e = some (.letE nm xt xv xb) := by
              rw [hde, denoteNode, hxt, hxv, hxb, hnmDen]; rfl
            rcases h₁ : allLevelParamsDefinedIGo st params lmemo memo ty
              with ⟨rt, lmemo₁, memo₁⟩
            rw [h₁] at hgo
            obtain ⟨hinv₁, hden₁⟩ := ih ty hguard.1 hinv h₁
            have hrt := hden₁ xt hxt
            cases hbt : rt with
            | false =>
              rw [hbt] at hgo
              dsimp only at hgo
              cases hgo
              have hcond : ∀ x, st.denote e = some x →
                  x.allLevelParamsDefined params = false := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                simp only [Expr.allLevelParamsDefined]
                rw [hrt, hbt]
                simp
              exact ⟨⟨hinv₁.1,
                hinv₁.2.insert (fun x hx => (hcond x hx).symm)⟩, hcond⟩
            | true =>
              rw [hbt] at hgo
              dsimp only at hgo
              rcases h₂ : allLevelParamsDefinedIGo st params lmemo₁ memo₁ val
                with ⟨rv, lmemo₂, memo₂⟩
              rw [h₂] at hgo
              obtain ⟨hinv₂, hden₂⟩ := ih val hguard.2.1 hinv₁ h₂
              have hrv := hden₂ xv hxv
              cases hbv : rv with
              | false =>
                rw [hbv] at hgo
                dsimp only at hgo
                cases hgo
                have hcond : ∀ x, st.denote e = some x →
                    x.allLevelParamsDefined params = false := by
                  intro x hxx
                  rw [hx] at hxx; cases hxx
                  simp only [Expr.allLevelParamsDefined]
                  rw [hrt, hbt, hrv, hbv]
                  simp
                exact ⟨⟨hinv₂.1,
                  hinv₂.2.insert (fun x hx => (hcond x hx).symm)⟩, hcond⟩
              | true =>
                rw [hbv] at hgo
                dsimp only at hgo
                rcases h₃ : allLevelParamsDefinedIGo st params lmemo₂ memo₂
                  body with ⟨rb, lmemo₃, memo₃⟩
                rw [h₃] at hgo
                cases hgo
                obtain ⟨hinv₃, hden₃⟩ := ih body hguard.2.2 hinv₂ h₃
                have hcond : ∀ x, st.denote e = some x →
                    x.allLevelParamsDefined params = rb := by
                  intro x hxx
                  rw [hx] at hxx; cases hxx
                  simp only [Expr.allLevelParamsDefined]
                  rw [hrt, hbt, hrv, hbv, ← hden₃ xb hxb]
                  simp
                exact ⟨⟨hinv₃.1,
                  hinv₃.2.insert (fun x hx => (hcond x hx).symm)⟩, hcond⟩
        | proj sNᵢ j sub =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd (hcl sub (by simp [ENode.children])) hguard
          case isTrue hguard =>
            obtain ⟨xs, hxs⟩ := denote_total hwf sub
              (Nat.lt_trans hguard hesz)
            obtain ⟨sN, hnmDen⟩ := denoteN_total hwf sNᵢ
              (hwf.names_lt e _ hn sNᵢ (by simp [ENode.names]))
            have hx : st.denote e = some (.proj sN j xs) := by
              rw [hde, denoteNode, hxs, hnmDen]; rfl
            rcases h₁ : allLevelParamsDefinedIGo st params lmemo memo sub
              with ⟨rs, lmemo₁, memo₁⟩
            rw [h₁] at hgo
            cases hgo
            obtain ⟨hinv₁, hden₁⟩ := ih sub hguard hinv h₁
            have hcond : ∀ x, st.denote e = some x →
                x.allLevelParamsDefined params = rs := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              simpa [Expr.allLevelParamsDefined] using hden₁ xs hxs
            exact ⟨⟨hinv₁.1,
              hinv₁.2.insert (fun x hx => (hcond x hx).symm)⟩, hcond⟩
        | lam nmᵢ ty body m =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            obtain ⟨xt, hxt⟩ := denote_total hwf ty
              (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xb, hxb⟩ := denote_total hwf body
              (Nat.lt_trans hguard.2 hesz)
            obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
              (fun u hu => hlv u (by simp [ENode.levels, hu]))
            obtain ⟨nm, hnmDen⟩ := denoteN_total hwf nmᵢ
              (hwf.names_lt e _ hn nmᵢ (by simp [ENode.names]))
            have hx : st.denote e = some (.lam nm xt xb bm) := by
              rw [hde, denoteNode, hxt, hxb, hbm, hnmDen]; rfl
            rcases h₁ : allLevelParamsDefinedIGo st params lmemo memo ty
              with ⟨rt, lmemo₁, memo₁⟩
            rw [h₁] at hgo
            obtain ⟨hinv₁, hden₁⟩ := ih ty hguard.1 hinv h₁
            have hrt := hden₁ xt hxt
            cases hbt : rt with
            | false =>
              rw [hbt] at hgo
              dsimp only at hgo
              cases hgo
              have hcond : ∀ x, st.denote e = some x →
                  x.allLevelParamsDefined params = false := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                simp only [Expr.allLevelParamsDefined]
                rw [hrt, hbt]
                simp
              exact ⟨⟨hinv₁.1,
                hinv₁.2.insert (fun x hx => (hcond x hx).symm)⟩, hcond⟩
            | true =>
              rw [hbt] at hgo
              dsimp only at hgo
              rcases h₂ : allLevelParamsDefinedIGo st params lmemo₁ memo₁
                body with ⟨rb, lmemo₂, memo₂⟩
              rw [h₂] at hgo
              obtain ⟨hinv₂, hden₂⟩ := ih body hguard.2 hinv₁ h₂
              have hrb := hden₂ xb hxb
              cases hbb : rb with
              | false =>
                rw [hbb] at hgo
                dsimp only at hgo
                cases hgo
                have hcond : ∀ x, st.denote e = some x →
                    x.allLevelParamsDefined params = false := by
                  intro x hxx
                  rw [hx] at hxx; cases hxx
                  simp only [Expr.allLevelParamsDefined]
                  rw [hrt, hbt, hrb, hbb]
                  simp
                exact ⟨⟨hinv₂.1,
                  hinv₂.2.insert (fun x hx => (hcond x hx).symm)⟩, hcond⟩
              | true =>
                rw [hbb] at hgo
                dsimp only at hgo
                cases m with
                | mk bi cod =>
                cases cod with
                | none =>
                  dsimp only at hgo
                  cases hgo
                  obtain rfl : bm = ⟨bi, none⟩ := by
                    simpa [denoteBM] using hbm.symm
                  have hcond : ∀ x, st.denote e = some x →
                      x.allLevelParamsDefined params = true := by
                    intro x hxx
                    rw [hx] at hxx; cases hxx
                    simp only [Expr.allLevelParamsDefined]
                    rw [hrt, hbt, hrb, hbb]
                    simp
                  exact ⟨⟨hinv₂.1,
                    hinv₂.2.insert (fun x hx => (hcond x hx).symm)⟩,
                    hcond⟩
                | some v =>
                  dsimp only at hgo
                  rcases h₃ : lparamsDefinedLIGo st params lmemo₂ v
                    with ⟨rc, lmemo₃⟩
                  rw [h₃] at hgo
                  cases hgo
                  obtain ⟨hinv₃, hden₃⟩ :=
                    lparamsDefinedLIGo_spec hwf v hinv₂.1 h₃
                  obtain ⟨xv, hxv⟩ := denoteL_total hwf v
                    (hlv v (by simp [ENode.levels]))
                  obtain rfl : bm = ⟨bi, some xv⟩ := by
                    have h := hbm.symm
                    simp only [denoteBM, hxv, Option.map_some,
                      Option.some.injEq] at h
                    exact h
                  have hcond : ∀ x, st.denote e = some x →
                      x.allLevelParamsDefined params = rc := by
                    intro x hxx
                    rw [hx] at hxx; cases hxx
                    simp only [Expr.allLevelParamsDefined]
                    rw [hrt, hbt, hrb, hbb, ← hden₃ xv hxv]
                    simp
                  exact ⟨⟨hinv₃,
                    hinv₂.2.insert (fun x hx => (hcond x hx).symm)⟩,
                    hcond⟩
        | forallE nmᵢ ty body m =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            obtain ⟨xt, hxt⟩ := denote_total hwf ty
              (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xb, hxb⟩ := denote_total hwf body
              (Nat.lt_trans hguard.2 hesz)
            obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
              (fun u hu => hlv u (by simp [ENode.levels, hu]))
            obtain ⟨nm, hnmDen⟩ := denoteN_total hwf nmᵢ
              (hwf.names_lt e _ hn nmᵢ (by simp [ENode.names]))
            have hx : st.denote e = some (.forallE nm xt xb bm) := by
              rw [hde, denoteNode, hxt, hxb, hbm, hnmDen]; rfl
            rcases h₁ : allLevelParamsDefinedIGo st params lmemo memo ty
              with ⟨rt, lmemo₁, memo₁⟩
            rw [h₁] at hgo
            obtain ⟨hinv₁, hden₁⟩ := ih ty hguard.1 hinv h₁
            have hrt := hden₁ xt hxt
            cases hbt : rt with
            | false =>
              rw [hbt] at hgo
              dsimp only at hgo
              cases hgo
              have hcond : ∀ x, st.denote e = some x →
                  x.allLevelParamsDefined params = false := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                simp only [Expr.allLevelParamsDefined]
                rw [hrt, hbt]
                simp
              exact ⟨⟨hinv₁.1,
                hinv₁.2.insert (fun x hx => (hcond x hx).symm)⟩, hcond⟩
            | true =>
              rw [hbt] at hgo
              dsimp only at hgo
              rcases h₂ : allLevelParamsDefinedIGo st params lmemo₁ memo₁
                body with ⟨rb, lmemo₂, memo₂⟩
              rw [h₂] at hgo
              obtain ⟨hinv₂, hden₂⟩ := ih body hguard.2 hinv₁ h₂
              have hrb := hden₂ xb hxb
              cases hbb : rb with
              | false =>
                rw [hbb] at hgo
                dsimp only at hgo
                cases hgo
                have hcond : ∀ x, st.denote e = some x →
                    x.allLevelParamsDefined params = false := by
                  intro x hxx
                  rw [hx] at hxx; cases hxx
                  simp only [Expr.allLevelParamsDefined]
                  rw [hrt, hbt, hrb, hbb]
                  simp
                exact ⟨⟨hinv₂.1,
                  hinv₂.2.insert (fun x hx => (hcond x hx).symm)⟩, hcond⟩
              | true =>
                rw [hbb] at hgo
                dsimp only at hgo
                cases m with
                | mk bi cod =>
                cases cod with
                | none =>
                  dsimp only at hgo
                  cases hgo
                  obtain rfl : bm = ⟨bi, none⟩ := by
                    simpa [denoteBM] using hbm.symm
                  have hcond : ∀ x, st.denote e = some x →
                      x.allLevelParamsDefined params = true := by
                    intro x hxx
                    rw [hx] at hxx; cases hxx
                    simp only [Expr.allLevelParamsDefined]
                    rw [hrt, hbt, hrb, hbb]
                    simp
                  exact ⟨⟨hinv₂.1,
                    hinv₂.2.insert (fun x hx => (hcond x hx).symm)⟩,
                    hcond⟩
                | some v =>
                  dsimp only at hgo
                  rcases h₃ : lparamsDefinedLIGo st params lmemo₂ v
                    with ⟨rc, lmemo₃⟩
                  rw [h₃] at hgo
                  cases hgo
                  obtain ⟨hinv₃, hden₃⟩ :=
                    lparamsDefinedLIGo_spec hwf v hinv₂.1 h₃
                  obtain ⟨xv, hxv⟩ := denoteL_total hwf v
                    (hlv v (by simp [ENode.levels]))
                  obtain rfl : bm = ⟨bi, some xv⟩ := by
                    have h := hbm.symm
                    simp only [denoteBM, hxv, Option.map_some,
                      Option.some.injEq] at h
                    exact h
                  have hcond : ∀ x, st.denote e = some x →
                      x.allLevelParamsDefined params = rc := by
                    intro x hxx
                    rw [hx] at hxx; cases hxx
                    simp only [Expr.allLevelParamsDefined]
                    rw [hrt, hbt, hrb, hbb, ← hden₃ xv hxv]
                    simp
                  exact ⟨⟨hinv₃,
                    hinv₂.2.insert (fun x hx => (hcond x hx).symm)⟩,
                    hcond⟩

/-- `allLevelParamsDefinedI` agrees with
`Expr.allLevelParamsDefined`. -/
theorem allLevelParamsDefinedI_spec {st : EStore} (hwf : st.WF)
    {params : List Name} {e : EIdx} {a : Expr}
    (ha : st.denote e = some a) :
    st.allLevelParamsDefinedI params e = a.allLevelParamsDefined params := by
  rcases hgo : allLevelParamsDefinedIGo st params {} {} e with ⟨r, lm, m⟩
  obtain ⟨-, hcond⟩ := allLevelParamsDefinedIGo_spec hwf e
    ⟨LvlQMemoInv.empty, QMemo0Inv.empty⟩ hgo
  simp only [allLevelParamsDefinedI, hgo]
  exact (hcond a ha).symm

/-! ## The indexed `constsResolveFI` walker -/

/-- The indexed walker agrees with the `Env`-lookup walker whenever the
lookups agree pointwise (the bridge instantiates at `mkFEnv`). -/
theorem constsResolveFIGo_eq {st : EStore} {fe : FEnv} {env : Env}
    (hfind : ∀ n, fe.find? n = env.find? n) :
    ∀ (e : EIdx) (memo : Std.HashMap EIdx Bool),
      constsResolveFIGo st fe memo e =
        EStore.constsResolveIGo st env memo e := by
  intro e
  induction e using Nat.strongRecOn with
  | _ e ih =>
    intro memo
    unfold constsResolveFIGo EStore.constsResolveIGo
    cases hm : memo[e]? with
    | some r => rfl
    | none =>
      dsimp only
      cases hn : st.nodes[e]? with
      | none => rfl
      | some n =>
        dsimp only
        cases n with
        | bvar i => rfl
        | sort u => rfl
        | lit l => cases l <;> simp only [hfind]
        | const nmᵢ us =>
          simp only [hfind]
          rfl

        | fvar idx nmᵢ ty =>
          by_cases hg : ty < e
          · simp only [dif_pos hg, ih ty hg]
          · simp only [dif_neg hg]
        | app f a =>
          by_cases hg : f < e ∧ a < e
          · simp only [dif_pos hg, ih f hg.1, ih a hg.2]
          · simp only [dif_neg hg]
        | lam nmᵢ ty body m =>
          by_cases hg : ty < e ∧ body < e
          · simp only [dif_pos hg, ih ty hg.1, ih body hg.2]
          · simp only [dif_neg hg]
        | forallE nmᵢ ty body m =>
          by_cases hg : ty < e ∧ body < e
          · simp only [dif_pos hg, ih ty hg.1, ih body hg.2]
          · simp only [dif_neg hg]
        | letE nmᵢ ty val body =>
          by_cases hg : ty < e ∧ val < e ∧ body < e
          · simp only [dif_pos hg, ih ty hg.1, ih val hg.2.1,
              ih body hg.2.2]
          · simp only [dif_neg hg]
        | proj sNᵢ j sub =>
          by_cases hg : sub < e
          · simp only [dif_pos hg, hfind, ih sub hg]
            rfl
          · simp only [dif_neg hg]

/-- `constsResolveFI` under `mkFEnv` agrees with
`Expr.constsResolve`. -/
theorem constsResolveFI_spec {st : EStore} {env : Env} {e : EIdx}
    {a : Expr} (hwf : st.WF) (he : st.denote e = some a) :
    constsResolveFI st (mkFEnv env) e = a.constsResolve env := by
  unfold constsResolveFI
  rw [constsResolveFIGo_eq (fun n => mkFEnv_find? env n)]
  exact constsResolveI_spec hwf he

/-! ## Store validation: `wfB` establishes canonicity -/

/-- Per-node facts of the range pass. -/
private theorem wfBNodes_facts {st : EStore} :
    ∀ (k : Nat), EStore.wfBNodes st k = true →
      ∀ i, i < k → ∃ n, st.nodes[i]? = some n ∧
        (∀ c ∈ n.children, c < i) ∧
        (∀ u ∈ n.levels, u < st.lnodes.size) ∧
        (∀ p ∈ n.names, p < st.nnodes.size) ∧
        st.cons[n]? = some i ∧
        st.bvarBs[i]? = some (n.bvarBoundOf st.bvarBs) ∧
        st.fvarBs[i]? = some (n.fvarRangeOf st.fvarBs) ∧
        st.eparamBs[i]? = some (n.hasLParamOf st.eparamBs st.lparamBs)
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | k + 1, h, i, hi => by
    unfold EStore.wfBNodes at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hrest, hk⟩ := h
    by_cases hik : i < k
    · exact wfBNodes_facts k hrest i hik
    · obtain rfl : i = k := by omega
      cases hn : st.nodes[i]? with
      | none => rw [hn] at hk; cases hk
      | some n =>
        rw [hn] at hk
        simp only [Bool.and_eq_true, beq_iff_eq] at hk
        obtain ⟨⟨⟨⟨⟨⟨hch, hlv⟩, hnm⟩, hcons⟩, hbv⟩, hfv⟩, hep⟩ := hk
        refine ⟨n, rfl, ?_, ?_, ?_, hcons, hbv, hfv, hep⟩
        · intro c hc
          cases n with
          | bvar i0 => simp [ENode.children] at hc
          | sort u => simp [ENode.children] at hc
          | const nmᵢ us => simp [ENode.children] at hc

          | lit l => simp [ENode.children] at hc
          | fvar idx nmᵢ t =>
            simp only [ENode.children, List.mem_singleton] at hc
            subst hc
            simpa using hch
          | app f a =>
            simp only [decide_eq_true_eq, Bool.and_eq_true] at hch
            simp only [ENode.children, List.mem_cons,
              List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl
            · exact hch.1
            · exact hch.2
          | lam nmᵢ t b m =>
            simp only [decide_eq_true_eq, Bool.and_eq_true] at hch
            simp only [ENode.children, List.mem_cons,
              List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl
            · exact hch.1
            · exact hch.2
          | forallE nmᵢ t b m =>
            simp only [decide_eq_true_eq, Bool.and_eq_true] at hch
            simp only [ENode.children, List.mem_cons,
              List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl
            · exact hch.1
            · exact hch.2
          | letE nmᵢ t v b =>
            simp only [decide_eq_true_eq, Bool.and_eq_true] at hch
            simp only [ENode.children, List.mem_cons,
              List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl | rfl
            · exact hch.1.1
            · exact hch.1.2
            · exact hch.2
          | proj sNᵢ j e0 =>
            simp only [ENode.children, List.mem_singleton] at hc
            subst hc
            simpa using hch
        · intro u hu
          cases n with
          | sort v =>
            simp only [ENode.levels, List.mem_singleton] at hu
            subst hu
            dsimp only at hlv
            simpa using hlv
          | const nmᵢ us =>
            simp only [ENode.levels] at hu
            dsimp only at hlv
            simp only [List.all_eq_true, decide_eq_true_eq] at hlv
            exact hlv u hu
          | lam nmᵢ t b m =>
            simp only [ENode.levels] at hu
            dsimp only at hlv
            cases hm : m.cod with
            | none => rw [hm] at hu; cases hu
            | some v =>
              rw [hm] at hu
              simp only [Option.toList_some, List.mem_singleton] at hu
              subst hu
              rw [hm] at hlv
              simpa using hlv
          | forallE nmᵢ t b m =>
            simp only [ENode.levels] at hu
            dsimp only at hlv
            cases hm : m.cod with
            | none => rw [hm] at hu; cases hu
            | some v =>
              rw [hm] at hu
              simp only [Option.toList_some, List.mem_singleton] at hu
              subst hu
              rw [hm] at hlv
              simpa using hlv
          | bvar i0 => simp [ENode.levels] at hu
          | fvar idx nmᵢ t => simp [ENode.levels] at hu

          | app f a => simp [ENode.levels] at hu
          | letE nmᵢ t v b => simp [ENode.levels] at hu

          | lit l => simp [ENode.levels] at hu
          | proj sNᵢ j e0 => simp [ENode.levels] at hu
        · intro p hp
          simp only [List.all_eq_true, decide_eq_true_eq] at hnm
          exact hnm p hp

/-- Per-node facts of the level range pass. -/
private theorem wfBLNodes_facts {st : EStore} :
    ∀ (k : Nat), EStore.wfBLNodes st k = true →
      ∀ u, u < k → ∃ m, st.lnodes[u]? = some m ∧
        (∀ c ∈ m.children, c < u) ∧ st.lcons[m]? = some u ∧
        st.lparamBs[u]? = some (m.hasParamOf st.lparamBs)
  | 0, _, u, hu => absurd hu (Nat.not_lt_zero u)
  | k + 1, h, u, hu => by
    unfold EStore.wfBLNodes at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hrest, hk⟩ := h
    by_cases huk : u < k
    · exact wfBLNodes_facts k hrest u huk
    · obtain rfl : u = k := by omega
      cases hn : st.lnodes[u]? with
      | none => rw [hn] at hk; cases hk
      | some m =>
        rw [hn] at hk
        simp only [Bool.and_eq_true, beq_iff_eq] at hk
        obtain ⟨⟨hch, hcons⟩, hpb⟩ := hk
        refine ⟨m, rfl, ?_, hcons, hpb⟩
        intro c hc
        cases m with
        | zero => simp [LNode.children] at hc
        | param p => simp [LNode.children] at hc
        | succ v =>
          simp only [LNode.children, List.mem_singleton] at hc
          subst hc
          simpa using hch
        | max a b =>
          simp only [decide_eq_true_eq, Bool.and_eq_true] at hch
          simp only [LNode.children, List.mem_cons,
            List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl
          · exact hch.1
          · exact hch.2
        | imax a b =>
          simp only [decide_eq_true_eq, Bool.and_eq_true] at hch
          simp only [LNode.children, List.mem_cons,
            List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl
          · exact hch.1
          · exact hch.2

/-- Per-node facts of the name range pass (task #88). -/
private theorem wfBNNodes_facts {st : EStore} :
    ∀ (k : Nat), EStore.wfBNNodes st k = true →
      ∀ i, i < k → ∃ m, st.nnodes[i]? = some m ∧
        (∀ c ∈ m.children, c < i) ∧ st.ncons[m]? = some i ∧
        st.rbNames[i]? = some (m.nameOf st.rbNames)
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | k + 1, h, i, hi => by
    unfold EStore.wfBNNodes at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hrest, hk⟩ := h
    by_cases hik : i < k
    · exact wfBNNodes_facts k hrest i hik
    · obtain rfl : i = k := by omega
      cases hn : st.nnodes[i]? with
      | none => rw [hn] at hk; cases hk
      | some m =>
        rw [hn] at hk
        simp only [Bool.and_eq_true, beq_iff_eq] at hk
        obtain ⟨⟨hch, hcons⟩, hrb⟩ := hk
        refine ⟨m, rfl, ?_, hcons, hrb⟩
        intro c hc
        cases m with
        | anonymous => simp [NNode.children] at hc
        | str p s =>
          simp only [NNode.children, List.mem_singleton] at hc
          subst hc
          simpa using hch
        | num p j =>
          simp only [NNode.children, List.mem_singleton] at hc
          subst hc
          simpa using hch

/-- The one-time store validation establishes canonicity: everything
the interned operations' faithfulness needs. -/
theorem wfB_wf {st : EStore} (h : st.wfB = true) : st.WF := by
  unfold EStore.wfB at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hns, hls⟩, hcons⟩, hlcons⟩, hbsz⟩, hfsz⟩, hpsz⟩,
    hesz⟩, hnns⟩, hncons⟩, hrbsz⟩ := h
  have hnf := wfBNodes_facts st.nodes.size hns
  have hlf := wfBLNodes_facts st.lnodes.size hls
  have hnnf := wfBNNodes_facts st.nnodes.size hnns
  refine ⟨?_, ?_, ?_, ?_, ?_, hbsz, hfsz, ?_, ?_, hpsz, ?_, hesz, ?_, ?_,
    ?_, ?_, hrbsz, ?_⟩
  · intro i n hn c hc
    obtain ⟨n', hn', hch, -, -, -, -, -, -⟩ :=
      hnf i (Array.getElem?_eq_some_iff.mp hn).1
    rw [hn] at hn'
    cases hn'
    exact hch c hc
  · intro n i
    constructor
    · intro hci
      rw [List.all_eq_true] at hcons
      have := hcons (n, i)
        (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hci)
      simpa using this
    · intro hn
      obtain ⟨n', hn', -, -, -, hc, -, -, -⟩ :=
        hnf i (Array.getElem?_eq_some_iff.mp hn).1
      rw [hn] at hn'
      cases hn'
      exact hc
  · intro i n hn u hu
    obtain ⟨n', hn', -, hlv, -, -, -, -, -⟩ :=
      hnf i (Array.getElem?_eq_some_iff.mp hn).1
    rw [hn] at hn'
    cases hn'
    exact hlv u hu
  · intro u m hm c hc
    obtain ⟨m', hm', hch, -, -⟩ := hlf u (Array.getElem?_eq_some_iff.mp hm).1
    rw [hm] at hm'
    cases hm'
    exact hch c hc
  · intro m u
    constructor
    · intro hcu
      rw [List.all_eq_true] at hlcons
      have := hlcons (m, u)
        (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hcu)
      simpa using this
    · intro hm
      obtain ⟨m', hm', -, hc, -⟩ := hlf u (Array.getElem?_eq_some_iff.mp hm).1
      rw [hm] at hm'
      cases hm'
      exact hc
  · intro i n hn
    obtain ⟨n', hn', -, -, -, -, hbv, -, -⟩ :=
      hnf i (Array.getElem?_eq_some_iff.mp hn).1
    rw [hn] at hn'
    cases hn'
    exact hbv
  · intro i n hn
    obtain ⟨n', hn', -, -, -, -, -, hfv, -⟩ :=
      hnf i (Array.getElem?_eq_some_iff.mp hn).1
    rw [hn] at hn'
    cases hn'
    exact hfv
  · intro u m hm
    obtain ⟨m', hm', -, -, hpb⟩ := hlf u (Array.getElem?_eq_some_iff.mp hm).1
    rw [hm] at hm'
    cases hm'
    exact hpb
  · intro i n hn
    obtain ⟨n', hn', -, -, -, -, -, -, hep⟩ :=
      hnf i (Array.getElem?_eq_some_iff.mp hn).1
    rw [hn] at hn'
    cases hn'
    exact hep
  · intro i n hn p hp
    obtain ⟨n', hn', -, -, hnm, -, -, -, -⟩ :=
      hnf i (Array.getElem?_eq_some_iff.mp hn).1
    rw [hn] at hn'
    cases hn'
    exact hnm p hp
  · intro i m hm c hc
    obtain ⟨m', hm', hch, -, -⟩ :=
      hnnf i (Array.getElem?_eq_some_iff.mp hm).1
    rw [hm] at hm'
    cases hm'
    exact hch c hc
  · intro m i
    constructor
    · intro hci
      rw [List.all_eq_true] at hncons
      have := hncons (m, i)
        (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hci)
      simpa using this
    · intro hm
      obtain ⟨m', hm', -, hc, -⟩ :=
        hnnf i (Array.getElem?_eq_some_iff.mp hm).1
      rw [hm] at hm'
      cases hm'
      exact hc
  · intro i m hm
    obtain ⟨m', hm', -, -, hrb⟩ :=
      hnnf i (Array.getElem?_eq_some_iff.mp hm).1
    rw [hm] at hm'
    cases hm'
    exact hrb

/-! ## Denotation of parsed declarations -/

/-- Structural denotation of a parsed constant-value header. -/
def denoteCVP (st : EStore) (cv : ConstantValP) : Option ConstantVal :=
  (st.denote cv.type).map fun ty => ⟨cv.name, cv.levelParams, ty⟩

/-- Structural denotation of a parsed declaration — the identification
of a `DeclP` with the spec `Declaration` the consistency statements
quantify over. -/
def denoteDeclP (st : EStore) : DeclP → Option Declaration
  | .axiomDecl v => (denoteCVP st v).map .axiomDecl
  | .defnDecl v value hint =>
    (denoteCVP st v).bind fun cv =>
      (st.denote value).map fun ve => .defnDecl cv ve hint
  | .thmDecl v value =>
    (denoteCVP st v).bind fun cv =>
      (st.denote value).map fun ve => .thmDecl cv ve
  | .opaqueDecl v value =>
    (denoteCVP st v).bind fun cv =>
      (st.denote value).map fun ve => .opaqueDecl cv ve
  | .basisDecl kind => some (.basisDecl kind)
  | .indDecl block => some (.indDecl block)

/-- On a canonical store, in-range parsed declarations denote. -/
theorem denoteDeclP_total {st : EStore} (hwf : st.WF) {pd : DeclP}
    (hin : pd.inRangeB st.nodes.size = true) :
    ∃ d, denoteDeclP st pd = some d := by
  cases pd with
  | axiomDecl v =>
    simp only [DeclP.inRangeB, decide_eq_true_eq] at hin
    obtain ⟨ty, hty⟩ := denote_total hwf v.type hin
    refine ⟨.axiomDecl ⟨v.name, v.levelParams, ty⟩, ?_⟩
    simp [denoteDeclP, denoteCVP, hty]
  | defnDecl v value hint =>
    simp only [DeclP.inRangeB, Bool.and_eq_true, decide_eq_true_eq] at hin
    obtain ⟨ty, hty⟩ := denote_total hwf v.type hin.1
    obtain ⟨ve, hve⟩ := denote_total hwf value hin.2
    refine ⟨.defnDecl ⟨v.name, v.levelParams, ty⟩ ve hint, ?_⟩
    simp [denoteDeclP, denoteCVP, hty, hve]
  | thmDecl v value =>
    simp only [DeclP.inRangeB, Bool.and_eq_true, decide_eq_true_eq] at hin
    obtain ⟨ty, hty⟩ := denote_total hwf v.type hin.1
    obtain ⟨ve, hve⟩ := denote_total hwf value hin.2
    refine ⟨.thmDecl ⟨v.name, v.levelParams, ty⟩ ve, ?_⟩
    simp [denoteDeclP, denoteCVP, hty, hve]
  | opaqueDecl v value =>
    simp only [DeclP.inRangeB, Bool.and_eq_true, decide_eq_true_eq] at hin
    obtain ⟨ty, hty⟩ := denote_total hwf v.type hin.1
    obtain ⟨ve, hve⟩ := denote_total hwf value hin.2
    refine ⟨.opaqueDecl ⟨v.name, v.levelParams, ty⟩ ve, ?_⟩
    simp [denoteDeclP, denoteCVP, hty, hve]
  | basisDecl kind => exact ⟨_, rfl⟩
  | indDecl block => exact ⟨_, rfl⟩

/-- Denotations of parsed declarations are `Ext`-stable (the parse
store only grows). -/
theorem denoteDeclP_mono {st st' : EStore} (_hwf : st.WF)
    (hext : Ext st st') {pd : DeclP} {d : Declaration}
    (h : denoteDeclP st pd = some d) : denoteDeclP st' pd = some d := by
  cases pd <;>
    simp only [denoteDeclP, denoteCVP, Option.map_eq_some_iff,
      Option.bind_eq_some_iff] at h ⊢
  case axiomDecl v =>
    obtain ⟨cv, ⟨ty, hty, rfl⟩, rfl⟩ := h
    exact ⟨_, ⟨ty, denote_mono hext hty, rfl⟩, rfl⟩
  case defnDecl v value hint =>
    obtain ⟨cv, ⟨ty, hty, rfl⟩, ve, hve, rfl⟩ := h
    exact ⟨_, ⟨ty, denote_mono hext hty, rfl⟩,
      ve, denote_mono hext hve, rfl⟩
  case thmDecl v value =>
    obtain ⟨cv, ⟨ty, hty, rfl⟩, ve, hve, rfl⟩ := h
    exact ⟨_, ⟨ty, denote_mono hext hty, rfl⟩,
      ve, denote_mono hext hve, rfl⟩
  case opaqueDecl v value =>
    obtain ⟨cv, ⟨ty, hty, rfl⟩, ve, hve, rfl⟩ := h
    exact ⟨_, ⟨ty, denote_mono hext hty, rfl⟩,
      ve, denote_mono hext hve, rfl⟩
  case basisDecl kind => exact h
  case indDecl block => exact h

end Setlec
