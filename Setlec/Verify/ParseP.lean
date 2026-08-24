import Setlec.Verify.ILevel
import Setlec.Kernel.CheckerS

/-!
# Parse-time interning: walker specs and parsed-declaration denotation
(task #78; store canonicity is carried by the parse arena's type since
task #103 — `WFStore`, `Setlec/Kernel/WFStore.lean`)

* Specs for the DAG-memoized syntactic walkers the parsed-index drivers
  run on raw and annotated input — `allLevelParamsDefinedI` (with its
  level-side walker) and the indexed `constsResolveFI` — against their
  `Expr`-level counterparts under the structural denotation.
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
        rw [node1?_nodes hn] at hnone
        cases hnone
      · rename_i n hn
        have hesz : epos e < st.nodes.size :=
          (Array.getElem?_eq_some_iff.mp hn).1
        have hclP := hwf.children_lt (epos e) n hn
        have hcl : ∀ c ∈ n.children, c < e := fun c hcin =>
          lt_of_epos_lt' (hclP c hcin).1 (hclP c hcin).2
        have hcv : ∀ c ∈ n.children, st.Valid1 c := fun c hcin =>
          ⟨(hclP c hcin).1, Nat.lt_trans (hclP c hcin).2 hesz⟩
        have hlv := hwf.levels_lt (epos e) n hn
        have hde : ∀ {x}, st.denote e = some x →
            st.denote e = denoteNode st.denote st.denoteL st.denoteN n :=
          fun hxx => denote_node
            (by rw [node1?_of_etier (denote_etier hxx)]; exact hn) hcl
        cases n with
        | bvar i =>
          dsimp only at hgo
          cases hgo
          have hcond : ∀ x, st.denote e = some x →
              x.allLevelParamsDefined params = true := by
            intro x hxx
            rw [hde hxx] at hxx
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
            rw [hde hxx] at hxx
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
          have hcond : ∀ x, st.denote e = some x →
              x.allLevelParamsDefined params = r := by
            intro x hxx
            have hx : st.denote e = some (.sort xu) := by
              rw [hde hxx, denoteNode, hxu]; rfl
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
            (hwf.names_lt (epos e) _ hn nmᵢ (by simp [ENode.names]))
          have hcond : ∀ x, st.denote e = some x →
              x.allLevelParamsDefined params = r := by
            intro x hxx
            have hx : st.denote e = some (.const nm ls) := by
              rw [hde hxx, denoteNode, hls, hnmDen]; rfl
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
              (hcv ty (by simp [ENode.children]))
            obtain ⟨nm, hnmDen⟩ := denoteN_total hwf nmᵢ
              (hwf.names_lt (epos e) _ hn nmᵢ (by simp [ENode.names]))
            rcases h₁ : allLevelParamsDefinedIGo st params lmemo memo ty
              with ⟨rt, lmemo₁, memo₁⟩
            rw [h₁] at hgo
            cases hgo
            obtain ⟨hinv₁, hden₁⟩ := ih ty hguard hinv h₁
            have hcond : ∀ x, st.denote e = some x →
                x.allLevelParamsDefined params = rt := by
              intro x hxx
              have hx : st.denote e = some (.fvar idx nm xt) := by
                rw [hde hxx, denoteNode, hxt, hnmDen]; rfl
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
              (hcv f (by simp [ENode.children]))
            obtain ⟨xa, hxa⟩ := denote_total hwf a
              (hcv a (by simp [ENode.children]))
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
                have hx : st.denote e = some (.app xf xa) := by
                  rw [hde hxx, denoteNode, hxf, hxa]; rfl
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
                have hx : st.denote e = some (.app xf xa) := by
                  rw [hde hxx, denoteNode, hxf, hxa]; rfl
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
              (hcv ty (by simp [ENode.children]))
            obtain ⟨xv, hxv⟩ := denote_total hwf val
              (hcv val (by simp [ENode.children]))
            obtain ⟨xb, hxb⟩ := denote_total hwf body
              (hcv body (by simp [ENode.children]))
            obtain ⟨nm, hnmDen⟩ := denoteN_total hwf nmᵢ
              (hwf.names_lt (epos e) _ hn nmᵢ (by simp [ENode.names]))
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
                have hx : st.denote e = some (.letE nm xt xv xb) := by
                  rw [hde hxx, denoteNode, hxt, hxv, hxb, hnmDen]; rfl
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
                  have hx : st.denote e = some (.letE nm xt xv xb) := by
                    rw [hde hxx, denoteNode, hxt, hxv, hxb, hnmDen]; rfl
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
                  have hx : st.denote e = some (.letE nm xt xv xb) := by
                    rw [hde hxx, denoteNode, hxt, hxv, hxb, hnmDen]; rfl
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
              (hcv sub (by simp [ENode.children]))
            obtain ⟨sN, hnmDen⟩ := denoteN_total hwf sNᵢ
              (hwf.names_lt (epos e) _ hn sNᵢ (by simp [ENode.names]))
            rcases h₁ : allLevelParamsDefinedIGo st params lmemo memo sub
              with ⟨rs, lmemo₁, memo₁⟩
            rw [h₁] at hgo
            cases hgo
            obtain ⟨hinv₁, hden₁⟩ := ih sub hguard hinv h₁
            have hcond : ∀ x, st.denote e = some x →
                x.allLevelParamsDefined params = rs := by
              intro x hxx
              have hx : st.denote e = some (.proj sN j xs) := by
                rw [hde hxx, denoteNode, hxs, hnmDen]; rfl
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
              (hcv ty (by simp [ENode.children]))
            obtain ⟨xb, hxb⟩ := denote_total hwf body
              (hcv body (by simp [ENode.children]))
            obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
              (fun u hu => hlv u (by simp [ENode.levels, hu]))
            obtain ⟨nm, hnmDen⟩ := denoteN_total hwf nmᵢ
              (hwf.names_lt (epos e) _ hn nmᵢ (by simp [ENode.names]))
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
                have hx : st.denote e = some (.lam nm xt xb bm) := by
                  rw [hde hxx, denoteNode, hxt, hxb, hbm, hnmDen]; rfl
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
                  have hx : st.denote e = some (.lam nm xt xb bm) := by
                    rw [hde hxx, denoteNode, hxt, hxb, hbm, hnmDen]; rfl
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
                    have hx : st.denote e = some (.lam nm xt xb ⟨bi, none⟩) := by
                      rw [hde hxx, denoteNode, hxt, hxb, hbm, hnmDen]; rfl
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
                    have hx : st.denote e = some (.lam nm xt xb ⟨bi, some xv⟩) := by
                      rw [hde hxx, denoteNode, hxt, hxb, hbm, hnmDen]; rfl
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
              (hcv ty (by simp [ENode.children]))
            obtain ⟨xb, hxb⟩ := denote_total hwf body
              (hcv body (by simp [ENode.children]))
            obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
              (fun u hu => hlv u (by simp [ENode.levels, hu]))
            obtain ⟨nm, hnmDen⟩ := denoteN_total hwf nmᵢ
              (hwf.names_lt (epos e) _ hn nmᵢ (by simp [ENode.names]))
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
                have hx : st.denote e = some (.forallE nm xt xb bm) := by
                  rw [hde hxx, denoteNode, hxt, hxb, hbm, hnmDen]; rfl
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
                  have hx : st.denote e = some (.forallE nm xt xb bm) := by
                    rw [hde hxx, denoteNode, hxt, hxb, hbm, hnmDen]; rfl
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
                    have hx : st.denote e = some (.forallE nm xt xb ⟨bi, none⟩) := by
                      rw [hde hxx, denoteNode, hxt, hxb, hbm, hnmDen]; rfl
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
                    have hx : st.denote e = some (.forallE nm xt xb ⟨bi, some xv⟩) := by
                      rw [hde hxx, denoteNode, hxt, hxb, hbm, hnmDen]; rfl
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
      cases hn : st.nodes[epos e]? with
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
    (hin : pd.inRangeB (st.nodes.size + st.nodes.size) = true) :
    ∃ d, denoteDeclP st pd = some d := by
  cases pd with
  | axiomDecl v =>
    simp only [DeclP.inRangeB, DeclP.inRange1, Bool.and_eq_true,
      decide_eq_true_eq, beq_iff_eq] at hin
    obtain ⟨ty, hty⟩ := denote_total hwf v.type
      (valid1_of_lt_encoded hin.1 hin.2)
    refine ⟨.axiomDecl ⟨v.name, v.levelParams, ty⟩, ?_⟩
    simp [denoteDeclP, denoteCVP, hty]
  | defnDecl v value hint =>
    simp only [DeclP.inRangeB, DeclP.inRange1, Bool.and_eq_true,
      decide_eq_true_eq, beq_iff_eq] at hin
    obtain ⟨ty, hty⟩ := denote_total hwf v.type
      (valid1_of_lt_encoded hin.1.1 hin.1.2)
    obtain ⟨ve, hve⟩ := denote_total hwf value
      (valid1_of_lt_encoded hin.2.1 hin.2.2)
    refine ⟨.defnDecl ⟨v.name, v.levelParams, ty⟩ ve hint, ?_⟩
    simp [denoteDeclP, denoteCVP, hty, hve]
  | thmDecl v value =>
    simp only [DeclP.inRangeB, DeclP.inRange1, Bool.and_eq_true,
      decide_eq_true_eq, beq_iff_eq] at hin
    obtain ⟨ty, hty⟩ := denote_total hwf v.type
      (valid1_of_lt_encoded hin.1.1 hin.1.2)
    obtain ⟨ve, hve⟩ := denote_total hwf value
      (valid1_of_lt_encoded hin.2.1 hin.2.2)
    refine ⟨.thmDecl ⟨v.name, v.levelParams, ty⟩ ve, ?_⟩
    simp [denoteDeclP, denoteCVP, hty, hve]
  | opaqueDecl v value =>
    simp only [DeclP.inRangeB, DeclP.inRange1, Bool.and_eq_true,
      decide_eq_true_eq, beq_iff_eq] at hin
    obtain ⟨ty, hty⟩ := denote_total hwf v.type
      (valid1_of_lt_encoded hin.1.1 hin.1.2)
    obtain ⟨ve, hve⟩ := denote_total hwf value
      (valid1_of_lt_encoded hin.2.1 hin.2.2)
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
