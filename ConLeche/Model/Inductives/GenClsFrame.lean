module

public import ConLeche.Model.Inductives.GenClsRows
import ConLeche.Model.Inductives.GenClsMinor
import ConLeche.Model.Inductives.GenRecPins
import ConLeche.Model.Inductives.ClassGenRead
import ConLeche.Model.Inductives.NestPosOut
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.StructRecKit
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRecTyping
import ConLeche.Model.Inductives.ContLeaf
import ConLeche.Model.Rules.Sound
import ConLeche.Model.IndFrame
import ConLeche.Model.Tiers
import ConLeche.Model.Capstone
import ConLeche.Verify.Rules.Bridge
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.Deep
import ConLeche.Verify.Inductives.ClassGenMinorSyn
import ConLeche.Semantics.Tower.FixTower
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.GenRecParams
import ConLeche.Verify.InferLeaves
import ConLeche.Model.Annot.BitRename

public section

/-!
# Terms of the rule frame, graded by the stored type's inference (lane GENREC-CLS)

A term whose free variables are the rule frame's openers — the stored
recursor type's prefix openers and the declared fields opened at the rule
prefix — and which the kernel INFERS at the frame's depth is graded at
every spine fitting the frame (`graded_of_infer_openers`: the frame's
context is `CtxOk` by its openers' readings and the frame's own grading,
and the inference is sound).

The inferences come from the stored recursor type's own (`classConstOk`):
the minor premise's prefix entry is inferred at its slot, hence — it is
scoped there — at the rule prefix, where it opens to the declared fields,
the inductive hypotheses and the conclusion `motive es (C ds f⃗)`, each
inferred at its depth.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockShape BlockParts TargetMajor
  ClassGen ClassCtor ClassRead FEnv GenRecRun ClassGenScoped RecShape NestState BinderMeta
  closeTelescope)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

section Kit

/-- **A successful inference of a telescope infers every opened domain**,
at its own depth. -/
theorem inferTypeCore_openPis_dom (hμ : μ.verifiedChecks = true) {envK : Env} {F : Nat}
    {n d : Nat} {e s : Expr} {fvs : List Expr} {o : Expr}
    (hop : openPisAtFvars n e d = some (fvs, o))
    (hinf : ConLeche.inferTypeCore μ envK F d e = .ok s) :
    ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      ∃ t, ConLeche.inferTypeCore μ envK F (d + i) x.fvarTypeD = .ok t := by
  intro i x hx
  have hi : i < fvs.length := (List.getElem?_eq_some_iff.mp hx).1
  have hn : fvs.length = n := ConLeche.Verify.openPisAtFvars_length _ hop
  obtain ⟨fA, fB, o₀, hA, hB, hfe⟩ := openPisAtFvars_split i (m := n - i)
    (by rw [show i + (n - i) = n by omega]; exact hop)
  have hAl : fA.length = i := ConLeche.Verify.openPisAtFvars_length _ hA
  have hBl : fB.length = n - i := ConLeche.Verify.openPisAtFvars_length _ hB
  obtain ⟨k, hk⟩ : ∃ k, n - i = k + 1 := ⟨n - i - 1, by omega⟩
  rw [hk] at hB
  obtain ⟨dom, bd, mb, rfl⟩ : ∃ dom bd mb, o₀ = .forallE dom bd mb := by
    match o₀, hB with
    | .forallE dom bd mb, _ => exact ⟨dom, bd, mb, rfl⟩
  have hxE : x = .fvar (d + i) dom := by
    simp only [openPisAtFvars] at hB
    split at hB
    · next fvs' o' _ =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hB
      obtain ⟨rfl, -⟩ := hB
      rw [hfe, List.getElem?_append_right (by omega), hAl, Nat.sub_self] at hx
      simpa using hx.symm
    · exact nomatch hB
  have hdomInf : ∃ t, ConLeche.inferTypeCore μ envK F (d + i) dom = .ok t := by
    cases i with
    | zero =>
      simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hA
      obtain ⟨-, rfl⟩ := hA
      rw [Nat.add_zero]
      exact ConLeche.inferTypeCore_forallE_dom' hinf
    | succ k =>
      obtain ⟨bt, -, hbt, -⟩ := inferTypeCore_openPis_body hμ k hA hinf
      exact ConLeche.inferTypeCore_forallE_dom' hbt
  rw [hxE]
  exact hdomInf

/-- **A term the kernel infers over a frame of openers is graded at every
spine fitting the frame**: the openers' types read as the frame's
domains, which are graded along their fitting spines. -/
theorem graded_of_infer_openers (hμ : μ.verifiedChecks = true) {envC : Env}
    (mpC : EnvModelM V μ envC) (ψ : Name → Nat) {F D : Nat} {fr : List Expr}
    {doms : List AnnotTerm} (hdl : doms.length = D)
    (hshape : ∀ (i : Nat) (x : Expr), fr[i]? = some x → ∃ ty, x = Expr.fvar i ty)
    (hws : ∀ x ∈ fr, Expr.WScoped D x)
    (hlb : ∀ x ∈ fr, (Expr.fvarTypeD x).looseBVarsBounded 0 = true)
    (hdoms : ∀ (i : Nat) (x : Expr), fr[i]? = some x →
      denoteMeta mpC.base2.acval envC ψ i (Expr.fvarTypeD x) = some (doms.getD i default))
    (hok : ∀ l, l < D → ∀ (σ : Nat → V) (ys : List V), SpineFit σ (doms.take l) ys →
      WellDenotedV V (consList ys σ) (doms.getD l default))
    {e t : Expr} (hinf : ConLeche.inferTypeCore μ envC F D e = .ok t)
    (hwsE : Expr.WScoped D e) (hbE : e.looseBVarsBounded 0 = true)
    (hleaf : ∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2 ∈ fr) :
    ∃ w, denoteMeta mpC.base2.acval envC ψ D e = some w ∧
      ∀ (σ : Nat → V) (ys : List V), SpineFit σ doms ys → WellDenotedV V (consList ys σ) w := by
  obtain rfl : μ = .verified := CheckMode.eq_verified hμ
  have hLX : Expr.LeavesBounded e := leavesBounded_of_openers hlb hleaf
  have hltE : ∀ l ∈ e.fvarLeaves, l.1 < D := fun l hl => Expr.fvarLeaves_lt_of_wscoped hwsE l hl
  have hent : ∀ i, i < D → doms.reverse[D - 1 - i]? = some (doms.getD i default) := by
    intro i hi
    rw [List.getElem?_reverse (by omega), hdl, show D - 1 - (D - 1 - i) = i by omega,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  have hCE : CtxOk mpC.base2 ψ D doms.reverse e :=
    ctxOk_of_openers mpC.base2.acval_closed (Aa := fun i => doms.getD i default)
      (by rw [List.length_reverse, hdl]) hshape hws hdoms hleaf hltE hent
      (fun i hi ρ hρ => by
        have hs := Sat_drop hρ (D - i)
        have hdrop : doms.reverse.drop (D - i) = (doms.take i).reverse := by
          rw [List.drop_reverse, hdl, show D - (D - i) = i by omega]
        rw [hdrop] at hs
        have hsp := spineFit_frameIdx_of_sat hs
        have hc := consList_frameIdx (V := V) (doms.take i).length (fun j => ρ (j + (D - i)))
        have hw := hok i hi _ _ hsp
        rw [hc] at hw
        rw [show (fun j => ρ (j + (D - 1 - i) + 1)) = (fun j => ρ (j + (D - i))) by
          funext j; congr 1; omega]
        exact hw)
  obtain ⟨wa, hwa⟩ := acceptedReads_of mpC.base2 ψ hinf hwsE hbE hLX
  obtain ⟨-, -, -, -, hgr, -⟩ :=
    Rules.infer_sound (Rules.RulesInputs.ofSem mpC ψ) (Rules.inferTypeCore_bridge hinf)
      ⟨hwsE, hbE, hLX⟩ hCE hwa
  refine ⟨wa, hwa, fun σ ys hys => hgr _ ?_⟩
  have := sat_of_spineFit (Δ₀ := ([] : List AnnotTerm)) (Sat_nil V σ) hys
  simpa using this

theorem list_getD_append_left {α : Type} {l l' : List α} {d : α} {n : Nat}
    (h : n < l.length) : (l ++ l').getD n d = l.getD n d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem list_getD_append_right {α : Type} {l l' : List α} {d : α} {n : Nat}
    (h : l.length ≤ n) : (l ++ l').getD n d = l'.getD (n - l.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

/-- **A graded frame of openers** at depth `D`: positional variables,
scoped and bounded, their types reading as the frame's domains, which are
graded along their fitting spines. -/
structure GradedFrame {envC : Env} (mpC : EnvModelM V μ envC) (ψ : Name → Nat) (D : Nat)
    (fr : List Expr) (doms : List AnnotTerm) : Prop where
  len : doms.length = D
  frLen : fr.length = D
  shape : ∀ (i : Nat) (x : Expr), fr[i]? = some x → ∃ ty, x = Expr.fvar i ty
  ws : ∀ x ∈ fr, Expr.WScoped D x
  lb : ∀ x ∈ fr, (Expr.fvarTypeD x).looseBVarsBounded 0 = true
  rd : ∀ (i : Nat) (x : Expr), fr[i]? = some x →
    denoteMeta mpC.base2.acval envC ψ i (Expr.fvarTypeD x) = some (doms.getD i default)
  ok : ∀ l, l < D → ∀ (σ : Nat → V) (ys : List V), SpineFit σ (doms.take l) ys →
    WellDenotedV V (consList ys σ) (doms.getD l default)

/-- `graded_of_infer_openers` at a graded frame. -/
theorem GradedFrame.graded (hμ : μ.verifiedChecks = true) {envC : Env}
    {mpC : EnvModelM V μ envC} {ψ : Name → Nat} {D : Nat} {fr : List Expr}
    {doms : List AnnotTerm} (G : GradedFrame mpC ψ D fr doms) {F : Nat}
    {e t : Expr} (hinf : ConLeche.inferTypeCore μ envC F D e = .ok t)
    (hwsE : Expr.WScoped D e) (hbE : e.looseBVarsBounded 0 = true)
    (hleaf : ∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2 ∈ fr) :
    ∃ w, denoteMeta mpC.base2.acval envC ψ D e = some w ∧
      ∀ (σ : Nat → V) (ys : List V), SpineFit σ doms ys → WellDenotedV V (consList ys σ) w :=
  graded_of_infer_openers hμ mpC ψ G.len G.shape G.ws G.lb G.rd G.ok hinf hwsE hbE hleaf

/-- A leaf of a term scoped at `D` among a frame's openers extended by
more is among the frame's, when the frame has `D` positional openers. -/
theorem mem_frame_of_lt {fr zs : List Expr} {D : Nat}
    (hsh : ∀ (k : Nat) (y : Expr), zs[k]? = some y → ∃ ty, y = Expr.fvar (D + k) ty)
    {l : Nat × Expr} (hm : Expr.fvar l.1 l.2 ∈ fr ++ zs) (hlt : l.1 < D) :
    Expr.fvar l.1 l.2 ∈ fr := by
  rcases List.mem_append.mp hm with hm | hm
  · exact hm
  · obtain ⟨pos, hpos⟩ := List.getElem?_of_mem hm
    obtain ⟨ty, hty⟩ := hsh pos _ hpos
    have h1 : l.1 = D + pos := by injection hty
    omega

set_option maxHeartbeats 4000000 in
/-- **A graded frame extends by the openers of an inferred telescope over
it**: their types read (they are inferred), and each is graded along the
spines fitting the frame and the openers before it. -/
theorem GradedFrame.extend (hμ : μ.verifiedChecks = true) {envC : Env}
    {mpC : EnvModelM V μ envC} {ψ : Name → Nat} {D : Nat} {fr : List Expr}
    {doms : List AnnotTerm} (G : GradedFrame mpC ψ D fr doms) {F n : Nat}
    {T body t : Expr} {zs : List Expr} (hop : ConLeche.openPisAtFvars n T D = some (zs, body))
    (hinf : ConLeche.inferTypeCore μ envC F D T = .ok t)
    (hwsT : Expr.WScoped D T) (hbT : T.looseBVarsBounded 0 = true)
    (hleaf : ∀ l ∈ T.fvarLeaves, Expr.fvar l.1 l.2 ∈ fr) :
    GradedFrame mpC ψ (D + n) (fr ++ zs) (doms ++ readOpenedDoms mpC.base2.acval envC ψ D zs) ∧
      (∃ tb, ConLeche.inferTypeCore μ envC F (D + n) body = .ok tb) ∧
      Expr.WScoped (D + n) body ∧ body.looseBVarsBounded 0 = true ∧
      (∀ l ∈ body.fvarLeaves, Expr.fvar l.1 l.2 ∈ fr ++ zs) := by
  have hzl : zs.length = n := ConLeche.Verify.openPisAtFvars_length _ hop
  have hsh : ∀ (k : Nat) (y : Expr), zs[k]? = some y → ∃ ty, y = Expr.fvar (D + k) ty :=
    fun k y hy => openPisAtFvars_index _ _ _ hop k y hy
  obtain ⟨hwsZ, hwsB⟩ := openPisAtFvars_WScoped _ _ _ hop hwsT
  obtain ⟨hbB, hbZ⟩ := ConLeche.Verify.openPisAtFvars_bounded _ hop hbT
  have hleafs : ∀ l, (l ∈ body.fvarLeaves ∨ ∃ z ∈ zs, l ∈ z.fvarLeaves) →
      Expr.fvar l.1 l.2 ∈ fr ++ zs := by
    intro l hl
    rcases openPisAtFvars_leaves _ hop l hl with h' | h'
    · exact List.mem_append_left _ (hleaf l h')
    · exact List.mem_append_right _ h'
  have hinfZ := inferTypeCore_openPis_dom hμ hop hinf
  have hwsZt : ∀ (k : Nat) (y : Expr), zs[k]? = some y →
      Expr.WScoped (D + k) (Expr.fvarTypeD y) :=
    fun k y hy => openPisAtFvars_typeWScoped _ hop hwsT k y hy
  have hlbFZ : ∀ x ∈ fr ++ zs, (Expr.fvarTypeD x).looseBVarsBounded 0 = true := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact G.lb x hx
    · exact hbZ x hx
  -- the openers' types read
  have hread : ∀ (k : Nat) (y : Expr), zs[k]? = some y →
      ∃ a, denoteMeta mpC.base2.acval envC ψ (D + k) (Expr.fvarTypeD y) = some a := by
    intro k y hy
    obtain ⟨tk, htk⟩ := hinfZ k y hy
    have hLk : Expr.LeavesBounded (Expr.fvarTypeD y) := fun l hl => by
      obtain ⟨ty, rfl⟩ := hsh k y hy
      have hm := hleafs l (Or.inr ⟨_, List.mem_of_getElem? hy, by
        simp only [Expr.fvarLeaves, Expr.fvarTypeD] at hl ⊢
        exact List.mem_cons_of_mem _ hl⟩)
      simpa [Expr.fvarTypeD] using hlbFZ _ hm
    exact acceptedReads_of mpC.base2 ψ htk (hwsZt k y hy)
      (hbZ y (List.mem_of_getElem? hy)) hLk
  have hrdl : (readOpenedDoms mpC.base2.acval envC ψ D zs).length = n := by
    rw [readOpenedDoms_length_eq, hzl]
  have hdomsZ : ∀ (k : Nat) (y : Expr), zs[k]? = some y →
      denoteMeta mpC.base2.acval envC ψ (D + k) (Expr.fvarTypeD y)
        = some ((readOpenedDoms mpC.base2.acval envC ψ D zs).getD k default) := by
    intro k y hy
    obtain ⟨a, ha⟩ := hread k y hy
    have hk : k < zs.length := (List.getElem?_eq_some_iff.mp hy).1
    have hyE : zs[k] = y := (List.getElem?_eq_some_iff.mp hy).2
    have := readOpenedDoms_getElem (acval := mpC.base2.acval) (env := envC) (ψ := ψ) D zs k hk
    rw [hyE, ha] at this
    rw [ha, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hk), this]
    rfl
  -- the extended frames, one opener at a time
  have hstep : ∀ k, k ≤ n →
      GradedFrame mpC ψ (D + k) (fr ++ zs.take k)
        (doms ++ (readOpenedDoms mpC.base2.acval envC ψ D zs).take k) := by
    intro k
    induction k with
    | zero =>
      intro _
      simpa using G
    | succ k ih =>
      intro hk
      have Gk := ih (by omega)
      obtain ⟨y, hy⟩ : ∃ y, zs[k]? = some y := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨ty, hyE⟩ := hsh k y hy
      have hfrk : (fr ++ zs.take k).length = D + k := by
        simp [G.frLen, hzl]; omega
      have htk1 : zs.take (k + 1) = zs.take k ++ [y] := by
        rw [List.take_add_one, hy]; rfl
      have hdk1 : (readOpenedDoms mpC.base2.acval envC ψ D zs).take (k + 1)
          = (readOpenedDoms mpC.base2.acval envC ψ D zs).take k
            ++ [(readOpenedDoms mpC.base2.acval envC ψ D zs).getD k default] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by omega), List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by omega)]
        rfl
      -- the new opener's type, graded over the frame so far
      have hleafY : ∀ l ∈ (Expr.fvarTypeD y).fvarLeaves, Expr.fvar l.1 l.2 ∈ fr ++ zs.take k := by
        intro l hl
        have hm := hleafs l (Or.inr ⟨y, List.mem_of_getElem? hy, by
          rw [hyE] at hl ⊢
          simp only [Expr.fvarLeaves, Expr.fvarTypeD] at hl ⊢
          exact List.mem_cons_of_mem _ hl⟩)
        have hlt : l.1 < D + k := Expr.fvarLeaves_lt_of_wscoped (hwsZt k y hy) l hl
        rcases List.mem_append.mp hm with hm | hm
        · exact List.mem_append_left _ hm
        · refine List.mem_append_right _ ?_
          obtain ⟨pos, hpos⟩ := List.getElem?_of_mem hm
          obtain ⟨ty', hty'⟩ := hsh pos _ hpos
          have h1 : l.1 = D + pos := by injection hty'
          have hpt : (zs.take k)[pos]? = some (Expr.fvar l.1 l.2) := by
            rw [List.getElem?_take, if_pos (by omega)]; exact hpos
          exact List.mem_of_getElem? hpt
      obtain ⟨tk, htk⟩ := hinfZ k y hy
      obtain ⟨w, hw, hgw⟩ := Gk.graded hμ htk (hwsZt k y hy) (hbZ y (List.mem_of_getElem? hy))
        hleafY
      have hwE : w = (readOpenedDoms mpC.base2.acval envC ψ D zs).getD k default := by
        have := hdomsZ k y hy
        rw [hw] at this
        exact Option.some.inj this
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [G.len, hrdl]; omega
      · simp [G.frLen, hzl]; omega
      · intro i x hx
        rw [htk1, ← List.append_assoc] at hx
        rcases Nat.lt_or_ge i (D + k) with hi | hi
        · rw [List.getElem?_append_left (by rw [hfrk]; exact hi)] at hx
          exact Gk.shape i x hx
        · rw [List.getElem?_append_right (by rw [hfrk]; exact hi), hfrk] at hx
          have hi' : i - (D + k) = 0 := by
            have := (List.getElem?_eq_some_iff.mp hx).1; simp at this; omega
          rw [hi'] at hx
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
          rw [← hx]
          exact ⟨ty, by rw [hyE, show i = D + k by omega]⟩
      · intro x hx
        rw [htk1, ← List.append_assoc] at hx
        rcases List.mem_append.mp hx with hx | hx
        · exact (Gk.ws x hx).mono (by omega)
        · simp only [List.mem_singleton] at hx
          rw [hx, hyE]
          have := hwsZt k y hy
          rw [hyE] at this
          simp only [Expr.WScoped, Expr.fvarTypeD] at this ⊢
          exact ⟨by omega, this⟩
      · intro x hx
        rw [htk1, ← List.append_assoc] at hx
        rcases List.mem_append.mp hx with hx | hx
        · exact Gk.lb x hx
        · simp only [List.mem_singleton] at hx
          rw [hx]
          exact hbZ _ (List.mem_of_getElem? hy)
      · intro i x hx
        rw [htk1, ← List.append_assoc] at hx
        rw [hdk1, ← List.append_assoc]
        have hdl : (doms ++ (readOpenedDoms mpC.base2.acval envC ψ D zs).take k).length
            = D + k := Gk.len
        rcases Nat.lt_or_ge i (D + k) with hi | hi
        · rw [List.getElem?_append_left (by rw [hfrk]; exact hi)] at hx
          rw [Gk.rd i x hx, list_getD_append_left
            (l := doms ++ (readOpenedDoms mpC.base2.acval envC ψ D zs).take k) (by rw [hdl]; exact hi)]
        · rw [List.getElem?_append_right (by rw [hfrk]; exact hi), hfrk] at hx
          have hi' : i - (D + k) = 0 := by
            have := (List.getElem?_eq_some_iff.mp hx).1; simp at this; omega
          have hiE : i = D + k := by
            have := (List.getElem?_eq_some_iff.mp hx).1; simp at this; omega
          rw [hi'] at hx
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
          rw [← hx, hiE, hdomsZ k y hy, list_getD_append_right (Nat.le_of_eq hdl), hdl,
            Nat.sub_self]
          rfl
      · intro l hl σ ys hys
        rw [hdk1, ← List.append_assoc] at hys ⊢
        have hdl : (doms ++ (readOpenedDoms mpC.base2.acval envC ψ D zs).take k).length
            = D + k := Gk.len
        rcases Nat.lt_or_ge l (D + k) with hlk | hlk
        · rw [List.take_append_of_le_length (by rw [hdl]; omega)] at hys
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hdl]; exact hlk),
            ← List.getD_eq_getElem?_getD]
          exact Gk.ok l hlk σ ys hys
        · obtain rfl : l = D + k := by omega
          rw [List.take_append_of_le_length (Nat.le_of_eq hdl.symm), ← hdl,
            List.take_length] at hys
          rw [list_getD_append_right (Nat.le_of_eq hdl), hdl, Nat.sub_self]
          simp only [List.getD_cons_zero]
          rw [← hwE]
          exact hgw σ ys hys
  refine ⟨?_, ?_, hwsB, hbB, fun l hl => hleafs l (Or.inl hl)⟩
  · have := hstep n (Nat.le_refl _)
    rw [show zs.take n = zs by rw [← hzl, List.take_length],
      List.take_of_length_le (show (readOpenedDoms mpC.base2.acval envC ψ D zs).length ≤ n from
        Nat.le_of_eq hrdl)] at this
    exact this
  · rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0] at hop
      simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
      obtain ⟨-, rfl⟩ := hop
      exact ⟨t, by rw [h0, Nat.add_zero]; exact hinf⟩
    · obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
      rw [hk] at hop
      obtain ⟨bt, -, hbt, -⟩ := inferTypeCore_openPis_body hμ k hop hinf
      exact ⟨bt, by rw [hk]; exact hbt⟩

end Kit

/-! ## The minor premise, opened at the rule frame -/

section Open

variable {F : Nat} {env₁ envC : Env} {pp : BlockParts} {nestedBit : Bool} {pos : NestState}
  {cvTas : List ConstantVal} {block : List ConstantInfo}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)}

set_option maxHeartbeats 8000000 in
/-- **The minor premise of `(c, j)`, opened at the rule frame, with its
inferences**: the stored type's openers (their readings the rule
prefix's domains), and the minor premise's prefix entry — inferred at its
slot, hence at the rule prefix — opened there to the declared fields and
the inductive hypotheses (their types erasure-equal to the generator's)
and the conclusion; every opened domain and the conclusion inferred, all
leaves among the openers. -/
theorem genMinorOpen (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR) (mpC : EnvModelM V μ envC)
    (hfind : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat), r.2.2.2[i]? = some cA →
        envC.find? cA.1.name = some (.ctorInfo cA.1 (ConLeche.tgtMajorsOf out j).nPc cA.2))
    (ψ : Name → Nat) {c j : Nat} (hc : c < (tgtRs out).length)
    (hj : j < blockRecNCt (tgtRs out) c) :
    ∃ (cls s : Nat) (x : ClassCtor) (res : Expr) (ws : List Expr)
      (ihs : List (Expr × BinderMeta)) (fvs1 : List Expr) (o1 : Expr) (xs' : List Expr)
      (rest : Expr),
      genClsOf R.rd c = cls ∧ genCtorAt R.g R.rd c j = x ∧ genMinorSlot R.g R.rd c j = s ∧
      x ∈ R.g.ctors.getD cls [] ∧ tgtMajor out c = R.g.cls.getD cls default ∧
      pp.toBlockShape.rulePrefixAt c = R.g.pre.length ∧ R.g.nP + s < R.g.pre.length ∧
      ConLeche.openPisAtFvars x.nF x.tyD R.g.pre.length
        = some (tgtFieldFvs pp.toBlockShape out c j, res) ∧
      tgtCbody pp.toBlockShape out c j = res ∧ (tgtCtorOf out c j).2 = x.nF ∧
      (tgtCtorOf out c j).1 = x.cv ∧
      ConLeche.targetPiDomsWith (tgtFieldFvs pp.toBlockShape out c j) x.tyN = some ws ∧
      ihs.length = x.recs.length ∧
      (∀ (l i t tele : Nat), x.recs[l]? = some (i, t, tele) →
        (∃ ty, R.g.ihTy t tele (ws.getD i default)
          ((tgtFieldFvs pp.toBlockShape out c j).getD i default)
          (R.g.pre.length + x.nF + l) = some ty ∧ ihs[l]? = some (ty, R.g.bm)) ∧
        (∃ n, ConLeche.classRecOf R.rd.recCls R.cvGs t = some n) ∧
        (∃ xs idx, R.g.ihParts t tele (ws.getD i default) (R.g.pre.length + x.nF)
          = some (xs, idx)) ∧
        ∃ st, ConLeche.ClassRead.motiveSlot ⟨R.g.slots, []⟩ t = some st ∧ st < s) ∧
      (∃ sc, ConLeche.ClassRead.motiveSlot ⟨R.g.slots, []⟩ cls = some sc ∧ sc < s) ∧
      -- the stored type's openers
      ConLeche.openPisAtFvars (pp.toBlockShape.majorIdxAt c + 1) ((tgtRs out)[c]'hc).1.type 0
        = some (fvs1, o1) ∧
      R.g.pre.length ≤ pp.toBlockShape.majorIdxAt c ∧
      fvs1.length = pp.toBlockShape.majorIdxAt c + 1 ∧
      (∀ (i : Nat) (y : Expr), fvs1[i]? = some y → ∃ ty, y = Expr.fvar i ty) ∧
      (∀ y ∈ fvs1, Expr.WScoped (pp.toBlockShape.majorIdxAt c + 1) y ∧
        (Expr.fvarTypeD y).looseBVarsBounded 0 = true) ∧
      (∀ (i : Nat) (y : Expr), i < R.g.pre.length → fvs1[i]? = some y →
        denoteMeta mpC.base2.acval envC ψ i (Expr.fvarTypeD y)
          = some ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).getD i
              default)) ∧
      -- the minor premise, opened at the rule prefix
      xs'.length = x.nF + ihs.length ∧
      (∀ (k : Nat) (y : Expr), xs'[k]? = some y → ∃ ty, y = Expr.fvar (R.g.pre.length + k) ty) ∧
      (∀ y ∈ xs', Expr.WScoped (R.g.pre.length + x.nF + ihs.length) y ∧
        (Expr.fvarTypeD y).looseBVarsBounded 0 = true) ∧
      (∀ (k : Nat) (y : Expr), k < x.nF → xs'[k]? = some y →
        Expr.ErasedEq (Expr.fvarTypeD y)
          (Expr.fvarTypeD ((tgtFieldFvs pp.toBlockShape out c j).getD k default))) ∧
      (∀ (l : Nat) (y : Expr), xs'[x.nF + l]? = some y →
        Expr.ErasedEq (Expr.fvarTypeD y) ((ihs.getD l default).1)) ∧
      Expr.ErasedEq rest
        (Expr.mkAppN (R.g.motVar cls) (res.getAppArgs.drop (R.g.cls.getD cls default).nPc ++
          [Expr.mkAppN (.const x.cv.name (R.g.cls.getD cls default).lvls)
            ((R.g.cls.getD cls default).ds ++ tgtFieldFvs pp.toBlockShape out c j)])) ∧
      ConLeche.ScB (R.g.pre.length + x.nF)
        (Expr.mkAppN (R.g.motVar cls) (res.getAppArgs.drop (R.g.cls.getD cls default).nPc ++
          [Expr.mkAppN (.const x.cv.name (R.g.cls.getD cls default).lvls)
            ((R.g.cls.getD cls default).ds ++ tgtFieldFvs pp.toBlockShape out c j)])) ∧
      (∀ (k : Nat) (y : Expr), xs'[k]? = some y →
        ∃ t, ConLeche.inferTypeCore μ envC F (R.g.pre.length + k) (Expr.fvarTypeD y) = .ok t) ∧
      (∃ t, ConLeche.inferTypeCore μ envC F (R.g.pre.length + x.nF + ihs.length) rest = .ok t) ∧
      Expr.WScoped (R.g.pre.length + x.nF + ihs.length) rest ∧ rest.looseBVarsBounded 0 = true ∧
      (∀ l, (l ∈ rest.fvarLeaves ∨ ∃ y ∈ xs', l ∈ y.fvarLeaves) →
        Expr.fvar l.1 l.2 ∈ fvs1.take R.g.pre.length ++ xs') := by
  obtain ⟨cls, s, x, T, res, ws, ihs, hgc, hgx, hms, hxmem, hMaj, ⟨ihs0, hsS⟩, hpreT, hTs, hrP,
    hopR, hCB, hnF, hcv, hwsR, hihl, hih, ⟨sc, hmc, hscl⟩, hTE⟩ := genMinorSetup R hg h hfind hc hj
  have hr : (tgtRs out)[c]? = some ((tgtRs out)[c]'hc) := List.getElem?_eq_getElem hc
  have hpl : R.g.pre.length = R.g.nP + R.g.slots.length :=
    (ConLeche.ClassGen.prefixBinders_scoped hg hg.pre).1
  have hsl : s < R.g.slots.length := (List.getElem?_eq_some_iff.mp hsS).1
  have hmp : R.g.nP + s < R.g.pre.length := by omega
  -- the stored type's openers
  obtain ⟨cls', ty', ifs', body', -, -, -, -, -, -, -, -, -, -, fvs0, o0, hop0, hE⟩ :=
    genRun_binders hμ R hg h mpC ψ hc
  obtain ⟨fvs1, concl1, hop1, -, hTyE, hlenRds, -, hdomsR, -, hwdTy⟩ :=
    recStage_tyPis (V := V) hμ mpC h hr ψ
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hop1.symm.trans hop0))
  have hle := blockRecHrPle (p := pp) h hc
  have hlenF : fvs1.length = pp.toBlockShape.majorIdxAt c + 1 :=
    ConLeche.Verify.openPisAtFvars_length _ hop1
  obtain ⟨hw0, hb0⟩ := recStage_tyClosed h hr
  have hwsF := (openPisAtFvars_WScoped _ _ 0 hop1 hw0).1
  have hbF := (ConLeche.Verify.openPisAtFvars_bounded _ hop1 hb0).2
  have hshF : ∀ (i : Nat) (y : Expr), fvs1[i]? = some y → ∃ ty, y = Expr.fvar i ty := by
    intro i y hy
    obtain ⟨ty, hty⟩ := openPisAtFvars_index _ _ 0 hop1 i y hy
    exact ⟨ty, by simpa using hty⟩
  have hlenPd := blockRulePdomsAV_length (V := V) hμ mpC h hr ψ
  have hPd : ∀ (i : Nat) (y : Expr), i < R.g.pre.length → fvs1[i]? = some y →
      denoteMeta mpC.base2.acval envC ψ i (Expr.fvarTypeD y)
        = some ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).getD i
            default) := by
    intro i y hi hy
    obtain ⟨pd, hpd, -, hrd⟩ := hdomsR i y hy
    rw [hrd, blockRulePdomsAV, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take,
      if_pos (by rw [hrP]; exact hi), hpd]
    rfl
  -- the minor's entry: erasure-equal to the generator's, inferred at its slot
  obtain ⟨y, hy⟩ : ∃ y, fvs1[R.g.nP + s]? = some y :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hyE := hE _ y T hy (by
    rw [List.append_assoc, List.getElem?_append_left (by omega), hpreT]; rfl)
  obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.recStageG_tyGen h hr
  obtain ⟨stype, -, hinfT, -⟩ := TE.hcv.sorted
  obtain ⟨tT, htT⟩ := inferTypeCore_openPis_dom hμ hop1 hinfT (R.g.nP + s) y hy
  rw [Nat.zero_add] at htT
  have hwsY : Expr.WScoped (R.g.nP + s) (Expr.fvarTypeD y) := by
    have := openPisAtFvars_typeWScoped _ hop1 hw0 (R.g.nP + s) y hy
    rwa [Nat.zero_add] at this
  have htT' : ConLeche.inferTypeCore μ envC F R.g.pre.length (Expr.fvarTypeD y) = .ok tT := by
    rw [ConLeche.inferTypeCore_depth_inv mpC.base2.wf F
      (Expr.WScoped.to_wscopedB (hwsY.mono (by omega)))
      (Expr.WScoped.to_wscopedB hwsY)]
    exact htT
  -- the generator's pieces are scoped and bounded
  obtain ⟨hfl, hfvsS, hresS⟩ := ConLeche.ScB.openPis hopR
    ((hg.tyD cls x hxmem).mono (by omega))
  have hwsS : ∀ i, i < x.nF → ConLeche.ScB (R.g.pre.length + x.nF) (ws.getD i default) :=
    fun i hi => ConLeche.ScB.targetPiDomsWith_getD hwsR
      ((hg.tyN cls x hxmem).mono (by omega)) (fun a ha => by
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
        obtain ⟨ty, hxe, hty⟩ := hfvsS k _ (List.getElem?_eq_getElem hk)
        rw [hxe]; exact ConLeche.ScB.fvar (by omega) hty) (by omega)
  have hihS : ∀ l ty bm', ihs[l]? = some (ty, bm') →
      ConLeche.ScB (R.g.pre.length + x.nF + l) ty := by
    intro l ty bm' hl
    have hl' : l < x.recs.length := by
      rw [← hihl]; exact (List.getElem?_eq_some_iff.mp hl).1
    obtain ⟨⟨i, t, tele⟩, hq⟩ : ∃ q, x.recs[l]? = some q :=
      ⟨_, List.getElem?_eq_getElem hl'⟩
    obtain ⟨⟨ty', hty', hl2⟩, -, -, st, hst, hstl⟩ := hih l i t tele hq
    rw [hl] at hl2
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hl2)
    obtain ⟨hiF, -⟩ := ConLeche.ClassGen.recs_mem (List.mem_of_getElem? hq)
    have hi : i < (tgtFieldFvs pp.toBlockShape out c j).length := by rw [hfl]; exact hiF
    obtain ⟨tyf, hxe, htyf⟩ := hfvsS i _ (List.getElem?_eq_getElem hi)
    refine genIhTy_scb hst (by omega) ((hwsS i hiF).mono (by omega)) ?_ hty'
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, hxe]
    exact ConLeche.ScB.fvar (by omega) (htyf.mono (by omega))
  have hcl : ∀ p ∈ (tgtFieldFvs pp.toBlockShape out c j).map R.g.binder ++ ihs,
      p.1.looseBVarsBounded 0 = true := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hp
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy'
      obtain ⟨ty, hxe, hty⟩ := hfvsS k _ (List.getElem?_eq_getElem hk)
      rw [hxe]; exact hty.2
    · obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hp
      exact (hihS l _ _ (List.getElem?_eq_getElem hl)).2
  have hbbS : ConLeche.ScB (R.g.pre.length + x.nF)
      (Expr.mkAppN (R.g.motVar cls) (res.getAppArgs.drop (R.g.cls.getD cls default).nPc ++
        [Expr.mkAppN (.const x.cv.name (R.g.cls.getD cls default).lvls)
          ((R.g.cls.getD cls default).ds ++ tgtFieldFvs pp.toBlockShape out c j)])) := by
    rw [ConLeche.ClassGen.motVar_eq hmc]
    refine ConLeche.ScB.mkAppN (ConLeche.ScB.fvar (by omega) (ConLeche.ScB.sort _ _))
      fun a ha => ?_
    rcases List.mem_append.mp ha with ha | ha
    · exact ConLeche.ScB.getAppArgs hresS a (List.mem_of_mem_drop ha)
    · simp only [List.mem_singleton] at ha
      subst ha
      refine ConLeche.ScB.mkAppN (ConLeche.ScB.const _ _ _) fun b hb => ?_
      rcases List.mem_append.mp hb with hb | hb
      · exact (hg.ds cls b hb).mono (by omega)
      · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
        obtain ⟨ty, hxe, hty⟩ := hfvsS k _ (List.getElem?_eq_getElem hk)
        rw [hxe]; exact ConLeche.ScB.fvar (by omega) (hty.mono (by omega))
  -- open the entry at the rule prefix
  obtain ⟨xs', rest, hop', hrest, hdoms'⟩ := open_of_erasedEq_closeTelescope _ R.g.pre.length _
    (Expr.fvarTypeD y) hcl hbbS.2 (by rw [← hTE]; exact hyE)
  have hxl' : xs'.length = x.nF + ihs.length := by
    rw [ConLeche.Verify.openPisAtFvars_length _ hop']; simp [hfl]
  rw [show ((tgtFieldFvs pp.toBlockShape out c j).map R.g.binder ++ ihs).length
    = x.nF + ihs.length by simp [hfl]] at hop'
  have hwsY' : Expr.WScoped R.g.pre.length (Expr.fvarTypeD y) := hwsY.mono (by omega)
  obtain ⟨hwsX', hwsR'⟩ := openPisAtFvars_WScoped _ _ _ hop' hwsY'
  have hbY : (Expr.fvarTypeD y).looseBVarsBounded 0 = true := hbF y (List.mem_of_getElem? hy)
  obtain ⟨hbR', hbX'⟩ := ConLeche.Verify.openPisAtFvars_bounded _ hop' hbY
  have hshX : ∀ (k : Nat) (z : Expr), xs'[k]? = some z →
      ∃ ty, z = Expr.fvar (R.g.pre.length + k) ty :=
    fun k z hz => openPisAtFvars_index _ _ _ hop' k z hz
  have hinfX := inferTypeCore_openPis_dom hμ hop' htT'
  have hinfR : ∃ t, ConLeche.inferTypeCore μ envC F (R.g.pre.length + x.nF + ihs.length) rest
      = .ok t := by
    rcases Nat.eq_zero_or_pos (x.nF + ihs.length) with h0 | hpos
    · rw [h0] at hop'
      simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop'
      obtain ⟨-, rfl⟩ := hop'
      exact ⟨tT, by rw [Nat.add_assoc, h0, Nat.add_zero]; exact htT'⟩
    · obtain ⟨k, hk⟩ : ∃ k, x.nF + ihs.length = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
      rw [hk] at hop'
      obtain ⟨bt, -, hbt, -⟩ := inferTypeCore_openPis_body hμ k hop' htT'
      exact ⟨bt, by rw [Nat.add_assoc, hk]; exact hbt⟩
  -- leaves
  have hnil : ((tgtRs out)[c]'hc).1.type.fvarLeaves = [] := fvarLeaves_nil_of_wscoped_zero hw0
  have hleafY : ∀ l ∈ (Expr.fvarTypeD y).fvarLeaves,
      Expr.fvar l.1 l.2 ∈ fvs1.take R.g.pre.length := by
    intro l hl
    have hmem : Expr.fvar l.1 l.2 ∈ fvs1 := by
      rcases openPisAtFvars_leaves _ hop1 l (Or.inr ⟨y, List.mem_of_getElem? hy, by
        obtain ⟨ty, rfl⟩ := hshF _ y hy
        simp only [Expr.fvarLeaves, Expr.fvarTypeD] at hl ⊢
        exact List.mem_cons_of_mem _ hl⟩) with h' | h'
      · rw [hnil] at h'; exact nomatch h'
      · exact h'
    obtain ⟨pos, hpos⟩ := List.getElem?_of_mem hmem
    obtain ⟨ty', hty'⟩ := hshF pos _ hpos
    have h1 : l.1 = pos := by injection hty'
    have hlt : l.1 < R.g.nP + s := Expr.fvarLeaves_lt_of_wscoped hwsY l hl
    have hpt : (fvs1.take R.g.pre.length)[pos]? = some (Expr.fvar l.1 l.2) := by
      rw [List.getElem?_take, if_pos (by omega)]; exact hpos
    exact List.mem_of_getElem? hpt
  have hleafs : ∀ l, (l ∈ rest.fvarLeaves ∨ ∃ z ∈ xs', l ∈ z.fvarLeaves) →
      Expr.fvar l.1 l.2 ∈ fvs1.take R.g.pre.length ++ xs' := by
    intro l hl
    rcases openPisAtFvars_leaves _ hop' l hl with h' | h'
    · exact List.mem_append_left _ (hleafY l h')
    · exact List.mem_append_right _ h'
  refine ⟨cls, s, x, res, ws, ihs, fvs1, _, xs', rest, hgc, hgx, hms, hxmem, hMaj, hrP, hmp,
    hopR, hCB, hnF, hcv, hwsR, hihl, hih, ⟨sc, hmc, hscl⟩, hop1, by rw [← hrP]; exact hle, hlenF,
    hshF, fun z hz => ⟨by simpa using hwsF z hz, hbF z hz⟩, hPd, hxl', hshX,
    fun z hz => ⟨by rw [Nat.add_assoc]; exact hwsX' z hz, hbX' z hz⟩, ?_, ?_, hrest, hbbS, hinfX,
    hinfR, by rw [Nat.add_assoc]; exact hwsR', hbR', hleafs⟩
  · intro k z hk hz
    have hkf : k < (tgtFieldFvs pp.toBlockShape out c j).length := by rw [hfl]; exact hk
    have := hdoms' k z _ hz (by
      rw [List.getElem?_append_left (by simpa using hkf), List.getElem?_map,
        List.getElem?_eq_getElem hkf]; rfl)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkf]
    simpa [ClassGen.binder] using this
  · intro l z hz
    have hl : l < ihs.length := by
      have := (List.getElem?_eq_some_iff.mp hz).1; omega
    have := hdoms' (x.nF + l) z _ hz (by
      rw [List.getElem?_append_right (by simp [hfl]), List.length_map, hfl,
        Nat.add_sub_cancel_left, List.getElem?_eq_getElem hl]; rfl)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
    exact this

/-- A leaf of a positional opener list below `b + n` is among its first `n`. -/
theorem mem_take_of_fvar_lt {L : List Expr} {b n : Nat}
    (hsh : ∀ (k : Nat) (y : Expr), L[k]? = some y → ∃ ty, y = Expr.fvar (b + k) ty)
    {l : Nat × Expr} (hm : Expr.fvar l.1 l.2 ∈ L) (hlt : l.1 < b + n) :
    Expr.fvar l.1 l.2 ∈ L.take n := by
  obtain ⟨pos, hpos⟩ := List.getElem?_of_mem hm
  obtain ⟨ty, hty⟩ := hsh pos _ hpos
  have h1 : l.1 = b + pos := by injection hty
  have hpt : (L.take n)[pos]? = some (Expr.fvar l.1 l.2) := by
    rw [List.getElem?_take, if_pos (by omega)]; exact hpos
  exact List.mem_of_getElem? hpt

set_option maxHeartbeats 8000000 in
/-- **The rule frame is a graded frame of openers**: the stored type's
prefix openers, then the minor premise's field openers at the rule prefix
(`genMinorOpen`'s data), over the rule frame's domains. -/
theorem genFieldFrame (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR) (mpC : EnvModelM V μ envC)
    (hfind : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat), r.2.2.2[i]? = some cA →
        envC.find? cA.1.name = some (.ctorInfo cA.1 (ConLeche.tgtMajorsOf out j).nPc cA.2))
    (ψ : Name → Nat) {c j : Nat} (hc : c < (tgtRs out).length)
    (hj : j < blockRecNCt (tgtRs out) c) {x : ClassCtor} {res : Expr}
    {ihs : List (Expr × BinderMeta)} {fvs1 xs' : List Expr} {rest : Expr}
    (hrP : pp.toBlockShape.rulePrefixAt c = R.g.pre.length)
    (hopR : ConLeche.openPisAtFvars x.nF x.tyD R.g.pre.length
        = some (tgtFieldFvs pp.toBlockShape out c j, res))
    (hle : R.g.pre.length ≤ pp.toBlockShape.majorIdxAt c)
    (hlenF : fvs1.length = pp.toBlockShape.majorIdxAt c + 1)
    (hshF : ∀ (i : Nat) (y : Expr), fvs1[i]? = some y → ∃ ty, y = Expr.fvar i ty)
    (hwbF : ∀ y ∈ fvs1, Expr.WScoped (pp.toBlockShape.majorIdxAt c + 1) y ∧
        (Expr.fvarTypeD y).looseBVarsBounded 0 = true)
    (hPd : ∀ (i : Nat) (y : Expr), i < R.g.pre.length → fvs1[i]? = some y →
        denoteMeta mpC.base2.acval envC ψ i (Expr.fvarTypeD y)
          = some ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).getD i
              default))
    (hxl' : xs'.length = x.nF + ihs.length)
    (hshX : ∀ (k : Nat) (y : Expr), xs'[k]? = some y → ∃ ty, y = Expr.fvar (R.g.pre.length + k) ty)
    (hwbX : ∀ y ∈ xs', Expr.WScoped (R.g.pre.length + x.nF + ihs.length) y ∧
        (Expr.fvarTypeD y).looseBVarsBounded 0 = true)
    (hdF : ∀ (k : Nat) (y : Expr), k < x.nF → xs'[k]? = some y →
        Expr.ErasedEq (Expr.fvarTypeD y)
          (Expr.fvarTypeD ((tgtFieldFvs pp.toBlockShape out c j).getD k default)))
    (hinfX : ∀ (k : Nat) (y : Expr), xs'[k]? = some y →
        ∃ t, ConLeche.inferTypeCore μ envC F (R.g.pre.length + k) (Expr.fvarTypeD y) = .ok t)
    (hleafs : ∀ l, (l ∈ rest.fvarLeaves ∨ ∃ y ∈ xs', l ∈ y.fvarLeaves) →
        Expr.fvar l.1 l.2 ∈ fvs1.take R.g.pre.length ++ xs') :
    GradedFrame mpC ψ (R.g.pre.length + x.nF)
      (fvs1.take R.g.pre.length ++ xs'.take x.nF)
      (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
        ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) := by
  have hr : (tgtRs out)[c]? = some ((tgtRs out)[c]'hc) := List.getElem?_eq_getElem hc
  generalize hPd0 : blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c = pdoms
    at hPd ⊢
  generalize hFd0 : tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j = fdoms
  have hlenPd : pdoms.length = R.g.pre.length := by
    rw [← hPd0, blockRulePdomsAV_length hμ mpC h hr ψ, hrP]
  have hfl : (tgtFieldFvs pp.toBlockShape out c j).length = x.nF :=
    ConLeche.Verify.openPisAtFvars_length _ hopR
  have hlenFd : fdoms.length = x.nF := by
    rw [← hFd0, tgtFdomsAV, readOpenedDoms_length_eq, hfl]
  -- the frame
  let fr : List Expr := fvs1.take R.g.pre.length ++ xs'.take x.nF
  have hfrl : fr.length = R.g.pre.length + x.nF := by
    simp only [fr, List.length_append, List.length_take, hlenF, hxl']; omega
  have hfrE : ∀ (i : Nat) (z : Expr), fr[i]? = some z →
      (i < R.g.pre.length ∧ fvs1[i]? = some z) ∨
        (R.g.pre.length ≤ i ∧ i - R.g.pre.length < x.nF ∧ xs'[i - R.g.pre.length]? = some z) := by
    intro i z hz
    simp only [fr] at hz
    rcases Nat.lt_or_ge i R.g.pre.length with hi | hi
    · rw [List.getElem?_append_left (by simp [hlenF]; omega), List.getElem?_take,
        if_pos hi] at hz
      exact Or.inl ⟨hi, hz⟩
    · rw [List.getElem?_append_right (by simp [hlenF]; omega),
        show (fvs1.take R.g.pre.length).length = R.g.pre.length by simp [hlenF]; omega,
        List.getElem?_take] at hz
      split at hz
      · exact Or.inr ⟨hi, by omega, hz⟩
      · exact nomatch hz
  have hshape : ∀ (i : Nat) (z : Expr), fr[i]? = some z → ∃ ty, z = Expr.fvar i ty := by
    intro i z hz
    rcases hfrE i z hz with ⟨-, hz⟩ | ⟨hi, -, hz⟩
    · exact hshF i z hz
    · obtain ⟨ty, hty⟩ := hshX _ z hz
      exact ⟨ty, by rw [hty, show R.g.pre.length + (i - R.g.pre.length) = i by omega]⟩
  have hwsfr : ∀ z ∈ fr, Expr.WScoped (R.g.pre.length + x.nF) z := by
    intro z hz
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hz
    obtain ⟨ty, rfl⟩ := hshape i z hi
    have hil : i < R.g.pre.length + x.nF := by
      have := (List.getElem?_eq_some_iff.mp hi).1; omega
    rcases hfrE i _ hi with ⟨-, hz'⟩ | ⟨-, -, hz'⟩
    · have := (hwbF _ (List.mem_of_getElem? hz')).1
      simp only [Expr.WScoped] at this ⊢
      exact ⟨hil, this.2⟩
    · have := (hwbX _ (List.mem_of_getElem? hz')).1
      simp only [Expr.WScoped] at this ⊢
      exact ⟨hil, this.2⟩
  have hlbfr : ∀ z ∈ fr, (Expr.fvarTypeD z).looseBVarsBounded 0 = true := by
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact (hwbF z (List.mem_of_mem_take hz)).2
    · exact (hwbX z (List.mem_of_mem_take hz)).2
  have hdomsfr : ∀ (i : Nat) (z : Expr), fr[i]? = some z →
      denoteMeta mpC.base2.acval envC ψ i (Expr.fvarTypeD z)
        = some ((pdoms ++ fdoms).getD i default) := by
    intro i z hz
    rcases hfrE i z hz with ⟨hi, hz'⟩ | ⟨hi, hk, hz'⟩
    · rw [hPd i z hi hz']
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (show i < pdoms.length by omega)]
    · generalize hk' : i - R.g.pre.length = k at hk hz'
      obtain rfl : i = R.g.pre.length + k := by omega
      -- the field type reads (it is inferred), as the rule frame's field domain
      obtain ⟨tk, htk⟩ := hinfX k z hz'
      have hwk : Expr.WScoped (R.g.pre.length + k) (Expr.fvarTypeD z) := by
        obtain ⟨ty, rfl⟩ := hshX k z hz'
        have := (hwbX _ (List.mem_of_getElem? hz')).1
        simp only [Expr.WScoped, Expr.fvarTypeD] at this ⊢
        exact this.2
      have hbk := (hwbX _ (List.mem_of_getElem? hz')).2
      have hLk : Expr.LeavesBounded (Expr.fvarTypeD z) := fun l hl => by
        have hm := hleafs l (Or.inr ⟨z, List.mem_of_getElem? hz', by
          obtain ⟨ty, rfl⟩ := hshX k z hz'
          simp only [Expr.fvarLeaves, Expr.fvarTypeD] at hl ⊢
          exact List.mem_cons_of_mem _ hl⟩)
        rcases List.mem_append.mp hm with hm | hm
        · have := (hwbF _ (List.mem_of_mem_take hm)).2
          simpa [Expr.fvarTypeD] using this
        · have := (hwbX _ hm).2
          simpa [Expr.fvarTypeD] using this
      obtain ⟨a, ha⟩ := acceptedReads_of mpC.base2 ψ htk hwk hbk hLk
      have hkf : k < (tgtFieldFvs pp.toBlockShape out c j).length := by rw [hfl]; exact hk
      have hE := hdF k z hk hz'
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkf, Option.getD_some] at hE
      have hrd := readOpenedDoms_getElem (acval := mpC.base2.acval) (env := envC) (ψ := ψ)
        R.g.pre.length _ k hkf
      rw [ha, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlenPd,
        Nat.add_sub_cancel_left, ← hFd0]
      rw [← denoteMeta_erasedEq hE, ha] at hrd
      simp only [tgtFdomsAV, tgtRP] at hrd ⊢
      have hrP' : (pp.recs.getD c default).rP = R.g.pre.length := hrP
      rw [hrP', List.getElem?_eq_getElem (by simpa using hkf), hrd]
      rfl
  have hok : ∀ l, l < R.g.pre.length + x.nF → ∀ (σ : Nat → V) (zs : List V),
      SpineFit σ ((pdoms ++ fdoms).take l) zs →
      WellDenotedV V (consList zs σ) ((pdoms ++ fdoms).getD l default) := by
    intro l hl σ zs hzs
    have := genCls_frameV hμ R hg h mpC hfind ψ hc hj l (by
      rw [List.length_append, blockRulePdomsAV_length hμ mpC h hr ψ, hrP, tgtFdomsAV,
        readOpenedDoms_length_eq, hfl]; exact hl) σ zs (by rw [hPd0, hFd0]; exact hzs)
    rwa [hPd0, hFd0] at this
  have hDl : (pdoms ++ fdoms).length = R.g.pre.length + x.nF := by
    rw [List.length_append, hlenPd, hlenFd]
  exact ⟨hDl, hfrl, hshape, hwsfr, hlbfr, hdomsfr, hok⟩

set_option maxHeartbeats 8000000 in
/-- **The declared index expressions and the fired spine are graded** at
every spine fitting the rule frame (`hargs` of the family premise; the
validity half of `hrowV`): each is erasure-equal to an argument of the
minor premise's conclusion, which the stored type's inference infers. -/
theorem genArgs_graded (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR) (mpC : EnvModelM V μ envC)
    (hfind : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat), r.2.2.2[i]? = some cA →
        envC.find? cA.1.name = some (.ctorInfo cA.1 (ConLeche.tgtMajorsOf out j).nPc cA.2))
    (ψ : Name → Nat) (ρ : Nat → V) {c j : Nat} (hc : c < (tgtRs out).length)
    (hj : j < blockRecNCt (tgtRs out) c) (ys : List V)
    (hys : SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
      ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) ys) :
    (∀ e ∈ tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j,
      WellDenotedV V (consList ys ρ) e) ∧
    WellDenotedV V (consList ys ρ) (tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ c j) := by
  obtain ⟨cls, s, x, res, ws, ihs, fvs1, o1, xs', rest, hgc, hgx, hms, hxmem, hMaj, hrP, hmp,
    hopR, hCB, hnF, hcv, hwsR, hihl, hih, -, hop1, hle, hlenF, hshF, hwbF, hPd, hxl', hshX,
    hwbX, hdF, -, hrest, hbbS, hinfX, ⟨tR, hinfR⟩, hwsRest, hbRest, hleafs⟩ :=
    genMinorOpen hμ R hg h mpC hfind ψ hc hj
  have G := genFieldFrame hμ R hg h mpC hfind ψ hc hj hrP hopR hle hlenF hshF hwbF hPd hxl' hshX
    hwbX hdF hinfX hleafs
  -- one argument of the conclusion, graded
  have hconcl := hrest
  obtain ⟨f', as', hrE, -, hasl⟩ := erasedEq_mkAppN_inv _ hconcl
  rw [hrE] at hconcl hinfR hwsRest hbRest hleafs
  obtain ⟨-, hargE⟩ := ConLeche.erasedEq_mkAppN_args _ hasl hconcl
  have harg : ∀ (m : Nat) (a e : Expr), as'[m]? = some a →
      (res.getAppArgs.drop (R.g.cls.getD cls default).nPc ++
        [Expr.mkAppN (.const x.cv.name (R.g.cls.getD cls default).lvls)
          ((R.g.cls.getD cls default).ds ++ tgtFieldFvs pp.toBlockShape out c j)])[m]? = some e →
      ∃ w, denoteMeta mpC.base2.acval envC ψ (R.g.pre.length + x.nF) e = some w ∧
        WellDenotedV V (consList ys ρ) w := by
    intro m a e ha he
    have hEa := hargE m e a he ha
    have haA : a ∈ (Expr.mkAppN f' as').getAppArgs := by
      rw [Expr.getAppArgs_mkAppN]; exact List.mem_append_right _ (List.mem_of_getElem? ha)
    have heS : ConLeche.ScB (R.g.pre.length + x.nF) e :=
      ConLeche.ScB.getAppArgs hbbS e (by
        rw [Expr.getAppArgs_mkAppN]
        exact List.mem_append_right _ (List.mem_of_getElem? he))
    have hwa : Expr.WScoped (R.g.pre.length + x.nF) a :=
      WScoped.of_erasedEq a hEa (wscoped_of_getAppArgs hwsRest a haA) heS.1
    have hba : a.looseBVarsBounded 0 = true := looseBVarsBounded_getAppArgs hbRest a haA
    obtain ⟨ta, hta⟩ := ConLeche.inferTypeCore_mkAppN_args as' hinfR a (List.mem_of_getElem? ha)
    have hta' : ConLeche.inferTypeCore μ envC F (R.g.pre.length + x.nF) a = .ok ta := by
      rw [ConLeche.inferTypeCore_depth_inv mpC.base2.wf F (Expr.WScoped.to_wscopedB hwa)
        (Expr.WScoped.to_wscopedB (hwa.mono
          (show R.g.pre.length + x.nF ≤ R.g.pre.length + x.nF + ihs.length by omega)))]
      exact hta
    have hleafA : ∀ l ∈ a.fvarLeaves,
        Expr.fvar l.1 l.2 ∈ fvs1.take R.g.pre.length ++ xs'.take x.nF := by
      intro l hl
      have hm := hleafs l (Or.inl (fvarLeaves_getAppArgs haA l hl))
      have hlt : l.1 < R.g.pre.length + x.nF := Expr.fvarLeaves_lt_of_wscoped hwa l hl
      rcases List.mem_append.mp hm with hm | hm
      · exact List.mem_append_left _ hm
      · exact List.mem_append_right _ (mem_take_of_fvar_lt hshX hm hlt)
    obtain ⟨w, hw, hgr⟩ := G.graded hμ hta' hwa hba hleafA
    exact ⟨w, by rw [denoteMeta_erasedEq hEa] at hw; exact hw, hgr ρ ys hys⟩
  have hB : tgtB pp.toBlockShape out c j = R.g.pre.length + x.nF := by
    simp only [tgtB, tgtRP]
    have hrP' : (pp.recs.getD c default).rP = R.g.pre.length := hrP
    rw [hrP', hnF]
  have hnpc : (tgtMajor out c).nPc = (R.g.cls.getD cls default).nPc := by rw [hMaj]
  have hlenA : as'.length = (res.getAppArgs.drop (R.g.cls.getD cls default).nPc).length + 1 := by
    rw [hasl]; simp
  refine ⟨fun e he => ?_, ?_⟩
  · rw [tgtEsAV, hCB, hnpc, hB] at he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem he0
    obtain ⟨a, ha⟩ : ∃ a, as'[m]? = some a := ⟨_, List.getElem?_eq_getElem (by rw [hlenA]; omega)⟩
    obtain ⟨w, hw, hg'⟩ := harg m a _ ha (by
      rw [List.getElem?_append_left hm, List.getElem?_eq_getElem hm])
    rw [hw]; exact hg'
  · have hm := (res.getAppArgs.drop (R.g.cls.getD cls default).nPc).length
    obtain ⟨a, ha⟩ : ∃ a, as'[(res.getAppArgs.drop (R.g.cls.getD cls default).nPc).length]?
        = some a := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨w, hw, hg'⟩ := harg _ a _ ha (by
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl)
    rw [tgtMkAV, hB, show (tgtCtorOf out c j).1.name = x.cv.name by rw [hcv], hMaj, hw]
    exact hg'

theorem readOpenedDoms_congr_erasedEq {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {ψ : Name → Nat} :
    ∀ (d : Nat) (zs xs : List Expr), zs.length = xs.length →
      (∀ (k : Nat) (z x : Expr), zs[k]? = some z → xs[k]? = some x →
        Expr.ErasedEq (Expr.fvarTypeD z) (Expr.fvarTypeD x)) →
      readOpenedDoms acval env ψ d zs = readOpenedDoms acval env ψ d xs
  | _, [], [], _, _ => rfl
  | d, z :: zs, x :: xs, hl, h => by
    simp only [readOpenedDoms]
    rw [denoteMeta_erasedEq (h 0 z x rfl rfl),
      readOpenedDoms_congr_erasedEq (d + 1) zs xs (by simpa using hl)
        (fun k z' x' hz hx => h (k + 1) z' x' (by simpa using hz) (by simpa using hx))]
  | _, [], _ :: _, hl, _ => by simp at hl
  | _, _ :: _, [], hl, _ => by simp at hl

theorem denoteMetaSpine_of_some {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {d : Nat} :
    ∀ (as : List Expr), (∀ a ∈ as, ∃ v, denoteMeta acval env φ d a = some v) →
      DenoteMetaSpine acval env φ d as (as.map fun a => (denoteMeta acval env φ d a).getD default)
  | [], _ => .nil
  | a :: as, h => by
    obtain ⟨v, hv⟩ := h a List.mem_cons_self
    refine .cons (by simp only [hv, Option.getD_some]) (denoteMetaSpine_of_some as fun b hb =>
      h b (List.mem_cons_of_mem _ hb))

theorem genIhdAV_length' {acval : Name → (Name → Nat) → AnnotTerm} {env : Env} {g : ClassGen}
    {rd : ClassRead} {bit : Nat} {ψ : Name → Nat} {c j : Nat} :
    (genIhdAV acval env g rd bit ψ c j).length = (genCtorAt g rd c j).recs.length := by
  simp [genIhdAV]

set_option maxHeartbeats 16000000 in
/-- **The `l`-th inductive hypothesis of `(c, j)`, opened at the rule
frame**: the rule frame extended by the `ih`'s telescope is a graded
frame of openers (its domains the `ih` datum's telescope), over which the
`ih`'s index arguments, applied field, and its motive application are
graded — all from the stored type's inference of the `ih` binder. -/
theorem genIhFrame (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR) (mpC : EnvModelM V μ envC)
    (hfind : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat), r.2.2.2[i]? = some cA →
        envC.find? cA.1.name = some (.ctorInfo cA.1 (ConLeche.tgtMajorsOf out j).nPc cA.2))
    (ψ : Name → Nat) {c j : Nat} (hc : c < (tgtRs out).length)
    (hj : j < blockRecNCt (tgtRs out) c) {bit l : Nat} {q : IhDatum}
    (hql : (genIhdAV mpC.base2.acval envC R.g R.rd bit ψ c j)[l]? = some q) :
    ∃ (t st : Nat) (fr : List Expr),
      q.1 = genRecIdx R.rd t ∧ ConLeche.ClassRead.motiveSlot ⟨R.g.slots, []⟩ t = some st ∧
      R.g.nP + st < R.g.pre.length ∧
      GradedFrame mpC ψ (R.g.pre.length + (genCtorAt R.g R.rd c j).nF + q.2.1.length) fr
        (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
          ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j ++ q.2.1.map (·.2)) ∧
      (∀ e ∈ q.2.2.1 ++ [q.2.2.2], ∀ (σ : Nat → V) (ys : List V),
        SpineFit σ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
          ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j ++ q.2.1.map (·.2)) ys →
        WellDenotedV V (consList ys σ) e) ∧
      (∀ (σ : Nat → V) (ys : List V),
        SpineFit σ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
          ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j ++ q.2.1.map (·.2)) ys →
        WellDenotedV V (consList ys σ)
          (AnnotTerm.mkAppN (.bvar (R.g.pre.length + (genCtorAt R.g R.rd c j).nF + q.2.1.length
              - 1 - (R.g.nP + st)))
            (q.2.2.1 ++ [q.2.2.2]))) := by
  obtain ⟨cls, s, x, res, ws, ihs, fvs1, o1, xs', rest, hgc, hgx, hms, hxmem, hMaj, hrP, hmp,
    hopR, hCB, hnF, hcv, hwsR, hihl, hih, -, hop1, hle, hlenF, hshF, hwbF, hPd, hxl', hshX,
    hwbX, hdF, hdIh, hrest, hbbS, hinfX, -, hwsRest, hbRest, hleafs⟩ :=
    genMinorOpen hμ R hg h mpC hfind ψ hc hj
  have G := genFieldFrame hμ R hg h mpC hfind ψ hc hj hrP hopR hle hlenF hshF hwbF hPd hxl' hshX
    hwbX hdF hinfX hleafs
  subst hgx
  -- the `ih` datum
  have hll : l < (genCtorAt R.g R.rd c j).recs.length := by
    have := (List.getElem?_eq_some_iff.mp hql).1
    rwa [genIhdAV_length'] at this
  obtain ⟨⟨i, t, tele⟩, hrec⟩ : ∃ r, (genCtorAt R.g R.rd c j).recs[l]? = some r :=
    ⟨_, List.getElem?_eq_getElem hll⟩
  obtain ⟨⟨ty, hty, hihsl⟩, -, ⟨xs, idx, hip⟩, st, hst, hstl⟩ := hih l i t tele hrec
  have hq := genIhdAV_getElem (acval := mpC.base2.acval) (env := envC) (bit := bit) (ψ := ψ)
    hrec hopR hwsR hip
  rw [hql] at hq
  obtain rfl := Option.some.inj hq
  generalize hD : R.g.pre.length + (genCtorAt R.g R.rd c j).nF = D at G hip hty ⊢
  have hiF : i < (genCtorAt R.g R.rd c j).nF :=
    (ConLeche.ClassGen.recs_mem (List.mem_of_getElem? hrec)).1
  obtain ⟨hfl, hfvsS, hresS⟩ := ConLeche.ScB.openPis hopR
    ((hg.tyD cls _ hxmem).mono (by omega))
  have hi : i < (tgtFieldFvs pp.toBlockShape out c j).length := by rw [hfl]; exact hiF
  have hwsS : ConLeche.ScB D (ws.getD i default) := by
    rw [← hD]
    exact ConLeche.ScB.targetPiDomsWith_getD hwsR
      ((hg.tyN cls _ hxmem).mono (by omega)) (fun a ha => by
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
        obtain ⟨ty, hxe, hty⟩ := hfvsS k _ (List.getElem?_eq_getElem hk)
        rw [hxe]; exact ConLeche.ScB.fvar (by omega) hty) (by omega)
  have hfS : ConLeche.ScB D ((tgtFieldFvs pp.toBlockShape out c j).getD i default) := by
    obtain ⟨tyf, hxe, htyf⟩ := hfvsS i _ (List.getElem?_eq_getElem hi)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, hxe]
    exact ConLeche.ScB.fvar (by omega) (htyf.mono (by omega))
  have hstD : R.g.nP + st < D := by omega
  -- the `ih`'s type, as built at the rule frame
  generalize hfE : (tgtFieldFvs pp.toBlockShape out c j).getD i default = f at hfS hty
  have hty0 : R.g.ihTy t tele (ws.getD i default) f D = some (closeTelescope (xs.map R.g.binder) D
      (Expr.mkAppN (R.g.motVar t) (idx ++ [Expr.mkAppN f xs]))) := by
    unfold ClassGen.ihTy
    rw [hip]; rfl
  have hT0S := genIhTy_scb hst hstD hwsS hfS hty0
  have htyE : ty = closeTelescope (xs.map R.g.binder) D
      (Expr.mkAppN (R.g.motVar t) (idx ++ [Expr.mkAppN f xs])) := by
    have := ConLeche.ClassGen.ihTy_depth hwsS.1.fvarsBelow hfS.1.fvarsBelow
      (by rw [hst]; exact hstD) hT0S.1.fvarsBelow hty0 l
    exact Option.some.inj (hty.symm.trans this)
  -- the stored `ih` binder, erasure-equal to it
  have hlI : l < ihs.length := by rw [hihl]; exact hll
  obtain ⟨y, hy⟩ : ∃ y, xs'[(genCtorAt R.g R.rd c j).nF + l]? = some y :=
    ⟨_, List.getElem?_eq_getElem (by rw [hxl']; omega)⟩
  have hyE : Expr.ErasedEq (Expr.fvarTypeD y) (closeTelescope (xs.map R.g.binder) D
      (Expr.mkAppN (R.g.motVar t) (idx ++ [Expr.mkAppN f xs]))) := by
    have := hdIh l y hy
    rwa [List.getD_eq_getElem?_getD, hihsl, Option.getD_some, htyE] at this
  obtain ⟨ty', hyF⟩ := hshX _ y hy
  have hwsY : Expr.WScoped (D + l) (Expr.fvarTypeD y) := by
    have := (hwbX y (List.mem_of_getElem? hy)).1
    rw [hyF] at this ⊢
    simp only [Expr.WScoped, Expr.fvarTypeD] at this ⊢
    rw [← hD]; rw [← Nat.add_assoc] at this; exact this.2
  have hwsYD : Expr.WScoped D (Expr.fvarTypeD y) :=
    WScoped.of_erasedEq _ hyE hwsY hT0S.1
  have hbY : (Expr.fvarTypeD y).looseBVarsBounded 0 = true := (hwbX y (List.mem_of_getElem? hy)).2
  obtain ⟨tY, htY⟩ := hinfX _ y hy
  have htYD : ConLeche.inferTypeCore μ envC F D (Expr.fvarTypeD y) = .ok tY := by
    rw [ConLeche.inferTypeCore_depth_inv mpC.base2.wf F (Expr.WScoped.to_wscopedB hwsYD)
      (Expr.WScoped.to_wscopedB hwsY)]
    rw [← hD]; rw [← Nat.add_assoc] at htY; exact htY
  have hleafY : ∀ l' ∈ (Expr.fvarTypeD y).fvarLeaves,
      Expr.fvar l'.1 l'.2 ∈ fvs1.take R.g.pre.length ++ xs'.take (genCtorAt R.g R.rd c j).nF := by
    intro l' hl'
    have hm := hleafs l' (Or.inr ⟨y, List.mem_of_getElem? hy, by
      rw [hyF] at hl' ⊢
      simp only [Expr.fvarLeaves, Expr.fvarTypeD] at hl' ⊢
      exact List.mem_cons_of_mem _ hl'⟩)
    have hlt : l'.1 < D := Expr.fvarLeaves_lt_of_wscoped hwsYD l' hl'
    rcases List.mem_append.mp hm with hm | hm
    · exact List.mem_append_left _ hm
    · exact List.mem_append_right _ (mem_take_of_fvar_lt hshX hm (by omega))
  -- open it at the rule frame
  obtain ⟨hxsl, hxsS, hidxS⟩ := ConLeche.ClassGen.ihParts_scoped hwsS (Nat.le_refl _) hip
  have hcl : ∀ p ∈ xs.map R.g.binder, p.1.looseBVarsBounded 0 = true := by
    intro p hp
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hp
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hz
    obtain ⟨tz, hxe, htz⟩ := hxsS k _ (List.getElem?_eq_getElem hk)
    rw [hxe]; exact htz.2
  have hbS : ConLeche.ScB (D + tele) (Expr.mkAppN (R.g.motVar t) (idx ++ [Expr.mkAppN f xs])) := by
    rw [ConLeche.ClassGen.motVar_eq hst]
    refine ConLeche.ScB.mkAppN (ConLeche.ScB.fvar (by omega) (ConLeche.ScB.sort _ _))
      fun a ha => ?_
    rcases List.mem_append.mp ha with ha | ha
    · exact hidxS a ha
    · simp only [List.mem_singleton] at ha
      subst ha
      refine ConLeche.ScB.mkAppN (hfS.mono (by omega)) fun b hb => ?_
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
      obtain ⟨tz, hxe, htz⟩ := hxsS k _ (List.getElem?_eq_getElem hk)
      rw [hxe]; exact ConLeche.ScB.fvar (by omega) (htz.mono (by omega))
  obtain ⟨zs, rest2, hopZ, hrest2, hdz⟩ := open_of_erasedEq_closeTelescope _ D _
    (Expr.fvarTypeD y) hcl hbS.2 hyE
  obtain ⟨G2, ⟨tb, hinfB⟩, hwsB, hbB, hleafB⟩ := G.extend hμ hopZ htYD hwsYD hbY hleafY
  have hzl : zs.length = xs.length := by
    rw [ConLeche.Verify.openPisAtFvars_length _ hopZ, List.length_map]
  have hrdE : readOpenedDoms mpC.base2.acval envC ψ D zs
      = readOpenedDoms mpC.base2.acval envC ψ D xs :=
    readOpenedDoms_congr_erasedEq D zs xs hzl fun k z x hz hx => by
      have := hdz k z x.fvarTypeD hz (by rw [List.getElem?_map, hx]; rfl)
      exact this
  -- the conclusion's arguments and the conclusion, graded
  have hq2l : ((readOpenedDoms mpC.base2.acval envC ψ D xs).map fun b => (bit, b)).length
      = (xs.map R.g.binder).length := by simp
  have hmap : ((readOpenedDoms mpC.base2.acval envC ψ D xs).map fun b => (bit, b)).map (·.2)
      = readOpenedDoms mpC.base2.acval envC ψ D zs := by
    rw [hrdE, List.map_map]; exact List.map_id _
  rw [hq2l, hmap]
  have hrest2' := hrest2
  obtain ⟨f2, as2, hr2E, -, has2l⟩ := erasedEq_mkAppN_inv _ hrest2'
  rw [hr2E] at hrest2 hinfB hwsB hbB hleafB
  obtain ⟨-, hargE⟩ := ConLeche.erasedEq_mkAppN_args _ has2l hrest2
  have harg : ∀ (m : Nat) (e : Expr), (idx ++ [Expr.mkAppN f xs])[m]? = some e →
      ∃ w, denoteMeta mpC.base2.acval envC ψ (D + (xs.map R.g.binder).length) e = some w ∧
        ∀ (σ : Nat → V) (ys : List V),
          SpineFit σ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
            ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j
            ++ readOpenedDoms mpC.base2.acval envC ψ D zs) ys →
          WellDenotedV V (consList ys σ) w := by
    intro m e he
    obtain ⟨a, ha⟩ : ∃ a, as2[m]? = some a :=
      ⟨_, List.getElem?_eq_getElem (by rw [has2l]; exact (List.getElem?_eq_some_iff.mp he).1)⟩
    have hEa := hargE m e a he ha
    have haA : a ∈ (Expr.mkAppN f2 as2).getAppArgs := by
      rw [Expr.getAppArgs_mkAppN]; exact List.mem_append_right _ (List.mem_of_getElem? ha)
    obtain ⟨ta, hta⟩ := ConLeche.inferTypeCore_mkAppN_args as2 hinfB a (List.mem_of_getElem? ha)
    obtain ⟨w, hw, hgw⟩ := G2.graded hμ hta (wscoped_of_getAppArgs hwsB a haA)
      (looseBVarsBounded_getAppArgs hbB a haA)
      (fun l' hl' => hleafB l' (fvarLeaves_getAppArgs haA l' hl'))
    exact ⟨w, by rw [denoteMeta_erasedEq hEa] at hw; exact hw, hgw⟩
  have hsome : ∀ e ∈ idx ++ [Expr.mkAppN f xs],
      ∃ v, denoteMeta mpC.base2.acval envC ψ (D + (xs.map R.g.binder).length) e = some v := by
    intro e he
    obtain ⟨m, hm⟩ := List.getElem?_of_mem he
    obtain ⟨w, hw, -⟩ := harg m e hm
    exact ⟨w, hw⟩
  have hbl : (xs.map R.g.binder).length = xs.length := List.length_map _
  refine ⟨t, st, _, rfl, hst, by omega, G2, fun e he σ ys hys => ?_, fun σ ys hys => ?_⟩
  · rw [hbl] at harg
    have he' : e ∈ (idx ++ [Expr.mkAppN f xs]).map fun e =>
        (denoteMeta mpC.base2.acval envC ψ (D + xs.length) e).getD default := by
      rw [List.map_append]; simpa using he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he'
    obtain ⟨m, hm⟩ := List.getElem?_of_mem he0
    obtain ⟨w, hw, hgw⟩ := harg m e0 hm
    rw [hw]
    exact hgw σ ys hys
  · -- the conclusion itself
    obtain ⟨tr, htr⟩ : ∃ tr, ConLeche.inferTypeCore μ envC F (D + (xs.map R.g.binder).length)
        (Expr.mkAppN f2 as2) = .ok tr := ⟨tb, hinfB⟩
    obtain ⟨w, hw, hgw⟩ := G2.graded hμ htr hwsB hbB hleafB
    rw [denoteMeta_erasedEq hrest2, ConLeche.ClassGen.motVar_eq hst,
      denoteMeta_mkAppN (denoteMetaSpine_of_some _ hsome) (denoteMeta_fvar _ _ _ _)] at hw
    obtain rfl := Option.some.inj hw
    have := hgw σ ys hys
    rw [hbl, List.map_append] at this
    simpa using this

end Open

end ConLeche.Model
