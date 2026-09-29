module

public import ConLeche.Model.Inductives.GenClsFrame
import ConLeche.Model.Inductives.GenClsMinor
import ConLeche.Model.Inductives.GenClsSem
import ConLeche.Model.Inductives.GenRecPreRun
import ConLeche.Model.Inductives.GenRecRules
import ConLeche.Model.Inductives.ClassGenRead
import ConLeche.Model.Inductives.ClassRecKit
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.TargetCallKit
import ConLeche.Model.Inductives.BlockRecIdxConv
import ConLeche.Model.Annot.BitShift
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Annot.BitRename
import ConLeche.Verify.Inductives.GenDepth
import ConLeche.Verify.Inductives.ClassGenScope
import ConLeche.Verify.Shift
import ConLeche.Semantics.Tower.TowerKit

public section

/-!
# The generated calls are typed (lane GENREC-CLS)

`GenPreSem.callTy`: an inductive hypothesis's call — its index arguments
and applied field, at a spine fitting its telescope — fits the callee
recursor's index and major domains.  The stored type infers the `ih`
binder `Π a⃗, motive_t e⃗ (f a⃗)`, so the motive application is graded
(`genIhFrame`), and a graded application of a value of a Π-tower fits
the tower (`spineFit_of_wellDenoted_mkAppN_pi`).  The tower is the
motive's type, `Π ı⃗ (t : I D⃗ ı⃗), Sort`, read at the motive's slot; the
callee's index and major domains are the same telescope opened at the
rule prefix — the slot's opening shifted (`openPisAtFvars_shiftIter`),
read lifted past the prefix's later slots (`denoteMeta_shiftIter`).
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

/-! ## Opening deeper: the iterated shift -/

section Shift

/-- `m` shifts from `d`: the variables at and above `d` move up by `m`. -/
@[expose] def shiftIter (d : Nat) : Nat → Expr → Expr
  | 0, e => e
  | m + 1, e => Expr.shiftFrom (d + m) (shiftIter d m e)

theorem shiftIter_eq_self {d : Nat} {e : Expr} (h : Expr.fvarsBelow d e) :
    ∀ m, shiftIter d m e = e
  | 0 => rfl
  | m + 1 => by
    show Expr.shiftFrom (d + m) (shiftIter d m e) = e
    rw [shiftIter_eq_self h m, Expr.shiftFrom_eq_self (Expr.fvarsBelow_mono (by omega) h)]

theorem shiftIter_mkAppN {d : Nat} (f : Expr) (as : List Expr) :
    ∀ m, shiftIter d m (Expr.mkAppN f as) = Expr.mkAppN (shiftIter d m f) (as.map (shiftIter d m))
  | 0 => by simp [shiftIter]
  | m + 1 => by
    show Expr.shiftFrom (d + m) (shiftIter d m (Expr.mkAppN f as)) = _
    rw [shiftIter_mkAppN f as m, Expr.shiftFrom_mkAppN, List.map_map]
    rfl

/-- **An opening at `d`, moved `m` deeper**, is the opening shifted `m`
times, when the telescope is below `d`. -/
theorem openPisAtFvars_shiftIter {n d : Nat} {e : Expr} {fvs : List Expr} {o : Expr}
    (he : Expr.fvarsBelow d e) (h : ConLeche.openPisAtFvars n e d = some (fvs, o)) :
    ∀ m, ConLeche.openPisAtFvars n e (d + m) = some (fvs.map (shiftIter d m), shiftIter d m o)
  | 0 => by simpa [shiftIter] using h
  | m + 1 => by
    have ih := openPisAtFvars_shiftIter he h m
    have := ConLeche.openPisAtFvars_shiftFrom (p := d + m) n (Nat.le_refl _) ih
    rw [Expr.shiftFrom_eq_self (Expr.fvarsBelow_mono (by omega) he), List.map_map] at this
    rw [show d + (m + 1) = d + m + 1 by omega]
    exact this

theorem wscoped_shiftIter {d k : Nat} {e : Expr} (he : Expr.WScoped (d + k) e) :
    ∀ m, Expr.WScoped (d + m + k) (shiftIter d m e)
  | 0 => by simpa [shiftIter] using he
  | m + 1 => by
    have ih := wscoped_shiftIter he m
    show Expr.WScoped (d + (m + 1) + k) (Expr.shiftFrom (d + m) (shiftIter d m e))
    have hb := Expr.wscopedB_shiftFrom (p := d + m) (shiftIter d m e) (d := d + m + k) (by omega)
    rw [Expr.WScoped.to_wscopedB ih] at hb
    rw [show d + (m + 1) + k = d + m + k + 1 by omega]
    exact Expr.WScoped.of_wscopedB hb

/-- **The reading of an `m`-times shifted term** at `m` more binders is
the reading lifted by `m` at the term's own local depth `k`. -/
theorem denoteMeta_shiftIter {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    {d k : Nat} {e : Expr} (he : Expr.WScoped (d + k) e) :
    ∀ m, denoteMeta acval env φ (d + m + k) (shiftIter d m e)
      = (denoteMeta acval env φ (d + k) e).map (AnnotTerm.liftN m · k)
  | 0 => by
    cases h : denoteMeta acval env φ (d + k) e <;> simp [shiftIter, h, AnnotTerm.liftN_zero]
  | m + 1 => by
    have ih := denoteMeta_shiftIter (env := env) (φ := φ) hacl he m
    have hw := wscoped_shiftIter he m
    show denoteMeta acval env φ (d + (m + 1) + k) (Expr.shiftFrom (d + m) (shiftIter d m e)) = _
    rw [show d + (m + 1) + k = d + m + k + 1 by omega,
      denoteMeta_shiftFrom hacl _ _ (by omega) hw, ih,
      show d + m + k - (d + m) = k by omega]
    cases denoteMeta acval env φ (d + k) e with
    | none => rfl
    | some a =>
      simp only [Option.map_some]
      rw [AnnotTerm.liftN_liftN, Nat.add_comm 1 m]

end Shift

/-! ## The motive's type is the callee's index and major telescope -/

section Motive

variable {F : Nat} {env₁ envC : Env} {pp : BlockParts} {nestedBit : Bool} {pos : NestState}
  {cvTas : List ConstantVal} {block : List ConstantInfo}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)}

theorem list_getElem_eq_getD {α : Type} {l : List α} {k : Nat} (h : k < l.length) (d : α) :
    l[k] = l.getD k d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem shiftIter_fvar {d : Nat} (k : Nat) (ty : Expr) :
    ∀ m, shiftIter d m (.fvar (d + k) ty) = .fvar (d + m + k) (shiftIter d m ty)
  | 0 => by simp [shiftIter]
  | m + 1 => by
    show Expr.shiftFrom (d + m) (shiftIter d m (.fvar (d + k) ty)) = _
    rw [shiftIter_fvar k ty m]
    simp only [Expr.shiftFrom, show d + m + k ≥ d + m by omega, if_true]
    rw [show d + m + k + 1 = d + (m + 1) + k by omega]
    rfl

set_option maxHeartbeats 16000000 in
/-- **The motive of class `t`, read in any recursor's prefix, is the
Π-tower of the callee's index and major domains** — those domains
opened at the rule prefix are the tower's opened at the motive's slot,
lifted past the prefix's later slots; every binder numeral is `1`. -/
theorem genMotRds (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR) (mpC : EnvModelM V μ envC)
    (ψ : Name → Nat) {c T t st : Nat} (hc : c < (tgtRs out).length) (hT : T < (tgtRs out).length)
    (hct : genClsOf R.rd T = t)
    (hst : ConLeche.ClassRead.motiveSlot ⟨R.g.slots, []⟩ t = some st) :
    ∃ (pds : List (Nat × Nat × AnnotTerm)) (R0 : AnnotTerm),
      (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).getD
          (R.g.nP + st) default = mkPisAV pds R0 ∧
      (∀ p ∈ pds, p.2.1 ≠ 0) ∧
      ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ T).map (·.2.2)).drop
          R.g.pre.length
        = liftDomsK (R.g.pre.length - (R.g.nP + st)) 0 (pds.map (·.2.2)) := by
  have hrc : (tgtRs out)[c]? = some ((tgtRs out)[c]'hc) := List.getElem?_eq_getElem hc
  have hpl : R.g.pre.length = R.g.nP + R.g.slots.length :=
    (ConLeche.ClassGen.prefixBinders_scoped hg hg.pre).1
  have hsl : st < R.g.slots.length := ConLeche.ClassRead.motiveSlot_lt hst
  generalize hdD : R.g.nP + st = d
  have hdP : d < R.g.pre.length := by omega
  -- the motive's prefix entry
  obtain ⟨hcount, key, hkey⟩ := motiveSlot_count hst
  obtain ⟨Tm, hTm, hpreT⟩ := ConLeche.ClassGen.prefixBinders_motive hg hkey
  rw [hcount, hdD] at hTm
  rw [hdD] at hpreT
  unfold ClassGen.motiveTy at hTm
  obtain ⟨⟨ifsD, majD⟩, hmajD, hTm⟩ := Option.bind_eq_some_iff.mp hTm
  simp only [Option.pure_def, Option.some.injEq] at hTm
  obtain ⟨hifsD, hmajS⟩ := ConLeche.ClassGen.major_scoped hg (by omega) hmajD
  obtain ⟨ty, body, hty, hopD, hmajE⟩ := ConLeche.ClassGen.major_inv hmajD
  -- the caller's stored type: its entry at the motive's slot, read
  obtain ⟨clsc, tyc, ifsc, bodyc, -, -, -, -, -, hRPc, -, -, -, -, fvs0, o0, hop0, hE⟩ :=
    genRun_binders hμ R hg h mpC ψ hc
  obtain ⟨fvs1, concl1, hop1, -, -, hlenRds1, -, hdomsR1, -, -⟩ :=
    recStage_tyPis (V := V) hμ mpC h hrc ψ
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hop1.symm.trans hop0))
  have hle := blockRecHrPle (p := pp) h hc
  have hlenF : fvs1.length = pp.toBlockShape.majorIdxAt c + 1 :=
    ConLeche.Verify.openPisAtFvars_length _ hop1
  obtain ⟨y, hy⟩ : ∃ y, fvs1[d]? = some y := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hyE := hE d y Tm hy (by
    rw [List.append_assoc, List.getElem?_append_left hdP, hpreT]; rfl)
  obtain ⟨pd, hpd, -, hrd⟩ := hdomsR1 d y hy
  have hPdget : (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).getD d
      default = pd.2.2 := by
    rw [blockRulePdomsAV, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take,
      if_pos (by omega), hpd]; rfl
  rw [← hTm] at hyE
  have hcl : ∀ p ∈ ifsD.map ConLeche.classBinder, p.1.looseBVarsBounded 0 = true := by
    intro p hp
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hp
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hz
    obtain ⟨tz, hxe, htz⟩ := hifsD k _ (List.getElem?_eq_getElem hk)
    rw [hxe]; exact htz.2
  have hbb : (Expr.forallE majD (.sort R.g.elim) default).looseBVarsBounded 0 = true := by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨hmajS.2, trivial⟩
  obtain ⟨bs, b, hPE, hbl, hbs, hb⟩ := denoteMeta_closeTelescope_read _ d _ _ hcl hbb hyE hrd
  rw [denoteMeta_forallE] at hb
  obtain ⟨A, hA, hb⟩ := Option.bind_eq_some_iff.mp hb
  obtain ⟨B, -, hb⟩ := Option.bind_eq_some_iff.mp hb
  obtain rfl := (Option.some.inj hb).symm
  -- the callee's index and major domains
  obtain ⟨cls, tyT, ifsR, bodyR, hgcT, hMT, htyT, hopT, hiflT, hRPT, -, hlenRdsT, hidxR, hmajR,
    -, -, -, -⟩ := genRun_binders hμ R hg h mpC ψ hT
  obtain rfl : cls = t := hgcT.symm.trans hct
  rw [hMT] at htyT hopT hiflT hlenRdsT hmajR
  obtain rfl : tyT = ty := Option.some.inj (htyT.symm.trans hty)
  have htl : cls < R.g.cls.length := by
    have := genRun_cls_lt R hT
    rw [hgcT] at this
    exact this
  have hScB : ConLeche.ScB d tyT :=
    ConLeche.ScB.of_instPisWith hty ((hg.former cls htl).mono (Nat.zero_le _))
      (fun e he => (hg.ds cls e he).mono (by omega))
  have hshD := openPisAtFvars_shiftIter hScB.1.fvarsBelow hopD (R.g.pre.length - d)
  rw [hRPT] at hopT
  rw [show d + (R.g.pre.length - d) = R.g.pre.length by omega, hopT] at hshD
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hshD)
  have hifsDl : ifsD.length = (R.g.cls.getD cls default).nIdx :=
    ConLeche.Verify.openPisAtFvars_length _ hopD
  have hbl' : bs.length = ifsD.length := by rw [hbl, List.length_map]
  refine ⟨bs ++ [(0, pwBit ψ (default : BinderMeta).pw, A)], B, ?_, ?_, ?_⟩
  · rw [hPdget, hPE, mkPisAV_append]; rfl
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
      obtain ⟨z, hz⟩ : ∃ z, ifsD[k]? = some z := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨a, ha, -⟩ := hbs k (ConLeche.classBinder z) (by rw [List.getElem?_map, hz]; rfl)
      rw [List.getElem?_eq_getElem hk] at ha
      rw [Option.some.inj ha]
      have hdef : (ConLeche.classBinder z).2.pw = .never := rfl
      simp [hdef, pwBit]
    · simp only [List.mem_singleton] at hp
      subst hp
      have hdef : (default : BinderMeta).pw = .never := rfl
      simp [hdef, pwBit]
  · generalize hm : R.g.pre.length - d = m at hidxR hmajR ⊢
    have hrP : R.g.pre.length = d + m := by omega
    refine List.ext_getElem (by
      rw [List.length_drop, hlenRdsT, hRPT, liftDomsK_length, List.length_map, List.length_append,
        hbl', hifsDl]; simp only [List.length_singleton]; omega) fun k h1 h2 => ?_
    have hk : k < ifsD.length + 1 := by
      rw [List.length_drop, hlenRdsT, hRPT, ← hifsDl] at h1; omega
    rw [List.getElem_drop]
    rw [list_getElem_eq_getD _ default, list_getElem_eq_getD h2 default,
      liftDomsK_getD _ _ _ _ (by simp [hbl']; omega), Nat.zero_add]
    rcases Nat.lt_or_ge k ifsD.length with hkI | hkI
    · -- an index domain
      obtain ⟨z, hz⟩ : ∃ z, ifsD[k]? = some z := ⟨_, List.getElem?_eq_getElem hkI⟩
      obtain ⟨tz, hzE, hzS⟩ := hifsD k z hz
      obtain ⟨a, ha, hra⟩ := hbs k (ConLeche.classBinder z) (by rw [List.getElem?_map, hz]; rfl)
      have hRk := hidxR k (shiftIter d m z) (by rw [List.getElem?_map, hz]; rfl)
      rw [hzE, shiftIter_fvar k tz m, hRPT] at hRk
      simp only [Expr.fvarTypeD] at hRk
      rw [hrP, denoteMeta_shiftIter mpC.base2.acval_closed hzS.1 m] at hRk
      simp only [ConLeche.classBinder, hzE, Expr.fvarTypeD] at hra
      rw [hra] at hRk
      simp only [Option.map_some, Option.some.injEq] at hRk
      rw [hrP, ← hRk, List.getD_eq_getElem?_getD, List.map_append, List.getElem?_append_left
        (by simp [hbl']; exact hkI), List.getElem?_map, ha]
      rfl
    · -- the major domain
      obtain rfl : k = ifsD.length := by omega
      have hmajS' : Expr.WScoped (d + ifsD.length) majD := hmajS.1
      have hsh := denoteMeta_shiftIter (env := envC) (φ := ψ) mpC.base2.acval_closed hmajS' m
      rw [List.length_map] at hA
      rw [hA, hmajE, shiftIter_mkAppN, List.map_append,
        List.map_congr_left (l := (R.g.cls.getD cls default).ds) (g := id) (fun e he =>
          shiftIter_eq_self (Expr.fvarsBelow_mono (by omega) (hg.ds cls e he).1.fvarsBelow) m),
        shiftIter_eq_self (e := Expr.const _ _) trivial m, List.map_id] at hsh
      rw [hRPT, ← hifsDl, hrP] at hmajR
      rw [hmajR] at hsh
      simp only [Option.map_some, Option.some.injEq] at hsh
      rw [hrP, hsh, List.map_append, list_getD_append_right (by simp [hbl'])]
      simp [hbl']

end Motive

end ConLeche.Model
