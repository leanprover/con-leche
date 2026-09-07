import Lech.SetP.DirectFix.FixRecReadDefsP
import Lech.SetP.DirectFix.FixDataP
import Lech.SetP.DirectSum.SumRecDataP
import Lech.Verify.Direct.DirectBody

/-!
# The recursive constructors' reading premises (task #188)

The per-constructor facts of a recursive block (`FixCtorDataI`,
`FixDataP.lean` — the sum route's data with the field kinds, the
opened form and the per-field index readings) yield the reading
premises `CtorReadsR` (`FixRecReadDefsP.lean`) the generated
recursor's reading theorems consume.  The one bridge: a recursive
field's index expressions off the raw constructor type
(`directFieldIdxOf`), instantiated at the opening's variables, are the
opened variable's type's index arguments — an opened variable's type
is its binder's domain instantiated at the earlier variables
(`openPisAtFvars_fvarTypeD`), and instantiation at variables maps the
argument spine (`getAppArgs_instSeq_fvars`).
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.TT Lech.TTVerify SetTheory
open Lech.Semantics (AVExpr)
open Lech (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## Instantiation at variables and the argument spine -/

/-- Substituting a variable maps an application's arguments. -/
theorem Expr.getAppArgs_instantiate1_fvar {i : Nat} {nm : Name} {t : Expr} :
    ∀ (e : Expr) (k : Nat),
      (e.instantiate1 (.fvar i t) k).getAppArgs
        = e.getAppArgs.map (fun a => a.instantiate1 (.fvar i t) k) := by
  intro e
  induction e with
  | app g a ihg iha =>
    intro k
    simp only [Expr.instantiate1, Expr.getAppArgs, List.map_append, List.map_cons, List.map_nil]
    rw [ihg k]
  | bvar j =>
    intro k
    simp only [Expr.instantiate1]
    split
    · rfl
    · split <;> rfl
  | _ => intro k; first | rfl | (simp only [Expr.instantiate1]; rfl)

/-- Instantiation at variables maps an application's arguments. -/
theorem Expr.getAppArgs_instSeq_fvars :
    ∀ (as : List Expr) (t : Nat) (e : Expr),
      (∀ a ∈ as, ∃ (i : Nat) (nm : Name) (ty : Expr), a = Expr.fvar i ty) →
      (Expr.instSeq as t e).getAppArgs = e.getAppArgs.map (Expr.instSeq as t)
  | [], _, e, _ => by simp [Expr.instSeq]
  | a :: as, t, e, hfv => by
    obtain ⟨i, nm, ty, rfl⟩ := hfv a List.mem_cons_self
    show (Expr.instSeq as (t - 1) (e.instantiate1 (.fvar i ty) t)).getAppArgs = _
    rw [Expr.getAppArgs_instSeq_fvars as (t - 1) _ (fun a ha => hfv a (List.mem_cons_of_mem _ ha)),
      Expr.getAppArgs_instantiate1_fvar, List.map_map]
    rfl

/-! ## An opened variable's type -/

/-- **An opened variable's type is its binder's domain instantiated at
the earlier variables.** -/
theorem openPisAtFvars_fvarTypeD :
    ∀ (n : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {o : Expr}
      {bs : List (Name × Expr × BinderMeta)} {body : Expr},
      openPisAtFvars n e d = some (fvs, o) →
      e.stripPis n = some (bs, body) →
      ∀ (i : Nat) (b : Name × Expr × BinderMeta) (x : Expr),
        bs[i]? = some b → fvs[i]? = some x →
        x.fvarTypeD = Expr.instSeq (fvs.take i) (i - 1) b.2.1
  | 0, e, d, fvs, o, bs, body, hop, hst, i, b, x, hb, _ => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hst
    rw [← hst.1] at hb
    exact nomatch hb
  | n + 1, e, d, fvs, o, bs, body, hop, hst, i, b, x, hb, hx => by
    match e, hop, hst with
    | .forallE dom bd mb, hop, hst =>
      simp only [openPisAtFvars] at hop
      split at hop
      · next fvs₁ e₁ h₁ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        simp only [Expr.stripPis, Option.map_eq_some_iff] at hst
        obtain ⟨⟨bs', body₀⟩, hst', heq⟩ := hst
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hb hx
          subst hb; subst hx
          rfl
        | succ i =>
          simp only [List.getElem?_cons_succ] at hb hx
          obtain ⟨bs'', hst'', hdoms⟩ :=
            Lech.stripPis_instantiate1_full (v := .fvar d dom) n 0 hst'
          have hb'' := hdoms i b hb
          rw [Nat.zero_add] at hb''
          have ih := openPisAtFvars_fvarTypeD n h₁ hst'' i _ x hb'' hx
          rw [ih, List.take_succ_cons]
          rfl
      · exact nomatch hop

/-! ## The constructor data, per block -/

/-- The recursive constructor data of a list of constructors, from
constructor `j` on. -/
def fixCtorDataList (dsF : Nat → (Name → Nat) → List (Nat × Nat × AVExpr))
    (esF : Nat → (Name → Nat) → List AVExpr) (ksF : Nat → List RecFieldKind)
    (eissF : Nat → (Name → Nat) → List (List AVExpr)) (ψ : Name → Nat) :
    List (ConstantVal × Nat) → Nat → List CtorDatumR
  | [], _ => []
  | c :: cs, j =>
    (c.1.name, c.2, dsF j ψ, esF j ψ, Lech.recIdxOf (ksF j), eissF j ψ) ::
      fixCtorDataList dsF esF ksF eissF ψ cs (j + 1)

omit [SetTheory V] in
theorem fixCtorDataList_length (dsF : Nat → (Name → Nat) → List (Nat × Nat × AVExpr))
    (esF : Nat → (Name → Nat) → List AVExpr) (ksF : Nat → List RecFieldKind)
    (eissF : Nat → (Name → Nat) → List (List AVExpr)) (ψ : Name → Nat) :
    ∀ (cs : List (ConstantVal × Nat)) (j : Nat),
      (fixCtorDataList dsF esF ksF eissF ψ cs j).length = cs.length
  | [], _ => rfl
  | _ :: cs, j => by simp [fixCtorDataList, fixCtorDataList_length dsF esF ksF eissF ψ cs (j + 1)]

omit [SetTheory V] in
theorem fixCtorDataList_getElem? (dsF : Nat → (Name → Nat) → List (Nat × Nat × AVExpr))
    (esF : Nat → (Name → Nat) → List AVExpr) (ksF : Nat → List RecFieldKind)
    (eissF : Nat → (Name → Nat) → List (List AVExpr)) (ψ : Name → Nat) :
    ∀ (cs : List (ConstantVal × Nat)) (j i : Nat),
      (fixCtorDataList dsF esF ksF eissF ψ cs j)[i]?
        = (cs[i]?).map fun c =>
            (c.1.name, c.2, dsF (j + i) ψ, esF (j + i) ψ, Lech.recIdxOf (ksF (j + i)),
              eissF (j + i) ψ)
  | [], _, _ => rfl
  | c :: cs, j, 0 => by simp [fixCtorDataList]
  | c :: cs, j, i + 1 => by
    simp only [fixCtorDataList, List.getElem?_cons_succ]
    rw [fixCtorDataList_getElem? dsF esF ksF eissF ψ cs (j + 1) i]
    congr 2
    funext c
    rw [show j + 1 + i = j + (i + 1) from by omega]

/-- The per-constructor facts of a recursive block at a position. -/
def FixCtorFactsAt {env : Env} (m : EnvS2Core V env) (env₀ : Env) (T : Name) (lps : List Name)
    (nP nIdx : Nat) (resSort : Level) (isProp large : Bool) (idxF : Nat → List Expr)
    (dsF : Nat → (Name → Nat) → List (Nat × Nat × AVExpr))
    (esF : Nat → (Name → Nat) → List AVExpr) (srcsF : Nat → List (Option Nat))
    (ksF : Nat → List RecFieldKind) (fvsPF xFvsF : Nat → List Expr) (xrestF : Nat → Expr)
    (eissF : Nat → (Name → Nat) → List (List AVExpr)) (j : Nat) (cA : ConstantVal × Nat) : Prop :=
  env.find? cA.1.name = some (.ctorInfo cA.1 nP cA.2) ∧
  cA.1.levelParams = lps ∧
  FixCtorDataI m env₀ T lps cA.1 nP cA.2 nIdx resSort isProp large (idxF j) (dsF j) (esF j)
    (srcsF j) (ksF j) (fvsPF j) (xFvsF j) (xrestF j) (eissF j)

omit [SetTheory V] in
/-- The recursive positions are bounded by the field count. -/
theorem mem_recIdxOf {ks : List RecFieldKind} {i : Nat} :
    i ∈ Lech.recIdxOf ks ↔ i < ks.length ∧ ks.getD i .ordinary = .recursive := by
  unfold Lech.recIdxOf
  rw [List.mem_filter, List.mem_range, beq_iff_eq]

omit [SetTheory V] in
/-- The recursive positions are strictly increasing. -/
theorem recIdxOf_pairwise (ks : List RecFieldKind) : (Lech.recIdxOf ks).Pairwise (· < ·) :=
  (List.pairwise_lt_range).filter _

/-- A positional characterisation of the reading premises. -/
theorem CtorReadsR.of_getElem? {m : EnvS2Core V env} {ψ : Name → Nat} {T : Name} {lps : List Name}
    {nP nIdx : Nat} :
    ∀ {ctors : List (Name × Nat × Expr × List Nat)} {cds : List CtorDatumR},
      ctors.length = cds.length →
      (∀ (i : Nat) (c : Name × Nat × Expr × List Nat) (cd : CtorDatumR),
        ctors[i]? = some c → cds[i]? = some cd → CtorReadR m ψ T lps nP nIdx c cd) →
      CtorReadsR m ψ T lps nP nIdx ctors cds
  | [], [], _, _ => .nil
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | c :: cs, cd :: cds, hlen, h =>
    .cons (h 0 c cd rfl rfl) (CtorReadsR.of_getElem? (by simpa using hlen)
      fun i c' cd' hc hcd => h (i + 1) c' cd' (by simpa using hc) (by simpa using hcd))

/-- **The reading premises from the constructor facts.** -/
theorem fixCtorReadsR_of {m : EnvS2Core V env} {env₀ : Env} {T : Name} {lps : List Name}
    {nP nIdx : Nat} {resSort : Level} {isProp large : Bool} {idxF : Nat → List Expr}
    {dsF : Nat → (Name → Nat) → List (Nat × Nat × AVExpr)}
    {esF : Nat → (Name → Nat) → List AVExpr} {srcsF : Nat → List (Option Nat)}
    {ksF : Nat → List RecFieldKind} {fvsPF xFvsF : Nat → List Expr} {xrestF : Nat → Expr}
    {eissF : Nat → (Name → Nat) → List (List AVExpr)} (ψ : Name → Nat)
    {ctorsA : List (ConstantVal × Nat)} {kinds : List (List RecFieldKind)}
    (hlenK : kinds.length = ctorsA.length)
    (hks : ∀ i, i < ctorsA.length → kinds[i]? = some (ksF i))
    (hcf : ∀ i cA, ctorsA[i]? = some cA →
      FixCtorFactsAt m env₀ T lps nP nIdx resSort isProp large idxF dsF esF srcsF ksF fvsPF xFvsF
        xrestF eissF i cA) :
    CtorReadsR m ψ T lps nP nIdx (Lech.directFixCtors4 ctorsA kinds)
      (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0) := by
  refine CtorReadsR.of_getElem? ?_ ?_
  · rw [fixCtorDataList_length]
    simp [Lech.directFixCtors4, hlenK]
  intro i c cd hc hcd
  simp only [Lech.directFixCtors4, List.getElem?_zipWith] at hc
  cases hA : ctorsA[i]? with
  | none => rw [hA] at hc; exact nomatch hc
  | some cA =>
    have hi : i < ctorsA.length := (List.getElem?_eq_some_iff.mp hA).1
    rw [hA, hks i hi] at hc
    simp only [Option.some.injEq] at hc
    subst hc
    rw [fixCtorDataList_getElem?, hA, Nat.zero_add] at hcd
    simp only [Option.map_some, Option.some.injEq] at hcd
    subst hcd
    obtain ⟨hf, hlps, hD⟩ := hcf i cA hA
    obtain ⟨hCf, -, -, hCb, -⟩ := m.wf _ (Lech.Semantics.Env.find?_mem hf)
    simp only [ConstantInfo.toConstantVal] at hCf hCb
    have hksLen := hD.ksLen
    -- the opening
    obtain ⟨crest, hopP, hopX⟩ := hD.opens
    have hopAll : openPisAtFvars (nP + cA.2) cA.1.type 0 = some (fvsPF i ++ xFvsF i, xrestF i) :=
      openPisAtFvars_add nP hopP (by rw [Nat.zero_add]; exact hopX)
    obtain ⟨cbs, es, hst, -⟩ := hD.resid
    refine ⟨rfl, rfl, ⟨_, hf, hlps⟩, hCf, hCb, hD.resid, hD.read ψ, hD.len ψ, hD.lenE ψ, rfl,
      ?_, recIdxOf_pairwise _, hD.eissLen ψ, ?_, ?_, ?_⟩
    · intro i' hi'
      have := (mem_recIdxOf.mp hi').1
      rwa [hksLen] at this
    · intro i' hi'
      obtain ⟨hlt, hrec⟩ := mem_recIdxOf.mp hi'
      rw [hksLen] at hlt
      exact hD.eisLen ψ i' hrec hlt
    · -- the index expressions off the raw type, at the opening's variables
      intro i' hi' fvs o hop
      obtain ⟨hlt, hrec⟩ := mem_recIdxOf.mp hi'
      rw [hksLen] at hlt
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj (hop.symm.trans hopAll))
      obtain ⟨x, hx⟩ : ∃ x, (xFvsF i)[i']? = some x :=
        ⟨_, List.getElem?_eq_getElem (by rw [hD.xLen]; exact hlt)⟩
      have hread := hD.eisRead ψ i' x hx hrec
      have hxA : (fvsPF i ++ xFvsF i)[nP + i']? = some x := by
        rw [List.getElem?_append_right (by rw [hD.pLen]; omega), hD.pLen, Nat.add_sub_cancel_left]
        exact hx
      obtain ⟨b, hb⟩ : ∃ b, cbs[nP + i']? = some b :=
        ⟨_, List.getElem?_eq_getElem (by rw [Lech.Expr.stripPis_length _ hst]; omega)⟩
      have hty := openPisAtFvars_fvarTypeD (nP + cA.2) hopAll hst (nP + i') b x hb hxA
      have hfvars : ∀ a ∈ (fvsPF i ++ xFvsF i).take (nP + i'),
          ∃ (k : Nat) (nm : Name) (ty : Expr), a = Expr.fvar k ty := by
        intro a ha
        obtain ⟨q, hq⟩ := List.getElem?_of_mem (List.mem_of_mem_take ha)
        obtain ⟨nm, ty, rfl⟩ := (opening_vars_at hopAll).2.1 q a hq
        exact ⟨_, nm, ty, rfl⟩
      have hargs : (directFieldIdxOf cA.1.type nP cA.2 i').map
          (Expr.instSeq ((fvsPF i ++ xFvsF i).take (nP + i')) (nP + i' - 1))
          = x.fvarTypeD.getAppArgs.drop nP := by
        rw [hty, Expr.getAppArgs_instSeq_fvars _ _ _ hfvars, ← List.map_drop]
        congr 1
        unfold Lech.directFieldIdxOf
        rw [hst]
        simp only [List.getD_eq_getElem?_getD, hb, Option.getD_some]
      rw [hargs]
      exact hread
    · intro i' hi'
      obtain ⟨hlt, hrec⟩ := mem_recIdxOf.mp hi'
      rw [hksLen] at hlt
      exact hD.recEntry ψ i' hrec hlt

end Lech.SetP
