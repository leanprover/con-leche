module

public import InLeanProof.PassCtors
import ConLeche.Verify.Inductives.NestScope

/-!
# O7-stages: the positivity context against master's (task #451, lane O7-stages)

`blockNestCtxI_run` (`blockNestCtxS_spec`'s twin): InLean's `blockNestCtx`
builds the context master's pure `blockNestCtx` builds at the translated
shape, its parameters and holes read at the final state.  InLean's context
holds the environment (`fe`), master's the lookup (`find?`); `blockNestCtx`
reads neither, so the lookup is any.

* `instPisWithI_tr`: InLean's `instPisWith` at arguments with a closed
  reading is master's at the readings (InLean's also skips `mdata`, which
  the reading drops).
* `nestHolesI_run`: the holes loop (`for` with an early `return none`) reads
  as master's `mapM` over the member indices.

The proofs are functional (`bindI_ok`, `pureI_ok`), as O7's.
-/

set_option experimental.vcgen true

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached

variable {mode : ConLeche.CheckMode} {eager : Bool} {env : ConLeche.Env}

/-! ## Instantiating a telescope's leading binders -/

/-- **InLean's `instPisWith`, read**: at arguments with a closed reading, the
result has a reading, and it is master's `instPisWith` at the readings. -/
theorem instPisWithI_tr {s : InLean.CState} :
    ∀ (as : List Lean.Expr) (e : Lean.Expr) {r : Lean.Expr}, OkS s e = true → OkSL s as = true →
      (∀ a ∈ as, (TrS s a).looseBVarsBounded 0 = true) →
      InLean.instPisWith as e = some r →
      OkS s r = true ∧ ConLeche.instPisWith (TrSL s as) (TrS s e) = some (TrS s r)
  | [], e, r, he, _, _, h => by
    simp only [InLean.instPisWith, Option.some.injEq] at h
    subst h
    exact ⟨he, rfl⟩
  | a :: as, .forallE n t b bi, r, he, ha, hc, h => by
    simp only [InLean.instPisWith] at h
    simp only [OkS_forallE, Bool.and_eq_true] at he
    simp only [OkSL_cons, Bool.and_eq_true] at ha
    have hca := hc a List.mem_cons_self
    have hb' := OkS_inst1 he.2 ha.1 hca
    rw [inst1I_eq] at h
    obtain ⟨h1, h2⟩ := instPisWithI_tr as _ hb' ha.2 (fun x hx => hc x (List.mem_cons_of_mem _ hx)) h
    refine ⟨h1, ?_⟩
    rw [TrS_forallE, TrSL_cons, ConLeche.instPisWith, ← TrS_inst1_eq he.2 ha.1 hca]
    exact h2
  | a :: as, .mdata m e, r, he, ha, hc, h => by
    simp only [InLean.instPisWith] at h
    rw [OkS_mdata] at he
    rw [TrS_mdata]
    exact instPisWithI_tr (a :: as) e he ha hc h
  | _ :: _, .bvar _, _, _, _, _, h | _ :: _, .fvar _, _, _, _, _, h
  | _ :: _, .mvar _, _, _, _, _, h | _ :: _, .sort _, _, _, _, _, h
  | _ :: _, .const _ _, _, _, _, _, h | _ :: _, .app _ _, _, _, _, _, h
  | _ :: _, .lam _ _ _ _, _, _, _, _, h | _ :: _, .letE _ _ _ _ _, _, _, _, _, h
  | _ :: _, .lit _, _, _, _, _, h | _ :: _, .proj _ _ _, _, _, _, _, h => by
    simp [InLean.instPisWith] at h

/-! ## The holes -/

/-- Master's hole at member index `mm` (`nestHoles`' body). -/
@[expose] def cHoleAt (cctx : ConLeche.NestCtx) (mm : Nat) : Option ConLeche.Expr :=
  match cctx.formers[mm]? with
  | some cv => (ConLeche.instPisWith cctx.params cv.type).map (.fvar (cctx.nP + mm) ·)
  | none => none

theorem cNestHoles_eq (cctx : ConLeche.NestCtx) :
    ConLeche.nestHoles cctx = (List.range cctx.names.length).mapM (cHoleAt cctx) := rfl

/-- What the holes loop needs of the two contexts: the same formers (read),
parameter count and member count, the parameters read at the loop's first
state `sI`, closed. -/
structure HolesPre (sI : InLean.CState) (ctx : InLean.NestCtx) (cctx : ConLeche.NestCtx) : Prop where
  formers : cctx.formers = ctx.formers.map trCV
  nP : cctx.nP = ctx.nP
  params : cctx.params = TrSL sI ctx.params
  okParams : OkSL sI ctx.params = true
  clParams : ∀ a ∈ ctx.params, (TrS sI a).looseBVarsBounded 0 = true
  okFormers : ∀ cv ∈ ctx.formers, okC cv.type = true ∧ (trC cv.type).looseBVarsBounded 0 = true

/-- **The holes loop**: from the first state `sI`, every iteration that
continues pushes master's hole at its index. -/
theorem nestHolesLoopI_run {sI : InLean.CState} {ctx : InLean.NestCtx} {cctx : ConLeche.NestCtx}
    (hP : HolesPre sI ctx cctx) :
    ∀ (l : List Nat) (out : Array Lean.Expr) {s₀ s' : InLean.CState}
      {r : Option (Option (List Lean.Expr)) × Array Lean.Expr},
      CSOKI mode eager env s₀ → TabLe sI s₀ → OkSL s₀ out.toList = true →
      (forIn l ((none, out) : Option (Option (List Lean.Expr)) × Array Lean.Expr)
        fun (mm : Nat) (r : Option (Option (List Lean.Expr)) × Array Lean.Expr) =>
          match ctx.formers[mm]? with
          | some cv =>
            match InLean.instPisWith ctx.params cv.type with
            | some ty => do
              let x ← InLean.mkFVarM (ctx.nP + mm) ty
              pure (ForInStep.yield (none, r.snd.push x))
            | none => pure (ForInStep.done (some none, r.snd))
          | none => pure (ForInStep.done (some none, r.snd))) s₀ = .ok (r, s') →
      CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkSL s' r.snd.toList = true ∧
        (∀ x, r.fst ≠ some (some x)) ∧
        (r.fst = none → ∃ rest, l.mapM (cHoleAt cctx) = some rest ∧
          TrSL s' r.snd.toList = TrSL s' out.toList ++ rest)
  | [], out, s₀, s', r, hs, _, hout, h => by
    rw [List.forIn_nil] at h
    obtain ⟨rfl, rfl⟩ := pureI_ok h
    exact ⟨hs, TabLe.refl _, hout, fun _ h => by simp at h, fun _ => ⟨[], rfl, by simp⟩⟩
  | mm :: l, out, s₀, s', r, hs, hI, hout, h => by
    rw [List.forIn_cons] at h
    obtain ⟨st, s₁, h1, h2⟩ := bindI_ok h
    cases hf : ctx.formers[mm]? with
    | none =>
      simp only [hf] at h1
      obtain ⟨rfl, rfl⟩ := pureI_ok h1
      obtain ⟨rfl, rfl⟩ := pureI_ok h2
      exact ⟨hs, TabLe.refl _, hout, fun _ h => by simp at h, fun h => by simp at h⟩
    | some cv =>
      simp only [hf] at h1
      cases hi : InLean.instPisWith ctx.params cv.type with
      | none =>
        simp only [hi] at h1
        obtain ⟨rfl, rfl⟩ := pureI_ok h1
        obtain ⟨rfl, rfl⟩ := pureI_ok h2
        exact ⟨hs, TabLe.refl _, hout, fun _ h => by simp at h, fun h => by simp at h⟩
      | some ty =>
        simp only [hi] at h1
        obtain ⟨x, s₂, hx, h1⟩ := bindI_ok h1
        obtain ⟨rfl, rfl⟩ := pureI_ok h1
        simp only at h2
        obtain ⟨hokcv, hclcv⟩ := hP.okFormers cv (List.mem_of_getElem? hf)
        obtain ⟨hokty, hty⟩ := instPisWithI_tr ctx.params cv.type (OkS_of_okC _ hokcv) hP.okParams
          hP.clParams hi
        rw [TrS_of_okC _ hokcv] at hty
        have hclty : (TrS sI ty).looseBVarsBounded 0 = true :=
          ConLeche.looseBVarsBounded_instPisWith (fun a ha => by
            obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
            exact hP.clParams b hb) hclcv hty
        have hokty₀ := okS_of_tabLe hI hokty
        have htr₀ := TrS_of_tabLe hI hokty
        obtain ⟨hs₂, ht₂, hokx, htx⟩ := tripleI_iff_run.1
          (mkFVarM_specI hs (ctx.nP + mm) hokty₀ (by rw [htr₀]; exact hclty)) x s₂ hx
        have hout₂ : OkSL s₂ (out.push x).toList = true := by
          simp only [Array.toList_push, OkSL, List.all_append, List.all_cons, List.all_nil,
            Bool.and_true, Bool.and_eq_true]
          exact ⟨okSL_of_tabLe ht₂ hout, hokx⟩
        obtain ⟨hs', ht', hok', hns, hR⟩ := nestHolesLoopI_run hP l (out.push x) hs₂ (hI.trans ht₂)
          hout₂ h2
        refine ⟨hs', ht₂.trans ht', hok', hns, fun hn => ?_⟩
        obtain ⟨rest, hrest, htr⟩ := hR hn
        have hhole : cHoleAt cctx mm = some (.fvar (ctx.nP + mm) (TrS sI ty)) := by
          unfold cHoleAt
          rw [hP.formers, List.getElem?_map, hf]
          simp only [Option.map_some, trCV_type, hP.params, hP.nP, hty, Option.map_some]
        refine ⟨.fvar (ctx.nP + mm) (TrS sI ty) :: rest, ?_, ?_⟩
        · rw [List.mapM_cons, hhole, hrest]; rfl
        · rw [htr]
          have hx' : TrS s' x = .fvar (ctx.nP + mm) (TrS sI ty) := by
            rw [TrS_of_tabLe ht' hokx, htx, htr₀]
          simp only [Array.toList_push, TrSL, List.map_append, List.map_cons, List.map_nil,
            List.append_assoc, List.cons_append, List.nil_append]
          rw [show TrS s' x = _ from hx']

/-- **The holes** (`nestHoles`): InLean's answer `some holes` is master's, read
at the final state. -/
theorem nestHolesI_run {ctx : InLean.NestCtx} {cctx : ConLeche.NestCtx} {s₀ s' : InLean.CState}
    {holes : List Lean.Expr} (hP : HolesPre s₀ ctx cctx) (hn : cctx.names.length = ctx.names.length)
    (hs : CSOKI mode eager env s₀) (h : InLean.nestHoles ctx s₀ = .ok (some holes, s')) :
    CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkSL s' holes = true ∧
      ConLeche.nestHoles cctx = some (TrSL s' holes) := by
  unfold InLean.nestHoles at h
  obtain ⟨r, s₁, h1, h2⟩ := bindI_ok h
  obtain ⟨hs₁, ht₁, hok₁, hns, hR⟩ := nestHolesLoopI_run (mode := mode) (eager := eager) (env := env) hP
    (List.range ctx.names.length) #[] hs (TabLe.refl _) rfl h1
  obtain ⟨r1, r2⟩ := r
  cases r1 with
  | some x =>
    cases x with
    | some y => exact (hns y rfl).elim
    | none =>
      obtain ⟨hx, rfl⟩ := pureI_ok h2
      cases hx
  | none =>
    obtain ⟨hx, rfl⟩ := pureI_ok h2
    cases hx
    obtain ⟨rest, hrest, htr⟩ := hR rfl
    refine ⟨hs₁, ht₁, hok₁, ?_⟩
    rw [cNestHoles_eq, hn, hrest]
    simpa [TrSL] using htr.symm

/-! ## The context -/

theorem trShape_formers (p : InLean.BlockShape) :
    (trShape p).formers = p.formers.map trCV := by
  simp [ConLeche.BlockShape.formers, InLean.BlockShape.formers, trShape, trMember]

theorem trShape_nP (p : InLean.BlockShape) : (trShape p).nP = p.nP := rfl

/-- **The positivity context** (`blockNestCtxS_spec`'s twin): InLean's
`blockNestCtx` builds `p.nestCtx fvs fe` and holes whose readings at the final
state are master's context at the translated shape (at any lookup) and its
holes; the parameters are variables, closed, one per parameter. -/
theorem blockNestCtxI_run {p : InLean.BlockShape} {fe : InLean.FEnv} {s₀ s' : InLean.CState}
    {ctx : InLean.NestCtx} {holes : List Lean.Expr} (find? : ConLeche.Name → Option ConLeche.ConstantInfo)
    (hs : CSOKI mode eager env s₀)
    (hok : ∀ ms ∈ p.members, okC ms.cvT.type = true ∧ (trC ms.cvT.type).looseBVarsBounded 0 = true)
    (h : InLean.blockNestCtx p fe s₀ = .ok ((ctx, holes), s')) :
    CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ ∃ fvs, ctx = p.nestCtx fvs fe ∧
      OkSL s' fvs = true ∧ OkSL s' holes = true ∧
      (∀ a ∈ fvs, (TrS s' a).looseBVarsBounded 0 = true) ∧
      Runs (ConLeche.blockNestCtx (m := ConLeche.FueledM) (trShape p) find?)
        ((trShape p).nestCtx (TrSL s' fvs) find?, TrSL s' holes) := by
  unfold InLean.blockNestCtx at h
  obtain ⟨c0, s₁, h1, h⟩ := bindI_ok h
  cases h0 : p.formers.head? with
  | none => simp only [h0, InLean.unwrapOr] at h1; exact (throwI_ok h1).elim
  | some cv0 =>
  simp only [h0, InLean.unwrapOr] at h1
  obtain ⟨hc0, rfl⟩ := pureI_ok h1
  subst hc0
  have hcv0 : cv0 ∈ p.formers := List.mem_of_mem_head? h0
  obtain ⟨ms0, hms0, hcvT⟩ := List.mem_map.1 hcv0
  obtain ⟨hok0, hcl0⟩ := hok ms0 hms0
  rw [hcvT] at hok0 hcl0
  obtain ⟨o, s₂, h2, h⟩ := bindI_ok h
  obtain ⟨q0, s₃, h3, h⟩ := bindI_ok h
  cases o with
  | none => simp only [InLean.unwrapOr] at h3; exact (throwI_ok h3).elim
  | some pq =>
  simp only [InLean.unwrapOr] at h3
  obtain ⟨hpq, rfl⟩ := pureI_ok h3
  subst hpq
  obtain ⟨fvs, b⟩ := pq
  obtain ⟨o2, s₄, h4, h⟩ := bindI_ok h
  obtain ⟨hl, s₅, h5, h⟩ := bindI_ok h
  cases o2 with
  | none => simp only [InLean.unwrapOr] at h5; exact (throwI_ok h5).elim
  | some hl' =>
  simp only [InLean.unwrapOr] at h5
  obtain ⟨hhl, rfl⟩ := pureI_ok h5
  subst hhl
  obtain ⟨hctx, rfl⟩ := pureI_ok h
  simp only [Prod.mk.injEq] at hctx
  obtain ⟨rfl, rfl⟩ := hctx
  -- the opener, read at the opener's own state
  obtain ⟨hs₂, ht₂, hokf, hop, hfv⟩ := openClosedI_run hs hok0 hcl0 h2 (TabLe.refl _)
  have hclf : ∀ a ∈ fvs, (TrS s₂ a).looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 ha
    have hx : (TrSL s₂ fvs)[i]? = some (TrS s₂ a) := by
      simp [TrSL, hi]
    obtain ⟨⟨k, ty, hk⟩, -, -⟩ := hfv i _ hx
    rw [hk]
    simp [ConLeche.Expr.looseBVarsBounded]
  -- the holes
  have hP : HolesPre s₂ (p.nestCtx fvs fe) ((trShape p).nestCtx (TrSL s₂ fvs) find?) := by
    refine ⟨?_, rfl, rfl, hokf, hclf, ?_⟩
    · show (trShape p).formers = p.formers.map trCV
      exact trShape_formers p
    · intro cv hcv
      obtain ⟨ms, hms, rfl⟩ := List.mem_map.1 hcv
      exact hok ms hms
  obtain ⟨hs₄, ht₄, hokh, hholes⟩ := nestHolesI_run hP
    (by simp [ConLeche.BlockShape.nestCtx, InLean.BlockShape.nestCtx, trShape_memberNames]) hs₂ h4
  refine ⟨hs₄, ht₂.trans ht₄, fvs, rfl, okSL_of_tabLe ht₄ hokf, hokh, ?_, ?_⟩
  · intro a ha
    rw [TrS_of_tabLe ht₄ (by simp only [OkSL, List.all_eq_true] at hokf; exact hokf a ha)]
    exact hclf a ha
  · rw [TrSL_of_tabLe ht₄ hokf]
    have hc0 : (trShape p).formers.head? = some (trCV cv0) := by
      rw [trShape_formers, List.head?_map, h0]; rfl
    unfold ConLeche.blockNestCtx
    simp only [hc0, ConLeche.unwrapOr]
    refine Runs.bind (Runs.pure _) ?_
    simp only [trCV_type] at hop ⊢
    rw [trShape_nP, hop]
    refine Runs.bind (Runs.pure _) ?_
    simp only [hholes]
    refine Runs.bind (Runs.pure _) ?_
    exact Runs.pure _

end InLeanProof
