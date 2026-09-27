module

public import ConLeche.Verify.Inductives.PosDerivK

public section

/-!
# The key-named derivation's normal forms are a decision-free function (K-f)

`posDK_nfOk`: every field and telescope judgment of `PosDK` has, as its
normal-form output, what `nestNf` / `nestTeleNf`
(`ConLeche/Kernel/Inductives/FieldNf.lean`) compute on its input at the
judgment's hole range `[nP, L.hi)` — the members, the layout's flexible
families and its own group's holes — at every fuel above a bound.

`posDK_node_nf` is the determinism tie the recursor check needs (PROOFPLAN
K-f, the analogue of `posD_nfOk`): a node's derivation fixes its layout as
THE value of the one layout function `nestLayoutK` at `nestContainer`
(`posDK_node_layout_fun`: two node derivations of one key have one layout),
and each of its crests' walked telescope is `nestTeleNf` of that crest at
that layout.  A reader that recomputes `nestLayoutK` for the key and runs
`nestTeleNf` on its crests computes the derivation's normal forms.
-/

namespace ConLeche

variable {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx} {hk : UseHookK}

/-- What `posDK_nfOk` states per judgment. -/
@[expose] def PosJK.NfOk (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) : PosJK → Prop
  | .field L _ dep _ e _ nf => ∃ F, ∀ fuel, F ≤ fuel →
      nestNf ops env ctx.names ctx.nP L.hi fuel dep e = .ok nf
  | .tele L _ nF j cur _ nds res => ∃ F, ∀ fuel, F ≤ fuel →
      nestTeleNf ops env ctx.names ctx.nP L.hi fuel L.hi nF j cur = .ok (nds, res)
  | _ => True

/-- `nestNf` one step in, at a known reduct. -/
private theorem nestNf_succK {names : List Name} {nP hi fuel dep : Nat} {e w : Expr}
    (hw : ops.whnf env dep e = .ok w) :
    nestNf ops env names nP hi (fuel + 1) dep e =
      nestNfAt names nP hi (nestNf ops env names nP hi fuel) dep e w := by
  show ops.whnf env dep e >>= _ = _
  rw [hw]
  rfl

/-- A reduct whose head is a variable or a constant is no `Π`. -/
private theorem nestNf_rigidK {names : List Name} {nP hi fuel dep : Nat} {e w : Expr}
    (hw : ops.whnf env dep e = .ok w) (hocc : w.nestOcc names nP hi = true)
    (hnp : ∀ a b bm, w ≠ .forallE a b bm) :
    nestNf ops env names nP hi (fuel + 1) dep e = .ok w := by
  rw [nestNf_succK hw]
  unfold nestNfAt
  rw [hocc]
  cases w with
  | forallE a b bm => exact absurd rfl (hnp a b bm)
  | _ => rfl

private theorem getAppFn_fvar_ne_piK {w : Expr} {i : Nat} {ty : Expr}
    (h : w.getAppFn = .fvar i ty) : ∀ a b bm, w ≠ .forallE a b bm := by
  intro a b bm he; subst he; simp [Expr.getAppFn] at h

private theorem getAppFn_const_ne_piK {w : Expr} {n : Name} {us : List Level}
    (h : w.getAppFn = .const n us) : ∀ a b bm, w ≠ .forallE a b bm := by
  intro a b bm he; subst he; simp [Expr.getAppFn] at h

/-- **The key-named walk's normal forms are `nestNf`'s.** -/
theorem posDK_nfOk : ∀ {j : PosJK}, PosDKH ops env ctx hk j → PosJK.NfOk ops env ctx j := by
  intro j h
  induction h with
  | @const L met dep kb e w hw hocc =>
    refine ⟨1, fun fuel hf => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [nestNf_succK hw]
    unfold nestNfAt
    rw [hocc]
    rfl
  | @pi L met dep kb e a b bm k nb hw hocc ha hb ih =>
    obtain ⟨F, hF⟩ := ih
    refine ⟨F + 1, fun fuel hf => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [nestNf_succK hw]
    unfold nestNfAt
    rw [hocc]
    show (do
      let nb ← nestNf ops env ctx.names ctx.nP L.hi f (dep + 1) (b.instantiate1 (.fvar dep a))
      pure (Expr.forallE a (nb.abstract1 dep) bm) : CheckM Expr) = _
    rw [hF f (by omega)]
    rfl
  | @hole L met dep kb e w i ty hw hocc hfn =>
    refine ⟨1, fun fuel hf => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    exact nestNf_rigidK hw hocc (getAppFn_fvar_ne_piK hfn)
  | @famHole L met dep kb e w i ty key nI hw hocc hfn =>
    refine ⟨1, fun fuel hf => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    exact nestNf_rigidK hw hocc (getAppFn_fvar_ne_piK hfn)
  | @ownHole L met dep kb e w i ty g hw hocc hfn =>
    refine ⟨1, fun fuel hf => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    exact nestNf_rigidK hw hocc (getAppFn_fvar_ne_piK hfn)
  | @cont L met dep kb e w n us Lc nPc nI cty hw hocc hfn =>
    refine ⟨1, fun fuel hf => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    exact nestNf_rigidK hw hocc (getAppFn_const_ne_piK hfn)
  | teleNil => exact ⟨0, fun _ _ => rfl⟩
  | @teleCons L met nF j a b bm k nd ks nds res ha hs hb iha ihs ihb =>
    obtain ⟨F₁, hF₁⟩ := iha
    obtain ⟨F₂, hF₂⟩ := ihb
    refine ⟨max F₁ F₂, fun fuel hf => ?_⟩
    simp only [nestTeleNf]
    show (do
      let nd ← nestNf ops env ctx.names ctx.nP L.hi fuel (L.hi + j) a
      let (nds, res) ← nestTeleNf ops env ctx.names ctx.nP L.hi fuel L.hi nF
        (j + 1) (b.instantiate1 (.fvar (L.hi + j) a))
      pure ((nd, bm) :: nds, res) : CheckM _) = _
    rw [hF₁ fuel (by omega), hF₂ fuel (by omega)]
    rfl
  | _ => trivial

/-- A telescope judgment's normal forms and result are `nestTeleNf`'s. -/
theorem PosDKH.tele_nestTeleNf {L : LayoutK} {met : List Nat} {nF j : Nat} {cur res : Expr}
    {ks : List PosKind} {nds : List (Expr × BinderMeta)}
    (h : PosDKH ops env ctx hk (.tele L met nF j cur ks nds res)) :
    ∃ F, ∀ fuel, F ≤ fuel →
      nestTeleNf ops env ctx.names ctx.nP L.hi fuel L.hi nF j cur = .ok (nds, res) :=
  posDK_nfOk h

/-- **A telescope's normal forms are its input's**: two derivations of one
telescope agree on its normal forms and result. -/
theorem posDK_tele_nf_fun {L : LayoutK} {met met' : List Nat} {nF j : Nat} {cur res res' : Expr}
    {ks ks' : List PosKind} {nds nds' : List (Expr × BinderMeta)}
    (h : PosDKH ops env ctx hk (.tele L met nF j cur ks nds res))
    (h' : PosDKH ops env ctx hk (.tele L met' nF j cur ks' nds' res')) :
    nds = nds' ∧ res = res' := by
  obtain ⟨F, hF⟩ := h.tele_nestTeleNf
  obtain ⟨F', hF'⟩ := h'.tele_nestTeleNf
  have := (hF (max F F') (by omega)).symm.trans (hF' (max F F') (by omega))
  simp only [Except.ok.injEq, Prod.mk.injEq] at this
  exact this

/-- The inputs of a judgment determine its outputs, at any met set: the
motive over the judgments. -/
@[expose] def PosJK.Fun (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (hk : UseHookK) :
    PosJK → Prop
  | .field L _ dep kb e k nf => ∀ met' k' nf',
      PosDKH ops env ctx hk (.field L met' dep kb e k' nf') → k = k' ∧ nf = nf'
  | .tele L _ nF j cur ks nds res => ∀ met' ks' nds' res',
      PosDKH ops env ctx hk (.tele L met' nF j cur ks' nds' res') → ks = ks' ∧ nds = nds' ∧ res = res'
  | _ => True

private theorem ok_injK {α : Type} {a b : α} (h₁ : (Except.ok a : CheckM α) = .ok b) : a = b := by
  cases h₁; rfl

/-- **The derivation is functional in its outputs**: a field's kind and
normal form, a telescope's kinds, normal forms and result. -/
theorem posDK_fun : ∀ {j : PosJK}, PosDKH ops env ctx hk j → PosJK.Fun ops env ctx hk j := by
  intro j h
  induction h with
  | @const L met dep kb e w hw hocc =>
    intro met' k' nf' h'
    cases h' with
    | const hw' _ => rw [hw] at hw'; cases ok_injK hw'; exact ⟨rfl, rfl⟩
    | pi hw' hocc' => rw [hw] at hw'; cases ok_injK hw'; rw [hocc] at hocc'; exact nomatch hocc'
    | hole hw' hocc' => rw [hw] at hw'; cases ok_injK hw'; rw [hocc] at hocc'; exact nomatch hocc'
    | famHole hw' hocc' => rw [hw] at hw'; cases ok_injK hw'; rw [hocc] at hocc'; exact nomatch hocc'
    | ownHole hw' hocc' => rw [hw] at hw'; cases ok_injK hw'; rw [hocc] at hocc'; exact nomatch hocc'
    | cont hw' hocc' => rw [hw] at hw'; cases ok_injK hw'; rw [hocc] at hocc'; exact nomatch hocc'
  | @pi L met dep kb e a b bm k nb hw hocc ha hb ih =>
    intro met' k' nf' h'
    cases h' with
    | const hw' hocc' => rw [hw] at hw'; cases ok_injK hw'; rw [hocc] at hocc'; exact nomatch hocc'
    | pi hw' _ _ hb' =>
      rw [hw] at hw'; cases ok_injK hw'
      obtain ⟨rfl, rfl⟩ := ih _ _ _ hb'
      exact ⟨rfl, rfl⟩
    | hole hw' _ hfn => rw [hw] at hw'; cases ok_injK hw'; simp [Expr.getAppFn] at hfn
    | famHole hw' _ hfn => rw [hw] at hw'; cases ok_injK hw'; simp [Expr.getAppFn] at hfn
    | ownHole hw' _ hfn => rw [hw] at hw'; cases ok_injK hw'; simp [Expr.getAppFn] at hfn
    | cont hw' _ hfn => rw [hw] at hw'; cases ok_injK hw'; simp [Expr.getAppFn] at hfn
  | @hole L met dep kb e w i ty hw hocc hfn hlo hhi =>
    intro met' k' nf' h'
    cases h' with
    | const hw' hocc' => rw [hw] at hw'; cases ok_injK hw'; rw [hocc] at hocc'; exact nomatch hocc'
    | pi hw' => rw [hw] at hw'; cases ok_injK hw'; simp [Expr.getAppFn] at hfn
    | hole hw' _ hfn' => rw [hw] at hw'; cases ok_injK hw'; rw [hfn] at hfn'; cases hfn'; exact ⟨rfl, rfl⟩
    | famHole hw' _ hfn' hlo' => rw [hw] at hw'; cases ok_injK hw'; rw [hfn] at hfn'; cases hfn'; omega
    | ownHole hw' _ hfn' hlo' => rw [hw] at hw'; cases ok_injK hw'; rw [hfn] at hfn'; cases hfn'; omega
    | cont hw' _ hfn' => rw [hw] at hw'; cases ok_injK hw'; rw [hfn] at hfn'; exact nomatch hfn'
  | @famHole L met dep kb e w i ty key nI hw hocc hfn hlo hhi hj =>
    intro met' k' nf' h'
    cases h' with
    | const hw' hocc' => rw [hw] at hw'; cases ok_injK hw'; rw [hocc] at hocc'; exact nomatch hocc'
    | pi hw' => rw [hw] at hw'; cases ok_injK hw'; simp [Expr.getAppFn] at hfn
    | hole hw' _ hfn' _ hhi' => rw [hw] at hw'; cases ok_injK hw'; rw [hfn] at hfn'; cases hfn'; omega
    | famHole hw' => rw [hw] at hw'; cases ok_injK hw'; exact ⟨rfl, rfl⟩
    | ownHole hw' _ hfn' _ _ hj' =>
      rw [hw] at hw'; cases ok_injK hw'; rw [hfn] at hfn'; cases hfn'; omega
    | cont hw' _ hfn' => rw [hw] at hw'; cases ok_injK hw'; rw [hfn] at hfn'; exact nomatch hfn'
  | @ownHole L met dep kb e w i ty g hw hocc hfn hlo hhi hj =>
    intro met' k' nf' h'
    cases h' with
    | const hw' hocc' => rw [hw] at hw'; cases ok_injK hw'; rw [hocc] at hocc'; exact nomatch hocc'
    | pi hw' => rw [hw] at hw'; cases ok_injK hw'; simp [Expr.getAppFn] at hfn
    | hole hw' _ hfn' _ hhi' => rw [hw] at hw'; cases ok_injK hw'; rw [hfn] at hfn'; cases hfn'; omega
    | famHole hw' _ hfn' _ _ hj' =>
      rw [hw] at hw'; cases ok_injK hw'; rw [hfn] at hfn'; cases hfn'; omega
    | ownHole hw' => rw [hw] at hw'; cases ok_injK hw'; exact ⟨rfl, rfl⟩
    | cont hw' _ hfn' => rw [hw] at hw'; cases ok_injK hw'; rw [hfn] at hfn'; exact nomatch hfn'
  | @cont L met dep kb e w n us Lc nPc nI cty hw hocc hfn =>
    intro met' k' nf' h'
    cases h' with
    | const hw' hocc' => rw [hw] at hw'; cases ok_injK hw'; rw [hocc] at hocc'; exact nomatch hocc'
    | pi hw' => rw [hw] at hw'; cases ok_injK hw'; simp [Expr.getAppFn] at hfn
    | hole hw' _ hfn' => rw [hw] at hw'; cases ok_injK hw'; rw [hfn] at hfn'; exact nomatch hfn'
    | famHole hw' _ hfn' => rw [hw] at hw'; cases ok_injK hw'; rw [hfn] at hfn'; exact nomatch hfn'
    | ownHole hw' _ hfn' => rw [hw] at hw'; cases ok_injK hw'; rw [hfn] at hfn'; exact nomatch hfn'
    | cont hw' => rw [hw] at hw'; cases ok_injK hw'; exact ⟨rfl, rfl⟩
  | teleNil =>
    intro met' ks' nds' res' h'
    cases h'
    exact ⟨rfl, rfl, rfl⟩
  | @teleCons L met nF j a b bm k nd ks nds res ha hs hb iha ihs ihb =>
    intro met' ks' nds' res' h'
    cases h' with
    | teleCons ha' _ hb' =>
      obtain ⟨rfl, rfl⟩ := iha _ _ _ ha'
      obtain ⟨rfl, rfl, rfl⟩ := ihb _ _ _ _ hb'
      exact ⟨rfl, rfl, rfl⟩
  | _ => trivial

/-- A walked constructor list, inverted: each crest's telescope derived,
U4, the result headed by a family with hole-free indices. -/
theorem PosDKH.ctors_mem {L : LayoutK} {met : List Nat} :
    ∀ {cs : List ((ConstantVal × Nat) × Expr)}, PosDKH ops env ctx hk (.ctors L met cs) →
      ∀ x ∈ cs, ∃ ks nds cur, PosDKH ops env ctx hk (.tele L met x.1.2 0 x.2 ks nds cur) ∧
        ((List.range x.1.2).any fun i => ks.getD i .ordinary != .ordinary &&
          structUsedLater (closeTelescope nds L.hi cur) 0 i) = false ∧
        nestResHead cur = true ∧
        (cur.getAppArgs.drop L.dsF.length).all (fun y => !y.nestOcc ctx.names ctx.nP L.hi) = true
  | [], _, x, hx => nomatch hx
  | ((cv, nF), crest) :: cs, h, x, hx => by
    cases h with
    | ctorsCons htele hu4 hres hidx hrest =>
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨_, _, _, htele, hu4, hres, hidx⟩
      · exact PosDKH.ctors_mem hrest x hx

/-- **Two node derivations of one key have one layout** (the layout is the
value of the one function `nestLayoutK`). -/
theorem posDK_node_layout_fun {kc : NestKey} {lo lo' : LayoutOutK} {met met' : List Nat}
    (h : PosDKH ops env ctx hk (.node kc lo met)) (h' : PosDKH ops env ctx hk (.node kc lo' met')) :
    lo = lo' := by
  cases h with
  | node hlay _ =>
    cases h' with
    | node hlay' _ =>
      rw [hlay] at hlay'
      simpa using hlay'

/-- **THE DETERMINISM TIE (K-f)**: a node's derivation fixes its layout as
`nestLayoutK` at `nestContainer`, and each of its crests' walked field
normal forms and result are `nestTeleNf` of that crest at that layout's
hole range and depth. -/
theorem posDK_node_nf {kc : NestKey} {lo : LayoutOutK} {met : List Nat}
    (h : PosDKH ops env ctx hk (.node kc lo met)) :
    nestLayoutK ops env ctx (nestContainer ctx) kc = .ok lo ∧
      ∀ x ∈ lo.ctors.zip lo.crests, ∃ ks nds cur,
        PosDKH ops env ctx hk (.tele lo.L met x.1.2 0 x.2 ks nds cur) ∧
        ∃ F, ∀ fuel, F ≤ fuel →
          nestTeleNf ops env ctx.names ctx.nP lo.L.hi fuel lo.L.hi x.1.2 0 x.2 = .ok (nds, cur) := by
  cases h with
  | node hlay hwalk =>
    refine ⟨hlay, fun x hx => ?_⟩
    obtain ⟨ks, nds, cur, ht, -⟩ := hwalk.ctors_mem x hx
    exact ⟨ks, nds, cur, ht, ht.tele_nestTeleNf⟩

end ConLeche
