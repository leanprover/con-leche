module

public import ConLeche.Verify.Inductives.PosDerivK
import ConLeche.Verify.Inductives.PosDerivKInv
import ConLeche.Verify.Inductives.DirectInv
import ConLeche.Verify.Inductives.PosDerivInv

public section

/-!
# What a key-named layout guarantees (`nestLayoutK_spec`)

`LayoutSpecK`: the facts a successful `nestLayoutK` (at `nestContainer`)
establishes about its output, which the model side reads (PROOFPLAN §1.3,
`nestLayoutK_inv`).  The group is the key's canonical group (`groupOfK`: its
recorded block, the key first when it is not recorded there; the node's layout
is its HEAD's), their constructors the environment's (`groupCtors`), level
parameters distinct; the
parameters `DsF` are the key's parameters with some keys abstracted to the
flexible families `hiAt0 + i` (`i < nF`); the group's formers at `DsF`
(K-a, `nestInstType` at the layout's base depth), the key `C us DsF` typed
there, and every crest (`crestsK`) typed into a sort at `L.hi`.

This lemma deliberately reads only the FINAL joint typing of the layout
(`layoutTypeK`) and the group listing, never the flexibility trials that
choose the families: the choice of the flexible set is data here, and a
different way of computing it changes only `flexSubstK_fvar` below.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche

variable {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx} {hk : UseHookK}

/-- **What a layout guarantees** (see the module docstring). -/
@[expose] def LayoutSpecK (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (kc : NestKey)
    (lo : LayoutOutK) : Prop :=
  (∃ nPc Lc, nestContainer ctx ((groupOfK ctx kc.cname).headD kc.cname) = some (nPc, Lc) ∧
    groupCtors ctx nPc (groupOfK ctx kc.cname) = some lo.ctors) ∧
  (∀ c ∈ lo.ctors, Name.nodup c.1.levelParams = true) ∧
  lo.L.grp = groupOfK ctx kc.cname ∧ lo.L.lvls = kc.lvls ∧
  lo.ginfo.map (·.1) = lo.L.grp ∧
  lo.L.hi = ctx.hiAt 0 + lo.L.nF + lo.ginfo.length ∧
  (∃ S : List (NestKey × Expr), lo.L.dsF = kc.ds.map (absKeysK S) ∧
    ∀ p ∈ S, ∃ i ty, i < lo.L.nF ∧ p.2 = .fvar (ctx.hiAt 0 + i) ty) ∧
  (∀ g ∈ lo.ginfo, nestInstType (m := CheckM) ctx (ctx.hiAt 0 + lo.L.nF)
    ⟨g.1, kc.lvls, lo.L.dsF⟩ = .ok g.2) ∧
  crestsK kc.lvls lo.L.dsF
    (lo.ginfo.mapIdx fun g (n, _, ty) => (n, Expr.fvar (ctx.hiAt 0 + lo.L.nF + g) ty)) lo.ctors
    = some lo.crests ∧
  (∃ ty, ops.inferType env (ctx.hiAt 0 + lo.L.nF)
    (Expr.mkAppN (.const ((groupOfK ctx kc.cname).headD kc.cname) kc.lvls) lo.L.dsF) = .ok ty) ∧
  (∀ c ∈ lo.crests, ∃ ty sv, ops.inferType env lo.L.hi c = .ok ty ∧
    ops.ensureSort env lo.L.hi ty = .ok sv)

/-! ## The canonical group -/

theorem mem_groupOfK {C n : Name} (h : n ∈ groupOfK ctx C) : n = C ∨ n ∈ nestBlockOf ctx C := by
  unfold groupOfK at h
  simp only at h
  split at h
  · exact Or.inr (List.mem_eraseDups.mp h)
  · rcases List.mem_cons.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_eraseDups.mp h)

theorem self_mem_groupOfK (C : Name) : C ∈ groupOfK ctx C := by
  unfold groupOfK
  simp only
  split
  · rename_i h; simpa using h
  · exact List.mem_cons_self

theorem groupOfK_nodup (C : Name) : (groupOfK ctx C).Nodup := by
  unfold groupOfK
  simp only
  split
  · exact posD_nodup_eraseDups _
  · rename_i h
    refine List.nodup_cons.mpr ⟨fun hm => h (by simpa using hm), posD_nodup_eraseDups _⟩

theorem groupOfK_ne_nil (C : Name) : groupOfK ctx C ≠ [] := by
  intro h; have := self_mem_groupOfK (ctx := ctx) C; rw [h] at this; simp at this

theorem groupOfK_head_mem (C : Name) : (groupOfK ctx C).headD C ∈ groupOfK ctx C := by
  cases h : groupOfK ctx C with
  | nil => exact absurd h (groupOfK_ne_nil C)
  | cons x xs => simp

/-! ## Pieces -/

/-- A typing step into a sort succeeded: inferred, then a sort. -/
theorem typeAtK_ok_sort {d : Nat} {e : Expr}
    (h : typeAtK (m := CheckM) ops env d e true = .ok ()) :
    ∃ ty sv, ops.inferType env d e = .ok ty ∧ ops.ensureSort env d ty = .ok sv := by
  unfold typeAtK at h
  rcases tryCatchK_ok h with h | ⟨err, _, h⟩
  · simp only [bind, Except.bind, if_true] at h
    split at h
    · simp at h
    rename_i ty hty
    split at h
    · simp at h
    rename_i sv hsv
    exact ⟨ty, sv, hty, hsv⟩
  · exfalso
    revert h
    split
    · split <;> exact throwK_ne_ok
    · exact throwK_ne_ok

theorem typeCrestsK_ok {d : Nat} :
    ∀ (cs : List Expr), typeCrestsK (m := CheckM) ops env d cs = .ok () →
      ∀ c ∈ cs, ∃ ty sv, ops.inferType env d c = .ok ty ∧ ops.ensureSort env d ty = .ok sv
  | [], _, c, hc => nomatch hc
  | c :: cs, h, x, hx => by
    simp only [typeCrestsK, bind, Except.bind] at h
    split at h
    · simp at h
    rename_i u hu
    rcases List.mem_cons.mp hx with rfl | hx
    · exact typeAtK_ok_sort hu
    · exact typeCrestsK_ok cs h x hx

theorem groupInfoK_ok {us : List Level} {dsF : List Expr} {hiK : Nat} :
    ∀ (gs : List Name) (gi : List (Name × Nat × Expr)),
      groupInfoK (m := CheckM) ctx us dsF hiK gs = .ok gi →
      gi.map (·.1) = gs ∧ ∀ g ∈ gi, nestInstType (m := CheckM) ctx hiK ⟨g.1, us, dsF⟩ = .ok g.2
  | [], gi, h => by
    simp only [groupInfoK, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun _ hg => nomatch hg⟩
  | g :: gs, gi, h => by
    simp only [groupInfoK, bind, Except.bind, pure, Except.pure] at h
    split at h
    · simp at h
    rename_i r hr
    split at h
    · simp at h
    rename_i rest hrest
    simp only [Except.ok.injEq] at h
    subst h
    obtain ⟨h1, h2⟩ := groupInfoK_ok gs rest hrest
    refine ⟨by simp [h1], fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hr
    · exact h2 x hx

/-- **The monadic group listing is the pure one** (at `nestContainer`). -/
theorem groupCtorsK_ok {nPc : Nat} :
    ∀ (cs : List Name) (ctors : List (ConstantVal × Nat)),
      groupCtorsK (m := CheckM) (nestContainer ctx) nPc cs = .ok ctors →
      groupCtors ctx nPc cs = some ctors
  | [], ctors, h => by
    simp only [groupCtorsK, pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl
  | c :: cs, ctors, h => by
    simp only [groupCtorsK, bind, Except.bind, pure, Except.pure] at h
    split at h
    · simp at h
    rename_i q hq
    have hq' := unwrapOr_ok hq
    obtain ⟨nP', L⟩ := q
    split at h
    · rename_i hok
      split at h
      · simp at h
      rename_i rest hrest
      simp only [Except.ok.injEq] at h
      subst h
      simp only [groupCtors, hq']
      rw [if_pos (by simpa using hok), groupCtorsK_ok cs rest hrest]
      rfl
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **The layout's layout-typing, inverted**. -/
theorem layoutTypeK_ok {kc : NestKey} {gnames : List Name} {ctors : List (ConstantVal × Nat)}
    {S : List (NestKey × Expr)} {nF : Nat} {dsF : List Expr} {ginfo : List (Name × Nat × Expr)}
    {crests : List Expr}
    (h : layoutTypeK (m := CheckM) ops env ctx kc gnames ctors S nF = .ok (dsF, ginfo, crests)) :
    dsF = kc.ds.map (absKeysK S) ∧ ginfo.map (·.1) = gnames ∧
      (∀ g ∈ ginfo, nestInstType (m := CheckM) ctx (ctx.hiAt 0 + nF) ⟨g.1, kc.lvls, dsF⟩ = .ok g.2) ∧
      crestsK kc.lvls dsF
        (ginfo.mapIdx fun g (n, _, ty) => (n, Expr.fvar (ctx.hiAt 0 + nF + g) ty)) ctors
        = some crests ∧
      (∃ ty, ops.inferType env (ctx.hiAt 0 + nF) (Expr.mkAppN (.const kc.cname kc.lvls) dsF)
        = .ok ty) ∧
      ∀ c ∈ crests, ∃ ty sv, ops.inferType env (ctx.hiAt 0 + nF + ginfo.length) c = .ok ty ∧
        ops.ensureSort env (ctx.hiAt 0 + nF + ginfo.length) ty = .ok sv := by
  simp only [layoutTypeK, bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  rename_i gi hgi
  split at h
  · simp at h
  rename_i cr hcr
  split at h
  · simp at h
  rename_i u hu
  split at h
  · simp at h
  rename_i u₂ hu₂
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  obtain ⟨h1, h2⟩ := groupInfoK_ok _ _ hgi
  exact ⟨rfl, h1, h2, unwrapOr_ok hcr, typeAtK_ok hu, typeCrestsK_ok _ hu₂⟩

/-- The flexible substitution sends every key to a family `hiAt0 + i`,
`i` below the number of flexible families. -/
theorem flexSubstK_fvar {reps : List NestKey} {als : List (NestKey × Nat)}
    {fl : List (Nat × Expr × Nat)} :
    ∀ p ∈ flexSubstK ctx reps als fl, ∃ i ty, i < fl.length ∧ p.2 = .fvar (ctx.hiAt 0 + i) ty := by
  intro p hp
  unfold flexSubstK at hp
  obtain ⟨rz, hrz, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem hrz
  rw [List.getElem_mapIdx] at he
  have hi' : i < fl.length := by simpa using hi
  refine ⟨i, fl[i].2.1, hi', ?_⟩
  subst he
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hp
    rfl
  · obtain ⟨a, -, rfl⟩ := List.mem_map.mp hp
    rfl

/-! ## The spec -/

/-- **What a successful layout guarantees** (`LayoutSpecK`). -/
theorem nestLayoutK_spec {kc : NestKey} {lo : LayoutOutK}
    (h : nestLayoutK (m := CheckM) ops env ctx (nestContainer ctx) kc = .ok lo) :
    LayoutSpecK ops env ctx kc lo := by
  simp only [nestLayoutK, bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  rename_i q hq
  have hq' := unwrapOr_ok hq
  split at h
  · simp at h
  rename_i ctors hctors
  split at h
  rotate_left
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  rename_i hnd
  split at h
  · simp at h
  rename_i ra hra
  obtain ⟨reps, als⟩ := ra
  split at h
  · simp at h
  rename_i fl hfl
  split at h
  · simp at h
  rename_i r hr
  obtain ⟨dsF, ginfo, crests⟩ := r
  simp only [Except.ok.injEq] at h
  subst h
  have hlt : layoutTypeK (m := CheckM) ops env ctx
      { kc with cname := (groupOfK ctx kc.cname).headD kc.cname } (groupOfK ctx kc.cname)
      ctors (flexSubstK ctx reps als fl) fl.length = .ok (dsF, ginfo, crests) := by
    rcases tryCatchK_ok hr with hr | ⟨err, _, hr⟩
    · exact hr
    · exfalso
      revert hr
      split
      · split <;> exact throwK_ne_ok
      · exact throwK_ne_ok
  obtain ⟨hds, hnames, hinst, hcr, hkty, hty⟩ := layoutTypeK_ok hlt
  refine ⟨⟨q.1, q.2, hq', groupCtorsK_ok _ _ hctors⟩, ?_, rfl, rfl, hnames, rfl,
    ⟨_, hds, fun p hp => flexSubstK_fvar p hp⟩, hinst, hcr, hkty, hty⟩
  intro c hc
  exact List.all_eq_true.mp hnd c hc

/-- A node's derivation carries its layout's spec. -/
theorem PosDKH.node_spec {kc : NestKey} {lo : LayoutOutK} {met : List Nat}
    (h : PosDKH ops env ctx hk (.node kc lo met)) : LayoutSpecK ops env ctx kc lo := by
  cases h with
  | node hlay _ => exact nestLayoutK_spec hlay

end ConLeche
