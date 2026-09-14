module

public import ConLeche.Verify.Inductives.NestedLeaves
public import ConLeche.Verify.Lits
import ConLeche.Verify.EnvWF

public section

/-!
# The nested elimination and the literal guard (task #311)

The model reads a pin's components at the formers' environment `env₁`,
and `denoteMeta`'s literal arms are guarded there: the DOWNWARD
transfer (`denoteMeta_envExtend_down`, task #310) asks
`litsResolve env₁` of its subject.  The pins are not the checker's
input — the elimination mints them — so the condition is established
the way `elimNested_leaves` and `elimNested_pins_noProjAt` establish
theirs: a loop invariant (`LitInv`) over the walk.

The walk mints no literal of its own.  What it puts into a pin is the
container applied to arguments of the walked constructor type, and
what it puts into a copy's constructors is the container's STORED
types — which resolve at `env` (`EnvWF`), hence have their literals
guarded there and at every environment `env` extends into — closed
over the first former's binders.  So the pins' literals are guarded
wherever the block's own (annotated) constructor types' and the first
former's type's are: `elimNested_pins_litsOk`.

The guard itself and its closure kit (`Expr.LitsOk`) are
`ConLeche/Verify/Lits.lean`'s; this module is the instance at the
elimination.
-/

namespace ConLeche


namespace Expr

variable {envL : Env}

/-- An opening's residual carries the guard (its variables carry it
outright — the guard is blind to `fvar` annotations). -/
theorem litsOk_openPisAtFvars :
    ∀ (n : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {o : Expr},
      openPisAtFvars n e d = some (fvs, o) → LitsOk env e →
      (∀ x ∈ fvs, LitsOk env x) ∧ LitsOk env o
  | 0, e, d, fvs, o, hop, he => by
    simp only [ConLeche.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    exact ⟨(fun x hx => nomatch hx), he⟩
  | n + 1, e, d, fvs, o, hop, he => by
    match e, he, hop with
    | .forallE dom bd mb, he, hop =>
      simp only [ConLeche.openPisAtFvars] at hop
      split at hop
      · next fvs₁ e₁ h₁ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        rw [litsOk_forallE] at he
        obtain ⟨hfvs, ho⟩ :=
          litsOk_openPisAtFvars n h₁ (LitsOk.instantiate1 litsOk_fvar bd 0 he.2)
        refine ⟨fun x hx => ?_, ho⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact litsOk_fvar
        · exact hfvs x hx
      · exact nomatch hop

end Expr

open Expr in
/-- Closing a body over binders whose domains are guarded keeps the
guard. -/
theorem litsOk_closeTelescope {envL : Env} :
    ∀ (bs : List (Expr × BinderMeta)) (k : Nat) {body : Expr},
      (∀ b ∈ bs, LitsOk envL b.1) → LitsOk envL body →
      LitsOk envL (closeTelescope bs k body)
  | [], _, _, _, hb => hb
  | (_dom, _bm) :: bs, k, _body, hbs, hb =>
    litsOk_forallE.mpr ⟨hbs _ List.mem_cons_self,
      LitsOk.abstract1 _ k 0
        (litsOk_closeTelescope bs (k + 1) (fun b hb' => hbs b (List.mem_cons_of_mem _ hb')) hb)⟩

/-! ## The containers' literals are guarded -/

/-- What the elimination copies out of a container has its literals
guarded at `envL`: every member's stored constructor types are the
environment's. -/
@[expose] def ContainersLitsOk (envL env : Env) : Prop :=
  ∀ (I : Name) (ci : ContainerInfo), containerInfo? env I = some ci →
    ∀ J ∈ ci.members, ∀ c ∈ J.ctors, Expr.LitsOk envL c.type

/-- Under `EnvWF`, the containers' stored constructor types RESOLVE at
`env`, hence have their literals guarded there — and at any
environment `env` extends into. -/
theorem containersLitsOk_of_wf {env envL : Env} (hwf : EnvWF env)
    (hm : ∀ n : Name, (env.find? n).isSome = true → (envL.find? n).isSome = true) :
    ContainersLitsOk envL env := by
  intro I ci hci J hJ c hc
  obtain ⟨-, hctors⟩ := containerInfo?_stored hci J hJ
  obtain ⟨cvc, nPc, nF, hfc, hty⟩ := hctors c hc
  rw [hty]
  exact Expr.LitsOk.mono hm
    (Expr.LitsOk.of_constsResolve (hwf _ (List.mem_of_find?_eq_some hfc)).2.2.1)

/-! ## The invariant -/

/-- Every pin and every constructor type of the growing list has its
literals guarded at `envL`. -/
structure LitInv (envL : Env) (st : ElimState) : Prop where
  pins : ∀ q ∈ st.pins, Expr.LitsOk envL q.pin
  ctors : ∀ t ∈ st.types, ∀ c ∈ t.ctors, Expr.LitsOk envL c.2.1

open Expr in
/-- A mint keeps the invariant: the new pins are the container applied
to arguments of the walked term, the new copies' constructors are the
container's stored types at those arguments, closed over the first
former's binders. -/
theorem mkCopies_litInv {env envL : Env} {pbs : List (Expr × BinderMeta)}
    {lvls : List Level} {Ds : List Expr} {I : Name} {base size : Nat}
    (hpbs : ∀ b ∈ pbs, LitsOk envL b.1) (hDs : ∀ D ∈ Ds, LitsOk envL D) :
    ∀ {members : List ContainerMember} {st st' : ElimState} {got : Option Name},
      mkCopies env pbs lvls Ds I base size members st = .ok (st', got) →
      (∀ J ∈ members, ∀ c ∈ J.ctors, LitsOk envL c.type) →
      LitInv envL st → LitInv envL st' := by
  intro members st st' got hmk hcl hinv
  obtain ⟨copies, hclen, hty, hpin, hall⟩ := mkCopies_spec hmk
  refine ⟨fun q hq => ?_, fun t ht c hc => ?_⟩
  · rw [hpin] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hinv.pins q hq
    · obtain ⟨j, hj⟩ := List.getElem?_of_mem hq
      rw [List.getElem?_zipWith] at hj
      split at hj
      · obtain rfl := Option.some.inj hj
        exact LitsOk.mkAppN litsOk_const hDs
      · exact nomatch hj
  · rw [hty] at ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hinv.ctors t ht c hc
    · obtain ⟨j, hj⟩ := List.getElem?_of_mem ht
      have hjJ : j < members.length := by
        rw [← hclen]; exact (List.getElem?_eq_some_iff.mp hj).1
      obtain ⟨copy, hcopy, hmkc, -⟩ := hall j _ (List.getElem?_eq_getElem hjJ)
      obtain rfl : t = copy := Option.some.inj (hj.symm.trans hcopy)
      obtain ⟨-, -, -, hctors⟩ := mkCopy_inv hmkc
      obtain ⟨l, hl⟩ := List.getElem?_of_mem hc
      have hlJ : l < members[j].ctors.length := by
        have := (List.getElem?_eq_some_iff.mp hl).1
        rw [(mkCopy_inv hmkc).2.2.1] at this
        exact this
      obtain ⟨cI, hcI, hl'⟩ := hctors l _ (List.getElem?_eq_getElem hlJ)
      obtain rfl := Option.some.inj (hl.symm.trans hl')
      show LitsOk envL (closeTelescope pbs 0 cI)
      refine litsOk_closeTelescope pbs 0 hpbs (LitsOk.instPis hcI ?_ hDs)
      exact LitsOk.instantiateLevelParams _ _ _
        (hcl _ (List.getElem_mem hjJ) _ (List.getElem_mem hlJ))

open Expr in
/-- A fired replacement: the state keeps the invariant and the answer
is guarded. -/
theorem replaceIfNested_lits {env envL : Env} {blvls : List Level}
    {params : List Expr} {pbs : List (Expr × BinderMeta)} (hcc : ContainersLitsOk envL env)
    (hpbs : ∀ b ∈ pbs, LitsOk envL b.1) (hpar : ∀ p ∈ params, LitsOk envL p)
    {st st' : ElimState} {e r : Expr}
    (h : replaceIfNested env blvls params pbs st e = .ok (some (r, st')))
    (he : LitsOk envL e) (hinv : LitInv envL st) :
    LitInv envL st' ∧ LitsOk envL r := by
  have hidx : ∀ (n : Nat), ∀ a ∈ e.getAppArgs.drop n, LitsOk envL a :=
    fun n a ha => he.getAppArgs a (List.mem_of_mem_drop ha)
  have hans : ∀ (aux : Name) (n : Nat),
      LitsOk envL (Expr.mkAppN (Expr.mkAppN (.const aux blvls) params) (e.getAppArgs.drop n)) :=
    fun aux n => LitsOk.mkAppN (LitsOk.mkAppN litsOk_const hpar) (hidx n)
  unfold replaceIfNested at h
  simp only [bind, Except.bind] at h
  split at h
  · split at h
    · next I lvls hfn =>
      split at h
      · split at h
        · exact nomatch h
        · split at h
          · split at h
            · exact nomatch h
            · exact nomatch h
          · next ci hci =>
            split at h
            · exact nomatch h
            · split at h
              · exact nomatch h
              · next nested hocc =>
                split at h
                · exact nomatch h
                · split at h
                  · next q hq =>
                    simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq,
                      Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl⟩ := h
                    exact ⟨hinv, hans _ _⟩
                  · split at h
                    · exact nomatch h
                    · next p hmk =>
                      obtain ⟨stq, gotq⟩ := p
                      split at h
                      · exact nomatch h
                      · next auxI hgot =>
                        simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq,
                          Prod.mk.injEq] at h
                        obtain ⟨rfl, rfl⟩ := h
                        refine ⟨mkCopies_litInv hpbs ?_ hmk (hcc I ci hci) hinv, hans _ _⟩
                        exact fun D hD => he.getAppArgs D (List.mem_of_mem_take hD)
      · exact nomatch h
    · exact nomatch h
  · exact nomatch h

open Expr in
/-- **The walk keeps the invariant**, and its output is guarded
whenever its input is. -/
theorem replaceAllNested_lits {env envL : Env} {blvls : List Level}
    {params : List Expr} {pbs : List (Expr × BinderMeta)} (hcc : ContainersLitsOk envL env)
    (hpbs : ∀ b ∈ pbs, LitsOk envL b.1) (hpar : ∀ p ∈ params, LitsOk envL p) :
    ∀ (e : Expr) {st : ElimState} {r : Expr × ElimState},
      replaceAllNested env blvls params pbs st e = .ok r → LitsOk envL e →
      LitInv envL st → LitInv envL r.2 ∧ LitsOk envL r.1 := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro st r h he hinv
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ⟨hinv, he⟩
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_lits hcc hpbs hpar hr' he hinv
      · split at h
        · contradiction
        · next x₁ st₁ h₁ =>
          split at h
          · contradiction
          · next x₂ st₂ h₂ =>
            obtain rfl := Except.ok.inj h
            obtain ⟨hf, ha⟩ := litsOk_app.mp he
            obtain ⟨hinv₁, hx₁⟩ := ihf h₁ hf hinv
            obtain ⟨hinv₂, hx₂⟩ := iha h₂ ha hinv₁
            exact ⟨hinv₂, litsOk_app.mpr ⟨hx₁, hx₂⟩⟩
  | lam ty b bm ihty ihb =>
    intro st r h he hinv
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ⟨hinv, he⟩
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_lits hcc hpbs hpar hr' he hinv
      · split at h
        · contradiction
        · next x₁ st₁ h₁ =>
          split at h
          · contradiction
          · next x₂ st₂ h₂ =>
            obtain rfl := Except.ok.inj h
            obtain ⟨hf, ha⟩ := litsOk_lam.mp he
            obtain ⟨hinv₁, hx₁⟩ := ihty h₁ hf hinv
            obtain ⟨hinv₂, hx₂⟩ := ihb h₂ ha hinv₁
            exact ⟨hinv₂, litsOk_lam.mpr ⟨hx₁, hx₂⟩⟩
  | forallE ty b bm ihty ihb =>
    intro st r h he hinv
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ⟨hinv, he⟩
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_lits hcc hpbs hpar hr' he hinv
      · split at h
        · contradiction
        · next x₁ st₁ h₁ =>
          split at h
          · contradiction
          · next x₂ st₂ h₂ =>
            obtain rfl := Except.ok.inj h
            obtain ⟨hf, ha⟩ := litsOk_forallE.mp he
            obtain ⟨hinv₁, hx₁⟩ := ihty h₁ hf hinv
            obtain ⟨hinv₂, hx₂⟩ := ihb h₂ ha hinv₁
            exact ⟨hinv₂, litsOk_forallE.mpr ⟨hx₁, hx₂⟩⟩
  | letE ty v b ihty ihv ihb =>
    intro st r h he hinv
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ⟨hinv, he⟩
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_lits hcc hpbs hpar hr' he hinv
      · split at h
        · contradiction
        · next x₁ st₁ h₁ =>
          split at h
          · contradiction
          · next x₂ st₂ h₂ =>
            split at h
            · contradiction
            · next x₃ st₃ h₃ =>
              obtain rfl := Except.ok.inj h
              obtain ⟨h1, h2, h3⟩ := litsOk_letE.mp he
              obtain ⟨hinv₁, hx₁⟩ := ihty h₁ h1 hinv
              obtain ⟨hinv₂, hx₂⟩ := ihv h₂ h2 hinv₁
              obtain ⟨hinv₃, hx₃⟩ := ihb h₃ h3 hinv₂
              exact ⟨hinv₃, litsOk_letE.mpr ⟨hx₁, hx₂, hx₃⟩⟩
  | proj s j x ihx =>
    intro st r h he hinv
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ⟨hinv, he⟩
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_lits hcc hpbs hpar hr' he hinv
      · split at h
        · contradiction
        · next x₁ st₁ h₁ =>
          obtain rfl := Except.ok.inj h
          have hx := litsOk_proj.mp he
          obtain ⟨hinv₁, hx₁⟩ := ihx h₁ hx hinv
          exact ⟨hinv₁, litsOk_proj.mpr hx₁⟩
  | bvar j =>
    intro st r h he hinv
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ⟨hinv, he⟩
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_lits hcc hpbs hpar hr' he hinv
      · obtain rfl := Except.ok.inj h
        exact ⟨hinv, he⟩
  | fvar idx ty _ =>
    intro st r h he hinv
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ⟨hinv, he⟩
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_lits hcc hpbs hpar hr' he hinv
      · obtain rfl := Except.ok.inj h
        exact ⟨hinv, he⟩
  | sort u =>
    intro st r h he hinv
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ⟨hinv, he⟩
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_lits hcc hpbs hpar hr' he hinv
      · obtain rfl := Except.ok.inj h
        exact ⟨hinv, he⟩
  | const n us =>
    intro st r h he hinv
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ⟨hinv, he⟩
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_lits hcc hpbs hpar hr' he hinv
      · obtain rfl := Except.ok.inj h
        exact ⟨hinv, he⟩
  | lit l =>
    intro st r h he hinv
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ⟨hinv, he⟩
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_lits hcc hpbs hpar hr' he hinv
      · obtain rfl := Except.ok.inj h
        exact ⟨hinv, he⟩

open Expr in
/-- One type's constructors rewritten: the invariant is kept and the
rewritten constructors are guarded. -/
theorem elimCtors_lits {env envL : Env} {blvls : List Level} {nP : Nat}
    {params : List Expr} {pbs₀ : List (Expr × BinderMeta)} (hcc : ContainersLitsOk envL env)
    (hpbs : ∀ b ∈ pbs₀, LitsOk envL b.1) (hpar : ∀ p ∈ params, LitsOk envL p) :
    ∀ {cs : List (Name × Expr × Nat)} {st : ElimState}
      {r : List (Name × Expr × Nat) × ElimState},
      elimCtors env blvls nP params pbs₀ cs st = .ok r →
      (∀ c ∈ cs, LitsOk envL c.2.1) → LitInv envL st →
      LitInv envL r.2 ∧ ∀ c ∈ r.1, LitsOk envL c.2.1
  | [], st, r, h, _, hinv => by
    simp only [elimCtors, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨hinv, fun c hc => nomatch hc⟩
  | (c, cty, nF) :: rest, st, r, h, hcs, hinv => by
    simp only [elimCtors, bind, Except.bind] at h
    split at h
    · next pbs rest₀ hstrip =>
      split at h
      · next cbody hinst =>
        split at h
        · contradiction
        · next q st₁ hq =>
          split at h
          · contradiction
          · next rest' st₂ hrest =>
            simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            have hcty : LitsOk envL cty := hcs _ List.mem_cons_self
            have hpbs' := LitsOk.stripPis_doms nP hstrip hcty
            obtain ⟨hinv₁, hbody⟩ := replaceAllNested_lits hcc hpbs hpar _ hq
              (LitsOk.instPis hinst hcty hpar) hinv
            obtain ⟨hinv₂, hrest'⟩ := elimCtors_lits hcc hpbs hpar hrest
              (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')) hinv₁
            refine ⟨hinv₂, fun c' hc' => ?_⟩
            rcases List.mem_cons.mp hc' with rfl | hc'
            · exact litsOk_closeTelescope pbs 0 hpbs' hbody
            · exact hrest' c' hc'
      · contradiction
    · contradiction

open Expr in
/-- The worklist keeps the invariant. -/
theorem elimLoop_lits {env envL : Env} {blvls : List Level} {nP : Nat}
    {params : List Expr} {pbs₀ : List (Expr × BinderMeta)} (hcc : ContainersLitsOk envL env)
    (hpbs : ∀ b ∈ pbs₀, LitsOk envL b.1) (hpar : ∀ p ∈ params, LitsOk envL p) :
    ∀ {fuel qhead : Nat} {st st' : ElimState},
      elimLoop env blvls nP params pbs₀ fuel qhead st = .ok st' →
      LitInv envL st → LitInv envL st'
  | 0, _, _, _, h, _ => nomatch h
  | fuel + 1, qhead, st, st', h, hinv => by
    simp only [elimLoop] at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact hinv
    · next t ht =>
      split at h
      · exact nomatch h
      · next cs' st₁ hcs =>
        have hmem : t ∈ st.types := List.mem_of_getElem? ht
        obtain ⟨hinv₁, hcs'⟩ := elimCtors_lits hcc hpbs hpar hcs (hinv.ctors t hmem) hinv
        refine elimLoop_lits hcc hpbs hpar h ⟨hinv₁.pins, fun t' ht' c hc => ?_⟩
        rcases List.mem_or_eq_of_mem_set ht' with ht' | rfl
        · exact hinv₁.ctors t' ht' c hc
        · exact hcs' c hc

open Expr in
/-- **THE PINS' LITERALS ARE GUARDED**: at the elimination's end every
pin's literals have their support stored at `envL`, given the block's
own constructor types and the first former's type guarded there.  The
walk mints no literal of its own: a pin is the container applied to
arguments of a walked term, and a copy's constructors are the
container's stored types instantiated at those arguments and closed
over the first former's binders. -/
theorem elimNested_pins_litsOk {env envL : Env} {nP : Nat} {lps : List Name}
    {types : List AuxType} {st : ElimState}
    (hwf : EnvWF env)
    (hm : ∀ n : Name, (env.find? n).isSome = true → (envL.find? n).isSome = true)
    (h : elimNested env nP lps types = .ok st)
    (hty : ∀ t ∈ types, ∀ c ∈ t.ctors, Expr.LitsOk envL c.2.1)
    (ht₀ : ∀ t₀ ∈ types.head?, Expr.LitsOk envL t₀.type) :
    ∀ q ∈ st.pins, Expr.LitsOk envL q.pin := by
  have hcc : ContainersLitsOk envL env := containersLitsOk_of_wf hwf hm
  unfold elimNested at h
  split at h
  · next t₀ hh =>
    split at h
    · next params body hop =>
      split at h
      · next pbs body₀ hstrip =>
        have hcl : LitsOk envL t₀.type := ht₀ t₀ (by rw [hh]; exact rfl)
        have hpar : ∀ p ∈ params, LitsOk envL p :=
          (litsOk_openPisAtFvars nP hop hcl).1
        have hpbs : ∀ b ∈ pbs, LitsOk envL b.1 := LitsOk.stripPis_doms nP hstrip hcl
        have hinv₀ : LitInv envL ⟨types, [], 1⟩ :=
          ⟨(fun q hq => nomatch hq), fun t ht c hc => hty t ht c hc⟩
        exact (elimLoop_lits hcc hpbs hpar h hinv₀).pins
      · contradiction
    · contradiction
  · contradiction

end ConLeche
