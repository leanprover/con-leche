module

public import ConLeche.Verify.Inductives.NestedLeaves
public import ConLeche.Verify.Inductives.MutualInv
public import ConLeche.Verify.ProjSlots
import ConLeche.Verify.Inductives.StructRec
import ConLeche.Verify.Inductives.FixRec
import ConLeche.Verify.EnvWF
import ConLeche.Verify.Extend.Inversions

public section

/-!
# The nested elimination and a projection slot (task #309)

The model reads a pin's inference at the opened frame of the block's
first former, and a `.proj T i` node whose slot the environment does
not answer has no denotation.  Two facts close that gap for the nested
route, both about a slot `T, i` the PRE-BLOCK environment does not
carry:

* `checkMutualCore_findProj_fresh` — the SCRATCH install adds a
  projection table only for a member of the block it installs, and
  those names are fresh at the environment it started from.  So a slot
  that the auxiliary environment answers and the pre-block one does not
  belongs to a member name the pre-block environment does not carry.
* `elimNested_pins_noProjAt` — every pin the elimination mints carries
  no `.proj T i` node, given that the block's own constructors and the
  first former's type carry none.  This is the `NoProjAt` twin of
  `elimNested_leaves` (`ConLeche/Verify/Inductives/NestedLeaves.lean`)
  and runs through the same loop invariant: the pins are the container
  applied to arguments of a walked constructor type, the copies'
  constructors are the container's stored types — which RESOLVE at an
  environment without `T`, hence carry no node of the slot
  (`Expr.noProjAt_of_constsResolve`) — instantiated at those arguments
  and closed over the first former's binders.
-/

namespace ConLeche

/-! ## Openings, instantiations and telescopes keep `NoProjAt` -/

namespace Expr

variable {T : Name} {i : Nat}

/-- `instPis` keeps the absence of a slot's node. -/
theorem noProjAt_instPis :
    ∀ {e : Expr} {args : List Expr} {r : Expr}, Expr.instPis e args = some r →
      NoProjAt T i e → (∀ a ∈ args, NoProjAt T i a) → NoProjAt T i r
  | e, [], r, h, he, _ => by
    simp only [Expr.instPis, Option.some.injEq] at h
    subst h
    exact he
  | .forallE dom body m, a :: as, r, h, he, hargs => by
    simp only [Expr.instPis] at h
    rw [noProjAt_forallE] at he
    exact noProjAt_instPis h
      (NoProjAt.instantiate1 (hargs a List.mem_cons_self) body 0 he.2)
      (fun x hx => hargs x (List.mem_cons_of_mem _ hx))
  | .bvar _, _ :: _, _, h, _, _ | .fvar _ _, _ :: _, _, h, _, _ | .sort _, _ :: _, _, h, _, _
  | .const _ _, _ :: _, _, h, _, _ | .app _ _, _ :: _, _, h, _, _
  | .lam _ _ _, _ :: _, _, h, _, _ | .letE _ _ _, _ :: _, _, h, _, _
  | .lit _, _ :: _, _, h, _, _ | .proj _ _ _, _ :: _, _, h, _, _ => by
    simp [Expr.instPis] at h

/-- An opening's variables and residual carry no node of the slot when
the opened type carries none. -/
theorem noProjAt_openPisAtFvars :
    ∀ (n : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {o : Expr},
      openPisAtFvars n e d = some (fvs, o) → NoProjAt T i e →
      (∀ x ∈ fvs, NoProjAt T i x) ∧ NoProjAt T i o
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
        rw [noProjAt_forallE] at he
        have hfv : NoProjAt T i (Expr.fvar d dom) := noProjAt_fvar.mpr he.1
        obtain ⟨hfvs, ho⟩ :=
          noProjAt_openPisAtFvars n h₁ (NoProjAt.instantiate1 hfv bd 0 he.2)
        refine ⟨fun x hx => ?_, ho⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hfv
        · exact hfvs x hx
      · exact nomatch hop

end Expr

open Expr in
/-- Closing a body over binders that carry no node of the slot keeps
the absence. -/
theorem noProjAt_closeTelescope {T : Name} {i : Nat} :
    ∀ (bs : List (Expr × BinderMeta)) (k : Nat) {body : Expr},
      (∀ b ∈ bs, NoProjAt T i b.1) → NoProjAt T i body →
      NoProjAt T i (closeTelescope bs k body)
  | [], _, _, _, hb => hb
  | (_dom, _bm) :: bs, k, _body, hbs, hb =>
    noProjAt_forallE.mpr ⟨hbs _ List.mem_cons_self,
      NoProjAt.abstract1 _ k 0
        (noProjAt_closeTelescope bs (k + 1) (fun b hb' => hbs b (List.mem_cons_of_mem _ hb')) hb)⟩

/-! ## The containers carry no node of an unstored slot -/

/-- What the elimination copies out of a container carries no `.proj T i`
node: every member's stored constructor types are the environment's, and
the environment does not carry `T`. -/
@[expose] def ContainersNoProj (T : Name) (i : Nat) (env : Env) : Prop :=
  ∀ (I : Name) (ci : ContainerInfo), containerInfo? env I = some ci →
    ∀ J ∈ ci.members, ∀ c ∈ J.ctors, Expr.NoProjAt T i c.type

/-- Under `EnvWF`, a slot the environment does not carry occurs in no
container's stored constructor type: the stored types resolve. -/
theorem containersNoProj_of_wf {env : Env} {T : Name} {i : Nat} (hwf : EnvWF env)
    (hT : env.find? T = none) : ContainersNoProj T i env := by
  intro I ci hci J hJ c hc
  obtain ⟨-, hctors⟩ := containerInfo?_stored hci J hJ
  obtain ⟨cvc, nPc, nF, hfc, hty⟩ := hctors c hc
  rw [hty]
  exact Expr.noProjAt_of_constsResolve hT _ (hwf _ (List.mem_of_find?_eq_some hfc)).2.2.1

/-! ## The invariant -/

/-- Every pin and every constructor type of the growing list carries no
`.proj T i` node. -/
structure ProjInv (T : Name) (i : Nat) (st : ElimState) : Prop where
  pins : ∀ q ∈ st.pins, Expr.NoProjAt T i q.pin
  ctors : ∀ t ∈ st.types, ∀ c ∈ t.ctors, Expr.NoProjAt T i c.2.1

open Expr in
/-- A mint keeps the invariant: the new pins are the container applied
to arguments of the walked term, the new copies' constructors are the
container's stored types at those arguments, closed over the first
former's binders. -/
theorem mkCopies_projInv {env : Env} {T : Name} {i : Nat} {pbs : List (Expr × BinderMeta)}
    {lvls : List Level} {Ds : List Expr} {I : Name} {base size : Nat}
    (hpbs : ∀ b ∈ pbs, NoProjAt T i b.1) (hDs : ∀ D ∈ Ds, NoProjAt T i D) :
    ∀ {members : List ContainerMember} {st st' : ElimState} {got : Option Name},
      mkCopies env pbs lvls Ds I base size members st = .ok (st', got) →
      (∀ J ∈ members, ∀ c ∈ J.ctors, NoProjAt T i c.type) →
      ProjInv T i st → ProjInv T i st' := by
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
        exact NoProjAt.mkAppN noProjAt_const hDs
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
      show NoProjAt T i (closeTelescope pbs 0 cI)
      refine noProjAt_closeTelescope pbs 0 hpbs (noProjAt_instPis hcI ?_ hDs)
      exact NoProjAt.instantiateLevelParams _ _ _
        (hcl _ (List.getElem_mem hjJ) _ (List.getElem_mem hlJ))

open Expr in
/-- A fired replacement: the state keeps the invariant and the answer
carries no node of the slot. -/
theorem replaceIfNested_noProj {env : Env} {T : Name} {i : Nat} {blvls : List Level}
    {params : List Expr} {pbs : List (Expr × BinderMeta)} (hcc : ContainersNoProj T i env)
    (hpbs : ∀ b ∈ pbs, NoProjAt T i b.1) (hpar : ∀ p ∈ params, NoProjAt T i p)
    {st st' : ElimState} {e r : Expr}
    (h : replaceIfNested env blvls params pbs st e = .ok (some (r, st')))
    (he : NoProjAt T i e) (hinv : ProjInv T i st) :
    ProjInv T i st' ∧ NoProjAt T i r := by
  have hidx : ∀ (n : Nat), ∀ a ∈ e.getAppArgs.drop n, NoProjAt T i a :=
    fun n a ha => he.getAppArgs a (List.mem_of_mem_drop ha)
  have hans : ∀ (aux : Name) (n : Nat),
      NoProjAt T i (Expr.mkAppN (Expr.mkAppN (.const aux blvls) params) (e.getAppArgs.drop n)) :=
    fun aux n => NoProjAt.mkAppN (NoProjAt.mkAppN noProjAt_const hpar) (hidx n)
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
                        refine ⟨mkCopies_projInv hpbs ?_ hmk (hcc I ci hci) hinv, hans _ _⟩
                        exact fun D hD => he.getAppArgs D (List.mem_of_mem_take hD)
      · exact nomatch h
    · exact nomatch h
  · exact nomatch h

open Expr in
/-- **The walk keeps the invariant**, and its output carries no node of
the slot whenever its input carries none. -/
theorem replaceAllNested_noProj {env : Env} {T : Name} {i : Nat} {blvls : List Level}
    {params : List Expr} {pbs : List (Expr × BinderMeta)} (hcc : ContainersNoProj T i env)
    (hpbs : ∀ b ∈ pbs, NoProjAt T i b.1) (hpar : ∀ p ∈ params, NoProjAt T i p) :
    ∀ (e : Expr) {st : ElimState} {r : Expr × ElimState},
      replaceAllNested env blvls params pbs st e = .ok r → NoProjAt T i e →
      ProjInv T i st → ProjInv T i r.2 ∧ NoProjAt T i r.1 := by
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
        exact replaceIfNested_noProj hcc hpbs hpar hr' he hinv
      · split at h
        · contradiction
        · next x₁ st₁ h₁ =>
          split at h
          · contradiction
          · next x₂ st₂ h₂ =>
            obtain rfl := Except.ok.inj h
            obtain ⟨hf, ha⟩ := noProjAt_app.mp he
            obtain ⟨hinv₁, hx₁⟩ := ihf h₁ hf hinv
            obtain ⟨hinv₂, hx₂⟩ := iha h₂ ha hinv₁
            exact ⟨hinv₂, noProjAt_app.mpr ⟨hx₁, hx₂⟩⟩
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
        exact replaceIfNested_noProj hcc hpbs hpar hr' he hinv
      · split at h
        · contradiction
        · next x₁ st₁ h₁ =>
          split at h
          · contradiction
          · next x₂ st₂ h₂ =>
            obtain rfl := Except.ok.inj h
            obtain ⟨hf, ha⟩ := noProjAt_lam.mp he
            obtain ⟨hinv₁, hx₁⟩ := ihty h₁ hf hinv
            obtain ⟨hinv₂, hx₂⟩ := ihb h₂ ha hinv₁
            exact ⟨hinv₂, noProjAt_lam.mpr ⟨hx₁, hx₂⟩⟩
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
        exact replaceIfNested_noProj hcc hpbs hpar hr' he hinv
      · split at h
        · contradiction
        · next x₁ st₁ h₁ =>
          split at h
          · contradiction
          · next x₂ st₂ h₂ =>
            obtain rfl := Except.ok.inj h
            obtain ⟨hf, ha⟩ := noProjAt_forallE.mp he
            obtain ⟨hinv₁, hx₁⟩ := ihty h₁ hf hinv
            obtain ⟨hinv₂, hx₂⟩ := ihb h₂ ha hinv₁
            exact ⟨hinv₂, noProjAt_forallE.mpr ⟨hx₁, hx₂⟩⟩
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
        exact replaceIfNested_noProj hcc hpbs hpar hr' he hinv
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
              obtain ⟨h1, h2, h3⟩ := noProjAt_letE.mp he
              obtain ⟨hinv₁, hx₁⟩ := ihty h₁ h1 hinv
              obtain ⟨hinv₂, hx₂⟩ := ihv h₂ h2 hinv₁
              obtain ⟨hinv₃, hx₃⟩ := ihb h₃ h3 hinv₂
              exact ⟨hinv₃, noProjAt_letE.mpr ⟨hx₁, hx₂, hx₃⟩⟩
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
        exact replaceIfNested_noProj hcc hpbs hpar hr' he hinv
      · split at h
        · contradiction
        · next x₁ st₁ h₁ =>
          obtain rfl := Except.ok.inj h
          obtain ⟨hne, hx⟩ := noProjAt_proj.mp he
          obtain ⟨hinv₁, hx₁⟩ := ihx h₁ hx hinv
          exact ⟨hinv₁, noProjAt_proj.mpr ⟨hne, hx₁⟩⟩
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
        exact replaceIfNested_noProj hcc hpbs hpar hr' he hinv
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
        exact replaceIfNested_noProj hcc hpbs hpar hr' he hinv
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
        exact replaceIfNested_noProj hcc hpbs hpar hr' he hinv
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
        exact replaceIfNested_noProj hcc hpbs hpar hr' he hinv
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
        exact replaceIfNested_noProj hcc hpbs hpar hr' he hinv
      · obtain rfl := Except.ok.inj h
        exact ⟨hinv, he⟩

open Expr in
/-- One type's constructors rewritten: the invariant is kept and the
rewritten constructors carry no node of the slot. -/
theorem elimCtors_noProj {env : Env} {T : Name} {i : Nat} {blvls : List Level} {nP : Nat}
    {params : List Expr} {pbs₀ : List (Expr × BinderMeta)} (hcc : ContainersNoProj T i env)
    (hpbs : ∀ b ∈ pbs₀, NoProjAt T i b.1) (hpar : ∀ p ∈ params, NoProjAt T i p) :
    ∀ {cs : List (Name × Expr × Nat)} {st : ElimState}
      {r : List (Name × Expr × Nat) × ElimState},
      elimCtors env blvls nP params pbs₀ cs st = .ok r →
      (∀ c ∈ cs, NoProjAt T i c.2.1) → ProjInv T i st →
      ProjInv T i r.2 ∧ ∀ c ∈ r.1, NoProjAt T i c.2.1
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
            have hcty : NoProjAt T i cty := hcs _ List.mem_cons_self
            have hpbs' := NoProjAt.stripPis_doms nP hstrip hcty
            obtain ⟨hinv₁, hbody⟩ := replaceAllNested_noProj hcc hpbs hpar _ hq
              (noProjAt_instPis hinst hcty hpar) hinv
            obtain ⟨hinv₂, hrest'⟩ := elimCtors_noProj hcc hpbs hpar hrest
              (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')) hinv₁
            refine ⟨hinv₂, fun c' hc' => ?_⟩
            rcases List.mem_cons.mp hc' with rfl | hc'
            · exact noProjAt_closeTelescope pbs 0 hpbs' hbody
            · exact hrest' c' hc'
      · contradiction
    · contradiction

open Expr in
/-- The worklist keeps the invariant. -/
theorem elimLoop_noProj {env : Env} {T : Name} {i : Nat} {blvls : List Level} {nP : Nat}
    {params : List Expr} {pbs₀ : List (Expr × BinderMeta)} (hcc : ContainersNoProj T i env)
    (hpbs : ∀ b ∈ pbs₀, NoProjAt T i b.1) (hpar : ∀ p ∈ params, NoProjAt T i p) :
    ∀ {fuel qhead : Nat} {st st' : ElimState},
      elimLoop env blvls nP params pbs₀ fuel qhead st = .ok st' →
      ProjInv T i st → ProjInv T i st'
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
        obtain ⟨hinv₁, hcs'⟩ := elimCtors_noProj hcc hpbs hpar hcs (hinv.ctors t hmem) hinv
        refine elimLoop_noProj hcc hpbs hpar h ⟨hinv₁.pins, fun t' ht' c hc => ?_⟩
        rcases List.mem_or_eq_of_mem_set ht' with ht' | rfl
        · exact hinv₁.ctors t' ht' c hc
        · exact hcs' c hc

open Expr in
/-- **THE PINS CARRY NO NODE OF AN UNSTORED SLOT**: at the elimination's
end every pin is free of `.proj T i`, given the block's own constructor
types and the first former's type free of it and `T` unstored. -/
theorem elimNested_pins_noProjAt {env : Env} {nP : Nat} {lps : List Name}
    {types : List AuxType} {st : ElimState} {T : Name} {i : Nat}
    (hwf : EnvWF env) (hT : env.find? T = none) (hslot : env.findProj? T i = none)
    (h : elimNested env nP lps types = .ok st)
    (hty : ∀ t ∈ types, ∀ c ∈ t.ctors, Expr.NoProjAt T i c.2.1)
    (ht₀ : ∀ t₀ ∈ types.head?, Expr.NoProjAt T i t₀.type) :
    ∀ q ∈ st.pins, Expr.NoProjAt T i q.pin := by
  -- `hslot` is the model lane's companion hypothesis (the slot is
  -- unanswered at `env`); what this proof needs is the stronger fact
  -- that `T` is UNSTORED there, so the binder is only carried
  have _hslot := hslot
  have hcc : ContainersNoProj T i env := containersNoProj_of_wf hwf hT
  unfold elimNested at h
  split at h
  · next t₀ hh =>
    split at h
    · next params body hop =>
      split at h
      · next pbs body₀ hstrip =>
        have hcl : NoProjAt T i t₀.type := ht₀ t₀ (by rw [hh]; exact rfl)
        have hpar : ∀ p ∈ params, NoProjAt T i p :=
          (noProjAt_openPisAtFvars nP hop hcl).1
        have hpbs : ∀ b ∈ pbs, NoProjAt T i b.1 := NoProjAt.stripPis_doms nP hstrip hcl
        have hinv₀ : ProjInv T i ⟨types, [], 1⟩ :=
          ⟨(fun q hq => nomatch hq), fun t ht c hc => hty t ht c hc⟩
        exact (elimLoop_noProj hcc hpbs hpar h hinv₀).pins
      · contradiction
    · contradiction
  · contradiction

/-! ## The scratch install's new constants

The auxiliary (scratch) install of the elimination's block is
`checkMutualCore`.  Its five stages cons constants: the formers
(`.indInfo`), the constructors (`.ctorInfo`), the recursors
(`.recInfo`) and — only at the structure-like members — the projection
tables (`.projInfo`).  `checkMutualCore_new` reads that off the stage
chain once, as the two facts the model lane needs of every constant
the install adds (`ScratchNew`): a projection table is a MEMBER's,
whose own name the pre-block environment does not carry (the formers'
front door found it free), and every new name is either one of the
block's recursor names or unreserved (the front doors again, and a
table's name is `.num`-shaped).
-/

variable {mode : CheckMode}

/-- An extension of `env` by constants that all satisfy `P`. -/
private def NewExt (P : ConstantInfo → Prop) (env envOut : Env) : Prop :=
  ∃ new : List ConstantInfo, envOut.consts = new ++ env.consts ∧ ∀ c ∈ new, P c

/-- A lookup the extension does not answer from its own constants is
the base's. -/
private theorem find?_of_new_none {new : List ConstantInfo} {env envOut : Env} {n : Name}
    (hc : envOut.consts = new ++ env.consts)
    (hn : List.find? (fun c => c.name == n) new = none) :
    envOut.find? n = env.find? n := by
  rw [Env.find?, hc, List.find?_append, hn]
  rfl

private theorem NewExt.rfl' (P : ConstantInfo → Prop) (env : Env) : NewExt P env env :=
  ⟨[], by simp, by simp⟩

private theorem NewExt.cons {P : ConstantInfo → Prop} {env : Env} {c : ConstantInfo}
    (h : P c) : NewExt P env ⟨c :: env.consts⟩ :=
  ⟨[c], rfl, by
    intro c' hc'
    obtain rfl := List.mem_singleton.mp hc'
    exact h⟩

private theorem NewExt.trans {P : ConstantInfo → Prop} {env env₁ env₂ : Env}
    (h₁ : NewExt P env env₁) (h₂ : NewExt P env₁ env₂) : NewExt P env env₂ := by
  obtain ⟨new₁, hc₁, hn₁⟩ := h₁
  obtain ⟨new₂, hc₂, hn₂⟩ := h₂
  refine ⟨new₂ ++ new₁, by rw [hc₂, hc₁, List.append_assoc], ?_⟩
  intro c hc
  rcases List.mem_append.mp hc with hc' | hc'
  · exact hn₂ c hc'
  · exact hn₁ c hc'

/-- Stage 1: the formers are `.indInfo`. -/
private theorem consMutualFormers_newExt {P : ConstantInfo → Prop} :
    ∀ {fms : List MutualFormerA} {env : Env}, (∀ f ∈ fms, P (.indInfo f.cvTa {})) →
      NewExt P env (consMutualFormers fms env)
  | [], env, _ => NewExt.rfl' _ _
  | f :: fs, env, hP => by
    show NewExt P env (consMutualFormers fs ⟨.indInfo f.cvTa {} :: env.consts⟩)
    exact (NewExt.cons (hP f List.mem_cons_self)).trans
      (consMutualFormers_newExt (fun g hg => hP g (List.mem_cons_of_mem _ hg)))

/-- Stage 3: the constructors are `.ctorInfo`. -/
private theorem consMutualCtors_newExt {P : ConstantInfo → Prop} {nP : Nat} :
    ∀ {ctorsA : List (ConstantVal × Nat)} {env : Env},
      (∀ cA ∈ ctorsA, P (.ctorInfo cA.1 nP cA.2)) →
      NewExt P env (consMutualCtors nP ctorsA env)
  | [], env, _ => NewExt.rfl' _ _
  | cA :: cs, env, hP => by
    show NewExt P env (consMutualCtors nP cs ⟨.ctorInfo cA.1 nP cA.2 :: env.consts⟩)
    exact (NewExt.cons (hP cA List.mem_cons_self)).trans
      (consMutualCtors_newExt (fun c' hc' => hP c' (List.mem_cons_of_mem _ hc')))

/-- Stage 4: the recursors are `.recInfo`. -/
private theorem storeMutualRecs_newExt {P : ConstantInfo → Prop} {env₂ : Env} {b : MutualBlock}
    {fms : List MutualFormerA} {rulesOf : List (List (MutualCtor × Expr))} :
    ∀ {l : List (ConstantVal × Nat)} {env : Env},
      (∀ q ∈ l, ∀ (mI rP : Nat) (rules : List RecRule), P (.recInfo q.1 mI rP rules)) →
      NewExt P env (storeMutualRecs env₂ b fms rulesOf l env)
  | [], env, _ => NewExt.rfl' _ _
  | (cvRa, mIdx) :: rest, env, hP => by
    show NewExt P env (storeMutualRecs env₂ b fms rulesOf rest
      ⟨.recInfo cvRa (b.rulePrefix + (fms.getD mIdx default).nIdx) b.rulePrefix
        (mutualRules env₂.find? cvRa.name b.nP (b.rulePrefix + (fms.getD mIdx default).nIdx)
          b.rulePrefix cvRa.type (rulesOf.getD mIdx [])) :: env.consts⟩)
    exact (NewExt.cons (hP (cvRa, mIdx) List.mem_cons_self _ _ _)).trans
      (storeMutualRecs_newExt (fun q hq => hP q (List.mem_cons_of_mem _ hq)))

/-- Stage 5: a table is a member's. -/
private theorem mutualTables_newExt {P : ConstantInfo → Prop} {b : MutualBlock}
    {ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)} :
    ∀ {l : List (MutualFormerA × Nat)} {env env' : Env},
      mutualTables (m := CheckM) b ctorsA sortss l env = .ok env' →
      (∀ q ∈ l, ∀ tbl : ProjTable, tbl.structName = q.1.cvTa.name → P (.projInfo tbl)) →
      NewExt P env env'
  | [], env, env', h, _ => by
    obtain rfl := mutualTables_nil_inv h
    exact NewExt.rfl' _ _
  | (f, mIdx) :: rest, env, env', h, hP => by
    obtain ⟨envI, hI, hrest⟩ := mutualTables_inv h
    refine NewExt.trans ?_ (mutualTables_newExt hrest
      (fun q hq => hP q (List.mem_cons_of_mem _ hq)))
    rcases mutualMemberTable_inv hI with rfl | ⟨J, c, -, -, htbl⟩
    · exact NewExt.rfl' _ _
    · obtain ⟨bodies, -, -, -, -, rfl⟩ := checkStructProjTable_inv htbl
      exact NewExt.cons (hP (f, mIdx) List.mem_cons_self _ rfl)

/-- **What the scratch install's new constants are**: a projection
table is a member's, whose structure name the pre-block environment
does not carry; and every new name is one of the block's recursor
names or unreserved. -/
private def ScratchNew (env : Env) (b : MutualBlock) (c : ConstantInfo) : Prop :=
  (∀ tbl : ProjTable, c = .projInfo tbl → env.find? tbl.structName = none) ∧
  ((∃ t, t < b.k ∧ c.name = b.recName t) ∨ reservedBasisNames.contains c.name = false)

/-- **The scratch install's stage chain**, read once: `envAux` is `env`
grown by constants that all satisfy `ScratchNew`. -/
private theorem checkMutualCore_new {env envAux : Env} {b : MutualBlock} {F : Nat}
    {streamRecs : Option (List (ConstantVal × List RecRule))} {auxRoute : Bool}
    (h : checkMutualCore (m := CheckM) (fueledOps mode F) env b streamRecs auxRoute = .ok envAux) :
    NewExt (ScratchNew env b) env envAux := by
  obtain ⟨-, -, -, -, env₁, fms, _f₀, _tq₀, ctorsA, _sortss, _kinds, _formers4, _ctors4,
    cvRas, rulesOf, hformers, -, -, -, -, hctors, -, -, -, hrectys, -, htbl⟩ :=
    checkMutualCore_inv h
  obtain ⟨hchecks, rfl⟩ := mutualFormers_inv hformers
  -- the members: found free and unreserved by the formers' front door
  have hform : ∀ f ∈ fms, env.find? f.cvTa.name = none ∧
      reservedBasisNames.contains f.cvTa.name = false := by
    intro f hf
    obtain ⟨cv, hff⟩ := mutualFormerChecks_front_mem hchecks f hf
    rw [hff.name]
    exact ⟨hff.fresh, hff.nres⟩
  -- the constructors: unreserved by their own front door, at either grade
  have hctorNres : ∀ cA ∈ ctorsA, reservedBasisNames.contains cA.1.name = false := by
    intro cA hcA
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hcA
    obtain ⟨hlen, -, hall⟩ := checkMutualCtors_inv hctors
    have hj' : j < b.ctors.length := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      omega
    obtain ⟨-, sorts, -, hrun⟩ := hall j b.ctors[j] cA (List.getElem?_eq_getElem hj') hj
    obtain ⟨⟨ty', hff⟩, -, -⟩ := checkMutualCtor_front hrun
    rw [hff.name]
    exact hff.nres
  -- the recursors: the generated name at the member's index
  have hrecName : ∀ q ∈ cvRas.zipIdx, ∃ t, t < b.k ∧ (Prod.fst q).name = b.recName t := by
    intro q hq
    obtain ⟨cvRa, mIdx⟩ := q
    have hget : cvRas[mIdx]? = some cvRa := List.mk_mem_zipIdx_iff_getElem?.mp hq
    obtain ⟨hlen, hall⟩ := checkMutualRecTys_inv hrectys
    have hlt : mIdx < b.k := by
      have := (List.getElem?_eq_some_iff.mp hget).1
      omega
    obtain ⟨cvRa', hget', hrun⟩ := hall mIdx hlt
    obtain rfl : cvRa = cvRa' := Option.some.inj (hget.symm.trans hget')
    obtain ⟨_recTy, _sty, _u, -, -, -, -, -, -, -, -, hshape⟩ := checkMutualRecTy_shape hrun
    exact ⟨mIdx, hlt, by rw [hshape]⟩
  have e1 : NewExt (ScratchNew env b) env (consMutualFormers fms env) :=
    consMutualFormers_newExt (fun f hf =>
      ⟨fun _ heq => ConstantInfo.noConfusion heq, Or.inr (hform f hf).2⟩)
  have e2 : NewExt (ScratchNew env b) (consMutualFormers fms env)
      (consMutualCtors b.nP ctorsA (consMutualFormers fms env)) :=
    consMutualCtors_newExt (fun cA hcA =>
      ⟨fun _ heq => ConstantInfo.noConfusion heq, Or.inr (hctorNres cA hcA)⟩)
  have e3 : NewExt (ScratchNew env b) (consMutualCtors b.nP ctorsA (consMutualFormers fms env))
      (storeMutualRecs (consMutualCtors b.nP ctorsA (consMutualFormers fms env)) b fms rulesOf
        cvRas.zipIdx (consMutualCtors b.nP ctorsA (consMutualFormers fms env))) :=
    storeMutualRecs_newExt (fun q hq _ _ _ =>
      ⟨fun _ heq => ConstantInfo.noConfusion heq, Or.inl (hrecName q hq)⟩)
  have e4 : NewExt (ScratchNew env b)
      (storeMutualRecs (consMutualCtors b.nP ctorsA (consMutualFormers fms env)) b fms rulesOf
        cvRas.zipIdx (consMutualCtors b.nP ctorsA (consMutualFormers fms env))) envAux :=
    mutualTables_newExt htbl (by
      intro q hq tbl hst
      obtain ⟨f, m⟩ := q
      have hmem : f ∈ fms := List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp hq)
      refine ⟨fun tbl' heq => ?_, Or.inr (reservedBasisNames_not_num _ _)⟩
      obtain rfl := ConstantInfo.projInfo.inj heq
      rw [hst]
      exact (hform f hmem).1)
  exact (e1.trans e2).trans (e3.trans e4)

/-- **A projection slot the scratch install answers is a block
member's, fresh at the environment it started from**: only the table
stage conses a `.projInfo`, and it does so for a member whose name the
formers' front door found free. -/
theorem checkMutualCore_findProj_fresh {env envAux : Env} {b : MutualBlock} {F : Nat}
    {streamRecs : Option (List (ConstantVal × List RecRule))} {auxRoute : Bool}
    (h : checkMutualCore (m := CheckM) (fueledOps mode F) env b streamRecs auxRoute = .ok envAux)
    {sn : Name} {i : Nat}
    (h₁ : env.findProj? sn i = none) (h₂ : (envAux.findProj? sn i).isSome = true) :
    env.find? sn = none := by
  obtain ⟨new, hc, hnew⟩ := checkMutualCore_new h
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp h₂
  obtain ⟨tbl, hft, hi, -⟩ := Env.findProj?_some he
  cases hfind : List.find? (fun c => c.name == projTableName sn) new with
  | none =>
    rw [find?_of_new_none hc hfind] at hft
    rw [Env.findProj?_of_table hft hi] at h₁
    exact nomatch h₁
  | some c =>
    have hcf : envAux.find? (projTableName sn) = some c := by
      rw [Env.find?, hc, List.find?_append, hfind]
      rfl
    obtain rfl : c = .projInfo tbl := Option.some.inj (hcf.symm.trans hft)
    have hb := List.find?_some hfind
    simp only [beq_iff_eq] at hb
    have hname : projTableName tbl.structName = projTableName sn := hb
    have hst : env.find? tbl.structName = none :=
      (hnew _ (List.mem_of_find?_eq_some hfind)).1 tbl rfl
    rwa [projTableName_inj hname] at hst

/-- **The scratch install introduces no reserved basis name**: the
formers' and constructors' front doors refuse one, a table's name is
`.num`-shaped, and the recursors' names are the block's own — which
the caller's `hrecNres` says are unreserved. -/
theorem checkMutualCore_reserved_fresh {env envAux : Env} {b : MutualBlock} {F : Nat}
    {streamRecs : Option (List (ConstantVal × List RecRule))} {auxRoute : Bool}
    (h : checkMutualCore (m := CheckM) (fueledOps mode F) env b streamRecs auxRoute = .ok envAux)
    (hrecNres : ∀ t, t < b.k → reservedBasisNames.contains (b.recName t) = false)
    {n : Name} (hres : reservedBasisNames.contains n = true) (hfresh : env.find? n = none) :
    envAux.find? n = none := by
  obtain ⟨new, hc, hnew⟩ := checkMutualCore_new h
  cases hfind : List.find? (fun c => c.name == n) new with
  | none =>
    rw [find?_of_new_none hc hfind]
    exact hfresh
  | some c =>
    exfalso
    have hb := List.find?_some hfind
    simp only [beq_iff_eq] at hb
    rcases (hnew c (List.mem_of_find?_eq_some hfind)).2 with ⟨t, ht, hname⟩ | hnres
    · rw [hb] at hname
      rw [hname, hrecNres t ht] at hres
      exact Bool.noConfusion hres
    · rw [hb] at hnres
      rw [hnres] at hres
      exact Bool.noConfusion hres

end ConLeche
