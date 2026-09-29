module

public import ConLeche.Verify.Inductives.RecCheckRun
import ConLeche.Verify.ExceptBind
import ConLeche.Verify.Inductives.PositivityInv

public section

/-!
# The calls' run facts at a nested stage

The run facts the calls' landing reads off the install, beside
`RecCheckRun.lean` and `PositivityInv.lean`:

* every checked major records the walk's normal forms its class matches
  (`TargetRecRun.nfsRun`: `targetMajorNfs … = .ok TargetMajor.nfs`);
* every call's typing ran (`targetCallsOk_each`).

The members' own entries are the root frame's, recorded like every
frame's (`CtorsRecRoot`, `checkBlockPositivity_deriv`).
-/

namespace ConLeche

variable {mode : CheckMode}

/-! ## A checked major's recorded normal forms -/

/-- **Every stored major records its class's normal forms**, at a run of
the target check (its table `R.tbl`). -/
theorem targetRecRun_nfs {fe : FEnv} {p : BlockShape} {nested : Bool}
    {block : List ConstantInfo} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
    {F : Nat} (R : TargetRecRun mode F fe p nested block cvTas ctorsAs out) :
    ∀ t ∈ out, targetMajorNfs (fueledOps mode F) fe.env p (cvTas.map (·.type)) t.2.1.pfvs
      t.2.1.lvls t.2.1.ds t.2.1.ctors R.tbl = .ok t.2.1.nfs := by
  intro t ht
  have h0 := targetRecRun_out_fst R
  have hm : (t.1, t.2.1) ∈ R.tys.map (fun t => (t.1, t.2.1)) := by
    rw [← h0]; exact List.mem_map_of_mem ht
  obtain ⟨t', ht', he⟩ := List.mem_map.mp hm
  have := R.nfsRun t' ht'
  have e2 : t'.2.1 = t.2.1 := (Prod.mk.inj he).2
  rw [← e2]; exact this

/-! ## Every call's typing ran -/

/-- **Every call's typing ran**, one by one. -/
theorem targetCallsOk_each {env : Env} {p : BlockShape} {formerTys : List Expr} {cn : Name}
    {fam : TargetFamily}
    {fvsPref fvsF : List Expr} {teles : List (List (Expr × BinderMeta))}
    {absM mvF : Expr → Expr} {base k dA F : Nat} {pw : PropWhen} {fwss : List (List Expr)} :
    ∀ {ihs : List TargetIh},
      targetCallsOk (fueledOps mode F) env p formerTys cn fam fvsPref fvsF teles absM mvF base k
        dA pw fwss ihs = .ok () →
      ∀ ih ∈ ihs, targetCallOk (fueledOps mode F) env p formerTys cn fam fvsPref fvsF teles
        absM mvF base k dA pw fwss ih = .ok ()
  | [], _, ih, hih => nomatch hih
  | ih0 :: ihs, h, ih, hih => by
    unfold targetCallsOk at h
    obtain ⟨u, hu, h⟩ := exceptBind_ok h
    rcases List.mem_cons.mp hih with rfl | hih
    · cases u; exact hu
    · exact targetCallsOk_each h ih hih

end ConLeche
