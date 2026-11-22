/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Devon Tuma
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Oracle.Relabel
public import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.RunWith

/-!
# Relabeling external requests of programs with private randomness

Relabeling preserves private sampling. The execution law tracks the result and final state of the
external handler.
-/

public section

universe u u' w

namespace Cslib

namespace ProbOracleComp

variable {ι : Type u} {κ : Type u'} {spec : ι → Type} {target : κ → Type}

/-- Relabel external requests, forwarding private samples to the same sampling interface. -/
@[expose] def relabel (send : ι → κ) (decode : (q : ι) → target (send q) → spec q)
    {α : Type w} (program : ProbOracleComp spec α) : ProbOracleComp target α :=
  simulate (fun q => decode q <$> query (send q)) program

/-- On the combined interface, private samples keep their request and reply unchanged.
The same polynomial lens translates all external requests. -/
theorem relabel_eq_oracleComp_relabel (send : ι → κ) (decode : (q : ι) → target (send q) → spec q)
    {α : Type w} (program : ProbOracleComp spec α) :
    relabel send decode program =
      OracleComp.relabel (spec := probOracleSpec spec) (target := probOracleSpec target)
        (Sum.map id send) (fun q => match q with
          | .inl _ => id
          | .inr k => decode k) program := by
  rw [OracleComp.relabel_eq_substitute]
  apply congrArg (fun h => OracleComp.substitute h program)
  funext q
  cases q <;> rfl

/-- The result and final oracle state of a relabeling have the law of running the original
program with the request forwarded and only the returned answer decoded. -/
theorem runWith_relabel (send : ι → κ) (decode : (q : ι) → target (send q) → spec q)
    {State : Type} (oracle : (q : κ) → State → PMF (target q × State))
    {α : Type w} (program : ProbOracleComp spec α) (s : State) :
    runWith oracle (relabel send decode program) s =
      runWith (fun q st => (oracle (send q) st).map (Prod.map (decode q) id)) program s := by
  rw [relabel, runWith_simulate]
  apply congrArg (fun handler => runWith handler program s)
  funext q st
  rw [runWith_map, runWith_query]

end ProbOracleComp

end Cslib
