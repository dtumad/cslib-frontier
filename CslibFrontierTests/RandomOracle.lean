/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Languages.Probabilistic.RandomOracle.Invariant

/-! Adaptive lazy sampling, complete private state, and concrete query/cache bounds. -/

namespace CslibFrontierTests.RandomOracle

open Cslib Cslib.Probability

private def counted (_ : Bool) : StateM ℕ ℕ := do
  let value ← get
  set (value + 1)
  return value

-- A repeated key increments the underlying counter once and keeps one cache entry.
example : (((do
    let first ← memoize counted false
    let second ← memoize counted false
    pure (first, second)) : StateT (List (Bool × ℕ)) (StateM ℕ) (ℕ × ℕ)).run []).run 7 =
      (((7, 7), [(false, 7)]), 8) := rfl

-- The first duplicate entry wins; neither its value nor its tail is rewritten.
example : (memoize counted false [(false, 4), (false, 9)]).run 7 =
    ((4, [(false, 4), (false, 9)]), 7) := rfl

private def adaptive : OracleComp (fun _ : Bool => Bool) (Bool × Bool × Bool) := do
  let first ← OracleComp.query false
  let second ← OracleComp.query first
  let third ← OracleComp.query false
  return (first, second, third)

-- Every oracle, including a stateful one, sees exactly this uniform three-call upper bound.
private theorem adaptive_queryBounds : adaptive.IsQueryBounded 3 :=
  ((OracleComp.IsCostBounded.query false).bind fun first =>
    (OracleComp.IsCostBounded.query first).bind fun second =>
      (OracleComp.IsCostBounded.query false).bind fun third =>
        OracleComp.IsCostBounded.pure (first, second, third) 0).mono (by norm_num)

-- Eagerly sample a table or lazily cache it: the adaptive client's output has the same law.
example :
    (do
      let table ← PMF.uniformOfFintype (Bool → Bool)
      OracleComp.interpret (fun q => PMF.pure (table q)) adaptive) =
      ((OracleComp.interpret
        (Cslib.RandomOracle.answer (fun _ => PMF.uniformOfFintype Bool)) adaptive).run
          (fun _ => none)).map Prod.fst :=
  Cslib.RandomOracle.uniform_interpret_eq_lazy adaptive

-- The cache bound is instantiated by a concrete adaptive program, not left as an assumption.
example (cache next : List (Bool × Bool)) (result : Bool × Bool × Bool)
    (h : (result, next) ∈ ((OracleComp.interpret
      (memoize (fun _ => PMF.uniformOfFintype Bool)) adaptive).run cache).support) :
    next.length ≤ cache.length + 3 :=
  (Cslib.RandomOracle.memoize_cache_bounds _ adaptive (fun _ => 1) 3 1
    adaptive_queryBounds (OracleComp.QueriesSatisfy.of_forall (fun _ => le_rfl) _) cache next
    result h).1

-- The first and third replies agree, including after an answer-dependent intermediate query.
example (table : Bool → Bool) :
    OracleComp.interpret (fun q => PMF.pure (table q)) adaptive =
      PMF.pure (table false, table (table false), table false) := by
  simp [adaptive]

-- Missing entries are independent; an initially assigned answer remains fixed in all completions.
example (table : Bool → Bool)
    (h : table ∈ (Cslib.RandomOracle.complete (fun _ => PMF.uniformOfFintype Bool)
      (fun q => if q = false then some true else none)).support) : table false = true :=
  Cslib.RandomOracle.complete_agrees _ _ _ h false true (by decide)

-- Closed uniform samplers implement the same eager-table experiment through a list cache.
example :
    ProbComp.eval (Prod.fst <$>
      (OracleComp.interpret (memoize (fun _ : Bool => ProbComp.uniform Bool)) adaptive).run []) =
      (do
        let table ← PMF.pi (fun _ : Bool => PMF.uniformOfFintype Bool)
        OracleComp.interpret (fun q => PMF.pure (table q)) adaptive) := by
  simpa only [ProbComp.eval_uniform] using
    Cslib.RandomOracle.eval_run_interpret_memoize_eq_eager
      (fun _ : Bool => ProbComp.uniform Bool) adaptive

-- A repeated key uses the first list entry. The full cache and the sampler's counter survive
-- replay, including the shadowed duplicate and the unused key.
example : ((OracleComp.interpret (memoize counted) (do
    let x ← OracleComp.query (spec := fun _ : Bool => ℕ) false
    let y ← OracleComp.query false
    return x + y)).run [(false, 4), (false, 9), (true, 3)]).run 7 =
      ((8, [(false, 4), (false, 9), (true, 3)]), 7) := by
  apply congrArg (fun action : StateM ℕ (ℕ × List (Bool × ℕ)) => action.run 7)
    (PFunctor.FreeM.run_liftM_eq_pure_of_liftM_eq_some (P := ⟨Bool, fun _ => ℕ⟩)
      (fun q : Bool => if q then none else some 4) (memoize counted)
      [(false, 4), (false, 9), (true, 3)] ?_ (by rfl))
  intro q v hv
  cases q with
  | false => cases Option.some.inj hv; rfl
  | true => simp at hv

-- A cached reply outside the sampler's support survives while a fresh query draws from it.
private def initial (q : Bool) : Option Bool := if q then none else some true

example :
    OracleComp.runWith (RandomOracle.answer fun _ : Bool => PMF.pure false)
      (do
        let hit ← OracleComp.query (spec := fun _ : Bool => Bool) false
        let draw ← OracleComp.query true
        return (hit, draw)) initial =
      PMF.pure ((true, false), Function.update initial true (some false)) := by
  simp [RandomOracle.answer, initial]

-- Sampling cannot repair a missing adaptive answer in a partial replay.
example : OracleComp.interpret (fun q : Bool => if q then none else some true) adaptive =
    none := rfl

end CslibFrontierTests.RandomOracle
