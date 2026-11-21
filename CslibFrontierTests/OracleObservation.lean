/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import CslibFrontier.Languages.Probabilistic.Observation
import CslibFrontier.Languages.Probabilistic.Transcript
import CslibFrontier.Languages.Probabilistic.Oracle.Transcript
import CslibFrontier.Languages.Probabilistic.RandomPermutation

open Cslib Cslib.OracleComp

namespace OracleObservationTests

-- The identity monad needs no probability structure, and observations can depend on both states.
example : (interpret
    (withObserver (m := Id) (fun (_ : Unit) (s : Nat) => (s, s + 1) :
      Unit → StateT Nat Id Nat)
      (fun _ before answer after seen => seen ++ [before, answer, after]))
    (query ())).run (4, [2]) = (4, 5, [2, 4, 4, 5]) := by
  rw [run_interpret_query, withObserver_apply]
  rfl

-- A failed base effect remains failed; observation cannot manufacture a reply.
example : (interpret
    (withObserver (fun (_ : Unit) (_ : Nat) => none : Unit → StateT Nat Option Nat)
      (fun _ _ answer _ seen => answer :: seen)) (query ())).run (4, [2]) = none := by
  rw [run_interpret_query, withObserver_apply]
  rfl

public inductive Request
  | read
  | advance

private abbrev Reply : Request → Type
  | .read => Nat
  | .advance => Bool

-- The base StateM counts effects independently of the oracle's private state.
private def oracle : (q : Request) → StateT Nat (StateM Nat) (Reply q)
  | .read => fun state calls => ((state, state), calls + 1)
  | .advance => fun state calls => ((true, state + 1), calls + 1)

private def program : OracleComp Reply (Nat × Bool × Nat) := do
  let before ← query Request.read
  let advanced ← query Request.advance
  let after ← query Request.read
  pure (before, advanced, after)

private def record : (q : Request) → Nat → Reply q → Nat → List Nat → List Nat
  | .read, before, answer, after, seen => seen ++ [before, answer, after]
  | .advance, before, answer, after, seen => seen ++ [before, if answer then 1 else 0, after]

-- A program without requests keeps its initial observation and performs no effects.
example : ((interpret (withObserver oracle record) (pure ())).run (4, [99])).run 7 =
    (((), 4, [99]), 7) := by
  rw [run_interpret_pure]
  rfl

-- Detect reversed observations, lost initial observations, wrong states or repeated effects.
example : ((interpret (withObserver oracle record) program).run (4, [99])).run 0 =
    (((4, true, 5), 5, [99, 4, 4, 4, 4, 1, 5, 5, 5, 5]), 3) := by
  simp only [program, run_interpret_bind, run_interpret_query, run_interpret_pure,
    withObserver_apply, StateT.run_bind, StateT.run_map, StateT.run_pure, oracle, record]
  rfl

-- Observation retains the entire private state, not just the visible result.
example : ((fun (result, state, _) => (result, state)) <$>
    (interpret (withObserver oracle record) program).run (4, [99])).run 0 =
      (((4, true, 5), 5), 3) := by
  rw [run_interpret_withObserver]
  simp only [program, run_interpret_bind, run_interpret_query, run_interpret_pure,
    StateT.run_bind, StateT.run_pure, oracle]
  rfl

-- Applying the product law collects both observations over exactly three oracle effects.
example :
    ((fun (a, (s, log), n) => (a, s, log, n)) <$>
      (interpret (withObserver (withObserver oracle record)
        (fun _ _ _ _ n => n + 1)) program).run ((4, [99]), 7)).run 0 =
      (((4, true, 5), 5, [99, 4, 4, 4, 4, 1, 5, 5, 5, 5], 10), 3) := by
  rw [run_interpret_withObserver_prod oracle record (fun _ _ _ _ (n : Nat) => n + 1)]
  simp only [program, run_interpret_bind, run_interpret_query, run_interpret_pure,
    withObserver_apply, StateT.run_bind, StateT.run_map, StateT.run_pure, oracle, record]
  rfl

-- Typed transcripts are newest first and preserve a nonempty suffix, even in a non-PMF monad.
example : ((interpret (withTranscript oracle) program).run
    (4, [⟨Request.read, 20⟩])).run 0 =
      (((4, true, 5), 5,
        [⟨Request.read, 5⟩, ⟨Request.advance, true⟩, ⟨Request.read, 4⟩,
          ⟨Request.read, 20⟩]), 3) := by
  simp only [program, run_interpret_bind, run_interpret_query, run_interpret_pure,
    withTranscript_apply, StateT.run_bind, StateT.run_map, StateT.run_pure, oracle]
  rfl

-- Private sampling does not add an external transcript entry.
example (sample : ProbComp Bool) :
    ProbOracleComp.runWith
      (withTranscript (fun (_ : Unit) (s : Nat) => PMF.pure (true, s)))
      (ProbOracleComp.sample sample) (4, []) =
        (sample.eval).map (fun result => (result, 4, [])) := by
  simp [ProbOracleComp.runWith_sample]

open Cslib.RandomPermutation

-- On a hit, even a previously set flag is retained and no entry is added.
example (bad : Bool) :
    forgetfulWithBad (.forward false) ([(false, false)], bad) =
      PMF.pure (false, [(false, false)], bad) :=
  forgetfulWithBad_of_cachedAnswer_eq_some (by decide) bad

-- On a miss, false collides with the previously occupied range while true is fresh.
example :
    forgetfulWithBad (.forward true) ([(false, false)], false) =
      (Probability.PMF.uniformOfFintype Bool).map
        (fun a => (a, [(true, a), (false, false)], !a)) := by
  rw [forgetfulWithBad_of_cachedAnswer_eq_none (q := .forward true)
    (cache := [(false, false)]) (by decide)]
  congr 1
  funext a
  cases a <;> decide

-- The inverse miss checks the occupied domain {false}; its range is the opposite singleton.
example :
    forgetfulWithBad (.inverse false) ([(false, true)], false) =
      (Probability.PMF.uniformOfFintype Bool).map
        (fun a => (a, [(a, false), (false, true)], !a)) := by
  rw [forgetfulWithBad_of_cachedAnswer_eq_none (q := .inverse false)
    (cache := [(false, true)]) (by decide)]
  congr 1
  funext a
  cases a <;> decide

end OracleObservationTests
