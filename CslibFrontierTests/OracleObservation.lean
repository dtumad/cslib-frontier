module

import CslibFrontier.Languages.Probabilistic.Observation
import CslibFrontier.Languages.Probabilistic.Transcript
import CslibFrontier.Languages.Probabilistic.Oracle.Transcript

open Cslib Cslib.OracleComp

namespace OracleObservationTests

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

-- Fusing two observers still performs exactly three oracle effects.
example : ((interpret (withObserver (withObserver oracle record)
    (fun _ _ _ _ count => count + 1)) program).run ((4, [99]), 7)).run 0 =
      (((4, true, 5), (5, [99, 4, 4, 4, 4, 1, 5, 5, 5, 5]), 10), 3) := by
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

end OracleObservationTests
