/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Observation

/-!
# Observing oracle transcripts

`withTranscript` records each query and its answer while preserving the oracle's private state.
Entries are stored newest first. Forgetting the transcript recovers the original execution,
including its final private state.

Query budgets (`Cslib.OracleComp.IsCostBounded`) are properties of the program itself; every
logged run respects them.

This is semantic instrumentation, not a claim that recording arbitrary replies is efficient.
In particular, a machine's clock bounds its requests but need not bound the oracle's replies.

## Main definitions

* `Cslib.OracleComp.Transcript`, `.withTranscript`: typed query logging with private state.

## Main results

* `Cslib.OracleComp.run_interpret_withTranscript`: forgetting the log preserves full execution.
* `Cslib.OracleComp.run_interpret_withTranscript_append`: retain an existing transcript suffix.

## References

Adapted from Languages/Probabilistic/Transcript.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the single `OracleComp.interpret` interface.
-/

public section

namespace Cslib.OracleComp

universe u v

variable {Query : Type u} {Response : Query → Type u} {State α : Type u}
variable {m : Type u → Type v} [Monad m]

/-- Queries and their typed replies, stored in reverse chronological order. -/
abbrev Transcript (Response : Query → Type u) := List ((q : Query) × Response q)

/-- Observe calls without changing the underlying oracle's replies or private state. -/
def withTranscript (oracle : (q : Query) → StateT State m (Response q))
    (q : Query) : StateT (State × Transcript Response) m (Response q) :=
  withObserver oracle (fun q _ answer _ transcript => ⟨q, answer⟩ :: transcript) q

/-- Each call prepends its query and reply to the existing transcript. -/
@[simp] theorem withTranscript_apply (oracle : (q : Query) → StateT State m (Response q))
    (q : Query) (state : State × Transcript Response) :
    withTranscript oracle q state =
      (fun (answer, s') => (answer, s', ⟨q, answer⟩ :: state.2)) <$> oracle q state.1 :=
  withObserver_apply _ _ _ _

variable [LawfulMonad m]

/-- Forgetting the transcript preserves the result and the oracle's complete final state. -/
theorem run_interpret_withTranscript (oracle : (q : Query) → StateT State m (Response q))
    (program : OracleComp Response α) (s : State) (transcript : Transcript Response) :
    (fun (result, state, _) => (result, state)) <$>
        (interpret (withTranscript oracle) program).run (s, transcript) =
      (interpret oracle program).run s :=
  run_interpret_withObserver oracle _ program s transcript

/-- An existing transcript is an untouched suffix of the newly recorded interaction. -/
theorem run_interpret_withTranscript_append (oracle : (q : Query) → StateT State m (Response q))
    (program : OracleComp Response α) (s : State) (transcript : Transcript Response) :
    (interpret (withTranscript oracle) program).run (s, transcript) =
      (fun (result, state, fresh) => (result, state, fresh ++ transcript)) <$>
        (interpret (withTranscript oracle) program).run (s, []) := by
  symm
  apply run_interpret_map_state (withTranscript oracle) (withTranscript oracle)
    (fun state => (state.1, state.2 ++ transcript))
  rintro q ⟨state, fresh⟩
  simp [Functor.map_map]

/-- A representation of the private state transports the complete typed transcript unchanged. -/
theorem run_interpret_withTranscript_map_state {State' : Type u}
    (oracle : (q : Query) → StateT State m (Response q))
    (oracle' : (q : Query) → StateT State' m (Response q)) (represent : State → State')
    (step : ∀ q s, (fun (a, s') => (a, represent s')) <$> oracle q s =
      oracle' q (represent s))
    (program : OracleComp Response α) (s : State) (transcript : Transcript Response) :
    (fun (a, s', seen) => (a, represent s', seen)) <$>
        (interpret (withTranscript oracle) program).run (s, transcript) =
      (interpret (withTranscript oracle') program).run (represent s, transcript) :=
  run_interpret_withObserver_map oracle oracle' _ _ represent id step
    (by intros; rfl) program s transcript

end Cslib.OracleComp
