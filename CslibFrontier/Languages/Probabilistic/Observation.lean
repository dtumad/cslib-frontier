/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Simulation

/-!
# Passive observation of stateful oracle calls

`withObserver` runs an oracle once, then updates an observation using the request, reply and
both private states. The observation cannot affect the oracle or perform another effect.
This covers transcripts, response-sensitive statistics and accumulated execution costs.

## Main results

* `run_interpret_withObserver`: erasing observation preserves the joint result and private state.
* `run_interpret_withObserver_map`: compatible state and observation representations commute
  with adaptive execution.
* `run_interpret_withObserver_prod`: two observers can be fused into one product observer.

The state-extension and projection pattern follows the stateful handler combinators in PolyFun.
The statements use the existing `OracleComp` interpreter and hold for any lawful base monad.
-/

public section

namespace Cslib.OracleComp

universe u v w

variable {Query : Type u} {Response : Query → Type v} {State α Obs : Type v}
variable {m : Type v → Type w} [Monad m]

/-- Run the oracle once, then update a passive observation from the call's two states and reply.
The observation update is pure and cannot change the reply or the private state. -/
def withObserver (oracle : (q : Query) → StateT State m (Response q))
    (update : (q : Query) → State → Response q → State → Obs → Obs)
    (q : Query) : StateT (State × Obs) m (Response q) :=
  fun (s, observation) =>
    (fun (answer, s') => (answer, s', update q s answer s' observation)) <$> oracle q s

/-- The observation update sees the same reply and final state that the oracle returned. -/
@[simp] theorem withObserver_apply (oracle : (q : Query) → StateT State m (Response q))
    (update : (q : Query) → State → Response q → State → Obs → Obs)
    (q : Query) (s : State) (observation : Obs) :
    withObserver oracle update q (s, observation) =
      (fun (answer, s') => (answer, s', update q s answer s' observation)) <$> oracle q s := by
  rfl

variable [LawfulMonad m]

/-- Forgetting observation preserves the result and the complete final private state. -/
theorem run_interpret_withObserver (oracle : (q : Query) → StateT State m (Response q))
    (update : (q : Query) → State → Response q → State → Obs → Obs)
    (program : OracleComp Response α) (s : State) (observation : Obs) :
    (fun (result, state, _) => (result, state)) <$>
        (interpret (withObserver oracle update) program).run (s, observation) =
      (interpret oracle program).run s := by
  apply run_interpret_map_state (withObserver oracle update) oracle Prod.fst
  rintro q ⟨s, observation⟩
  simp [Functor.map_map]

/-- Transport the private state and observation together when both the oracle transition and
the observation update respect their representations. -/
theorem run_interpret_withObserver_map {State' Obs' : Type v}
    (oracle : (q : Query) → StateT State m (Response q))
    (oracle' : (q : Query) → StateT State' m (Response q))
    (update : (q : Query) → State → Response q → State → Obs → Obs)
    (update' : (q : Query) → State' → Response q → State' → Obs' → Obs')
    (represent : State → State') (observe : Obs → Obs')
    (step : ∀ q s, (fun (a, s') => (a, represent s')) <$> oracle q s =
      oracle' q (represent s))
    (compatible : ∀ q s a s' o, observe (update q s a s' o) =
      update' q (represent s) a (represent s') (observe o))
    (program : OracleComp Response α) (s : State) (o : Obs) :
    (fun (a, s', o') => (a, represent s', observe o')) <$>
        (interpret (withObserver oracle update) program).run (s, o) =
      (interpret (withObserver oracle' update') program).run (represent s, observe o) := by
  apply run_interpret_map_state _ _ (Prod.map represent observe)
  rintro q ⟨s, o⟩
  simp only [Prod.map_apply, withObserver_apply]
  rw [← step q s]
  simp [Functor.map_map, compatible]

/-- Two observers of the same calls can be collected in one pass. Nested observation has the
same joint law after reassociating its state; it never repeats the underlying oracle effect. -/
theorem run_interpret_withObserver_prod {Obs' : Type v}
    (oracle : (q : Query) → StateT State m (Response q))
    (first : (q : Query) → State → Response q → State → Obs → Obs)
    (second : (q : Query) → State → Response q → State → Obs' → Obs')
    (program : OracleComp Response α) (s : State) (o : Obs) (o' : Obs') :
    (fun (a, (s', x), y) => (a, s', x, y)) <$>
        (interpret (withObserver (withObserver oracle first)
          (fun q before a after y => second q before.1 a after.1 y)) program).run ((s, o), o') =
      (interpret (withObserver oracle (fun q before a after (x, y) =>
        (first q before a after x, second q before a after y))) program).run (s, o, o') := by
  apply run_interpret_map_state (m := m) _ _
    (fun (state : (State × Obs) × Obs') => (state.1.1, state.1.2, state.2))
  rintro q ⟨⟨s', x⟩, y⟩
  simp [Functor.map_map]

end Cslib.OracleComp
