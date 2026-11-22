/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Languages.Probabilistic.Forking
import CslibFrontier.Probability.Forking
import CslibFrontier.Probability.PMF

/-!
# Tests for the forking lemma

An algorithm that always names its only answer is accepted with probability `1`, so forking it
succeeds with probability at least `1 - 1 / 2`; it succeeds exactly when two independent bits
differ, so the bound is attained. The oracle program that asks one query and names it satisfies
the hypotheses of the oracle forking lemma, which gives a positive forking probability; a
successful fork gives two runs that ask the same query. A program that names a position without
asking any query never forks successfully.
-/

namespace CslibFrontierTests.Crypto.Forking

open Cslib Cslib.Probability

/-- Always name the only answer. -/
def always (_ : Unit) (_ : Fin 1 → Bool) : Option (Fin 1) × Unit := (some 0, ())

example : (Forking.accept (PMF.pure ()) always true) = 1 := by
  simp [Forking.accept, always]

/-- The general forking lemma for `always`: `1 - 1 / 2 ≤ frk`. -/
example : (1 : ℝ) / 2 ≤ ((Forking.fork (PMF.pure ()) always).map Option.isSome true).toReal := by
  have h := Forking.sq_div_sub_le_fork (PMF.pure ()) always
  have hacc : (Forking.accept (PMF.pure ()) always true).toReal = 1 := by
    simp [Forking.accept, always]
  rw [hacc] at h
  simp only [Fintype.card_bool, Nat.cast_ofNat, Nat.cast_one, one_pow, div_one] at h
  linarith

/-! ### Oracle programs -/

/-- Ask one query and name it. -/
def askOnce (_ : Unit) : OracleComp (fun _ : Unit => Bool) (Option ℕ × Bool) := do
  let a ← OracleComp.query (spec := fun _ : Unit => Bool) ()
  return (some 0, a)

/-- `askOnce` asks one query. -/
theorem askOnce_queries (s : Unit) : (askOnce s).IsQueryBounded 1 :=
  (OracleComp.IsCostBounded.query ()).bind fun a => OracleComp.IsCostBounded.pure (some 0, a) 0

/-- Forking `askOnce`, which always names its query, succeeds with probability at least
`1 / 4`. -/
example : (1 : ℝ) / 4 ≤ ((Forking.fork (PMF.pure ())
    (OracleComp.forkingAlgorithm false 1 askOnce)).map Option.isSome true).toReal := by
  have h := OracleComp.le_add_sqrt_fork (PMF.pure ()) askOnce false askOnce_queries
  have hacc : ((do
      let s ← PMF.pure ()
      let run ← (OracleComp.interpret OracleComp.countingUniform (askOnce s)).run 0
      return (OracleComp.validIndex 1 run.2 run.1.1).isSome : PMF Bool) true).toReal = 1 := by
    rw [Probability.PMF.monad_bind_eq_bind, PMF.pure_bind, Probability.PMF.monad_bind_eq_bind,
      OracleComp.run_interpret_countingUniform_eq false (askOnce ()) (askOnce_queries ()),
      PMF.bind_map]
    simp [Function.comp_def, askOnce, OracleComp.validIndex]
  rw [hacc] at h
  simp only [Fintype.card_bool, Nat.cast_ofNat, Nat.cast_one, one_mul] at h
  have hsqrt : (1 : ℝ) / 2 ≤ √(((Forking.fork (PMF.pure ())
      (OracleComp.forkingAlgorithm false 1 askOnce)).map Option.isSome true).toReal) := by
    linarith
  nlinarith [Real.sq_sqrt (ENNReal.toReal_nonneg (a := ((Forking.fork (PMF.pure ())
    (OracleComp.forkingAlgorithm false 1 askOnce)).map Option.isSome true))), Real.sqrt_nonneg
    (((Forking.fork (PMF.pure ()) (OracleComp.forkingAlgorithm false 1 askOnce)).map
      Option.isSome true).toReal)]

/-- Both runs of a successful fork of `askOnce` ask the same query. -/
example {j : Fin 1} {out out' : (Option ℕ × Bool) × List Unit}
    (hfork : some (j, out, out') ∈
      (Forking.fork (PMF.pure ()) (OracleComp.forkingAlgorithm false 1 askOnce)).support) :
    out.2.take (j + 1) = out'.2.take (j + 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, htake, -⟩ := OracleComp.mem_support_fork hfork
  exact htake

/-- Name position `0` without asking any query. -/
def nameWithoutAsking (_ : Unit) : OracleComp (fun _ : Unit => Bool) (Option ℕ × Unit) :=
  pure (some 0, ())

/-- A program that names position `0` without asking any query does not validly name it, so its
fork never succeeds. -/
example : (Forking.fork (PMF.pure ()) (OracleComp.forkingAlgorithm false 1
    nameWithoutAsking)).map Option.isSome true = 0 := by
  simp [Forking.fork, Forking.onTapes,
    OracleComp.forkingAlgorithm, OracleComp.validIndex, nameWithoutAsking]

-- The first answer selects a request with a different reply type. Position two is
-- the second occurrence of the Boolean request. An early negative answer finishes the run.
private abbrev replies : Bool → Type
  | false => Bool
  | true => ℕ

private def adaptive : OracleComp replies ℕ :=
  .liftBind false fun (b : Bool) => if b then
    .liftBind true fun (n : ℕ) => .liftBind false fun (keep : Bool) => pure (if keep then n else 0)
  else pure 17

private def answer (enable : Bool) : (q : Bool) → Unit → replies q × Unit
  | false, _ => (enable, ())
  | true, _ => ((3 : ℕ), ())

example : (OracleComp.Checkpoint.seek (answer true) 2 adaptive ()).occurrence? =
    some (false, 1) := rfl

example : (OracleComp.Checkpoint.seek (answer false) 2 adaptive ()).occurrence? = none := rfl

-- An exhausted list uses the supplied default to decide the next request.
example : (OracleComp.Checkpoint.seek (fun _ (s : List Bool) => (s.headD false, s.tail))
    1 (OracleComp.query (spec := fun _ : Bool => Bool) true >>= fun b => OracleComp.query b)
    []).occurrence? = some (false, 0) := rfl

-- The oracle prefix constructor names also work when matching the shared spine.
example {p r : OracleComp replies ℕ} (path : OracleComp.Prefix p r) :
    (match p, r, path with
      | _, _, .root _ => true
      | _, _, .step _ _ => false) = path.events.isEmpty := by
  cases path <;> rfl

-- Rewind before the second call. Its answer selects different residuals and final traces.
private def forkAtSecond : OracleComp (fun _ : Bool => Bool) Bool := do
  let first ← OracleComp.query false
  let second ← OracleComp.query first
  if second then OracleComp.query false else pure false

example :
    let focus := OracleComp.Checkpoint.seek (fun _ (s : List Bool) => (s.headD false, s.tail))
      1 forkAtSecond [true]
    focus.resumeWithAnswers false [true, true] = (true, [false, true, false]) ∧
      focus.resumeWithAnswers false [false, true] = (false, [false, true]) := by
  exact ⟨rfl, rfl⟩

end CslibFrontierTests.Crypto.Forking
