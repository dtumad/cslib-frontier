/-
Copyright (c) 2026 Quang Dao, Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Devon Tuma
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Basic

/-!
# Stopping an oracle program before a selected query

A `Prefix` witnesses the replies leading from a program to a particular residual program.
Running at most `n` steps produces a `Checkpoint`. If the program still has a query, the
checkpoint retains that request and its continuation, whose argument is the reply type of
that request. Selecting replies by position allows repeated calls to receive different replies.

This specializes the typed cursor for polynomial free programs in PolyFun
(`PFunctor.Free.Cursor` and `PFunctor.Free.Cursor.Occurrence`) to indexed replay.
A checkpoint records the current residual itself, allowing two forks to share its continuation.
-/

public section

namespace Cslib.OracleComp

universe u v w z

variable {Q : Type u} {spec : OracleSpec.{u, v} Q} {α : Type w}

/-- A typed path from the source program to a residual. Each step retains its actual reply. -/
inductive Prefix : OracleComp spec α → OracleComp spec α → Type (max u v w) where
  | root (p : OracleComp spec α) : Prefix p p
  | step {q : Q} {k : spec q → OracleComp spec α} {r : OracleComp spec α} (a : spec q)
      (rest : Prefix (k a) r) : Prefix (PFunctor.FreeM.liftBind q k) r

namespace Prefix

/-- Chronological requests and dependent replies along the prefix. -/
@[expose] def events {p r : OracleComp spec α} : Prefix p r → List ((q : Q) × spec q)
  | .root _ => []
  | .step (q := q) a rest => ⟨q, a⟩ :: rest.events

/-- Resume at the residual and plug the second prefix back into the original program. -/
@[expose] def append {p r t : OracleComp spec α} : Prefix p r → Prefix r t → Prefix p t
  | .root _, tail => tail
  | .step a rest, tail => .step a (rest.append tail)

/-- Plugging a prefix into its context reconstructs the concatenation of the two histories. -/
@[simp] theorem events_append {p r t : OracleComp spec α} (h : Prefix p r) (s : Prefix r t) :
    (h.append s).events = h.events ++ s.events := by
  induction h with
  | root => rfl
  | step a rest ih => simp only [append, events, List.cons_append, ih]

end Prefix

/-- A completed run or the exact typed continuation at the next unanswered query. -/
inductive Checkpoint (p : OracleComp spec α) : Type (max u v w) where
  | done (a : α) (path : Prefix p (.pure a)) : Checkpoint p
  | call (q : Q) (resume : spec q → OracleComp spec α)
      (path : Prefix p (.liftBind q resume)) : Checkpoint p

namespace Checkpoint

/-- Extend a checkpoint backwards by one answered request. -/
@[expose] def prepend {q : Q} {k : spec q → OracleComp spec α} (a : spec q) :
    Checkpoint (k a) → Checkpoint (PFunctor.FreeM.liftBind q k)
  | .done b path => .done b (.step a path)
  | .call t resume path => .call t resume (.step a path)

/-- Follow at most `n` replies from a stateful reply source; stop before issuing query `n`. -/
@[expose] def seek {S : Type z} (answer : (q : Q) → S → spec q × S) :
    (n : ℕ) → (p : OracleComp spec α) → S → Checkpoint p
  | _, .pure a, _ => .done a (.root _)
  | 0, .liftBind q k, _ => .call q k (.root _)
  | n + 1, .liftBind q k, s =>
    let (a, s') := answer q s
    prepend a (seek answer n (k a) s')

/-- Requests through the selected position, including the focused, unanswered query if present. -/
@[expose] def queries {p : OracleComp spec α} : Checkpoint p → List Q
  | .done _ path => path.events.map Sigma.fst
  | .call q _ path => path.events.map Sigma.fst ++ [q]

/-- The selected request and its zero-based occurrence among requests with that same name.
The count excludes the selected request itself. -/
@[expose] def occurrence? [DecidableEq Q] {p : OracleComp spec α} :
    Checkpoint p → Option (Q × ℕ)
  | .done .. => none
  | .call q _ path => some (q, (path.events.map Sigma.fst).count q)

/-- Crossing one earlier request increases the occurrence number exactly when its name matches. -/
@[simp] theorem occurrence?_prepend [DecidableEq Q] {q : Q} {k : spec q → OracleComp spec α}
    (a : spec q) (c : Checkpoint (k a)) :
    (prepend a c).occurrence? = c.occurrence?.map
      (fun (r, n) => (r, n + if q = r then 1 else 0)) := by
  cases c with
  | done => rfl
  | call r f path => simp only [prepend, occurrence?, Prefix.events, List.map_cons,
      List.count_cons, beq_iff_eq, Option.map_some]

@[simp] private theorem queries_prepend {q : Q} {k : spec q → OracleComp spec α}
    (a : spec q) (c : Checkpoint (k a)) :
    (prepend a c).queries = q :: c.queries := by
  cases c <;> rfl

@[simp] theorem queries_seek_succ {S : Type z} (answer : (q : Q) → S → spec q × S) (n : ℕ)
    (q : Q) (k : spec q → OracleComp spec α) (s : S) :
    (seek answer (n + 1) (.liftBind q k) s).queries =
      q :: (seek answer n (k (answer q s).1) (answer q s).2).queries := by
  simp only [seek, queries_prepend]

end Checkpoint

end Cslib.OracleComp
