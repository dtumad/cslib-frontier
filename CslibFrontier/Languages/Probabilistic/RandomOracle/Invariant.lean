/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Alexander Hicks
-/

module
-- upstream: candidate

public import Cslib.Foundations.Data.PFunctor.Free.Partial
public import CslibFrontier.Languages.Probabilistic.Oracle.EvalPure
public import CslibFrontier.Languages.Probabilistic.RandomOracle
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Tactic.SuppCases

/-!
# Cache invariants of the lazy random oracle

A run of an oracle program under the lazy random oracle `RandomOracle.answer dist` only extends
its cache, samples fresh answers from the support of `dist`, and returns what the program
computes against any total oracle extending the final cache
(`OracleComp.mem_support_runWith_answer_invariant`). Completing the final cache to a total oracle
with `OracleComp.cacheOracle` turns facts about deterministic evaluation (`OracleComp.evalPure`)
into facts about the lazy random-oracle run: a program that returns `a` against every oracle drawn
from the pointwise support of `dist` returns `PMF.pure a` under `RandomOracle.answer dist`
(`OracleComp.map_fst_runWith_answer_eq_pure`).

A partial interpretation runs the same program in `Option`, stopping at the first missing
answer. Every supported run succeeds under its own final cache. A handler that answers the
cached calls without changing its state then repeats the result with that entire state intact.
These settlement and replay laws adapt Alexander Hicks's `QueryCache.toPartialImpl` laws
from VCVio's random-oracle query-tracking library.

## Main definitions

* `Cslib.OracleComp.cacheOracle`: a total oracle extending a cache, answering uncached queries
  with an element of the support of `dist`.

## Main results

* `Cslib.OracleComp.interpret_finalCache_of_mem_support_runWith_answer`: each supported run
  settles its program in its final cache.
* `PFunctor.FreeM.run_liftM_eq_pure_of_liftM_eq_some` replays a settled program while
  preserving the entire interpreter state.
* `Cslib.OracleComp.mem_support_runWith_answer_invariant`: the cache invariant of supported runs.
* `Cslib.OracleComp.map_fst_runWith_answer_eq_pure`: oracle programs that are constant on the
  support of `dist` are deterministic under the lazy random oracle.
-/

@[expose] public section

namespace Cslib

namespace OracleComp

universe u

variable {ι : Type u} {spec : OracleSpec.{u, u} ι} {α : Type u}

/-- Every supported lazy run extends its initial cache, adds only supported fresh assignments,
and can be replayed by looking up the entries in its final cache. Entries supplied at the start
may already lie outside their samplers' support. -/
theorem interpret_finalCache_of_mem_support_runWith_answer [DecidableEq ι]
    (dist : (q : ι) → PMF (spec q)) (prog : OracleComp spec α)
    {cache cache' : RandomOracle.Cache spec} {res : α}
    (hmem : (res, cache') ∈ (runWith (RandomOracle.answer dist) prog cache).support) :
    (∀ q v, cache q = some v → cache' q = some v) ∧
      (∀ q v, cache q = none → cache' q = some v → v ∈ (dist q).support) ∧
      interpret cache' prog = some res := by
  induction prog using OracleComp.induction generalizing cache with
  | pure a =>
    supp_cases hmem [runWith_pure] with ⟨rfl, rfl⟩
    exact ⟨fun _ _ h => h, fun _ _ h h' => by simp [h] at h', rfl⟩
  | query_bind q cont ih =>
    rw [runWith_freeMBind, runWith_query] at hmem
    supp_cases hmem with ⟨⟨ans, next⟩, hstep, hrest⟩
    rw [PFunctor.FreeM.bind_eq_bind, interpret_bind, interpret_query]
    cases hq : cache q with
    | some value =>
      supp_cases hstep [RandomOracle.answer_of_some dist cache q value hq] with ⟨rfl, rfl⟩
      obtain ⟨extend, fresh, replay⟩ := ih _ hrest
      exact ⟨extend, fresh, by simp [extend q _ hq, replay]⟩
    | none =>
      supp_cases hstep [RandomOracle.answer_of_none dist cache q hq] with ⟨v, hv, rfl, rfl⟩
      obtain ⟨extend, fresh, replay⟩ := ih v hrest
      have stored := extend q v (Function.update_self ..)
      refine ⟨fun k x hk => ?_, fun k x hk hfinal => ?_, by simp [stored, replay]⟩
      · apply extend
        have hne : k ≠ q := by rintro rfl; simp [hq] at hk
        simpa [Function.update_of_ne hne] using hk
      · by_cases h : k = q
        · subst k
          have heq := Option.some.inj (stored.symm.trans hfinal)
          exact heq ▸ hv
        · exact fresh k x (by simpa [Function.update_of_ne h] using hk) hfinal

/-- Multi-step invariant of `runWith (RandomOracle.answer dist)`: any outcome `(res, cache')` in
the support of a run from `cache` produces a final cache `cache'` extending `cache` whose entries
lie in `(dist q).support`, and `res = evalPure h prog` for every total function `h` extending
`cache'`. -/
theorem mem_support_runWith_answer_invariant [DecidableEq ι] (dist : (q : ι) → PMF (spec q))
    (prog : OracleComp spec α) {cache cache' : RandomOracle.Cache spec} {res : α}
    (hsupp : ∀ q' v', cache q' = some v' → v' ∈ (dist q').support)
    (hmem : (res, cache') ∈ (runWith (RandomOracle.answer dist) prog cache).support) :
    (∀ q' v', cache q' = some v' → cache' q' = some v') ∧
      (∀ q' v', cache' q' = some v' → v' ∈ (dist q').support) ∧
      (∀ h : (q : ι) → spec q,
        (∀ q' v', cache' q' = some v' → h q' = v') → res = evalPure h prog) := by
  obtain ⟨extend, fresh, replay⟩ :=
    interpret_finalCache_of_mem_support_runWith_answer dist prog hmem
  refine ⟨extend, fun q v hv => ?_, fun h hh => ?_⟩
  · cases hq : cache q with
    | none => exact fresh q v hq hv
    | some w =>
      have hEq := Option.some.inj ((extend q w hq).symm.trans hv)
      exact hEq ▸ hsupp q w hq
  · exact (PFunctor.FreeM.liftM_eq_pure_of_liftM_eq_some (P := ⟨ι, spec⟩) (m := Id)
      cache' h hh replay).symm

/-- Extend a partial cache `cache` to a total deterministic oracle by returning `v` when
`cache q = some v` and otherwise choosing an element in `(dist q).support`. -/
noncomputable def cacheOracle (dist : (q : ι) → PMF (spec q))
    (cache : RandomOracle.Cache spec) (q : ι) : spec q :=
  (cache q).getD (Classical.choose (dist q).support_nonempty)

theorem cacheOracle_eq_of_eq_some (dist : (q : ι) → PMF (spec q))
    (cache : RandomOracle.Cache spec) {q : ι} {v : spec q} (h : cache q = some v) :
    cacheOracle dist cache q = v := by
  simp [cacheOracle, h]

theorem cacheOracle_mem_support (dist : (q : ι) → PMF (spec q))
    {cache : RandomOracle.Cache spec}
    (hsupp : ∀ q' v', cache q' = some v' → v' ∈ (dist q').support) (q : ι) :
    cacheOracle dist cache q ∈ (dist q).support := by
  unfold cacheOracle
  cases h : cache q with
  | none => exact Classical.choose_spec (dist q).support_nonempty
  | some v => exact hsupp q v h

/-- If an oracle program evaluates to `a` under every deterministic oracle drawn from the
point-wise support of `dist`, then running it under the lazy random oracle
`RandomOracle.answer dist` from the empty cache yields `PMF.pure a`. -/
theorem map_fst_runWith_answer_eq_pure [DecidableEq ι] (dist : (q : ι) → PMF (spec q))
    (prog : OracleComp spec α) (a : α)
    (hprog : ∀ h : (q : ι) → spec q, (∀ q, h q ∈ (dist q).support) → evalPure h prog = a) :
    (runWith (RandomOracle.answer dist) prog (fun _ => none)).map Prod.fst = PMF.pure a := by
  refine (Probability.PMF.map_congr_on_support _ Prod.fst (Function.const _ a) ?_).trans
    (PMF.map_const _ a)
  rintro ⟨res, cache'⟩ hmem
  obtain ⟨-, hsupp', heval⟩ := mem_support_runWith_answer_invariant dist prog (by simp) hmem
  have heq := heval (cacheOracle dist cache')
    (fun _ _ h => cacheOracle_eq_of_eq_some dist cache' h)
  exact heq.trans (hprog (cacheOracle dist cache') (cacheOracle_mem_support dist hsupp'))

end OracleComp

end Cslib
