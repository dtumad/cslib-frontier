/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Devon Tuma
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.RunWith
public import CslibFrontier.Languages.Probabilistic.QueryCount

/-!
# Relabeling typed oracle requests

A relabeling sends each request to one target request and decodes its reply. Relabeling twice
composes the request maps in execution order and the reply maps in reverse order. A structural
cost bound transfers along any such map. When each decoder is surjective, every source branch
is represented and the bound also reflects. For programs with private randomness,
`ProbOracleComp.relabel` forwards only external requests.

The request and reply action follows `PFunctor.FreeM.mapLens` and `liftM_mapLens` in
[PolyFun](https://github.com/Verified-zkEVM/PolyFun/blob/713d8857/PolyFun/PFunctor/Free/Basic.lean).
The cost laws use `OracleComp.IsCostBounded`.
-/

public section

namespace Cslib

universe u u' u'' v v' v'' w z

namespace OracleComp

variable {ι : Type u} {κ : Type u'} {η : Type u''} {spec : ι → Type v}

/-- Replace each call by one request, then pass the decoded reply to its continuation. -/
@[expose] def relabel {target : κ → Type v'} (send : ι → κ)
    (decode : (q : ι) → target (send q) → spec q) {α : Type w}
    (program : OracleComp spec α) : OracleComp target α :=
  substitute (fun q => PFunctor.FreeM.map (decode q) (query (send q))) program

/-- Relabeling each request and reply by the identity preserves the program. -/
@[simp] theorem relabel_id {α : Type w} (program : OracleComp spec α) :
    relabel (target := spec) id (fun _ => id) program = program :=
  substitute_query_eq_self program

/-- Successive relabelings compose the request maps and decode each pair of replies in reverse
order. -/
theorem relabel_relabel {mid : κ → Type v'} {target : η → Type v''}
    (first : ι → κ) (decode : (q : ι) → mid (first q) → spec q)
    (second : κ → η) (decode' : (q : κ) → target (second q) → mid q)
    {α : Type w} (program : OracleComp spec α) :
    relabel second decode' (relabel first decode program) =
      relabel (second ∘ first) (fun q => decode q ∘ decode' (first q)) program := by
  simp only [relabel, substitute_substitute, substitute_map, substitute_query]
  rfl

variable {target : κ → Type v} (send : ι → κ) (decode : (q : ι) → target (send q) → spec q)

/-- Interpreting a relabeled program forwards the request to the given handler and decodes the
reply in the handler's monad. -/
theorem interpret_relabel {m : Type v → Type z} [Monad m] [LawfulMonad m]
    (oracle : (q : κ) → m (target q)) {α : Type v} (program : OracleComp spec α) :
    interpret oracle (relabel send decode program) =
      interpret (fun q => decode q <$> oracle (send q)) program := by
  simp only [relabel, substitute_eq_interpret, interpret_interpret, PFunctor.FreeM.map_eq_map,
    interpret_map, interpret_query]

/-- The cost of a relabeled request is the cost of the single target request it makes. -/
theorem IsCostBounded.relabel {cost : κ → ℕ} {α : Type v} {program : OracleComp spec α} {n : ℕ}
    (h : IsCostBounded (cost ∘ send) program n) :
    IsCostBounded cost (relabel send decode program) n := by
  rw [OracleComp.relabel, substitute_eq_interpret]
  exact h.interpret fun q => (isCostBounded_map_iff _ _ _).2 (IsCostBounded.query (send q))

/-- If every source reply can be obtained by decoding a target reply, a relabeling preserves
and reflects structural cost bounds. -/
theorem isCostBounded_relabel_iff (onto : ∀ q, Function.Surjective (decode q))
    (cost : κ → ℕ) {α : Type v} (program : OracleComp spec α) (n : ℕ) :
    IsCostBounded cost (relabel send decode program) n ↔ IsCostBounded (cost ∘ send) program n := by
  refine ⟨?_, IsCostBounded.relabel send decode⟩
  induction program generalizing n with
  | pure a => exact fun _ => .pure a n
  | liftBind q cont ih =>
    intro h
    change IsCostBounded cost (PFunctor.FreeM.liftBind (send q)
      (fun b => relabel send decode (cont (decode q b)))) n at h
    obtain ⟨hle, hnext⟩ := IsCostBounded.liftBind_iff.mp h
    refine IsCostBounded.liftBind_iff.mpr ⟨hle, fun a => ?_⟩
    obtain ⟨b, rfl⟩ := onto q a
    exact ih _ _ (hnext b)

end OracleComp

namespace ProbOracleComp

variable {ι : Type u} {κ : Type u'} {spec : ι → Type} {target : κ → Type}

/-- Relabel external requests, forwarding private samples to the same sampling interface. -/
@[expose] def relabel (send : ι → κ) (decode : (q : ι) → target (send q) → spec q)
    {α : Type w} (program : ProbOracleComp spec α) : ProbOracleComp target α :=
  simulate (fun q => decode q <$> query (send q)) program

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
