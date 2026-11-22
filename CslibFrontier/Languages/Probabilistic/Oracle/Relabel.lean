/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Devon Tuma
-/

module
-- upstream: candidate

public import Cslib.Foundations.Data.PFunctor.Free.Lens
public import CslibFrontier.Languages.Probabilistic.Basic

/-!
# Relabeling typed oracle requests

A relabeling sends each request to one target request and decodes its reply. Relabeling twice
composes the request maps in execution order and the reply maps in reverse order.
The request and reply maps form a polynomial lens.
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
  program.mapLens (P := ⟨ι, spec⟩) (Q := ⟨κ, target⟩) ⟨send, decode⟩

/-- Relabeling each request and reply by the identity preserves the program. -/
@[simp] theorem relabel_id {α : Type w} (program : OracleComp spec α) :
    relabel (target := spec) id (fun _ => id) program = program :=
  PFunctor.FreeM.mapLens_id program

/-- Successive relabelings compose the request maps and decode each pair of replies in reverse
order. -/
theorem relabel_relabel {mid : κ → Type v'} {target : η → Type v''}
    (first : ι → κ) (decode : (q : ι) → mid (first q) → spec q)
    (second : κ → η) (decode' : (q : κ) → target (second q) → mid q)
    {α : Type w} (program : OracleComp spec α) :
    relabel second decode' (relabel first decode program) =
      relabel (second ∘ first) (fun q => decode q ∘ decode' (first q)) program :=
  PFunctor.FreeM.mapLens_mapLens (P := ⟨ι, spec⟩) (Q := ⟨κ, mid⟩) (R := ⟨η, target⟩)
    ⟨second, decode'⟩ ⟨first, decode⟩ program

/-- One-query substitution along a request map acts by the associated polynomial lens. -/
theorem relabel_eq_substitute {target : κ → Type v'} (send : ι → κ)
    (decode : (q : ι) → target (send q) → spec q) {α : Type w} (program : OracleComp spec α) :
    relabel send decode program =
      substitute (fun q => PFunctor.FreeM.map (decode q) (query (send q))) program := by
  induction program with
  | pure => rfl
  | liftBind q k ih => exact congrArg (PFunctor.FreeM.liftBind (send q)) (funext fun b => ih _)

variable {target : κ → Type v} (send : ι → κ) (decode : (q : ι) → target (send q) → spec q)

/-- Interpreting a relabeled program forwards the request to the given handler and decodes the
reply in the handler's monad. -/
theorem interpret_relabel {m : Type v → Type z} [Monad m] [LawfulMonad m]
    (oracle : (q : κ) → m (target q)) {α : Type v} (program : OracleComp spec α) :
    interpret oracle (relabel send decode program) =
      interpret (fun q => decode q <$> oracle (send q)) program :=
  PFunctor.FreeM.liftM_mapLens (P := ⟨ι, spec⟩) (Q := ⟨κ, target⟩) ⟨send, decode⟩ oracle program

end OracleComp

end Cslib
