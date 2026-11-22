/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Devon Tuma
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Oracle.Relabel
public import CslibFrontier.Languages.Probabilistic.QueryCount

/-!
# Structural query budgets under relabeling

A cost bound transfers along any relabeling. A surjective decoder reaches every branch of the
source program, so the bound also reflects.
-/

public section

namespace Cslib.OracleComp

universe u u' v

variable {ι : Type u} {κ : Type u'} {spec : ι → Type v} {target : κ → Type v}
  (send : ι → κ) (decode : (q : ι) → target (send q) → spec q)

/-- The cost of a relabeled request is the cost of the single target request it makes. -/
theorem IsCostBounded.relabel {cost : κ → ℕ} {α : Type v} {program : OracleComp spec α} {n : ℕ}
    (h : IsCostBounded (cost ∘ send) program n) :
    IsCostBounded cost (relabel send decode program) n := by
  rw [relabel_eq_substitute, substitute_eq_interpret]
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

end Cslib.OracleComp
