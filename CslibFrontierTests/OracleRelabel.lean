/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import CslibFrontier.Languages.Probabilistic.Oracle.Relabel

/-! # Relabeling an adaptive request and preserving private samples -/

namespace CslibFrontierTests.OracleRelabel

open Cslib

private def branch : OracleComp (fun _ : Unit => Bool) Unit :=
  .liftBind () fun b => if b then .liftBind () (fun _ => .pure ()) else .pure ()

-- The decoder loses the branch on which two requests are made.
example : OracleComp.IsCostBounded (fun _ => 1)
    (OracleComp.relabel (target := fun _ : Unit => Unit) id (fun _ _ => false) branch) 1 :=
  OracleComp.IsCostBounded.liftBind_iff.mpr ⟨le_rfl, fun _ => .pure _ 0⟩

private theorem branch_ne_one : ¬OracleComp.IsCostBounded (fun _ => 1) branch 1 := by
  intro h
  have htrue := (OracleComp.IsCostBounded.liftBind_iff.mp h).2 true
  exact Nat.not_succ_le_zero 0 (OracleComp.IsCostBounded.liftBind_iff.mp htrue).1

-- Negating Boolean replies retains every source branch, so even after relabeling one call is
-- insufficient.
example : ¬OracleComp.IsCostBounded (fun _ => 1)
    (OracleComp.relabel (target := fun _ : Unit => Bool) id (fun _ => Bool.not) branch) 1 := by
  rw [OracleComp.isCostBounded_relabel_iff _ _ (fun _ b => ⟨!b, by cases b <;> rfl⟩)]
  exact branch_ne_one

-- The sampled bit still chooses the external request, whose numeric answer is decoded.
example :
    ProbOracleComp.relabel (spec := fun _ : Bool => Bool) (target := fun _ : Option Bool => ℕ)
      some (fun _ n => n == 0) (do
        let b ← ProbOracleComp.sample (ProbComp.unifFin 1)
        ProbOracleComp.query (b == 0)) =
      (do
        let b ← ProbOracleComp.sample (ProbComp.unifFin 1)
        (fun n => n == 0) <$> ProbOracleComp.query (spec := fun _ : Option Bool => ℕ)
          (some (b == 0))) := by
  simp [ProbOracleComp.relabel]

-- The first decoded answer enables a second request. Both state transitions are visible in
-- the joint law, including the transition made by the final request.
example :
    ProbOracleComp.runWith
      (spec := fun _ : Option Bool => ℕ) (fun _ (s : ℕ) => PMF.pure (s + 1, s + 1))
      (ProbOracleComp.relabel (spec := fun _ : Bool => Bool) some (fun _ n => n == 1) (do
        let again ← ProbOracleComp.query true
        if again then ProbOracleComp.query false else pure false)) 0 =
      PMF.pure (false, 2) := by
  simp [ProbOracleComp.runWith_relabel]

end CslibFrontierTests.OracleRelabel
