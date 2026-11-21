/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
-- upstream: candidate

public import Cslib.Foundations.Data.PFunctor.Basic
public import CslibFrontier.Computability.DecisionTree.Cost
public import CslibFrontier.Languages.Probabilistic.QueryCount

/-!
# Boolean decision trees as free query programs

Each node asks its variable for one bit. The two continuations of that call are the two
subtrees. `equivFreeM` identifies these representations, and `eval_toFreeM` interprets each
query by reading the input assignment. A structural path may give two different answers to
the same query. `weightedDepth_le_iff_isCostBounded` counts even these paths.
For large output types, map all leaves to `Unit` before applying the budget theorem.
`weightedDepth_map` preserves the weighted depth under this operation.

The correspondence and evaluation laws are ported from PolyFunFrontier's
`PFunctor.Free.DecisionTree` at `713d8857`.
-/

public section

universe u v

namespace Cslib.DecisionTree

open PFunctor

variable {ι : Type u} {β : Type v}

/-- A decision tree as a free program: a leaf returns its output, and a node queries its variable
and continues with the branch for the answer. -/
@[expose] def toFreeM : DecisionTree ι β → (monomial ι Bool).FreeM β
  | leaf b => .pure b
  | node i t₀ t₁ => .liftBind i fun b => cond b t₁.toFreeM t₀.toFreeM

/-- A free program over Boolean queries as a decision tree. -/
@[expose] def ofFreeM : (monomial ι Bool).FreeM β → DecisionTree ι β
  | .pure b => leaf b
  | .liftBind i k => node i (ofFreeM (k false)) (ofFreeM (k true))

@[simp] theorem toFreeM_leaf (b : β) : (leaf b : DecisionTree ι β).toFreeM = pure b := rfl

@[simp] theorem toFreeM_node (i : ι) (t₀ t₁ : DecisionTree ι β) :
    (node i t₀ t₁).toFreeM =
      (FreeM.lift (P := monomial ι Bool) i).bind fun b => cond b t₁.toFreeM t₀.toFreeM :=
  rfl

@[simp] theorem ofFreeM_pure (b : β) : ofFreeM (pure b : (monomial ι Bool).FreeM β) = leaf b :=
  rfl

@[simp] theorem ofFreeM_lift_bind (i : ι)
    (k : (monomial ι Bool).B i → (monomial ι Bool).FreeM β) :
    ofFreeM ((FreeM.lift (P := monomial ι Bool) i).bind
        (α := no_index (monomial ι Bool).B i) k) =
      node i (ofFreeM (k false)) (ofFreeM (k true)) :=
  rfl

@[simp] theorem ofFreeM_toFreeM (t : DecisionTree ι β) : ofFreeM t.toFreeM = t := by
  induction t with
  | leaf => rfl
  | node i t₀ t₁ ih₀ ih₁ => exact congrArg₂ (node i) ih₀ ih₁

@[simp] theorem toFreeM_ofFreeM (p : (monomial ι Bool).FreeM β) : (ofFreeM p).toFreeM = p := by
  induction p using FreeM.induction with
  | pure => rfl
  | lift_bind i k ih =>
    rw [ofFreeM_lift_bind, toFreeM_node]
    congr 1
    funext b
    cases b
    · exact ih false
    · exact ih true

/-- Decision trees over `ι` are exactly the free programs of the Boolean query interface
`monomial ι Bool`. -/
@[expose] def equivFreeM : DecisionTree ι β ≃ (monomial ι Bool).FreeM β where
  toFun := toFreeM
  invFun := ofFreeM
  left_inv := ofFreeM_toFreeM
  right_inv := toFreeM_ofFreeM

@[simp] theorem equivFreeM_apply (t : DecisionTree ι β) : equivFreeM t = t.toFreeM := rfl

@[simp] theorem equivFreeM_symm_apply (p : (monomial ι Bool).FreeM β) :
    equivFreeM.symm p = ofFreeM p :=
  rfl

/-- Evaluating a decision tree on `x` folds its free program, answering each query `i` by
`x i`. -/
theorem eval_toFreeM (t : DecisionTree ι β) (x : ι → Bool) :
    t.toFreeM.foldFreeM id (fun i k => k (x i)) = t.eval x := by
  induction t with
  | leaf => rfl
  | node i t₀ t₁ ih₀ ih₁ =>
    change FreeM.foldFreeM id _ (cond (x i) t₁.toFreeM t₀.toFreeM) = cond (x i) _ _
    cases x i
    · exact ih₀
    · exact ih₁

/-- A free program over Boolean queries, answered from `x`, returns what its decision tree
returns on `x`. -/
theorem eval_ofFreeM (p : (monomial ι Bool).FreeM β) (x : ι → Bool) :
    (ofFreeM p).eval x = p.foldFreeM id (fun i k => k (x i)) := by
  rw [← eval_toFreeM, toFreeM_ofFreeM]

/-- A weighted structural depth bound is precisely a free-program query budget. -/
theorem weightedDepth_le_iff_isCostBounded {γ : Type} (t : DecisionTree ι γ)
    (w : ι → ℕ) (n : ℕ) :
    t.weightedDepth w ≤ n ↔ OracleComp.IsCostBounded w t.toFreeM n := by
  induction t generalizing n with
  | leaf a => exact ⟨fun _ => .pure a n, fun _ => Nat.zero_le _⟩
  | node i l r il ir =>
    change max (l.weightedDepth w) (r.weightedDepth w) + w i ≤ n ↔
      OracleComp.IsCostBounded w
        (FreeM.liftBind i fun b : Bool => cond b r.toFreeM l.toFreeM) n
    rw [OracleComp.IsCostBounded.liftBind_iff, Bool.forall_bool]
    simp only [Bool.cond_false, Bool.cond_true, ← il, ← ir]
    omega

/-- Relabeling the leaves, including by the unique value of `Unit`, preserves structural cost. -/
@[simp] theorem weightedDepth_map {γ : Type*} (f : β → γ) (t : DecisionTree ι β) (w : ι → ℕ) :
    (t.map f).weightedDepth w = t.weightedDepth w := by
  induction t with
  | leaf => rfl
  | node i l r il ir => simp only [map, weightedDepth_node, il, ir]

end Cslib.DecisionTree
