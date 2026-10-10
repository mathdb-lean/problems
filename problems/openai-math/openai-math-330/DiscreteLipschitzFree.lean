import Mathlib
/-
Copyright 2026 OpenAI. Licensed under the Apache License, Version 2.0.
Copyright 2026 The mathdb-lean Authors.

The definitions and the statements below are OpenAI's, from
github.com/openai/math at the revision named in the metadata block; see NOTICE.
What this library changed: each `sorry`-bodied theorem became the definition of
the proposition it stated, and `Problem.Target` conjoins those propositions.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

/-!
Converted from github.com/openai/math. `source_locator` names the comparator
challenge this came from and `source_solution_module` the module there that
proves it; both are at `source_version`. The definitions are the challenge's
own; each sorried theorem became `<name>_statement`, and `Problem.Target`
below conjoins them. `track` is solved because comparator accepted OpenAI's
proof against this very statement. Whether the statement says what the paper's
title says is what the scope note, carried as a caveat, is about.

- problem_id: DiscreteLipschitzFree
- collection: openai-math
- question_id: openai-math:330
- source: openai-math
- source_locator: lean/ComparatorChallenges/DiscreteLipschitzFree.lean#OAI.DiscreteFree.source_endpoints
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs a countable uniformly discrete metric space whose real Lipschitz-free Banach space has the approximation property but not the bounded approximation property, answering Kalton's question negatively. Finite-rank operators approximate the identity on every compact set, but their norms cannot share a finite bound. ([Lean](lean/docs/330.md)) We construct a countable uniformly discrete metric space whose real Lipschitz-free space has the approximation property but fails the bounded approximation property, answering Kalton's question negatively. The identity can be approximated on every compact set by finite-rank operators, but no uniform bound on their norms is possible.
- notes: OpenAI math result family 330, A uniformly discrete counterexample to bounded approximation in Lipschitz-free spaces -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/330.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.DiscreteFree.source_endpoints
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.LipschitzFree.Main
- source_papers: preprints/Failure-of-Bounded-Approximation-in-a-Lipschitz-Free-Space-over-a-Uniformly-Discrete-Metric-Space-September-26-2026/main.pdf
- source_scope_note: lean/docs/330.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

/-!
# Real Lipschitz-free spaces and approximation properties
-/

noncomputable section
open scoped BigOperators ENNReal

namespace DiscreteFree

variable {M : Type*} [MetricSpace M]

def lipSubmodule (o : M) : Submodule ℝ (M → ℝ) where
  carrier := {f | f o = 0 ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∀ x y, |f x - f y| ≤ C * dist x y}
  zero_mem' := by
    refine ⟨rfl, 0, le_rfl, ?_⟩
    intro x y
    simp
  add_mem' := by
    rintro f g ⟨hfo, C, hC, hf⟩ ⟨hgo, D, hD, hg⟩
    refine ⟨by simpa using congrArg₂ (· + ·) hfo hgo,
      C + D, add_nonneg hC hD, ?_⟩
    intro x y
    change |f x + g x - (f y + g y)| ≤ (C + D) * dist x y
    calc
      _ = |(f x - f y) + (g x - g y)| := by ring_nf
      _ ≤ |f x - f y| + |g x - g y| := abs_add_le _ _
      _ ≤ C * dist x y + D * dist x y := add_le_add (hf x y) (hg x y)
      _ = _ := by ring
  smul_mem' := by
    rintro c f ⟨hfo, C, hC, hf⟩
    refine ⟨by simp [hfo], |c| * C, mul_nonneg (abs_nonneg c) hC, ?_⟩
    intro x y
    change |c * f x - c * f y| ≤ (|c| * C) * dist x y
    calc
      _ = |c| * |f x - f y| := by rw [← mul_sub, abs_mul]
      _ ≤ |c| * (C * dist x y) := mul_le_mul_of_nonneg_left (hf x y) (abs_nonneg c)
      _ = _ := by ring

def Lip0 (o : M) := ↥(lipSubmodule o)

namespace Lip0

variable {o : M}

instance : AddCommGroup (Lip0 o) := inferInstanceAs (AddCommGroup ↥(lipSubmodule o))
instance : Module ℝ (Lip0 o) := inferInstanceAs (Module ℝ ↥(lipSubmodule o))

instance : CoeFun (Lip0 o) (fun _ => M → ℝ) := ⟨fun f => f.val⟩

def slope (o : M) : Lip0 o →ₗ[ℝ] lp (fun _ : M × M => ℝ) ∞ where
  toFun f := ⟨fun z : M × M => (f z.1 - f z.2) / dist z.1 z.2, by
    obtain ⟨C, hC, hf⟩ := f.property.2
    apply memℓp_infty
    refine ⟨C, ?_⟩
    rintro r ⟨⟨x, y⟩, rfl⟩
    change ‖(f x - f y) / dist x y‖ ≤ C
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg dist_nonneg]
    by_cases hxy : x = y
    · simp [hxy, hC]
    · exact (div_le_iff₀ (dist_pos.mpr hxy)).2 (hf x y)⟩
  map_add' f g := by
    apply lp.ext
    funext z
    change ((f z.1 + g z.1) - (f z.2 + g z.2)) / dist z.1 z.2 =
      (f z.1 - f z.2) / dist z.1 z.2 + (g z.1 - g z.2) / dist z.1 z.2
    ring
  map_smul' c f := by
    apply lp.ext
    funext z
    change (c * f z.1 - c * f z.2) / dist z.1 z.2 =
      c * ((f z.1 - f z.2) / dist z.1 z.2)
    ring

instance (o : M) : NormedAddCommGroup (Lip0 o) :=
  NormedAddCommGroup.induced _ _ (slope o).toAddMonoidHom (by
    intro f g h
    apply Subtype.ext
    funext x
    have hx := congrArg (fun q : lp (fun _ : M × M => ℝ) ∞ => q (x, o)) h
    change (f x - f o) / dist x o = (g x - g o) / dist x o at hx
    rw [f.property.1, g.property.1, sub_zero, sub_zero] at hx
    by_cases hxo : x = o
    · rw [hxo, f.property.1, g.property.1]
    · exact (div_left_inj' (ne_of_gt (dist_pos.mpr hxo))).mp hx)

instance (o : M) : NormedSpace ℝ (Lip0 o) :=
  NormedSpace.induced ℝ _ _ (slope o)

end Lip0

def evaluation (o x : M) : (Lip0 o →L[ℝ] ℝ) :=
  LinearMap.mkContinuous
    ({ toFun := fun f : Lip0 o => f x
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl } : Lip0 o →ₗ[ℝ] ℝ)
    (dist x o) (fun f => by
      change ‖f x‖ ≤ dist x o * ‖f‖
      rw [mul_comm]
      have hx := lp.norm_apply_le_norm (by simp : (∞ : ℝ≥0∞) ≠ 0)
        (Lip0.slope o f) (x, o)
      change ‖(f x - f o) / dist x o‖ ≤ ‖f‖ at hx
      rw [f.property.1, sub_zero, norm_div, Real.norm_of_nonneg dist_nonneg] at hx
      by_cases hxo : x = o
      · rw [hxo, f.property.1, norm_zero, dist_self, mul_zero]
      · exact (div_le_iff₀ (dist_pos.mpr hxo)).mp hx)

def freeSubmodule (o : M) : Submodule ℝ ((Lip0 o →L[ℝ] ℝ)) :=
  (Submodule.span ℝ (Set.range (evaluation o))).topologicalClosure

def FreeSpace (o : M) := ↥(freeSubmodule o)

instance (o : M) : NormedAddCommGroup (FreeSpace o) :=
  inferInstanceAs (NormedAddCommGroup ↥(freeSubmodule o))

instance (o : M) : NormedSpace ℝ (FreeSpace o) :=
  inferInstanceAs (NormedSpace ℝ ↥(freeSubmodule o))

def delta (o x : M) : FreeSpace o :=
  ⟨evaluation o x, Submodule.le_topologicalClosure _
    (Submodule.subset_span ⟨x, rfl⟩)⟩

def HasAP (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∀ C : Set X, IsCompact C → ∀ ε : ℝ, 0 < ε →
    ∃ T : X →L[ℝ] X, Module.Finite ℝ (LinearMap.range T.toLinearMap) ∧
      ∃ η : ℝ, η < ε ∧ ∀ u ∈ C, ‖T u - u‖ ≤ η

def HasBAP (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (Λ : ℝ) : Prop :=
  ∀ C : Set X, IsCompact C → ∀ ε : ℝ, 0 < ε →
    ∃ T : X →L[ℝ] X, Module.Finite ℝ (LinearMap.range T.toLinearMap) ∧
      ‖T‖ ≤ Λ ∧ ∃ η : ℝ, η < ε ∧ ∀ u ∈ C, ‖T u - u‖ ≤ η

def blockBound (p : ℕ) : ℝ := 300 * (p : ℝ)^2 + 150 * (p : ℝ) + 5

def BlockStatement : Prop :=
  ∀ p : ℕ, 1 ≤ p → ∃ (M : Type) (d : MetricSpace M) (o : M),
    letI := d
    Countable M ∧ (∀ x y : M, x ≠ y → 1 ≤ dist x y) ∧
      (∀ x y : M, dist x y ≤ blockBound p) ∧
      ∃ A : Finset M, o ∈ A ∧ ∀ T : FreeSpace o →L[ℝ] FreeSpace o,
        Module.Finite ℝ (LinearMap.range T.toLinearMap) → ‖T‖ ≤ (p : ℝ) →
          ∃ a ∈ A, (1 / 2 : ℝ) ≤ ‖T (delta o a) - delta o a‖

def MainStatement : Prop :=
  ∃ (M : Type) (d : MetricSpace M) (o : M),
    letI := d
    Countable M ∧ (∀ x y : M, x ≠ y → 1 ≤ dist x y) ∧
      (¬ Bornology.IsBounded (Set.univ : Set M)) ∧
      (¬ ProperSpace M) ∧ HasAP (FreeSpace o) ∧
      ∀ Λ : ℝ, 1 ≤ Λ → ¬ HasBAP (FreeSpace o) Λ

def source_endpoints_statement : Prop :=
  BlockStatement ∧ MainStatement

end DiscreteFree

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.DiscreteFree.source_endpoints_statement

end Problem

/- Formalization scope, from lean/docs/330.md: Kalton's question asks whether uniform discreteness of a metric space forces its Lipschitz-free space to have the bounded approximation property. The formalization constructs a countable metric space with all distinct points at distance at least one whose real Lipschitz-free space has the approximation property but fails every bounded approximation bound. The metric space is unbounded and not proper. The earlier quantitative renorming result for real $\ell_1$ is retained: for each integer $p\ge1$, an equivalent complete norm has the $2B_p$-bounded approximation property but fails the $p$-bounded approximation property, where $B_p=300p^2+150p+5$. -/
