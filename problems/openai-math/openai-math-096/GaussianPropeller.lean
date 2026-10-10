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

- problem_id: GaussianPropeller
- collection: openai-math
- question_id: openai-math:096
- source: openai-math
- source_locator: lean/ComparatorChallenges/GaussianPropeller.lean#OAI.GaussianPropeller.all_partitions
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves that the sum of squared Gaussian first moments of any finite measurable partition is at most $`9/(8\pi)`$. In dimension at least two, three planar sectors of angle $`2\pi/3`$, extended orthogonally, attain the bound. Combined with the separate Unique Games theorem, this proves NP-hardness of improving the loss factor $`(8\pi/9)(1-1/k)`$ for identity-target kernel clustering with fixed k ≥ 3 on rational centered positive semidefinite inputs. ([Lean](lean/docs/096.md)) We prove the Gaussian propeller conjecture: for every finite measurable partition of a Euclidean space, the sum of the squared lengths of its Gaussian first moments is at most $`9/(8\pi)`$. For dimension at least two and at least three cells, three planar sectors of angle $`2\pi/3`$, extended by an orthogonal Euclidean factor, attain the bound.
- notes: OpenAI math result family 096, The Gaussian propeller conjecture in every dimension -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/096.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.GaussianPropeller.all_partitions
- source_theorem_count: 1
- source_solution_module: OAI.Probability.GaussianPropeller.Main
- source_main_result: OAI.GaussianPropeller.all_partitions
- source_papers: preprints/The-Gaussian-Propeller-Bound-in-Every-Dimension-September-24-2026/main.pdf
- source_scope_note: lean/docs/096.md
- source_field: Probability
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GaussianPropeller

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

noncomputable def gaussian (d : ℕ) : Measure (Space d) := stdGaussian (Space d)

def IsPartition {d k : ℕ} (A : Fin k → Set (Space d)) : Prop :=
  (∀ i, MeasurableSet (A i)) ∧ ∀ᵐ x ∂gaussian d, ∃! i, x ∈ A i

noncomputable def centroid {d : ℕ} (A : Set (Space d)) : Space d :=
  ∫ x in A, x ∂gaussian d

noncomputable def value {d k : ℕ} (A : Fin k → Set (Space d)) : ℝ :=
  ∑ i, ‖centroid (A i)‖ ^ 2

def coord {d : ℕ} (j : ℕ) (x : Space d) : ℝ :=
  if h : j < d then x ⟨j, h⟩ else 0

noncomputable def propeller (d k : ℕ) (i : Fin k) : Set (Space d) :=
  if i.val = 0 then {x | |coord 1 x| ≤ Real.sqrt 3 * coord 0 x}
  else if i.val = 1 then {x | 0 ≤ coord 1 x ∧ Real.sqrt 3 * coord 0 x ≤ coord 1 x}
  else if i.val = 2 then {x | coord 1 x ≤ 0 ∧ Real.sqrt 3 * coord 0 x ≤ -coord 1 x}
  else ∅

def AllPartitions : Prop :=
  (∀ (d k : ℕ), 0 < d → 0 < k → ∀ A : Fin k → Set (Space d),
    IsPartition A → value A ≤ 9 / (8 * Real.pi)) ∧
  (∀ (d k : ℕ), 2 ≤ d → 3 ≤ k →
    IsPartition (propeller d k) ∧ value (propeller d k) = 9 / (8 * Real.pi))

def all_partitions_statement : Prop :=
  AllPartitions

end GaussianPropeller

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.GaussianPropeller.all_partitions_statement

end Problem

/- Formalization scope, from lean/docs/096.md: The Gaussian propeller problem asks how large the sum of squared Gaussian first moments can be over a partition. The formalized result proves the sharp bound $9/(8\pi)$ for every positive dimension and every positive number of labelled cells, allowing empty cells and arbitrary masses. In dimension at least two with at least three cells, three planar sectors of angle $120^\circ$, extended in orthogonal directions, attain equality. The separate Gaussian-maxima and kernel-clustering consequences are not included. -/
