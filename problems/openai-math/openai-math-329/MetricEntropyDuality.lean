import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Order.Lattice.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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

- problem_id: MetricEntropyDuality
- collection: openai-math
- question_id: openai-math:329
- source: openai-math
- source_locator: lean/ComparatorChallenges/MetricEntropyDuality.lean#OAI.MetricEntropyDuality.exists_entropy_duality_counterexample_with_covers
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Disproves Pietsch's dimension-free duality conjecture for metric entropy. Origin-symmetric convex bodies violate every proposed choice of universal constants in the conjectured comparison between covering numbers and those of the polar bodies, even when the covering body is a cube. ([Lean](lean/docs/329.md)) We disprove Pietsch's dimension-free duality conjecture for metric entropy. For every proposed pair of universal constants, we construct origin-symmetric convex bodies that violate the corresponding covering-entropy inequality, already when the covering body is a cube.
- notes: OpenAI math result family 329, A counterexample to metric-entropy duality -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/329.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.MetricEntropyDuality.exists_entropy_duality_counterexample_with_covers
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.MetricEntropy.Main
- source_main_result: OAI.MetricEntropyDuality.exists_entropy_duality_counterexample_with_covers
- source_papers: preprints/Counterexamples-to-the-duality-conjecture-for-metric-entropy-September-24-2026/main.pdf
- source_scope_note: lean/docs/329.md
- source_field: Analysis
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

universe u

noncomputable section

namespace MetricEntropyDuality

open Filter Topology
open scoped BigOperators Pointwise

abbrev RealSpace (ι : Type u) := ι → ℝ

def pairing {ι : Type u} [Fintype ι] (x y : RealSpace ι) : ℝ :=
  ∑ i, x i * y i

def cube (ι : Type u) : Set (RealSpace ι) :=
  {x | ∀ i, |x i| ≤ 1}

def polar {ι : Type u} [Fintype ι] (K : Set (RealSpace ι)) : Set (RealSpace ι) :=
  {y | ∀ x ∈ K, pairing x y ≤ 1}

def Covers {ι : Type u} {M : ℕ} (A B : Set (RealSpace ι))
    (centers : Fin M → RealSpace ι) : Prop :=
  ∀ x ∈ A, ∃ j, x - centers j ∈ B

def Coverable {ι : Type u} (A B : Set (RealSpace ι)) : Prop :=
  ∃ M : ℕ, ∃ centers : Fin M → RealSpace ι, Covers A B centers

def coveringNumber {ι : Type u} (A B : Set (RealSpace ι)) : ℕ :=
  sInf {M : ℕ | ∃ centers : Fin M → RealSpace ι, Covers A B centers}

structure IsSymmetricConvexBody {ι : Type u} [Fintype ι]
    (K : Set (RealSpace ι)) : Prop where
  isCompact : IsCompact K
  convex : Convex ℝ K
  symmetric : ∀ x, x ∈ K ↔ -x ∈ K
  interior_nonempty : (interior K).Nonempty

def exists_entropy_duality_counterexample_with_covers_statement : Prop :=
  ∀ (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b),
    ∃ n : ℕ, 0 < n ∧ ∃ K : Set (RealSpace (Fin n)),
      IsSymmetricConvexBody K ∧
      Coverable K (cube (Fin n)) ∧
      Coverable (polar (cube (Fin n))) (a⁻¹ • polar K) ∧
      b * Real.log (coveringNumber (polar (cube (Fin n))) (a⁻¹ • polar K) : ℝ) <
        Real.log (coveringNumber K (cube (Fin n)) : ℝ)

end MetricEntropyDuality

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.MetricEntropyDuality.exists_entropy_duality_counterexample_with_covers_statement

end Problem

/- Formalization scope, from lean/docs/329.md: Metric-entropy duality predicts a universal comparison between covering numbers of convex bodies and their polars. The formalized result disproves such a comparison: for every $a,b\ge1$, there is an origin-symmetric convex body $K$ in a positive finite dimension with $\log N(K,B_\infty)>b\log N(B_\infty^\circ,a^{-1}K^\circ)$, where $N$ is the least number of translates in a finite cover. A further construction makes the dual-to-primal logarithmic entropy ratio tend to zero as the dimension grows. -/
