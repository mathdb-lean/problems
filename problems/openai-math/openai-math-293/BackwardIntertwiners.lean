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

- problem_id: BackwardIntertwiners
- collection: openai-math
- question_id: openai-math:293
- source: openai-math
- source_locator: lean/ComparatorChallenges/BackwardIntertwiners.lean#OAI.BackwardIntertwiners.direct_algebra_corollary
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs a nonzero norm-quasinilpotent operator on every infinite-dimensional separable complex Hilbert space with no nonzero proper closed subspace invariant under every commuting operator. The construction also gives operators with no nontrivial invariant projection in the hyperfinite type II1 factor. ([Lean](lean/docs/293.md)) For every irrational angle, we construct a continuous nonnegative circle weight with exactly one zero and logarithmic integral $`-\infty`$ whose weighted rotation has no nontrivial invariant projection in the associated hyperfinite type II1 factor. This answers negatively the question of Zhu, Fang, and Shi, with the angle prescribed in advance. The resulting operator is nonzero and norm-quasinilpotent. We give a negative answer to the hyperinvariant-subspace problem by constructing, on every infinite-dimensional separable complex Hilbert space, a nonzero bounded norm-quasinilpotent operator with no nonzero proper closed hyperinvariant subspace. Its commutant is a proper strongly closed unital transitive complex operator algebra. We give a negative answer to the hyperinvariant-subspace problem by constructing, on every infinite-dimensional separable complex Hilbert space, a nonzero bounded norm-quasinilpotent operator with no nonzero proper closed hyperinvariant subspace. Its commutant is a proper strongly closed unital transitive complex operator algebra.
- notes: OpenAI math result family 293, Invariant projections, hyperinvariant subspaces, and transitive algebras -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/293.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.BackwardIntertwiners.direct_algebra_corollary
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.BackwardIntertwiners.AlgebraCorollary
- source_main_result: OAI.BackwardIntertwiners.direct_algebra_corollary
- source_papers: preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf preprints/Backward-intertwiners-and-a-transitive-commutant-September-27-2026/paper.pdf preprints/Backward-intertwiners-and-a-transitive-commutant-September-27-2026/paper.pdf
- source_scope_note: lean/docs/293.md
- source_field: Analysis
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace Hyperinvariant233
open Filter
open scoped Topology
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def commutant (T : H →L[ℂ] H) : Subalgebra ℂ (H →L[ℂ] H) :=
  Subalgebra.centralizer ℂ ({T} : Set (H →L[ℂ] H))

def TransitiveCommutant (T : H →L[ℂ] H) : Prop :=
  ∀ K : Submodule ℂ H, IsClosed (K : Set H) →
    (∀ A : H →L[ℂ] H, A * T = T * A → ∀ x ∈ K, A x ∈ K) →
    K = ⊥ ∨ K = ⊤

@[instance_reducible]
def strongOperatorTopology : TopologicalSpace (H →L[ℂ] H) :=
  TopologicalSpace.induced (fun A : H →L[ℂ] H => (fun x : H => A x)) inferInstance

def FullClaim : Prop :=
  ∃ T : H →L[ℂ] H, T ≠ 0 ∧
    Tendsto (fun n : ℕ => ‖T ^ n‖ ^ (1 / (n : ℝ))) atTop (𝓝 0) ∧
    TransitiveCommutant T ∧ commutant T ≠ ⊤ ∧
    @IsClosed (H →L[ℂ] H) strongOperatorTopology (commutant T : Set (H →L[ℂ] H))

end Hyperinvariant233

namespace BackwardIntertwiners
open Filter Topology MeasureTheory Set
noncomputable section
open scoped ENNReal

def direct_algebra_corollary_statement : Prop :=
  ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H] (hInf : ¬FiniteDimensional ℂ H),
    Hyperinvariant233.FullClaim (H:=H)

end
end BackwardIntertwiners

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u_1} : Prop :=
  _root_.OAI.BackwardIntertwiners.direct_algebra_corollary_statement.{u_1}

end Problem

/- Formalization scope, from lean/docs/293.md: For every irrational rotation angle $\theta\in(0,1)$, the formalization constructs a continuous nonnegative circle weight with a single zero and logarithmic integral $-\infty$ whose weighted rotation is nonzero and quasinilpotent. In its associated hyperfinite type $\mathrm{II}_1$ factor, the operator has no nontrivial invariant projection: $(1-p)Tp=0$ forces $p=0$ or $p=1$. The linked statements also include an earlier existence construction, a product realization, and the selected product model's Brown measure $\delta_0$. The formalization for the companion paper [Backward intertwiners and a transitive commutant](../../preprints/Backward-intertwiners-and-a-transitive-commutant-September-27-2026/paper.pdf) gives, on every separable infinite-dimensional complex Hilbert space, a nonzero quasinilpotent operator whose commutant is transitive, proper, and closed in the strong operator topology. Thus no nontrivial closed subspace is invariant under every operator in the commutant. The hyperinvariant-subspace problem asks whether every bounded operator on a complex Hilbert space has a nontrivial closed subspace invariant under every operator that commutes with it. The formalization gives a negative answer on every separable infinite-dimensional complex Hilbert space: there is a nonzero quasinilpotent operator with a transitive commutant. Its commutant is a proper unital operator algebra closed in the strong operator topology. The construction therefore has no nonzero proper closed hyperinvariant subspace. -/
