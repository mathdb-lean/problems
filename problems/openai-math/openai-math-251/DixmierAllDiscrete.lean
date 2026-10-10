import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.Discrete
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

- problem_id: DixmierAllDiscrete
- collection: openai-math
- question_id: openai-math:251
- source: openai-math
- source_locator: lean/ComparatorChallenges/DixmierAllDiscrete.lean#OAI.Dixmier.current_main_theorem
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Resolves Dixmier's problem for all discrete groups: amenability is equivalent to every uniformly bounded Hilbert-space representation being similar to a unitary representation. For countable discrete groups, amenability is also equivalent to strong Ulam stability: sufficiently accurate unitary approximate representations are uniformly close in operator norm to genuine representations on the same, possibly infinite-dimensional, Hilbert space. ([Lean](lean/docs/251.md)) We prove that a discrete group is amenable if and only if every uniformly bounded representation on a complex Hilbert space is similar to a unitary representation. This resolves Dixmier's unitarizability problem affirmatively for discrete groups.
- notes: OpenAI math result family 251, Amenability, unitarizability, and strong Ulam stability -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/251.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Dixmier.current_main_theorem
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.Unitarizability.AllDiscrete
- source_main_result: OAI.Dixmier.current_main_theorem
- source_papers: preprints/Unitarizability-Implies-Amenability-for-Countable-Groups-September-23-2026/paper.pdf
- source_scope_note: lean/docs/251.md
- source_field: Analysis
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section
universe u v
namespace Dixmier
open scoped BoundedContinuousFunction

def leftTranslate {G : Type u} [Group G] [TopologicalSpace G]
    [DiscreteTopology G] (g : G) (f : G →ᵇ ℂ) : G →ᵇ ℂ :=
  f.compContinuous ⟨fun x => g⁻¹ * x, continuous_of_discreteTopology⟩

def Amenable (G : Type u) [Group G] [TopologicalSpace G]
    [DiscreteTopology G] : Prop :=
  ∃ m : (G →ᵇ ℂ) →ₗ[ℂ] ℂ,
    m (BoundedContinuousFunction.const G 1) = 1 ∧
    (∀ f : G →ᵇ ℂ, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) →
      0 ≤ (m f).re ∧ (m f).im = 0) ∧
    ∀ (g : G) (f : G →ᵇ ℂ), m (leftTranslate g f) = m f

def SimilarToUnitary {G : Type u} [Group G]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : G →* (H →L[ℂ] H)) : Prop :=
  ∃ S : H ≃L[ℂ] H, ∀ (g : G) (x : H), ‖S (π g (S.symm x))‖ = ‖x‖

def Unitarizable (G : Type u) [Group G] : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (π : G →* (H →L[ℂ] H)),
    (∃ C : ℝ, ∀ g, ‖π g‖ ≤ C) → SimilarToUnitary π

def CurrentMainTheorem : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [DiscreteTopology G],
    (Amenable G ↔ Unitarizable.{u, max u v} G) ∧
    ∀ (ε : ℝ), 0 < ε → ¬ Amenable G →
      ∃ (H : Type (max u v)) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
        (_ : CompleteSpace H) (π : G →* (H →L[ℂ] H)),
        (Countable G → TopologicalSpace.SeparableSpace H) ∧
        (∀ g, ‖π g‖ ≤ 1 + ε) ∧ ¬ SimilarToUnitary π

def current_main_theorem_statement : Prop :=
  CurrentMainTheorem.{u,v}

end Dixmier
end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u, v} : Prop :=
  _root_.OAI.Dixmier.current_main_theorem_statement.{u, v}

end Problem

/- Formalization scope, from lean/docs/251.md: Dixmier's unitarizability problem asks whether a discrete group is amenable exactly when every uniformly bounded Hilbert-space representation is similar to a unitary one. The formalization establishes this equivalence for every discrete group. For every nonamenable group and every $\varepsilon>0$, it also gives a nonunitarizable representation with uniform operator bound at most $1+\varepsilon$. The Hilbert space can be chosen separable for countable groups; a separate linked statement records a separable witness with uniform bound $101$ in that case. -/
