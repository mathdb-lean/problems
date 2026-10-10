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

- problem_id: DiskMaximal
- collection: openai-math
- question_id: openai-math:085
- source: openai-math
- source_locator: lean/ComparatorChallenges/DiskMaximal.lean#OAI.CenteredDiskEndpoint.main_endpoint
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Resolves the planar centered-disk case of the Hajłasz–Onninen maximal-function regularity problem. For every real $`f\in W^{1,1}(\mathbb R^2)`$, the centered disk maximal function satisfies $`\|\nabla Mf\|_1\le C\|\nabla f\|_1`$ with an absolute constant. It belongs locally to $`W^{1,1}`$ and has a globally integrable weak gradient. ([Lean](lean/docs/085.md)) We prove the endpoint gradient bound $`\|\nabla Mf\|_1\le C\|\nabla f\|_1`$ for every real-valued $`f\in W^{1,1}(\mathbb R^2)`$, where $`Mf(x)`$ is the supremum of the averages of $`|f|`$ over disks centered at x, and C is an absolute constant. The maximal function belongs to $`W^{1,1}_{\mathrm{loc}}(\mathbb R^2)`$ and has a globally integrable weak gradient. This gives a positive resolution of the planar centered-disk case of the endpoint question of Hajłasz and Onninen.
- notes: OpenAI math result family 085, Endpoint Sobolev regularity of centered disk averages -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/085.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.CenteredDiskEndpoint.main_endpoint
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.DiskMaximal.Main
- source_papers: preprints/An-Endpoint-Gradient-Bound-for-the-Centered-Disk-Maximal-Operator-September-26-2026/article.pdf
- source_scope_note: lean/docs/085.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff

noncomputable section
namespace CenteredDiskEndpoint

/-- The Euclidean plane, not the product space with its max norm. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Absolute disk average, retaining possible infinite values. -/
def absoluteDiskAverage (f : Plane → ℝ) (x : Plane) (r : ℝ) : ℝ≥0∞ :=
  (∫⁻ y in Metric.ball x r, ENNReal.ofReal |f y|) /
    ENNReal.ofReal (Real.pi * r ^ 2)

/-- The actual centered disk maximal function, over every positive real radius. -/
def maximal (f : Plane → ℝ) (x : Plane) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : 0 < r), absoluteDiskAverage f x r

/-- Real representative; the endpoint also asserts that `maximal f` is finite a.e. -/
def maximalReal (f : Plane → ℝ) (x : Plane) : ℝ := (maximal f x).toReal

/-- The i-th coordinate derivative of a smooth test function. -/
def testPartial (φ : Plane → ℝ) (i : Fin 2) (x : Plane) : ℝ :=
  fderiv ℝ φ x (EuclideanSpace.single i 1)

/-- Distributional first derivatives represented by a vector-valued function. -/
def HasWeakGradient (f : Plane → ℝ) (g : Plane → Plane) : Prop :=
  ∀ (φ : Plane → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
    ∀ i : Fin 2, (∫ x, f x * testPartial φ i x) = -∫ x, g x i * φ x

/-- Local W^(1,1), expressed using the same distributional gradient convention. -/
def InW11Loc (f : Plane → ℝ) : Prop :=
  LocallyIntegrable f ∧
    ∃ g : Plane → Plane, LocallyIntegrable g ∧ HasWeakGradient f g

/-- The gradient L1 norm in Euclidean norm. -/
def gradientNorm (g : Plane → Plane) : ℝ := ∫ x, ‖g x‖

/-- Exact endpoint, including finiteness before passing to the real representative.
Quantifying the input gradient makes the norm bound independent of a choice of
representative of its weak derivatives. -/
def EndpointStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (f : Plane → ℝ) (g : Plane → Plane),
      Integrable f → Integrable g → HasWeakGradient f g →
      (∀ᵐ x, maximal f x ≠ ⊤) ∧
      LocallyIntegrable (maximalReal f) ∧
      InW11Loc (maximalReal f) ∧
      ∃ G : Plane → Plane, Integrable G ∧
        HasWeakGradient (maximalReal f) G ∧ gradientNorm G ≤ C * gradientNorm g

def main_endpoint_statement : Prop :=
  EndpointStatement

end CenteredDiskEndpoint

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.CenteredDiskEndpoint.main_endpoint_statement

end Problem

/- Formalization scope, from lean/docs/085.md: The centered disk maximal operator takes the supremum of averages of $|f|$ over disks centered at each point. The formalization proves that every real $f\in W^{1,1}(\mathbb R^2)$ has a maximal function that is finite almost everywhere, belongs to $W^{1,1}_{\mathrm{loc}}$, and has a globally integrable weak gradient satisfying $\|\nabla Mf\|_1\le C\|\nabla f\|_1$ for one absolute constant $C$. The earlier signed finite-band estimate for smooth compactly supported functions is also retained. The general endpoint statement covers the Sobolev setting of the paper; a BV extension is outside these statements. -/
