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

- problem_id: BernoulliNonflatInSeven
- collection: openai-math
- question_id: openai-math:367
- source: openai-math
- source_locator: lean/ComparatorChallenges/BernoulliNonflatInSeven.lean#OAI.Bernoulli.nonflat_in_seven
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Establishes seven as the first dimension admitting a nonflat, one-homogeneous global minimizer of the one-phase Bernoulli energy. Consequently, minimizing free boundaries are smooth through dimension six, and their singular sets have dimension at most $`n-7`$ in higher dimensions. ([Lean](lean/docs/367.md)) We prove that seven is the critical dimension for the one-phase Bernoulli problem: every nonzero one-homogeneous global minimizer in dimensions at most six is flat, while a nonflat one-homogeneous global minimizer exists in dimension seven. It follows that the interior free boundary of a local minimizer is smooth in dimensions at most six. In dimension n ≥ 7, its singular set has Hausdorff dimension at most $`n-7`$, and this bound is sharp. In dimension seven, the singular set is locally finite.
- notes: OpenAI math result family 367, The critical dimension for the one-phase Bernoulli problem -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/367.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Bernoulli.nonflat_in_seven
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.BernoulliCone.Main
- source_papers: preprints/The-critical-dimension-for-one-phase-Bernoulli-minimizers-September-24-2026/The-critical-dimension-for-one-phase-Bernoulli-minimizers-September-24-2026.pdf
- source_scope_note: lean/docs/367.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace Bernoulli
open scoped _root_.Bernoulli

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Compactly supported smooth real tests in the open set. -/
def Test {d : ℕ} (D : Set (Space d)) (φ : Space d → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ D

/-- Distributional gradient, tested in every constant direction. -/
def WeakGradient {d : ℕ} (D : Set (Space d))
    (u : Space d → ℝ) (G : Space d → Space d) : Prop :=
  ∀ φ, Test D φ → ∀ h : Space d,
    (∫ x in D, u x * (fderiv ℝ φ x) h) =
      -(∫ x in D, inner ℝ (G x) h * φ x)

/-- H¹(D), with its weak gradient. -/
def H1 {d : ℕ} (D : Set (Space d))
    (u : Space d → ℝ) (G : Space d → Space d) : Prop :=
  MemLp u 2 (volume.restrict D) ∧
  MemLp G 2 (volume.restrict D) ∧ WeakGradient D u G

/-- H¹₀(D) is H¹-closure of C∞ compactly supported functions.
Both L² errors tend to zero. This does not restrict competitors to smooth ones. -/
def H10 {d : ℕ} (D : Set (Space d))
    (u : Space d → ℝ) (G : Space d → Space d) : Prop :=
  H1 D u G ∧ ∀ ε : ℝ, 0 < ε → ∃ φ : Space d → ℝ,
    Test D φ ∧
    eLpNorm (fun x => u x - φ x) 2 (volume.restrict D) < ENNReal.ofReal ε ∧
    eLpNorm (fun x => G x - gradient φ x) 2 (volume.restrict D) < ENNReal.ofReal ε

/-- Ballwise H¹_loc, on an open set (balls have compact closure inside D). -/
def H1Loc {d : ℕ} (D : Set (Space d))
    (u : Space d → ℝ) (G : Space d → Space d) : Prop :=
  ∀ c : Space d, ∀ r : ℝ, 0 < r → Metric.closedBall c r ⊆ D →
    H1 (Metric.ball c r) u G

/-- The exact volume-one Bernoulli energy, not just Dirichlet energy. -/
def energy {d : ℕ} (D : Set (Space d))
    (u : Space d → ℝ) (G : Space d → Space d) : ℝ :=
  ∫ x in D, ‖G x‖ ^ 2 + if 0 < u x then (1 : ℝ) else 0

/-- Full ballwise local comparison. Competitor and gradient are arbitrary
Sobolev representatives on the ball, with zero-trace difference. -/
def LocalMinimizer {d : ℕ} (D : Set (Space d)) (u : Space d → ℝ) : Prop :=
  IsOpen D ∧ ∃ G : Space d → Space d,
    H1Loc D u G ∧ (∀ᵐ x ∂volume.restrict D, 0 ≤ u x) ∧
    ∀ c : Space d, ∀ r : ℝ, 0 < r → Metric.closedBall c r ⊆ D →
      ∀ (v : Space d → ℝ) (V : Space d → Space d),
        H1 (Metric.ball c r) v V →
        (∀ᵐ x ∂volume.restrict (Metric.ball c r), 0 ≤ v x) →
        H10 (Metric.ball c r) (fun x => v x - u x) (fun x => V x - G x) →
        energy (Metric.ball c r) u G ≤ energy (Metric.ball c r) v V

/-- Nonnegative global minimizer, with all centers and all positive radii. -/
def GlobalMinimizer {d : ℕ} (u : Space d → ℝ) : Prop :=
  LocalMinimizer Set.univ u

def OneHomogeneous {d : ℕ} (u : Space d → ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ᵐ x ∂volume, u (r • x) = r * u x

def Nonzero {d : ℕ} (u : Space d → ℝ) : Prop :=
  ¬ (u =ᵐ[volume] fun _ => 0)

/-- Flatness is a.e. equality of H¹ representatives. -/
def Flat {d : ℕ} (u : Space d → ℝ) : Prop :=
  ∃ e : Space d, ‖e‖ = 1 ∧ ∀ᵐ x ∂volume, u x = max (inner ℝ x e) 0

def nonflat_in_seven_statement : Prop :=
  ∃ u : Space 7 → ℝ,
    GlobalMinimizer u ∧ Nonzero u ∧ OneHomogeneous u ∧ ¬ Flat u

end Bernoulli

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.Bernoulli.nonflat_in_seven_statement

end Problem

/- Formalization scope, from lean/docs/367.md: The paper identifies seven as the critical dimension for nonflat one-homogeneous global minimizers of the one-phase Bernoulli problem. The linked formalization proves the existence side: in dimension seven there is a nonzero one-homogeneous global minimizer that is not a half-space solution. The flatness classification in dimensions at most six and the resulting regularity and singular-set bounds are outside this selected statement. -/
