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

- problem_id: TriangularHilbert
- collection: openai-math
- question_id: openai-math:082
- source: openai-math
- source_locator: lean/ComparatorChallenges/TriangularHilbert.lean#OAI.TriangularHilbert.main_estimate
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves maximal and annular r-variation bounds, for every r &gt; 2, from complex $`L^3(\mathbb R^2)\times L^3(\mathbb R^2)`$ to $`L^{3/2}(\mathbb R^2)`$. The maximal estimate controls both hard truncation endpoints and gives almost-everywhere and norm convergence. Pairing with a third input settles the triangular Hilbert transform estimate at the symmetric $`L^3\times L^3\times L^3`$ point. ([Lean](lean/docs/082.md)) For arbitrary complex inputs in $`L^3(\mathbb R^2)`$, we prove the pointwise maximal $`L^3\times L^3\to L^{3/2}`$ estimate for the triangular Hilbert transform, with the supremum over both hard truncation endpoints. The estimate yields joint almost-everywhere and L3/2 convergence as the lower endpoint tends to zero and the upper endpoint tends to infinity. This also proves the conjectured scalar estimate at the symmetric point.
- notes: OpenAI math result family 082, Annular variation and dyadic absolute bounds for the triangular Hilbert transform -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/082.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.TriangularHilbert.main_estimate
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.TriangularHilbert.Main
- source_main_result: OAI.TriangularHilbert.main_estimate
- source_papers: preprints/The-maximal-triangular-Hilbert-transform-at-the-symmetric-point-September-24-2026/paper.pdf
- source_scope_note: lean/docs/082.md
- source_field: Analysis
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace TriangularHilbert

abbrev Plane := ℝ × ℝ

structure Endpoints where
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  lower_lt_upper : lower < upper

def annulus (ε R : ℝ) : Set ℝ := {t | ε < |t| ∧ |t| < R}

def integrand (F G : Plane → ℂ) (z : Plane) (t : ℝ) : ℂ :=
  F (z.1 + t, z.2) * G (z.1, z.2 + t) / (t : ℂ)

def truncation (F G : Plane → ℂ) (E : Endpoints) (z : Plane) : ℂ :=
  ∫ t in annulus E.lower E.upper, integrand F G z t

def GoodPoint (F G : Plane → ℂ) (z : Plane) : Prop :=
  ∀ n : ℕ, IntegrableOn (integrand F G z)
    (annulus (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2))

def maximal (F G : Plane → ℂ) (z : Plane) : ℝ≥0∞ := by
  classical
  exact if GoodPoint F G z then
    ⨆ E : Endpoints, ENNReal.ofReal ‖truncation F G E z‖ else 0

def maximalNorm (F G : Plane → ℂ) : ℝ≥0∞ :=
  (∫⁻ z : Plane, maximal F G z ^ ((3 : ℝ) / 2)) ^ ((2 : ℝ) / 3)

def MainEstimate : Prop :=
  ∃ C : ℝ≥0, ∀ F G : Plane → ℂ,
    MemLp F 3 volume → MemLp G 3 volume →
    (∀ᵐ z ∂volume, GoodPoint F G z) ∧
    AEMeasurable (maximal F G) volume ∧
    maximalNorm F G ≤ (C : ℝ≥0∞) * eLpNorm F 3 volume * eLpNorm G 3 volume

open MeasureTheory Filter
open scoped ENNReal

def main_estimate_statement : Prop :=
  MainEstimate

end TriangularHilbert

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.TriangularHilbert.main_estimate_statement

end Problem

/- Formalization scope, from lean/docs/082.md: The formalized result proves the symmetric maximal estimate for the triangular Hilbert transform: for arbitrary complex $F,G\in L^3(\mathbb R^2)$, the $L^{3/2}$ norm of the supremum over all finite hard-truncation intervals is at most $C\|F\|_3\|G\|_3$ for one absolute constant $C$. It also establishes a common full-measure set on which the truncated integrals are defined and almost-everywhere measurability of the maximal output. -/
