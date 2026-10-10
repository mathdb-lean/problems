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

- problem_id: CubicTorus
- collection: openai-math
- question_id: openai-math:354
- source: openai-math
- source_locator: lean/ComparatorChallenges/CubicTorus.lean#OAI.CubicTorus.unit_cubic_isoperimetric
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Determines the isoperimetric profile of the unit cubic flat three-torus and classifies every finite-perimeter minimizer: balls, circular tubes around shortest closed geodesics, coordinate slabs, and their complements. The transition volumes are $`4\pi/81`$ and $`1/\pi`$, with exactly the adjacent two types minimizing at each transition. ([Lean](lean/docs/354.md)) We prove the isoperimetric conjecture for the cubic flat three-torus and classify all minimizers, including the equality cases at the transition volumes $`4\pi/81`$ and $`1/\pi`$. The minimizing regions are balls, circular tubes about shortest closed geodesics, coordinate slabs, and their complements.
- notes: OpenAI math result family 354, The isoperimetric profile of the cubic three-torus -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/354.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.CubicTorus.unit_cubic_isoperimetric
- source_theorem_count: 1
- source_solution_module: OAI.Geometry.CubicTorus.Main
- source_papers: preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf
- source_scope_note: lean/docs/354.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace CubicTorus

abbrev Cover := EuclideanSpace ℝ (Fin 3)
abbrev Torus := PiLp 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))

/-- The quotient R³ → R³/Z³ in orthonormal coordinates. -/
def quotientMap (x : Cover) : Torus :=
  WithLp.toLp 2 (fun i => (x i : AddCircle (1 : ℝ)))

/-- One unit-volume fundamental domain; its boundary is immaterial to integration. -/
def fundamentalCube : Set Cover := {x | ∀ i, 0 ≤ x i ∧ x i < 1}

/-- The Riemannian volume measure of the unit flat torus. -/
def torusVolume : Measure Torus :=
  Measure.map quotientMap (volume.restrict fundamentalCube)

/-- An integer lattice vector in the Euclidean cover. -/
def latticeVector (n : Fin 3 → ℤ) : Cover := WithLp.toLp 2 (fun i => (n i : ℝ))

/-- The smooth vector fields on the flat torus with pointwise length at most one,
expressed as Z³-periodic fields on its Euclidean cover. The explicit ℕ∞ index
is C^∞; top of WithTop ℕ∞ would instead mean analytic in this Mathlib. -/
def AdmissibleField (F : Cover → Cover) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) F ∧
  (∀ (n : Fin 3 → ℤ) (x : Cover), F (x + latticeVector n) = F x) ∧
  ∀ x, ‖F x‖ ≤ 1

/-- Euclidean divergence in the orthonormal coordinate frame. -/
def divergence (F : Cover → Cover) (x : Cover) : ℝ :=
  ∑ i : Fin 3, (fderiv ℝ F x (EuclideanSpace.single i 1)) i

/-- De Giorgi perimeter, allowed to be infinite; no regularity of E is imposed. -/
def perimeter (E : Set Torus) : ℝ≥0∞ :=
  ⨆ (F : Cover → Cover) (_ : AdmissibleField F),
    ENNReal.ofReal (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x)

/-- Finite-perimeter measurable regions, including all null-set modifications. -/
def FinitePerimeter (E : Set Torus) : Prop :=
  NullMeasurableSet E torusVolume ∧ perimeter E < ⊤

/-- A global perimeter minimizer under the prescribed volume constraint. -/
def IsMinimizerAt (V : ℝ) (E : Set Torus) : Prop :=
  FinitePerimeter E ∧ torusVolume E = ENNReal.ofReal V ∧
  ∀ F : Set Torus, FinitePerimeter F → torusVolume F = ENNReal.ofReal V →
    perimeter E ≤ perimeter F

/-- The candidate unit-torus isoperimetric profile. -/
def candidateProfile (V : ℝ) : ℝ :=
  let v := min V (1 - V)
  min ((36 * Real.pi) ^ (1 / 3 : ℝ) * v ^ (2 / 3 : ℝ))
    (min (2 * Real.sqrt (Real.pi * v)) 2)

/-- Canonical centered ball. Its radius on the listed branch is below 1/2. -/
def canonicalBall (V : ℝ) : Set Torus :=
  Metric.ball 0 ((3 * V / (4 * Real.pi)) ^ (1 / 3 : ℝ))

/-- Canonical tube around the shortest closed geodesic in coordinate direction 0. -/
def canonicalTube (V : ℝ) : Set Torus :=
  {x | ‖x 1‖ ^ 2 + ‖x 2‖ ^ 2 < (Real.sqrt (V / Real.pi)) ^ 2}

/-- Canonical slab of width V between two parallel coordinate tori. -/
def canonicalSlab (V : ℝ) : Set Torus := {x | ‖x 0‖ < V / 2}

/-- Equality of regions up to ambient flat isometry and a null set. -/
def CongruentAE (E F : Set Torus) : Prop :=
  ∃ φ : Torus ≃ᵢ Torus, E =ᵐ[torusVolume] (φ '' F)

/-- Exactly the closed phase ranges, so adjacent types are BOTH included at ties. -/
def SmallStandardRegion (V : ℝ) (E : Set Torus) : Prop :=
  (V ≤ 4 * Real.pi / 81 ∧ CongruentAE E (canonicalBall V)) ∨
  (4 * Real.pi / 81 ≤ V ∧ V ≤ 1 / Real.pi ∧ CongruentAE E (canonicalTube V)) ∨
  (1 / Real.pi ≤ V ∧ CongruentAE E (canonicalSlab V))

/-- The equality class at every interior volume, including complementation. -/
def StandardRegionAt (V : ℝ) (E : Set Torus) : Prop :=
  if V ≤ 1 / 2 then SmallStandardRegion V E
  else SmallStandardRegion (1 - V) Eᶜ

/-- Attainment, the sharp profile, and all equality cases at interior volumes. -/
def unit_cubic_isoperimetric_statement : Prop :=
  ∀ (V : ℝ) (hV : V ∈ Ioo 0 1),
    (∃ E : Set Torus, IsMinimizerAt V E) ∧
    (∀ E : Set Torus, IsMinimizerAt V E →
      perimeter E = ENNReal.ofReal (candidateProfile V)) ∧
    (∀ E : Set Torus, IsMinimizerAt V E ↔ StandardRegionAt V E)

end CubicTorus
end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.CubicTorus.unit_cubic_isoperimetric_statement

end Problem

/- Formalization scope, from lean/docs/354.md: The formalization determines the isoperimetric profile and all minimizers in the unit cubic flat three-torus. At every volume $0<V<1$, a minimizer exists, and the minimizers, up to null-set changes, are exactly balls, circular tubes about shortest closed geodesics, coordinate slabs, and their complements in the appropriate volume ranges. The classification includes all equality cases at the transition volumes $4\pi/81$ and $1/\pi$, and every minimizer has the stated candidate-profile perimeter. -/
