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

- problem_id: TriangularCovering
- collection: openai-math
- question_id: openai-math:100
- source: openai-math
- source_locator: lean/ComparatorChallenges/TriangularCovering.lean#OAI.TriangularCovering.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Covers the entire closed regular tetrahedron by finitely many cylinders with compact triangular perpendicular bases whose total area is less than half its smallest orthogonal projection area. This disproves Bang's half-area cylinder-covering bound and the stronger directionwise normalized conjecture in dimension three. ([Lean](lean/docs/100.md)) A regular tetrahedron admits a finite cylinder covering with compact triangular perpendicular bases whose total area is less than half its minimum orthogonal projection area. This disproves the half-area cylinder-covering conjecture. By affine invariance, the same construction gives a counterexample to the directionwise normalized half-bound for every nondegenerate tetrahedron. We approximate compact ruled families of segments by finitely many cylinders with square intercept tiles and perpendicular-base area at most their integral projection cost plus any positive error. The velocity field is C1, and its differential has opposite real eigenvalues whose magnitudes are strictly below the inverse segment half-length; both eigenvalues may vanish. The result includes square-zero differentials with unrestricted shear and fields that pass between the two regimes. It holds for arbitrary compact label sets. The two-cylinder covering of a regular tetrahedron can be perturbed to give finite covers with total perpendicular base area strictly below half its minimum projection area. These covers give negative answers to both the half-area question and the directionwise normalized half-bound conjecture. By affine invariance, the directionwise conclusion holds for every nondegenerate tetrahedron. We prove that radially aligned segment sweeps admit finite cylinder covers with one triangular base for each interval of any tagged partition. As the mesh tends to zero, the total perpendicular base area converges to a weighted parameter area. An explicit application covers every regular tetrahedron with total base area below half its minimum projection area, giving negative answers to the half-area question and the directionwise normalized 1-Codimensional Cylinder Covering Conjecture.
- notes: OpenAI math result family 100, Cylinder coverings below the half-area bound -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/100.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.TriangularCovering.main
- source_theorem_count: 1
- source_solution_module: OAI.Geometry.TriangularCovering.Main
- source_papers: preprints/Finite-angular-cylinder-covers-below-the-half-area-bound-September-27-2026/main.pdf preprints/Finite-cylinder-approximation-of-ruled-sets-September-27-2026/main.pdf preprints/Slope-field-perturbations-of-the-two-cylinder-covering-September-27-2026/main.pdf preprints/Finite-triangular-approximation-of-radial-sweeps-September-27-2026/main.pdf
- source_scope_note: lean/docs/100.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

abbrev Space := EuclideanSpace ℝ (Fin 3)

def H : ℝ := Real.sqrt 2

def point (x y t : ℝ) : Space := !₂[x, y, H * t]

def K : Set Space :=
  {z | ∃ x y t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ |x| ≤ 1 - t ∧ |y| ≤ t ∧ z = point x y t}

def projection (u z : Space) : Space := z - (inner ℝ u z) • u

def area (B : Set Space) : ℝ := (Measure.euclideanHausdorffMeasure 2 B).toReal

def shadowArea (u : Space) : ℝ := area (projection u '' K)

def A_min : ℝ := sInf {a : ℝ | ∃ u : Space, ‖u‖ = 1 ∧ a = shadowArea u}

structure TriCylinder where
  axis : Space
  base : Set Space
  unit_axis : ‖axis‖ = 1
  perpendicular : ∀ z ∈ base, inner ℝ axis z = 0
  triangular : ∃ v : Fin 3 → Space, AffineIndependent ℝ v ∧
    base = convexHull ℝ (Set.range v)
  compact : IsCompact base
  convex : Convex ℝ base
  measurable : MeasurableSet base
  finite_area : Measure.euclideanHausdorffMeasure 2 base ≠ ⊤

def TriCylinder.carrier (c : TriCylinder) : Set Space :=
  {z | ∃ b ∈ c.base, ∃ r : ℝ, z = b + r • c.axis}

def Covers {m : ℕ} (c : Fin m → TriCylinder) : Prop :=
  ∀ z ∈ K, ∃ i : Fin m, z ∈ (c i).carrier

def totalArea {m : ℕ} (c : Fin m → TriCylinder) : ℝ :=
  ∑ i : Fin m, area (c i).base

def relativeCost {m : ℕ} (c : Fin m → TriCylinder) : ℝ :=
  ∑ i : Fin m, area (c i).base / shadowArea (c i).axis

def n (ε : ℝ) : ℕ := ⌈2 / ε ^ 2⌉₊

def MainAsymptotic : Prop :=
  ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
    ∀ ε : ℝ, 0 < ε → ε < δ →
      ∃ c : Fin (2 * n ε) → TriCylinder,
        Covers c ∧
        |totalArea c / H - (1 / 2 - (13 / 6000 : ℝ) * ε ^ 2)| ≤ C * ε ^ 4 ∧
        totalArea c < A_min / 2

def NormalizedCounterexample : Prop :=
  ∃ m : ℕ, ∃ c : Fin m → TriCylinder, Covers c ∧ relativeCost c < 1 / 2

def main_statement : Prop :=
  A_min = H ∧ MainAsymptotic ∧ NormalizedCounterexample

end TriangularCovering

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.TriangularCovering.main_statement

end Problem

/- Formalization scope, from lean/docs/100.md: The half-area cylinder-covering conjecture predicts that a cylinder cover of a convex body has total perpendicular-base area at least half its smallest projection area. The formalization constructs finite covers of a regular tetrahedron by cylinders with compact triangular bases whose total area is strictly below that bound. For the explicit small parameter $\varepsilon$, the normalized area is $1/2-(13/6000)\varepsilon^2+O(\varepsilon^4)$, giving the strict saving. It also gives a counterexample to the directionwise normalized half-bound. The broader Comparator file includes the companion ruled-set and radial-sweep approximation results. The formalization approximates compact ruled families of line segments by finite cylinder covers with perpendicular-base area at most the integral projection cost plus any prescribed positive error. The selected results cover the stated $C^1$ hyperbolic differential condition, square-zero and nilpotent cases, physical rescalings, logarithmic and product-cell estimates, and singular cases. Compact label sets need not have regular boundary. The differential and segment-length hypotheses remain part of each result. The aggregate Comparator file also contains the companion tetrahedron counterexamples and radial-sweep estimates. The formalization proves that every regular tetrahedron has a finite cylinder cover whose total perpendicular-base area is strictly less than half its minimum projection area. It supplies covers with parallelogram bases and also proves the directionwise normalized cost is below one half. These are counterexamples to the two cylinder-covering bounds studied in the paper. The linked aggregate includes the accompanying explicit angular covers and finite approximation theorems for ruled sets and radial sweeps. The affine extension of the directionwise conclusion to every nondegenerate tetrahedron is outside the selected regular-tetrahedron statements. The formalization proves finite triangular-cylinder approximation for radially aligned segment sweeps. For every tagged partition of the parameter interval, it constructs one cylinder per interval with the prescribed radial direction, and the total perpendicular-base area converges to the weighted parameter area as the mesh tends to zero. It also covers the corresponding actual swept set under the stated geometric hypotheses. The same aggregate includes finite cylinder covers of regular tetrahedra below half the minimum projection area. These are the radial approximation and covering consequences relevant to the paper. -/
