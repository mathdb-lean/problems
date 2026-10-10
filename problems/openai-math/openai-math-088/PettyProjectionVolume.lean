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

- problem_id: PettyProjectionVolume
- collection: openai-math
- question_id: openai-math:088
- source: openai-math
- source_locator: lean/ComparatorChallenges/PettyProjectionVolume.lean#OAI.PettyProjection.petty_projection_volume
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves Petty's projection-volume conjecture in the remaining dimensions n ≥ 4: ellipsoids uniquely minimize projection-body volume at fixed body volume. Also establishes the full Lutwak–Petty projection inequalities. In contrast, products of simplices exceed Brannen's proposed simplex maximum for normalized projection-body volume by an exponential factor in every sufficiently large dimension. ([Lean](lean/docs/088.md)) We prove that ellipsoids uniquely minimize the volume of the projection body among convex bodies of fixed volume in every dimension at least four. This proves Petty's projection-volume conjecture in these dimensions. The product of two ten-dimensional simplices has larger normalized projection-body volume than a twenty-dimensional simplex. This gives a counterexample to Brannen's proposed simplex maximum.
- notes: OpenAI math result family 088, Sharp projection-body inequalities and a counterexample to simplex maximization -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/088.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.PettyProjection.petty_projection_volume
- source_theorem_count: 1
- source_solution_module: OAI.Geometry.ProjectionBodies.Main
- source_main_result: OAI.PettyProjection.petty_projection_volume
- source_papers: preprints/Pettys-projection-volume-conjecture-in-dimensions-at-least-four-September-24-2026/paper.pdf preprints/A-product-counterexample-to-the-simplex-maximum-for-projection-body-volume-September-24-2026/paper.pdf
- source_scope_note: lean/docs/088.md
- source_field: Geometry
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace

namespace PettyProjection

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

def IsConvexBody {n : ℕ} (K : Set (Space n)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

def unitBall (n : ℕ) : Set (Space n) := Metric.closedBall 0 1

def kappa (n : ℕ) : ℝ := volume.real (unitBall n)

def perpendicular {n : ℕ} (u : Space n) : Submodule ℝ (Space n) :=
  (Submodule.span ℝ {u})ᗮ

/-- Volume in the induced Euclidean structure on the orthogonal hyperplane. -/
def shadowVolume {n : ℕ} (K : Set (Space n)) (u : Space n) : ℝ :=
  (volume : Measure (perpendicular u)).real
    ((perpendicular u).orthogonalProjectionOnto '' K)

/-- The body with support function equal to the volumes of orthogonal shadows,
expressed as its defining intersection of supporting half-spaces. -/
def projectionBody {n : ℕ} (K : Set (Space n)) : Set (Space n) :=
  {x | ∀ u : Space n, ‖u‖ = 1 → ⟪u, x⟫ ≤ shadowVolume K u}

def projectionRatio {n : ℕ} (K : Set (Space n)) : ℝ :=
  volume.real (projectionBody K) / volume.real K ^ (n - 1)

def pettyConstant (n : ℕ) : ℝ :=
  kappa (n - 1) ^ n * kappa n ^ (2 - (n : ℤ))

def IsEllipsoid {n : ℕ} (K : Set (Space n)) : Prop :=
  ∃ (a : Space n) (T : Space n ≃ₗ[ℝ] Space n),
    K = (fun x => a + T x) '' unitBall n

/-- The exact unrestricted inequality and its global equality characterization.
-/
def petty_projection_volume_statement : Prop :=
  ∀ (n : ℕ) (hn : 4 ≤ n) (K : Set (Space n)) (hK : IsConvexBody K),
    pettyConstant n ≤ projectionRatio K ∧
      (projectionRatio K = pettyConstant n ↔ IsEllipsoid K)

end PettyProjection
end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.PettyProjection.petty_projection_volume_statement

end Problem

/- Formalization scope, from lean/docs/088.md: Petty's projection-volume conjecture predicts $\displaystyle \frac{|\Pi K|}{|K|^{n-1}}\ge \kappa_{n-1}^{n}\kappa_n^{2-n},$ with equality exactly for ellipsoids; here $\kappa_j$ is the volume of the Euclidean unit ball in dimension $j$. The formalization establishes this for every convex body $K\subset\mathbb R^n$ and every $n\ge4$. Other inequalities in the projection-body family are not included. Brannen's simplex-maximization conjecture predicts that a simplex maximizes normalized projection-body volume $|\Pi K|/|K|^{n-1}$ in dimension $n$. The formalized counterexample is the product of two ten-dimensional simplices. Its normalized projection volume, divided by that of a twenty-dimensional simplex, is $\displaystyle \frac{22{,}355{,}476}{22{,}020{,}096}>1.$ Thus the proposed maximum fails in dimension $20$. The paper's exponential-factor result for every sufficiently large dimension is not included. -/
