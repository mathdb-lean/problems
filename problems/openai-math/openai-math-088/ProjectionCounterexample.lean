import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Geometry.Euclidean.Volume.Measure
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

- problem_id: ProjectionCounterexample
- collection: openai-math
- question_id: openai-math:088
- source: openai-math
- source_locator: lean/ComparatorChallenges/ProjectionCounterexample.lean#OAI.ProjectionCounterexample.universal_simplex_upper_bound_false
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves Petty's projection-volume conjecture in the remaining dimensions n ≥ 4: ellipsoids uniquely minimize projection-body volume at fixed body volume. Also establishes the full Lutwak–Petty projection inequalities. In contrast, products of simplices exceed Brannen's proposed simplex maximum for normalized projection-body volume by an exponential factor in every sufficiently large dimension. ([Lean](lean/docs/088.md)) We prove that ellipsoids uniquely minimize the volume of the projection body among convex bodies of fixed volume in every dimension at least four. This proves Petty's projection-volume conjecture in these dimensions. The product of two ten-dimensional simplices has larger normalized projection-body volume than a twenty-dimensional simplex. This gives a counterexample to Brannen's proposed simplex maximum.
- notes: OpenAI math result family 088, Sharp projection-body inequalities and a counterexample to simplex maximization -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/088.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.ProjectionCounterexample.universal_simplex_upper_bound_false
- source_theorem_count: 1
- source_solution_module: OAI.Geometry.ProjectionBody.Counterexample
- source_main_result: OAI.ProjectionCounterexample.universal_simplex_upper_bound_false
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

namespace ProjectionCounterexample

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

def simplex (d : ℕ) : Set (E d) :=
  convexHull ℝ (insert 0 (range fun i : Fin d => EuclideanSpace.single i (1 : ℝ)))

def IsConvexBody {d : ℕ} (P : Set (E d)) : Prop :=
  IsCompact P ∧ Convex ℝ P ∧ (interior P).Nonempty

def project {d : ℕ} (u : E d) : E d →L[ℝ] E d :=
  (ℝ ∙ u)ᗮ.starProjection

def projectionVolume {d : ℕ} (P : Set (E d)) (u : E d) : ℝ :=
  (Measure.euclideanHausdorffMeasure (d - 1) (project u '' P)).toReal

def projectionBody {d : ℕ} (P : Set (E d)) : Set (E d) :=
  {x | ∀ u : E d, ‖u‖ = 1 → ⟪u, x⟫ ≤ projectionVolume P u}

def bodyVolume {d : ℕ} (P : Set (E d)) : ℝ := (volume P).toReal

def ratio {d : ℕ} (P : Set (E d)) : ℝ :=
  bodyVolume (projectionBody P) / bodyVolume P ^ (d - 1)

def universal_simplex_upper_bound_false_statement : Prop :=
  ¬ (∀ P : Set (E 20), IsConvexBody P → ratio P ≤ ratio (simplex 20))

end ProjectionCounterexample

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.ProjectionCounterexample.universal_simplex_upper_bound_false_statement

end Problem

/- Formalization scope, from lean/docs/088.md: Petty's projection-volume conjecture predicts $\displaystyle \frac{|\Pi K|}{|K|^{n-1}}\ge \kappa_{n-1}^{n}\kappa_n^{2-n},$ with equality exactly for ellipsoids; here $\kappa_j$ is the volume of the Euclidean unit ball in dimension $j$. The formalization establishes this for every convex body $K\subset\mathbb R^n$ and every $n\ge4$. Other inequalities in the projection-body family are not included. Brannen's simplex-maximization conjecture predicts that a simplex maximizes normalized projection-body volume $|\Pi K|/|K|^{n-1}$ in dimension $n$. The formalized counterexample is the product of two ten-dimensional simplices. Its normalized projection volume, divided by that of a twenty-dimensional simplex, is $\displaystyle \frac{22{,}355{,}476}{22{,}020{,}096}>1.$ Thus the proposed maximum fails in dimension $20$. The paper's exponential-factor result for every sufficiently large dimension is not included. -/
