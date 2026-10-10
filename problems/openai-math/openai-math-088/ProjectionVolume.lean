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

- problem_id: ProjectionVolume
- collection: openai-math
- question_id: openai-math:088
- source: openai-math
- source_locator: lean/ComparatorChallenges/ProjectionVolume.lean#OAI.Paper092.product_counterexample
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves Petty's projection-volume conjecture in the remaining dimensions n ≥ 4: ellipsoids uniquely minimize projection-body volume at fixed body volume. Also establishes the full Lutwak–Petty projection inequalities. In contrast, products of simplices exceed Brannen's proposed simplex maximum for normalized projection-body volume by an exponential factor in every sufficiently large dimension. ([Lean](lean/docs/088.md)) We prove that ellipsoids uniquely minimize the volume of the projection body among convex bodies of fixed volume in every dimension at least four. This proves Petty's projection-volume conjecture in these dimensions. The product of two ten-dimensional simplices has larger normalized projection-body volume than a twenty-dimensional simplex. This gives a counterexample to Brannen's proposed simplex maximum.
- notes: OpenAI math result family 088, Sharp projection-body inequalities and a counterexample to simplex maximization -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/088.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Paper092.product_counterexample
- source_theorem_count: 1
- source_solution_module: OAI.Geometry.ProjectionVolume.ProductCounterexample
- source_main_result: OAI.Paper092.product_counterexample
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
open scoped RealInnerProductSpace Pointwise

namespace Paper092

noncomputable def simplexConstant (d : ℕ) : ℝ :=
  (d + 1) * (d : ℝ) ^ d / d.factorial

abbrev Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)

def normalHyperplane {n : ℕ} (u : Euclidean n) : Submodule ℝ (Euclidean n) :=
  (Submodule.span ℝ ({u} : Set (Euclidean n)))ᗮ

def projectionVolume {n : ℕ} (K : Set (Euclidean n)) (u : Euclidean n) : ENNReal :=
  (volume : Measure (normalHyperplane u))
    ((normalHyperplane u).orthogonalProjectionOnto '' K)

def brightness {n : ℕ} (K : Set (Euclidean n)) (u : Euclidean n) : ℝ :=
  ‖u‖ * (projectionVolume K u).toReal

def projectionBody {n : ℕ} (K : Set (Euclidean n)) : Set (Euclidean n) :=
  {y | ∀ u, ⟪u, y⟫ ≤ brightness K u}

def normalizedProjectionVolume {n : ℕ} (K : Set (Euclidean n)) : ℝ :=
  (volume (projectionBody K)).toReal / (volume K).toReal ^ (n - 1)

def standardSimplex (n : ℕ) : Set (Euclidean n) :=
  convexHull ℝ (insert 0 (Set.range fun i : Fin n => EuclideanSpace.single i (1 : ℝ)))

def firstBlock (x : Euclidean 20) : Euclidean 10 :=
  WithLp.toLp 2 (fun i : Fin 10 => x (Fin.castAdd 10 i))

def secondBlock (x : Euclidean 20) : Euclidean 10 :=
  WithLp.toLp 2 (fun i : Fin 10 => x (Fin.natAdd 10 i))

def productWitness : Set (Euclidean 20) :=
  {x | firstBlock x ∈ standardSimplex 10 ∧ secondBlock x ∈ standardSimplex 10}

def product_counterexample_statement : Prop :=
  (IsCompact productWitness ∧ Convex ℝ productWitness ∧
      (interior productWitness).Nonempty) ∧
    normalizedProjectionVolume productWitness / simplexConstant 20 =
      (121 * (Nat.choose 20 10 : ℝ)) / (21 * (2 : ℝ) ^ 20) ∧
    normalizedProjectionVolume productWitness / simplexConstant 20 =
      (22355476 : ℝ) / 22020096 ∧
    1 < normalizedProjectionVolume productWitness / simplexConstant 20 ∧
    (volume (projectionBody productWitness)).toReal >
      simplexConstant 20 * (volume productWitness).toReal ^ 19

end Paper092

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.Paper092.product_counterexample_statement

end Problem

/- Formalization scope, from lean/docs/088.md: Petty's projection-volume conjecture predicts $\displaystyle \frac{|\Pi K|}{|K|^{n-1}}\ge \kappa_{n-1}^{n}\kappa_n^{2-n},$ with equality exactly for ellipsoids; here $\kappa_j$ is the volume of the Euclidean unit ball in dimension $j$. The formalization establishes this for every convex body $K\subset\mathbb R^n$ and every $n\ge4$. Other inequalities in the projection-body family are not included. Brannen's simplex-maximization conjecture predicts that a simplex maximizes normalized projection-body volume $|\Pi K|/|K|^{n-1}$ in dimension $n$. The formalized counterexample is the product of two ten-dimensional simplices. Its normalized projection volume, divided by that of a twenty-dimensional simplex, is $\displaystyle \frac{22{,}355{,}476}{22{,}020{,}096}>1.$ Thus the proposed maximum fails in dimension $20$. The paper's exponential-factor result for every sufficiently large dimension is not included. -/
