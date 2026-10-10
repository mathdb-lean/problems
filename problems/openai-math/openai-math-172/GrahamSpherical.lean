import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.InfiniteSum.Real
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

- problem_id: GrahamSpherical
- collection: openai-math
- question_id: openai-math:172
- source: openai-math
- source_locator: lean/ComparatorChallenges/GrahamSpherical.lean#OAI.GrahamSpherical.full_main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Classifies finite point configurations that occur monochromatically, at their original scale, in every finite coloring of sufficiently high-dimensional Euclidean space. The characterization is an algebraic condition over the coordinate field. It also disproves the Leader–Russell–Walters conjecture that every such configuration is a subset of a finite transitive set. ([Lean](lean/docs/172.md)) We classify finite Euclidean Ramsey configurations by a necessary and sufficient tensor condition over their coordinate fields. The Ramsey property here concerns monochromatic congruent copies at the original scale under arbitrary finite colorings. The criterion shows that every nonempty subtransitive set and every nonempty set of at most five points on a circle is Ramsey. In particular, some Ramsey cyclic quadrilaterals are not subtransitive, disproving the necessity direction of the Leader–Russell–Walters conjectured characterization.
- notes: OpenAI math result family 172, Classification of finite Euclidean Ramsey configurations -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/172.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.GrahamSpherical.full_main
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.SphericalRamsey.Main
- source_main_result: OAI.GrahamSpherical.full_main
- source_papers: preprints/A-classification-of-finite-Euclidean-Ramsey-configurations-September-23-2026/paper.pdf
- source_scope_note: lean/docs/172.md
- source_field: Combinatorics
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

namespace GrahamSpherical

abbrev Point (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Label := Fin 3 × Fin 4

def parameter : ℝ := ∑' m : ℕ, 1 / (10 : ℝ) ^ ((m + 1).factorial)

def u : ℝ := (1 - parameter ^ 2) / (1 + parameter ^ 2)
def v : ℝ := (2 * parameter) / (1 + parameter ^ 2)

def squareCoordinate (q : Fin 4) : Fin 2 → ℝ :=
  if q = 0 then ![1, 0] else
  if q = 1 then ![-1, 0] else
  if q = 2 then ![0, 1] else ![0, -1]

def coordinates (i : Label) : Fin 2 → ℝ :=
  let q := squareCoordinate i.2
  if i.1 = 0 then ![u * q 0 - v * q 1, v * q 0 + u * q 1] else
  if i.1 = 1 then ![u * q 0 + v * q 1, -v * q 0 + u * q 1] else q

def vertex (i : Label) : Point 2 := WithLp.toLp 2 (coordinates i)

def witness : Set (Point 2) := Set.range vertex

def AvoidsCopy {d n r : ℕ} (X : Set (Point d)) (color : Point n → Fin r) : Prop :=
  ¬ ∃ f : X → Point n, Isometry f ∧ ∃ c : Fin r, ∀ x, color (f x) = c

def EuclideanRamsey {d : ℕ} (X : Set (Point d)) : Prop :=
  ∀ r : ℕ, 0 < r → ∃ n : ℕ, 0 < n ∧
    ∀ color : Point n → Fin r,
      ∃ f : X → Point n, Isometry f ∧ ∃ c : Fin r, ∀ x, color (f x) = c

end GrahamSpherical

end

namespace GrahamSpherical.Specification

def FullAuthoredResult : Prop :=
  witness.ncard = 12 ∧
  witness ⊆ Metric.sphere (0 : Point 2) 1 ∧
  (∀ n : ℕ, 0 < n → ∃ color : Point n → Fin 50, AvoidsCopy witness color) ∧
  ¬ EuclideanRamsey witness

end GrahamSpherical.Specification

noncomputable section

namespace GrahamSpherical

def full_main_statement : Prop :=
  Specification.FullAuthoredResult

end GrahamSpherical

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.GrahamSpherical.full_main_statement

end Problem

/- Formalization scope, from lean/docs/172.md: A finite configuration is Euclidean Ramsey if every finite coloring of some sufficiently high-dimensional Euclidean space contains a monochromatic congruent copy at the original scale. The formalization gives the tensor-field classification for full-affine-span configurations, covers singleton and affine-span reductions, and proves that every Ramsey configuration is cospherical. It also proves that every nonempty subset of a finite transitive configuration and every nonempty set of at most five points on a circle is Ramsey. A further sufficient condition uses linear independence of the quadratic evaluation rows of a spherical configuration. The formalization also gives spherical non-Ramsey examples: the specified twelve-point set on the unit circle has a fifty-color obstruction in every positive dimension, and a nine-point circle configuration built from algebraically independent parameters is non-Ramsey. -/
