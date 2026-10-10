import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Basic.Complex.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
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

- problem_id: AbhyankarSathaye
- collection: openai-math
- question_id: openai-math:049
- source: openai-math
- source_locator: lean/ComparatorChallenges/AbhyankarSathaye.lean#OAI.AbhyankarSathaye.exists_noncoordinate_polynomial
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs a polynomial in four complex variables that is not a coordinate but becomes one after adjoining a single variable, disproving the Stable Coordinate conjecture in four variables. Every fiber is affine three-space, yet none of its embeddings is rectifiable, also disproving the Abhyankar–Sathaye conjecture even when all fibers are affine spaces. ([Lean](lean/docs/049.md)) We construct an explicit counterexample to the Abhyankar–Sathaye conjecture: a noncoordinate polynomial in four complex variables whose zero fibre is affine three-space. Adjoining variables gives counterexamples in every ambient dimension at least four. We construct an explicit degree-five polynomial over $`\mathbf C`$ that is not a coordinate in four variables but becomes one after adjoining a single variable. This gives a counterexample to the stable coordinate conjecture in four variables. Every fiber is isomorphic to affine three-space, yet its embedding in affine four-space is not rectifiable. Thus the example also disproves the Abhyankar–Sathaye embedding conjecture in ambient dimension four.
- notes: OpenAI math result family 049, A stable-coordinate counterexample in four variables -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/049.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.AbhyankarSathaye.exists_noncoordinate_polynomial
- source_theorem_count: 1
- source_solution_module: OAI.AlgebraicGeometry.AbhyankarSathaye.Counterexample
- source_main_result: OAI.AbhyankarSathaye.exists_noncoordinate_polynomial
- source_papers: preprints/An-explicit-noncoordinate-polynomial-with-affine-three-space-zero-fibre-September-24-2026/paper.pdf preprints/A-stable-coordinate-that-is-not-a-coordinate-in-four-variables-October-5-2026/stable-coordinate-four-variables.pdf
- source_scope_note: lean/docs/049.md
- source_field: AlgebraicGeometry
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace AbhyankarSathaye

/-- In every dimension at least four, a polynomial can define affine space
without being a coordinate of the ambient polynomial ring. -/
def exists_noncoordinate_polynomial_statement : Prop :=
  ∀ (n : ℕ) (hn : 4 ≤ n),
    ∃ F : MvPolynomial (Fin n) ℂ,
      Nonempty ((MvPolynomial (Fin n) ℂ ⧸ Ideal.span {F}) ≃ₐ[ℂ]
        MvPolynomial (Fin (n - 1)) ℂ) ∧
      ¬ ∃ (equiv : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ)
        (index : Fin n), equiv (MvPolynomial.X index) = F

end AbhyankarSathaye

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.AbhyankarSathaye.exists_noncoordinate_polynomial_statement

end Problem

/- Formalization scope, from lean/docs/049.md: The stable coordinate conjecture predicts that a polynomial that becomes a coordinate after adjoining variables was already a coordinate. The formalization gives an explicit degree-five polynomial in four complex variables that becomes a coordinate after adjoining one variable but is not a coordinate in four variables. Every fiber is isomorphic to affine three-space, yet no fiber can be carried to a coordinate hyperplane by an ambient polynomial automorphism. The Abhyankar–Sathaye conjecture predicts that a polynomial defining an affine-space quotient must be an ambient coordinate. For every $n\ge4$, the formalized counterexample gives $F\in\mathbb C[x_1,\ldots,x_n]$ with quotient $\mathbb C[x_1,\ldots,x_n]/(F)\cong\mathbb C[y_1,\ldots,y_{n-1}]$, although $F$ is not a coordinate. A companion gives $n-1$ commuting, locally nilpotent derivations, linearly independent over the polynomial ring, whose common kernel is generated by the construction's explicit polynomial and contains no ambient coordinate. The extra $n-4$ derivations are ordinary partial derivatives in the added variables. The three-variable case is not covered. -/
