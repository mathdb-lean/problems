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

- problem_id: ComplexCancellation
- collection: openai-math
- question_id: openai-math:047
- source: openai-math
- source_locator: lean/ComparatorChallenges/ComplexCancellation.lean#OAI.ComplexCancellation.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs an integral complex affine fourfold $`X\not\cong\mathbb A^4`$ with $`X\times\mathbb A^1\cong\mathbb A^5`$, disproving affine-space cancellation over ℂ in dimension four. It also disproves the Dolgachev–Weisfeiler affine-fibration conjecture: smooth surjections $`X\to\mathbb A^1`$ and $`\mathbb A^5\to\mathbb A^2`$ have every residue-field fiber isomorphic to affine three-space but are not Zariski-locally trivial. ([Lean](lean/docs/047.md)) We construct an explicit integral complex affine fourfold X with $`X\times\mathbb A^1\cong\mathbb A^5`$ but $`X\not\cong\mathbb A^4`$. This gives a negative answer to Zariski's affine-space cancellation problem over ℂ in dimension four. The same construction disproves the Stable Coordinate Conjecture in ambient dimension five and yields smooth 𝔸3-fibrations over 𝔸1 and 𝔸2 that are not Zariski-locally trivial. These fibrations disprove the Dolgachev–Weisfeiler affine-fibration conjecture over these bases.
- notes: OpenAI math result family 047, Zariski cancellation and affine fibrations over the complex numbers -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/047.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.ComplexCancellation.main
- source_theorem_count: 1
- source_solution_module: OAI.Algebra.AffineCancellation.Main
- source_main_result: OAI.ComplexCancellation.main
- source_papers: preprints/An-explicit-failure-of-complex-affine-space-cancellation-September-23-2026/paper.pdf
- source_scope_note: lean/docs/047.md
- source_field: Algebra
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

namespace ComplexCancellation

abbrev P := MvPolynomial (Fin 5) ℂ

def p : P := MvPolynomial.X 0
def s : P := MvPolynomial.X 1
def u : P := MvPolynomial.X 2
def F : P := MvPolynomial.X 3
def J : P := MvPolynomial.X 4
def x : P := s ^ 2 + u ^ 3 + p ^ 2 * F
def H : P := x ^ 2 * F - (1 + 2 * s * x) * J - p ^ 2 * J ^ 2 - p * u
abbrev A := P ⧸ Ideal.span {H}

def MainStatement : Prop :=
  Algebra.FiniteType ℂ A ∧ IsDomain A ∧ ringKrullDim A = 4 ∧
  Nonempty (Polynomial A ≃ₐ[ℂ] MvPolynomial (Fin 5) ℂ) ∧
  ¬ Nonempty (A ≃ₐ[ℂ] MvPolynomial (Fin 4) ℂ)

def main_statement : Prop :=
  MainStatement

end ComplexCancellation

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.ComplexCancellation.main_statement

end Problem

/- Formalization scope, from lean/docs/047.md: Affine-space cancellation asks whether $X\times\mathbb A^1\cong\mathbb A^{n+1}$ forces $X\cong\mathbb A^n$. The formalized result gives an explicit finite-type complex domain $A$ of Krull dimension four with $A[w]\cong\mathbb C[x_1,\ldots,x_5]$ but $A\not\cong\mathbb C[x_1,\ldots,x_4]$. Thus adjoining one variable erases a genuine algebraic distinction. The separate stable-coordinate and general line-bundle lifting consequences are not included. -/
