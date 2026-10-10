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

- problem_id: CompleteCrouzeix
- collection: openai-math
- question_id: openai-math:325
- source: openai-math
- source_locator: lean/ComparatorChallenges/CompleteCrouzeix.lean#OAI.CompleteCrouzeix.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Resolves the complete Crouzeix conjecture: for every bounded operator A on a complex Hilbert space and every finite matrix-valued polynomial P, one has $`\lVert P[A]\rVert\le2\sup_{z\in W(A)}\lVert P(z)\rVert`$, where $`W(A)`$ is the numerical range. The constant 2 is sharp, independent of the matrix size, and valid in infinite dimensions. ([Lean](lean/docs/325.md)) We give a direct proof of the sharp constant-two numerical-range inequality for matrix-valued polynomials in all finite base and coefficient dimensions. This resolves the complete Crouzeix conjecture in its matrix formulation, including matrices whose numerical ranges are points or line segments. We resolve the complete Crouzeix conjecture by proving the sharp constant-two numerical-range inequality for every bounded operator on a complex Hilbert space and every matrix-valued polynomial. No separability assumption is needed. The closure of the numerical range is a complete 2-spectral set, and the bound extends to finite matrix-valued functions holomorphic near that closure. For a finite matrix and a bounded convex domain containing its numerical range with regular real-analytic Jordan boundary, the optimal similarity making its conformal disk image contractive is attained with condition number at most two. For the similar matrix, one continuous positive boundary density of mass the identity represents the evaluation of every matrix-valued function holomorphic near the closed domain.
- notes: OpenAI math result family 325, The complete Crouzeix conjecture -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/325.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.CompleteCrouzeix.main
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.NumericalRange.Main
- source_main_result: OAI.CompleteCrouzeix.main
- source_papers: preprints/A-direct-proof-of-the-complete-Crouzeix-inequality-September-26-2026/paper.pdf preprints/The-complete-Crouzeix-theorem-September-23-2026/paper.pdf
- source_scope_note: lean/docs/325.md
- source_field: Analysis
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace CompleteCrouzeix

def numericalRange {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Set ℂ :=
  {z | ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧
    inner ℂ x (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A x) = z}

def polynomialValue {m d : ℕ} (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ)
    (z : ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  ∑ k : Fin (d + 1), (z ^ (k : ℕ)) • B k

def polynomialAt {n m d : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ :=
  ∑ k : Fin (d + 1), Matrix.kronecker (A ^ (k : ℕ)) (B k)

def rangeMaximum {n m d : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  sSup ((fun z => ‖polynomialValue B z‖) '' numericalRange A)

def UniversalBound (C : ℝ) : Prop :=
  ∀ (n m d : ℕ), 0 < n → 0 < m →
    ∀ (A : Matrix (Fin n) (Fin n) ℂ)
      (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ),
      ‖polynomialAt A B‖ ≤ C * rangeMaximum A B

def main_statement : Prop :=
  UniversalBound 2 ∧ ∀ C : ℝ, UniversalBound C → 2 ≤ C

end CompleteCrouzeix
end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.CompleteCrouzeix.main_statement

end Problem

/- Formalization scope, from lean/docs/325.md: The complete Crouzeix inequality bounds a matrix-valued polynomial evaluated at a matrix by its maximum norm on the numerical range. The formalized result proves the bound with constant $2$ for every positive matrix and coefficient size, every polynomial degree, and arbitrary complex coefficients. It also proves that no smaller universal constant works. Normality of the matrix and nonempty interior of its numerical range are not assumed. The formalization proves the complete Crouzeix inequality with sharp constant two for every bounded operator on an arbitrary complex Hilbert space. For every matrix-valued polynomial, its operator evaluation has norm at most twice its supremum norm on the numerical range. The same bound holds for finite matrix-valued functions holomorphic near the closure of the numerical range and for rational functions with poles outside that closure. No separability assumption is required. For finite matrices in a bounded convex domain with regular real-analytic Jordan boundary, the structural result gives an attained optimal similarity with condition number at most two and one continuous positive boundary density of mass the identity representing every matrix-valued analytic test. The linked supporting statements include numerical-range geometry and finite-compression identities. -/
