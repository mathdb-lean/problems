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

- problem_id: PermanentCubic
- collection: openai-math
- question_id: openai-math:108
- source: openai-math
- source_locator: lean/ComparatorChallenges/PermanentCubic.lean#OAI.PermanentBorder.permanent_cubic_lower_bounds
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves an $`\Omega(n^3)`$ lower bound for the border determinantal complexity of the $`n\times n`$ permanent over ℂ. Even coefficientwise limits of determinants of affine-linear matrices require matrix size at least $`cn^3`$, for an absolute c &gt; 0 and all sufficiently large n; the same bound therefore holds for exact representations. ([Lean](lean/docs/108.md)) We prove that the complex border determinantal complexity of the $`m\times m`$ permanent is $`\Omega(m^3)`$, allowing arbitrary affine-linear determinant representations and coefficientwise limits. It also gives cubic lower bounds for exact determinantal complexity and for the numbers of vertices and edges in affine-linear algebraic branching programs, including coefficientwise limits with a fixed vertex or edge budget.
- notes: OpenAI math result family 108, A cubic permanent–determinant lower bound -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/108.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.PermanentBorder.permanent_cubic_lower_bounds
- source_theorem_count: 1
- source_solution_module: OAI.Algebra.Determinantal.Main
- source_papers: preprints/A-cubic-lower-bound-for-border-determinantal-complexity-of-the-permanent-September-24-2026/A-cubic-lower-bound-for-border-determinantal-complexity-of-the-permanent-September-24-2026.pdf
- source_scope_note: lean/docs/108.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace PermanentBorder

open Filter
open scoped Topology

abbrev Variables (m : ℕ) := Fin m × Fin m
abbrev Poly (σ : Type*) := MvPolynomial σ ℂ

noncomputable def permanentPolynomial (m : ℕ) : Poly (Variables m) :=
  ∑ τ : Equiv.Perm (Fin m), ∏ i : Fin m, MvPolynomial.X (i, τ i)

noncomputable def affineMatrixPolynomial {σ : Type*} [Fintype σ] (n : ℕ)
    (A₀ : Matrix (Fin n) (Fin n) ℂ)
    (A : σ → Matrix (Fin n) (Fin n) ℂ) : Poly σ :=
  Matrix.det (fun i j => MvPolynomial.C (A₀ i j) +
    ∑ v : σ, MvPolynomial.C (A v i j) * MvPolynomial.X v)

def HasBorderDeterminant {σ : Type*} [Fintype σ] (n : ℕ) (p : Poly σ) : Prop :=
  0 < n ∧ ∃ (A₀ : ℕ → Matrix (Fin n) (Fin n) ℂ)
    (A : ℕ → σ → Matrix (Fin n) (Fin n) ℂ),
    ∀ d : σ →₀ ℕ, Tendsto
      (fun j => (affineMatrixPolynomial n (A₀ j) (A j)).coeff d)
      atTop (𝓝 (p.coeff d))

def HasExactDeterminant {σ : Type*} [Fintype σ] (n : ℕ) (p : Poly σ) : Prop :=
  0 < n ∧ ∃ (A₀ : Matrix (Fin n) (Fin n) ℂ)
    (A : σ → Matrix (Fin n) (Fin n) ℂ), affineMatrixPolynomial n A₀ A = p

def permanent_cubic_lower_bounds_statement : Prop :=
  (∀ (m n : ℕ), 1408 ≤ m → HasBorderDeterminant n (permanentPolynomial m) →
      (m : ℝ)^3 / (5529600 * Real.exp 1) ≤ (n : ℝ)) ∧
    (∀ (m n : ℕ), 1408 ≤ m → HasExactDeterminant n (permanentPolynomial m) →
      (m : ℝ)^3 / (5529600 * Real.exp 1) ≤ (n : ℝ))

end PermanentBorder

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.PermanentBorder.permanent_cubic_lower_bounds_statement

end Problem

/- Formalization scope, from lean/docs/108.md: The formalization proves a cubic lower bound for both exact and border determinantal representations of the complex $m\times m$ permanent. For $m\ge1408$, every affine-linear determinant representation of size $n$, including coefficientwise limits, satisfies $n\ge m^3/(5529600e)$. A general supporting theorem applies to a polynomial in $d\ge2$ variables whose first nonzero homogeneous Taylor term has degree $r\ge2$ and no nonzero singular zero. Its exact and border determinantal sizes are at least $(r-1)(d-1)/(4e)$. The paper's algebraic-branching-program consequences are outside these statements. -/
