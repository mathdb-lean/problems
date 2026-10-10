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

- problem_id: HyperbolicCones
- collection: openai-math
- question_id: openai-math:095
- source: openai-math
- source_locator: lean/ComparatorChallenges/HyperbolicCones.lean#OAI.Paper256.main_result
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Disproves the Projected Lax conjecture: some hyperbolicity cones are not spectrahedral shadows. The examples admit no exact finite affine semidefinite lift, regardless of the number of auxiliary variables or the real coefficients used. This also disproves the generalized Lax conjecture that every hyperbolicity cone is spectrahedral. ([Lean](lean/docs/095.md)) We construct a homogeneous polynomial of degree 16 in 23 real variables whose hyperbolicity cone has no representation by a finite homogeneous real symmetric linear matrix inequality. This disproves the geometric Generalized Lax conjecture.
- notes: OpenAI math result family 095, Hyperbolicity cones without semidefinite lifts -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/095.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Paper256.main_result
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.HyperbolicCones.Main
- source_main_result: OAI.Paper256.main_result
- source_papers: preprints/A-Nonspectrahedral-Hyperbolicity-Cone-September-24-2026/nonspectrahedral-hyperbolicity-cone.pdf
- source_scope_note: lean/docs/095.md
- source_field: Analysis
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

open scoped Matrix.Norms.L2Operator

universe u

namespace Paper256

abbrev Mat (n : ℕ) (R : Type u) := Matrix (Fin n) (Fin n) R

abbrev Sym (n : ℕ) := selfAdjoint (Mat n ℝ)

instance instFiniteDimensionalSym (n : ℕ) : FiniteDimensional ℝ (Sym n) :=
  FiniteDimensional.finiteDimensional_submodule (selfAdjoint.submodule ℝ (Mat n ℝ))

abbrev Ambient := (Sym 4 × Sym 4) × (Fin 3 → ℝ)

abbrev SymIndex := {ij : Fin 4 × Fin 4 // ij.1 ≤ ij.2}

abbrev Coord := (SymIndex ⊕ SymIndex) ⊕ Fin 3

def qMatrix {R : Type u} [CommRing R] (y : Fin 3 → R) : Mat 3 R :=
  fun i j => if i = j then y i ^ 2 + y (i + 1) ^ 2 else -(y i * y j)

def phi {R : Type u} [CommRing R] (y : Fin 3 → R) (X : Mat 4 R) : Mat 4 R :=
  fun i j => Fin.cases
    (Fin.cases
      (Matrix.trace (qMatrix y * X.submatrix Fin.succ Fin.succ))
      (fun j => -(∑ k, X 0 k.succ * qMatrix y k j)) j)
    (fun i => Fin.cases
      (-(∑ k, qMatrix y i k * X k.succ 0))
      (fun j => X 0 0 * qMatrix y i j) j) i

def matrixValue {R : Type u} [CommRing R]
    (X Z : Mat 4 R) (y : Fin 3 → R) : R :=
  Matrix.det ((Matrix.det X) • Z - phi y (Matrix.adjugate X))

def symmetricCoordinates {R : Type u} (v : SymIndex → R) : Mat 4 R :=
  fun i j => if h : i ≤ j then v ⟨(i, j), h⟩
    else v ⟨(j, i), le_of_lt (lt_of_not_ge h)⟩

def polynomial : MvPolynomial Coord ℝ :=
  matrixValue
    (symmetricCoordinates fun ij => MvPolynomial.X (Sum.inl (Sum.inl ij)))
    (symmetricCoordinates fun ij => MvPolynomial.X (Sum.inl (Sum.inr ij)))
    (fun i => MvPolynomial.X (Sum.inr i))

def coordinates (x : Ambient) : Coord → ℝ :=
  Sum.elim (Sum.elim
    (fun ij => (x.1.1 : Mat 4 ℝ) ij.val.1 ij.val.2)
    (fun ij => (x.1.2 : Mat 4 ℝ) ij.val.1 ij.val.2)) x.2

def basePoint : Ambient := ((1, 1), 0)

def linePolynomial (x : Ambient) : Polynomial ℝ :=
  MvPolynomial.eval₂ Polynomial.C
    (fun i => Polynomial.C (coordinates basePoint i) * Polynomial.X -
      Polynomial.C (coordinates x i)) polynomial

def cone : Set Ambient :=
  {x | ∀ t : ℂ, (linePolynomial x).aeval t = 0 → t.im = 0 ∧ 0 ≤ t.re}

def main_result_statement : Prop :=
  Module.finrank ℝ Ambient = 23 ∧
    polynomial.IsHomogeneous 20 ∧
    polynomial.totalDegree = 20 ∧
    MvPolynomial.eval (coordinates basePoint) polynomial = 1 ∧
    (∀ (x : Ambient) (z : ℂ), (linePolynomial x).aeval z = 0 → z.im = 0) ∧
    ∀ (N : ℕ) (_hN : 0 < N) (L : Ambient →ₗ[ℝ] Sym N),
      cone ≠ {x | (L x : Mat N ℝ).PosSemidef}

end Paper256

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.Paper256.main_result_statement

end Problem

/- Formalization scope, from lean/docs/095.md: The generalized Lax conjecture predicts that every hyperbolicity cone is spectrahedral. The formalized counterexample is an explicit homogeneous polynomial of degree $20$ in $23$ real variables. It is hyperbolic, but its closed hyperbolicity cone cannot be represented as the positive-semidefinite region of any finite real symmetric linear matrix pencil, in any positive matrix size. -/
