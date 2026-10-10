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

- problem_id: CrouzeixHilbert
- collection: openai-math
- question_id: openai-math:325
- source: openai-math
- source_locator: lean/ComparatorChallenges/CrouzeixHilbert.lean#OAI.CrouzeixHilbert.hilbert
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Resolves the complete Crouzeix conjecture: for every bounded operator A on a complex Hilbert space and every finite matrix-valued polynomial P, one has $`\lVert P[A]\rVert\le2\sup_{z\in W(A)}\lVert P(z)\rVert`$, where $`W(A)`$ is the numerical range. The constant 2 is sharp, independent of the matrix size, and valid in infinite dimensions. ([Lean](lean/docs/325.md)) We give a direct proof of the sharp constant-two numerical-range inequality for matrix-valued polynomials in all finite base and coefficient dimensions. This resolves the complete Crouzeix conjecture in its matrix formulation, including matrices whose numerical ranges are points or line segments. We resolve the complete Crouzeix conjecture by proving the sharp constant-two numerical-range inequality for every bounded operator on a complex Hilbert space and every matrix-valued polynomial. No separability assumption is needed. The closure of the numerical range is a complete 2-spectral set, and the bound extends to finite matrix-valued functions holomorphic near that closure. For a finite matrix and a bounded convex domain containing its numerical range with regular real-analytic Jordan boundary, the optimal similarity making its conformal disk image contractive is attained with condition number at most two. For the similar matrix, one continuous positive boundary density of mass the identity represents the evaluation of every matrix-valued function holomorphic near the closed domain.
- notes: OpenAI math result family 325, The complete Crouzeix conjecture -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/325.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.CrouzeixHilbert.hilbert
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.Crouzeix.Main
- source_papers: preprints/A-direct-proof-of-the-complete-Crouzeix-inequality-September-26-2026/paper.pdf preprints/The-complete-Crouzeix-theorem-September-23-2026/paper.pdf
- source_scope_note: lean/docs/325.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

/-! The sharp complete inequality for bounded operators on complex Hilbert spaces. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace
open Set

namespace CrouzeixHilbert

universe u

abbrev Operator (H : Type u) [NormedAddCommGroup H] [NormedSpace ℂ H] := H →L[ℂ] H
abbrev Coeff (m : ℕ) := Matrix (Fin m) (Fin m) ℂ

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def numericalRange (A : Operator H) : Set ℂ :=
  {z | ∃ x : H, ‖x‖ = 1 ∧ ⟪x, A x⟫_ℂ = z}

def numericalClosure (A : Operator H) : Set ℂ := closure (numericalRange A)

def supNorm {E : Type*} [NormedAddCommGroup E] (S : Set ℂ) (F : ℂ → E) : ℝ :=
  sSup (insert 0 ((fun z => ‖F z‖) '' S))

abbrev Amplification (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (m : ℕ) := UniformSpace.Completion (H ⊗[ℂ] EuclideanSpace ℂ (Fin m))

def tensorOperator (A : Operator H) {m : ℕ} (B : Coeff m) :
    Operator (Amplification H m) :=
  (TensorProduct.mapL A (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin m) B)).completion

def matrixPolynomial {m d : ℕ} (B : Fin (d + 1) → Coeff m) (z : ℂ) : Coeff m :=
  ∑ k : Fin (d + 1), z ^ (k : ℕ) • B k

def polynomialEval (A : Operator H) {m d : ℕ} (B : Fin (d + 1) → Coeff m) :
    Operator (Amplification H m) :=
  ∑ k : Fin (d + 1), tensorOperator (A ^ (k : ℕ)) (B k)

structure SmoothContour where
  path : ℝ → ℂ
  smooth : ContDiff ℝ 1 path
  closed : path 0 = path 1

def SmoothContour.index (Γ : SmoothContour) (z : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    ∫ t in (0 : ℝ)..1, deriv Γ.path t / (Γ.path t - z)

structure CalculusContour (K U : Set ℂ) extends SmoothContour where
  avoids : ∀ t ∈ Icc (0 : ℝ) 1, path t ∈ U \ K
  index_inside : ∀ z ∈ K, toSmoothContour.index z = 1
  index_outside : ∀ z ∉ U, toSmoothContour.index z = 0

def contourEval (A : Operator H) (Γ : SmoothContour) (f : ℂ → ℂ) : Operator H :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
    ∫ t in (0 : ℝ)..1, (deriv Γ.path t * f (Γ.path t)) •
      Ring.inverse (algebraMap ℂ (Operator H) (Γ.path t) - A)

def holomorphicEval (A : Operator H) (U : Set ℂ) (f : ℂ → ℂ) : Operator H := by
  classical
  exact if h : Nonempty (CalculusContour (numericalClosure A) U) then
    contourEval A (Classical.choice h).toSmoothContour f
  else 0

def matrixHolomorphicEval (A : Operator H) {m : ℕ} (U : Set ℂ)
    (F : ℂ → Coeff m) : Operator (Amplification H m) :=
  ∑ i, ∑ j, tensorOperator (holomorphicEval A U (fun z => F z i j))
    (Matrix.single i j 1)

def EntrywiseHolomorphic {m : ℕ} (U : Set ℂ) (F : ℂ → Coeff m) : Prop :=
  ∀ i j, DifferentiableOn ℂ (fun z => F z i j) U

abbrev RationalMatrix (m : ℕ) := Matrix (Fin m) (Fin m) (RatFunc ℂ)

def PolesOutside {m : ℕ} (K : Set ℂ) (R : RationalMatrix m) : Prop :=
  ∀ i j z, z ∈ K → (R i j).denom.eval z ≠ 0

def matrixRationalFunction {m : ℕ} (R : RationalMatrix m) (z : ℂ) : Coeff m :=
  fun i j => RatFunc.eval (RingHom.id ℂ) z (R i j)

def rationalEval (A : Operator H) (r : RatFunc ℂ) : Operator H :=
  (Polynomial.aeval A r.num) * Ring.inverse (Polynomial.aeval A r.denom)

def matrixRationalEval (A : Operator H) {m : ℕ} (R : RationalMatrix m) :
    Operator (Amplification H m) :=
  ∑ i, ∑ j, tensorOperator (rationalEval A (R i j)) (Matrix.single i j 1)

def NonzeroConclusion (A : Operator H) : Prop :=
  IsCompact (numericalClosure A) ∧
  Convex ℝ (numericalClosure A) ∧
  spectrum ℂ A ⊆ numericalClosure A ∧
  (∀ (m : ℕ), 0 < m → ∀ (d : ℕ) (B : Fin (d + 1) → Coeff m),
    ‖polynomialEval A B‖ ≤ 2 * supNorm (numericalRange A) (matrixPolynomial B) ∧
    supNorm (numericalRange A) (matrixPolynomial B) =
      supNorm (numericalClosure A) (matrixPolynomial B) ∧
    ∃ z ∈ numericalClosure A,
      supNorm (numericalClosure A) (matrixPolynomial B) = ‖matrixPolynomial B z‖) ∧
  (∀ (m : ℕ), 0 < m → ∀ (U : Set ℂ) (F : ℂ → Coeff m),
    IsOpen U → numericalClosure A ⊆ U → EntrywiseHolomorphic U F →
    Nonempty (CalculusContour (numericalClosure A) U) ∧
    (∀ Γ : CalculusContour (numericalClosure A) U, ∀ i j,
      holomorphicEval A U (fun z => F z i j) =
        contourEval A Γ.toSmoothContour (fun z => F z i j)) ∧
    ‖matrixHolomorphicEval A U F‖ ≤ 2 * supNorm (numericalClosure A) F ∧
    ∃ z ∈ numericalClosure A, supNorm (numericalClosure A) F = ‖F z‖) ∧
  (∀ (m : ℕ), 0 < m → ∀ (R : RationalMatrix m),
    PolesOutside (numericalClosure A) R →
    (∀ i j, IsUnit (Polynomial.aeval A (R i j).denom)) ∧
    ‖matrixRationalEval A R‖ ≤
      2 * supNorm (numericalClosure A) (matrixRationalFunction R) ∧
    (∃ z ∈ numericalClosure A,
      supNorm (numericalClosure A) (matrixRationalFunction R) =
        ‖matrixRationalFunction R z‖) ∧
    ∃ U : Set ℂ, IsOpen U ∧ numericalClosure A ⊆ U ∧
      EntrywiseHolomorphic U (matrixRationalFunction R) ∧
      matrixRationalEval A R = matrixHolomorphicEval A U (matrixRationalFunction R))

def ZeroConclusion (A : Operator H) : Prop :=
  numericalRange A = ∅ ∧
  (∀ (m d : ℕ) (B : Fin (d + 1) → Coeff m),
    polynomialEval A B = 0 ∧
    supNorm (numericalRange A) (matrixPolynomial B) = 0 ∧
    ‖polynomialEval A B‖ ≤ 2 * supNorm (numericalRange A) (matrixPolynomial B)) ∧
  (∀ (m : ℕ) (U : Set ℂ) (F : ℂ → Coeff m),
    matrixHolomorphicEval A U F = 0 ∧
    supNorm (numericalRange A) F = 0 ∧
    ‖matrixHolomorphicEval A U F‖ ≤ 2 * supNorm (numericalRange A) F) ∧
  (∀ (m : ℕ) (R : RationalMatrix m),
    matrixRationalEval A R = 0 ∧
    supNorm (numericalRange A) (matrixRationalFunction R) = 0 ∧
    ‖matrixRationalEval A R‖ ≤
      2 * supNorm (numericalRange A) (matrixRationalFunction R))

def SharpConstant : Prop :=
  ∃ (A : Operator (EuclideanSpace ℂ (Fin 2))) (B : Fin 2 → Coeff 1),
    supNorm (numericalRange A) (matrixPolynomial (d := 1) B) = 1 ∧
    ‖polynomialEval A (d := 1) B‖ = 2

end CrouzeixHilbert

namespace CrouzeixHilbert

universe u

def hilbert_statement : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (A : Operator H),
    (Nontrivial H → NonzeroConclusion A) ∧
    (Subsingleton H → ZeroConclusion A) ∧ SharpConstant

end CrouzeixHilbert

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u} : Prop :=
  _root_.OAI.CrouzeixHilbert.hilbert_statement.{u}

end Problem

/- Formalization scope, from lean/docs/325.md: The complete Crouzeix inequality bounds a matrix-valued polynomial evaluated at a matrix by its maximum norm on the numerical range. The formalized result proves the bound with constant $2$ for every positive matrix and coefficient size, every polynomial degree, and arbitrary complex coefficients. It also proves that no smaller universal constant works. Normality of the matrix and nonempty interior of its numerical range are not assumed. The formalization proves the complete Crouzeix inequality with sharp constant two for every bounded operator on an arbitrary complex Hilbert space. For every matrix-valued polynomial, its operator evaluation has norm at most twice its supremum norm on the numerical range. The same bound holds for finite matrix-valued functions holomorphic near the closure of the numerical range and for rational functions with poles outside that closure. No separability assumption is required. For finite matrices in a bounded convex domain with regular real-analytic Jordan boundary, the structural result gives an attained optimal similarity with condition number at most two and one continuous positive boundary density of mass the identity representing every matrix-valued analytic test. The linked supporting statements include numerical-range geometry and finite-compression identities. -/
