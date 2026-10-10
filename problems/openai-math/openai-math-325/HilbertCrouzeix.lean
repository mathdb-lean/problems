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

- problem_id: HilbertCrouzeix
- collection: openai-math
- question_id: openai-math:325
- source: openai-math
- source_locator: lean/ComparatorChallenges/HilbertCrouzeix.lean#OAI.HilbertCrouzeix.numericalClosure_geometry
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Resolves the complete Crouzeix conjecture: for every bounded operator A on a complex Hilbert space and every finite matrix-valued polynomial P, one has $`\lVert P[A]\rVert\le2\sup_{z\in W(A)}\lVert P(z)\rVert`$, where $`W(A)`$ is the numerical range. The constant 2 is sharp, independent of the matrix size, and valid in infinite dimensions. ([Lean](lean/docs/325.md)) We give a direct proof of the sharp constant-two numerical-range inequality for matrix-valued polynomials in all finite base and coefficient dimensions. This resolves the complete Crouzeix conjecture in its matrix formulation, including matrices whose numerical ranges are points or line segments. We resolve the complete Crouzeix conjecture by proving the sharp constant-two numerical-range inequality for every bounded operator on a complex Hilbert space and every matrix-valued polynomial. No separability assumption is needed. The closure of the numerical range is a complete 2-spectral set, and the bound extends to finite matrix-valued functions holomorphic near that closure. For a finite matrix and a bounded convex domain containing its numerical range with regular real-analytic Jordan boundary, the optimal similarity making its conformal disk image contractive is attained with condition number at most two. For the similar matrix, one continuous positive boundary density of mass the identity represents the evaluation of every matrix-valued function holomorphic near the closed domain.
- notes: OpenAI math result family 325, The complete Crouzeix conjecture -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/325.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.HilbertCrouzeix.numericalClosure_geometry OAI.HilbertCrouzeix.exists_finite_compression OAI.HilbertCrouzeix.rational_denominator_isUnit OAI.HilbertCrouzeix.zeroConclusion
- source_theorem_count: 4
- source_solution_module: OAI.Analysis.HilbertCrouzeix.Main
- source_papers: preprints/A-direct-proof-of-the-complete-Crouzeix-inequality-September-26-2026/paper.pdf preprints/The-complete-Crouzeix-theorem-September-23-2026/paper.pdf
- source_scope_note: lean/docs/325.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

open Complex Set
open scoped TensorProduct Matrix.Norms.L2Operator Classical ComplexConjugate

namespace HilbertCrouzeix

universe u

abbrev Coeff (m : ℕ) := Matrix (Fin m) (Fin m) ℂ
abbrev CoeffSpace (m : ℕ) := EuclideanSpace ℂ (Fin m)

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def numericalRange (A : H →L[ℂ] H) : Set ℂ :=
  {z | ∃ x : H, ‖x‖ = 1 ∧ inner ℂ x (A x) = z}

def numericalClosure (A : H →L[ℂ] H) : Set ℂ := closure (numericalRange A)

abbrev Amplification (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (m : ℕ) := UniformSpace.Completion (H ⊗[ℂ] CoeffSpace m)

def tensorOp {m : ℕ} (A : H →L[ℂ] H) (B : Coeff m) :
    Amplification H m →L[ℂ] Amplification H m :=
  (TensorProduct.mapL A (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℂ) B)).completion

def matrixPolynomial {m d : ℕ} (B : Fin (d + 1) → Coeff m) (z : ℂ) : Coeff m :=
  ∑ k : Fin (d + 1), z ^ k.val • B k

def polynomialEval {m d : ℕ} (A : H →L[ℂ] H) (B : Fin (d + 1) → Coeff m) :
    Amplification H m →L[ℂ] Amplification H m :=
  ∑ k : Fin (d + 1), tensorOp (A ^ k.val) (B k)

def normSup {E : Type*} [Norm E] (S : Set ℂ) (f : ℂ → E) : ℝ :=
  if S.Nonempty then sSup ((fun z => ‖f z‖) '' S) else 0
def contourIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (γ : ℝ → ℂ) (f : ℂ → E) : E :=
  ∫ t : ℝ in (0 : ℝ)..1, deriv γ t • f (γ t)

def contourIndex (γ : ℝ → ℂ) (z : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * contourIntegral γ (fun w => (w - z)⁻¹)

def IsCauchyContour (K U : Set ℂ) (γ : ℝ → ℂ) : Prop :=
  ContDiff ℝ 1 γ ∧ γ 0 = γ 1 ∧
  (∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ U \ K) ∧
  (∀ z ∈ K, contourIndex γ z = 1) ∧
  (∀ z ∉ U, contourIndex γ z = 0)

def chosenContour (K U : Set ℂ) : ℝ → ℂ :=
  Classical.epsilon (IsCauchyContour K U)

variable [CompleteSpace H]

def dunfordIntegral (A : H →L[ℂ] H) (γ : ℝ → ℂ) (f : ℂ → ℂ) : H →L[ℂ] H :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
    contourIntegral γ (fun z => f z • resolvent A z)

def holomorphicCalculus (A : H →L[ℂ] H) (U : Set ℂ) (f : ℂ → ℂ) : H →L[ℂ] H :=
  dunfordIntegral A (chosenContour (numericalClosure A) U) f

def matrixUnit {m : ℕ} (i j : Fin m) : Coeff m := Matrix.single i j 1

def holomorphicEval {m : ℕ} (A : H →L[ℂ] H) (U : Set ℂ) (F : ℂ → Coeff m) :
    Amplification H m →L[ℂ] Amplification H m :=
  ∑ i : Fin m, ∑ j : Fin m,
    tensorOp (holomorphicCalculus A U (fun z => F z i j)) (matrixUnit i j)
abbrev RationalMatrix (m : ℕ) := Matrix (Fin m) (Fin m) (RatFunc ℂ)

def poleFreeSet {m : ℕ} (R : RationalMatrix m) : Set ℂ :=
  {z | ∀ i j, (R i j).denom.eval z ≠ 0}

def rationalFunction {m : ℕ} (R : RationalMatrix m) (z : ℂ) : Coeff m :=
  fun i j => RatFunc.eval (RingHom.id ℂ) z (R i j)

def rationalCalculus (A : H →L[ℂ] H) (r : RatFunc ℂ) : H →L[ℂ] H :=
  Polynomial.aeval A r.num * Ring.inverse (Polynomial.aeval A r.denom)

def rationalEval {m : ℕ} (A : H →L[ℂ] H) (R : RationalMatrix m) :
    Amplification H m →L[ℂ] Amplification H m :=
  ∑ i : Fin m, ∑ j : Fin m, tensorOp (rationalCalculus A (R i j)) (matrixUnit i j)
def ZeroConclusion (A : H →L[ℂ] H) : Prop :=
  numericalRange A = ∅ ∧
  (∀ (m : ℕ) (F : ℂ → Coeff m), normSup (numericalRange A) F = 0) ∧
  ∀ (m : ℕ), 0 < m →
    (∀ T : Amplification H m →L[ℂ] Amplification H m, T = 0) ∧
    (∀ (d : ℕ) (B : Fin (d + 1) → Coeff m), polynomialEval A B = 0 ∧
      ‖polynomialEval A B‖ ≤ 2 * normSup (numericalRange A) (matrixPolynomial B)) ∧
    (∀ (U : Set ℂ) (F : ℂ → Coeff m), holomorphicEval A U F = 0 ∧
      ‖holomorphicEval A U F‖ ≤ 2 * normSup (numericalRange A) F) ∧
    (∀ (R : RationalMatrix m), rationalEval A R = 0 ∧
      ‖rationalEval A R‖ ≤ 2 * normSup (numericalRange A) (rationalFunction R))

section CompressionDefinitions
omit [CompleteSpace H]

def compression (A : H →L[ℂ] H) (E : Submodule ℂ H) [E.HasOrthogonalProjection] :
    E →L[ℂ] E := E.orthogonalProjectionOnto.comp (A.comp E.subtypeL)
def completedIsometry {V : Type*} {W : Type*}
    [NormedAddCommGroup V] [NormedAddCommGroup W] [NormedSpace ℂ V] [NormedSpace ℂ W]
    (f : V →ₗᵢ[ℂ] W) : UniformSpace.Completion V →ₗᵢ[ℂ] UniformSpace.Completion W :=
  { f.toContinuousLinearMap.completion.toLinearMap with
    norm_map' := f.isometry.completion_map.norm_map_of_map_zero
      (f.toContinuousLinearMap.completion.map_zero) }

def tensorInclusion (E : Submodule ℂ H) (m : ℕ) :
    Amplification E m →ₗᵢ[ℂ] Amplification H m :=
  completedIsometry (TensorProduct.mapIsometry E.subtypeₗᵢ (.id : CoeffSpace m →ₗᵢ[ℂ] CoeffSpace m))

end CompressionDefinitions

def numericalClosure_geometry_statement : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →L[ℂ] H),
    IsCompact (numericalClosure A) ∧ Convex ℝ (numericalClosure A) ∧
      spectrum ℂ A ⊆ numericalClosure A

omit [CompleteSpace H] in
def exists_finite_compression_statement : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {m d : ℕ} (A : H →L[ℂ] H) (B : Fin (d + 1) → Coeff m) (ξ : H ⊗[ℂ] CoeffSpace m),
    ∃ (E : Submodule ℂ H) (hE : FiniteDimensional ℂ E),
      letI : FiniteDimensional ℂ E := hE
      ∃ η : Amplification E m,
        tensorInclusion E m η = (↑ξ : Amplification H m) ∧
        tensorInclusion E m (polynomialEval (compression A E) B η) =
          polynomialEval A B (↑ξ)

def rational_denominator_isUnit_statement : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H] (A : H →L[ℂ] H) {m : ℕ} (R : RationalMatrix m) (hR : numericalClosure A ⊆ poleFreeSet R) (i j : Fin m),
    IsUnit (Polynomial.aeval A (R i j).denom)

def zeroConclusion_statement : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Subsingleton H] (A : H →L[ℂ] H),
    ZeroConclusion A

end HilbertCrouzeix

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u} : Prop :=
  _root_.OAI.HilbertCrouzeix.numericalClosure_geometry_statement.{u} ∧
  _root_.OAI.HilbertCrouzeix.exists_finite_compression_statement.{u} ∧
  _root_.OAI.HilbertCrouzeix.rational_denominator_isUnit_statement.{u} ∧
  _root_.OAI.HilbertCrouzeix.zeroConclusion_statement.{u}

end Problem

/- Formalization scope, from lean/docs/325.md: The complete Crouzeix inequality bounds a matrix-valued polynomial evaluated at a matrix by its maximum norm on the numerical range. The formalized result proves the bound with constant $2$ for every positive matrix and coefficient size, every polynomial degree, and arbitrary complex coefficients. It also proves that no smaller universal constant works. Normality of the matrix and nonempty interior of its numerical range are not assumed. The formalization proves the complete Crouzeix inequality with sharp constant two for every bounded operator on an arbitrary complex Hilbert space. For every matrix-valued polynomial, its operator evaluation has norm at most twice its supremum norm on the numerical range. The same bound holds for finite matrix-valued functions holomorphic near the closure of the numerical range and for rational functions with poles outside that closure. No separability assumption is required. For finite matrices in a bounded convex domain with regular real-analytic Jordan boundary, the structural result gives an attained optimal similarity with condition number at most two and one continuous positive boundary density of mass the identity representing every matrix-valued analytic test. The linked supporting statements include numerical-range geometry and finite-compression identities. -/
