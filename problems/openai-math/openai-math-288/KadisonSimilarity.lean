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

- problem_id: KadisonSimilarity
- collection: openai-math
- question_id: openai-math:288
- source: openai-math
- source_locator: lean/ComparatorChallenges/KadisonSimilarity.lean#OAI.KadisonSimilarity.universalCommutatorTheorem
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves Kadison's similarity conjecture: every bounded complex-linear unital algebra homomorphism from a unital complex C∗-algebra to operators on a Hilbert space becomes a $`*`$-homomorphism after conjugation by a bounded invertible operator. ([Lean](lean/docs/288.md)) We prove that every bounded complex-linear unital algebra homomorphism from a unital complex C∗-algebra into the bounded operators on an arbitrary Hilbert space is similar to a $`*`$-homomorphism. This resolves Kadison's similarity conjecture positively. We also obtain one universal hyperreflexivity constant for all unital von Neumann algebras on arbitrary complex Hilbert spaces.
- notes: OpenAI math result family 288, Kadison's similarity conjecture -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/288.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.KadisonSimilarity.universalCommutatorTheorem OAI.KadisonSimilarity.universalHyperreflexivity OAI.KadisonSimilarity.similarityTheorem
- source_theorem_count: 3
- source_solution_module: OAI.Analysis.KadisonSimilarity.UnconditionalSimilarity
- source_papers: preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf
- source_scope_note: lean/docs/288.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

namespace KadisonSimilarity

universe u v

section Homomorphisms

variable (A H : Type*) [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev BoundedUnitalHom :=
  {π : A →ₐ[ℂ] (H →L[ℂ] H) // Continuous π}

def SimilarToStar (π : BoundedUnitalHom A H) : Prop :=
  ∃ S : (H →L[ℂ] H)ˣ, ∀ a : A,
    (S : H →L[ℂ] H) * π.1 (star a) * (↑S⁻¹ : H →L[ℂ] H) =
      star ((S : H →L[ℂ] H) * π.1 a * (↑S⁻¹ : H →L[ℂ] H))

end Homomorphisms

section Commutators

variable {R : Type*} [NormedRing R]

def commutator (S T : R) : R := S * T - T * S

end Commutators

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

section

attribute [-instance] NonUnitalCStarAlgebra.toNormedSpace

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

abbrev HilbertCopies (H : Type u) (n : ℕ) := PiLp 2 (fun _ : Fin n => H)

def matrixOperator {n : ℕ} (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H)) :
    HilbertCopies H n →L[ℂ] HilbertCopies H n :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      ∑ j : Fin n, (X i j).comp (PiLp.proj 2 (fun _ : Fin n => H) j))

def amplify (Y : H →L[ℂ] H) (n : ℕ) :
    HilbertCopies H n →L[ℂ] HilbertCopies H n :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => Y.comp (PiLp.proj 2 (fun _ : Fin n => H) i))

def innerDerivation (Y : H →L[ℂ] H) :
    (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
  ContinuousLinearMap.mul ℂ (H →L[ℂ] H) Y -
    (ContinuousLinearMap.mul ℂ (H →L[ℂ] H)).flip Y

variable [CompleteSpace H]

def scalarCommutatorNorm (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H) : ℝ := by
  let : SeminormedAddCommGroup P.toStarSubalgebra.toSubalgebra.toSubmodule := inferInstance
  let : NormedSpace ℂ P.toStarSubalgebra.toSubalgebra.toSubmodule := inferInstance
  exact ‖(innerDerivation Y).comp P.toStarSubalgebra.toSubalgebra.toSubmodule.subtypeL‖

def CommutatorEstimate (P : VonNeumannAlgebra H) (C : ℝ) : Prop :=
  ∀ (Y : H →L[ℂ] H) (n : ℕ) (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H)),
    (∀ i j, X i j ∈ P) →
    ‖commutator (amplify Y n) (matrixOperator X)‖ ≤
      C * scalarCommutatorNorm P Y * ‖matrixOperator X‖

def UniformCommutatorEstimate (C : ℝ) : Prop :=
  ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (P : VonNeumannAlgebra K), CommutatorEstimate P C

def UniversalCommutatorTheorem : Prop := ∃ C : ℝ, 0 ≤ C ∧ UniformCommutatorEstimate.{u} C

def SimilarityTheorem : Prop :=
  ∀ (A : Type u) [CStarAlgebra A] (K : Type v) [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (π : BoundedUnitalHom A K),
    SimilarToStar A K π

abbrev CommutantProjection (M : VonNeumannAlgebra H) :=
  {e : H →L[ℂ] H // e ∈ M.commutant ∧ star e = e ∧ e * e = e}

def offDiagonalSeminorm (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) : ℝ :=
  sSup (Set.range fun e : CommutantProjection M =>
    ‖(1 - (e : H →L[ℂ] H)) * T * (e : H →L[ℂ] H)‖)

def UniversalHyperreflexivity (C : ℝ) : Prop :=
  ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (M : VonNeumannAlgebra K) (T : K →L[ℂ] K),
    Metric.infDist T (M : Set (K →L[ℂ] K)) ≤ 2 * C * offDiagonalSeminorm M T

end

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

def rowConstant : ℝ := 4 * Real.sqrt 2
def cyclicConstant : ℝ := (1 + 4 * rowConstant) ^ 2
def cornerConstant : ℝ := 6 * Real.pi ^ 2 * (1 + 4 * cyclicConstant)
def factorConstant : ℝ := max (max (3 * cornerConstant + 2) (1 + 2 * rowConstant)) 2
def universalConstant : ℝ := 3 * factorConstant + 2

/-- One absolute constant controls every finite matrix commutator. -/
def universalCommutatorTheorem_statement : Prop :=
  UniversalCommutatorTheorem.{u}

/-- Every von Neumann algebra has hyperreflexivity constant at most `2 * universalConstant`. -/
def universalHyperreflexivity_statement : Prop :=
  UniversalHyperreflexivity.{u} universalConstant

/-- Every bounded unital representation is similar to a star representation. -/
def similarityTheorem_statement : Prop :=
  SimilarityTheorem.{u,v}

end KadisonSimilarity

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u, v} : Prop :=
  _root_.OAI.KadisonSimilarity.universalCommutatorTheorem_statement.{u} ∧
  _root_.OAI.KadisonSimilarity.universalHyperreflexivity_statement.{u} ∧
  _root_.OAI.KadisonSimilarity.similarityTheorem_statement.{u, v}

end Problem

/- Formalization scope, from lean/docs/288.md: Kadison's similarity problem asks whether every bounded unital homomorphism from a unital complex $C^*$-algebra into operators on a Hilbert space is similar to a $*$-homomorphism. The formalization proves this for arbitrary Hilbert spaces. It also gives one universal hyperreflexivity constant for all unital von Neumann algebras. The linked commutator estimate is uniform over all finite matrix amplifications: its constant is independent of the algebra, Hilbert space, and amplification size. This is the quantitative derivation estimate supporting the similarity result. -/
