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

- problem_id: ArnoldCounterexample
- collection: openai-math
- question_id: openai-math:347
- source: openai-math
- source_locator: lean/ComparatorChallenges/ArnoldCounterexample.lean#OAI.ArnoldCounterexample.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Disproves stable-Morse lower bounds for nondegenerate Hamiltonian fixed points: on simply connected closed Kähler manifolds of real dimension 22, the deficit below the stable Morse number is unbounded. A separate Hamiltonian diffeomorphism of the complex quadric threefold has exactly three fixed points, fewer than the four critical points required of every smooth function. ([Lean](lean/docs/347.md)) We construct a smooth Hamiltonian diffeomorphism of the complex quadric threefold with exactly three fixed points, at least one of which is degenerate. The critical number and the unit-inclusive rational cup length of this manifold are both four. Thus the example disproves the unrestricted critical-number and rational cup-length forms of the Arnold conjecture.
- notes: OpenAI math result family 347, Counterexamples to stable-Morse and strong Arnold fixed-point bounds -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/347.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.ArnoldCounterexample.main
- source_theorem_count: 1
- source_solution_module: OAI.Geometry.Arnold.Main
- source_main_result: OAI.ArnoldCounterexample.main
- source_papers: preprints/A-degenerate-counterexample-to-the-critical-number-Arnold-bound-September-23-2026/paper.pdf
- source_scope_note: lean/docs/347.md
- source_field: Geometry
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section
open scoped BigOperators ContDiff

namespace ArnoldCounterexample

abbrev CV := Fin 5 → ℂ

def quadricPolynomial (z : CV) : ℂ := ∑ j, z j ^ 2

def normSquared (z : CV) : ℝ := ∑ j, Complex.normSq (z j)

def IsUnitQuadric (z : CV) : Prop :=
  normSquared z = 1 ∧ quadricPolynomial z = 0

abbrev UnitQuadric := {z : CV // IsUnitQuadric z}

/-- The literal projective quadric sum z_j^2 = 0 in CP^4. -/
def Q3 := {q : Projectivization ℂ CV //
  ∃ (z : CV) (hz : z ≠ 0), Projectivization.mk ℂ z hz = q ∧
    quadricPolynomial z = 0}

def project (z : UnitQuadric) : Q3 := by
  have hz : (z : CV) ≠ 0 := by
    intro h
    have hunit := z.property.1
    simp [normSquared, h] at hunit
  exact ⟨Projectivization.mk ℂ z hz, z, hz, rfl, z.property.2⟩

/-- Horizontal lifts of the real tangent of Q3 at [z]. -/
def Horizontal (z v : CV) : Prop :=
  (∑ j, star (z j) * v j) = 0 ∧ (∑ j, z j * v j) = 0

/-- The restricted Fubini--Study form, evaluated on horizontal lifts. -/
def omega (v w : CV) : ℝ := 2 * (∑ j, star (v j) * w j).im

/-- A local smooth extension of the pullback of h to the unit isotropic cone. -/
def LocalFunctionLift (h : Q3 → ℝ) (z : UnitQuadric)
    (U : Set CV) (g : CV → ℝ) : Prop :=
  IsOpen U ∧ (z : CV) ∈ U ∧ ContDiffOn ℝ ∞ g U ∧
    ∀ y : UnitQuadric, (y : CV) ∈ U → g y = h (project y)

def IsSmoothFunction (h : Q3 → ℝ) : Prop :=
  ∀ z : UnitQuadric, ∃ (U : Set CV) (g : CV → ℝ), LocalFunctionLift h z U g

structure SmoothFunction where
  toFun : Q3 → ℝ
  smooth : IsSmoothFunction toFun

/-- dh_q = 0, expressed using all local lifts, independent of normal extensions. -/
def IsCritical (h : Q3 → ℝ) (q : Q3) : Prop :=
  ∀ z : UnitQuadric, project z = q →
    ∀ (U : Set CV) (g : CV → ℝ), LocalFunctionLift h z U g →
      ∀ v : CV, Horizontal z v → fderiv ℝ g z v = 0

def criticalSet (h : SmoothFunction) : Set Q3 := {q | IsCritical h.toFun q}

/-- The minimum critical number, including degenerate functions (ENat allows infinity). -/
def criticalNumber : ℕ∞ := ⨅ h : SmoothFunction, (criticalSet h).encard

/-- An explicit smooth lift of a Hamiltonian isotopy, with inverse and generator.
The Hamiltonian equation uses i_X omega = dH. -/
structure HamiltonianPath (φ : Q3 ≃ Q3) where
  forward : ℝ × CV → CV
  backward : ℝ × CV → CV
  hamiltonian : ℝ × CV → ℝ
  forward_smooth : ContDiff ℝ ∞ forward
  backward_smooth : ContDiff ℝ ∞ backward
  hamiltonian_smooth : ContDiff ℝ ∞ hamiltonian
  forward_preserves : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : UnitQuadric,
    IsUnitQuadric (forward (t, z))
  backward_preserves : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : UnitQuadric,
    IsUnitQuadric (backward (t, z))
  forward_phase : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : UnitQuadric,
    ∀ a : ℂ, Complex.normSq a = 1 → forward (t, a • (z : CV)) = a • forward (t, z)
  backward_phase : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : UnitQuadric,
    ∀ a : ℂ, Complex.normSq a = 1 → backward (t, a • (z : CV)) = a • backward (t, z)
  hamiltonian_phase : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : UnitQuadric,
    ∀ a : ℂ, Complex.normSq a = 1 → hamiltonian (t, a • (z : CV)) = hamiltonian (t, z)
  left_inverse : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : UnitQuadric,
    backward (t, forward (t, z)) = z
  right_inverse : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : UnitQuadric,
    forward (t, backward (t, z)) = z
  start : ∀ z : UnitQuadric, forward (0, z) = z
  finish : ∀ z : UnitQuadric,
    project ⟨forward (1, z), forward_preserves 1 (by norm_num) z⟩ = φ (project z)
  equation : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : UnitQuadric, ∀ v : CV,
    Horizontal (forward (t, z)) v →
      omega (deriv (fun s : ℝ => forward (s, z)) t) v =
        fderiv ℝ (fun w : CV => hamiltonian (t, w)) (forward (t, z)) v

def IsHamiltonian (φ : Q3 ≃ Q3) : Prop := Nonempty (HamiltonianPath φ)

def fixedSet (φ : Q3 ≃ Q3) : Set Q3 := {q | φ q = q}

/-- Eigenvalue 1 in the derivative on the quotient tangent, not an ambient
  spurious vertical eigenvector. v is nonzero and horizontal. -/
def HasDegenerateFixedPoint (φ : Q3 ≃ Q3) : Prop :=
  ∃ (z : UnitQuadric) (v : CV), φ (project z) = project z ∧ v ≠ 0 ∧
    Horizontal z v ∧ ∃ (U : Set CV) (G : CV → CV),
      IsOpen U ∧ (z : CV) ∈ U ∧ ContDiffOn ℝ ∞ G U ∧ G z = z ∧
      (∀ y : UnitQuadric, (y : CV) ∈ U →
        ∃ hy : IsUnitQuadric (G y), project ⟨G y, hy⟩ = φ (project y)) ∧
      ∃ a : ℝ, fderiv ℝ G z v - v = a • (Complex.I • (z : CV))

/-- The Hamiltonian counterexample, with the complete fixed set, the lower bound
for all smooth functions, and a genuine nonzero quotient-tangent eigenvector. -/
def main_statement : Prop :=
  ∃ φ : Q3 ≃ Q3, IsHamiltonian φ ∧ (fixedSet φ).encard = 3 ∧
      (3 : ℕ∞) < 4 ∧ 4 ≤ criticalNumber ∧ HasDegenerateFixedPoint φ

end ArnoldCounterexample

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.ArnoldCounterexample.main_statement

end Problem

/- Formalization scope, from lean/docs/347.md: The critical-number form of Arnold's fixed-point conjecture predicts at least as many fixed points as the minimum number of critical points of a smooth function. The formalized counterexample is a Hamiltonian diffeomorphism of the complex quadric threefold with exactly three fixed points, while every smooth function on that manifold has at least four critical points. At least one fixed point is degenerate. The separate nondegenerate Morse-number construction is not included. -/
