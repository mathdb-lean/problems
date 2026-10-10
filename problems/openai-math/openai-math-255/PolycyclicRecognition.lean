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

- problem_id: PolycyclicRecognition
- collection: openai-math
- question_id: openai-math:255
- source: openai-math
- source_locator: lean/ComparatorChallenges/PolycyclicRecognition.lean#OAI.PolycyclicRecognition.group_recognition
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves that every finitely generated group quasi-isometric to a finitely generated virtually polycyclic group is virtually polycyclic, resolving the Eskin–Fisher–Whyte lattice-recognition conjecture. Equivalently, a group quasi-isometric to a lattice in a connected simply connected solvable Lie group is virtually a uniform lattice in some such Lie group, possibly a different one. ([Lean](lean/docs/255.md)) We prove that every finitely generated group quasi-isometric to a finitely generated virtually polycyclic group is virtually polycyclic. This resolves the lattice-recognition conjecture of Eskin, Fisher and Whyte, which allows the ambient solvable Lie group in the conclusion to differ from the one in the hypothesis.
- notes: OpenAI math result family 255, Quasi-isometric recognition of virtually polycyclic groups -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/255.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.PolycyclicRecognition.group_recognition OAI.PolycyclicRecognition.main_uniform_bounded_height OAI.PolycyclicRecognition.lattice_recognition
- source_theorem_count: 3
- source_solution_module: OAI.GroupTheory.PolycyclicRecognition.Recognition
- source_papers: preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf
- source_scope_note: lean/docs/255.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

/-! # Quasi-isometric recognition and uniform bounded height

A polycyclic group has a finite subnormal series with cyclic factors. The
height quotient below is the quotient of the Lie algebra by the common
kernel of the diagonal adjoint characters.
-/

noncomputable section

namespace ChromaticCyclic

structure CyclicStep {G : Type*} [Group G] (H K : Subgroup G) : Prop where
  le : H ≤ K
  normal : (H.subgroupOf K).Normal
  cyclic : letI := normal; IsCyclic (K ⧸ H.subgroupOf K)

structure CyclicSeries {G : Type*} [Group G] (H K : Subgroup G) (n : ℕ) where
  group : ℕ → Subgroup G
  first : group 0 = H
  last : group n = K
  step : ∀ i < n, CyclicStep (group i) (group (i + 1))

end ChromaticCyclic

namespace PolycyclicRecognition

open Module LieAlgebra MeasureTheory
open scoped Manifold NNReal

section Coarse

variable {G H J : Type*} [Group G] [Group H] [Group J]

/-- Uniform control of finite sets of group differences. -/
def GroupBornologous (f : G → H) : Prop :=
  ∀ S : Set G, S.Finite → ∃ T : Set H, T.Finite ∧
    ∀ x y, x⁻¹ * y ∈ S → (f x)⁻¹ * f y ∈ T

/-- Coarse inverse maps with errors contained in fixed finite sets. -/
structure GroupCoarseEquivalence (G H : Type*) [Group G] [Group H] where
  toFun : G → H
  invFun : H → G
  bornologous_toFun : GroupBornologous toFun
  bornologous_invFun : GroupBornologous invFun
  left_error : (Set.range fun x => x⁻¹ * invFun (toFun x)).Finite
  right_error : (Set.range fun y => y⁻¹ * toFun (invFun y)).Finite

end Coarse

section Polycyclic

open ChromaticCyclic

variable (G : Type*) [Group G]

/-- Polycyclicity expressed by an actual cyclic subnormal series. -/
def IsPolycyclic : Prop :=
  ∃ n : ℕ, Nonempty (CyclicSeries (⊥ : Subgroup G) ⊤ n)

/-- Virtual polycyclicity means a polycyclic subgroup of finite index. -/
def IsVirtuallyPolycyclic : Prop :=
  ∃ H : Subgroup G, H.FiniteIndex ∧ IsPolycyclic H

end Polycyclic

section UniformLattice

variable {G : Type*} [Group G]

/-- A uniform lattice is discrete and has a compact fundamental cover. -/
def IsUniformLattice [TopologicalSpace G] (Λ : Subgroup G) : Prop :=
  DiscreteTopology Λ ∧ ∃ K : Set G, IsCompact K ∧
    ∀ g : G, ∃ (γ : Λ) (k : G), k ∈ K ∧ (γ : G) * k = g

end UniformLattice

/-- A connected simply connected finite-dimensional real solvable Lie group. -/
structure SimplyConnectedSolvableLieModel where
  modelSpace : Type
  [normedAddCommGroup : NormedAddCommGroup modelSpace]
  [normedSpace : NormedSpace ℝ modelSpace]
  [finiteDimensional : FiniteDimensional ℝ modelSpace]
  carrier : Type
  [topologicalSpace : TopologicalSpace carrier]
  [chartedSpace : ChartedSpace modelSpace carrier]
  [group : Group carrier]
  [lieGroup : LieGroup (𝓘(ℝ, modelSpace)) ⊤ carrier]
  [t2Space : T2Space carrier]
  [secondCountableTopology : SecondCountableTopology carrier]
  [simplyConnectedSpace : SimplyConnectedSpace carrier]
  [solvable : Group.IsSolvable carrier]

attribute [instance] SimplyConnectedSolvableLieModel.normedAddCommGroup
  SimplyConnectedSolvableLieModel.normedSpace SimplyConnectedSolvableLieModel.finiteDimensional
  SimplyConnectedSolvableLieModel.topologicalSpace SimplyConnectedSolvableLieModel.chartedSpace
  SimplyConnectedSolvableLieModel.group SimplyConnectedSolvableLieModel.lieGroup
  SimplyConnectedSolvableLieModel.t2Space SimplyConnectedSolvableLieModel.simplyConnectedSpace
  SimplyConnectedSolvableLieModel.secondCountableTopology
  SimplyConnectedSolvableLieModel.solvable

/-- A discrete subgroup with a normalized invariant measure on its coset space. -/
def IsFiniteCovolumeLattice {G : Type} [Group G] [TopologicalSpace G]
    (Λ : Subgroup G) : Prop :=
  letI : MeasurableSpace (G ⧸ Λ) := borel _
  DiscreteTopology Λ ∧ ∃ μ : Measure (G ⧸ Λ),
    IsProbabilityMeasure μ ∧ SMulInvariantMeasure G (G ⧸ Λ) μ

/-- Explicit chains with bounded steps and a linear bound on their length. -/
structure LinearMetricChains (X : Type*) [PseudoMetricSpace X] where
  step : ℝ
  step_pos : 0 < step
  slope : ℝ
  slope_nonneg : 0 ≤ slope
  error : ℝ
  error_nonneg : 0 ≤ error
  chain : ∀ x y : X, ∃ (n : ℕ) (p : ℕ → X),
    p 0 = x ∧ p n = y ∧ (n : ℝ) ≤ slope * dist x y + error ∧
      ∀ i < n, dist (p i) (p (i + 1)) ≤ step

/-- A compatible proper left-invariant metric with large-scale-geodesic chains. -/
structure ProperChainMetric (G : Type*) [Group G] [TopologicalSpace G] where
  metric : MetricSpace G
  topology_eq : metric.toUniformSpace.toTopologicalSpace = ‹TopologicalSpace G›
  proper : letI := metric; ProperSpace G
  leftInvariant : letI := metric; IsIsometricSMul G G
  chains : letI := metric; LinearMetricChains G

/-- The compatible metric retains the original topology definitionally. -/
abbrev ProperChainMetric.compatibleMetric
    {G : Type*} [Group G] [TopologicalSpace G] (d : ProperChainMetric G) : MetricSpace G :=
  d.metric.replaceTopology d.topology_eq.symm

section Height

variable {L I : Type*} [AddCommGroup L] [Module ℝ L]

/-- The common kernel, including the empty family of characters. -/
def heightKernel (χ : I → L →ₗ[ℝ] ℝ) : Submodule ℝ L := ⨅ i, (χ i).ker

/-- The canonical linear height quotient. -/
abbrev HeightSpace (χ : I → L →ₗ[ℝ] ℝ) := L ⧸ heightKernel χ

/-- The quotient map defining infinitesimal height. -/
def heightProjection (χ : I → L →ₗ[ℝ] ℝ) : L →ₗ[ℝ] HeightSpace χ :=
  (heightKernel χ).mkQ

end Height

/-- A simultaneous real upper triangular basis for the adjoint representation. -/
structure TriangularAdjoint (L : Type*) [LieRing L] [LieAlgebra ℝ L] (n : ℕ) where
  basis : Basis (Fin n) ℝ L
  upper : ∀ x : L, (LinearMap.toMatrix basis basis (LieAlgebra.ad ℝ L x)).IsUpperTriangular

namespace TriangularAdjoint

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {n : ℕ}
variable (T : TriangularAdjoint L n)

/-- The diagonal entries of the adjoint representation. -/
noncomputable def character (i : Fin n) : L →ₗ[ℝ] ℝ where
  toFun x := T.basis.repr ⁅x, T.basis i⁆ i
  map_add' x y := by simp [add_lie]
  map_smul' r x := (by simp [smul_lie] : _ = r * T.basis.repr ⁅x, T.basis i⁆ i)

end TriangularAdjoint

section Exponential

attribute [local instance 10000] NormedField.toNormedSpace

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]

/-- The exponential is characterized by its one-parameter subgroups and
by their tangent vectors at the identity. -/
structure IsGroupExponential (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) : Prop where
  map_zero : Exp 0 = 1
  map_add_smul : ∀ (v : GroupLieAlgebra (𝓘(ℝ, E)) G) (s t : ℝ),
    Exp ((s + t) • v) = Exp (s • v) * Exp (t • v)
  hasMFDerivAt_zero : ∀ v : GroupLieAlgebra (𝓘(ℝ, E)) G,
    HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) (fun t : ℝ => Exp (t • v)) 0
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) v)

end Exponential

/-- Unimodularity for the canonical Borel Haar measure of the Lie group. -/
def ModelIsUnimodular (R : SimplyConnectedSolvableLieModel) : Prop :=
  letI : IsTopologicalGroup R.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, R.modelSpace)) ⊤
  letI : LocallyCompactSpace R.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, R.modelSpace))
  letI : MeasurableSpace R.carrier := borel _
  letI : BorelSpace R.carrier := ⟨rfl⟩
  (Measure.haar : Measure R.carrier).IsMulRightInvariant

/-- The upper, lower, and coarse-surjectivity bounds of a self quasi-isometry. -/
structure SelfQuasiIsometry (G : Type*) [PseudoMetricSpace G] (K C : ℝ) where
  toFun : G → G
  upper : ∀ x y, dist (toFun x) (toFun y) ≤ K * dist x y + C
  lower : ∀ x y, dist x y ≤ K * dist (toFun x) (toFun y) + K * C
  surjective : ∀ y, ∃ x, dist y (toFun x) ≤ C

/-- Quasi-isometric recognition, including the finite-index uniform-lattice realization. -/
def group_recognition_statement : Prop :=
  ∀ {P J : Type} [Group P] [Group J] [Group.FG P] [Group.FG J] (e : GroupCoarseEquivalence P J) (hP : IsVirtuallyPolycyclic P),
    IsVirtuallyPolycyclic J ∧
      ∃ Γ : Subgroup J, Γ.FiniteIndex ∧
        ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
          IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ)

/-- One finite slope group controls the height of every self quasi-isometry. -/
def main_uniform_bounded_height_statement : Prop :=
  ∀ (R : SimplyConnectedSolvableLieModel) (d : ProperChainMetric R.carrier) {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, R.modelSpace)) R.carrier) a) (huni : ModelIsUnimodular R) {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (q : HeightSpace T.character ≃ₗ[ℝ] W) (Exp : GroupLieAlgebra (𝓘(ℝ, R.modelSpace)) R.carrier → R.carrier) (hExp : IsGroupExponential Exp) (π : R.carrier →* Multiplicative W) (hπExp : ∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x)),
    letI := d.compatibleMetric
    ∃ A : Subgroup (W ≃ₗ[ℝ] W), Set.Finite (A : Set (W ≃ₗ[ℝ] W)) ∧
      ∀ K C : ℝ, 1 ≤ K → 0 ≤ C → ∃ B : ℝ, 0 ≤ B ∧
        ∀ F : SelfQuasiIsometry R.carrier K C, ∃ AF : A, ∀ g,
          ‖(π (F.toFun g)).toAdd - ((π (F.toFun 1)).toAdd + AF.val (π g).toAdd)‖ ≤ B

/-- Finite-covolume lattice recognition, allowing a different ambient Lie group. -/
def lattice_recognition_statement : Prop :=
  ∀ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier) (hΛ : IsFiniteCovolumeLattice Λ) {J : Type} [Group J] [Group.FG J] (e : GroupCoarseEquivalence Λ J),
    ∃ Γ : Subgroup J, Γ.FiniteIndex ∧
      ∃ (R : SimplyConnectedSolvableLieModel) (Δ : Subgroup R.carrier),
        IsUniformLattice Δ ∧ Nonempty (Γ ≃* Δ)

end PolycyclicRecognition

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.PolycyclicRecognition.group_recognition_statement ∧
  _root_.OAI.PolycyclicRecognition.main_uniform_bounded_height_statement ∧
  _root_.OAI.PolycyclicRecognition.lattice_recognition_statement

end Problem

/- Formalization scope, from lean/docs/255.md: The formalization proves quasi-isometric recognition of virtually polycyclic groups: every finitely generated group quasi-isometric to a finitely generated virtually polycyclic group is itself virtually polycyclic. It also realizes a finite-index subgroup of the recognized group as a uniform lattice in a simply connected solvable Lie group, which may differ from the original ambient group. The linked structural estimate controls the height-coordinate behavior of self quasi-isometries of the stated unimodular solvable Lie models, up to bounded error and one of finitely many linear height symmetries. -/
