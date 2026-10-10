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

- problem_id: SharpCAT0Filling
- collection: openai-math
- question_id: openai-math:337
- source: openai-math
- source_locator: lean/ComparatorChallenges/SharpCAT0Filling.lean#OAI.CAT0Fillings.sharp_integral_filling
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves generalized Cartan–Hadamard isoperimetry in every dimension: in a complete simply connected manifold with sectional curvature at most κ ≤ 0, every finite-volume finite-perimeter set satisfies the sharp comparison with the equal-volume model ball. Bounded positive-volume equality regions for κ = 0 are Euclidean balls. Also proves sharp Euclidean filling bounds for compactly supported integral n-cycles, n ≥ 2, in arbitrary proper CAT$`(0)`$ spaces. ([Lean](lean/docs/337.md))
- notes: OpenAI math result family 337, Sharp Cartan–Hadamard isoperimetry and rigidity -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/337.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.CAT0Fillings.sharp_integral_filling
- source_theorem_count: 1
- source_solution_module: OAI.Geometry.CAT0Fillings.Main
- source_scope_note: lean/docs/337.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings

attribute [local instance] Classical.propDecidable

universe u

abbrev Euc (k : ℕ) := EuclideanSpace ℝ (Fin k)
abbrev Functional (X : Type u) (k : ℕ) := (X → ℝ) → (Fin k → X → ℝ) → ℝ

section MetricCurrents

variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

def BoundedLip (b : X → ℝ) : Prop :=
  (∃ K : ℝ≥0, LipschitzWith K b) ∧ ∃ M : ℝ, ∀ x, |b x| ≤ M

def Admissible {k : ℕ} (b : X → ℝ) (π : Fin k → X → ℝ) : Prop :=
  BoundedLip b ∧ ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)

def Controls {k : ℕ} (T : Functional X k) (μ : Measure X) : Prop :=
  ∀ (b : X → ℝ) (π : Fin k → X → ℝ), BoundedLip b →
    (∀ i, LipschitzWith 1 (π i)) →
    |T b π| ≤ ∫ x, |b x| ∂μ

noncomputable def mass {k : ℕ} (T : Functional X k) : ℝ :=
  sInf {r : ℝ | ∃ μ : Measure X,
    IsFiniteMeasure μ ∧ Controls T μ ∧ r = μ.real univ}

structure IsMetricCurrent {k : ℕ} (T : Functional X k) : Prop where
  offDomain : ∀ b π, ¬Admissible b π → T b π = 0
  linearFirst : ∀ b₁ b₂ π (a c : ℝ), BoundedLip b₁ → BoundedLip b₂ →
    (∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) →
    T (fun x => a * b₁ x + c * b₂ x) π = a * T b₁ π + c * T b₂ π
  linearCoord : ∀ b π i f (a c : ℝ), Admissible b π →
    (∃ K : ℝ≥0, LipschitzWith K f) →
    T b (Function.update π i (fun x => a * π i x + c * f x)) =
      a * T b π + c * T b (Function.update π i f)
  sequentialContinuity : ∀ b π (πs : ℕ → Fin k → X → ℝ), BoundedLip b →
    (∀ i, ∃ K : ℝ≥0, ∀ j, LipschitzWith K (πs j i)) →
    (∀ i x, Tendsto (fun j => πs j i x) atTop (𝓝 (π i x))) →
    Tendsto (fun j => T b (πs j)) atTop (𝓝 (T b π))
  locality : ∀ b π, Admissible b π →
    (∃ (i : Fin k) (U : Set X) (c : ℝ), IsOpen U ∧ Function.support b ⊆ U ∧
      ∀ x ∈ U, π i x = c) → T b π = 0
  finiteMass : ∃ μ : Measure X, IsFiniteMeasure μ ∧ Controls T μ

noncomputable def boundarySucc {k : ℕ} (T : Functional X (k + 1)) : Functional X k :=
  fun b π => if Admissible b π then T (fun _ => 1) (Matrix.vecCons b π) else 0

noncomputable def boundary : {k : ℕ} → Functional X k → Functional X (k - 1)
  | 0, _ => fun _ _ => 0
  | _ + 1, T => boundarySucc T

structure IntegerChart (X : Type u) [MetricSpace X] (k : ℕ) where
  domain : Set (Euc k)
  borel : MeasurableSet domain
  bounded : Bornology.IsBounded domain
  param : domain → X
  bilipschitz : ∃ L U : ℝ≥0, LipschitzWith L param ∧ AntilipschitzWith U param
  multiplicity : Euc k → ℤ
  integrable : Integrable (fun z => (multiplicity z : ℝ)) (volume.restrict domain)

namespace IntegerChart

variable {k : ℕ} (C : IntegerChart X k)

noncomputable def scalar (f : X → ℝ) (z : Euc k) : ℝ :=
  if hz : z ∈ C.domain then f (C.param ⟨z, hz⟩) else 0

noncomputable def jacobian (π : Fin k → X → ℝ) (z : Euc k) : ℝ :=
  Matrix.det (fun i j =>
    (fderivWithin ℝ (C.scalar (π i)) C.domain z) (EuclideanSpace.single j 1))

noncomputable def action : Functional X k :=
  fun b π => if Admissible b π then
    ∫ z in C.domain, (C.multiplicity z : ℝ) * C.scalar b z * C.jacobian π z
  else 0

def image : Set X := Set.range C.param

end IntegerChart

def IntegerRectifiable {k : ℕ} (T : Functional X k) : Prop :=
  ∃ C : ℕ → IntegerChart X k,
    Pairwise (fun i j => Disjoint (C i).image (C j).image) ∧
    (∀ i, IsMetricCurrent (C i).action) ∧
    Summable (fun i => mass (C i).action) ∧
    ∀ b π, T b π = ∑' i, (C i).action b π

def IsIntegral : (k : ℕ) → Functional X k → Prop
  | 0, T => IsMetricCurrent T ∧ IntegerRectifiable T
  | _ + 1, T => IsMetricCurrent T ∧ IntegerRectifiable T ∧
      IsMetricCurrent (boundarySucc T) ∧ IntegerRectifiable (boundarySucc T)

abbrev IntegralCurrent (X : Type u) [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (k : ℕ) := { T : Functional X k // IsIntegral k T }

def CompactlySupported {k : ℕ} (T : Functional X k) : Prop :=
  ∃ K : Set X, IsCompact K ∧
    ∀ b π, Admissible b π → (∀ x ∈ K, b x = 0) → T b π = 0

def IsCycle {k : ℕ} (T : Functional X k) : Prop := boundary T = fun _ _ => 0

end MetricCurrents

section Geometry
variable (X : Type u) [MetricSpace X]

def IsCAT0 : Prop :=
  ∃ segment : X → X → ℝ → X,
    (∀ x y, segment x y 0 = x ∧ segment x y 1 = y) ∧
    (∀ x y s t, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      dist (segment x y s) (segment x y t) = |s - t| * dist x y) ∧
    (∀ o x y s t, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      dist (segment o x s) (segment o y t) ^ 2 ≤
        (s * dist o x - t * dist o y) ^ 2 +
          s * t * ((dist x y) ^ 2 - (dist o x - dist o y) ^ 2))

end Geometry

noncomputable def omega (k : ℕ) : ℝ :=
  (volume (Metric.ball (0 : Euc k) 1)).toReal
noncomputable def sphereArea (n : ℕ) : ℝ := (n + 1 : ℝ) * omega (n + 1)
noncomputable def fillingCoefficient (n : ℕ) : ℝ :=
  1 / ((n + 1 : ℝ) * (sphereArea n) ^ (1 / (n : ℝ)))
noncomputable def fillingPower (n : ℕ) : ℝ := (n + 1 : ℝ) / (n : ℝ)

def sharp_integral_filling_statement : Prop :=
  ∀ (X : Type u) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X] (hX : IsCAT0 X) (n : ℕ) (hn : 2 ≤ n) (T : IntegralCurrent X n) (hTc : CompactlySupported T.val) (hTz : IsCycle T.val),
    ∃ S : IntegralCurrent X (n + 1), CompactlySupported S.val ∧
      boundarySucc S.val = T.val ∧
      mass S.val ≤ fillingCoefficient n * (mass T.val) ^ fillingPower n

end CAT0Fillings

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u} : Prop :=
  _root_.OAI.CAT0Fillings.sharp_integral_filling_statement.{u}

end Problem

/- Formalization scope, from lean/docs/337.md: The formalization proves the sharp Euclidean filling inequality for every compactly supported integral $n$-cycle in a proper $\mathrm{CAT}(0)$ space, for $n\ge2$. It constructs a compactly supported integral filling whose mass is at most $C_n$ times the boundary mass to the power $(n+1)/n$, where $C_n$ is the Euclidean isoperimetric coefficient. Integer multiplicities and the ambient dimension are unrestricted. A second statement proves that this coefficient is optimal by giving, in Euclidean space, a cycle for which every compactly supported integral filling has at least that mass. This yields the selected integral-current form of the Cartan–Hadamard isoperimetric conjecture. -/
