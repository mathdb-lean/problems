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

- problem_id: RuledCovering
- collection: openai-math
- question_id: openai-math:100
- source: openai-math
- source_locator: lean/ComparatorChallenges/RuledCovering.lean#OAI.RuledApproximation.fullMain
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Covers the entire closed regular tetrahedron by finitely many cylinders with compact triangular perpendicular bases whose total area is less than half its smallest orthogonal projection area. This disproves Bang's half-area cylinder-covering bound and the stronger directionwise normalized conjecture in dimension three. ([Lean](lean/docs/100.md)) A regular tetrahedron admits a finite cylinder covering with compact triangular perpendicular bases whose total area is less than half its minimum orthogonal projection area. This disproves the half-area cylinder-covering conjecture. By affine invariance, the same construction gives a counterexample to the directionwise normalized half-bound for every nondegenerate tetrahedron. We approximate compact ruled families of segments by finitely many cylinders with square intercept tiles and perpendicular-base area at most their integral projection cost plus any positive error. The velocity field is C1, and its differential has opposite real eigenvalues whose magnitudes are strictly below the inverse segment half-length; both eigenvalues may vanish. The result includes square-zero differentials with unrestricted shear and fields that pass between the two regimes. It holds for arbitrary compact label sets. The two-cylinder covering of a regular tetrahedron can be perturbed to give finite covers with total perpendicular base area strictly below half its minimum projection area. These covers give negative answers to both the half-area question and the directionwise normalized half-bound conjecture. By affine invariance, the directionwise conclusion holds for every nondegenerate tetrahedron. We prove that radially aligned segment sweeps admit finite cylinder covers with one triangular base for each interval of any tagged partition. As the mesh tends to zero, the total perpendicular base area converges to a weighted parameter area. An explicit application covers every regular tetrahedron with total base area below half its minimum projection area, giving negative answers to the half-area question and the directionwise normalized 1-Codimensional Cylinder Covering Conjecture.
- notes: OpenAI math result family 100, Cylinder coverings below the half-area bound -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/100.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.RuledApproximation.fullMain
- source_theorem_count: 1
- source_solution_module: OAI.Geometry.RuledCovering.Main
- source_papers: preprints/Finite-angular-cylinder-covers-below-the-half-area-bound-September-27-2026/main.pdf preprints/Finite-cylinder-approximation-of-ruled-sets-September-27-2026/main.pdf preprints/Slope-field-perturbations-of-the-two-cylinder-covering-September-27-2026/main.pdf preprints/Finite-triangular-approximation-of-radial-sweeps-September-27-2026/main.pdf
- source_scope_note: lean/docs/100.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace RuledApproximation

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Space := EuclideanSpace ℝ (Fin 3)

def vec2 (x y : ℝ) : Plane := WithLp.toLp 2 ![x, y]
def vec3 (x y z : ℝ) : Space := WithLp.toLp 2 ![x, y, z]
def axial (s : ℝ) (p : Plane) : Space := vec3 s (p 0) (p 1)

def IsParallelogram {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) : Prop :=
  ∃ c u v : E, LinearIndependent ℝ ![u, v] ∧
    P = {x | ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
      x = c + s • u + t • v}

def IsTriangle {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) : Prop :=
  ∃ c u v : E, LinearIndependent ℝ ![u, v] ∧
    P = {x | ∃ s : ℝ, ∃ t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ s + t ≤ 1 ∧
      x = c + s • u + t • v}

structure Cylinder where
  axis : Space
  unit_axis : ‖axis‖ = 1
  base : Set ((Submodule.span ℝ ({axis} : Set Space))ᗮ)

namespace Cylinder

def carrier (C : Cylinder) : Set Space :=
  {x | ∃ b ∈ C.base, ∃ t : ℝ, x = (b : Space) + t • C.axis}

def area (C : Cylinder) : ℝ := volume.real C.base

def parallelogram (C : Cylinder) : Prop := IsParallelogram C.base

def triangle (C : Cylinder) : Prop := IsTriangle C.base

def openBounded (C : Cylinder) : Prop :=
  IsOpen C.base ∧ Bornology.IsBounded C.base ∧ MeasurableSet C.base
end Cylinder

def familySet {n : ℕ} (C : Fin n → Cylinder) : Set Space := ⋃ i, (C i).carrier
def familyArea {n : ℕ} (C : Fin n → Cylinder) : ℝ := ∑ i, (C i).area

def HasFiniteCover (shape : Cylinder → Prop) (S : Set Space) (A : ℝ) : Prop :=
  ∃ n : ℕ, ∃ C : Fin n → Cylinder,
    (∀ i, shape (C i)) ∧ S ⊆ familySet C ∧ familyArea C ≤ A

/-- No boundary hypothesis is included in this neighborhood regularity predicate. -/
def SmoothNear (n : WithTop ℕ∞) (D : Set Plane) (v : Plane → Plane) : Prop :=
  ∃ U : Set Plane, IsOpen U ∧ D ⊆ U ∧ ContDiffOn ℝ n v U

/-- In dimension two these two distinct nonzero eigenvalues are all the eigenvalues. -/
def HyperbolicAt (L : ℝ) (v : Plane → Plane) (p : Plane) : Prop :=
  ∃ lam : ℝ, 0 < L * lam ∧ L * lam < 1 ∧
    Module.End.HasEigenvalue (fderiv ℝ v p).toLinearMap lam ∧
    Module.End.HasEigenvalue (fderiv ℝ v p).toLinearMap (-lam)

def weight (v : Plane) : ℝ := 1 / Real.sqrt (1 + ‖v‖ ^ 2)
def physicalWeight (h : ℝ) (w : Plane) : ℝ :=
  1 / Real.sqrt (1 + w 0 ^ 2 + h ^ 2 * w 1 ^ 2)

def ruled (D : Set Plane) (v : Plane → Plane) (L : ℝ) : Set Space :=
  {z | ∃ p ∈ D, ∃ r : ℝ, |r| ≤ L ∧
    z = vec3 (p 0 + r * v p 0) (p 1 + r * v p 1) r}

def physicalRuled (h : ℝ) (D : Set Plane) (v : Plane → Plane) (L : ℝ) : Set Space :=
  {z | ∃ p ∈ D, ∃ s : ℝ, |s| ≤ L ∧
    z = vec3 s (p 0 + s * v p 0) (h * (p 1 + s * v p 1))}

def HyperbolicStatement : Prop :=
  ∀ (D : Set Plane) (v : Plane → Plane) (L : ℝ),
    IsCompact D → SmoothNear 1 D v → 0 < L →
    (∀ p ∈ D, HyperbolicAt L v p) →
    ∀ e : ℝ, 0 < e → HasFiniteCover Cylinder.parallelogram (ruled D v L)
      ((∫ p in D, weight (v p)) + e)

def PhysicalHyperbolicStatement : Prop :=
  ∀ (h L : ℝ) (D : Set Plane) (v : Plane → Plane),
    0 < h → 0 < L → IsCompact D → SmoothNear 1 D v →
    (∀ p ∈ D, HyperbolicAt L v p) →
    ∀ (e : ℝ), 0 < e → ∀ F : Space ≃ᵢ Space,
    HasFiniteCover Cylinder.parallelogram (F '' physicalRuled h D v L)
      (h * (∫ p in D, physicalWeight h (v p)) + e)

def OpenRectangleC2 (D : Set Plane) (v : Plane → Plane) : Prop :=
  ∃ a b : Plane, (∀ i, a i < b i) ∧
    D ⊆ {p | ∀ i, p i ∈ Ioo (a i) (b i)} ∧
    ContDiffOn ℝ 2 v {p | ∀ i, p i ∈ Ioo (a i) (b i)}

def LogarithmicStatement : Prop :=
  ∀ (X k : ℝ) (D : Set Plane) (v : Plane → Plane),
    0 < X → 0 < k → IsCompact D → volume (frontier D) = 0 →
    OpenRectangleC2 D v →
    (∀ p ∈ D, LinearMap.trace ℝ Plane (fderiv ℝ v p).toLinearMap = 0 ∧
      LinearMap.det (fderiv ℝ v p).toLinearMap < 0 ∧
      k * X * Real.sqrt (-LinearMap.det (fderiv ℝ v p).toLinearMap) < 1) →
    ∀ e : ℝ, 0 < e → HasFiniteCover Cylinder.openBounded
      (physicalRuled 1 D (fun p => k • v p) X)
      ((∫ p in D, 1 / Real.sqrt (1 + k ^ 2 * ‖v p‖ ^ 2)) + e)

def ProductCellStatement : Prop :=
  ∀ (h M : ℝ) (D : Set Plane) (v : Plane → Plane),
    0 < h → 0 < M → IsCompact D → volume (frontier D) = 0 →
    SmoothNear 1 D v → (∀ p ∈ D, HyperbolicAt M v p) →
    ∀ e : ℝ, 0 < e → HasFiniteCover Cylinder.openBounded (physicalRuled h D v M)
      (h * (∫ p in D, physicalWeight h (v p)) + e)

def OrthogonalGridStatement : Prop :=
  ∀ (D : Set Plane) (v : Plane → Plane) (kappa : ℝ),
    IsCompact D → volume (frontier D) = 0 → SmoothNear 1 D v → kappa < 1 →
    (∀ p ∈ D, LinearMap.trace ℝ Plane (fderiv ℝ v p).toLinearMap = 0 ∧
      LinearMap.det (fderiv ℝ v p).toLinearMap < 0 ∧ ‖fderiv ℝ v p‖ ≤ kappa) →
    ∀ e : ℝ, 0 < e → HasFiniteCover Cylinder.parallelogram
      (physicalRuled (Real.sqrt 2) D v 1)
      (Real.sqrt 2 * (∫ p in D,
        1 / Real.sqrt (1 + v p 0 ^ 2 + 2 * v p 1 ^ 2)) + e)

def unitSquare : Set Plane := {x | ∀ i, |x i| ≤ (1 : ℝ) / 2}

def IsSquareTile (T : Set Plane) : Prop :=
  ∃ c : Plane, ∃ R : Plane ≃ₗᵢ[ℝ] Plane, ∃ a : ℝ, 0 < a ∧
    T = (fun x => c + a • R x) '' unitSquare

def auxiliaryCylinder (T : Set Plane) (g : Plane) : Set Space :=
  {z | ∃ s : ℝ, ∃ b ∈ T, z = axial s (b + s • g)}

def firstPhysicalMap (h : ℝ) (z : Space) : Space := vec3 (z 0) (z 1) (h * z 2)
def secondPhysicalMap (h a : ℝ) (z : Space) : Space :=
  vec3 (z 1) (z 0) (h * (a - z 2))

def NilpotentStatement : Prop :=
  ∀ (D : Set Plane) (G : Plane → Plane), IsCompact D → SmoothNear ∞ D G →
    (∀ b ∈ D, (fderiv ℝ G b).comp (fderiv ℝ G b) = 0) →
    ∀ h eps : ℝ, 0 < h → 0 < eps →
    ∃ n : ℕ, ∃ T : Fin n → Set Plane, ∃ g : Fin n → Plane,
      (∀ i, IsSquareTile (T i)) ∧
      physicalRuled 1 D G 1 ⊆ ⋃ i, auxiliaryCylinder (T i) (g i) ∧
      (∑ i, volume.real (T i) * physicalWeight h (g i)) ≤
        (∫ b in D, physicalWeight h (G b)) + eps ∧
      ∀ a : ℝ, ∃ C₁ C₂ : Fin n → Cylinder,
        (∀ i, (C₁ i).parallelogram ∧ (C₂ i).parallelogram ∧
          (C₁ i).carrier = firstPhysicalMap h '' auxiliaryCylinder (T i) (g i) ∧
          (C₂ i).carrier = secondPhysicalMap h a '' auxiliaryCylinder (T i) (g i) ∧
          (C₁ i).area = h * volume.real (T i) * physicalWeight h (g i) ∧
          (C₂ i).area = h * volume.real (T i) * physicalWeight h (g i))

/-- The regular edge-2 tetrahedron in physical coordinates. -/
def tetrahedron : Set Space :=
  {z | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ |z 0| ≤ 1 - t ∧ |z 1| ≤ t ∧
    z 2 = Real.sqrt 2 * t}

def singularField (p : ℝ) (b : Plane) : Plane :=
  vec2 (((1 / 2 : ℝ) / 2) * (b 1 / (1 / 2)) ^ (p - 1) *
    (p + (2 - p) * (b 0 / b 1) ^ 2))
    ((b 1 / (1 / 2)) ^ (p - 2) * b 0)

def ceilingPolynomial (p b : ℝ) : ℝ :=
  b ^ 2 * ((1 / 2 : ℝ) * p / 2 + (2 - p) / (2 * (1 / 2)) * b ^ 2)

def singularDomain (p gamma c : ℝ) : Set Plane :=
  {b | c ^ gamma ≤ b 1 ∧ b 1 ≤ 2 ∧ |b 0| ≤ b 1 ∧
    b 1 ≤ (1 / 2 : ℝ) + c ^ 2 * ceilingPolynomial p (b 0) + c ^ (5 / 2 : ℝ)}

def singularLower (p gamma c : ℝ) : Set Space :=
  physicalRuled (Real.sqrt 2) (singularDomain p gamma c)
    (fun b => c • singularField p b) 1

def singularUpper (p gamma c : ℝ) : Set Space :=
  {z | ∃ b ∈ singularDomain p gamma c, ∃ y : ℝ, |y| ≤ 1 ∧
    z = vec3 (b 0 - c * y * singularField p b 0) y
      (Real.sqrt 2 * (1 - (b 1 - c * y * singularField p b 1)))}

def lowerTip (d : ℝ) : Set Space :=
  {z | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 2 * d ∧ |z 1| ≤ t ∧ z 2 = Real.sqrt 2 * t}

def upperTip (d : ℝ) : Set Space :=
  {z | ∃ s : ℝ, 0 ≤ s ∧ s ≤ 2 * d ∧ |z 0| ≤ s ∧ z 2 = Real.sqrt 2 * (1 - s)}

def singularCost (p gamma c : ℝ) : ℝ :=
  Real.sqrt 2 * ∫ b in singularDomain p gamma c,
    physicalWeight (Real.sqrt 2) (c • singularField p b)

def singularCoefficient (p : ℝ) : ℝ :=
  (1 / 2 : ℝ) ^ 4 * (2 * p ^ 2 + 10 * p - 13) / (30 * p)

def SingularStatement : Prop :=
  ∀ p gamma : ℝ, 1 < p → p < (Real.sqrt 51 - 5) / 2 →
    1 < gamma → gamma < 1 / (2 - p) →
    singularCoefficient p < 0 ∧
    Asymptotics.IsLittleO (𝓝[>] (0 : ℝ))
      (fun c => 2 * singularCost p gamma c + 8 * Real.sqrt 2 * (c ^ gamma) ^ 2 -
        (Real.sqrt 2 / 2 + 2 * Real.sqrt 2 * singularCoefficient p * c ^ 2))
      (fun c => c ^ 2) ∧
    ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ),
      ∃ n m : ℕ, ∃ C : Fin n → Cylinder, ∃ D : Fin m → Cylinder,
      ∃ B₁ B₂ : Cylinder,
        (∀ i, (C i).parallelogram) ∧ (∀ j, (D j).parallelogram) ∧
        B₁.triangle ∧ B₂.triangle ∧
        singularLower p gamma c ⊆ familySet C ∧
        singularUpper p gamma c ⊆ familySet D ∧
        B₁.carrier = lowerTip (c ^ gamma) ∧ B₂.carrier = upperTip (c ^ gamma) ∧
        tetrahedron ⊆ familySet C ∪ familySet D ∪ B₁.carrier ∪ B₂.carrier ∧
        familyArea C + familyArea D + B₁.area + B₂.area < Real.sqrt 2 / 2

def FullMain : Prop :=
  HyperbolicStatement ∧ PhysicalHyperbolicStatement ∧ LogarithmicStatement ∧
  ProductCellStatement ∧ OrthogonalGridStatement ∧ NilpotentStatement ∧ SingularStatement

def fullMain_statement : Prop :=
  FullMain

end RuledApproximation

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.RuledApproximation.fullMain_statement

end Problem

/- Formalization scope, from lean/docs/100.md: The half-area cylinder-covering conjecture predicts that a cylinder cover of a convex body has total perpendicular-base area at least half its smallest projection area. The formalization constructs finite covers of a regular tetrahedron by cylinders with compact triangular bases whose total area is strictly below that bound. For the explicit small parameter $\varepsilon$, the normalized area is $1/2-(13/6000)\varepsilon^2+O(\varepsilon^4)$, giving the strict saving. It also gives a counterexample to the directionwise normalized half-bound. The broader Comparator file includes the companion ruled-set and radial-sweep approximation results. The formalization approximates compact ruled families of line segments by finite cylinder covers with perpendicular-base area at most the integral projection cost plus any prescribed positive error. The selected results cover the stated $C^1$ hyperbolic differential condition, square-zero and nilpotent cases, physical rescalings, logarithmic and product-cell estimates, and singular cases. Compact label sets need not have regular boundary. The differential and segment-length hypotheses remain part of each result. The aggregate Comparator file also contains the companion tetrahedron counterexamples and radial-sweep estimates. The formalization proves that every regular tetrahedron has a finite cylinder cover whose total perpendicular-base area is strictly less than half its minimum projection area. It supplies covers with parallelogram bases and also proves the directionwise normalized cost is below one half. These are counterexamples to the two cylinder-covering bounds studied in the paper. The linked aggregate includes the accompanying explicit angular covers and finite approximation theorems for ruled sets and radial sweeps. The affine extension of the directionwise conclusion to every nondegenerate tetrahedron is outside the selected regular-tetrahedron statements. The formalization proves finite triangular-cylinder approximation for radially aligned segment sweeps. For every tagged partition of the parameter interval, it constructs one cylinder per interval with the prescribed radial direction, and the total perpendicular-base area converges to the weighted parameter area as the mesh tends to zero. It also covers the corresponding actual swept set under the stated geometric hypotheses. The same aggregate includes finite cylinder covers of regular tetrahedra below half the minimum projection area. These are the radial approximation and covering consequences relevant to the paper. -/
