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

- problem_id: PinchedKahler
- collection: openai-math
- question_id: openai-math:359
- source: openai-math
- source_locator: lean/ComparatorChallenges/PinchedKahler.lean#OAI.PinchedHartogs.main_theorem
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs a contractible domain in ℂ3 with a complete negatively pinched Kähler metric but no bounded holomorphic coordinates, disproving bounded-domain uniformization in this setting. A higher-dimensional example has sectional curvature at most −1 and only constant bounded holomorphic functions; its curvature is not bounded below. ([Lean](lean/docs/359.md)) We construct a contractible domain in complex dimension three with a complete Kähler metric whose real sectional curvatures lie between two finite negative constants. It admits no bounded holomorphic map to ℂ3 with nowhere-vanishing Jacobian and is therefore not biholomorphic to a bounded domain. This gives a negative answer to the negatively pinched Kähler uniformization question.
- notes: OpenAI math result family 359, Negative Kähler curvature without bounded holomorphic coordinates -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/359.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.PinchedHartogs.main_theorem OAI.PinchedHartogs.controlled_potential OAI.PinchedHartogs.metric_transfer
- source_theorem_count: 3
- source_solution_module: OAI.Geometry.Kahler.Main
- source_main_result: OAI.PinchedHartogs.main_theorem
- source_papers: preprints/A-negatively-pinched-Kahler-threefold-without-bounded-holomorphic-coordinates-September-25-2026/paper.pdf
- source_scope_note: lean/docs/359.md
- source_field: Geometry
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace PinchedHartogs

abbrev Base := EuclideanSpace ℂ (Fin 2)
abbrev Ambient := Base × ℂ
abbrev Target := Fin 3 → ℂ

def ball : Set Base := {z | ‖z‖ < 1}

def hartogs (φ : Base → ℝ) : Set Ambient :=
  {p | p.1 ∈ ball ∧ Real.exp (φ p.1) * ‖p.2‖ ^ 2 < 1}

def noMinorant (φ : Base → ℝ) : Prop :=
  ¬ ∃ (H : Base → ℂ) (C : ℝ), AnalyticOnNhd ℂ H ball ∧
    ∀ z ∈ ball, (H z).re ≤ C + 4 * Real.log (1 / (1 - ‖z‖)) + φ z

def coordVector (j : Fin 3) : Ambient :=
  ![(EuclideanSpace.single 0 1, 0), (EuclideanSpace.single 1 1, 0), (0, 1)] j

def jacobian (F : Ambient → Target) (p : Ambient) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j ↦ (fderiv ℂ F p (coordVector j)) i

open scoped Matrix.Norms.Elementwise

abbrev CMatrix := Matrix (Fin 3) (Fin 3) ℂ
abbrev CurvatureTensor := Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℂ

def coordinates (u : Ambient) : Fin 3 → ℂ := ![u.1 0, u.1 1, u.2]

def dz (f : Ambient → ℂ) (p : Ambient) (j : Fin 3) : ℂ :=
  (fderiv ℝ f p (coordVector j) - Complex.I * fderiv ℝ f p (Complex.I • coordVector j)) / 2

def dbar (f : Ambient → ℂ) (p : Ambient) (j : Fin 3) : ℂ :=
  (fderiv ℝ f p (coordVector j) + Complex.I * fderiv ℝ f p (Complex.I • coordVector j)) / 2

def hermitianValue (h : CMatrix) (u v : Ambient) : ℂ :=
  ∑ i, ∑ j, h i j * coordinates u i * star (coordinates v j)

def realArea (h : CMatrix) (u v : Ambient) : ℝ :=
  (hermitianValue h u u).re * (hermitianValue h v v).re - (hermitianValue h u v).re ^ 2

def tensorValue (R : CurvatureTensor) (u v w y : Ambient) : ℂ :=
  ∑ a, ∑ b, ∑ c, ∑ d,
    R a b c d * coordinates u a * star (coordinates v b) * coordinates w c * star (coordinates y d)

def curvature (g : Ambient → CMatrix) (p : Ambient) : CurvatureTensor := fun a b c d ↦
  -dbar (fun q ↦ dz (fun r ↦ g r c d) q a) p b +
    ∑ e, ∑ k, (g p)⁻¹ e k * dz (fun q ↦ g q c e) p a * dbar (fun q ↦ g q k d) p b

def sectional (g : Ambient → CMatrix) (p u v : Ambient) : ℝ :=
  ((tensorValue (curvature g p) u u v v).re - (tensorValue (curvature g p) u v u v).re) /
    (2 * realArea (g p) u v)

def IsKahlerMetric (M : Set Ambient) (g : Ambient → CMatrix) : Prop :=
  ContDiffOn ℝ ∞ g M ∧
  (∀ p ∈ M, ∀ i j, g p i j = star (g p j i)) ∧
  (∀ p ∈ M, ∀ u : Ambient, u ≠ 0 → 0 < (hermitianValue (g p) u u).re) ∧
  (∀ p ∈ M, ∀ i j k, dz (fun q ↦ g q k j) p i = dz (fun q ↦ g q i j) p k)

def christoffel (g : Ambient → CMatrix) (p : Ambient) (k a c : Fin 3) : ℂ :=
  ∑ e, (g p)⁻¹ e k * dz (fun q ↦ g q c e) p a

def GeodesicallyComplete (M : Set Ambient) (g : Ambient → CMatrix) : Prop :=
  ∀ p ∈ M, ∀ v : Ambient, ∃ γ : ℝ → Ambient,
    ContDiff ℝ ∞ γ ∧ (∀ t, γ t ∈ M) ∧ γ 0 = p ∧ deriv γ 0 = v ∧
      ∀ t k, coordinates (deriv (deriv γ) t) k +
        ∑ a, ∑ c, christoffel g (γ t) k a c * coordinates (deriv γ t) a *
          coordinates (deriv γ t) c = 0

def IsNegativelyPinched (M : Set Ambient) (g : Ambient → CMatrix) (A B : ℝ) : Prop :=
  0 < A ∧ A ≤ B ∧ ∀ p ∈ M, ∀ u v : Ambient, LinearIndependent ℝ ![u, v] →
    -B ≤ sectional g p u v ∧ sectional g p u v ≤ -A

def NoBoundedCoordinates (M : Set Ambient) : Prop :=
  ∀ F : Ambient → Target, AnalyticOnNhd ℂ F M →
    (∃ B : ℝ, ∀ p ∈ M, ∀ i, ‖F p i‖ ≤ B) →
      ¬ ∀ p ∈ M, (jacobian F p).det ≠ 0

def BiholomorphicToBoundedDomain (M : Set Ambient) : Prop :=
  ∃ N : Set Ambient, IsOpen N ∧ Bornology.IsBounded N ∧
    ∃ F G : Ambient → Ambient, AnalyticOnNhd ℂ F M ∧ AnalyticOnNhd ℂ G N ∧
      MapsTo F M N ∧ MapsTo G N M ∧ (∀ p ∈ M, G (F p) = p) ∧ (∀ q ∈ N, F (G q) = q)

def MainTheorem : Prop :=
  ∃ (M : Set Ambient) (g : Ambient → CMatrix) (A B : ℝ),
    IsOpen M ∧ M.Nonempty ∧ ContractibleSpace M ∧ IsKahlerMetric M g ∧
      GeodesicallyComplete M g ∧ IsNegativelyPinched M g A B ∧
      NoBoundedCoordinates M ∧ ¬ BiholomorphicToBoundedDomain M

def psi (z : Base) : ℝ := -Real.log (1 - ‖z‖ ^ 2)
def metricPotential (φ : Base → ℝ) (lam : ℝ) (p : Ambient) : ℝ :=
  lam * psi p.1 - Real.log (1 - Real.exp (φ p.1) * ‖p.2‖ ^ 2)

def complexHessian (f : Ambient → ℝ) (p : Ambient) : CMatrix :=
  fun i j ↦ dz (fun q ↦ dbar (fun r ↦ (f r : ℂ)) q j) p i

def hartogsMetric (φ : Base → ℝ) (lam : ℝ) : Ambient → CMatrix :=
  complexHessian (metricPotential φ lam)

def dzBase (f : Base → ℂ) (z : Base) (i : Fin 2) : ℂ :=
  (fderiv ℝ f z (EuclideanSpace.single i 1) -
    Complex.I * fderiv ℝ f z (Complex.I • EuclideanSpace.single i 1)) / 2

def dbarBase (f : Base → ℂ) (z : Base) (i : Fin 2) : ℂ :=
  (fderiv ℝ f z (EuclideanSpace.single i 1) +
    Complex.I * fderiv ℝ f z (Complex.I • EuclideanSpace.single i 1)) / 2

def baseHessian (φ : Base → ℝ) (z : Base) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j ↦ dzBase (fun q ↦ dbarBase (fun r ↦ (φ r : ℂ)) q j) z i

def centeredChart (r : ℝ) (U : Base ≃ₗᵢ[ℂ] Base) (ζ : Base) : Base :=
  U (WithLp.toLp 2 ![((r : ℂ) + ζ 0) / (1 + (r : ℂ) * ζ 0),
    ((Real.sqrt (1 - r ^ 2) : ℝ) : ℂ) * ζ 1 / (1 + (r : ℂ) * ζ 0)])

def ChartControl (φ : Base → ℝ) (c C : ℝ) : Prop :=
  ∀ r : ℝ, 0 ≤ r → r < 1 → ∀ U : Base ≃ₗᵢ[ℂ] Base, ∀ v : Base,
    c * ‖v‖ ^ 2 ≤ (∑ i, ∑ j, baseHessian (φ ∘ centeredChart r U) 0 i j * v i * star (v j)).re ∧
    (∑ i, ∑ j, baseHessian (φ ∘ centeredChart r U) 0 i j * v i * star (v j)).re ≤ C * ‖v‖ ^ 2

def ChartJets (φ : Base → ℝ) (C : ℝ) : Prop :=
  ∀ r : ℝ, 0 ≤ r → r < 1 → ∀ U : Base ≃ₗᵢ[ℂ] Base, ∀ i j k l : Fin 2,
    ‖dzBase (fun z ↦ baseHessian (φ ∘ centeredChart r U) z i j) 0 k‖ +
    ‖dbarBase (fun z ↦ baseHessian (φ ∘ centeredChart r U) z i j) 0 l‖ +
    ‖dzBase (fun z ↦ dbarBase (fun q ↦ baseHessian (φ ∘ centeredChart r U) q i j) z l) 0 k‖ ≤ C

def ControlledPotential : Prop :=
  ∃ φ : Base → ℝ, ∃ C : ℝ, ContDiffOn ℝ ∞ φ ball ∧
    ChartControl φ 1 C ∧ ChartJets φ C ∧ noMinorant φ

def MetricTransfer : Prop :=
  ∀ c C : ℝ, 0 < c → c ≤ C → ∃ lam0 : ℝ, 0 < lam0 ∧
    ∀ φ : Base → ℝ, ContDiffOn ℝ ∞ φ ball → ChartControl φ c C → ChartJets φ C →
      ∀ lam : ℝ, lam0 ≤ lam → ContractibleSpace (hartogs φ) ∧
        IsKahlerMetric (hartogs φ) (hartogsMetric φ lam) ∧
        GeodesicallyComplete (hartogs φ) (hartogsMetric φ lam) ∧
        ∃ A B : ℝ, IsNegativelyPinched (hartogs φ) (hartogsMetric φ lam) A B

def main_theorem_statement : Prop :=
  MainTheorem

def controlled_potential_statement : Prop :=
  ControlledPotential

def metric_transfer_statement : Prop :=
  MetricTransfer

end PinchedHartogs

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.PinchedHartogs.main_theorem_statement ∧
  _root_.OAI.PinchedHartogs.controlled_potential_statement ∧
  _root_.OAI.PinchedHartogs.metric_transfer_statement

end Problem

/- Formalization scope, from lean/docs/359.md: The formalized result constructs a nonempty contractible complex threefold with a complete Kähler metric whose real sectional curvatures lie between two fixed negative constants. Nevertheless, it has no system of bounded holomorphic coordinates and is not biholomorphic to a bounded domain. The metric is obtained from an explicitly controlled potential. This is the negatively pinched construction; the different companion with only one-sided curvature control is separate. -/
