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

- problem_id: HotSpots
- collection: openai-math
- question_id: openai-math:369
- source: openai-math
- source_locator: lean/ComparatorChallenges/HotSpots.lean#OAI.StrictHotSpots.main_theorem
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves a strict form of Burdzy's simply connected hot spots conjecture. On every smooth bounded simply connected planar domain, each nonzero eigenfunction for the first positive Neumann eigenvalue has no interior critical point, so all global extrema lie on the boundary. Eigenvalue multiplicity is allowed. ([Lean](lean/docs/369.md)) We prove the strict hot spots conjecture for smooth bounded simply connected planar domains. More precisely, every nonzero eigenfunction for the first positive Neumann eigenvalue has nonvanishing gradient in the interior, so all its global maxima and minima lie on the boundary. This holds even when the eigenvalue is multiple.
- notes: OpenAI math result family 369, The hot spots conjecture for simply connected planar domains -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/369.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.StrictHotSpots.main_theorem
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.HotSpots.Main
- source_papers: preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/main.pdf
- source_scope_note: lean/docs/369.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace StrictHotSpots

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def SmoothBoundary (Ω : Set Plane) : Prop :=
  ∀ p ∈ frontier Ω, ∃ (U : Set Plane) (ρ : Plane → ℝ),
    IsOpen U ∧ p ∈ U ∧ ContDiffOn ℝ ∞ ρ U ∧
    fderiv ℝ ρ p ≠ 0 ∧ ρ p = 0 ∧
    Ω ∩ U = {x | ρ x < 0} ∩ U

def AdmissibleDomain (Ω : Set Plane) : Prop :=
  Ω.Nonempty ∧ IsOpen Ω ∧ Bornology.IsBounded Ω ∧
    IsSimplyConnected Ω ∧ SmoothBoundary Ω

def HasH1Gradient (Ω : Set Plane) (v : Plane → ℝ) (g : Plane → Plane) : Prop :=
  MemLp v 2 (volume.restrict Ω) ∧ MemLp g 2 (volume.restrict Ω) ∧
  ∀ φ : Plane → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    ∀ e : Plane,
      (∫ x in Ω, v x * (fderiv ℝ φ x) e) =
        -(∫ x in Ω, (inner ℝ (g x) e) * φ x)

def rayleighValues (Ω : Set Plane) : Set ℝ :=
  {r | ∃ (v : Plane → ℝ) (g : Plane → Plane),
    HasH1Gradient Ω v g ∧ (∫ x in Ω, v x) = 0 ∧
    0 < (∫ x in Ω, (v x) ^ 2) ∧
    r = (∫ x in Ω, ‖g x‖ ^ 2) / (∫ x in Ω, (v x) ^ 2)}

def firstPositiveNeumannValue (Ω : Set Plane) : ℝ := sInf (rayleighValues Ω)

def InFirstNeumannEigenspace (Ω : Set Plane) (u : Plane → ℝ) : Prop :=
  ContDiffOn ℝ ∞ u (closure Ω) ∧ HasH1Gradient Ω u (gradient u) ∧
    (∫ x in Ω, u x) = 0 ∧
    ∀ (v : Plane → ℝ) (g : Plane → Plane), HasH1Gradient Ω v g →
      (∫ x in Ω, inner ℝ (gradient u x) (g x)) =
        firstPositiveNeumannValue Ω * (∫ x in Ω, u x * v x)

def MainConclusion (Ω : Set Plane) (u : Plane → ℝ) : Prop :=
  (∀ x ∈ Ω, gradient u x ≠ 0) ∧
    ∀ x ∈ Ω, sInf (u '' frontier Ω) < u x ∧ u x < sSup (u '' frontier Ω)

def main_theorem_statement : Prop :=
  ∀ (Ω : Set Plane) (hΩ : AdmissibleDomain Ω) (u : Plane → ℝ) (hu : InFirstNeumannEigenspace Ω u) (hne : ∃ x ∈ Ω, u x ≠ 0),
    MainConclusion Ω u

end StrictHotSpots
end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.StrictHotSpots.main_theorem_statement

end Problem

/- Formalization scope, from lean/docs/369.md: The strict hot-spots conjecture asks whether extrema of a first nonconstant Neumann eigenfunction occur only on the boundary. The formalization proves the stronger interior statement on every nonempty smooth bounded simply connected planar domain: every nonzero eigenfunction in the first positive Neumann eigenspace has nonvanishing gradient throughout the interior. Consequently all global maxima and minima lie on the boundary. The conclusion applies to every eigenfunction even when the eigenvalue is multiple. -/
