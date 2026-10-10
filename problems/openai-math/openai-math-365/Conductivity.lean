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

- problem_id: Conductivity
- collection: openai-math
- question_id: openai-math:365
- source: openai-math
- source_locator: lean/ComparatorChallenges/Conductivity.lean#OAI.ScalarConductivity.main_nonuniqueness
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Zero-frequency measurements on any nonempty open boundary patch determine a smooth metric and smooth unitary connection on a trivial Hermitian rank-two bundle over a compact connected manifold of dimension at least three, up to diffeomorphism and gauge fixed on that patch. Inputs and observations use the same patch. In contrast, distinct uniformly positive bounded measurable scalar conductivities on a three-dimensional ball can have identical full-boundary data. ([Lean](lean/docs/365.md)) We construct two distinct uniformly positive bounded measurable scalar conductivities on a ball in ℝ3 with the same full Dirichlet-to-Neumann operator. Both conductivities equal one near the boundary. This gives nonuniqueness in the scalar Calderón problem at bounded measurable regularity.
- notes: OpenAI math result family 365, Joint metric and connection recovery from one boundary patch -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/365.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.ScalarConductivity.main_nonuniqueness
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.Conductivity.Main
- source_main_result: OAI.ScalarConductivity.main_nonuniqueness
- source_papers: preprints/Nonuniqueness-for-Bounded-Measurable-Scalar-Conductivities-in-Three-Dimensions-September-23-2026/paper.pdf
- source_scope_note: lean/docs/365.md
- source_field: Analysis
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ScalarConductivity

abbrev R3 := EuclideanSpace ℝ (Fin 3)
abbrev JetFiber := EuclideanSpace ℝ (Fin 4)
def ball : Set R3 := Metric.ball 0 3
def ballMeasure : Measure R3 := volume.restrict ball
abbrev JetSpace := Lp JetFiber 2 ballMeasure

def smoothJet (f : R3 → ℝ) (x : R3) : JetFiber :=
  WithLp.toLp 2 (Fin.cases (f x) (fun i => gradient f x i))

def smoothJets : Set JetSpace :=
  { z | ∃ (f : R3 → ℝ) (_ : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
      (hf : MemLp (smoothJet f) 2 ballMeasure), z = hf.toLp (smoothJet f) }

def compactSmoothJets : Set JetSpace :=
  { z | ∃ (f : R3 → ℝ) (_ : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
      (_ : HasCompactSupport f) (_ : tsupport f ⊆ ball)
      (hf : MemLp (smoothJet f) 2 ballMeasure), z = hf.toLp (smoothJet f) }

def H1Space : Submodule ℝ JetSpace :=
  (Submodule.span ℝ smoothJets).topologicalClosure
abbrev H1 := H1Space

def zeroTraceAmbient : Submodule ℝ JetSpace :=
  (Submodule.span ℝ compactSmoothJets).topologicalClosure

def H10 : Submodule ℝ H1 := zeroTraceAmbient.comap H1Space.subtype

instance H10_isClosed : IsClosed (H10 : Set H1) := by
  exact (Submodule.isClosed_topologicalClosure
    (Submodule.span ℝ compactSmoothJets)).preimage continuous_subtype_val

abbrev TraceSpace := H1 ⧸ H10
abbrev TraceDual := TraceSpace →L[ℝ] ℝ
abbrev DNOperator := TraceSpace →L[ℝ] TraceDual

def trace (u : H1) : TraceSpace := H10.mkQ u

def weakGradient (u : H1) (x : R3) : R3 :=
  WithLp.toLp 2 (fun i => (u.val x) i.succ)

def energy (γ : R3 → ℝ) (u v : H1) : ℝ :=
  ∫ x, γ x * inner ℝ (weakGradient u x) (weakGradient v x) ∂ballMeasure

def Harmonic (γ : R3 → ℝ) (u : H1) : Prop :=
  ∀ h : H1, h ∈ H10 → energy γ u h = 0

def IsDirichletToNeumann (γ : R3 → ℝ) (Λ : DNOperator) : Prop :=
  ∀ f : TraceSpace, ∃ u : H1,
    trace u = f ∧ Harmonic γ u ∧
    (∀ u' : H1, trace u' = f → Harmonic γ u' → u' = u) ∧
    ∀ v : H1, Λ f (trace v) = energy γ u v

def EqualOneNearBoundary (γ : R3 → ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ r < 3 ∧ ∀ᵐ x ∂ballMeasure, r < ‖x‖ → γ x = 1

def MainStatement : Prop :=
  ∃ (γ₀ γ₁ : R3 → ℝ) (c C : ℝ) (Λ : DNOperator),
    0 < c ∧ c < C ∧
    Measurable γ₀ ∧ Measurable γ₁ ∧
    MemLp γ₀ ∞ ballMeasure ∧ MemLp γ₁ ∞ ballMeasure ∧
    (∀ᵐ x ∂ballMeasure, c ≤ γ₀ x ∧ γ₀ x ≤ C) ∧
    (∀ᵐ x ∂ballMeasure, c ≤ γ₁ x ∧ γ₁ x ≤ C) ∧
    EqualOneNearBoundary γ₀ ∧ EqualOneNearBoundary γ₁ ∧
    0 < ballMeasure {x | γ₀ x ≠ γ₁ x} ∧
    IsDirichletToNeumann γ₀ Λ ∧ IsDirichletToNeumann γ₁ Λ

def main_nonuniqueness_statement : Prop :=
  MainStatement

end ScalarConductivity
end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.ScalarConductivity.main_nonuniqueness_statement

end Problem

/- Formalization scope, from lean/docs/365.md: The Calderón inverse problem asks whether boundary measurements determine an interior conductivity. The formalized result gives nonuniqueness for bounded measurable scalar conductivities on the ball $B(0,3)\subset\mathbb R^3$: two uniformly positive conductivities differ on a set of positive volume, equal $1$ near the boundary, and have the same full weak Dirichlet-to-Neumann operator. Weak solutions exist uniquely for every boundary trace. -/
