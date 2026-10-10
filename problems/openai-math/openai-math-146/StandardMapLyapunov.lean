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

- problem_id: StandardMapLyapunov
- collection: openai-math
- question_id: openai-math:146
- source: openai-math
- source_locator: lean/ComparatorChallenges/StandardMapLyapunov.lean#OAI.StandardMapEntropy.main_entropy_complete
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves that the standard sine map on the two-dimensional torus has positive metric entropy with respect to area for every sufficiently large positive parameter. This establishes Sinai's positive-parameter-measure conjecture for the original family, with the stronger conclusion of a full parameter tail. ([Lean](lean/docs/146.md)) We prove that the standard sine map of the two-dimensional torus has positive metric entropy with respect to normalized area for every sufficiently large positive parameter. This gives a full parameter tail, and hence answers Sinai's positive-parameter-measure conjecture affirmatively.
- notes: OpenAI math result family 146, Positive metric entropy for the standard map -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/146.md
- track: solved
- answer_shape: proof
- context_lemmas: sine_periodic cosine_periodic
- source_theorem: OAI.StandardMapEntropy.main_entropy_complete
- source_theorem_count: 1
- source_solution_module: OAI.Dynamics.StandardMap.EntropyLyapunov
- source_papers: preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/paper.pdf
- source_scope_note: lean/docs/146.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace StandardMapEntropy

abbrev Circle := AddCircle (1 : ℝ)
abbrev Torus := Circle × Circle

lemma sine_periodic : Function.Periodic (fun x : ℝ => Real.sin (2 * Real.pi * x)) 1 := by
  intro x
  dsimp only
  rw [show 2 * Real.pi * (x + 1) = 2 * Real.pi * x + 2 * Real.pi by ring]
  exact Real.sin_add_two_pi _

noncomputable def sine (x : Circle) : ℝ := sine_periodic.lift x

noncomputable def standardMap (k : ℝ) (z : Torus) : Torus :=
  (z.1 + z.2 + (k * sine z.1 : ℝ), z.2 + (k * sine z.1 : ℝ))

noncomputable def area : Measure Torus :=
  (volume : Measure Circle).prod (volume : Measure Circle)

def FinitePartition (r : ℕ) := { p : Torus → Fin (r + 1) // Measurable p }

def blockAtom {r : ℕ} (f : Torus → Torus) (p : FinitePartition r)
    (n : ℕ) (w : Fin n → Fin (r + 1)) : Set Torus :=
  { z | ∀ i : Fin n, p.val (f^[i.val] z) = w i }

noncomputable def blockEntropy {r : ℕ} (μ : Measure Torus) (f : Torus → Torus)
    (p : FinitePartition r) (n : ℕ) : ℝ :=
  - ∑ w : Fin n → Fin (r + 1),
    (μ (blockAtom f p n w)).toReal * Real.log (μ (blockAtom f p n w)).toReal

noncomputable def partitionEntropy {r : ℕ} (μ : Measure Torus) (f : Torus → Torus)
    (p : FinitePartition r) : ℝ≥0∞ :=
  ⨅ n : ℕ, ENNReal.ofReal (blockEntropy μ f p (n + 1) / (n + 1 : ℝ))

noncomputable def metricEntropy (μ : Measure Torus) (f : Torus → Torus) : ℝ≥0∞ :=
  ⨆ r : ℕ, ⨆ p : FinitePartition r, partitionEntropy μ f p

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

lemma cosine_periodic : Function.Periodic (fun x : ℝ => Real.cos (2*Real.pi*x)) 1 := by
  intro x
  dsimp only
  rw [show 2*Real.pi*(x+1)=2*Real.pi*x+2*Real.pi by ring]
  exact Real.cos_add_two_pi _
noncomputable def cosine (x : Circle) : ℝ := cosine_periodic.lift x

noncomputable def torusPotential (k : ℝ) (x : Circle) : ℝ := 2+(2*Real.pi*k)*cosine x

noncomputable def transferStep (v : ℝ) : ℂ →L[ℝ] ℂ :=
  { toLinearMap :=
      { toFun := fun z => ⟨v*z.re-z.im,z.re⟩
        map_add' := by intro z w; apply Complex.ext <;> simp; ring
        map_smul' := by intro t z; apply Complex.ext <;> simp; ring }
    cont := by
      exact Complex.equivRealProdCLM.symm.continuous.comp
        (((continuous_const.mul Complex.continuous_re).sub Complex.continuous_im).prodMk Complex.continuous_re) }

noncomputable def tangentCoordinates : ℂ →L[ℝ] ℂ :=
  { toLinearMap :=
      { toFun := fun z => ⟨z.re, z.re-z.im⟩
        map_add' := by intro z w; apply Complex.ext <;> simp; ring
        map_smul' := by intro t z; apply Complex.ext <;> simp; ring }
    cont := Complex.equivRealProdCLM.symm.continuous.comp
      (Complex.continuous_re.prodMk (Complex.continuous_re.sub Complex.continuous_im)) }

local instance realTangentCompTriple :
    RingHomCompTriple (RingHom.id ℝ) (RingHom.id ℝ) (RingHom.id ℝ) := inferInstance

noncomputable def standardDerivative (k : ℝ) (z : Torus) : ℂ →L[ℝ] ℂ :=
  tangentCoordinates.comp ((transferStep (torusPotential k z.1)).comp tangentCoordinates)

noncomputable def standardDerivativeProduct (k : ℝ) (z : Torus) (n : ℕ) : ℂ →L[ℝ] ℂ :=
  Nat.rec (ContinuousLinearMap.id ℝ ℂ)
    (fun i A => (standardDerivative k ((standardMap k)^[i] z)).comp A) n

noncomputable def wedge (z w : ℂ) : ℝ := z.re * w.im - z.im * w.re

def VectorGrowth (k : ℝ) (z : Torus) (v : ℂ) (l : ℝ) : Prop :=
  v ≠ 0 ∧ Tendsto (fun n : ℕ => Real.log ‖standardDerivativeProduct k z n v‖ / (n : ℝ))
    atTop (𝓝 l)

def LyapunovSpectrumAt (k : ℝ) (z : Torus) (l : ℝ) : Prop :=
  0 ≤ l ∧ ((l = 0 ∧ ∀ v : ℂ, v ≠ 0 → VectorGrowth k z v 0) ∨
    (0 < l ∧ ∃ s : ℂ, s ≠ 0 ∧ ∀ v : ℂ, v ≠ 0 →
      VectorGrowth k z v (if wedge s v = 0 then -l else l)))

def PositiveLargestLyapunov (k : ℝ) : Prop :=
  ∃ E : Set Torus, MeasurableSet E ∧ 0 < area E ∧
    ∀ z ∈ E, ∃ l : ℝ, 0 < l ∧ LyapunovSpectrumAt k z l ∧
      Tendsto
        (fun n : ℕ => Real.log ‖standardDerivativeProduct k z n‖ / (n : ℝ))
        atTop (𝓝 l)

def main_entropy_complete_statement : Prop :=
  ∃ k₀ : ℝ, 0 < k₀ ∧ ∀ k : ℝ, k₀ ≤ k →
      0 < metricEntropy area (standardMap k) ∧
      PositiveLargestLyapunov k ∧
      (0 < metricEntropy area (standardMap k) ↔ PositiveLargestLyapunov k)

end StandardMapEntropy

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.StandardMapEntropy.main_entropy_complete_statement

end Problem

/- Formalization scope, from lean/docs/146.md: The formalization proves Sinai's positive-entropy conjecture for the standard sine map on the two-dimensional torus in the stronger form of a full positive parameter tail. For every sufficiently large parameter, normalized area has positive metric entropy, and a positive-area set has positive largest Lyapunov exponent with the stated derivative-growth limit. It also constructs a positive-area invariant ergodic hyperbolic component. That component splits into finitely many cyclic pieces on each of which the corresponding iterate is Bernoulli. No genericity assumption on the parameter is used. -/
