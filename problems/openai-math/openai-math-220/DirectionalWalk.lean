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

- problem_id: DirectionalWalk
- collection: openai-math
- question_id: openai-math:220
- source: openai-math
- source_locator: lean/ComparatorChallenges/DirectionalWalk.lean#OAI.DirectionalZeroOne.directional_zero_one
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: On ℤd, d ≥ 3, directional escape has probability zero or one for iid strictly elliptic nearest-neighbor environments, and for stationary ergodic finite-range-dependent environments under uniform ellipticity. In iid uniformly elliptic environments with d ≥ 2, almost-sure directional transience implies a deterministic limiting velocity with positive projection in that direction, resolving the ballisticity conjecture. ([Lean](lean/docs/220.md)) We prove the directional zero–one conjecture for nearest-neighbor random walks in independent and identically distributed strictly elliptic environments on ℤd, d ≥ 3: the probability of escape in each fixed nonzero real direction is zero or one. Only strict positivity of the transition probabilities is required; no uniform lower bound or moment assumption is imposed. We prove that almost-sure transience in a fixed direction implies a deterministic limiting velocity with positive projection in that direction for nearest-neighbor random walks in independent and identically distributed uniformly elliptic environments on ℤd, d ≥ 2. This resolves the ballisticity conjecture positively.
- notes: OpenAI math result family 220, Directional zero–one laws beyond iid environments and iid ballisticity -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/220.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.DirectionalZeroOne.directional_zero_one
- source_theorem_count: 1
- source_solution_module: OAI.Probability.DirectionalWalk.Main
- source_papers: preprints/A-directional-zero-one-law-under-strict-ellipticity-September-23-2026/paper.pdf preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf
- source_scope_note: lean/docs/220.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

abbrev Site (d : ℕ) := Fin d → ℤ
abbrev Step (d : ℕ) := Fin d × Bool

def stepVector {d : ℕ} (e : Step d) : Site d :=
  fun i => if i = e.1 then (if e.2 then 1 else -1) else 0

def Row (d : ℕ) :=
  {p : Step d → ℝ // (∀ e, p e ∈ Set.Icc (0 : ℝ) 1) ∧ ∑ e, p e = 1}

instance (d : ℕ) : MeasurableSpace (Row d) := inferInstanceAs
  (MeasurableSpace {p : Step d → ℝ //
    (∀ e, p e ∈ Set.Icc (0 : ℝ) 1) ∧ ∑ e, p e = 1})

abbrev Environment (d : ℕ) := Site d → Row d
abbrev Path (d : ℕ) := ℕ → Site d
abbrev State (d : ℕ) := Environment d × Site d

def StrictEllipticity {d : ℕ} (μ : Measure (Row d)) : Prop :=
  ∀ᵐ p ∂μ, ∀ e, 0 < p.val e

noncomputable def environmentLaw {d : ℕ} (μ : Measure (Row d))
    [IsProbabilityMeasure μ] : Measure (Environment d) :=
  Measure.infinitePi (fun _ => μ)

noncomputable def transition (d : ℕ) : Kernel (State d) (State d) where
  toFun s := ∑ e : Step d,
    ENNReal.ofReal ((s.1 s.2).val e) • Measure.dirac (s.1, s.2 + stepVector e)
  measurable' := by
    apply measurable_from_prod_countable_left
    intro x
    apply Finset.measurable_sum
    intro e he
    apply Measure.measurable_of_measurable_coe
    intro t ht
    simp only [Measure.smul_apply, smul_eq_mul]
    apply Measurable.mul
    · exact (measurable_pi_apply e |>.comp
        (measurable_subtype_coe.comp (measurable_pi_apply x))).ennreal_ofReal
    · exact (Measure.measurable_coe ht).comp
        (Measure.measurable_dirac.comp (measurable_id.prodMk measurable_const))

instance (d : ℕ) : IsMarkovKernel (transition d) where
  isProbabilityMeasure s := by
    constructor
    change (∑ e : Step d,
      ENNReal.ofReal ((s.1 s.2).val e) •
        Measure.dirac (s.1, s.2 + stepVector e)) Set.univ = 1
    simp only [Measure.finsetSum_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · rw [(s.1 s.2).property.2, ENNReal.ofReal_one]
    · intro e he
      exact ((s.1 s.2).property.1 e).1

noncomputable def historyKernel (d n : ℕ) :
    Kernel ((i : Finset.Iic n) → State d) (State d) :=
  (transition d).comap (fun h => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
    (measurable_pi_apply _)

instance (d n : ℕ) : IsMarkovKernel (historyKernel d n) := by
  unfold historyKernel
  infer_instance

noncomputable def initialLaw {d : ℕ} (μ : Measure (Row d))
    [IsProbabilityMeasure μ] (x : Site d) : Measure (State d) :=
  (environmentLaw μ).map (fun ω => (ω, x))

noncomputable def annealed {d : ℕ} (μ : Measure (Row d))
    [IsProbabilityMeasure μ] (x : Site d) : Measure (Path d) :=
  (Kernel.trajMeasure (X := fun _ => State d) (initialLaw μ x) (historyKernel d)).map
    (fun z n => (z n).2)

def escape {d : ℕ} (ℓ : Fin d → ℝ) : Set (Path d) :=
  {X | Tendsto (fun n => ∑ i, (X n i : ℝ) * ℓ i) atTop atTop}

def directional_zero_one_statement : Prop :=
  ∀ (d : ℕ) (hd : 3 ≤ d) (μ : Measure (Row d)) [IsProbabilityMeasure μ] (hell : StrictEllipticity μ) (ℓ : Fin d → ℝ) (hℓ : ℓ ≠ 0),
    annealed μ 0 (escape ℓ) = 0 ∨ annealed μ 0 (escape ℓ) = 1

end DirectionalZeroOne

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.DirectionalZeroOne.directional_zero_one_statement

end Problem

/- Formalization scope, from lean/docs/220.md: The directional zero–one conjecture asks whether a random walk's probability of escape in a fixed direction must be zero or one. The formalization proves this for nearest-neighbor walks in independent identically distributed strictly elliptic environments on $\mathbb Z^d$, for every $d\ge3$ and every nonzero real direction. Strict ellipticity means that every allowed transition probability is positive almost surely; no uniform positive lower bound or moment condition is assumed. The probability is the annealed law from the origin. For an i.i.d. uniformly elliptic nearest-neighbor random environment on $\mathbb Z^d$, the formalization proves that almost-sure directional transience implies convergence of $X_n/n$ to a deterministic velocity with positive projection in that direction for every $d\ge2$. For $d\ge3$, positive probability of transience in any nonzero direction already suffices. The limiting velocity is unique, and the unit directions with positive transience probability are exactly the open hemisphere having positive inner product with that velocity; transience has probability one on that hemisphere and zero on its complement. The environment is sampled once and retained along the walk, and the probabilities use the annealed law from the origin. -/
