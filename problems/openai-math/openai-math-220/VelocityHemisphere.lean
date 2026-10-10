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

- problem_id: VelocityHemisphere
- collection: openai-math
- question_id: openai-math:220
- source: openai-math
- source_locator: lean/ComparatorChallenges/VelocityHemisphere.lean#OAI.DirectionalTransience.positive_probability_transience_velocity_hemisphere
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: On ℤd, d ≥ 3, directional escape has probability zero or one for iid strictly elliptic nearest-neighbor environments, and for stationary ergodic finite-range-dependent environments under uniform ellipticity. In iid uniformly elliptic environments with d ≥ 2, almost-sure directional transience implies a deterministic limiting velocity with positive projection in that direction, resolving the ballisticity conjecture. ([Lean](lean/docs/220.md)) We prove the directional zero–one conjecture for nearest-neighbor random walks in independent and identically distributed strictly elliptic environments on ℤd, d ≥ 3: the probability of escape in each fixed nonzero real direction is zero or one. Only strict positivity of the transition probabilities is required; no uniform lower bound or moment assumption is imposed. We prove that almost-sure transience in a fixed direction implies a deterministic limiting velocity with positive projection in that direction for nearest-neighbor random walks in independent and identically distributed uniformly elliptic environments on ℤd, d ≥ 2. This resolves the ballisticity conjecture positively.
- notes: OpenAI math result family 220, Directional zero–one laws beyond iid environments and iid ballisticity -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/220.md
- track: solved
- answer_shape: proof
- context_lemmas: measurable_current_row
- source_theorem: OAI.DirectionalTransience.positive_probability_transience_velocity_hemisphere
- source_theorem_count: 1
- source_solution_module: OAI.Probability.Ballisticity.VelocityHemisphere
- source_papers: preprints/A-directional-zero-one-law-under-strict-ellipticity-September-23-2026/paper.pdf preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf
- source_scope_note: lean/docs/220.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace DirectionalTransience

abbrev Lattice (d : ℕ) := Fin d → ℤ
abbrev Direction (d : ℕ) := Fin d × Bool
abbrev Vector (d : ℕ) := Fin d → ℝ
abbrev Row (d : ℕ) := {p : Direction d → ℝ≥0 // ∑ e, p e = 1}
abbrev Environment (d : ℕ) := Lattice d → Row d
abbrev State (d : ℕ) := Environment d × Lattice d
abbrev Path (d : ℕ) := ℕ → Lattice d

def step {d : ℕ} (e : Direction d) : Lattice d :=
  fun i => if i = e.1 then (if e.2 then 1 else -1) else 0

noncomputable def environmentLaw {d : ℕ} (ν : Measure (Row d)) :
    Measure (Environment d) := Measure.infinitePi (fun _ => ν)

def UniformElliptic {d : ℕ} (ν : Measure (Row d)) : Prop :=
  ∃ κ : ℝ≥0, 0 < κ ∧ ∀ᵐ p ∂ν, ∀ e, κ ≤ p.1 e

lemma measurable_current_row {d : ℕ} :
    Measurable (fun z : State d => z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro x
  exact measurable_pi_apply x

noncomputable def transition {d : ℕ} : Kernel (State d) (State d) where
  toFun z := ∑ e : Direction d,
    ((z.1 z.2).1 e : ℝ≥0∞) • Measure.dirac (z.1, z.2 + step e)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    apply Finset.measurable_fun_sum
    intro e _
    apply Measurable.mul
    · exact (measurable_pi_apply e |>.comp
        (measurable_subtype_coe.comp measurable_current_row)).coe_nnreal_ennreal
    · exact (Measure.measurable_coe hs).comp
        (Measure.measurable_dirac.comp (measurable_fst.prodMk
          (measurable_snd.add_const (step e))))

instance transition_markov {d : ℕ} : IsMarkovKernel (transition (d := d)) where
  isProbabilityMeasure z := by
    constructor
    change (∑ e : Direction d,
      ((z.1 z.2).1 e : ℝ≥0∞) • Measure.dirac (z.1, z.2 + step e)) Set.univ = 1
    simp only [Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply_of_mem
      (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofNNReal_finsetSum, (z.1 z.2).2]
    rfl

noncomputable def historyTransition {d : ℕ} (n : ℕ) :
    Kernel ((i : Finset.Iic n) → State d) (State d) where
  toFun z := transition (z ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
  measurable' := transition.measurable.comp (measurable_pi_apply _)

instance historyTransition_markov {d : ℕ} (n : ℕ) :
    IsMarkovKernel (historyTransition (d := d) n) where
  isProbabilityMeasure _ := transition_markov.isProbabilityMeasure _

noncomputable def initialLaw {d : ℕ} (ν : Measure (Row d)) : Measure (State d) :=
  (environmentLaw ν).map (fun ω => (ω, (0 : Lattice d)))

noncomputable def annealedLaw {d : ℕ} (ν : Measure (Row d)) : Measure (Path d) :=
  (@Kernel.trajMeasure (fun _ => State d) _ (initialLaw ν) (historyTransition (d := d)) _).map
    (fun z n => (z n).2)

def dot {d : ℕ} (v ℓ : Vector d) : ℝ := ∑ i, v i * ℓ i

def realPosition {d : ℕ} (x : Lattice d) : Vector d := fun i => (x i : ℝ)

def TransientPaths {d : ℕ} (ℓ : Vector d) : Set (Path d) :=
  {X | Tendsto (fun n => dot (realPosition (X n)) ℓ) atTop atTop}

def VelocityPaths {d : ℕ} (v : Vector d) : Set (Path d) :=
  {X | Tendsto (fun n : ℕ => fun i => (X n i:ℝ)/(n:ℝ)) atTop (𝓝 v)}

def positive_probability_transience_velocity_hemisphere_statement : Prop :=
  ∀ {d : ℕ} (hd : 3 ≤ d) (ν : Measure (Row d)) [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : ℓ ≠ 0) (hpos : 0 < annealedLaw ν (TransientPaths ℓ)),
    ∃ v : Vector d,
      v ≠ 0 ∧ 0 < dot v ℓ ∧ annealedLaw ν (VelocityPaths v) = 1 ∧
      (∀ w : Vector d, annealedLaw ν (VelocityPaths w) = 1 → w = v) ∧
      {u : Vector d | dot u u = 1 ∧ annealedLaw ν (TransientPaths u) = 1} =
        {u : Vector d | dot u u = 1 ∧ 0 < annealedLaw ν (TransientPaths u)} ∧
      {u : Vector d | dot u u = 1 ∧ 0 < annealedLaw ν (TransientPaths u)} =
        {u : Vector d | dot u u = 1 ∧ 0 < dot v u} ∧
      (∀ u : Vector d, dot u u = 1 → dot v u ≤ 0 →
        annealedLaw ν (TransientPaths u) = 0)

end DirectionalTransience

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.DirectionalTransience.positive_probability_transience_velocity_hemisphere_statement

end Problem

/- Formalization scope, from lean/docs/220.md: The directional zero–one conjecture asks whether a random walk's probability of escape in a fixed direction must be zero or one. The formalization proves this for nearest-neighbor walks in independent identically distributed strictly elliptic environments on $\mathbb Z^d$, for every $d\ge3$ and every nonzero real direction. Strict ellipticity means that every allowed transition probability is positive almost surely; no uniform positive lower bound or moment condition is assumed. The probability is the annealed law from the origin. For an i.i.d. uniformly elliptic nearest-neighbor random environment on $\mathbb Z^d$, the formalization proves that almost-sure directional transience implies convergence of $X_n/n$ to a deterministic velocity with positive projection in that direction for every $d\ge2$. For $d\ge3$, positive probability of transience in any nonzero direction already suffices. The limiting velocity is unique, and the unit directions with positive transience probability are exactly the open hemisphere having positive inner product with that velocity; transience has probability one on that hemisphere and zero on its complement. The environment is sampled once and retained along the walk, and the probabilities use the annealed law from the origin. -/
