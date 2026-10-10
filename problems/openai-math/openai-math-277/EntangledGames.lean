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

- problem_id: EntangledGames
- collection: openai-math
- question_id: openai-math:277
- source: openai-math
- source_locator: lean/ComparatorChallenges/EntangledGames.lean#OAI.ThresholdParallelRepetition.threshold_parallel_repetition
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves exponential threshold repetition for every finite two-player one-round game: if its entangled value is v &lt; 1, the probability of winning at least a fraction $`v+\delta`$ of k independent repetitions decays exponentially in k, for $`0\lt \delta\lt 1-v`$. Arbitrary joint finite-dimensional entangled strategies and correlated question distributions are allowed. ([Lean](lean/docs/277.md)) For every finite two-player game with entangled value v &lt; 1, we prove exponential decay for the probability of winning at least a $`v+\delta`$ fraction of k independent repetitions, uniformly over all finite-dimensional joint strategies. The result allows arbitrary correlated question distributions and holds for every $`0\lt \delta\lt 1-v`$ and k ≥ 1. Its universal rate is proportional to $`\delta^5/(1+\log(|\mathcal A||\mathcal B|))`$, where $`\mathcal A,\mathcal B`$ are the answer alphabets. For each fixed question distribution, we also obtain an explicit cubic rate in δ.
- notes: OpenAI math result family 277, Threshold repetition for entangled games -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/277.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.ThresholdParallelRepetition.threshold_parallel_repetition
- source_theorem_count: 1
- source_solution_module: OAI.Probability.EntangledGames.Main
- source_main_result: OAI.ThresholdParallelRepetition.threshold_parallel_repetition
- source_papers: preprints/Threshold-parallel-repetition-for-finite-dimensional-entangled-games-September-25-2026/paper.pdf
- source_scope_note: lean/docs/277.md
- source_field: Probability
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder

namespace ThresholdParallelRepetition

structure Game (x y a b : ℕ) where
  questionProb : Fin (x + 1) × Fin (y + 1) → ℝ
  questionProb_nonneg : ∀ z, 0 ≤ questionProb z
  questionProb_sum : ∑ z, questionProb z = 1
  accepts : Fin (x + 1) → Fin (y + 1) → Fin (a + 1) → Fin (b + 1) → Bool

structure Strategy (X Y A B : Type) [Fintype A] [Fintype B] where
  dimA : ℕ
  dimB : ℕ
  state : Fin (dimA + 1) × Fin (dimB + 1) → ℂ
  state_unit : ∑ i, Complex.normSq (state i) = 1
  alice : X → A → Matrix (Fin (dimA + 1)) (Fin (dimA + 1)) ℂ
  bob : Y → B → Matrix (Fin (dimB + 1)) (Fin (dimB + 1)) ℂ
  alice_pos : ∀ x a, (alice x a).PosSemidef
  bob_pos : ∀ y b, (bob y b).PosSemidef
  alice_total : ∀ x, ∑ a, alice x a = 1
  bob_total : ∀ y, ∑ b, bob y b = 1

def Strategy.born {X Y A B : Type} [Fintype A] [Fintype B]
    (S : Strategy X Y A B) (x : X) (y : Y) (a : A) (b : B) : ℝ :=
  ∑ i, ∑ j, (star (S.state i) *
    (S.alice x a i.1 j.1 * S.bob y b i.2 j.2) * S.state j).re

abbrev SingleStrategy (x y a b : ℕ) :=
  Strategy (Fin (x + 1)) (Fin (y + 1)) (Fin (a + 1)) (Fin (b + 1))

def successProbability {x y a b : ℕ} (G : Game x y a b) (S : SingleStrategy x y a b) : ℝ :=
  ∑ z : Fin (x + 1) × Fin (y + 1), G.questionProb z *
    ∑ w : Fin (a + 1) × Fin (b + 1),
      if G.accepts z.1 z.2 w.1 w.2 then S.born z.1 z.2 w.1 w.2 else 0

def entangledValue {x y a b : ℕ} (G : Game x y a b) : ℝ :=
  sSup (Set.range (successProbability G))

abbrev RepeatedStrategy (x y a b k : ℕ) :=
  Strategy (Fin k → Fin (x + 1)) (Fin k → Fin (y + 1))
    (Fin k → Fin (a + 1)) (Fin k → Fin (b + 1))

def wins {x y a b k : ℕ} (G : Game x y a b)
    (xs : Fin k → Fin (x + 1)) (ys : Fin k → Fin (y + 1))
    (as : Fin k → Fin (a + 1)) (bs : Fin k → Fin (b + 1)) : ℕ :=
  ∑ i, if G.accepts (xs i) (ys i) (as i) (bs i) then 1 else 0

def thresholdProbability {x y a b k : ℕ} (G : Game x y a b) (δ : ℝ)
    (S : RepeatedStrategy x y a b k) : ℝ :=
  ∑ xs : Fin k → Fin (x + 1), ∑ ys : Fin k → Fin (y + 1),
    (∏ i, G.questionProb (xs i, ys i)) *
      ∑ as : Fin k → Fin (a + 1), ∑ bs : Fin k → Fin (b + 1),
        if ⌈(entangledValue G + δ) * (k : ℝ)⌉₊ ≤ wins G xs ys as bs
        then S.born xs ys as bs else 0

def thresholdValue {x y a b k : ℕ} (G : Game x y a b) (δ : ℝ) : ℝ :=
  sSup (Set.range (thresholdProbability (k := k) G δ))

def threshold_parallel_repetition_statement : Prop :=
  ∃ κ₀ : ℝ, 0 < κ₀ ∧
      ∀ (x y a b : ℕ) (G : Game x y a b), entangledValue G < 1 →
      ∀ (δ : ℝ), 0 < δ → δ < 1 - entangledValue G →
      ∀ (k : ℕ), 1 ≤ k →
        (∀ S : RepeatedStrategy x y a b k,
          thresholdProbability G δ S ≤
            Real.exp (-κ₀ * δ ^ 13 / (1 + Real.log (((a + 1) * (b + 1) : ℕ) : ℝ)) * k)) ∧
        thresholdValue (k := k) G δ ≤
          Real.exp (-κ₀ * δ ^ 13 / (1 + Real.log (((a + 1) * (b + 1) : ℕ) : ℝ)) * k)

end ThresholdParallelRepetition

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.ThresholdParallelRepetition.threshold_parallel_repetition_statement

end Problem

/- Formalization scope, from lean/docs/277.md: The formalization gives exponential threshold parallel repetition for every finite two-player game with arbitrary correlated questions. If its finite-dimensional entangled value is $v<1$, its answer sets are $A,B$, and $0<\delta<1-v$, then the probability of winning at least the fraction $v+\delta$ of $k$ repetitions is at most $\exp(-\kappa\delta^{13}k/(1+\log(|A||B|)))$ for one universal $\kappa>0$. The bound applies to every joint finite-dimensional strategy and to their supremum, without assuming attainment. The separate distribution-dependent cubic bound is outside this scope. -/
