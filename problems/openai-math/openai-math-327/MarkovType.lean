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

- problem_id: MarkovType
- collection: openai-math
- question_id: openai-math:327
- source: openai-math
- source_locator: lean/ComparatorChallenges/MarkovType.lean#OAI.MarkovSuperreflexivity.hasNontrivialMarkovType_iff_hasEquivalentUCNorm
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves that every real Banach space with Markov type p for some p &gt; 1 admits an equivalent uniformly convex norm, answering Naor's renorming question. Together with the known converse, this characterizes superreflexivity by nontrivial Markov type. ([Lean](lean/docs/327.md)) We prove that every real Banach space with Markov type p &gt; 1 is superreflexive. Together with the known converse, this characterizes superreflexivity by nontrivial Markov type. This answers Naor's question: every real Banach space with nontrivial Markov type admits an equivalent uniformly smooth norm.
- notes: OpenAI math result family 327, Markov type characterizes superreflexivity -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/327.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.MarkovSuperreflexivity.hasNontrivialMarkovType_iff_hasEquivalentUCNorm
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.MarkovType.Main
- source_main_result: OAI.MarkovSuperreflexivity.hasNontrivialMarkovType_iff_hasEquivalentUCNorm
- source_papers: preprints/Nontrivial-Markov-Type-Forces-Superreflexivity-September-23-2026/paper.pdf
- source_scope_note: lean/docs/327.md
- source_field: Analysis
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

structure FiniteReversibleChain (S : Type*) [Fintype S] where
  π : S → ℝ
  P : S → S → ℝ
  π_nonneg : ∀ s, 0 ≤ π s
  sum_π : ∑ s, π s = 1
  P_nonneg : ∀ s t, 0 ≤ P s t
  sum_P : ∀ s, ∑ t, P s t = 1
  balance : ∀ s t, π s * P s t = π t * P t s

abbrev StatePath (S : Type*) (n : ℕ) := Fin (n + 1) → S

def pathWeight {S : Type*} [Fintype S]
    (C : FiniteReversibleChain S) (n : ℕ) (ω : StatePath S n) : ℝ :=
  C.π (ω 0) * ∏ i : Fin n, C.P (ω i.castSucc) (ω i.succ)

def stateCost {S X : Type*} [Fintype S] [NormedAddCommGroup X]
    (C : FiniteReversibleChain S) (f : S → X) (p : ℝ) (n : ℕ) : ℝ :=
  ∑ ω : StatePath S n,
    pathWeight C n ω * Real.rpow (‖f (ω (Fin.last n)) - f (ω 0)‖) p

def MarkovTypeWith (p K : ℝ) (X : Type*) [NormedAddCommGroup X] : Prop :=
  0 < p ∧ 0 < K ∧
    ∀ (m : ℕ) (C : FiniteReversibleChain (Fin m)) (f : Fin m → X) (n : ℕ),
      1 ≤ n → stateCost C f p n ≤ Real.rpow K p * (n : ℝ) * stateCost C f p 1

def HasMarkovType (p : ℝ) (X : Type*) [NormedAddCommGroup X] : Prop :=
  ∃ K : ℝ, MarkovTypeWith p K X

def HasNontrivialMarkovType (X : Type*) [NormedAddCommGroup X] : Prop :=
  ∃ p : ℝ, 1 < p ∧ HasMarkovType p X

section

universe u

variable (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]

structure EquivalentNorm where
  p : Seminorm ℝ X
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  upper_pos : 0 < upper
  lower_bound : ∀ x, lower * ‖x‖ ≤ p x
  upper_bound : ∀ x, p x ≤ upper * ‖x‖

variable {X}

def UniformConvex (p : Seminorm ℝ X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 2 → ∃ δ : ℝ, 0 < δ ∧
    ∀ x y : X, p x ≤ 1 → p y ≤ 1 → ε ≤ p (x - y) →
      p ((1 / 2 : ℝ) • (x + y)) ≤ 1 - δ

def HasEquivalentUCNorm (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∃ N : EquivalentNorm X, UniformConvex N.p

end

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def hasNontrivialMarkovType_iff_hasEquivalentUCNorm_statement : Prop :=
  ∀ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X],
    HasNontrivialMarkovType X ↔ HasEquivalentUCNorm X

end MarkovSuperreflexivity

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u_1} : Prop :=
  _root_.OAI.MarkovSuperreflexivity.hasNontrivialMarkovType_iff_hasEquivalentUCNorm_statement.{u_1}

end Problem

/- Formalization scope, from lean/docs/327.md: The formalized result proves that a real Banach space has nontrivial Markov type exactly when it admits an equivalent uniformly convex norm, hence exactly when it is superreflexive. Nontrivial Markov type means a uniform Markov-type bound for some exponent $p>1$ over all finite stationary reversible chains and all positive times. The exponent and equivalent norm may depend on the space, and the zero space is included. Additional formalized consequences concern uniformly smooth renormings and reflexivity of finitely representable spaces. -/
