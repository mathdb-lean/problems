import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.RingTheory.Finiteness.Defs
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

- problem_id: RealL1Renorming
- collection: openai-math
- question_id: openai-math:330
- source: openai-math
- source_locator: lean/ComparatorChallenges/RealL1Renorming.lean#OAI.DiscreteFree.real_l1_quantitative_renorming
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs a countable uniformly discrete metric space whose real Lipschitz-free Banach space has the approximation property but not the bounded approximation property, answering Kalton's question negatively. Finite-rank operators approximate the identity on every compact set, but their norms cannot share a finite bound. ([Lean](lean/docs/330.md)) We construct a countable uniformly discrete metric space whose real Lipschitz-free space has the approximation property but fails the bounded approximation property, answering Kalton's question negatively. The identity can be approximated on every compact set by finite-rank operators, but no uniform bound on their norms is possible.
- notes: OpenAI math result family 330, A uniformly discrete counterexample to bounded approximation in Lipschitz-free spaces -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/330.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.DiscreteFree.real_l1_quantitative_renorming
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.LipschitzFree.Renorming
- source_papers: preprints/Failure-of-Bounded-Approximation-in-a-Lipschitz-Free-Space-over-a-Uniformly-Discrete-Metric-Space-September-26-2026/main.pdf
- source_scope_note: lean/docs/330.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

/-!
# Quantitative renorming of real ℓ¹ with fixed vector-space operations
-/

open scoped BigOperators ENNReal

namespace DiscreteFree

variable {M : Type*} [MetricSpace M]

def HasBAP (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (Λ : ℝ) : Prop :=
  ∀ C : Set X, IsCompact C → ∀ ε : ℝ, 0 < ε →
    ∃ T : X →L[ℝ] X, Module.Finite ℝ (LinearMap.range T.toLinearMap) ∧
      ‖T‖ ≤ Λ ∧ ∃ η : ℝ, η < ε ∧ ∀ u ∈ C, ‖T u - u‖ ≤ η

def blockBound (p : ℕ) : ℝ := 300 * (p : ℝ)^2 + 150 * (p : ℝ) + 5

open scoped BigOperators ENNReal

def RealL1 : Type := lp (fun _ : ℕ => ℝ) (1 : ENNReal)

noncomputable instance : NormedAddCommGroup RealL1 :=
  inferInstanceAs (NormedAddCommGroup (lp (fun _ : ℕ => ℝ) (1 : ENNReal)))

noncomputable instance : NormedSpace ℝ RealL1 :=
  inferInstanceAs (NormedSpace ℝ (lp (fun _ : ℕ => ℝ) (1 : ENNReal)))

def RealL1RenormingStatement : Prop :=
  ∀ p : ℕ, 1 ≤ p → ∃ N : AddGroupNorm RealL1,
    (∀ (r : ℝ) (c : RealL1), N (r • c) = |r| * N c) ∧
    (∀ c : RealL1, (1 / 2 : ℝ) * ‖c‖ ≤ N c ∧ N c ≤ blockBound p * ‖c‖) ∧
    (let m : Module ℝ RealL1 := inferInstance
     letI : NormedAddCommGroup RealL1 := N.toNormedAddCommGroup
     ∃ s : NormedSpace ℝ RealL1, s.toModule = m ∧
       letI := s
       CompleteSpace RealL1 ∧
       HasBAP RealL1 (2 * blockBound p) ∧ ¬ HasBAP RealL1 (p : ℝ) ∧
         (p = 1 → ¬ HasBAP RealL1 1))

def real_l1_quantitative_renorming_statement : Prop :=
  RealL1RenormingStatement

end DiscreteFree

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.DiscreteFree.real_l1_quantitative_renorming_statement

end Problem

/- Formalization scope, from lean/docs/330.md: Kalton's question asks whether uniform discreteness of a metric space forces its Lipschitz-free space to have the bounded approximation property. The formalization constructs a countable metric space with all distinct points at distance at least one whose real Lipschitz-free space has the approximation property but fails every bounded approximation bound. The metric space is unbounded and not proper. The earlier quantitative renorming result for real $\ell_1$ is retained: for each integer $p\ge1$, an equivalent complete norm has the $2B_p$-bounded approximation property but fails the $p$-bounded approximation property, where $B_p=300p^2+150p+5$. -/
