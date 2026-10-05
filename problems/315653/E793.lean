/-
Copyright 2025 The Formal Conjectures Authors.
Copyright 2026 The mathdb-lean Authors.

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

import MathDBUtil

/-!
Converted from another corpus. `source` names it, `source_version`
pins the revision, and `source_locator` points at the one
declaration this came from. Every `source_` field describes that
declaration as it stands there, not as it stands here.

Read `track` for whether the problem is solved, which is a fact
about mathematics. `source_has_lean_proof` is a different claim --
whether that corpus holds a machine-checked proof -- and is false
for almost every problem, because it is a statement repository.

- problem_id: E793
- collection: erdos
- question_id: erdos:793
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/793.lean#erdos_793
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $F(n)$ be the maximum possible size of a subset $A \subseteq \{1, \ldots, n\}$ such that $a \nmid bc$ whenever $a, b, c \in A$ with $a \neq b$ and $a \neq c$. Is there a constant $c$ such that $$F(n) = \pi(n) + (c + o(1)) n^{2/3} (\log n)^{-2}?$$ A problem of Erdős [Er69, Er70b], who proved in [Er38] that $F(n) = \pi(n) + O(n^{2/3} (\log n)^{-2})$. The answer is yes, with $c = 27/2$: this was proved by GPT-5.6 Sol (prompted by Chojecki), refining the argument of [Er38]; see `erdos_793.variants.constant`.
- notes: Erdos Problem 793 -- https://www.erdosproblems.com/793
- track: solved
- answer_shape: decide
- source_stem: 793
- mathdb_ref: erdos:793
- source_namespace: Erdos793
- source_theorem: erdos_793
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter Real
open scoped Topology

namespace Problem

/-- A finite set `A ⊆ ℕ` is *strongly 2-primitive* if `a ∤ b * c` whenever `a, b, c ∈ A` with
`a ≠ b` and `a ≠ c`. -/
def Strongly2Primitive (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → a ≠ c → ¬ a ∣ b * c

/-- `F n` is the maximal size of a strongly 2-primitive subset of `{1, …, n}`. -/
noncomputable def F (n : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 n).powerset.filter Strongly2Primitive).sup Finset.card

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ c : ℝ, Tendsto (fun n : ℕ ↦ ((F n : ℝ) - Nat.primeCounting n) /
          ((n : ℝ) ^ ((2 : ℝ) / 3) / (log n) ^ 2)) atTop (𝓝 c)

end Problem
