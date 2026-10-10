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

- problem_id: E844
- collection: erdos
- question_id: erdos:844
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/844.lean#erdos_844
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A\subseteq \{1,\ldots,N\}$ be such that, for all $a,b\in A$, the product $ab$ is not squarefree. Is the maximum size of such an $A$ achieved by taking $A$ to be the set of even numbers and odd non-squarefree numbers? A problem of Erdős and Sárközy. Weisenberg has provided the following positive proof. It is clear that such a maximal $A$ must contain all non-squarefree numbers. It therefore suffices to find the largest size of a subset of all squarefree numbers in $\{1,\ldots,N\}$ such that any two have at least one prime factor in common. By the result of Chvátal [Ch74] discussed in [701] this is maximised by the set of all even squarefree numbers. An alternative proof was independently found by Alexeev, Mixon, and Sawin [AMS25]. This was formalized in Lean by Jennings using Aristotle.
- notes: Erdos Problem 844 -- https://www.erdosproblems.com/844
- track: solved
- answer_shape: decide
- source_stem: 844
- mathdb_ref: erdos:844
- source_namespace: Erdos844
- source_theorem: erdos_844
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

/-- Those $n \in \{1,\ldots,N\}$ which are even or not squarefree, that is, the set of even
numbers together with the odd non-squarefree numbers. -/
def evenOrOddNonSquarefree (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => 2 ∣ n ∨ ¬ Squarefree n)

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ N : ℕ,
        IsGreatest {k : ℕ | ∃ A ⊆ Finset.Icc 1 N,
          (∀ a ∈ A, ∀ b ∈ A, ¬ Squarefree (a * b)) ∧ A.card = k}
          (evenOrOddNonSquarefree N).card

end Problem
