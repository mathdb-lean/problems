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

import MathdbUtil

/-!
Converted from another corpus. `source` names it, `source_version`
pins the revision, and `source_locator` points at the one
declaration this came from. Every `source_` field describes that
declaration as it stands there, not as it stands here.

Read `track` for whether the problem is solved, which is a fact
about mathematics. `source_has_lean_proof` is a different claim --
whether that corpus holds a machine-checked proof -- and is false
for almost every problem, because it is a statement repository.

- problem_id: E764
- collection: erdos
- question_id: erdos:764
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/764.lean#erdos_764
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A\subseteq \mathbb{N}$. Can there exist some constant $c>0$ such that $$\sum_{n\leq N} 1_A\ast 1_A\ast 1_A(n) = cN+O(1)?$$ The case of $1_A\ast 1_A(n)$ is the subject of [763](https://www.erdosproblems.com/763). The answer is no, proved in a strong form by Vaughan [Va72], who showed that in fact $$\sum_{n\leq N} 1_A\ast 1_A\ast 1_A(n) = cN+o\left(\frac{N^{1/4}}{(\log N)^{1/2}}\right)$$ is impossible. Vaughan proves a more general result that applies to any $h$-fold convolution, with different main terms permitted.
- notes: Erdos Problem 764 -- https://www.erdosproblems.com/764
- track: solved
- answer_shape: decide
- source_stem: 764
- mathdb_ref: erdos:764
- source_namespace: Erdos764
- source_theorem: erdos_764
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter Asymptotics AdditiveCombinatorics Set

namespace Problem

/-- The number of representations of `n` as an ordered sum of three elements of `A`,
$1_A\ast 1_A\ast 1_A(n)$. -/
noncomputable def tripleRep (A : Set ℕ) : ℕ → ℕ := 𝟙_A ∗ 𝟙_A ∗ 𝟙_A

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∃ (A : Set ℕ) (c : ℝ), 0 < c ∧
        (fun N : ℕ ↦ (∑ n ∈ Finset.range (N + 1), tripleRep A n : ℝ) - c * N) =O[atTop]
          fun _ ↦ (1 : ℝ)

end Problem
