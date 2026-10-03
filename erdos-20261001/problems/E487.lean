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

- problem_id: E487
- collection: erdos
- question_id: erdos:487
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/487.lean#erdos_487
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A\subseteq \mathbb{N}$ have positive density. Must there exist distinct $a,b,c\in A$ such that $[a,b]=c$ (where $[a,b]$ is the least common multiple of $a$ and $b$)? This is true, a consequence of the positive solution to [447] by Kleitman [Kl71]. Davenport and Erdős [DaEr36] showed that there must exist an infinite sequence $a_1<a_2\cdots$ in $A$ such that $a_i\mid a_j$ for all $i\leq j$, under the assumption that the upper logarithmic density of $A$ is positive.
- notes: Erdos Problem 487 -- https://www.erdosproblems.com/487
- track: solved
- answer_shape: decide
- source_stem: 487
- mathdb_ref: erdos:487
- source_namespace: Erdos487
- source_theorem: erdos_487
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ A : Set ℕ, A.HasPosDensity →
          ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ Nat.lcm a b = c

end Problem
