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

- problem_id: E178
- collection: erdos
- question_id: erdos:178
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/178.lean#erdos_178
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A_1,A_2,\ldots$ be an infinite collection of infinite sets of integers, say $A_i=\{a_{i1}<a_{i2}<\cdots\}$. Does there exist some $f:\mathbb{N}\to\{-1,1\}$ such that $$\max_{m, 1\leq i\leq d} \left\lvert \sum_{1\leq j\leq m} f(a_{ij})\right\rvert \ll_d 1$$ for all $d\geq 1$? Erdős remarks 'it seems certain that the answer is affirmative'. This was solved by Beck [Be81]. Recently Beck [Be17] proved that one can replace $\ll_d 1$ with $\ll d^{4+\epsilon}$ for any $\epsilon>0$.
- notes: Erdos Problem 178 -- https://www.erdosproblems.com/178
- track: solved
- answer_shape: decide
- source_stem: 178
- mathdb_ref: erdos:178
- source_namespace: Erdos178
- source_theorem: erdos_178
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

open Finset BigOperators

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ (a : ℕ → ℕ → ℕ) (ha : ∀ i, StrictMono (a i)),
        ∃ f : ℕ → ℤ, (∀ n, f n = 1 ∨ f n = -1) ∧
          ∀ d : ℕ, ∃ C : ℕ, ∀ m i : ℕ, i < d →
            |∑ j ∈ range m, f (a i j)| ≤ ↑C

end Problem
