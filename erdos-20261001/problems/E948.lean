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

- problem_id: E948
- collection: erdos
- question_id: erdos:948
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/948.lean#erdos_948
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is there a function $f(n)$ and a $k$ such that in any $k$-colouring of the integers there exists a sequence $a_1 < a_2 < \cdots$ such that $a_n < f(n)$ for infinitely many $n$ and the set $$\left\{ \sum_{i \in S} a_i : \textrm{finite nonempty } S \right\}$$ does not contain all colours? A question of Erdős [Er77c] and Erdős and Galvin [ErGa91]. The answer is no: GPT-5.5 Pro (prompted by Price) showed that for every $f$ there is a colouring of the integers such that the finite sums of every such sequence use all colours. The linked formal proof (Codex and GPT-5.6 Sol) gives, for every $f$ and $k \ge 1$, a colouring $c : \mathbb{Z} \to \{0, \ldots, k - 1\}$ such that for every strictly increasing $a$ with $a_n < f(n)$ infinitely often and every colour, some nonempty finite sum of the $a_i$ has that colour.
- notes: Erdos Problem 948 -- https://www.erdosproblems.com/948
- track: solved
- answer_shape: decide
- source_stem: 948
- mathdb_ref: erdos:948
- source_namespace: Erdos948
- source_theorem: erdos_948
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ (f : ℕ → ℕ) (k : ℕ), 0 < k ∧ ∀ colouring : ℤ → Fin k,
          ∃ a : ℕ → ℤ, StrictMono a ∧ {n | a n < f n}.Infinite ∧
            ∃ c : Fin k, ∀ S : Finset ℕ, S.Nonempty → colouring (∑ i ∈ S, a i) ≠ c

end Problem
