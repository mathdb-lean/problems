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

- problem_id: E594
- collection: erdos
- question_id: erdos:594
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/594.lean#erdos_594
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **Erdős Problem 594** (Erdős–Hajnal [ErHa66], [Er69b]): Does every graph $G$ with chromatic number $\geq \aleph_1$ contain all sufficiently large odd cycles? The answer is **Yes**, proved by Erdős, Hajnal, and Shelah [EHS74]. A graph has chromatic number $\geq \aleph_1$ (i.e. uncountable chromatic number) if and only if it admits no proper colouring with countably many colours; this is encoded as `IsEmpty (G.Coloring ℕ)`. The conclusion states that there is some $N$ such that for every $k \geq N$ the graph contains a cycle of odd length $2k + 1$.
- notes: Erdos Problem 594 -- https://www.erdosproblems.com/594
- track: solved
- answer_shape: decide
- source_stem: 594
- mathdb_ref: erdos:594
- source_namespace: Erdos594
- source_theorem: erdos_594
- source_category: research solved
- source_ams: 3 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Cardinal
open scoped Cardinal

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ (V : Type) (G : SimpleGraph V), IsEmpty (G.Coloring ℕ) →
          ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
            ∃ (v : V) (w : G.Walk v v), w.IsCycle ∧ w.length = 2 * k + 1

end Problem
