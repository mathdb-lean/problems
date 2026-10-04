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

- problem_id: E775
- collection: erdos
- question_id: erdos:775
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/775.lean#erdos_775
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is there a $3$-uniform hypergraph on $n$ vertices which contains at least $n-O(1)$ different sizes of cliques (maximal complete subgraphs)? The answer is no, as proved by Gao [Ga25]: more generally, for any $k\geq 3$, every $k$-uniform hypergraph on $n$ vertices contains at most $n-f_k(n)$ different sizes of cliques, where $f_k(n)\to \infty$ as $n\to \infty$.
- notes: Erdos Problem 775 -- https://www.erdosproblems.com/775
- track: solved
- answer_shape: decide
- source_stem: 775
- mathdb_ref: erdos:775
- source_namespace: Erdos775
- source_theorem: erdos_775
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ C : ℕ, ∃ᶠ n : ℕ in atTop, ∃ H : ThreeUniformHypergraph (Fin n),
          n - C ≤ (ThreeUniformHypergraph.cliqueSizes H).ncard

end Problem
