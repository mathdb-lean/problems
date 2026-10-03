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

- problem_id: E666
- collection: erdos
- question_id: erdos:666
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/666.lean#erdos_666
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $Q_n$ be the $n$-dimensional hypercube graph (so that $Q_n$ has $2^n$ vertices and $n2^{n-1}$ edges). Is it true that, for every $\epsilon>0$, if $n$ is sufficiently large, every subgraph of $Q_n$ with $$\geq \epsilon n2^{n-1}$$ many edges contains a $C_6$? The answer to this problem is no: Chung [Ch92] and Brouwer, Dejter, and Thomassen [BDT93] constructed an edge-partition of $Q_n$ into four subgraphs, each containing no $C_6$.
- notes: Erdos Problem 666 -- https://www.erdosproblems.com/666
- track: solved
- answer_shape: decide
- source_stem: 666
- mathdb_ref: erdos:666
- source_namespace: Erdos666
- source_theorem: erdos_666
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter SimpleGraph

open scoped Finset

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ H : SimpleGraph (Fin n → Bool), H ≤ hypercube n →
          ε * n * 2 ^ (n - 1 : ℕ) ≤ (H.edgeSet.ncard : ℝ) → (cycleGraph 6 ⊑ H)

end Problem
