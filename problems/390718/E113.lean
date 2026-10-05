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

- problem_id: E113
- collection: erdos
- question_id: erdos:113
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/113.lean#erdos_113
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If $G$ is bipartite then $\mathrm{ex}(n;G)\ll n^{3/2}$ if and only $G$ is $2$-degenerate, that is, $G$ contains no induced subgraph with minimal degree at least 3. Conjectured by Erdős and Simonovits [ErSi84]. Erdős first offered \$250 for a proof and \$100 for a counterexample, but in [Er93] offered \$500 for a counterexample. Disproved by Janzer [Ja23b] who constructed, for any $\epsilon>0$, a $3$-regular bipartite graph $H$ such that $$\mathrm{ex}(n;H)\ll n^{\frac{4}{3}+\epsilon}.$$ See also [146](https://www.erdosproblems.com/146) and [147](https://www.erdosproblems.com/147). The linked formal proof refutes the "only if" direction via Janzer's construction.
- notes: Erdos Problem 113 -- https://www.erdosproblems.com/113
- track: solved
- answer_shape: decide
- source_stem: 113
- mathdb_ref: erdos:113
- source_namespace: Erdos113
- source_theorem: erdos_113
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter Asymptotics SimpleGraph

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.IsBipartite →
        (((fun n : ℕ => (extremalNumber n G : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ)) ↔
          G.IsDegenerate 2)

end Problem
