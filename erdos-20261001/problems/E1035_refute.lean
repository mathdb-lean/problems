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

- problem_id: E1035_refute
- collection: erdos
- question_id: erdos:1035
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1035.lean#erdos_1035
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is there a constant $c > 0$ such that every graph on $2^n$ vertices with minimum degree $> (1-c) \cdot 2^n$ contains the $n$-dimensional hypercube $Q_n$? This is Erdős's question [Er93, p. 345]. See also [576] for the extremal number of edges that guarantee a $Q_n$.
- notes: Erdos Problem 1035 -- https://www.erdosproblems.com/1035
- track: open
- answer_shape: refute
- pair_id: E1035
- pair_role: refute
- source_stem: 1035
- mathdb_ref: erdos:1035
- source_namespace: Erdos1035
- source_theorem: erdos_1035
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

abbrev Target : Prop :=
    ¬ (
      ∃ c > 0, ∀ n : ℕ, ∀ (G : SimpleGraph (Fin (2 ^ n))) [DecidableRel G.Adj],
            (∀ v, (G.degree v : ℝ) > (1 - c) * 2 ^ n) →
              (SimpleGraph.hypercube n).IsContained G
    )

end Problem
