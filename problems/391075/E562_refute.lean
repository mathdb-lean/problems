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

- problem_id: E562_refute
- collection: erdos
- question_id: erdos:562
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/562.lean#erdos_562
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $R_r(n)$ denote the $r$-uniform hypergraph Ramsey number: the minimal $m$ such that if we $2$-colour all edges of the complete $r$-uniform hypergraph on $m$ vertices then there must be some monochromatic copy of the complete $r$-uniform hypergraph on $n$ vertices. Prove that, for $r \ge 3$, $$ \log_{r-1} R_r(n) \asymp_r n, $$ where $\log_{r-1}$ denotes the $(r-1)$-fold iterated logarithm.
- notes: Erdos Problem 562 -- https://www.erdosproblems.com/562
- track: open
- answer_shape: refute
- pair_id: E562
- pair_role: refute
- source_stem: 562
- mathdb_ref: erdos:562
- source_namespace: Erdos562
- source_theorem: erdos_562
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Combinatorics Filter Real
open scoped Asymptotics

namespace Problem

abbrev Target : Prop :=
    ¬ (
      ∀ r ≥ 3, (fun n ↦ log^[r - 1] (hypergraphRamsey r n)) =Θ[atTop] (fun n ↦ (n : ℝ))
    )

end Problem
