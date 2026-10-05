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

- problem_id: E740_prove
- collection: erdos
- question_id: erdos:740
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/740.lean#erdos_740
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $\mathfrak{m}$ be an infinite cardinal and $G$ be a graph with chromatic number $\mathfrak{m}$. Let $r\geq 1$. Must $G$ contain a subgraph of chromatic number $\mathfrak{m}$ which does not contain any odd cycle of length $\leq r$?
- notes: Erdos Problem 740 -- https://www.erdosproblems.com/740
- track: open
- answer_shape: prove
- pair_id: E740
- pair_role: prove
- source_stem: 740
- mathdb_ref: erdos:740
- source_namespace: Erdos740
- source_theorem: erdos_740
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open scoped Cardinal

namespace Problem

/-- A graph avoids odd cycles of length $\leq r$ if it contains no odd cycles of length at most $r$. -/
def NoShortOddCycle {V : Type*} (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∀ (v : V) (c : G.Walk v v), c.IsCycle → Odd c.length → c.length > r

abbrev Target : Prop :=
    ∀ (V : Type*) (G : SimpleGraph V),
        ℵ₀ ≤ G.chromaticCardinal →
          ∀ (r : ℕ),
            ∃ (H : G.Subgraph), H.coe.chromaticCardinal = G.chromaticCardinal ∧
              NoShortOddCycle H.coe r

end Problem
