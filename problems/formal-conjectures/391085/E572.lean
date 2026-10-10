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

- problem_id: E572
- collection: erdos
- question_id: erdos:572
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/572.lean#erdos_572
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Show that for $k\geq 3$ $$\mathrm{ex}(n;C_{2k})\gg n^{1+\frac{1}{k}}.$$ This problem is #46 in Extremal Graph Theory in the graphs problem collection.
- notes: Erdos Problem 572 -- https://www.erdosproblems.com/572
- track: open
- answer_shape: proof
- source_stem: 572
- mathdb_ref: erdos:572
- source_namespace: Erdos572
- source_theorem: erdos_572
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter

namespace Problem

abbrev Target : Prop :=
    ∀ (k : ℕ) (hk : 3 ≤ k),
      ∃ c > (0 : ℝ), ∀ᶠ (n : ℕ) in atTop,
        c * (n : ℝ) ^ (1 + 1 / (k : ℝ)) ≤
          (SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph (2 * k)) : ℝ)

end Problem
