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

- problem_id: E677
- collection: erdos
- question_id: erdos:677
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/677.lean#erdos_677
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Denote by $M(n, k)$ the least common multiple of the finite set $\{n+1, \dotsc, n+k\}$. Is it true that for all $m \geq n + k$, we get $M(m, k) \neq M(n, k)$?
- notes: Erdos Problem 677 -- https://www.erdosproblems.com/677
- track: open
- answer_shape: proof
- source_stem: 677
- mathdb_ref: erdos:677
- source_namespace: Erdos677
- source_theorem: erdos_677
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: lcmInterval_eq_example1
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Finset

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/--
Erdős expected very few solutions for $M(n, k) = M(m, l)$, where $m \geq n + k$ and $l > 1$.
The only solutions he knew were the following.
-/
@[category test, AMS 11]
lemma lcmInterval_eq_example1 : lcmInterval 4 3 = lcmInterval 13 2 ∧
                                lcmInterval 3 4 = lcmInterval 19 2 := by decide

abbrev Target : Prop :=
    ∀ (m n k : ℕ), k > 0 → m ≥ n + k → lcmInterval m k ≠ lcmInterval n k

end Problem
