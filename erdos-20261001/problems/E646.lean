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

- problem_id: E646
- collection: erdos
- question_id: erdos:646
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/646.lean#erdos_646
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $p_1,\ldots,p_k$ be distinct primes. Are there infinitely many $n$ such that $n!$ is divisible by an even power of each of the $p_i$? The answer is yes, proved by Berend [Be97], who further proved that the sequence of such $n$ has bounded gaps (where the bound depends on the initial set of primes).
- notes: Erdos Problem 646 -- https://www.erdosproblems.com/646
- track: solved
- answer_shape: decide
- source_stem: 646
- mathdb_ref: erdos:646
- source_namespace: Erdos646
- source_theorem: erdos_646
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open scoped Nat

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
          {n : ℕ | ∀ p ∈ S, Even (padicValNat p (n !))}.Infinite

end Problem
