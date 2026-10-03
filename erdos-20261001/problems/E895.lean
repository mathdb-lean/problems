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

- problem_id: E895
- collection: erdos
- question_id: erdos:895
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/895.lean#erdos_895
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that, for all sufficiently large $n$, if $G$ is a triangle-free graph on $\{1,\ldots,n\}$ then there must exist three independent points $a,b,a+b$? A problem of Erdős and Hajnal [Er95d]. The stated problem has been resolved by Barber (personal communication) who verified using a SAT solver that this is true for all $n\geq 18$.
- notes: Erdos Problem 895 -- https://www.erdosproblems.com/895
- track: solved
- answer_shape: decide
- source_stem: 895
- mathdb_ref: erdos:895
- source_namespace: Erdos895
- source_theorem: erdos_895
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ᶠ n in atTop, ∀ G : SimpleGraph (Set.Icc 1 n), G.CliqueFree 3 →
          ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}

end Problem
