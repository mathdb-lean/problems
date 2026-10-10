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

- problem_id: E34
- collection: erdos
- question_id: erdos:34
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/34.lean#erdos_34
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: For any permutation $\pi\in S_n$ of $\{1,\ldots,n\}$ let $S(\pi)$ count the number of distinct consecutive sums, that is, sums of the shape $\sum_{u\leq i\leq v}\pi(i)$. Is it true that $$ S(\pi) = o(n^2) $$ for all $\pi\in S_n$? Hegyvári [He86] gave a counterexample.
- notes: Erdos Problem 34 -- https://www.erdosproblems.com/34
- track: solved
- answer_shape: decide
- source_stem: 34
- mathdb_ref: erdos:34
- source_namespace: Erdos34
- source_theorem: erdos_34
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

open scoped BigOperators

/-- The set of consecutive sums of a permutation `p` of `{1,…,n}`, where position `k` holds the
value `p k + 1`: the sums `∑_{u ≤ k ≤ v} (p k + 1)`. -/
def consecutiveSums (n : ℕ) (p : Equiv.Perm (Fin n)) : Finset ℕ :=
  (Finset.univ.filter (fun x : Fin n × Fin n => x.1 ≤ x.2)).image
    (fun x => ∑ k ∈ Finset.Icc x.1 x.2, ((p k : ℕ) + 1))

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ c : ℝ, 0 < c → ∃ N : ℕ, ∀ n ≥ N, ∀ p : Equiv.Perm (Fin n),
          ((consecutiveSums n p).card : ℝ) < c * (n : ℝ) ^ 2

end Problem
