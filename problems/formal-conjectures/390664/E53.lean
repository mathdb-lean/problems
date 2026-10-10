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

- problem_id: E53
- collection: erdos
- question_id: erdos:53
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/53.lean#erdos_53
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A$ be a finite set of integers. Is it true that, for every $k$, if $\lvert A\rvert$ is sufficiently large depending on $k$, then there are least $\lvert A\rvert^k$ many integers which are either the sum or product of distinct elements of $A$? Asked by Erdős and Szemerédi [ErSz83]. Solved in this form by Chang [Ch03]. Erdős and Szemerédi proved that there exist arbitrarily large sets $A$ such that the number of integers which are the sum or product of distinct elements of $A$ is at most $$\exp\left(c \frac{(\log \lvert A\rvert)^2}{\log\log\lvert A\rvert}\right)$$ for some constant $c>0$. (erdosproblems.com multiplies by $\log\log\lvert A\rvert$; [ErSz83, Theorem 2] divides by it.) See also [52](https://www.erdosproblems.com/52).
- notes: Erdos Problem 53 -- https://www.erdosproblems.com/53
- track: solved
- answer_shape: decide
- source_stem: 53
- mathdb_ref: erdos:53
- source_namespace: Erdos53
- source_theorem: erdos_53
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

/-- The integers which are either the sum or the product of (one or more) distinct elements of
`A`. -/
def sumsAndProducts (A : Finset ℤ) : Finset ℤ :=
  (A.powerset.erase ∅).image (fun B => ∑ b ∈ B, b) ∪
    (A.powerset.erase ∅).image (fun B => ∏ b ∈ B, b)

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ k : ℕ, ∃ N : ℕ, ∀ A : Finset ℤ, N ≤ A.card →
        A.card ^ k ≤ (sumsAndProducts A).card

end Problem
