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

- problem_id: E1023
- collection: erdos
- question_id: erdos:1023
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1023.lean#erdos_1023
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $F(n)$ be the maximal size of a family of subsets of $\{1,\ldots,n\}$ such that no set in this family is the union of other members of the family. Is it true that there is a constant $c>0$ such that $$F(n)\sim c \frac{2^n}{n^{1/2}}?$$ Hunter observes in the comments that this follows from the solution to [447], which implies $F(n)\sim \binom{n}{n/2}$.
- notes: Erdos Problem 1023 -- https://www.erdosproblems.com/1023
- track: solved
- answer_shape: decide
- source_stem: 1023
- mathdb_ref: erdos:1023
- source_namespace: Erdos1023
- source_theorem: erdos_1023
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter

open scoped Asymptotics

namespace Problem

/--
`F n` is the maximal size of a family of subsets of $\{1,\ldots,n\}$ such that no set in this
family is the union of other members of the family.
-/
noncomputable def F (n : ℕ) : ℕ :=
  sSup {m | ∃ S ⊆ (Finset.Icc 1 n).powerset, S.SubfamilyUnionFree ∧ S.card = m}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ c : ℝ, 0 < c ∧
          ((fun n : ℕ => (F n : ℝ)) ~[atTop]
            (fun n : ℕ => c * 2 ^ n / (n : ℝ) ^ (1 / 2 : ℝ)))

end Problem
