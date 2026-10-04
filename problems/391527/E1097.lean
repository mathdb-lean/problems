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

- problem_id: E1097
- collection: erdos
- question_id: erdos:1097
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1097.lean#erdos_1097
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: The main conjecture: for any finite set of integers $A$ with $|A| = n$, the number of distinct common differences in three-term arithmetic progressions is $O(n^{3/2})$. This conjecture was resolved negatively by showing that the problem is exactly equivalent to Bourgain's sums-differences question [Bo99], which was introduced as an arithmetic path towards the Kakeya conjecture. Under this equivalence: - The greatest achievable exponent for this problem is equal to the smallest constant $c$ achievable for Bourgain's sums-differences question: $$|A -_G B| \ll \max(|A|, |B|, |A +_G B|)^c$$ - The $O(n^{3/2})$ prediction is disproved because the lower bound has been shown to satisfy $c \ge 1.77898$ (due to Zheng and AlphaEvolve [GGTW25], improving on Lemm [Le15]), which is strictly greater than $3/2 = 1.5$. - The best known upper bound is $c \le 11/6 \approx 1.833$ (due to Katz and Tao [KaTa99]). - While the specific $O(n^{3/2})$ prediction is resolved negatively, the general question of determining the exact optimal exponent $c$ remains open.
- notes: Erdos Problem 1097 -- https://www.erdosproblems.com/1097
- track: solved
- answer_shape: decide
- source_stem: 1097
- mathdb_ref: erdos:1097
- source_namespace: Erdos1097
- source_theorem: erdos_1097
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

/--
Given a finite set of integers `A` (modelled as a `Finset ℤ`), the set
`CommonDifferencesThreeTermAP A` consists of all integers `d` such that there
is a non-trivial three-term arithmetic progression `a, b, c ∈ A` with
`b - a = d` and `c - b = d`.
-/
def CommonDifferencesThreeTermAP (A : Finset ℤ) : Set ℤ :=
  {d : ℤ | d ≠ 0 ∧ ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, b - a = d ∧ c - b = d}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∃ C > (0 : ℝ), ∀ (A : Finset ℤ),
        (CommonDifferencesThreeTermAP A).ncard ≤ C * (A.card : ℝ) ^ (3 / 2 : ℝ)

end Problem
