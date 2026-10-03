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

- problem_id: E369
- collection: erdos
- question_id: erdos:369
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/369.lean#erdos_369
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $\epsilon>0$ and $k\geq 2$. Is it true that, for all sufficiently large $n$, there is a sequence of $k$ consecutive integers in $\{1,\ldots,n\}$ all of which are $n^\epsilon$-smooth? The problem is trivially true as written (simply taking $\{1,\ldots,k\}$ and $n>k^{1/\epsilon}$). There are (at least) two possible variants which are non-trivial, and it is not clear which Erdős and Graham meant. We formalize the second: each $m\in P$ (where $P$ is the sequence of $k$ consecutive integers sought for) must be in $[n/2,n]$. In this case a positive answer also follows directly from the result of Balog and Wooley [BaWo98] for infinitely many $n$. Proving this is true for all large $n$ does not follow immediately from [BaWo98], but can be deduced using a similar construction, as shown by SkyYang.
- notes: Erdos Problem 369 -- https://www.erdosproblems.com/369
- track: solved
- answer_shape: decide
- source_stem: 369
- mathdb_ref: erdos:369
- source_namespace: Erdos369
- source_theorem: erdos_369
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 2 ≤ k),
          ∀ᶠ (n : ℕ) in atTop, ∃ a : ℕ, n / 2 ≤ a + 1 ∧ a + k ≤ n ∧
            ∀ j < k, ∀ p ∈ (a + 1 + j).primeFactors, (p : ℝ) ≤ (n : ℝ) ^ ε

end Problem
