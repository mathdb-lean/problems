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

- problem_id: E220
- collection: erdos
- question_id: erdos:220
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/220.lean#erdos_220
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $n \geq 1$ and $$A = \{a_1 < \cdots < a_{\phi(n)}\} = \{1 \leq m < n : (m, n) = 1\}.$$ Is it true that $$\sum_{1 \leq k < \phi(n)} (a_{k+1} - a_k)^2 \ll \frac{n^2}{\phi(n)}?$$ A problem of Erdős [Er40, Er73, ErGr80], which is discussed in problem B40 of Guy's collection [Gu04]. The answer is yes, as proved by Montgomery and Vaughan [MoVa86], who in fact proved that $\sum_{1 \leq k < \phi(n)} (a_{k+1} - a_k)^\gamma \ll n^\gamma / \phi(n)^{\gamma - 1}$ for every $\gamma \geq 1$.
- notes: Erdos Problem 220 -- https://www.erdosproblems.com/220
- track: solved
- answer_shape: decide
- source_stem: 220
- mathdb_ref: erdos:220
- source_namespace: Erdos220
- source_theorem: erdos_220
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

/-- The sum of the squared differences of adjacent entries of a list of natural numbers. -/
def sumSquaredGaps : List ℕ → ℕ
  | a :: b :: rest => (b - a) ^ 2 + sumSquaredGaps (b :: rest)
  | _ => 0

/-- The reduced residues `1 ≤ m < n` with `(m, n) = 1`, in increasing order. -/
def sortedTotatives (n : ℕ) : List ℕ :=
  ((Finset.Ico 1 n).filter fun m => m.Coprime n).sort (· ≤ ·)

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
          (sumSquaredGaps (sortedTotatives n) : ℝ) ≤ C * (n : ℝ) ^ 2 / (n.totient : ℝ)

end Problem
