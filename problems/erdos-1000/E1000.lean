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

- problem_id: E1000
- collection: erdos
- question_id: erdos:1000
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1000.lean#erdos_1000
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A=\{n_1<n_2<\cdots\}$ be an infinite sequence of positive integers, and let $\phi_A(k)$ count the number of $1\leq m\leq n_k$ such that the fraction $\frac{m}{n_k}$ cannot be written as $\frac{b}{n_j}$ for any integer $b$ and any $j<k$; equivalently, $$ \frac{n_k}{(m,n_k)}\nmid n_j $$ for all $1\leq j<k$. Is there a sequence $A$ such that $$ \lim_{N\to \infty}\frac{1}{N}\sum_{k\leq N}\frac{\phi_A(k)}{n_k}=0? $$ This was solved by Haight [Ha] who proved that such a sequence does exist (contrary to Erdős' expectations).
- notes: Erdos Problem 1000 -- https://www.erdosproblems.com/1000
- track: solved
- answer_shape: decide
- source_stem: 1000
- mathdb_ref: erdos:1000
- source_namespace: Erdos1000
- source_theorem: erdos_1000
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter Topology

namespace Problem

/--
Given an infinite sequence of positive integers $A = \{n_1 < n_2 < \cdots\}$, `phiSeq n k` is
$\phi_A(k)$: the number of $1\leq m\leq n_k$ such that $\frac{m}{n_k}$ cannot be written as
$\frac{b}{n_j}$ for any integer $b$ and any $1\leq j<k$; equivalently,
$$
\frac{n_k}{(m,n_k)}\nmid n_j
$$
for all $1\leq j<k$.
-/
def phiSeq (n : ℕ → ℕ) (k : ℕ) : ℕ :=
  ((Finset.Icc 1 (n k)).filter fun m => ∀ j < k, ¬ (n k / Nat.gcd m (n k)) ∣ n j).card

/--
The average $\frac{1}{N}\sum_{k\leq N}\frac{\phi_A(k)}{n_k}$.
-/
noncomputable def phiAvg (n : ℕ → ℕ) (N : ℕ) : ℝ :=
  (∑ k ∈ Finset.range N, (phiSeq n k : ℝ) / (n k : ℝ)) / (N : ℝ)

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ n : ℕ → ℕ, StrictMono n ∧ 0 < n 0 ∧
          Tendsto (phiAvg n) atTop (𝓝 0)

end Problem
