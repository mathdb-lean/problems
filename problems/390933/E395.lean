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

- problem_id: E395
- collection: erdos
- question_id: erdos:395
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/395.lean#erdos_395
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If $z_1,\ldots,z_n\in \mathbb{C}$ with $\lvert z_i\rvert=1$ then is it true that the probability that $$\lvert \epsilon_1z_1+\cdots+\epsilon_nz_n\rvert \leq \sqrt{2},$$ where $\epsilon_i\in \{-1,1\}$ uniformly at random, is $\gg 1/n$? A reverse Littlewood-Offord problem. Erdős originally asked this with $\sqrt{2}$ replaced by $1$, but Carnielli and Carolino [CaCa11] observed that this is false, choosing $z_1=1$ and $z_k=i$ for $2\leq k\leq n$, where $n$ is even, since then the sum is at least $\sqrt{2}$ always. Solved in the affirmative by He, Juškevičius, Narayanan, and Spiro [HJNS24]. The bound of $1/n$ is the best possible, as shown by taking $z_k=1$ for $1\leq k\leq n/2$ and $z_k=i$ otherwise. See also [498](https://www.erdosproblems.com/498).
- notes: Erdos Problem 395 -- https://www.erdosproblems.com/395
- track: solved
- answer_shape: decide
- source_stem: 395
- mathdb_ref: erdos:395
- source_namespace: Erdos395
- source_theorem: erdos_395
- source_category: research solved
- source_ams: 5 60
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

/-- The number of sign patterns $\epsilon \in \{-1,1\}^n$ with
$\lvert \epsilon_1z_1+\cdots+\epsilon_nz_n\rvert \leq r$. -/
noncomputable def signedSumCount {n : ℕ} (z : Fin n → ℂ) (r : ℝ) : ℕ :=
  {ε : Fin n → ℤ | (∀ i, ε i = -1 ∨ ε i = 1) ∧ ‖∑ i, (ε i : ℂ) * z i‖ ≤ r}.ncard

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n → ∀ z : Fin n → ℂ,
        (∀ i, ‖z i‖ = 1) → c / n ≤ (signedSumCount z √2 : ℝ) / 2 ^ n

end Problem
