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

- problem_id: E230
- collection: erdos
- question_id: erdos:230
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/230.lean#erdos_230
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $P(z)=\sum_{1\leq k\leq n}a_kz^k$ for some $a_k\in \mathbb{C}$ with $\lvert a_k\rvert=1$ for $1\leq k\leq n$. Does there exist a constant $c>0$ such that, for $n\geq 2$, we have $$\max_{\lvert z\rvert=1}\lvert P(z)\rvert \geq (1+c)\sqrt{n}?$$ This is Problem 4.31 in [Ha74], in which it is described as a conjecture of Erdős and Newman. The lower bound of $\sqrt{n}$ is trivial from Parseval's theorem. Körner [Ko80] constructed, for all $n\geq 2$, polynomials $P(z)=\sum_{k\leq n} a_kz^k$ with $\lvert a_k\rvert=1$ for $1\leq k\leq n$ such that, for all $z$ with $\lvert z\rvert=1$, $$(c_1-o(1))\sqrt{n} \leq \lvert P(z)\rvert \leq (c_2+o(1))\sqrt{n}$$ for some absolute constants $0<c_1\leq c_2$. The answer is no (contrary to Erdős' initial guess). Kahane [Ka80] constructed 'ultraflat' polynomials $P(z)=\sum a_kz^k$ with $\lvert a_k\rvert=1$ such that $$P(z)=(1+o(1))\sqrt{n}$$ uniformly for all $z\in\mathbb{C}$ with $\lvert z\rvert=1$, where the $o(1)$ term $\to 0$ as $n\to \infty$. For more details see the paper [BoBo09] of Bombieri and Bourgain and where Kahane's construction is improved to yield such a polynomial with $$P(z)=\sqrt{n}+O(n^{\frac{7}{18}}(\log n)^{O(1)})$$ for all $z\in\mathbb{C}$ with $\lvert z\rvert=1$. See also [228](https://www.erdosproblems.com/228) and [1150](https://www.erdosproblems.com/1150).
- notes: Erdos Problem 230 -- https://www.erdosproblems.com/230
- track: solved
- answer_shape: decide
- source_stem: 230
- mathdb_ref: erdos:230
- source_namespace: Erdos230
- source_theorem: erdos_230
- source_category: research solved
- source_ams: 30 42
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter Topology

namespace Problem

/-- The maximum of $\lvert P(z)\rvert$ over the unit circle, for
$P(z)=\sum_{1\leq k\leq n}a_kz^k$. -/
noncomputable def circleMax {n : ℕ} (a : Fin n → ℂ) : ℝ :=
  ⨆ z : Metric.sphere (0 : ℂ) 1, ‖∑ k : Fin n, a k * (z : ℂ) ^ ((k : ℕ) + 1)‖

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n →
        ∀ a : Fin n → ℂ, (∀ k, ‖a k‖ = 1) → (1 + c) * √n ≤ circleMax a

end Problem
