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

- problem_id: E1099
- collection: erdos
- question_id: erdos:1099
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1099.lean#erdos_1099
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $1=d_1<\cdots<d_{\tau(n)}=n$ be the divisors of $n$, and for $\alpha>1$ let $$h_\alpha(n) = \sum_i \left( \frac{d_{i+1}}{d_i}-1\right)^\alpha.$$ Is it true that $$\liminf_{n\to \infty}h_\alpha(n) \ll_\alpha 1?$$ Erdős [Er81h] remarks that $n!$ or the least common multiple of $\{1,\ldots,n\}$ would be good candidates for an infinite sequence of $n$ with $h_\alpha(n)$ bounded. The $\liminf$ is trivially $\geq 1$, just considering the term $i=1$. A positive answer to the main question was provided by Vose [Vo84] by constructing a specific sequence. It remains open whether the two explicit sequences mentioned above satisfy this property. The statement "$\liminf h_\alpha(n)$ is finite" is formalised as "$h_\alpha(n)\leq C$ for infinitely many $n$".
- notes: Erdos Problem 1099 -- https://www.erdosproblems.com/1099
- track: solved
- answer_shape: decide
- source_stem: 1099
- mathdb_ref: erdos:1099
- source_namespace: Erdos1099
- source_theorem: erdos_1099
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter

namespace Problem

/--
For $\alpha>1$ and the divisors $1=d_1<\cdots<d_{\tau(n)}=n$ of $n$,
$$h_\alpha(n) = \sum_i \left( \frac{d_{i+1}}{d_i}-1\right)^\alpha.$$
-/
noncomputable def h (α : ℝ) (n : ℕ) : ℝ :=
  ∑ i : Fin (n.divisors.card - 1),
    ((Nat.nth (· ∣ n) (i + 1) : ℝ) / Nat.nth (· ∣ n) i - 1) ^ α

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ α : ℝ, 1 < α → ∃ C : ℝ, ∃ᶠ n : ℕ in atTop, h α n ≤ C

end Problem
