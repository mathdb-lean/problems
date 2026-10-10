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

- problem_id: E441
- collection: erdos
- question_id: erdos:441
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/441.lean#erdos_441
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $N\geq 1$. What is the size of the largest $A\subset \{1,\ldots,N\}$ such that $[a,b]\leq N$ for all $a,b\in A$, where $[a,b]$ is the least common multiple of $a$ and $b$? Is it attained by choosing all integers in $[1,(N/2)^{1/2}]$ together with all even integers in $[(N/2)^{1/2},(2N)^{1/2}]$? Let $g(N)$ denote the size of the largest such $A$. The construction mentioned proves that $g(N) \geq \left(\tfrac{9}{8}N\right)^{1/2}+O(1)$. Erdős [Er51b] proved $g(N) \leq (4N)^{1/2}+O(1)$, which was improved by Choi [Ch72b]. Chen [Ch98] established the asymptotic $g(N) \sim \left(\tfrac{9}{8}N\right)^{1/2}$. Chen and Dai [DaCh06] proved that $$g(N)\leq \left(\tfrac{9}{8}N\right)^{1/2}+ O\left(\left(\frac{N}{\log N}\right)^{1/2}\log\log N\right).$$ In [ChDa07] the same authors prove that, infinitely often, Erdős' construction is not optimal: if $B$ is that construction and $A$ is such that $\lvert A\rvert=g(N)$ then, for infinitely many $N$, $\lvert A\rvert\geq \lvert B\rvert+t-2$, where $t\geq 0$ is defined such that the $t$-fold iterated logarithm of $N$ is in $[0,1)$. (erdosproblems.com omits the $-2$; [ChDa07] proves the bound with it.) This is discussed in problems B26 and E2 of Guy's collection [Gu04].
- notes: Erdos Problem 441 -- https://www.erdosproblems.com/441
- track: solved
- answer_shape: decide
- source_stem: 441
- mathdb_ref: erdos:441
- source_namespace: Erdos441
- source_theorem: erdos_441
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter Asymptotics

namespace Problem

/--
`g N` is the size of the largest `A ⊆ {1, …, N}` such that `lcm(a, b) ≤ N` for all `a, b ∈ A`.
-/
noncomputable def g (N : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset ℕ,
    A ⊆ Finset.Icc 1 N ∧ (∀ a ∈ A, ∀ b ∈ A, Nat.lcm a b ≤ N) ∧ A.card = k}

/--
Erdős' construction: all integers in $[1,(N/2)^{1/2}]$ together with all even integers in
$[(N/2)^{1/2},(2N)^{1/2}]$.
-/
def erdosConstruction (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun a ↦ 2 * a ^ 2 ≤ N ∨ (2 ∣ a ∧ a ^ 2 ≤ 2 * N)

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ N : ℕ, 1 ≤ N → g N = (erdosConstruction N).card

end Problem
