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

- problem_id: E927
- collection: erdos
- question_id: erdos:927
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/927.lean#erdos_927
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $g(n)$ be the maximum number of different sizes of cliques that can occur in a graph on $n$ vertices. Estimate $g(n)$ - in particular, is it true that $$g(n) = n - \log_2 n - \log_*(n) + O(1),$$ where $\log_*(n)$ is the number of iterated logarithms such that $\log \cdots \log n < 1$? A quantity first considered by Moon and Moser [MoMo65], who proved $n - \log_2 n - 2 \log \log n < g(n) \le n - \lfloor \log_2 n \rfloor$. Erdős [Er66b] improved the lower bound to $n - \log_2 n - \log_*(n) - O(1) < g(n)$ and conjectured this was the correct order of magnitude. This was disproved by Spencer [Sp71], who proved that in fact $g(n) > n - \log_2 n - O(1)$. Here $\log_2 n$ and $\log_*(n)$ are formalised as `Nat.log 2 n` and `Nat.iteratedLog 2 n` (iterating `Nat.log 2` until the value is at most `1`); both differ from the quantities in the problem by $O(1)$, so the statement is unaffected. See also `erdos_775.variants.spencer` and `erdos_775.variants.moon_moser`.
- notes: Erdos Problem 927 -- https://www.erdosproblems.com/927
- track: solved
- answer_shape: decide
- source_stem: 927
- mathdb_ref: erdos:927
- source_namespace: Erdos927
- source_theorem: erdos_927
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter

namespace Problem

/-- `g n` is the maximum number of different sizes of cliques (maximal complete subgraphs) of a
graph on `n` vertices. -/
noncomputable def g (n : ℕ) : ℕ := by
  classical
  exact Finset.sup (Finset.univ (α := SimpleGraph (Fin n)))
    fun G => (SimpleGraph.cliqueSizes G).ncard

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ C : ℕ, ∀ᶠ n : ℕ in atTop,
          g n + Nat.log 2 n + Nat.iteratedLog 2 n ≤ n + C ∧
            n ≤ g n + Nat.log 2 n + Nat.iteratedLog 2 n + C

end Problem
