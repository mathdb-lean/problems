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

- problem_id: E296
- collection: erdos
- question_id: erdos:296
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/296.lean#erdos_296
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $N\geq 1$ and let $k(N)$ be maximal such that there are $k$ disjoint $A_1,\ldots,A_k\subseteq \{1,\ldots,N\}$ with $\sum_{n\in A_i}\frac{1}{n}=1$ for all $i$. Estimate $k(N)$. Is it true that $k(N)=o(\log N)$? Hunter and Sawhney observed that Bloom's theorem [Bl21], together with the greedy argument, gives $k(N)=(1-o(1))\log N$.
- notes: Erdos Problem 296 -- https://www.erdosproblems.com/296
- track: solved
- answer_shape: proof
- source_stem: 296
- mathdb_ref: erdos:296
- source_namespace: Erdos296
- source_theorem: erdos_296
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Filter

/-- The reciprocal sum of a finite set of natural numbers, as a rational number. -/
def recipSum (A : Finset ℕ) : ℚ :=
  ∑ n ∈ A, (1 : ℚ) / n

/-- There are `k` pairwise disjoint subsets of `{1, ..., N}` with reciprocal sum `1`. -/
def HasDisjointUnitDecomps (N k : ℕ) : Prop :=
  ∃ f : Fin k → Finset ℕ,
    (∀ i, f i ⊆ Finset.Icc 1 N) ∧
    (∀ i, recipSum (f i) = 1) ∧
    (∀ i j : Fin k, i ≠ j → Disjoint (f i) (f j))

abbrev Target : Prop :=
    (∀ N k : ℕ, HasDisjointUnitDecomps N k → (k : ℚ) ≤ recipSum (Finset.Icc 1 N)) ∧
      (∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ N : ℕ in atTop,
        HasDisjointUnitDecomps N ⌊(1 - ε) * Real.log N⌋₊)

end Problem
