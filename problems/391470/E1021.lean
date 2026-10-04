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

- problem_id: E1021
- collection: erdos
- question_id: erdos:1021
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1021.lean#erdos_1021
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that, for every $k \geq 3$, there is a constant $c_k > 0$ such that $$\mathrm{ex}(n, G_k) \ll n^{3/2 - c_k},$$ where $G_k$ is the bipartite graph between $\{y_1, \ldots, y_k\}$ and $\{z_1, \ldots, z_{\binom{k}{2}}\}$, with each $z_j$ joined to a unique pair of $y_i$? A conjecture of Erdős and Simonovits [Er71, Er74c], who proved (in unpublished work) that one must have $c_k \to 0$ as $k \to \infty$. The graph $G_k$ is the $1$-subdivision of $K_k$; for $k = 3$ it is the $6$-cycle. This was proved by Conlon and Lee [CoLe21] with $c_k = 6^{-k}$, improved to $c_k = \frac{1}{4k - 6}$ by Janzer [Ja19]; see `erdos_1021.variants.janzer`.
- notes: Erdos Problem 1021 -- https://www.erdosproblems.com/1021
- track: solved
- answer_shape: decide
- source_stem: 1021
- mathdb_ref: erdos:1021
- source_namespace: Erdos1021
- source_theorem: erdos_1021
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter Asymptotics

namespace Problem

/-- The graph `G_k`: the bipartite graph between `{y_1, …, y_k}` (the elements of `Fin k`) and
`{z_1, …, z_{k choose 2}}` (the two-element subsets of `Fin k`), each `z` being joined to the two
elements of the corresponding pair. This is the `1`-subdivision of `K_k`. -/
def cliqueSubdivision (k : ℕ) : SimpleGraph (Fin k ⊕ Set.powersetCard (Fin k) 2) where
  Adj x y :=
    match x, y with
    | Sum.inl i, Sum.inr p => i ∈ (p : Finset (Fin k))
    | Sum.inr p, Sum.inl i => i ∈ (p : Finset (Fin k))
    | _, _ => False
  symm := by
    constructor
    intro x y h
    cases x <;> cases y <;> simp_all
  loopless := by
    constructor
    intro x
    cases x <;> simp

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ k : ℕ, 3 ≤ k → ∃ c : ℝ, 0 < c ∧
          (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
            fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - c)

end Problem
