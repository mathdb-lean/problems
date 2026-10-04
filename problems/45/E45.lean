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

- problem_id: E45
- collection: erdos
- question_id: erdos:45
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/45.lean#erdos_45
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $k\geq 2$. Is there an integer $n_k$ such that, if $D=\{ 1<d<n_k : d\mid n_k\}$, then for any $k$-colouring of $D$ there is a monochromatic subset $D'\subseteq D$ such that $\sum_{d\in D'}\frac{1}{d}=1$? This follows from the colouring result of Croot [Cr03]. Croot's result allows for $n_k \leq e^{C^k}$ for some constant $C>1$ (simply taking $n_k$ to be the lowest common multiple of some interval $[1,C^k]$). Sawhney has observed that there is also a doubly exponential lower bound, and hence this bound is essentially sharp.
- notes: Erdos Problem 45 -- https://www.erdosproblems.com/45
- track: solved
- answer_shape: decide
- source_stem: 45
- mathdb_ref: erdos:45
- source_namespace: Erdos45
- source_theorem: erdos_45
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ k : ℕ, 2 ≤ k → ∃ n : ℕ, ∀ colouring : ℕ → Fin k,
          ∃ colour : Fin k, ∃ D' ⊆ {d ∈ n.divisors | 1 < d ∧ d < n},
            (∀ d ∈ D', colouring d = colour) ∧ D'.reciprocalSum = 1

end Problem
