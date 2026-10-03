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

- problem_id: E1109_prove
- collection: erdos
- question_id: erdos:1109
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1109.lean#erdos_1109
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $f(N)$ be the size of the largest subset $A\subseteq \{1,\ldots,N\}$ such that every $n\in A+A$ is squarefree. Estimate $f(N)$. In particular, is it true that $f(N)\leq N^{o(1)}$, or even $f(N) \leq (\log N)^{O(1)}$? This theorem formalizes the subpolynomial bound as `f(N) = O(N^ε)` for every `ε > 0`.
- notes: Erdos Problem 1109 -- https://www.erdosproblems.com/1109
- track: open
- answer_shape: prove
- pair_id: E1109
- pair_role: prove
- source_stem: 1109
- mathdb_ref: erdos:1109
- source_namespace: Erdos1109
- source_theorem: erdos_1109
- source_category: research open
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Asymptotics
open scoped Pointwise

namespace Problem

/--
`f N` is the largest size of a subset `A ⊆ {1, ..., N}` such that every element
of `A + A` is squarefree.
-/
noncomputable def f (N : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset ℕ,
    A ⊆ Finset.Icc 1 N ∧ (∀ n ∈ A + A, Squarefree n) ∧ A.card = k}

abbrev Target : Prop :=
    ∀ ε > (0 : ℝ),
      (fun N : ℕ => (f N : ℝ)) ≪ fun N : ℕ => (N : ℝ) ^ ε

end Problem
