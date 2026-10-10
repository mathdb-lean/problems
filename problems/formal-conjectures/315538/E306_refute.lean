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

- problem_id: E306_refute
- collection: erdos
- question_id: erdos:306
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/306.lean#erdos_306
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $\frac a b\in \mathbb{Q}_{>0}$ with $b$ squarefree. Are there integers $1 < n_1 < \dots < n_k$, each the product of two distinct primes, such that $\frac{a}{b}=\frac{1}{n_1}+\cdots+\frac{1}{n_k}$?
- notes: Erdos Problem 306 -- https://www.erdosproblems.com/306
- track: open
- answer_shape: refute
- pair_id: E306
- pair_role: refute
- source_stem: 306
- mathdb_ref: erdos:306
- source_namespace: Erdos306
- source_theorem: erdos_306
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open ArithmeticFunction
open scoped omega Omega

namespace Problem

abbrev Target : Prop :=
    ¬ (
      ∀ (q : ℚ), 0 < q → Squarefree q.den →
          ∃ k : ℕ, ∃ (n : Fin (k + 1) → ℕ), n 0 = 1 ∧ StrictMono n ∧
          (∀ i ∈ Finset.Icc 1 (Fin.last k), ω (n i) = 2 ∧ Ω (n i) = 2) ∧
          q = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / (n i)
    )

end Problem
