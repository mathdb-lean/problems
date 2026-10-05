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

- problem_id: RPrimeTuples_prime_tuples_conjecture
- collection: paper
- question_id: paper:PrimeTuples
- source: formal-conjectures
- source_locator: FormalConjectures/Paper/PrimeTuples.lean#prime_tuples_conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: For any `k ≥ 2`, let `a₁,...,aₖ` and `b₁,...,bₖ` be integers with `aᵢ > 0`. Suppose that for every prime `p` there exists an integer `n` such that `p ∤ ∏ i, (aᵢ n + bᵢ)`. Then there exist infinitely many `n` such that `aᵢ n + bᵢ` is prime for all `i`.
- notes: Problem from PrimeTuples
- track: open
- answer_shape: proof
- source_stem: PrimeTuples
- source_namespace: PrimeTuplesConjecture
- source_theorem: prime_tuples_conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Nat

namespace Problem

abbrev Target : Prop :=
    ∀ {k : ℕ} (hk : 2 ≤ k) (a : Fin k → ℕ+) (b : Fin k → ℕ)
        (hab : ∀ p, p.Prime → ∃ n, ¬ p ∣ ∏ i, (a i * n + b i)),
      Set.Infinite {n | ∀ i : Fin k, (a i * n + b i).Prime}

end Problem
