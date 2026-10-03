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

- problem_id: E499
- collection: erdos
- question_id: erdos:499
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/499.lean#erdos_499
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $M$ be a real $n \times n$ doubly stochastic matrix. Does there exist some $σ \in S_n$ such that $$ \prod_{1 \leq i \leq n} M_{i, σ(i)} \geq n^{-n}? $$ This is true, and was proved by Marcus and Minc [MaMi62] [MaMi62] Marcus, Marvin and Minc, Henryk, Some results on doubly stochastic matrices. Proc. Amer. Math. Soc. (1962), 571-579.
- notes: Erdos Problem 499 -- https://www.erdosproblems.com/499
- track: solved
- answer_shape: decide
- source_stem: 499
- mathdb_ref: erdos:499
- source_namespace: Erdos499
- source_theorem: erdos_499
- source_category: research solved
- source_ams: 15
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Nat

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ (∀ n, ∀ M ∈ doublyStochastic ℝ (Fin n), ∃ σ : Equiv.Perm (Fin n),
      n ^ (- n : ℤ) ≤ ∏ i, M i (σ i))

end Problem
