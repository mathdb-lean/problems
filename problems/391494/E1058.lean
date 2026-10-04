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

- problem_id: E1058
- collection: erdos
- question_id: erdos:1058
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1058.lean#erdos_1058
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $2=p_1<p_2<\cdots$ be the sequence of prime numbers. Are there only finitely many $n$ such that $n\in [p_{k-1},p_k)$ and the only primes dividing $n!+1$ are $p_{k}$ and $p_{k+1}$? A conjecture of Erdős and Stewart, as reported in problem A2 of Guy's collection [Gu04]. The only known cases are $n=1,2,3,4,5$. Luca [Lu01] proved that indeed these are the only solutions.
- notes: Erdos Problem 1058 -- https://www.erdosproblems.com/1058
- track: solved
- answer_shape: decide
- source_stem: 1058
- mathdb_ref: erdos:1058
- source_namespace: Erdos1058
- source_theorem: erdos_1058
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Nat

namespace Problem

/--
`n` is a *solution* if `n ∈ [p_{k-1}, p_k)` for some `k` (with the convention `p_0 = 1`, where
`p_1 = 2 < p_2 < ⋯` are the primes) and the only primes dividing `n! + 1` are `p_k` and
`p_{k+1}`. Primes are indexed from `0` by `Nat.nth Nat.Prime`.
-/
def IsSolution (n : ℕ) : Prop :=
  0 < n ∧ ∃ k : ℕ, (if k = 0 then 1 else nth Nat.Prime (k - 1)) ≤ n ∧
    n < nth Nat.Prime k ∧
      ∀ r : ℕ, r.Prime → r ∣ n ! + 1 → r = nth Nat.Prime k ∨ r = nth Nat.Prime (k + 1)

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ {n | IsSolution n}.Finite

end Problem
