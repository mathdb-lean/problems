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

- problem_id: E313_prove
- collection: erdos
- question_id: erdos:313
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/313.lean#erdos_313
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Are there infinitely many pairs `(m, P)` where `m ≥ 2` is an integer and `P` is a set of distinct primes such that the following equation holds: $\sum_{p \in P} \frac{1}{p} = 1 - \frac{1}{m}$?
- notes: Erdos Problem 313 -- https://www.erdosproblems.com/313
- track: open
- answer_shape: prove
- pair_id: E313
- pair_role: prove
- source_stem: 313
- mathdb_ref: erdos:313
- source_namespace: Erdos313
- source_theorem: erdos_313
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/--
This set contains all solutions `(m, P)` to the Erdős problem 313.
A solution is a pair where `m` is an integer `≥ 2` and `P` is a non-empty, finite set of
distinct prime numbers, such that the sum of the reciprocals of the primes in `P` equals `1 - 1/m`.
-/
def erdos313Solutions : Set (ℕ × Finset ℕ) :=
  {(m, P) | 2 ≤ m ∧ P.Nonempty ∧ (∀ p ∈ P, p.Prime) ∧ ∑ p ∈ P, (1 : ℚ) / p = 1 - 1 / m}

/--
An integer `n` is a **primary pseudoperfect number** if it is the denominator `m` in a
solution `(m, P)` to the Erdős 313 problem.
-/
def IsPrimaryPseudoperfect (n : ℕ) : Prop := ∃ P, (n, P) ∈ erdos313Solutions

abbrev Target : Prop :=
    erdos313Solutions.Infinite

end Problem
