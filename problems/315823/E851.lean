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

- problem_id: E851
- collection: erdos
- question_id: erdos:851
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/851.lean#erdos_851
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $\epsilon > 0$. Is there some $r \ll_\epsilon 1$ such that the density of integers of the form $2^k+n$, where $k \geq 0$ and $n$ has at most $r$ prime divisors, is at least $1-\epsilon$? This was proved affirmatively by Price and GPT-5.2 Pro [Pr26].
- notes: Erdos Problem 851 -- https://www.erdosproblems.com/851
- track: solved
- answer_shape: proof
- source_stem: 851
- mathdb_ref: erdos:851
- source_namespace: Erdos851
- source_theorem: erdos_851
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/--
`TwoPowAddSet r` is the set of integers of the form `2^k+n`, where `k ≥ 0` and `n` has at most `r`
prime divisors.
-/
def TwoPowAddSet (r : ℕ) := {(2 ^ k + n) | (k : ℕ) (n : ℕ) (_ : n.primeFactors.card ≤ r)}

/-- The set of integers of the form `2^k+p`, where `k ≥ 0` and `p` is prime. -/
def twoPowAddPrimeSet : Set ℕ := {(2 ^ k + p) | (k : ℕ) (p : ℕ) (_ : p.Prime)}

abbrev Target : Prop :=
    ∀ (ε : ℝ) (hε : ε ∈ Set.Ioo 0 1),
      ∃ r,
          1 - ε ≤ (TwoPowAddSet r).lowerDensity

end Problem
