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

- problem_id: NWilsonPrime_infinitely_many_wilson_primes
- collection: wikipedia
- question_id: wikipedia:WilsonPrime
- source: formal-conjectures
- source_locator: FormalConjectures/Wikipedia/WilsonPrime.lean#infinitely_many_wilson_primes
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: There are infinitely many Wilson primes.
- notes: Wikipedia: WilsonPrime -- https://en.wikipedia.org/wiki/Wilson_prime
- track: open
- answer_shape: proof
- source_stem: WilsonPrime
- source_namespace: WilsonPrime
- source_theorem: infinitely_many_wilson_primes
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: isWilsonPrime_five isWilsonPrime_thirteen not_isWilsonPrime_one not_isWilsonPrime_seven
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- A Wilson prime is a prime $p$ such that $p^2 \mid (p-1)!+1$. -/
def IsWilsonPrime (p : ℕ) : Prop :=
  p.Prime ∧ p ^ 2 ∣ (p - 1).factorial + 1

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- The prime $5$ is a Wilson prime. -/
@[category test, AMS 11]
theorem isWilsonPrime_five : IsWilsonPrime 5 := by
  norm_num [IsWilsonPrime, Nat.factorial]

/-- The prime $13$ is a Wilson prime. -/
@[category test, AMS 11]
theorem isWilsonPrime_thirteen : IsWilsonPrime 13 := by
  norm_num [IsWilsonPrime, Nat.factorial]

/-- The primality condition excludes $1$, which satisfies the divisibility condition alone. -/
@[category test, AMS 11]
theorem not_isWilsonPrime_one : ¬ IsWilsonPrime 1 := by
  norm_num [IsWilsonPrime]

/-- The prime $7$ is not a Wilson prime. -/
@[category test, AMS 11]
theorem not_isWilsonPrime_seven : ¬ IsWilsonPrime 7 := by
  norm_num [IsWilsonPrime, Nat.factorial]

abbrev Target : Prop :=
    Set.Infinite {p : ℕ | IsWilsonPrime p}

end Problem
