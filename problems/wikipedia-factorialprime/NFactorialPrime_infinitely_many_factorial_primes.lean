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

- problem_id: NFactorialPrime_infinitely_many_factorial_primes
- collection: wikipedia
- question_id: wikipedia:FactorialPrime
- source: formal-conjectures
- source_locator: FormalConjectures/Wikipedia/FactorialPrime.lean#infinitely_many_factorial_primes
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: There are infinitely many factorial primes.
- notes: Wikipedia: FactorialPrime -- https://en.wikipedia.org/wiki/Factorial_prime
- track: open
- answer_shape: proof
- source_stem: FactorialPrime
- source_namespace: FactorialPrime
- source_theorem: infinitely_many_factorial_primes
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: seven_isFactorialPrime twentyThree_isFactorialPrime
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- A factorial prime is a prime one above or one below a factorial. -/
def IsFactorialPrime (p : ℕ) : Prop :=
  p.Prime ∧ ∃ n : ℕ, p = n.factorial + 1 ∨ n.factorial = p + 1

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem seven_isFactorialPrime : IsFactorialPrime 7 := by
  refine ⟨by norm_num, 3, Or.inl ?_⟩
  norm_num

@[category test, AMS 11]
theorem twentyThree_isFactorialPrime : IsFactorialPrime 23 := by
  refine ⟨by norm_num, 4, Or.inr ?_⟩
  norm_num

abbrev Target : Prop :=
    Set.Infinite {p : ℕ | IsFactorialPrime p}

end Problem
