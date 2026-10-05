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

- problem_id: G64_prove
- collection: green
- question_id: green:64
- source: formal-conjectures
- source_locator: FormalConjectures/GreensOpenProblems/64.lean#green_64
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Do there exist infinitely many primes $p$ for which $p - 2$ has an odd number of prime factors, counted with multiplicity (i.e. $\Omega(p - 2)$ is odd)?
- notes: Green, open problem 64
- track: open
- answer_shape: prove
- pair_id: G64
- pair_role: prove
- source_stem: 64
- source_namespace: Green64
- source_theorem: green_64
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: green_64_mem_five green_64_mem_seven green_64_not_mem_eleven
- generator: adapters/formal_conjectures/adapter.py
-/

open ArithmeticFunction

open scoped ArithmeticFunction.Omega

namespace Problem

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- $5$ satisfies the condition: $5$ is prime and $5 - 2 = 3$ is prime, so $\Omega(3) = 1$ is odd. -/
@[category test, AMS 11]
theorem green_64_mem_five : 5 ∈ {p : ℕ | p.Prime ∧ Odd (Ω (p - 2))} := by
  refine ⟨by norm_num, ?_⟩
  rw [show (5 : ℕ) - 2 = 3 by norm_num, cardFactors_apply_prime (by norm_num)]
  exact odd_one

/-- $7$ satisfies the condition: $7$ is prime and $7 - 2 = 5$ is prime, so $\Omega(5) = 1$ is odd. -/
@[category test, AMS 11]
theorem green_64_mem_seven : 7 ∈ {p : ℕ | p.Prime ∧ Odd (Ω (p - 2))} := by
  refine ⟨by norm_num, ?_⟩
  rw [show (7 : ℕ) - 2 = 5 by norm_num, cardFactors_apply_prime (by norm_num)]
  exact odd_one

/-- $11$ does *not* satisfy the condition: although $11$ is prime, $11 - 2 = 9 = 3 ^ 2$ has
$\Omega(9) = 2$ prime factors, which is even. This shows the condition is non-trivial. -/
@[category test, AMS 11]
theorem green_64_not_mem_eleven : 11 ∉ {p : ℕ | p.Prime ∧ Odd (Ω (p - 2))} := by
  rintro ⟨-, hodd⟩
  rw [show (11 : ℕ) - 2 = 3 ^ 2 by norm_num, cardFactors_apply_prime_pow (by norm_num)] at hodd
  exact (by decide : ¬ Odd 2) hodd

abbrev Target : Prop :=
    {p : ℕ | p.Prime ∧ Odd (Ω (p - 2))}.Infinite

end Problem
