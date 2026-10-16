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

- problem_id: O111114_conjecture
- collection: oeis
- question_id: oeis:111114
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/111114.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Conjecture: As $n \rightarrow \infty$, there are infinitely many n's such that $a(n)$ is greater than $a(n+1)$.
- notes: OEIS A111114 -- https://oeis.org/A111114
- track: open
- answer_shape: proof
- source_stem: 111114
- source_namespace: OeisA111114
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_2 a_3 a_4 a_5
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Nat

/--
`a n` is the integer part of $\mathrm{prime}(n)/\pi(n)$.
Here $\mathrm{prime}(n)$ is the $n$-th prime number, and $\pi(n)$ is the prime-counting function.
The sequence is defined for $n \ge 2$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  (Nat.nth Nat.Prime (n - 1)) / (Nat.primeCounting n)

open Filter

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by
  have : Nat.nth Nat.Prime 1 = 3 := Nat.nth_prime_one_eq_three
  unfold a
  rw [this]
  decide

@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by
  have : Nat.nth Nat.Prime 2 = 5 := Nat.nth_prime_two_eq_five
  unfold a
  rw [this]
  decide

@[category test, AMS 11]
theorem a_4 : a 4 = 3 := by
  have : Nat.nth Nat.Prime 3 = 7 := Nat.nth_prime_three_eq_seven
  unfold a
  rw [this]
  decide

@[category test, AMS 11]
theorem a_5 : a 5 = 3 := by
  have : Nat.nth Nat.Prime 4 = 11 := Nat.nth_prime_four_eq_eleven
  unfold a
  rw [this]
  decide

abbrev Target : Prop :=
    ∃ᶠ n in atTop, a n > a (n + 1)

end Problem
