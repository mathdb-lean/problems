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

- problem_id: O1223_conjecture
- collection: oeis
- question_id: oeis:1223
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/1223.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Any subsequence a(n .. n+m) with n > 2 (as to exclude the untypical primes 2 and 3) should occur infinitely many times at other starting points k. This is false. The five-term block starting at $n = 3$ is $(2,4,2,4,2)$, and a congruence modulo $5$ shows that it occurs only at $n = 3$.
- notes: OEIS A1223 -- https://oeis.org/A1223
- track: solved
- answer_shape: proof
- source_stem: 1223
- source_namespace: OeisA1223
- source_theorem: conjecture
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- Prime gaps: differences between consecutive primes. -/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else Nat.nth Nat.Prime n - Nat.nth Nat.Prime (n - 1)

/-- Helper definition for extracting a finite subsequence (pattern) as a list. -/
noncomputable def gapSubsequence (startIndex length : ℕ) : List ℕ :=
  (List.range length).map (fun i => a (startIndex + i))

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  change Nat.nth Nat.Prime 1 - Nat.nth Nat.Prime 0 = 1
  rw [Nat.nth_prime_one_eq_three, Nat.nth_prime_zero_eq_two]

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by
  change Nat.nth Nat.Prime 2 - Nat.nth Nat.Prime 1 = 2
  rw [Nat.nth_prime_two_eq_five, Nat.nth_prime_one_eq_three]

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by
  change Nat.nth Nat.Prime 3 - Nat.nth Nat.Prime 2 = 2
  rw [Nat.nth_prime_three_eq_seven, Nat.nth_prime_two_eq_five]

abbrev Target : Prop :=
    ¬ ∀ (n m : ℕ), n ≥ 3 →
      Set.Infinite {k : ℕ | gapSubsequence k (m + 1) = gapSubsequence n (m + 1)}

end Problem
