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

- problem_id: E10_prove
- collection: erdos
- question_id: erdos:10
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/10.lean#erdos_10
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is there some $k$ such that every large integer is the sum of a prime and at most $k$ powers of $2$?
- notes: Erdos Problem 10 -- https://www.erdosproblems.com/10
- track: open
- answer_shape: prove
- pair_id: E10
- pair_role: prove
- source_stem: 10
- mathdb_ref: erdos:10
- source_namespace: Erdos10
- source_theorem: erdos_10
- source_category: research open
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: two_mem_sumPrimeAndTwoPows_zero one_not_mem_sumPrimeAndTwoPows
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter

namespace Problem

/--
The set of natural numbers that can be written as a sum
of a prime and at most $k$ powers of $2$.
-/
abbrev sumPrimeAndTwoPows (k : ℕ) : Set ℕ :=
  { p + (pows.map (2 ^ ·)).sum | (p : ℕ) (pows : Multiset ℕ) (_ : p.Prime)
    (_ : pows.card ≤ k)}

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- A prime is the sum of a prime and no powers of $2$. -/
@[category test, AMS 5 11]
theorem two_mem_sumPrimeAndTwoPows_zero : 2 ∈ sumPrimeAndTwoPows 0 :=
  ⟨2, 0, Nat.prime_two, by simp, by simp⟩

/-- $1$ is smaller than every prime, so it lies in no `sumPrimeAndTwoPows k`. -/
@[category test, AMS 5 11]
theorem one_not_mem_sumPrimeAndTwoPows (k : ℕ) : 1 ∉ sumPrimeAndTwoPows k := by
  rintro ⟨p, pows, hp, -, h⟩
  have : 2 ≤ p := hp.two_le
  omega

abbrev Target : Prop :=
    ∃ k, ∀ᶠ n : ℕ in atTop, n ∈ sumPrimeAndTwoPows k

end Problem
