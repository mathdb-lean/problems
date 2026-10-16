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

- problem_id: O167604_conjecture_refute
- collection: oeis
- question_id: oeis:167604
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/167604.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Does Chua's sequence contain every prime?
- notes: OEIS A167604 -- https://oeis.org/A167604
- track: open
- answer_shape: refute
- pair_id: O167604_conjecture
- pair_role: refute
- source_stem: 167604
- source_namespace: OeisA167604
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_1 a_2 a_3 a_4
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- The least prime occurring among the sums $d + n / d$ for divisors $d$ of $n$.

Taking the least prime factor of the product gives the same minimum and makes the definition
directly executable. -/
def next (n : ℕ) : ℕ :=
  Nat.minFac (∏ d ∈ n.divisors, (d + n / d))

/-- Product of the first $n$ terms of Chua's sequence. -/
def product : ℕ → ℕ
  | 0 => 1
  | n + 1 => product n * next (product n)

/-- Chua's sequence, extended by $a(0) = 1$. -/
def a : ℕ → ℕ
  | 0 => 1
  | n + 1 => next (product n)

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by
  norm_num [a, product, next]

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by
  norm_num [a, product, next]

@[category test, AMS 11]
theorem a_3 : a 3 = 5 := by
  norm_num [a, product, next,
    show (6 : ℕ).divisors = {1, 2, 3, 6} by decide]

@[category test, AMS 11]
theorem a_4 : a 4 = 11 := by
  norm_num [a, product, next,
    show (6 : ℕ).divisors = {1, 2, 3, 6} by decide,
    show (30 : ℕ).divisors = {1, 2, 3, 5, 6, 10, 15, 30} by decide]

abbrev Target : Prop :=
    ¬ (
      ∀ p : ℕ, p.Prime → ∃ n ≥ 1, a n = p
    )

end Problem
