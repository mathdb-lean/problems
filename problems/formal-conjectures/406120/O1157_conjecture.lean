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

- problem_id: O1157_conjecture
- collection: oeis
- question_id: oeis:1157
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/1157.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Conjecture: For each k = 2,3,..., all the rational numbers $\frac{\sigma_k(n)}{n^k} = \sum_{d|n} \frac{1}{d^k}$ (n = 1,2,3,...) have pairwise distinct fractional parts. - Zhi-Wei Sun, Oct 15 2015
- notes: OEIS A1157 -- https://oeis.org/A1157
- track: open
- answer_shape: proof
- source_stem: 1157
- source_namespace: OeisA1157
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_1 a_2 a_3 a_4 a_5
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- a n is the sum of squares of divisors of $n$. -/
def a (n : ℕ) : ℕ :=
  n.divisors.sum fun d => d ^ 2

open Nat Finset ArithmeticFunction

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 5 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 10 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 21 := by rfl

@[category test, AMS 11]
theorem a_5 : a 5 = 26 := by rfl

abbrev Target : Prop :=
    ∀ k : ℕ, 2 ≤ k →
      ∀ n₁ n₂ : ℕ, 0 < n₁ → 0 < n₂ → n₁ ≠ n₂ →
        Int.fract (↑((sigma k) n₁) / (↑n₁ ^ k : ℚ)) ≠
          Int.fract (↑((sigma k) n₂) / (↑n₂ ^ k : ℚ))

end Problem
