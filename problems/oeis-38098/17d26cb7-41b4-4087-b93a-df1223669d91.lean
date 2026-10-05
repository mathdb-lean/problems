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

- problem_id: O38098_conjecture2
- collection: oeis
- question_id: oeis:38098
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/38098.lean#conjecture2
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Conjecture (ii): all the numbers $\pi(n^2)/n^2$ ($n = 1, 2, 3, \ldots$) are pairwise distinct. Moreover, we have $\pi(n^2)/n^2 > \pi((n+1)^2)/(n+1)^2$ for all $n > 15646$. - Zhi-Wei Sun, Oct 17 2015
- notes: OEIS A38098 -- https://oeis.org/A38098
- track: open
- answer_shape: proof
- source_stem: 38098
- source_namespace: OeisA38098
- source_theorem: conjecture2
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_1 a_2 a_3 a_4 a_5
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- Number of primes strictly less than $n^3$. -/
def a (n : ℕ) : ℕ := (Nat.primesBelow (n ^ 3)).card

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by
  decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 4 := by
  decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 9 := by
  decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 18 := by
  decide

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 30 := by
  decide +kernel

abbrev Target : Prop :=
    (∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
      (Nat.primeCounting (m ^ 2) : ℚ) / (m ^ 2 : ℚ) =
      (Nat.primeCounting (n ^ 2) : ℚ) / (n ^ 2 : ℚ) → m = n) ∧
    (∀ n : ℕ, 15646 < n →
      (Nat.primeCounting ((n + 1) ^ 2) : ℚ) / ((n + 1) ^ 2 : ℚ) <
      (Nat.primeCounting (n ^ 2) : ℚ) / (n ^ 2 : ℚ))

end Problem
