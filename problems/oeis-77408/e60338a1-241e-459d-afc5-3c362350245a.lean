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

- problem_id: O77408_conjecture
- collection: oeis
- question_id: oeis:77408
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/77408.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: $103$ is conjectured to be the smallest number such that the Reverse and Add! algorithm in base $3$ does not lead to a palindrome. Its trajectory is conjectured to never reach a palindrome.
- notes: OEIS A77408 -- https://oeis.org/A77408
- track: open
- answer_shape: proof
- source_stem: 77408
- source_namespace: OeisA77408
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3 a_4 a_5
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- The number whose base-$b$ digits are the reversal of $n$'s base-$b$ digits. -/
def revBase (b n : ℕ) : ℕ :=
  Nat.ofDigits b (Nat.digits b n).reverse

/-- A natural number $n$ is a base-$b$ palindrome if its base-$b$ digits read the same forwards
and backwards. -/
def IsBasePalindrome (b n : ℕ) : Prop :=
  n = revBase b n

/-- Trajectory of 103 under the Reverse and Add! operation in base 3. -/
def a : ℕ → ℕ
  | 0 => 103
  | n + 1 => a n + revBase 3 (a n)

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 103 := by
  rfl

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 230 := by
  decide +kernel

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 436 := by
  decide +kernel

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 776 := by
  decide +kernel

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 2424 := by
  decide +kernel

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 3856 := by
  decide +kernel

abbrev Target : Prop :=
    ∀ (n : ℕ),
      ¬ IsBasePalindrome 3 (a n)

end Problem
