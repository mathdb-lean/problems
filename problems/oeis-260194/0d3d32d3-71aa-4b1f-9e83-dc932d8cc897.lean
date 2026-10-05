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

- problem_id: O260194_conjecture_refute
- collection: oeis
- question_id: oeis:260194
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/260194.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Does every positive integer occur as a difference in this sequence?
- notes: OEIS A260194 -- https://oeis.org/A260194
- track: open
- answer_shape: refute
- pair_id: O260194_conjecture
- pair_role: refute
- source_stem: 260194
- source_namespace: OeisA260194
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/--
OEIS A260194, shifted so that Lean index zero is the first OEIS term, with recurrence
$a(n+3) = a(n+2) + \gcd(a(n+2),a(n))$ and initial values $a(0)=a(1)=a(2)=1$.
-/
def a : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | n + 3 => a (n + 2) + Nat.gcd (a (n + 2)) (a n)

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 3 := by rfl

@[category test, AMS 11]
theorem a_5 : a 5 = 4 := by rfl

@[category test, AMS 11]
theorem a_6 : a 6 = 6 := by rfl

@[category test, AMS 11]
theorem a_7 : a 7 = 9 := by rfl

@[category test, AMS 11]
theorem a_8 : a 8 = 10 := by rfl

@[category test, AMS 11]
theorem a_9 : a 9 = 12 := by rfl

abbrev Target : Prop :=
    ¬ (
      ∀ d > 0, ∃ n, a (n + 1) = a n + d
    )

end Problem
