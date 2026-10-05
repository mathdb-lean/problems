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

- problem_id: O78590_conjecture
- collection: oeis
- question_id: oeis:78590
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/78590.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Are all terms integers? No. Exact divisibility first fails at $n = 7$; the corresponding rational term has reduced denominator $19$.
- notes: OEIS A78590 -- https://oeis.org/A78590
- track: solved
- answer_shape: decide
- source_stem: 78590
- source_namespace: OeisA78590
- source_theorem: conjecture
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_1 a_2 a_3 a_4 a_5
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

/-- $a(1)=1, a(2)=1, a(n)=(2^{a(n-1)} + 1)/a(n-2)$. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | n + 3 => (2 ^ a (n + 2) + 1) / a (n + 1)

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  rfl

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  rfl

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 3 := by
  rfl

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 9 := by
  rfl

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 171 := by
  rfl

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ n : ℕ, 3 ≤ n → a (n - 2) ∣ 2 ^ a (n - 1) + 1

end Problem
