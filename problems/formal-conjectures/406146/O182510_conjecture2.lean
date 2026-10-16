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

- problem_id: O182510_conjecture2
- collection: oeis
- question_id: oeis:182510
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/182510.lean#conjecture2
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Conjecture: more positive terms than negative. As $n \to \infty$, the count of positive terms is greater than the count of negative terms. The requirement that $n$ is large enough is needed, since the claim fails for $n = 100$.
- notes: OEIS A182510 -- https://oeis.org/A182510
- track: open
- answer_shape: proof
- source_stem: 182510
- source_namespace: OeisA182510
- source_theorem: conjecture2
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3 a_4 a_5 a_6
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- Defining recurrence for $a(n)$. -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => Int.xor (a (n + 1)) (n + 2 : ℤ) - a n

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = -1 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = -8 := by rfl

@[category test, AMS 11]
theorem a_5 : a 5 = -2 := by rfl

@[category test, AMS 11]
theorem a_6 : a 6 = 0 := by rfl

abbrev Target : Prop :=
    ∀ᶠ n in Filter.atTop,
      ((Finset.range n).filter (fun k => a k < 0)).card <
        ((Finset.range n).filter (fun k => 0 < a k)).card

end Problem
