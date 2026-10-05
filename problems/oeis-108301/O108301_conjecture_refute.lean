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

- problem_id: O108301_conjecture_refute
- collection: oeis
- question_id: oeis:108301
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/108301.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: $a(0)$, $a(1)$, $a(5)$, $a(6)$, $a(7)$ and $a(11)$ are primes. Are there any more?
- notes: OEIS A108301 -- https://oeis.org/A108301
- track: open
- answer_shape: refute
- pair_id: O108301_conjecture
- pair_role: refute
- source_stem: 108301
- source_namespace: OeisA108301
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3 a_4
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- The primary defining sequence `a`.
`a n` is the digital sum of the Fermat number $2^{2^n} + 1$. -/
def a (n : ℕ) : ℕ :=
  (Nat.digits 10 (2 ^ 2 ^ n + 1)).sum

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_0 : a 0 = 3 := by decide

@[category test, AMS 11]
theorem a_1 : a 1 = 5 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 8 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 14 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 26 := by decide

abbrev Target : Prop :=
    ¬ (
      ∃ n > 11, (a n).Prime
    )

end Problem
