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

- problem_id: O114216_conjecture_prove
- collection: oeis
- question_id: oeis:114216
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/114216.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is $a(33900)$ the last term equal to $1$?
- notes: OEIS A114216 -- https://oeis.org/A114216
- track: open
- answer_shape: prove
- pair_id: O114216_conjecture
- pair_role: prove
- source_stem: 114216
- source_namespace: OeisA114216
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/--
The primary defining sequence `a`.
$a(n)$ is the largest odd divisor of $a(n-1) + \textrm{prime}(n)$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | n' + 1 =>
    let pN : ℕ := Nat.nth Nat.Prime n'
    let prevA : ℕ := a n'
    let sumVal : ℕ := prevA + pN
    let nu2 : ℕ := padicValNat 2 sumVal
    sumVal / (2 ^ nu2)

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by
  rfl

abbrev Target : Prop :=
    ∀ n > 33900, a n ≠ 1

end Problem
