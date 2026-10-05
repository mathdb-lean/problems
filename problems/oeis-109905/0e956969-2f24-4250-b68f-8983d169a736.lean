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

- problem_id: O109905_conjecture_prove
- collection: oeis
- question_id: oeis:109905
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/109905.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: $a(n) = 0$ for $n = 1$, $6$, $30$ and $54$. Are there any others?
- notes: OEIS A109905 -- https://oeis.org/A109905
- track: open
- answer_shape: prove
- pair_id: O109905_conjecture
- pair_role: prove
- source_stem: 109905
- source_namespace: OeisA109905
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_1 a_2 a_3 a_4 a_5
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/--
$a(n)$ is the greatest prime of the form $k(n-k)+1$, where $k$ can take values
from $1$ to $\lfloor n/2 \rfloor$.
$a(n) = 0$ if no such prime exists.
-/
def a (n : ℕ) : ℕ :=
  (Finset.Icc 1 (n / 2))
  |>.image (fun k => k * (n - k) + 1)
  |>.filter Nat.Prime
  |>.sup id

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 3 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 5 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 7 := by decide

abbrev Target : Prop :=
    ∃ n : ℕ, n > 0 ∧ a n = 0 ∧ n ∉ ({1, 6, 30, 54} : Finset ℕ)

end Problem
