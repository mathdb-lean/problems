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

- problem_id: O22030_conjecture
- collection: oeis
- question_id: oeis:22030
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/22030.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Conjecture: $a(n) = 4 a(n-1) - a(n-3) + a(n-4)$. - Colin Barker, Feb 16 2012
- notes: OEIS A22030 -- https://oeis.org/A22030
- track: solved
- answer_shape: proof
- source_stem: 22030
- source_namespace: OeisA22030
- source_theorem: conjecture
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3 a_4 a_5
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/--
For even $n$, $a(n+2)$ is the greatest integer such that $a(n+2)/a(n+1) < a(n+1)/a(n)$;
for odd $n$, the least integer such that $a(n+2)/a(n+1) > a(n+1)/a(n)$;
$a(0) = 4, a(1) = 16$.
-/
def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 4
  | 1 => 16
  | n + 2 =>
    if Even n then
      (a (n + 1) ^ 2 + a n - 1) / a n - 1
    else
      (a (n + 1) ^ 2) / a n + 1

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem a_0 : a 0 = 4 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 16 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 63 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 249 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 984 := by rfl

@[category test, AMS 11]
theorem a_5 : a 5 = 3889 := by rfl

abbrev Target : Prop :=
    ∀ (n : ℕ) (hn : 4 ≤ n),
      a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)

end Problem
