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

- problem_id: O112970_conjecture1
- collection: oeis
- question_id: oeis:112970
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/112970.lean#conjecture1
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Conjecture: $a(2^n)=a(2^(n+1)+1)=\textrm{A033638}(n)$. This formalizes the equality $a(2^n) = a(2^(n+1)+1)$.
- notes: OEIS A112970 -- https://oeis.org/A112970
- track: solved
- answer_shape: proof
- source_stem: 112970
- source_namespace: OeisA112970
- source_theorem: conjecture1
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3 a_4
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/--
a n is the generalized Stern sequence, defined by the recurrence relations:
$a(2n+1) = a(n)$ and $a(2n) = a(n)$ + $a(n-2)$ with $a(0) = 1$, $a(1) = 1$
and $a(n) = 0$ for $n \le -1$.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 1
  else if n = 1 then 1
  else
    let k := n / 2
    if n % 2 = 1 then -- Odd case: a(2k + 1) = a(k)
      a k
    else -- Even case: a(2k) = a(k) + a(k - 2)
      let aPrev : ℕ :=
        -- a(m) is 0 if m < 0. Equivalent to checking k < 2 for the argument k-2.
        if k < 2 then 0
        else a (k - 2)
      a k + aPrev
termination_by n

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by unfold a; rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by unfold a; rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by unfold a; unfold a; unfold a; rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by unfold a; unfold a; rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 2 := by unfold a; unfold a; unfold a; unfold a; rfl

abbrev Target : Prop :=
    ∀ (n : ℕ),
      a (2^n) = a (2^(n + 1) + 1)

end Problem
