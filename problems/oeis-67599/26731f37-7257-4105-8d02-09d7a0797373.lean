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

- problem_id: O67599_conjecture_refute
- collection: oeis
- question_id: oeis:67599
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/67599.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: "$a(31) = a(177147) = 311$. Is there any solution to $a(n) = n$? - _Franklin T. Adams-Watters_, Dec 18 2006"
- notes: OEIS A67599 -- https://oeis.org/A67599
- track: open
- answer_shape: refute
- pair_id: O67599_conjecture
- pair_role: refute
- source_stem: 67599
- source_namespace: OeisA67599
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_2 a_3 a_4 a_5 a_6
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- Concatenates two natural numbers $a$ and $b$ base 10. -/
def concatenateNats (a b : ℕ) : ℕ :=
  a * (10 ^ (Nat.digits 10 b).length) + b

/-- Decimal encoding of the prime factorization of $n$. -/
def a (n : ℕ) : ℕ :=
  if n < 2 then 0
  else
    let factors : List ℕ := n.primeFactorsList.dedup
    let flat_list : List ℕ := factors.flatMap fun p ↦ [p, n.primeFactorsList.count p]
    flat_list.foldl concatenateNats 0

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem a_2 : a 2 = 21 := by
  decide +kernel

@[category test, AMS 11]
theorem a_3 : a 3 = 31 := by
  decide +kernel

@[category test, AMS 11]
theorem a_4 : a 4 = 22 := by
  decide +kernel

@[category test, AMS 11]
theorem a_5 : a 5 = 51 := by
  decide +kernel

@[category test, AMS 11]
theorem a_6 : a 6 = 2131 := by
  decide +kernel

abbrev Target : Prop :=
    ¬ (
      ∃ n : ℕ, 2 ≤ n ∧ a n = n
    )

end Problem
