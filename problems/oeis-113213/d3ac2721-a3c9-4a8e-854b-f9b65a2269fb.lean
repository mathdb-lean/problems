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

- problem_id: O113213_conjecture
- collection: oeis
- question_id: oeis:113213
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/113213.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Conjecture: $a(n) = O(n^3)$. The source defines $a(n)$ as the least $m$ with $2^n - m$ and $2^n + m$ prime, so it implicitly asserts that such an $m$ exists. Since `a n = 0` when no such $m$ exists, the existence of a prime pair is stated explicitly for all sufficiently large $n$.
- notes: OEIS A113213 -- https://oeis.org/A113213
- track: open
- answer_shape: proof
- source_stem: 113213
- source_namespace: OeisA113213
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_1 a_2 a_3 a_4 a_5
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Nat

/--
a n is the smallest number m such that $2^n - m$ and $2^n + m$ are primes.
Computed by checking elements from $0$ to $2^n$, as any larger $m$ would make
$2^n - m = 0$ which is not prime.
-/
def a (n : ℕ) : ℕ :=
  let s := (List.range (2^n + 1)).filter (fun m => (2^n - m).Prime ∧ (2^n + m).Prime)
  s.headD 0

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 3 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 3 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 9 := by decide

abbrev Target : Prop :=
    (∀ᶠ n : ℕ in Filter.atTop, ∃ m, (2 ^ n - m).Prime ∧ (2 ^ n + m).Prime) ∧
    (fun n : ℕ => (a n : ℝ)) =O[Filter.atTop] (fun n : ℕ => (n ^ 3 : ℝ))

end Problem
