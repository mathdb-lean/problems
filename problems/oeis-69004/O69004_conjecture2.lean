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

- problem_id: O69004_conjecture2
- collection: oeis
- question_id: oeis:69004
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/69004.lean#conjecture2
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Stronger conjecture: Let $\pi(n)$ be the prime counting function (A000720). Then $\pi(n) \ge a(n) \ge \pi(n)/5$ for $n > 1$, with the following equalities: $\pi(2) = a(2)$, $\pi(10) = a(10)$ and $a(12) = \pi(12)/5$. This conjunction is false: its upper bound $\pi(n) \ge a(n)$ fails at $n = 512720 = 2^4 \cdot 5 \cdot 13 \cdot 17 \cdot 29$, where $a(n) = 42666$ and $\pi(n) = 42493$. The OEIS entry tabulates $a$ only up to $n = 10^4$. The lower bound and the three equalities are unaffected; see `conjecture2.variants.without_upper_bound`.
- notes: OEIS A69004 -- https://oeis.org/A69004
- track: solved
- answer_shape: proof
- source_stem: 69004
- source_namespace: OeisA69004
- source_theorem: conjecture2
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_1 a_2 a_3 a_4 a_5
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Finset

/-- Number of times $n^2 + s^2$ is prime for positive integers $s < n$. -/
def a (n : ℕ) : ℕ :=
  ∑ s ∈ Ico 1 n, if (n ^ 2 + s ^ 2).Prime then 1 else 0

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by
  decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by
  decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by
  decide

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 2 := by
  decide

abbrev Target : Prop :=
    ¬ (
        (∀ n : ℕ, 1 < n → Nat.primeCounting n ≥ a n) ∧
        (∀ n : ℕ, 1 < n → 5 * a n ≥ Nat.primeCounting n) ∧
        Nat.primeCounting 2 = a 2 ∧
        Nat.primeCounting 10 = a 10 ∧
        5 * a 12 = Nat.primeCounting 12)

end Problem
