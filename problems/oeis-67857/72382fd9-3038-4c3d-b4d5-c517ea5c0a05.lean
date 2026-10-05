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

- problem_id: O67857_conjecture
- collection: oeis
- question_id: oeis:67857
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/67857.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: The terms are not all positive. The first negative one is $a(30) = -22690644647302814715858124800000$. Conjecture: $a(n) < 0$ if and only if A001221(n) is an odd number $\ge 3$. This conjecture is false. A counterexample is the product of all primes at most $1000$, which has $168$ distinct prime factors and a negative sequence value. The counterexample and formal proof were developed by Codex (GPT-6), prompted by Samuel Schlesinger.
- notes: OEIS A67857 -- https://oeis.org/A67857
- track: solved
- answer_shape: decide
- source_stem: 67857
- source_namespace: OeisA67857
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

open ArithmeticFunction Finset

/-- The sequence $a(n) = n! \sum_{d \mid n} \mu(n/d) H_d$ for $n \ge 1$, and $a(0) = 0$. -/
def a (n : ℕ) : ℚ :=
  if n = 0 then 0
  else
    (n.factorial : ℚ) *
      ∑ d ∈ n.divisors, ((moebius (n / d) : ℤ) : ℚ) * harmonic d

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  decide +kernel

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  decide +kernel

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 5 := by
  decide +kernel

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 14 := by
  decide +kernel

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 154 := by
  decide +kernel

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ n : ℕ, 0 < n →
      (a n < 0 ↔ Odd (cardDistinctFactors n) ∧ 3 ≤ cardDistinctFactors n)

end Problem
