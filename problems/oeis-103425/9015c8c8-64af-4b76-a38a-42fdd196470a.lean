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

- problem_id: O103425_conjecture
- collection: oeis
- question_id: oeis:103425
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/103425.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: The current sequence contains primes, including $3, 5, 41, 21523361$. Is there an $(a, b, c)$ weighted tribonacci sequence with $a, b, c$ relatively prime which is prime-free? Yes: take $(a, b, c) = (1, 1, -1)$ and the constant sequence $x(n) = 4$. The linked Lean proof is by Kenta Kitamura.
- notes: OEIS A103425 -- https://oeis.org/A103425
- track: solved
- answer_shape: decide
- source_stem: 103425
- source_namespace: OeisA103425
- source_theorem: conjecture
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3 a_4
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

/--
The primary defining sequence `a`.
$a(n)$ is defined by the recurrence relation $a(n) = 3 a(n-1) + a(n-2) - 3 a(n-3)$
with initial terms $a(0)=1, a(1)=3, a(2)=5$.
-/
def a : ℕ → ℕ
  | 0 => 1
  | 1 => 3
  | 2 => 5
  | n + 3 => 3 * a (n + 2) + a (n + 1) - 3 * a n

def IsWeightedTribonacci (a b c : ℤ) (x : ℕ → ℤ) : Prop :=
  ∀ n, x (n + 3) = a * x (n + 2) + b * x (n + 1) + c * x n

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by decide

@[category test, AMS 11]
theorem a_1 : a 1 = 3 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 5 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 15 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 41 := by decide

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ (a b c : ℤ) (x : ℕ → ℤ),
          Nat.gcd (Int.gcd a b) c.natAbs = 1 ∧
          IsWeightedTribonacci a b c x ∧
          ∀ n, ¬ (x n).natAbs.Prime

end Problem
