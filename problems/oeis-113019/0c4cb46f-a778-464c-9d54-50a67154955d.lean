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

- problem_id: O113019_conjecture
- collection: oeis
- question_id: oeis:113019
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/113019.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: $n=1$ and $32$ are fixed points. Are there any others? Yes: 9^9 = 387420489 is also a fixed point. - [Kenta Kitamura](https://oeis.org/wiki/User:Kenta_Kitamura), Aug 14 2026
- notes: OEIS A113019 -- https://oeis.org/A113019
- track: solved
- answer_shape: decide
- source_stem: 113019
- source_namespace: OeisA113019
- source_theorem: conjecture
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- context_lemmas: a_0 a_1 a_2 a_3 a_4
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

open Nat

/--
a n is the (Number of digits of n) raised to the power of (the digital root of n),
with appropriate adjustments for $n=0$.
-/
def a (n : ℕ) : ℕ :=
  -- The base: number of digits of n (adjusting n=0 to have 1 digit, like n=1).
  let numDigits : ℕ := (Nat.digits 10 (max 1 n)).length

  -- The exponent: digital root of n. This correctly yields 0 for n=0,
  -- and the standard 1..9 for n>0.
  let digitalRoot : ℕ := if n = 0 then 0 else (n - 1) % 9 + 1

  numDigits ^ digitalRoot

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by decide

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by decide

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ n : ℕ, a n = n → n = 1 ∨ n = 32

end Problem
