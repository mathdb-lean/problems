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

- problem_id: O70823_conjecture
- collection: oeis
- question_id: oeis:70823
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/70823.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: $a(n) \equiv 0 \pmod 3$ if $n > 2$. Is $a(n)$ always of the form $2^j \cdot 3^k \cdot s$ where $s$ is a squarefree number? Answer: False, $a(20)$ is divisible by $13^2$ but not by $13^3$.
- notes: OEIS A70823 -- https://oeis.org/A70823
- track: solved
- answer_shape: decide
- source_stem: 70823
- source_namespace: OeisA70823
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

/-- Number of digits of a natural number $n$ in base 10 (with 1 digit for 0). -/
def numDigitsBase10 (n : ℕ) : ℕ :=
  if n = 0 then 1 else Nat.log 10 n + 1

/-- Concatenate $x$ followed by $y$ in base 10. -/
def concatenate (x y : ℕ) : ℕ :=
  x * 10 ^ (numDigitsBase10 y) + y

/-- The sequence $a(1)=0, a(2)=1, a(n+2)=|\text{concat}(a(n+1),a(n))-\text{concat}(a(n),a(n+1))|$. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 =>
    let cat1 := concatenate (a (n + 2)) (a (n + 1))
    let cat2 := concatenate (a (n + 1)) (a (n + 2))
    ((cat1 : ℤ) - (cat2 : ℤ)).natAbs

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
theorem a_3 : a 3 = 9 := by
  decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 72 := by
  decide

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 243 := by
  decide

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ n : ℕ, 2 < n →
      a n ≡ 0 [MOD 3] ∧
        ∃ j k s : ℕ, a n = 2 ^ j * 3 ^ k * s ∧ Squarefree s

end Problem
