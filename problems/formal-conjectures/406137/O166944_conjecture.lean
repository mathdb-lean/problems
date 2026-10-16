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

- problem_id: O166944_conjecture
- collection: oeis
- question_id: oeis:166944
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/166944.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Conjecture: Every record of differences $a(n)-a(n-1)$ more than 5 is the greater of twin primes (A006512).
- notes: OEIS A166944 -- https://oeis.org/A166944
- track: open
- answer_shape: proof
- source_stem: 166944
- source_namespace: OeisA166944
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_1 a_2 a_3 a_4 a_5
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- Defining recurrence for $a(n)$. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 2
  | n + 2 =>
    let prev := a (n + 1)
    let idx := n + 2
    if idx % 2 = 0 then prev + Nat.gcd idx prev
    else prev + Nat.gcd (idx - 2) prev

/-- The difference sequence $d(n) = a(n) - a(n-1)$ for $n \ge 2$. -/
def d (n : ℕ) : ℕ := a n - a (n - 1)

/-- A prime $p$ is the greater of a twin prime pair if $p$ and $p - 2$ are both prime. -/
def IsGreaterTwinPrime (p : ℕ) : Prop := p.Prime ∧ (p - 2).Prime

/--
A value $R$ is a difference record if there exists $n \ge 2$ such that $d(n) = R$ and $R$
is strictly larger than all previous differences $d(k)$ for $2 \le k < n$.-/
def IsDifferenceRecord (R : ℕ) : Prop :=
  ∃ n : ℕ, 2 ≤ n ∧ d n = R ∧ ∀ k : ℕ, 2 ≤ k → k < n → d k < R

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 4 := by decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 5 := by decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 6 := by decide

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 9 := by decide

abbrev Target : Prop :=
    ∀ (R : ℕ) (hR : 5 < R) (hrec : IsDifferenceRecord R),
      IsGreaterTwinPrime R

end Problem
