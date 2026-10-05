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

- problem_id: O112521_conjecture
- collection: oeis
- question_id: oeis:112521
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/112521.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Conjecture: Starting with $n=1$, $a(n)$ is the main diagonal of the array $T(n, k)$.
- notes: OEIS A112521 -- https://oeis.org/A112521
- track: solved
- answer_shape: proof
- source_stem: 112521
- source_namespace: OeisA112521
- source_theorem: conjecture
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3 a_4 a_5
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Nat Int Finset

/--
`a n` is the $n$-th term of the sequence related to NOR bracketings.
-/
def a (n : ℕ) : ℕ :=
  (∑ j ∈ range n,
    let c1 : ℕ := (2 * j).choose j
    let c2Top : ℕ := 2 * n - (j + 2)
    let c2Bot : ℕ := n - (j + 1)
    let c2 : ℕ := c2Top.choose c2Bot
    let termMagnitude : ℤ := c1 * c2

    if j % 2 = 0 then termMagnitude else -termMagnitude
  ).toNat

/--
`T n k` is the array defined as $T(1,1) = 1$, $T(i,j) = 0$ if $i<1$ or $j<1$,
$T(n,k) = T(n,k-2) + T(n,k-1) - 2 T(n-1,k-1) + T(n-1,k) + T(n-2,k)$.
-/
def T (n k : ℕ) : ℤ :=
  if n = 0 ∨ k = 0 then 0
  else if n = 1 ∧ k = 1 then 1
  else
    T n (k - 2) + T n (k - 1) - 2 * T (n - 1) (k - 1) + T (n - 1) k + T (n - 2) k
termination_by n + k

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by decide

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 6 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 4 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 60 := by decide

abbrev Target : Prop :=
    ∀ (n : ℕ), n ≥ 1 → (a n : ℤ) = T n n

end Problem
