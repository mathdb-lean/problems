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

- problem_id: O103151_conjecture
- collection: oeis
- question_id: oeis:103151
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/103151.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Conjecture: all items for $n \ge 4$ are greater than or equal to $1$. This is a stronger conjecture than the Goldbach conjecture.
- notes: OEIS A103151 -- https://oeis.org/A103151
- track: open
- answer_shape: proof
- source_stem: 103151
- source_namespace: OeisA103151
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_1 a_2 a_3 a_4 a_5
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/--
The primary defining sequence `a`.
`a n` is the number of decompositions of `2n+1` into `2p+q`, where `p` and `q` are both odd primes.
-/
def a (n : ℕ) : ℕ :=
  -- We count the number of odd primes $p$ that satisfy the constraints.
  -- The range $p \le n$ is sufficient, as larger $p$ would make $q \le 1$, which is not prime.
  Finset.card (Finset.filter (fun p : ℕ =>
    -- p must be an odd prime.
    p.Prime ∧
    p ≠ 2 ∧
    -- Ensure the expression for $q$ is positive, so Nat subtraction is well-defined for prime $q$.
    2 * p < 2 * n + 1 ∧
    -- q = 2n+1 - 2p must be prime (and is automatically odd).
    Nat.Prime (2 * n + 1 - 2 * p)
  ) (Finset.range (n + 1)))

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by decide

abbrev Target : Prop :=
    ∀ (n : ℕ) (hn : n ≥ 4),
      a n ≥ 1

end Problem
