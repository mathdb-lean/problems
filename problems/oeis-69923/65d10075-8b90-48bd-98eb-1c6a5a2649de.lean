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

- problem_id: O69923_conjecture
- collection: oeis
- question_id: oeis:69923
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/69923.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: For any $n > 0$, is there always at least one prime $p$ such that $2^n \le p \le 2^n + \mathrm{prime}(n)$? (checked up to $n = 250$). In this case, that would be stronger than the Schinzel conjecture: "for $m > 1$ there's at least one prime $p$ such that $m \le p \le m + \log(m)^2$" since, for $n > 2$, $\mathrm{prime}(n) < \log(2^n)^2 = n^2 \log(2)$.
- notes: OEIS A69923 -- https://oeis.org/A69923
- track: open
- answer_shape: proof
- source_stem: 69923
- source_namespace: OeisA69923
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_1 a_2 a_3 a_4
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Finset

/-- Number of primes $p$ such that $2^n \le p \le 2^n + \mathrm{prime}(n)$. -/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let p := Nat.nth Nat.Prime (n - 1)
    ((Icc (2 ^ n) (2 ^ n + p)).filter Nat.Prime).card

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by
  change ((Icc (2 ^ 1) (2 ^ 1 + Nat.nth Nat.Prime 0)).filter Nat.Prime).card = 2
  rw [Nat.nth_prime_zero_eq_two]
  decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by
  change ((Icc (2 ^ 2) (2 ^ 2 + Nat.nth Nat.Prime 1)).filter Nat.Prime).card = 2
  rw [Nat.nth_prime_one_eq_three]
  decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by
  change ((Icc (2 ^ 3) (2 ^ 3 + Nat.nth Nat.Prime 2)).filter Nat.Prime).card = 2
  rw [Nat.nth_prime_two_eq_five]
  decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 3 := by
  change ((Icc (2 ^ 4) (2 ^ 4 + Nat.nth Nat.Prime 3)).filter Nat.Prime).card = 3
  rw [Nat.nth_prime_three_eq_seven]
  decide

abbrev Target : Prop :=
    ∀ (n : ℕ) (hn : 0 < n),
      1 ≤ a n

end Problem
