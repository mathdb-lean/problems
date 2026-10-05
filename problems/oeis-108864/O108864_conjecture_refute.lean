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

- problem_id: O108864_conjecture_refute
- collection: oeis
- question_id: oeis:108864
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/108864.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is $1155$ the last odd number in this sequence? ($1155$ is the $59$th term starting from $1$, corresponding to $a(58) = 1155$).
- notes: OEIS A108864 -- https://oeis.org/A108864
- track: open
- answer_shape: refute
- pair_id: O108864_conjecture
- pair_role: refute
- source_stem: 108864
- source_namespace: OeisA108864
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3 a_4
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Nat Finset Int

/--
The perfect deficiency of $n$ (A109883): the remainder after greedily subtracting
from $n$ its divisors in increasing order, skipping any divisor larger than the
current remainder.
-/
def perfectDeficiency (n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl (fun m d => if d ∣ n ∧ d ≤ m then m - d else m) n

/--
The condition for a number $n$ to be in the sequence.
It satisfies $0 < n$ and its perfect deficiency is $\le 10$.
-/
def A (n : ℕ) : Prop :=
  0 < n ∧ perfectDeficiency n ≤ 10

instance : DecidablePred A := by
  unfold A
  infer_instance

/--
The primary defining sequence `a`.
$a(n)$ is the $n$-th number (0-indexed) such that its perfect deficiency is $\le 10$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  n.nth A

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by
  have h1 : A 1 := by decide
  have hcnt : Nat.count A 1 = 0 := by decide
  have := Nat.nth_count (p := A) h1
  rwa [hcnt] at this

@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by
  have h2 : A 2 := by decide
  have hcnt : Nat.count A 2 = 1 := by decide
  have := Nat.nth_count (p := A) h2
  rwa [hcnt] at this

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by
  have h3 : A 3 := by decide
  have hcnt : Nat.count A 3 = 2 := by decide
  have := Nat.nth_count (p := A) h3
  rwa [hcnt] at this

@[category test, AMS 11]
theorem a_3 : a 3 = 4 := by
  have h4 : A 4 := by decide
  have hcnt : Nat.count A 4 = 3 := by decide
  have := Nat.nth_count (p := A) h4
  rwa [hcnt] at this

@[category test, AMS 11]
theorem a_4 : a 4 = 5 := by
  have h5 : A 5 := by decide
  have hcnt : Nat.count A 5 = 4 := by decide
  have := Nat.nth_count (p := A) h5
  rwa [hcnt] at this

abbrev Target : Prop :=
    ¬ (
      ∀ n > 58, Even (a n)
    )

end Problem
