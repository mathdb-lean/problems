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

- problem_id: O145355_conjecture
- collection: oeis
- question_id: oeis:145355
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/145355.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: This sequence suggests that the distance between a factorial and the closest power is tightly bounded.
- notes: OEIS A145355 -- https://oeis.org/A145355
- track: open
- answer_shape: proof
- source_stem: 145355
- source_namespace: OeisA145355
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_2 a_3 a_4 a_5
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Real

/-- The sequence $a(n) = \mathrm{round}(\mathrm{round}(\sqrt{n!})/|(\mathrm{round}(\sqrt{n!}))^2 - n!|)$. -/
noncomputable def a (n : ℕ) : ℕ :=
  let fact_r : ℝ := Nat.cast (Nat.factorial n)
  let r_int : ℤ := round (sqrt fact_r)
  let r_real : ℝ := Int.cast r_int
  let den_val : ℝ := abs (r_real ^ 2 - fact_r)
  (round (r_real / den_val)).toNat

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  delta a
  norm_num [((Int.floor_eq_iff.mpr _) : _ = (1 : ℤ)), ← not_lt, false, round_eq, Real.sqrt_lt',
    ← lt_sub_iff_add_lt]

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by
  delta a
  norm_num only [Nat.factorial, round_eq, ((Int.floor_eq_iff.2 _) : _ = (2 : ℤ)), Int.toNat,
    ← not_lt, true, abs_of_neg, ← lt_sub_iff_add_lt, Real.sqrt_lt, and_self_iff]

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 5 := by
  delta a
  norm_num [Int.toNat, show round (sqrt 24) = 5 by
    norm_num only [← not_lt, false, round_eq, true, Real.sqrt_lt', Int.floor_eq_iff,
      ← lt_sub_iff_add_lt, and_self], round_eq, false, Nat.factorial]

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 11 := by
  delta a
  norm_num [((Int.floor_eq_iff.2 _) : _ = (11 : ℤ)), round_eq, ← not_lt, Int.toNat,
    ← lt_sub_iff_add_lt, Real.sqrt_lt]

abbrev Target : Prop :=
    ∃ C : ℕ, ∀ n : ℕ, 2 ≤ n → a n ≤ C

end Problem
