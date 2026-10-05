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

- problem_id: O11545_conjecture1
- collection: oeis
- question_id: oeis:11545
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/11545.lean#conjecture1
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Wolfgang Haken (1977) conjectured that no term of this sequence is a perfect square, and estimated the probability that this conjecture is false to be smaller than $10^-9$.
- notes: OEIS A11545 -- https://oeis.org/A11545
- track: open
- answer_shape: proof
- source_stem: 11545
- source_namespace: OeisA11545
- source_theorem: conjecture1
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Real Int

/-- a n is the integer whose decimal digits are the first $n+1$ decimal digits of $\pi$. -/
noncomputable def a (n : ℕ) : ℕ :=
  (floor (Real.pi * (10 : ℝ) ^ n.cast)).toNat

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem a_0 : a 0 = 3 := by
  delta a
  norm_num [((Int.floor_eq_iff.mpr _) : ⌊π⌋ = ↑3), Int.toNat, false,
    le_of_lt Real.pi_gt_three, Real.pi_lt_four]

@[category test, AMS 11]
theorem a_1 : a 1 = 31 := by
  simp_all[a]
  exact (congr_arg _) ((Int.floor_eq_iff.2
    ⟨by linear_combination 10 * (.pi_gt_d20),
     by · linear_combination 10 * .pi_lt_d20⟩) : ⌊_⌋ = 31)

@[category test, AMS 11]
theorem a_2 : a 2 = 314 := by
  simp_all[a]
  exact (congr_arg _) ((Int.floor_eq_iff.mpr
    ⟨by · linear_combination 100 * .pi_gt_d20,
     by · linear_combination 100 * .pi_lt_d20⟩)) |>.trans (Int.toNat_natCast _)

@[category test, AMS 11]
theorem a_3 : a 3 = 3141 := by
  symm
  norm_num[a]
  exact (.symm ((congr_arg _) ((Int.floor_eq_iff.2
    ⟨by linear_combination 1000 * .pi_gt_d20,
     by linear_combination 1000 * .pi_lt_d20⟩) : ⌊_⌋ = 3141)))

abbrev Target : Prop :=
    ∀ n, ¬ IsSquare (a n)

end Problem
