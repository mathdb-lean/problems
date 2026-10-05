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

- problem_id: O114362_conjecture1
- collection: oeis
- question_id: oeis:114362
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/114362.lean#conjecture1
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Conjecture: if an integer $n > 1$ is odd, then $\zeta(2n)/\zeta(n)^2$ is irrational. Cf. W. Kohnen (link) and my conjecture in A348829. - Thomas Ordowski, Jan 05 2022
- notes: OEIS A114362 -- https://oeis.org/A114362
- track: open
- answer_shape: proof
- source_stem: 114362
- source_namespace: OeisA114362
- source_theorem: conjecture1
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open scoped Nat Real
open Filter
open Complex

/--
The primary defining sequence `a`.
Numerator of $\zeta(4n)/\zeta(2n)^2$ (with $a(0)=2$ instead of $-2$).
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then
    2
  else
    let b4n : ℚ := bernoulli (4 * n)
    let b2n : ℚ := bernoulli (2 * n)
    let binomQn : ℚ := ↑(Nat.choose (4 * n) (2 * n))
    let qN : ℚ := -2 * b4n / (b2n * b2n * binomQn)
    qN.num.natAbs

/-- `t n` is used in the second conjecture. -/
noncomputable def t (n : ℕ) : ℝ :=
  (riemannZeta (2 * (n : ℂ))).re / ((riemannZeta (n : ℂ)).re ^ 2)

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem a_0 : a 0 = 2 := by
  congr

@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by
  simp_all [a]
  norm_num only [bernoulli_eq_bernoulli'_of_ne_one, bernoulli'_four, bernoulli'_two, Nat.choose]

@[category test, AMS 11]
theorem a_2 : a 2 = 6 := by
  delta a
  norm_num +decide
    [bernoulli_eq_bernoulli'_of_ne_one, bernoulli'_eq_zero_of_odd, Int.natAbs_eq_iff, Nat.choose]
  rw [bernoulli'_def]
  have α := sum_bernoulli'
  norm_num only
    [←eq_sub_of_add_eq' (α _ ▸ Finset.sum_range_succ _ _).symm ▸ mul_div_cancel_left₀ _,
      Finset.sum_range_succ, or_false, or_true, Nat.choose]

@[category test, AMS 11]
theorem a_3 : a 3 = 691 := by
  delta and a
  norm_num [bernoulli_eq_bernoulli'_of_ne_one, two_mul, Nat.cast_choose]
  rw [bernoulli'_def, bernoulli'_def]
  have := sum_bernoulli'
  have R M := this (M+1) ▸ Finset.sum_range_succ _ _
  norm_num only
    [Nat.choose, ←sub_eq_of_eq_add' (R _) ▸ mul_div_cancel_left₀ _, Finset.sum_range_succ]

abbrev Target : Prop :=
    ∀ (n : ℕ) (hn_gt_one : 1 < n) (hn_odd : Odd n),
      Irrational ((riemannZeta (2 * n : ℂ) / (riemannZeta (n : ℂ)) ^ 2).re)

end Problem
