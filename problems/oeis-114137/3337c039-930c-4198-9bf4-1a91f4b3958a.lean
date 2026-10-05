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

- problem_id: O114137_conjecture1_prove
- collection: oeis
- question_id: oeis:114137
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/114137.lean#conjecture1
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: In this powers of 2 sequence, does 1 occur infinitely often?
- notes: OEIS A114137 -- https://oeis.org/A114137
- track: open
- answer_shape: prove
- pair_id: O114137_conjecture1
- pair_role: prove
- source_stem: 114137
- source_namespace: OeisA114137
- source_theorem: conjecture1
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_eq_of a_1 a_2 a_3 a_4 a_5
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Nat

/--
The primary defining sequence `a`.
$a(n)$ is the difference between first odd semiprime > $2^n$ and $2^n$.
$$a(n) = \min \{s \mid s > 2^n \text{ and } s \text{ is an odd semiprime}\} - 2^n$$
-/
noncomputable def a (n : ℕ) : ℕ :=
  let m := 2^n
  let s : Set ℕ := { s | s > m ∧ s.IsSemiprime ∧ Odd s }
  sInf s - m

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category API, AMS 11]
lemma a_eq_of (n val : ℕ)
  (h_mem : val.IsSemiprime ∧ Odd val)
  (h_gt : 2^n < val)
  (h_min : ∀ x, 2^n < x → x < val → ¬ (x.IsSemiprime ∧ Odd x)) :
  a n = val - 2^n := by
  change sInf { s | s > 2^n ∧ s.IsSemiprime ∧ Odd s } - 2^n = val - 2^n
  have h_S : sInf { s | s > 2^n ∧ s.IsSemiprime ∧ Odd s } = val := by
    apply IsLeast.csInf_eq
    constructor
    · exact ⟨h_gt, h_mem⟩
    · rintro x ⟨hx1, hx2⟩
      by_contra! h
      exact h_min x hx1 h hx2
  rw [h_S]

@[category test, AMS 11]
theorem a_1 : a 1 = 7 := by
  apply a_eq_of 1 9 (by
    norm_num [IsSemiprime, IsAlmostPrime, ArithmeticFunction.cardFactors_apply,
      Nat.primeFactorsList]) (by norm_num)
  intro x h1 h2
  interval_cases x <;>
    norm_num [IsSemiprime, IsAlmostPrime, ArithmeticFunction.cardFactors_apply]

@[category test, AMS 11]
theorem a_2 : a 2 = 5 := by
  apply a_eq_of 2 9 (by
    norm_num [IsSemiprime, IsAlmostPrime, ArithmeticFunction.cardFactors_apply,
      Nat.primeFactorsList]) (by norm_num)
  intro x h1 h2
  interval_cases x <;>
    norm_num [IsSemiprime, IsAlmostPrime, ArithmeticFunction.cardFactors_apply]

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by
  apply a_eq_of 3 9 (by
    norm_num [IsSemiprime, IsAlmostPrime, ArithmeticFunction.cardFactors_apply,
      Nat.primeFactorsList]) (by norm_num)
  intro x h1 h2
  interval_cases x

@[category test, AMS 11]
theorem a_4 : a 4 = 5 := by
  apply a_eq_of 4 21 (by
    norm_num [IsSemiprime, IsAlmostPrime, ArithmeticFunction.cardFactors_apply,
      Nat.primeFactorsList]) (by norm_num)
  intro x h1 h2
  interval_cases x <;>
    norm_num [IsSemiprime, IsAlmostPrime, ArithmeticFunction.cardFactors_apply]

@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by
  apply a_eq_of 5 33 (by
    norm_num [IsSemiprime, IsAlmostPrime, ArithmeticFunction.cardFactors_apply,
      Nat.primeFactorsList]) (by norm_num)
  intro x h1 h2
  interval_cases x

abbrev Target : Prop :=
    Set.Infinite {n : ℕ | a n = 1}

end Problem
