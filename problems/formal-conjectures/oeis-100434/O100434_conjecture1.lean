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

- problem_id: O100434_conjecture1
- collection: oeis
- question_id: oeis:100434
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/100434.lean#conjecture1
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **Conjecture from Creighton Dement (A100434)**: Let the auxiliary sequences c, d, e, f, g, b be defined as specified. Then for all $n \ge 0$, $c(n) + d(n) = b(n)$. **Proof outline**: strong two-step induction on the paired recurrences. The even/odd cases are coupled through closed identities between consecutive terms of the relevant pair of sequences (here $c, d$), and the induction step is discharged by `rfl`-level unfolding of the definitions plus linear arithmetic. (Numerically verified for $n < 600$ before formalization.)
- notes: OEIS A100434 -- https://oeis.org/A100434
- track: solved
- answer_shape: proof
- source_stem: 100434
- source_namespace: OeisA100434
- source_theorem: conjecture1
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3 a_4 a_even a_odd
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- The primary defining sequence `a`, which is the expansion of the generating function
$(1+x)(3+x)/(1+6x^2+x^4)$. It satisfies the recurrence $a(n) = -6 a(n-2) - a(n-4)$
for $n \ge 4$. -/
def a : ℕ → ℤ
  | 0 => 3
  | 1 => 4
  | 2 => -17
  | 3 => -24
  | n + 4 => -6 * a (n + 2) - a n

/-- $c(n)$ starts with $(1, -3, -7, 17)$ and satisfies the same recurrence as `a` -/
def c : ℕ → ℤ
  | 0 => 1
  | 1 => -3
  | 2 => -7
  | 3 => 17
  | n + 4 => -6 * c (n + 2) - c n

/-- $d(n)$ starts with $(2, 4, -10, -24)$ and satisfies the same recurrence as `a` -/
def d : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => -10
  | 3 => -24
  | n + 4 => -6 * d (n + 2) - d n

/-- $b(2n) = -c(2n+1)$, $b(2n+1) = c(2n)$ -/
-- Sign corrected (even branch): see https://github.com/google-deepmind/formal-conjectures/issues/5025
def b (n : ℕ) : ℤ :=
  if n % 2 = 0 then -c (n + 1)
  else c (n - 1)

/-- $e(2n) = d(2n)/2$, $e(2n+1) = - d(2n)/2$ -/
def e (n : ℕ) : ℤ :=
  if n % 2 = 0 then
    d n / 2
  else
    -- n is positive, so n-1 is safe in ℕ
    - (d (n - 1) / 2)

/-- $f(2n) = f(2n+1) = d(2n+1)/2$ -/
def f (n : ℕ) : ℤ :=
  let m := n / 2
  d (2 * m + 1) / 2

/-- $g(2n) = 0, g(2n+1) = c(2n+1)$ -/
def g (n : ℕ) : ℤ :=
  if n % 2 = 0 then 0
  else c n

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 3 := by rfl

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 4 := by rfl

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = -17 := by rfl

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = -24 := by rfl

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 99 := by rfl

/--
For all $n \ge 0$, we have $a(2n) = - c(2n+1)$.
-/
@[category textbook, AMS 11]
theorem a_even (n : ℕ) : a (2 * n) = - c (2 * n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero =>
    rfl
  | one =>
    rfl
  | more k ih1 ih2 =>
    have h_eq : 2 * (k + 2) = 2 * k + 4 := by omega
    have h_eq2 : 2 * (k + 2) + 1 = 2 * k + 5 := by omega
    rw [h_eq2, h_eq]
    have h_lhs : a (2 * k + 4) = -6 * a (2 * k + 2) - a (2 * k) := by rfl
    have h_rhs : c (2 * k + 5) = -6 * c (2 * k + 3) - c (2 * k + 1) := by rfl
    rw [h_lhs, h_rhs]
    have ih2' : a (2 * k + 2) = - c (2 * k + 3) := by
      have h_eq_ih : 2 * (k + 1) = 2 * k + 2 := by omega
      have h_eq2_ih : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
      rw [← h_eq2_ih, ← h_eq_ih]
      exact ih2
    rw [ih1, ih2']
    ring

/--
For all $n \ge 0$, we have $a(2n+1) = d(2n+1)$.
-/
@[category textbook, AMS 11]
theorem a_odd (n : ℕ) : a (2 * n + 1) = d (2 * n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero =>
    rfl
  | one =>
    rfl
  | more k ih1 ih2 =>
    have h_eq : 2 * (k + 2) + 1 = 2 * k + 5 := by omega
    rw [h_eq]
    have h_lhs : a (2 * k + 5) = -6 * a (2 * k + 3) - a (2 * k + 1) := by rfl
    have h_rhs : d (2 * k + 5) = -6 * d (2 * k + 3) - d (2 * k + 1) := by rfl
    rw [h_lhs, h_rhs]
    have ih2' : a (2 * k + 3) = d (2 * k + 3) := by
      have h_eq_ih : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
      rw [← h_eq_ih]
      exact ih2
    rw [ih1, ih2']

abbrev Target : Prop :=
    ∀ (n : ℕ),
      c n + d n = b n

end Problem
