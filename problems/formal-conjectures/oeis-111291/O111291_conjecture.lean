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

- problem_id: O111291_conjecture
- collection: oeis
- question_id: oeis:111291
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/111291.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Simon Colton conjectures that the number of refactorable numbers less than $x$ is at least $\frac{x}{2\log x}$. This is an asymptotic claim, so we state it for sufficiently large $x$. In this form it is a theorem: Zelinsky [Ze02, Theorem 7] proved that for every $k$ the number of refactorable numbers $\le n$ exceeds $k \pi(n)$ for all sufficiently large $n$, and $\pi(n) \sim n / \log n$. It also follows from Spiro's asymptotic [Sp85], by which the count is $\frac{x}{\sqrt{\log x}} (\log \log x)^{-1 + o(1)}$. See `colton_conjecture` for the pointwise conjecture that remains open.
- notes: OEIS A111291 -- https://oeis.org/A111291
- track: solved
- answer_shape: proof
- source_stem: 111291
- source_namespace: OeisA111291
- source_theorem: conjecture
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Nat Finset Real

/-- Helper function: number of refactorable numbers $\le m$. -/
def countRefactorableNat (m : ℕ) : ℕ :=
  (Icc 1 m).filter (fun k => k.divisors.card ∣ k) |>.card

/--
`a n` is the number of refactorable numbers $\le 10^n$.
A number $k$ is refactorable if its number of divisors, $\tau(k)$, divides $k$.
-/
def a (n : ℕ) : ℕ :=
  countRefactorableNat (10 ^ n)

/--
`countRefactorable x` is the number of refactorable numbers $\le x$.
-/
noncomputable def countRefactorable (x : ℝ) : ℕ :=
  if _hx : x ≥ 1 then
    countRefactorableNat (Int.toNat (floor x))
  else
    0

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 4 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 16 := by rfl

abbrev Target : Prop :=
    ∀ᶠ x in Filter.atTop,
        (countRefactorable x : ℝ) ≥ x / (2 * Real.log x)

end Problem
