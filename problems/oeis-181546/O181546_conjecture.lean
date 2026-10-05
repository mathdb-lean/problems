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

- problem_id: O181546_conjecture
- collection: oeis
- question_id: oeis:181546
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/181546.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Conjecture: Given $F(n,L) = \sum_{k=0}^{\lfloor n/2 \rfloor} \binom{n-k}{k}^L$, then $\lim_{n\to\infty} F(n+1,L)/F(n,L) = (\mathrm{Fibonacci}(L)\sqrt{5} + \mathrm{Lucas}(L))/2$ for $L \ge 0$ where $\mathrm{Fibonacci}(n) = \mathrm{A000045}(n)$ and $\mathrm{Lucas}(n) = \mathrm{A000032}(n)$.
- notes: OEIS A181546 -- https://oeis.org/A181546
- track: solved
- answer_shape: proof
- source_stem: 181546
- source_namespace: OeisA181546
- source_theorem: conjecture
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3 a_4
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Filter Real

/-- The generalized sum $F(n, L) = \sum_{k=0}^{\lfloor n/2 \rfloor} \binom{n-k}{k}^L$. -/
def F (n L : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n / 2 + 1), ((n - k).choose k) ^ L

/-- $a(n) = \sum_{k=0}^{\lfloor n/2 \rfloor} \binom{n-k}{k}^4$. -/
def a (n : ℕ) : ℕ := F n 4

/-- Lucas numbers $L(0) = 2, L(1) = 1, L(n) = L(n-1) + L(n-2)$. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n

/-- Conjectured limit value for $F(n+1, L) / F(n, L)$. -/
noncomputable def limitValue (L : ℕ) : ℝ :=
  (Nat.fib L * sqrt 5 + lucas L) / 2

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by decide

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 17 := by decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 83 := by decide

abbrev Target : Prop :=
    ∀ (L : ℕ),
      Tendsto (fun n => (F (n + 1) L : ℝ) / (F n L : ℝ)) atTop (nhds (limitValue L))

end Problem
