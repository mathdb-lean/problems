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

- problem_id: O87455_conjecture_prove
- collection: oeis
- question_id: oeis:87455
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/87455.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: It is an open question whether or not this sequence satisfies Benford's law [Berger-Hill, 2017; Arno Berger, email, Jan 06 2017]. - N. J. A. Sloane, Feb 08 2017
- notes: OEIS A87455 -- https://oeis.org/A87455
- track: open
- answer_shape: prove
- pair_id: O87455_conjecture
- pair_role: prove
- source_stem: 87455
- source_namespace: OeisA87455
- source_theorem: conjecture
- source_category: research open
- source_ams: 11 60
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3 a_4
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- The primary defining sequence `a`, satisfying $a(n) = 2 a(n-1) - 3 a(n-2)$ for $n \ge 2$,
with initial values $a(0)=1$ and $a(1)=1$. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => 2 * a (n + 1) - 3 * a n

/-- The decimal significand of an integer `x`: the unique real number $S(x) \in [1, 10)$ such that
$|x| = S(x) \cdot 10^k$ for some integer $k$, with the convention $S(0) = 0$. -/
noncomputable def significand (x : ℤ) : ℝ :=
  (x.natAbs : ℝ) / 10 ^ ((Nat.digits 10 x.natAbs).length - 1)

/-- A sequence of integers satisfies Benford's law if, for every $t \in [1, 10)$, the asymptotic
relative frequency of terms whose decimal significand is at most $t$ equals $\log_{10} t$
(Berger-Hill). This is strictly stronger than the law for the leading digit alone. -/
def SatisfiesBenford (s : ℕ → ℤ) : Prop :=
  ∀ t ∈ Set.Ico (1 : ℝ) 10,
    Filter.Tendsto
      (fun N : ℕ =>
        ((Finset.range N).filter (fun n => significand (s n) ≤ t)).card / (N : ℝ))
      Filter.atTop
      (nhds (Real.logb 10 t))

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by rfl

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by rfl

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = -1 := by rfl

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = -5 := by rfl

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = -7 := by rfl

abbrev Target : Prop :=
    SatisfiesBenford a

end Problem
