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

- problem_id: E945_prove
- collection: erdos
- question_id: erdos:945
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/945.lean#erdos_945
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that $F(x) \leq (\log x)^{O(1)}$?
- notes: Erdos Problem 945 -- https://www.erdosproblems.com/945
- track: open
- answer_shape: prove
- pair_id: E945
- pair_role: prove
- source_stem: 945
- mathdb_ref: erdos:945
- source_namespace: Erdos945
- source_theorem: erdos_945
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Real

namespace Problem

abbrev τ  := fun (n : ℕ) => n.divisors.card

/--
Let $F(x)$ be the maximal $k$ such that there exist $n+1, \dots, n+k \le x$
with $τ(n+1), \dots, τ(n+k)$ all distinct, where $τ(m)$ counts the divisors of $m$. -/
noncomputable def F (x : ℝ) : ℕ :=
  sSup {k | ∃ (n : ℕ), n + k ≤ x ∧ (Set.Ioc n (n + k)).InjOn τ}

-- Implementation note: we define a Prop here and below to be able to easily formulate
-- the equivalence between the two variants. Because the theorems require `answer(sorry)` we
-- can't handle this with `type_of%`.
def Erdos945Prop : Prop := ∃ O : ℝ → ℝ, O =O[atTop] (1 : ℝ → ℝ) ∧ ∀ᶠ x in atTop, F x ≤ log x ^ O x

def Erdos945Constant : Prop :=
  ∃ C > (0 : ℝ),  ∀ᶠ x : ℝ in atTop,
    ∃ a b : ℕ, a ≠ b ∧
    ↑a ∈ Set.Icc x (x + log x ^ C) ∧
    ↑b ∈ Set.Icc x (x + log x ^ C) ∧
    τ a = τ b

abbrev Target : Prop :=
    Erdos945Prop

end Problem
