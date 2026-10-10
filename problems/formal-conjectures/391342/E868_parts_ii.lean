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

- problem_id: E868_parts_ii
- collection: erdos
- question_id: erdos:868
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/868.lean#erdos_868.parts.ii
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A$ be an additive basis of order $2$, let $f(n)$ denote the number of ways in which $n$ can be written as the sum of two elements from $A$. If $f(n) > \epsilon \log n$ for large $n$ and an arbitrary fixed $\epsilon > 0$, then must $A$ contain a minimal additive basis of order $2$? Larsen and Larsen [LaLa26] constructed a counterexample with $f(n) > c \log n$ for all large $n$.
- notes: Erdos Problem 868 -- https://www.erdosproblems.com/868
- track: solved
- answer_shape: decide
- source_stem: 868
- mathdb_ref: erdos:868
- source_namespace: Erdos868
- source_theorem: erdos_868.parts.ii
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter

open scoped Pointwise

namespace Problem

/-- The number of ways in which a natural `n` can be written as the sum of
`o` members of the set `A`. Representations are counted as nondecreasing tuples, so that
two representations differing only in the order of their summands are counted once. -/
noncomputable
def ncard_add_repr (A : Set ℕ) (o : ℕ) (n : ℕ) : ℕ :=
  { a : Fin o → ℕ | Monotone a ∧ Set.range a ⊆ A ∧ ∑ i, a i = n }.ncard

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ᵉ (A : Set ℕ) (ε > 0), A.IsAsymptoticAddBasisOfOrder 2 →
      (∀ᶠ (n : ℕ) in atTop, ε * Real.log n < ncard_add_repr A 2 n) → ∃ B ⊆ A,
      B.IsAsymptoticAddBasisOfOrder 2 ∧ ∀ b ∈ B, ¬(B \ {b}).IsAsymptoticAddBasisOfOrder 2

end Problem
