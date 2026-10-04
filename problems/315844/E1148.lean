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

- problem_id: E1148
- collection: erdos
- question_id: erdos:1148
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1148.lean#erdos_1148
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Can every large integer $n$ be written as $n=x^2+y^2-z^2$ with $\max(x^2,y^2,z^2)\leq n$? This was proved affirmatively by Chojecki [Ch26], using a Duke-type equidistribution theorem. A Lean formalisation of the reduction (conditional on a Duke-type equidistribution theorem) exists; see the [forum discussion](https://www.erdosproblems.com/forum/thread/1148#post-4849). The linked formal proof (plby/lean-proofs) removes the Duke hypothesis; it is stated over `ℤ`, as `∃ N, ∀ n ≥ N, ∃ x y z : ℤ, n = x ^ 2 + y ^ 2 - z ^ 2 ∧ max (x ^ 2) (max (y ^ 2) (z ^ 2)) ≤ n`, which gives the statement below by taking absolute values.
- notes: Erdos Problem 1148 -- https://www.erdosproblems.com/1148
- track: solved
- answer_shape: decide
- source_stem: 1148
- mathdb_ref: erdos:1148
- source_namespace: Erdos1148
- source_theorem: erdos_1148
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter

namespace Problem

/--
A natural number $n$ which can be written as $n$ if $n = x^2 + y^2 - z^2$ with $\max(x^2, y^2, z^2)
\leq n$.
-/
def Erdos1148Prop (n : ℕ) : Prop :=
  ∃ x y z : ℕ, n = x ^ 2 + y ^ 2 - z ^ 2 ∧ x ^ 2 ≤ n ∧ y ^ 2 ≤ n ∧ z ^ 2 ≤ n

/--
The largest integer known which cannot be written this way is $6563$.
-/
private instance (n : ℕ) : Decidable (Erdos1148Prop n) :=
  decidable_of_iff
    (∃ x ∈ Finset.range (Nat.sqrt n + 1), ∃ y ∈ Finset.range (Nat.sqrt n + 1),
      ∃ z ∈ Finset.range (Nat.sqrt n + 1),
      n = x ^ 2 + y ^ 2 - z ^ 2 ∧ x ^ 2 ≤ n ∧ y ^ 2 ≤ n ∧ z ^ 2 ≤ n)
    (by
      constructor
      · rintro ⟨x, -, y, -, z, -, h⟩; exact ⟨x, y, z, h⟩
      · rintro ⟨x, y, z, h1, h2, h3, h4⟩
        refine ⟨x, Finset.mem_range.mpr ?_, y, Finset.mem_range.mpr ?_,
                z, Finset.mem_range.mpr ?_, h1, h2, h3, h4⟩
        all_goals (simp only [Nat.lt_succ_iff]; exact Nat.le_sqrt'.mpr ‹_›))

/--
The weaker property: $n = x^2 + y^2 - z^2$ such that $\max(x^2, y^2, z^2) \leq n + 2\sqrt{n}$.
-/
def erdos_1148_weaker_prop (n : ℕ) : Prop :=
  ∃ x y z : ℕ, n = x ^ 2 + y ^ 2 - z ^ 2 ∧
    (x ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n ∧
    (y ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n ∧
    (z ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ᶠ n in atTop, Erdos1148Prop n

end Problem
