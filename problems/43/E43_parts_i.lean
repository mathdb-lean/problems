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

- problem_id: E43_parts_i
- collection: erdos
- question_id: erdos:43
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/43.lean#erdos_43.parts.i
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If $A$ and $B$ are Sidon sets in $\{1,\ldots,N\}$ with $(A-A)\cap(B-B)=\{0\}$, is it true that $$\binom{\lvert A\rvert}{2}+\binom{\lvert B\rvert}{2}\leq\binom{f(N)}{2}+O(1)?$$ The answer is no; the Erdős Problems page notes that this follows from the solution to Erdős Problem 42.
- notes: Erdos Problem 43 -- https://www.erdosproblems.com/43
- track: solved
- answer_shape: decide
- source_stem: 43
- mathdb_ref: erdos:43
- source_namespace: Erdos43
- source_theorem: erdos_43.parts.i
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open scoped Pointwise

namespace Problem

/--
Let $f(N)$ be the maximum possible size of a Sidon set in $\{1,\ldots,N\}$.
-/
noncomputable abbrev f (N : ℕ) : ℕ := Finset.maxSidonSubsetCard (Finset.Icc 1 N)

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ C : ℝ, ∀ᶠ N in Filter.atTop, ∀ (A B : Finset ℕ),
          A ⊆ Finset.Icc 1 N →
          B ⊆ Finset.Icc 1 N →
          IsSidon (A : Set ℕ) →
          IsSidon (B : Set ℕ) →
          (A - A) ∩ (B - B) = {0} →
          ((A.card.choose 2 + B.card.choose 2 : ℕ) : ℝ) ≤ ((f N).choose 2 : ℝ) + C

end Problem
