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

- problem_id: G36_prove
- collection: green
- question_id: green:36
- source: formal-conjectures
- source_locator: FormalConjectures/GreensOpenProblems/36.lean#green_36
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Do the following exist, for arbitrarily large $n$? An abelian group $H$ with $|H| = n^{2+o(1)}$, together with subsets $A_1, ..., A_n, B_1, ..., B_n$ satisfying $|A_i||B_i| \ge n^{2-o(1)}$ and $|A_i + B_i| = |A_i||B_i|$, such that the sets $A_i + B_i$ are disjoint from the sets $A_j + B_k$ ($j \neq k$)? NOTE: according to [CKS05, 4.1], the conditions should be $A_i + B_j$ disjoint from $A_j + B_k$ for $i \neq k$. See `green_36.variants.cks05`.
- notes: Green, open problem 36
- track: open
- answer_shape: prove
- pair_id: G36
- pair_role: prove
- source_stem: 36
- source_namespace: Green36
- source_theorem: green_36
- source_category: research open
- source_ams: 5 20
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter
open scoped Pointwise

namespace Problem

/-- The simultaneous double product property [CKS05, 4.1]. -/
def SimultaneousDoubleProduct {ι H : Type*} [AddCommGroup H]
    (A B : ι → Finset H) : Prop :=
  open scoped Classical in
  (∀ i, (A i + B i).card = (A i).card * (B i).card) ∧
  (∀ i j k, i ≠ k → Disjoint (A i + B j) (A j + B k))

/-- A variant of the simultaneous double product property, as stated in [Gr24, Problem 36]. -/
def Green36Property {ι H : Type*} [AddCommGroup H]
    (A B : ι → Finset H) : Prop :=
  open scoped Classical in
  (∀ i, (A i + B i).card = (A i).card * (B i).card) ∧
  (∀ i j k, j ≠ k → Disjoint (A i + B i) (A j + B k))

abbrev Target : Prop :=
    ∀ ε > (0 : ℝ), ∃ᶠ n in atTop,
        ∃ (H : Type) (_ : AddCommGroup H) (_ : Finite H) (A B : Fin n → Finset H),
          (n : ℝ) ^ (2 - ε) ≤ Nat.card H ∧ Nat.card H ≤ (n : ℝ) ^ (2 + ε) ∧
          (∀ i, (n : ℝ) ^ (2 - ε) ≤ (A i).card * (B i).card) ∧
          Green36Property A B

end Problem
