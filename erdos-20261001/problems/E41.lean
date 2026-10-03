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

- problem_id: E41
- collection: erdos
- question_id: erdos:41
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/41.lean#erdos_41
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A \subset \mathbb{N}$ be an infinite set such that the triple sums $a+b+c$ are all distinct for $a,b,c \in A$ (aside from the trivial coincidences). Is it true that $$\liminf_{N \to \infty} \frac{\lvert A \cap \{1,\ldots,N\}\rvert}{N^{1/3}}=0?$$
- notes: Erdos Problem 41 -- https://www.erdosproblems.com/41
- track: open
- answer_shape: proof
- source_stem: 41
- mathdb_ref: erdos:41
- source_namespace: Erdos41
- source_theorem: erdos_41
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Set

namespace Problem

variable {α : Type} [AddCommMonoid α]

/--
`NtupleCondition A n` says that the sum of `n` elements of `A` determines the summands,
counted with multiplicity and up to permutation.

Multisets allow a summand to occur more than once, while multiset equality identifies precisely the
trivial coincidences obtained by reordering the summands.
-/
def NtupleCondition (A : Set α) (n : ℕ) : Prop :=
  ∀ I J : Multiset α,
    (∀ i ∈ I, i ∈ A) →
    (∀ j ∈ J, j ∈ A) →
    I.card = n →
    J.card = n →
    I.sum = J.sum →
    I = J

abbrev Target : Prop :=
    ∀ (A : Set ℕ) (h_triple : NtupleCondition A 3) (h_infinite : A.Infinite),
      Filter.atTop.liminf (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)) = 0

end Problem
