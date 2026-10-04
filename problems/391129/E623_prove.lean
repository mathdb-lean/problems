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

- problem_id: E623_prove
- collection: erdos
- question_id: erdos:623
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/623.lean#erdos_623
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $X$ be a set of cardinality $\aleph_\omega$ and $f$ be a function from the finite subsets of $X$ to $X$ such that $f(A)\not\in A$ for all $A$. Must there exist an infinite $Y\subseteq X$ that is independent - that is, for all finite $B\subset Y$ we have $f(B)\not\in Y$?
- notes: Erdos Problem 623 -- https://www.erdosproblems.com/623
- track: open
- answer_shape: prove
- pair_id: E623
- pair_role: prove
- source_stem: 623
- mathdb_ref: erdos:623
- source_namespace: Erdos623
- source_theorem: erdos_623
- source_category: research open
- source_ams: 3
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Real Set
open scoped Cardinal Ordinal

namespace Problem

universe u

abbrev Target : Prop :=
    ∀ (X : Type u) (hX : #X = ℵ_ ω)
        (f : Finset X → X), (∀ A : Finset X, f A ∉ A) →
        (∃ Y : Set X, Set.Infinite Y ∧ (∀ (B : Finset X), ↑B ⊆ Y → f B ∉ Y))

end Problem
