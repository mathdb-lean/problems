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

- problem_id: G52_prove
- collection: green
- question_id: green:52
- source: formal-conjectures
- source_locator: FormalConjectures/GreensOpenProblems/52.lean#green_52
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Suppose that $A \subset \mathbb{F}_2^n$ is a set with an additive complement of size $K$. Does $2A$ contain a coset of codimension $O_K(1)$?
- notes: Green, open problem 52
- track: open
- answer_shape: prove
- pair_id: G52
- pair_role: prove
- source_stem: 52
- source_namespace: Green52
- source_theorem: green_52
- source_category: research open
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Real
open scoped Pointwise

namespace Problem

abbrev Target : Prop :=
    ∃ (c : ℕ → ℕ), ∀ (n K : ℕ) (A : Set (𝔽₂ n)) (S : Finset (𝔽₂ n)),
      S.card = K → A + (S : Set (𝔽₂ n)) = Set.univ →
      ∃ (V : AffineSubspace (ZMod 2) (𝔽₂ n)), (V : Set (𝔽₂ n)) ⊆ A + A ∧
        n ≤ Module.finrank (ZMod 2) V.direction + c K

end Problem
