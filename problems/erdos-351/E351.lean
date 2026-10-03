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

- problem_id: E351
- collection: erdos
- question_id: erdos:351
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/351.lean#erdos_351
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $p(x) \in \mathbb{Q}[x]$ be a non-constant rational polynomial with positive leading coefficient. Is it true that $$A=\{ p(n)+1/n : n \in \mathbb{N}\}$$ is strongly complete, in the sense that, for any finite set $B$, $$\left\{\sum_{a \in X} a : X \subseteq A \setminus B, X \textrm{ is finite}\right\}$$ contains all sufficiently large integers?
- notes: Erdos Problem 351 -- https://www.erdosproblems.com/351
- track: solved
- answer_shape: decide
- source_stem: 351
- mathdb_ref: erdos:351
- source_namespace: Erdos351
- source_theorem: erdos_351
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Polynomial

namespace Problem

/-- The set of rational numbers of the form `P(n) + 1 / n` where `n` is a natural number
and `P` is a polynomial with rational coefficients.

Note: We include `P 0` in there (since `1 / 0 = 0`), but this doesn't change the validity of the
conjecture -/
def imageSet {α : Type*} [Semifield α] (P : α[X]) : Set α :=
  Set.range (fun (n : ℕ) ↦ P.eval ↑n + 1 / n)

/-- The predicate that a set `A` is strongly complete, i.e. that for every finite set `B`, every sufficiently
large integer is a sum of elements of the set `A \ B`. -/
def IsStronglyComplete {α : Type*} [Semiring α] (A : Set α) : Prop :=
  ∀ B : Finset α,
    ∀ᶠ (m : ℕ) in Filter.atTop,
      ↑m ∈ { ∑ n ∈ X, n | (X : Finset α) (_ : ↑X ⊆ A \ B) }

/-- The predicate that the rational polynomial `P` has a complete image. -/
def HasCompleteImage (P : ℚ[X]) : Prop := IsStronglyComplete (imageSet P)

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ P : ℚ[X], 0 < P.natDegree → 0 < P.leadingCoeff → HasCompleteImage P

end Problem
