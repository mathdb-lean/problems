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

- problem_id: E363
- collection: erdos
- question_id: erdos:363
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/363.lean#erdos_363
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that, for each fixed $n$ and fixed sizes $k_1,\ldots,k_n \geq 4$, there are only finitely many collections of disjoint intervals $I_1,\ldots,I_n$ of size $\lvert I_i\rvert = k_i$ for $1\leq i\leq n$ such that$$\prod_{1\leq i\leq n}\prod_{m\in I_i}m$$is a square? The number of intervals and their sizes are fixed: the list `ks` of sizes determines both. Without this restriction finiteness fails, by a result of Skałba (see [Ul05]). This is false: Ulas [Ul05] constructed infinitely many such collections with $n = 4$ and $k_1 = \cdots = k_4 = 4$.
- notes: Erdos Problem 363 -- https://www.erdosproblems.com/363
- track: solved
- answer_shape: decide
- source_stem: 363
- mathdb_ref: erdos:363
- source_namespace: Erdos363
- source_theorem: erdos_363
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

open Finset

/-- A finite set of naturals is an interval of naturals. -/
def IsInterval (I : Finset ℕ) : Prop :=
  ∃ a b : ℕ, I = Icc a b

/-- A collection of intervals as in Erdős Problem 363: disjoint intervals of positive integers,
each of size at least `4`, whose product is a square. Intervals containing `0` are excluded, since
their product is `0`, which is a square. -/
def IsValidCollection (S : List (Finset ℕ)) : Prop :=
  (∀ I ∈ S, IsInterval I) ∧
  (∀ I ∈ S, 4 ≤ I.card) ∧
  (∀ I ∈ S, 0 ∉ I) ∧
  S.Pairwise Disjoint ∧
  IsSquare ((S.map (fun I => ∏ m ∈ I, m)).prod)

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ ks : List ℕ,
        {S : List (Finset ℕ) | IsValidCollection S ∧ S.map Finset.card = ks}.Finite

end Problem
