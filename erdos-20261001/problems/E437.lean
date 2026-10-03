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

- problem_id: E437
- collection: erdos
- question_id: erdos:437
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/437.lean#erdos_437
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $1\leq a_1<\cdots<a_k\leq x$. How many of the partial products $a_1,a_1a_2,\ldots,a_1\cdots a_k$ can be squares? Is it true that, for any $\epsilon>0$, there can be more than $x^{1-\epsilon}$ squares? The answer is yes, which follows from work of Bui, Pratt, and Zaharescu [BPZ24], as noted by Tao [Ta24].
- notes: Erdos Problem 437 -- https://www.erdosproblems.com/437
- track: solved
- answer_shape: decide
- source_stem: 437
- mathdb_ref: erdos:437
- source_namespace: Erdos437
- source_theorem: erdos_437
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter Real

namespace Problem

/-- The number of partial products $a_1, a_1a_2, \ldots, a_1\cdots a_k$ of a finite sequence
`a = [a₁, …, a_k]` which are squares. -/
def squarePartialProducts (a : List ℕ) : ℕ :=
  ((Finset.range a.length).filter fun i ↦ IsSquare (a.take (i + 1)).prod).card

/-- `L x` is the maximal number of square partial products of a sequence
$1\leq a_1<\cdots<a_k\leq x$. -/
noncomputable def L (x : ℕ) : ℕ :=
  sSup {m | ∃ a : List ℕ, a.Pairwise (· < ·) ∧ (∀ n ∈ a, n ∈ Finset.Icc 1 x) ∧
    squarePartialProducts a = m}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ (1 - ε) < L x

end Problem
