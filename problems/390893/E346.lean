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

- problem_id: E346
- collection: erdos
- question_id: erdos:346
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/346.lean#erdos_346
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that for every lacunary, strongly complete sequence `A` that is not complete whenever infinitely many terms are removed from it, `lim A (n + 1) / A n = (1 + √5) / 2`? The answer is no. A counterexample recorded at [erdosproblems.com/346] has all successive ratios at least `6 / 5`, but has subsequences of successive ratios tending to two different limits, `(1 + √5) / 2` and `(1 + √5) / 2 + 1 / 4`.
- notes: Erdos Problem 346 -- https://www.erdosproblems.com/346
- track: solved
- answer_shape: decide
- source_stem: 346
- mathdb_ref: erdos:346
- source_namespace: Erdos346
- source_theorem: erdos_346
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter Topology Set

namespace Problem

/-- We define a sequence `f` by the formula `f n = n.fib - (- 1) ^ n`. -/
def f (n : ℕ) : ℕ := if Even n then n.fib - 1 else n.fib + 1

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ {A : ℕ → ℕ}, IsLacunary A → IsAddStronglyCompleteNatSeq A →
        (∀ B : Set ℕ, B ⊆ range A → B.Infinite → ¬ IsAddComplete (range A \ B)) →
        Tendsto (fun n => A (n + 1) / (A n : ℝ)) atTop (𝓝 ((1 + √5) / 2))

end Problem
