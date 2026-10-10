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

import MathDBUtil

/-!
Converted from another corpus. `source` names it, `source_version`
pins the revision, and `source_locator` points at the one
declaration this came from. Every `source_` field describes that
declaration as it stands there, not as it stands here.

Read `track` for whether the problem is solved, which is a fact
about mathematics. `source_has_lean_proof` is a different claim --
whether that corpus holds a machine-checked proof -- and is false
for almost every problem, because it is a statement repository.

- problem_id: E967
- collection: erdos
- question_id: erdos:967
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/967.lean#erdos_967
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $1<a_1<\cdots$ be a sequence of integers such that $\sum\frac{1}{a_i}<\infty$. Is it true that, for every $t\in \mathbb{R}$, $$1+\sum_{k}\frac{1}{a_k^{1+it}}\neq 0?$$ Yip [Yi25] has proved that this is not always true - in fact, for any real $t\neq 0$, there exists a sequence of integers $1<a_1<\cdots$ such that $\sum \frac{1}{a_i}<\infty$ and $1+\sum_{k}\frac{1}{a_k^{1+it}}=0$. This was formalized in Lean by Wu using Aristotle.
- notes: Erdos Problem 967 -- https://www.erdosproblems.com/967
- track: solved
- answer_shape: decide
- source_stem: 967
- mathdb_ref: erdos:967
- source_namespace: Erdos967
- source_theorem: erdos_967
- source_category: research solved
- source_ams: 11 30
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter

open scoped Topology

namespace Problem

/-- The summand $\frac{1}{n^{1+it}}$, for a natural number $n$ and $t\in\mathbb{R}$. -/
noncomputable def summand (t : ℝ) (n : ℕ) : ℂ := 1 / (n : ℂ) ^ (1 + t * Complex.I : ℂ)

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ a : ℕ → ℕ, StrictMono a → 1 < a 0 → Summable (fun k : ℕ => 1 / (a k : ℝ)) →
          ∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0

end Problem
