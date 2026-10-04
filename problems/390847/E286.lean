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

- problem_id: E286
- collection: erdos
- question_id: erdos:286
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/286.lean#erdos_286
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $k\geq 2$. Is it true that there exists an interval $I$ of width $(e-1+o(1))k$ and integers $n_1<\cdots<n_k\in I$ such that $$1=\frac{1}{n_1}+\cdots+\frac{1}{n_k}?$$ The answer is yes, proved by Croot [Cr01].
- notes: Erdos Problem 286 -- https://www.erdosproblems.com/286
- track: solved
- answer_shape: decide
- source_stem: 286
- mathdb_ref: erdos:286
- source_namespace: Erdos286
- source_theorem: erdos_286
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter Real

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∃ o : ℕ → ℝ, Tendsto o atTop (nhds 0) ∧
        ∀ᶠ k : ℕ in atTop, ∃ a b : ℝ, b - a = (exp 1 - 1 + o k) * k ∧
          ∃ S : Finset ℕ, S.card = k ∧ 0 ∉ S ∧ ∑ n ∈ S, (1 : ℝ) / n = 1 ∧
            ∀ n ∈ S, (n : ℝ) ∈ Set.Icc a b

end Problem
