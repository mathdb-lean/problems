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

- problem_id: E994
- collection: erdos
- question_id: erdos:994
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/994.lean#erdos_994
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $E\subseteq (0,1)$ be a meaurable subset with Lebesgue measure $\lambda(E)$. Is it true that, for almost all $\alpha$, $$\lim_{n\to \infty}\frac{1}{n}\sum_{1\leq k\leq n}1_{\{k\alpha \}\in E}=\lambda(E)$$ for all $E$? This is a conjecture of Khintchine [Kh23] (with the exceptional null set of $\alpha$ allowed to depend on $E$). It is false, and was disproved by Marstrand [Ma70].
- notes: Erdos Problem 994 -- https://www.erdosproblems.com/994
- track: solved
- answer_shape: decide
- source_stem: 994
- mathdb_ref: erdos:994
- source_namespace: Erdos994
- source_theorem: erdos_994
- source_category: research solved
- source_ams: 11 28
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter MeasureTheory Set

namespace Problem

open scoped Classical in
/-- The proportion $\frac{1}{n}\sum_{1\leq k\leq n}1_{\{k\alpha \}\in E}$ of the fractional parts
$\{k\alpha\}$, $1\leq k\leq n$, which lie in `E`. -/
noncomputable def visitAverage (E : Set ℝ) (α : ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 n, if Int.fract (k * α) ∈ E then (1 : ℝ) else 0) / n

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ E ⊆ Ioo (0 : ℝ) 1, MeasurableSet E →
          ∀ᵐ α : ℝ, Tendsto (visitAverage E α) atTop (nhds (volume E).toReal)

end Problem
