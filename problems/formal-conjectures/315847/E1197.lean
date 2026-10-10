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

- problem_id: E1197
- collection: erdos
- question_id: erdos:1197
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1197.lean#erdos_1197
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $E\subset (0,\infty)$ be a set of positive measure. Is it true that, for almost all $x>0$, for all sufficiently large (depending on $x$) integers $n$ there exists an integer $r\geq 1$ such that $nx\in r\cdot E$? A problem of Haight, who constructed a set $E\subset (0,\infty)$ of infinite measure such that, for all $x\in E$, $x\not\in r\cdot E$ if $r\geq 2$, and also for all $x>0$, if $n$ is large enough then $nx\not\in E$ (see [1195](https://www.erdosproblems.com/1195)). This is trivially true if $E$ contains an interval $(a,b)$ with $a<b$, since for any $x>0$, for all large $n$, the interval $(\frac{nx}{b},\frac{nx}{a})$ has length $>1$ so contains at least one integer $r\geq 1$. Buczolich and Mauldin [BuMa99] proved that there exists an open set $E\subset (0,\infty)$ and two intervals $I,J\subset [1/2,1)$ such that, for all $x\in I$, $x\in \frac{1}{n}\cdot E$ for infinitely many $n\geq 1$, and for almost all $x\in J$, $x\not\in \frac{1}{n}\cdot E$ for all sufficiently large (depending on $x$) $n$. This was solved in the negative by ebarschkis in the comments, who constructed a counterexample using a variant of the Buczolich-Mauldin construction.
- notes: Erdos Problem 1197 -- https://www.erdosproblems.com/1197
- track: solved
- answer_shape: decide
- source_stem: 1197
- mathdb_ref: erdos:1197
- source_namespace: Erdos1197
- source_theorem: erdos_1197
- source_category: research solved
- source_ams: 11 28
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter MeasureTheory
open scoped Pointwise

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ E : Set ℝ, MeasurableSet E → E ⊆ Set.Ioi 0 → 0 < volume E →
        ∀ᵐ x ∂(volume.restrict (Set.Ioi (0 : ℝ))), ∀ᶠ n : ℕ in atTop,
          ∃ r : ℕ, 1 ≤ r ∧ (n : ℝ) * x ∈ (r : ℝ) • E

end Problem
