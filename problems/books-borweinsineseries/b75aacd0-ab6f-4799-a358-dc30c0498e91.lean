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

- problem_id: BBorweinSineSeries_borwein_sine_series
- collection: books
- question_id: books:BorweinSineSeries
- source: formal-conjectures
- source_locator: FormalConjectures/Books/BorweinSineSeries.lean#borwein_sine_series
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Does the series $$ \sum_{n=1}^{\infty} \frac{\left(\frac{2}{3} + \frac{1}{3}\sin n\right)^n}{n} $$ converge? After computing approximately $10^7$ terms, the partial sums approximate $2.163$. See https://arxiv.org/abs/2007.11017 for a proof of the convergence, relying on an irrationality measure for pi. Also see https://github.com/AxiomMath/gdm-formal-conjectures/blob/main/docs/BorweinSineSeries.md for a partial formalization of the conjecture, conditional on such an irrationality measure of pi (cf https://arxiv.org/abs/1912.06345).
- notes: Book problem BorweinSineSeries -- https://mathworld.wolfram.com/HarmonicSeries.html
- track: solved
- answer_shape: decide
- source_stem: BorweinSineSeries
- source_namespace: BorweinSineSeries
- source_theorem: borwein_sine_series
- source_category: research solved
- source_ams: 26 40
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
      Summable fun n : ℕ+ ↦ ((2 / 3 + 1 / 3 * Real.sin (n : ℝ)) ^ (n : ℕ)) / (n : ℝ)

end Problem
