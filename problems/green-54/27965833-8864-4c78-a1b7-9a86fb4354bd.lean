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

- problem_id: G54
- collection: green
- question_id: green:54
- source: formal-conjectures
- source_locator: FormalConjectures/GreensOpenProblems/54.lean#green_54
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $K \subset \mathbb{R}^{\mathbb{N}}$ be a balanced compact set (that is, $\lambda K \subseteq K$ whenever $|\lambda| \leq 1$) and suppose that the normalised Gaussian measure $\gamma_\infty(K) \geq 0.99$. Does the sumset $10K = K + \cdots + K$ ($10$ times) contain a compact convex set $C$ with $\gamma_\infty(C) \geq 0.01$? The answer is yes: Hua, Song and Tudose proved that if $\gamma_n(A) > 5/6$ then $3(A + A + A)$ contains a symmetric convex body $C$ with $\gamma_n(C) \geq 1/4$, uniformly in $n$.
- notes: Green, open problem 54
- track: solved
- answer_shape: decide
- source_stem: 54
- source_namespace: Green54
- source_theorem: green_54
- source_category: research solved
- source_ams: 46 52 60
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open MeasureTheory ProbabilityTheory
open scoped Pointwise ENNReal

namespace Problem

/-- The infinite-dimensional Gaussian measure γ∞ on ℝ^ℕ,
defined as the countable product of standard Gaussian measures. -/
noncomputable def gaussianMeasureInf : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ K : Set (ℕ → ℝ), IsCompact K → Balanced ℝ K → (0.99 : ℝ≥0∞) ≤
    gaussianMeasureInf K → ∃ C : Set (ℕ → ℝ), IsCompact C ∧ Convex ℝ C ∧ C ⊆ (10 : ℕ) • K ∧
    (0.01 : ℝ≥0∞) ≤ gaussianMeasureInf C

end Problem
