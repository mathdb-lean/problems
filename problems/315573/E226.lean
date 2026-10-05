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

- problem_id: E226
- collection: erdos
- question_id: erdos:226
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/226.lean#erdos_226
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is there an entire non-linear function $f$ such that, for all $x\in\mathbb{R}$, $x$ is rational if and only if $f(x)$ is? Barth and Schneider [BaSc70] proved the stronger result for countable dense subsets of $\mathbb{R}$.
- notes: Erdos Problem 226 -- https://www.erdosproblems.com/226
- track: solved
- answer_shape: decide
- source_stem: 226
- mathdb_ref: erdos:226
- source_namespace: Erdos226
- source_theorem: erdos_226
- source_category: research solved
- source_ams: 30
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

/-- A real function preserves rationality. -/
def PreservesRationality (f : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, x ∈ Set.range ((↑) : ℚ → ℝ) ↔ f x ∈ Set.range ((↑) : ℚ → ℝ)

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ (∀ x : ℝ, (F x).im = 0) ∧
          (∀ g : AffineMap ℝ ℝ ℝ, (fun x : ℝ => (F x).re) ≠ g) ∧
          PreservesRationality (fun x : ℝ => (F x).re)

end Problem
