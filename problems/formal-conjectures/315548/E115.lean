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

- problem_id: E115
- collection: erdos
- question_id: erdos:115
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/115.lean#erdos_115
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If $p(z)$ is a polynomial of degree $n$ such that $\{z : \lvert p(z)\rvert\leq 1\}$ is connected then is it true that $$\max_{\substack{z\in\mathbb{C}\\ \lvert p(z)\rvert\leq 1}} \lvert p'(z)\rvert \leq (\tfrac{1}{2}+o(1))n^2?$$ Eremenko and Lempert [ErLe94] have shown this is true, and in fact Chebyshev polynomials are the extreme examples.
- notes: Erdos Problem 115 -- https://www.erdosproblems.com/115
- track: solved
- answer_shape: decide
- source_stem: 115
- mathdb_ref: erdos:115
- source_namespace: Erdos115
- source_theorem: erdos_115
- source_category: research solved
- source_ams: 30
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ p : Polynomial ℂ, p.Monic → p.natDegree = n →
          IsConnected {z : ℂ | ‖p.eval z‖ ≤ 1} → ∀ z : ℂ, ‖p.eval z‖ ≤ 1 →
            ‖p.derivative.eval z‖ ≤ (1 / 2 + ε) * (n : ℝ) ^ 2

end Problem
