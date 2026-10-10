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

- problem_id: E225
- collection: erdos
- question_id: erdos:225
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/225.lean#erdos_225
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $$ f(\theta) = \sum_{0\leq k\leq n}c_k e^{ik\theta}$$ be a trigonometric polynomial all of whose roots are real, such that $\max_{\theta\in [0,2\pi]}\lvert f(\theta)\rvert=1$. Then $$\int_0^{2\pi}\lvert f(\theta)\rvert \mathrm{d}\theta \leq 4.$$ This is Problem 4.20 in [Ha74], where it is attributed to Erdős. This was solved independently by Kristiansen [Kr74] (only in the case when $c_k\in\mathbb{R}$) and Saff and Sheil-Small [SaSh74] (for general $c_k\in \mathbb{C}$). (The original proof of Kristiansen contained an error which was later fixed in [Kr76].) "All roots real" refers to the zeros of $f$ as an entire function of $\theta\in\mathbb{C}$. We normalise by $c_0c_n\neq 0$ and $n\geq 1$: a factor $e^{im\theta}$ affects neither the zeros nor $\lvert f\rvert$ on the real line, while a single term $c_me^{im\theta}$ has no zeros and $\int_0^{2\pi}\lvert f\rvert = 2\pi$.
- notes: Erdos Problem 225 -- https://www.erdosproblems.com/225
- track: solved
- answer_shape: decide
- source_stem: 225
- mathdb_ref: erdos:225
- source_namespace: Erdos225
- source_theorem: erdos_225
- source_category: research solved
- source_ams: 30 42
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Set

namespace Problem

/-- The trigonometric polynomial $f(z) = \sum_{0\leq k\leq n}c_k e^{ikz}$, as an entire function
of $z\in\mathbb{C}$. -/
noncomputable def trigPoly (n : ℕ) (c : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), c k * Complex.exp (Complex.I * (k * z))

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ (n : ℕ) (c : ℕ → ℂ), 0 < n → c 0 ≠ 0 → c n ≠ 0 →
        (∀ z : ℂ, trigPoly n c z = 0 → z.im = 0) →
        (∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi), ‖trigPoly n c θ‖ ≤ 1) →
        (∃ θ ∈ Icc (0 : ℝ) (2 * Real.pi), ‖trigPoly n c θ‖ = 1) →
        ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖trigPoly n c θ‖ ≤ 4

end Problem
