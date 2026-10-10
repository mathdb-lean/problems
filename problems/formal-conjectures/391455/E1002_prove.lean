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

- problem_id: E1002_prove
- collection: erdos
- question_id: erdos:1002
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1002.lean#erdos_1002
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: For any $0<\alpha<1$, let $f(\alpha,n)=\frac{1}{\log n}\sum_{1\leq k\leq n}(\tfrac{1}{2}- \{ \alpha k\})$. Does $f(\alpha,n)$ have an asymptotic distribution function? In other words, is there a non-decreasing function $g$ such that $g(-\infty)=0$, $g(\infty)=1$, and $\lim_{n\to \infty}\lvert \{ \alpha\in (0,1): f(\alpha,n)\leq c\}\rvert=g(c)$?
- notes: Erdos Problem 1002 -- https://www.erdosproblems.com/1002
- track: open
- answer_shape: prove
- pair_id: E1002
- pair_role: prove
- source_stem: 1002
- mathdb_ref: erdos:1002
- source_namespace: Erdos1002
- source_theorem: erdos_1002
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Real Set Filter Finset MeasureTheory Topology

namespace Problem

abbrev Target : Prop :=
    ∃ g : ℝ → ℝ, Monotone g ∧
      Tendsto g atBot (𝓝 0) ∧
      Tendsto g atTop (𝓝 1) ∧
      letI f :=  fun (α : ℝ) (n : ℕ) ↦
        (1 / log n) * ∑ k ∈ Icc (1 : ℕ) n, (1 / 2 - Int.fract (α * k))
      ∀ c : ℝ, Tendsto (fun (n : ℕ) ↦ (volume { α | α ∈ Ioo (0 : ℝ) 1 ∧ f α n ≤ c }).toReal)
        atTop (𝓝 (g c))

end Problem
