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

- problem_id: E119_parts_iii
- collection: erdos
- question_id: erdos:119
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/119.lean#erdos_119.parts.iii
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that there exists $c > 0$ such that, for all large $n$, $\sum_{k \leq n} M_k > n^{1 + c}$? The \$100 prize was offered for the third question in [Er97f]. This was resolved by GPT 5.6 and Korsky (see the proof claims), who proved that $\sum_{k\leq n}M_k \gg \frac{n^{5/4}}{\sqrt{\log n}}$ (and hence for infinitely many $n$ we have $M_n> n^{1/4-o(1)}$).
- notes: Erdos Problem 119 -- https://www.erdosproblems.com/119
- track: solved
- answer_shape: decide
- source_stem: 119
- mathdb_ref: erdos:119
- source_namespace: Erdos119
- source_theorem: erdos_119.parts.iii
- source_category: research solved
- source_ams: 30
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter Finset Set

namespace Problem

/-
Here we use 0-indexing for generality and convenience, while in the original problem
formulation 1-indexing was used. This change does not affect the meaning of the problem.
In the description of the problem below we remain faithful to the original one.
-/

/-- Let $z_i$ be an infinite sequence of complex numbers such that $|z_i| = 1$ for all $i \geq 1$.
For $n \geq 1$ let $p_n(z) = \prod_{i \leq n} (z - z_i)$. -/
noncomputable def p (z : ℕ → ℂ) (n : ℕ) : ℂ → ℂ :=
    fun w => ∏ i ∈ range n, (w - z i)

/-- Let $M_n = \max_{|z| = 1} |p_n(z)|$. -/
noncomputable def M (z : ℕ → ℂ) (n : ℕ) : ℝ :=
    sSup { (‖p z n w‖) | (w : ℂ) (_ : ‖w‖ = 1) }

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ (z : ℕ → ℂ) (hz : ∀ i : ℕ, ‖z i‖ = 1),
      ∃ (c : ℝ) (hc : c > 0), ∀ᶠ n in atTop,
        ∑ k ∈ range n, M z k > n ^ (1 + c)

end Problem
