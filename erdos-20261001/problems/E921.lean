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

- problem_id: E921
- collection: erdos
- question_id: erdos:921
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/921.lean#erdos_921
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $k\geq 4$ and let $f_k(n)$ be the largest $m$ such that there is a graph on $n$ vertices with chromatic number $k$ in which every odd cycle has length $> m$. Then $$f_k(n) \asymp n^{\frac{1}{k-2}}.$$ A question of Erdős and Gallai. Proved for all $k\geq 4$ by Kierstead, Szemerédi, and Trotter [KST84]. The linked formal proof (Codex and GPT-5.6 Sol) states this as `f k n = Θ(n ^ (1 / (k - 2)))`, where `f k n` is the largest `m` such that some graph on `n` vertices with chromatic number `k` has no odd cycle of length at most `m`; the two eventual statements below are the two halves of this estimate.
- notes: Erdos Problem 921 -- https://www.erdosproblems.com/921
- track: solved
- answer_shape: decide
- source_stem: 921
- mathdb_ref: erdos:921
- source_namespace: Erdos921
- source_theorem: erdos_921
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ (k : ℕ), 4 ≤ k →
          ∃ (c₁ c₂ : ℝ), 0 < c₁ ∧ 0 < c₂ ∧
            (∀ᶠ (n : ℕ) in atTop,
              (∃ (G : SimpleGraph (Fin n)),
                G.chromaticNumber = (k : ℕ∞) ∧
                ∀ l ∈ G.oddCycleLengths, c₁ * (n : ℝ) ^ (1 / ((k : ℝ) - 2)) < (l : ℝ))) ∧
            (∀ᶠ (n : ℕ) in atTop,
              ∀ (G : SimpleGraph (Fin n)),
                G.chromaticNumber = (k : ℕ∞) →
                ∃ l ∈ G.oddCycleLengths, (l : ℝ) ≤ c₂ * (n : ℝ) ^ (1 / ((k : ℝ) - 2)))

end Problem
