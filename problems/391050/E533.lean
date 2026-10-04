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

- problem_id: E533
- collection: erdos
- question_id: erdos:533
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/533.lean#erdos_533
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $\delta > 0$. If $n$ is sufficiently large and $G$ is a graph on $n$ vertices with no $K_5$ and at least $\delta n^2$ edges, must $G$ contain a set of $\gg_\delta n$ vertices spanning no triangle? Equivalently, writing $\mathrm{RT}_3(n, K_5, m)$ for the maximum number of edges of a $K_5$-free graph on $n$ vertices in which every triangle-free vertex set has fewer than $m$ vertices (the *triangle Ramsey–Turán number*), is $$\delta_3(5) = \lim_{\epsilon \to 0} \lim_{n \to \infty} \frac{\mathrm{RT}_3(n, K_5, \epsilon n)}{n^2} = 0?$$ This is a problem of Erdős, Hajnal, Simonovits, Sós, and Szemerédi [EHSSS94], who proved $\delta_3(5) \leq 1/12$ and the analogous $\delta_3(4) = 0$, and observed $\delta_3(7) \geq 1/4$ via a construction of Erdős and Rogers [ErRo62]. The answer is **no**: Balogh and Lenz [BaLe13] disproved it by showing $\delta_3(5) > 0$, and the exact value $\delta_3(5) = 1/12$ was determined by the matching lower-bound construction of Liu, Reiher, Sharifzadeh, and Staden [LRSS21] (see `erdos_533.variants.lrss_lower`).
- notes: Erdos Problem 533 -- https://www.erdosproblems.com/533
- track: solved
- answer_shape: decide
- source_stem: 533
- mathdb_ref: erdos:533
- source_namespace: Erdos533
- source_theorem: erdos_533
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter SimpleGraph

namespace Problem

open scoped Classical in
abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
          ∀ G : SimpleGraph (Fin n), G.CliqueFree 5 →
            δ * (n : ℝ) ^ 2 ≤ G.edgeFinset.card →
              ∃ S : Finset (Fin n), c * n ≤ (S.card : ℝ) ∧
                G.CliqueFreeOn (S : Set (Fin n)) 3

end Problem
