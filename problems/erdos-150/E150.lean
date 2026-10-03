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

- problem_id: E150
- collection: erdos
- question_id: erdos:150
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/150.lean#erdos_150
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: A minimal cut of a graph is a minimal set of vertices whose removal disconnects the graph. Let $c(n)$ be the maximum number of minimal cuts a graph on $n$ vertices can have. Does $c(n)^{1/n}\to \alpha$ for some $\alpha <2$? It is unclear in [Er88] whether Erdős knew that the limit existed, which follows from a simple argument first given in the literature (to the best of my knowledge) by Bradač [Br24]. That $\alpha<2$ was proved by Fomin, Kratsch, Todinca, and Villanger [FKTV08], who proved $\alpha \leq 1.7087$. This was independently studied by Bradač [Br24] (unaware of this earlier work), who proved that $\alpha \leq 2^{H(1/3)}\approx 1.8899$, where $H(\cdot)$ is the binary entropy function. This was formalized in Lean by Monticone using Aristotle.
- notes: Erdos Problem 150 -- https://www.erdosproblems.com/150
- track: solved
- answer_shape: decide
- source_stem: 150
- mathdb_ref: erdos:150
- source_namespace: Erdos150
- source_theorem: erdos_150
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter

open scoped Topology

namespace Problem

/-- A *minimal cut* of a graph `G` is a minimal set `T` of vertices whose removal disconnects
`G`, that is, `G - T` fails to be preconnected while `G - S` is preconnected for every `S ⊂ T`. -/
def IsMinimalCut {V : Type*} (G : SimpleGraph V) (T : Set V) : Prop :=
  ¬ (G.induce Tᶜ).Preconnected ∧ ∀ S ⊂ T, (G.induce Sᶜ).Preconnected

/-- The maximum number $c(n)$ of minimal cuts a graph on $n$ vertices can have. -/
noncomputable def maxMinimalCuts (n : ℕ) : ℕ :=
  sSup {k | ∃ G : SimpleGraph (Fin n), {T : Set (Fin n) | IsMinimalCut G T}.ncard = k}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ α : ℝ, α < 2 ∧
          Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)

end Problem
