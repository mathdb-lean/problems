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

- problem_id: E180
- collection: erdos
- question_id: erdos:180
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/180.lean#erdos_180
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If $\mathcal{F}$ is a finite set of finite graphs then $\mathrm{ex}(n;\mathcal{F})$ is the maximum number of edges a graph on $n$ vertices can have without containing any subgraphs from $\mathcal{F}$. Note that it is trivial that $\mathrm{ex}(n;\mathcal{F})\leq \mathrm{ex}(n;G)$ for every $G\in\mathcal{F}$. Is it true that, for every $\mathcal{F}$, there exists $G\in\mathcal{F}$ such that $$\mathrm{ex}(n;G)\ll_{\mathcal{F}}\mathrm{ex}(n;\mathcal{F})?$$ This is the Erdős–Simonovits compactness conjecture. The answer is no: OpenAI [OpenAI26] give a family of connected bipartite graphs, none of them acyclic, for which no single member controls the family extremal number. See `erdos_180.variants.counterexample`.
- notes: Erdos Problem 180 -- https://www.erdosproblems.com/180
- track: solved
- answer_shape: decide
- source_stem: 180
- mathdb_ref: erdos:180
- source_namespace: Erdos180
- source_theorem: erdos_180
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter SimpleGraph

namespace Problem

/-- A finite graph, bundled with its vertex count, so that a family may mix orders. -/
structure FiniteGraph where
  order : ℕ
  graph : SimpleGraph (Fin order)

/-- A host graph is `family`-free when it contains no member of `family` as a subgraph. -/
def FamilyFree (family : Finset FiniteGraph) {n : ℕ} (host : SimpleGraph (Fin n)) : Prop :=
  ∀ forbidden ∈ family, forbidden.graph.Free host

open scoped Classical in
/-- $\mathrm{ex}(n;\mathcal{F})$, the greatest number of edges of a graph on `n` vertices
containing no member of `family`. -/
noncomputable def familyExtremal (family : Finset FiniteGraph) (n : ℕ) : ℕ :=
  (Finset.univ.filter (FamilyFree family)).sup
    fun host : SimpleGraph (Fin n) => host.edgeFinset.card

/-- No member of the family is acyclic. -/
def IsCyclicFamily (family : Finset FiniteGraph) : Prop :=
  ∀ forbidden ∈ family, ¬ forbidden.graph.IsAcyclic

/-- The family is *compact*: some single member already controls the family extremal number. -/
def IsCompactFamily (family : Finset FiniteGraph) : Prop :=
  ∃ forbidden ∈ family, ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n : ℕ in atTop,
      (extremalNumber n forbidden.graph : ℝ) ≤ C * (familyExtremal family n : ℝ)

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ family : Finset FiniteGraph,
          family.Nonempty → IsCyclicFamily family → IsCompactFamily family

end Problem
