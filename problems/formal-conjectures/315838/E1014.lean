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

- problem_id: E1014
- collection: erdos
- question_id: erdos:1014
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1014.lean#erdos_1014
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $R(k,l)$ be the Ramsey number, so the minimal $n$ such that every graph on at least $n$ vertices contains either a $K_k$ or an independent set on $l$ vertices. Prove, for fixed $k\geq 3$, that $$\lim_{l\to \infty}\frac{R(k,l+1)}{R(k,l)}=1.$$ This has been [solved](https://cdn.openai.com/pdf/6dc7175d-d9e7-4b8d-96b8-48fe5798cd5b/Ramsey.pdf) by an internal model at OpenAI.
- notes: Erdos Problem 1014 -- https://www.erdosproblems.com/1014
- track: solved
- answer_shape: proof
- source_stem: 1014
- mathdb_ref: erdos:1014
- source_namespace: Erdos1014
- source_theorem: erdos_1014
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter

open scoped Topology

namespace Problem

local notation "R(" k ", " l ")" => SimpleGraph.classicalRamsey k l

abbrev Target : Prop :=
    ∀ k : ℕ, 3 ≤ k →
        Tendsto (fun l : ℕ ↦ (R(k, l + 1) : ℝ) / (R(k, l) : ℝ)) atTop (𝓝 1)

end Problem
