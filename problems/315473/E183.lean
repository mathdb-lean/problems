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

- problem_id: E183
- collection: erdos
- question_id: erdos:183
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/183.lean#erdos_183
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $R(3;k)$ be the minimal $n$ such that if the edges of $K_n$ are coloured with $k$ colours then there must exist a monochromatic triangle. Determine $$\lim_{k\to \infty}R(3;k)^{1/k}.$$ There is no finite limit: $R(3;k)^{1/k}\to\infty$. This was established by OpenAI [OpenAI26] along with the explicit superexponential lower bound in `erdos_183.variants.explicit_lower_bound`.
- notes: Erdos Problem 183 -- https://www.erdosproblems.com/183
- track: solved
- answer_shape: proof
- source_stem: 183
- mathdb_ref: erdos:183
- source_namespace: Erdos183
- source_theorem: erdos_183
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter

open scoped Topology

namespace Problem

/-- `n` forces a monochromatic triangle on `k` colours when every `k`-colouring of the edges
of `K_n` has a colour class containing a triangle. -/
def ForcesMonochromaticTriangle (n k : ℕ) : Prop :=
  ∀ C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k), ¬ C.CliqueFree 3

/-- $R(3;k)$, the minimal `n` such that every `k`-colouring of the edges of `K_n` contains a
monochromatic triangle. -/
noncomputable def multicolourTriangleRamsey (k : ℕ) : ℕ :=
  sInf {n : ℕ | ForcesMonochromaticTriangle n k}

abbrev Target : Prop :=
    Tendsto (fun k : ℕ => (multicolourTriangleRamsey k : ℝ) ^ ((1 : ℝ) / (k : ℝ)))
      atTop atTop

end Problem
