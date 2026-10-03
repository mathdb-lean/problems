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

- problem_id: E146
- collection: erdos
- question_id: erdos:146
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/146.lean#erdos_146
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If $H$ is bipartite and is $r$-degenerate, that is, every induced subgraph of $H$ has minimum degree $\leq r$, then $$\mathrm{ex}(n;H) \ll n^{2-1/r}.$$ The answer is no. OpenAI [OpenAI26] give a connected bipartite `2`-degenerate `H` and constants `c, ε > 0` with $\mathrm{ex}(n;H)\geq cn^{3/2+\epsilon}$ for all large `n`, which exceeds the conjectured $n^{2-1/2}=n^{3/2}$. See `erdos_146.variants.two_degenerate_counterexample`.
- notes: Erdos Problem 146 -- https://www.erdosproblems.com/146
- track: solved
- answer_shape: decide
- source_stem: 146
- mathdb_ref: erdos:146
- source_namespace: Erdos146
- source_theorem: erdos_146
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter SimpleGraph

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ (r q : ℕ) (H : SimpleGraph (Fin q)),
          0 < r → H.IsBipartite → H.IsDegenerate r →
            Asymptotics.IsBigO atTop
              (fun n : ℕ => (extremalNumber n H : ℝ))
              (fun n : ℕ => (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ)))

end Problem
