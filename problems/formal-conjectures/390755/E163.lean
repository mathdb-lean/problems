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

- problem_id: E163
- collection: erdos
- question_id: erdos:163
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/163.lean#erdos_163
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: The Burr-Erdős conjecture: For any $d\geq 1$ if $H$ is a graph such that every subgraph contains a vertex of degree at most $d$ then $$R(H)\ll_d n.$$ Solved by Lee [Le17], who proved that $R(H) \leq 2^{2^{O(d)}}n$. This problem is #9 in Ramsey Theory in the graphs problem collection. The linked formal proof (Codex and GPT-5.6 Sol) gives, for graphs `H` on `Fin n`, a natural constant `C ≥ 1` with `RamseyFor H (C * n)` (every red/blue colouring of `K_{C n}` contains a monochromatic copy of `H`); transporting along `Fintype.equivFin` gives the statement below.
- notes: Erdos Problem 163 -- https://www.erdosproblems.com/163
- track: solved
- answer_shape: decide
- source_stem: 163
- mathdb_ref: erdos:163
- source_namespace: Erdos163
- source_theorem: erdos_163
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ (d : ℕ), 1 ≤ d →
          ∃ C > (0 : ℝ), ∀ (V : Type) [Fintype V] (H : SimpleGraph V),
            H.IsDegenerate d →
            (SimpleGraph.diagonalGraphRamsey H : ℝ) ≤ C * Fintype.card V

end Problem
