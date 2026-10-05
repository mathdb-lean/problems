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

- problem_id: E1010
- collection: erdos
- question_id: erdos:1010
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1010.lean#erdos_1010
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $t<\lfloor n/2\rfloor$. Does every graph on $n$ vertices with $\lfloor n^2/4\rfloor+t$ edges contain at least $t\lfloor n/2\rfloor$ triangles? Rademacher proved that every graph on $n$ vertices with $\lfloor n^2/4\rfloor+1$ edges contains at least $\lfloor n/2\rfloor$ triangles. Erdős [Er62d] proved that every graph on $n$ vertices with $\lfloor n^2/4\rfloor+t$ edges contains at least $t\lfloor n/2\rfloor$ triangles, for all $t<cn$, for some constant $c>0$. This is true, and was proved independently by Lovász and Simonovits [LoSi76] and Nikiforov and Khadzhiivanov [NiKh81].
- notes: Erdos Problem 1010 -- https://www.erdosproblems.com/1010
- track: solved
- answer_shape: decide
- source_stem: 1010
- mathdb_ref: erdos:1010
- source_namespace: Erdos1010
- source_theorem: erdos_1010
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open SimpleGraph

namespace Problem

open scoped Classical in
abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ n t : ℕ, t < n / 2 → ∀ G : SimpleGraph (Fin n),
        G.edgeFinset.card = n ^ 2 / 4 + t → t * (n / 2) ≤ (G.cliqueFinset 3).card

end Problem
