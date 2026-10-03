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

- problem_id: E570
- collection: erdos
- question_id: erdos:570
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/570.lean#erdos_570
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $k\geq 3$. Is it true that, if $m$ is sufficiently large, for any graph $H$ on $m$ edges without isolated vertices, $$R(C_k,H) \leq 2m+\left\lfloor\frac{k-1}{2}\right\rfloor?$$ This was proved for even $k$ by Erdős, Faudree, Rousseau, and Schelp [EFRS93]. This was proved for $k=3$ independently by Goddard and Kleitman [GoKl94] and Sidorenko [Si91]. This was proved for $k=5$ by Jayawardene [Ja99]. Finally it was proved for all odd $k\geq 7$ by Cambie, Freschi, Morawski, Petrova, and Pokrovskiy [CFMPP26]. This problem is #35 in Ramsey Theory in the graphs problem collection.
- notes: Erdos Problem 570 -- https://www.erdosproblems.com/570
- track: solved
- answer_shape: decide
- source_stem: 570
- mathdb_ref: erdos:570
- source_namespace: Erdos570
- source_theorem: erdos_570
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
        ∀ (k : ℕ) (hk : 3 ≤ k),
          ∀ᶠ (m : ℕ) in atTop,
            ∀ (W : Type) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj],
              (∀ v, 0 < H.degree v) →
              H.edgeSet.ncard = m →
              SimpleGraph.graphRamsey (SimpleGraph.cycleGraph k) H ≤ 2 * m + (k - 1) / 2

end Problem
