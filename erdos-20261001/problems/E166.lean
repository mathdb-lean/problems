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

- problem_id: E166
- collection: erdos
- question_id: erdos:166
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/166.lean#erdos_166
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Prove that $$R(4,k) \gg \frac{k^3}{(\log k)^{O(1)}}.$$ This is true, and was proved by Mattheus and Verstraëte [MaVe23], who showed that $R(4,k) \gg \frac{k^3}{(\log k)^4}$. This problem is #5 in Ramsey Theory in the graphs problem collection. The linked formal proof (Codex and GPT-5.6 Sol, via the construction of Bradač used for Problem 920) gives `k ^ 3 / (log k) ^ c = O(R(4, k))` for a natural `c > 0`, with the Ramsey number defined through `CliqueFree`/`IndepSetFree`; this implies the statement below.
- notes: Erdos Problem 166 -- https://www.erdosproblems.com/166
- track: solved
- answer_shape: decide
- source_stem: 166
- mathdb_ref: erdos:166
- source_namespace: Erdos166
- source_theorem: erdos_166
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
        ∃ (c C : ℝ), 0 < c ∧ 0 < C ∧
          ∀ᶠ (k : ℕ) in atTop,
            (SimpleGraph.classicalRamsey 4 k : ℝ) ≥
              C * (k : ℝ) ^ 3 / (Real.log k) ^ c

end Problem
