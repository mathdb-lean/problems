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

- problem_id: E986
- collection: erdos
- question_id: erdos:986
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/986.lean#erdos_986
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: For any fixed $s\geq 3$, $$R(s,k) \gg \frac{k^{s-1}}{(\log k)^c}$$ for some constant $c=c(s)>0$. According to Chung and Graham [ChGr98] this was first conjectured by Erdős in 1947. Proved by Bradač [Br26], with $c=2s-4$. The linked formal proof (Codex and GPT-5.6 Sol) gives `k ^ (s - 1) / (log k) ^ c = O(R(s, k))` for a natural `c > 0`, with the Ramsey number defined through `CliqueFree`/`IndepSetFree`; this implies the statement below.
- notes: Erdos Problem 986 -- https://www.erdosproblems.com/986
- track: solved
- answer_shape: proof
- source_stem: 986
- mathdb_ref: erdos:986
- source_namespace: Erdos986
- source_theorem: erdos_986
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter

namespace Problem

abbrev Target : Prop :=
    ∀ (s : ℕ) (hs : 3 ≤ s),
      ∃ (c C : ℝ), 0 < c ∧ 0 < C ∧
        ∀ᶠ (k : ℕ) in atTop,
          (SimpleGraph.classicalRamsey s k : ℝ) ≥
            C * (k : ℝ) ^ (s - 1) / (Real.log k) ^ c

end Problem
