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

- problem_id: E57
- collection: erdos
- question_id: erdos:57
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/57.lean#erdos_57
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If $G$ is a graph with infinite chromatic number and $a_1 < a_2 < \cdots$ are lengths of the odd cycles of $G$ then $\sum \frac{1}{a_i} = \infty$. Conjectured by Erdős and Hajnal [ErHa66], and solved by Liu and Montgomery [LiMo20]. The linked formal proof (Codex and GPT-5.6 Sol) states the conclusion as `¬ Summable (oddCycleReciprocal G)`, where `oddCycleReciprocal G n` is `n⁻¹` if `n` is an odd cycle length of `G` and `0` otherwise; this is the indicator form of the sum below.
- notes: Erdos Problem 57 -- https://www.erdosproblems.com/57
- track: solved
- answer_shape: proof
- source_stem: 57
- mathdb_ref: erdos:57
- source_namespace: Erdos57
- source_theorem: erdos_57
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

abbrev Target : Prop :=
    ∀ {V : Type*} (G : SimpleGraph V), G.chromaticNumber = ⊤ →
      ¬ Summable (fun (a : G.oddCycleLengths) ↦ 1 / (a : ℝ))

end Problem
