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

- problem_id: E541
- collection: erdos
- question_id: erdos:541
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/541.lean#erdos_541
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $a_1, \dots, a_p$ be (not necessarily distinct) residues modulo a prime $p$, such that there exists some $r$ so that if $S \subseteq [p]$ is non-empty and $$\sum_{i \in S} a_i \equiv 0 \pmod{p}$$ then $|S| = r$. Must there be at most two distinct residues amongst the $a_i$? This was formalized in Lean by Alexeev using Aristotle and ChatGPT.
- notes: Erdos Problem 541 -- https://www.erdosproblems.com/541
- track: solved
- answer_shape: decide
- source_stem: 541
- mathdb_ref: erdos:541
- source_namespace: Erdos541
- source_theorem: erdos_541
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ (∀ p, Fact p.Prime → ∀ (a : Fin p → ZMod p),
        (∃ r, ∀ (S : Finset (Fin p)), S ≠ ∅ → ∑ i ∈ S, a i = 0 → S.card = r) →
          (Set.range a).ncard ≤ 2)

end Problem
