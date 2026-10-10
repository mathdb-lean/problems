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

- problem_id: E596
- collection: erdos
- question_id: erdos:596
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/596.lean#erdos_596
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **Erdős Problem 596** (Erdős–Hajnal, [Er87]). For which graph pairs $(G_1, G_2)$ is it true that (1) for every $n \geq 1$ there is a graph $H$ without a $G_1$ such that any $n$-colouring of $H$'s edges contains a monochromatic $G_2$, and yet (2) for every graph $H$ without a $G_1$ there is an $\aleph_0$-colouring of $H$'s edges with no monochromatic $G_2$? Erdős and Hajnal originally conjectured that no such pair exists; but $(C_4, C_6)$ witnesses it (Nešetřil–Rödl + Erdős–Hajnal). The full question is to characterise the class of all such pairs, recorded here as `answer(sorry)`. See Problem 595 for the specific case $(G_1, G_2) = (K_4, K_3)$.
- notes: Erdos Problem 596 -- https://www.erdosproblems.com/596
- track: open
- answer_shape: value
- answer_type: ∀ {U₁ U₂ : Type}, SimpleGraph U₁ → SimpleGraph U₂ → Prop
- answer_pinned: false
- answer_pinned_reason: trivial_predicate_works
- source_stem: 596
- mathdb_ref: erdos:596
- source_namespace: Erdos596
- source_theorem: erdos_596
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open SimpleGraph

namespace Problem

abbrev Target (value : ∀ {U₁ U₂ : Type}, SimpleGraph U₁ → SimpleGraph U₂ → Prop) : Prop :=
    ∀ {U₁ U₂ : Type} (G₁ : SimpleGraph U₁) (G₂ : SimpleGraph U₂),
      IsErdosHajnalExceptional G₁ G₂ ↔
      value G₁ G₂

end Problem
