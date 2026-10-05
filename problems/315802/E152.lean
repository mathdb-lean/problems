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

- problem_id: E152
- collection: erdos
- question_id: erdos:152
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/152.lean#erdos_152
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Must `lim f n = ∞`? This was proved formally by the DeepMind prover agent [DM26a].
- notes: Erdos Problem 152 -- https://www.erdosproblems.com/152
- track: solved
- answer_shape: decide
- source_stem: 152
- mathdb_ref: erdos:152
- source_namespace: Erdos152
- source_theorem: erdos_152
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open scoped Pointwise Asymptotics
open Filter

namespace Problem

/-- Define `f n` to be the minimum of `|{s | s - 1 ∉ A + A, s ∈ A + A, s + 1 ∉ A + A}|` as `A`
ranges over all Sidon sets of size `n`. -/
noncomputable def f (n : ℕ) : ℕ :=
  ⨅ A : {A : Set ℕ | A.ncard = n ∧ IsSidon A},
  {s : ℕ | s - 1 ∉ A.1 + A.1 ∧ s ∈ A.1 + A.1 ∧ s + 1 ∉ A.1 + A.1}.ncard

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ Tendsto f atTop atTop

end Problem
