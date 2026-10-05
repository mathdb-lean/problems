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

- problem_id: M21003_prove
- collection: mathoverflow
- question_id: mathoverflow:21003
- source: formal-conjectures
- source_locator: FormalConjectures/Mathoverflow/21003.lean#mathoverflow_21003
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is there any polynomial $f(x, y) \in \mathbb{Q}[x, y]$ such that $f : \mathbb{Q} \times \mathbb{Q} \rightarrow \mathbb{Q}$ is a bijection?
- notes: MathOverflow 21003 -- https://mathoverflow.net/questions/21003
- track: open
- answer_shape: prove
- pair_id: M21003
- pair_role: prove
- source_stem: 21003
- source_namespace: Mathoverflow21003
- source_theorem: mathoverflow_21003
- source_category: research open
- source_ams: 12
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open scoped Polynomial

namespace Problem

abbrev Target : Prop :=
    ∃ f : MvPolynomial (Fin 2) ℚ, Function.Bijective fun x ↦ f.eval x

end Problem
