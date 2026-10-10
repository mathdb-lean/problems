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

- problem_id: E1126
- collection: erdos
- question_id: erdos:1126
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1126.lean#erdos_1126
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If $$f(x+y)=f(x)+f(y)$$ for almost all $x,y\in \mathbb{R}$ then there exists a function $g$ such that $$g(x+y)=g(x)+g(y)$$ for all $x,y\in\mathbb{R}$ such that $f(x)=g(x)$ for almost all $x$. Proved independently by de Bruijn [dB66] and Jurkat [Ju65].
- notes: Erdos Problem 1126 -- https://www.erdosproblems.com/1126
- track: solved
- answer_shape: decide
- source_stem: 1126
- mathdb_ref: erdos:1126
- source_namespace: Erdos1126
- source_theorem: erdos_1126
- source_category: research solved
- source_ams: 26 28
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open MeasureTheory

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀
        (f : ℝ → ℝ)
        (h :
          ∀ᵐ (p : ℝ × ℝ) ∂(volume.prod volume),
            f (p.1 + p.2) = f p.1 + f p.2),
        ∃ h : ℝ → ℝ,
          (∀ x y, h (x + y) = h x + h y) ∧ (∀ᵐ x ∂volume, f x = h x)

end Problem
