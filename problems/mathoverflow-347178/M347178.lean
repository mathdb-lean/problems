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

- problem_id: M347178
- collection: mathoverflow
- question_id: mathoverflow:347178
- source: formal-conjectures
- source_locator: FormalConjectures/Mathoverflow/347178.lean#mathoverflow_347178
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $f : \mathbb R^n \to \mathbb R, n \geq 2$ be a $C^1$ function. Is it true that $$\sup_{x \in \mathbb R^n}f(x) = \sup_{x\in \mathbb R^n} f(x+\nabla f(x))$$? Answer: No. A counterexample in $\mathbb R^2$ is recorded in the linked formal proof.
- notes: MathOverflow 347178 -- https://mathoverflow.net/questions/347178
- track: solved
- answer_shape: decide
- source_stem: 347178
- source_namespace: Mathoverflow347178
- source_theorem: mathoverflow_347178
- source_category: research solved
- source_ams: 26
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Real Set
open scoped EuclideanGeometry

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ᵉ (n ≥ 2) (f : ℝ^n → ℝ) (_ : ContDiff ℝ 1 f),
        (BddAbove (range f) ↔ BddAbove (range (fun x ↦ f (x + gradient f x)))) ∧
        (⨆ x, (f x : EReal)) = ⨆ x, (f (x + gradient f x) : EReal)

end Problem
