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

- problem_id: E907
- collection: erdos
- question_id: erdos:907
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/907.lean#erdos_907
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $f:\mathbb{R}\to \mathbb{R}$ be such that $f(x+h)-f(x)$ is continuous for every $h>0$. Is it true that $$f=g+h$$ for some continuous $g$ and additive $h$ (i.e. $h(x+y)=h(x)+h(y)$)? A conjecture of Erdős from the early 1950s. Answered in the affirmative by de Bruijn [dB51].
- notes: Erdos Problem 907 -- https://www.erdosproblems.com/907
- track: solved
- answer_shape: decide
- source_stem: 907
- mathdb_ref: erdos:907
- source_namespace: Erdos907
- source_theorem: erdos_907
- source_category: research solved
- source_ams: 26 39
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ f : ℝ → ℝ, (∀ h : ℝ, 0 < h → Continuous fun x => f (x + h) - f x) →
          ∃ g a : ℝ → ℝ, Continuous g ∧ (∀ x y, a (x + y) = a x + a y) ∧ f = g + a

end Problem
