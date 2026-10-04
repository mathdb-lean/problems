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

- problem_id: E1125
- collection: erdos
- question_id: erdos:1125
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1125.lean#erdos_1125
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $f:\mathbb{R}\to \mathbb{R}$ be such that $$2f(x) \leq f(x+h)+f(x+2h)$$ for every $x\in \mathbb{R}$ and $h>0$. Must $f$ be monotonic? A problem of Kemperman [Ke69], who proved it is true if $f$ is measurable. Erdős [Er81b] wrote 'if it were my problem I would offer \$500 for it'. This was solved by Laczkovich [La84].
- notes: Erdos Problem 1125 -- https://www.erdosproblems.com/1125
- track: solved
- answer_shape: decide
- source_stem: 1125
- mathdb_ref: erdos:1125
- source_namespace: Erdos1125
- source_theorem: erdos_1125
- source_category: research solved
- source_ams: 26
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ (f : ℝ → ℝ)
        (hf : ∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h)),
        Monotone f

end Problem
