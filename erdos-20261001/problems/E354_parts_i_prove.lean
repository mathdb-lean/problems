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

- problem_id: E354_parts_i_prove
- collection: erdos
- question_id: erdos:354
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/354.lean#erdos_354.parts.i
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $\alpha,\beta\in \mathbb{R}_{>0}$ such that $\alpha/\beta$ is irrational. Is the multiset $$\{ \lfloor \alpha\rfloor,\lfloor 2\alpha\rfloor,\lfloor 4\alpha\rfloor,\ldots\}\cup \{ \lfloor \beta\rfloor,\lfloor 2\beta\rfloor,\lfloor 4\beta\rfloor,\ldots\}$$ complete?
- notes: Erdos Problem 354 -- https://www.erdosproblems.com/354
- track: open
- answer_shape: prove
- pair_id: E354_parts_i
- pair_role: prove
- source_stem: 354
- mathdb_ref: erdos:354
- source_namespace: Erdos354
- source_theorem: erdos_354.parts.i
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- The sequence `⌊a⌋, ⌊γ * a⌋, ⌊γ ^ 2 * a⌋, ..., ⌊γ ^ i * a⌋, ...`. -/
noncomputable def FloorMultiples (a γ : ℝ) (n : ℕ) : ℤ := ⌊γ ^ n * a⌋

/-- The sequence `⌊a⌋, ⌊b⌋, ⌊γ * a⌋, ⌊γ * b⌋, ... ⌊γ ^ i * a⌋, ⌊γ ^ i * b⌋, ...` -/
noncomputable def FloorMultiples.interleave (a b γ : ℝ) (n : ℕ) : ℤ :=
  if n % 2 = 0 then
    FloorMultiples a γ (n / 2)
  else
    FloorMultiples b γ (n / 2)

abbrev Target : Prop :=
    ∀ᵉ (α > 0) (β > 0), Irrational (α / β) →
        IsAddCompleteNatSeq' (FloorMultiples.interleave α β 2)

end Problem
