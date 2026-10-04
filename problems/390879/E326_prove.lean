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

- problem_id: E326_prove
- collection: erdos
- question_id: erdos:326
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/326.lean#erdos_326
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Does there exist $A = \{a_1 < a_2 < \cdots\} \subset \mathbb{N}$ which is a minimal basis of order $2$ (i.e. every large integer is the sum of $2$ elements from $A$, and no proper subset of $A$ has this property), such that $$\lim_{k\to\infty} \frac{a_k}{k^2} = c$$ for some $c \neq 0$? Erdős and Graham conjectured a negative answer to this question [ErGr80]. "Minimal basis of order $2$" is formalised as `Minimal` for the predicate `Set.IsAsymptoticAddBasisOfOrder · 2` on sets of naturals ordered by inclusion.
- notes: Erdos Problem 326 -- https://www.erdosproblems.com/326
- track: open
- answer_shape: prove
- pair_id: E326
- pair_role: prove
- source_stem: 326
- mathdb_ref: erdos:326
- source_namespace: Erdos326
- source_theorem: erdos_326
- source_category: research open
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter

open scoped Topology

namespace Problem

abbrev Target : Prop :=
    ∃ (a : ℕ → ℕ), StrictMono a ∧
        Minimal (fun A : Set ℕ ↦ A.IsAsymptoticAddBasisOfOrder 2) (Set.range a) ∧
          ∃ (c : ℝ), c ≠ 0 ∧ Tendsto (fun n ↦ (a n : ℝ) / n ^ 2) atTop (𝓝 c)

end Problem

-- Formalisation note: This is trivially true for `x = 0` by taking `a = id`. Cassels' proof
