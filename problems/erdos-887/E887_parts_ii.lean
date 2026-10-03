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

- problem_id: E887_parts_ii
- collection: erdos
- question_id: erdos:887
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/887.lean#erdos_887.parts.ii
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is there an absolute constant $K$ such that, for every $C > 0$, if $n$ is sufficiently large then $n$ has at most $K$ divisors in $(n^{\frac{1}{2}}, n^{\frac{1}{2}} + C n^{\frac{1}{4}})$.
- notes: Erdos Problem 887 -- https://www.erdosproblems.com/887
- track: open
- answer_shape: proof
- source_stem: 887
- mathdb_ref: erdos:887
- source_namespace: Erdos887
- source_theorem: erdos_887.parts.ii
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Finset Real

namespace Problem

abbrev Target : Prop :=
    ∃ K, ∀ C > (0 : ℝ), ∀ᶠ n in atTop,
        #{ d ∈ Ioo ⌊√n⌋₊ ⌈√n + C * n^((1 : ℝ) / 4)⌉₊ | d ∣ n } ≤ K

end Problem
