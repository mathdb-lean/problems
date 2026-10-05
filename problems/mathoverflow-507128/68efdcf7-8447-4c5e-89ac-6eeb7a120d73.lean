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

- problem_id: M507128_exists_isFractionRing_self_ideal_ne_top_invertible
- collection: mathoverflow
- question_id: mathoverflow:507128
- source: formal-conjectures
- source_locator: FormalConjectures/Mathoverflow/507128.lean#exists_isFractionRing_self_ideal_ne_top_invertible
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: There exists a proper ideal `I` in a (commutative) total ring `R` of fractions that is an invertible module. If `I ⊊ R` is such an example, `I` must have infinite order in the Picard group. Moreover, `R` must not be Noetherian (otherwise it must be semi-local and therefore have trivial Picard group). The linked formal proof gives the following explicit construction. Let `D = ℂ[X, Y] / (Y² - X³)` be the coordinate ring of the cuspidal cubic. Let `P = (X - 1, Y - 1)`, which is an invertible ideal. Let `M` be the direct sum of the evaluation fibres at cusp parameters `r ≠ 1`. Form the idealization `R = D ⋉ M`. The desired ideal is the range of the multiplication map `R ⊗[D] P → R`.
- notes: MathOverflow 507128 -- https://mathoverflow.net/questions/507128/embeddability-order-on-picard-groups
- track: solved
- answer_shape: proof
- source_stem: 507128
- source_namespace: Mathoverflow507128
- source_theorem: exists_isFractionRing_self_ideal_ne_top_invertible
- source_category: research solved
- source_ams: 13
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

abbrev Target : Prop :=
    ∃ (R : Type) (_ : CommRing R) (_ : IsFractionRing R R) (I : Ideal R),
      I ≠ ⊤ ∧ Module.Invertible R I

end Problem
