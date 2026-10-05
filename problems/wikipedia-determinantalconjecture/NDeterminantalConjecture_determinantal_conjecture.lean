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

- problem_id: NDeterminantalConjecture_determinantal_conjecture
- collection: wikipedia
- question_id: wikipedia:DeterminantalConjecture
- source: formal-conjectures
- source_locator: FormalConjectures/Wikipedia/DeterminantalConjecture.lean#determinantal_conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Does the determinant of the sum $A + B$ of two $n \times n$ normal complex matrices $A$ and $B$ always lie in the convex hull of the $n!$ points $\prod\_i (\lambda(A)\_i + \lambda(B)\_{\sigma(i)})$? Here the numbers $\lambda(A)\_i$ and $\lambda(B)\_i$ are the eigenvalues of $A$ and $B$, and $\sigma$ is an element of the symmetric group $S\_n$.
- notes: Wikipedia: DeterminantalConjecture -- https://en.wikipedia.org/wiki/Determinantal_conjecture
- track: open
- answer_shape: proof
- source_stem: DeterminantalConjecture
- source_namespace: DeterminantalConjecture
- source_theorem: determinantal_conjecture
- source_category: research open
- source_ams: 15
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

/- Formalisation note: Here, we represent the two normal matrices as $U_1 D_1 U_1^*$ and
$U_2 D_2 U_2^*$ respectively, where $U_1, U_2$ are unitary and $D_1, D_2$
are diagonal. This is an universal form of a normal matrix,
allowing to retrieve $\lambda (A)_i$ as ${D_1}_{i,i}$, whereas the current mathlib
doesn't support obtaining the vector of eigenvalues from a general normal
non-Hermitian matrix. -/

namespace Problem

abbrev Target : Prop :=
    ∀ (n : Type) [Fintype n] [DecidableEq n]
        (d1 d2 : n → ℂ) (U1 U2 : unitary (Matrix n n ℂ)),
      (U1 * Matrix.diagonal d1 * star U1 + U2 * Matrix.diagonal d2 * star U2).det
        ∈ convexHull ℝ { ∏ i, (d1 i + d2 (σ i)) | σ : Equiv.Perm n }

end Problem

/- Formalisation note: Here, we represent the two normal matrices as $U_1 D_1 U_1^*$ and
$U_2 D_2 U_2^*$ respectively, where $U_1, U_2$ are unitary and $D_1, D_2$
are diagonal. This is an universal form of a normal matrix,
allowing to retrieve $\lambda (A)_i$ as ${D_1}_{i,i}$, whereas the current mathlib
doesn't support obtaining the vector of eigenvalues from a general normal
non-Hermitian matrix. -/
