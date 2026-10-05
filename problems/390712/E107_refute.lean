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

- problem_id: E107_refute
- collection: erdos
- question_id: erdos:107
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/107.lean#erdos_107
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $f(n)$ be minimal such that any $f(n)$ points in $ℝ^2$, no three on a line, contain $n$ points which form the vertices of a convex $n$-gon. Prove that $f(n) = 2^{n-2} + 1$.
- notes: Erdos Problem 107 -- https://www.erdosproblems.com/107
- track: open
- answer_shape: refute
- pair_id: E107
- pair_role: refute
- source_stem: 107
- mathdb_ref: erdos:107
- source_namespace: Erdos107
- source_theorem: erdos_107
- source_category: research open
- source_ams: 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: f_zero_eq
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter
open EuclideanGeometry

namespace Problem

/-- The set of $N$ such that any $N$ points in the plane, no three on a line,
contain a convex $n$-gon. -/
def cardSet (n : ℕ) := { N | ∀ (pts : Finset ℝ²), pts.card = N → NonTrilinear (pts : Set ℝ²) →
  HasConvexNGon n pts }

/-- The function $f(n)$ specified in `erdos_107`. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf (cardSet n)

namespace variants

end variants

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Depending on details of definitions,
the statement is false or trivial for $n < 3$. -/
@[category test, AMS 52]
theorem f_zero_eq : f 0 = 0 := by
  have : ∀ P, HasConvexNGon 0 P := by
    intro; use ∅; simp [ConvexIndep]
  simp [f, cardSet, this]

abbrev Target : Prop :=
    ¬ (
      ∀ n ≥ 3, f n = 2^(n - 2) + 1
    )

end Problem
