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

- problem_id: X2107_12475_CollatzLike_CollatzLike
- collection: arxiv
- question_id: arxiv:2107.12475/CollatzLike
- source: formal-conjectures
- source_locator: FormalConjectures/Arxiv/2107.12475/CollatzLike.lean#CollatzLike
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: For $n > 8$, $2^n$ is not the the sum of distinct powers of $3$. Expressed here in terms of the base $3$ digits of $n$. This conjecture is equivalent to the halting of a $15$-state $2$-symbol Turing Machine. TODO(lezeau): Formalize the Turing Machine version of this problem. Source: *Hardness of Busy Beaver Value BB(15)*: https://link.springer.com/chapter/10.1007/978-3-031-72621-7_9 This is also https://arxiv.org/abs/2107.12475.
- notes: arXiv 2107.12475/CollatzLike -- https://arxiv.org/abs/2107.12475
- track: open
- answer_shape: proof
- source_stem: 2107.12475/CollatzLike
- source_namespace: Arxiv.«2107.12475»
- source_theorem: CollatzLike
- source_category: research open
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: two_not_in_digits_three_pow_eight
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/--
For $n = 8$, $2$ is not contained in the base $3$ digits of $n$.
-/
@[category test, AMS 5 11]
theorem two_not_in_digits_three_pow_eight : 2 ∉ Nat.digits 3 (2^8) := by norm_num

abbrev Target : Prop :=
    ∀ (n : ℕ) (hn : 8 < n),
      2 ∈ Nat.digits 3 (2^n)

end Problem
