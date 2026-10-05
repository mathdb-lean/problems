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

- problem_id: RTuDengConjecture_tu_deng_conjecture
- collection: paper
- question_id: paper:TuDengConjecture
- source: formal-conjectures
- source_locator: FormalConjectures/Paper/TuDengConjecture.lean#tu_deng_conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **The Tu-Deng conjecture.** For $k \ge 2$ and a nonzero residue $t$ modulo $2^k - 1$, there are at most $2^{k-1}$ pairs of residues $(a, b)$ with $a + b = t$ whose binary weights (of their representatives in $0, \dots, 2^k - 2$) sum to at most $k - 1$. Proved in [LLX26] and independently in [Cu26]; see also the Lean development [Lean26].
- notes: Problem from TuDengConjecture -- https://doi.org/10.1007/s10623-010-9413-9
- track: solved
- answer_shape: proof
- source_stem: TuDengConjecture
- source_namespace: TuDengConjecture
- source_theorem: tu_deng_conjecture
- source_category: research solved
- source_ams: 5 11 94
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- The binary weight of a natural number: the number of ones in its binary expansion. -/
def binaryWeight (n : ℕ) : ℕ := (Nat.digits 2 n).sum

abbrev Target : Prop :=
    ∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0),
      {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
          p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
        ≤ 2 ^ (k - 1)

end Problem
