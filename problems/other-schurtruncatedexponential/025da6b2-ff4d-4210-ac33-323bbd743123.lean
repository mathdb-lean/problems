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

- problem_id: ZSchurTruncatedExponential_schur_truncatedExp_galoisGroup_equiv
- collection: other
- question_id: other:SchurTruncatedExponential
- source: formal-conjectures
- source_locator: FormalConjectures/Other/SchurTruncatedExponential.lean#schur_truncatedExp_galoisGroup_equiv
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **Schur's Theorem (1924):** Let `f_n(x) = ∑_{j=0}^n x^j/j!` be the `n`-th truncated exponential polynomial over `ℚ`. Then for `n ≥ 2`: - If `n ≡ 0 (mod 4)`, the Galois group of `f_n` is isomorphic to the alternating group `A_n` - If `n ≢ 0 (mod 4)`, the Galois group of `f_n` is isomorphic to the symmetric group `S_n`
- notes: Problem SchurTruncatedExponential -- https://math.stackexchange.com/questions/2814220
- track: solved
- answer_shape: proof
- source_stem: SchurTruncatedExponential
- source_namespace: SchurTruncatedExponential
- source_theorem: schur_truncatedExp_galoisGroup_equiv
- source_category: research solved
- source_ams: 12
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

/-
Note: This was asked by Nick Katz. Quasi-autoformalized using Claude 4.0 Sonnet.
-/

namespace Problem

open Polynomial

open scoped Nat

/--
The truncated exponential polynomial `truncatedExp n` is
given by `∑_{j=0}^{n} x^j / j!` over `ℚ`, which is the
`n`-th partial sum of the Taylor series for the exponential function `e^x`.
-/
noncomputable def truncatedExp (n : ℕ) : ℚ[X] :=
  ∑ j ∈ Finset.range (n + 1), (1 / j ! : ℚ) • X ^ j

abbrev Target : Prop :=
    ∀ (n : ℕ) (hn : n ≥ 2),
      letI f := truncatedExp n
      if n % 4 = 0 then
        -- Galois group is alternating group A_n
        Nonempty (f.Gal ≃* alternatingGroup (Fin n))
      else
        -- Galois group is symmetric group S_n
        Nonempty (f.Gal ≃* Equiv.Perm (Fin n))

end Problem
