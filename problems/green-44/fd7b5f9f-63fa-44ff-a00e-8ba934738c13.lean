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

- problem_id: G44_prove
- collection: green
- question_id: green:44
- source: formal-conjectures
- source_locator: FormalConjectures/GreensOpenProblems/44.lean#green_44
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Sieve $[N]$ by removing half the residue classes mod $p_i$, for primes $2 \leqslant p_1 < p_2 < \dots < p_{1000} < N^{9/10}$. Does the remaining set have size at most $\frac{1}{10} N$? We interpret "half the residue classes" as $\lfloor p_i / 2 \rfloor$.
- notes: Green, open problem 44
- track: open
- answer_shape: prove
- pair_id: G44
- pair_role: prove
- source_stem: 44
- source_namespace: Green44
- source_theorem: green_44
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open scoped Nat

abbrev Target : Prop :=
    ∀ (N : ℕ) (p : Fin 1000 → ℕ) (A : (i : Fin 1000) → Finset (ZMod (p i))),
      let remaining := (Finset.Icc 1 N).filter (fun x => ∀ i, (x : ZMod (p i)) ∉ A i)
      (∀ i, (p i).Prime) →
      StrictMono p →
      (p 999) ^ 10 < N ^ 9 →
      (∀ i, (A i).card = (p i) / 2) →
      10 * remaining.card ≤ N

end Problem
