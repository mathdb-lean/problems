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

- problem_id: G45_prove
- collection: green
- question_id: green:45
- source: formal-conjectures
- source_locator: FormalConjectures/GreensOpenProblems/45.lean#green_45
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Can we pick residue classes $a_p \pmod{p}$, one for each prime $p \leq N$, such that every integer $\leq N$ lies in at least $10$ of them? Erdős remarks that he does not know how to answer it with $10$ replaced by $2$; this is `Erdos689.erdos_689`.
- notes: Green, open problem 45 -- https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.45
- track: open
- answer_shape: prove
- pair_id: G45
- pair_role: prove
- source_stem: 45
- source_namespace: Green45
- source_theorem: green_45
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

abbrev Target : Prop :=
    ∀ᶠ N in .atTop, ∃ a : ℕ → ℕ, ∀ m ∈ Finset.Icc 1 N,
      10 ≤ (Finset.Icc 1 N |>.filter fun p => p.Prime ∧ a p ≡ m [MOD p]).card

end Problem
