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

- problem_id: E377_prove
- collection: erdos
- question_id: erdos:377
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/377.lean#erdos_377
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is there some absolute constant $C > 0$ such that $$ \sum_{p \leq n} 1_{p\nmid {2n \choose n}}\frac{1}{p} \leq C $$ for all $n$?
- notes: Erdos Problem 377 -- https://www.erdosproblems.com/377
- track: open
- answer_shape: prove
- pair_id: E377
- pair_role: prove
- source_stem: 377
- mathdb_ref: erdos:377
- source_namespace: Erdos377
- source_theorem: erdos_377
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter

open scoped Topology

namespace Problem

/--
The sum of the inverses of all primes smaller than $n$, which don't divide the central
binom coefficient.
-/
noncomputable abbrev sumInvPrimesNotDvdCentralBinom (n : ℕ) : ℝ :=
  ∑ p ∈ Finset.Icc 1 n with p.Prime, if p ∣ n.centralBinom then 0 else (1 : ℝ) / p

abbrev Target : Prop :=
    ∃ C > (0 : ℝ), ∀ (n : ℕ), sumInvPrimesNotDvdCentralBinom n ≤ C

end Problem
