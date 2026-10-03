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

- problem_id: E726_refute
- collection: erdos
- question_id: erdos:726
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/726.lean#erdos_726
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: As $n\to \infty$ ranges over integers $\sum_{p\leq n}1_{n\in (p/2,p)\pmod{p}}\frac{1}{p}\sim \frac{\log\log n}{2}$? A conjecture of Erdős, Graham, Ruzsa, and Straus [EGRS75]. By $n\in (p/2,p)\pmod{p}$ we mean $n\equiv r\pmod{p}$ for some integer $r$ with $p/2<r<p$. The remainder `n % p` is computed in `ℕ` before casting to `ℝ`.
- notes: Erdos Problem 726 -- https://www.erdosproblems.com/726
- track: open
- answer_shape: refute
- pair_id: E726
- pair_role: refute
- source_stem: 726
- mathdb_ref: erdos:726
- source_namespace: Erdos726
- source_theorem: erdos_726
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Nat Filter Finset
open scoped Topology Asymptotics

namespace Problem

abbrev Target : Prop :=
    ¬ (
      (fun n : ℕ ↦ ∑ p ∈ (range (n + 1)).filter
            (fun p : ℕ ↦ p.Prime ∧ (p : ℝ) / 2 < ((n % p : ℕ) : ℝ)),
          (1 : ℝ) / (p : ℝ))
        ~[atTop] (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) / 2)
    )

end Problem
