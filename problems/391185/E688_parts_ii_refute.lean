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

- problem_id: E688_parts_ii_refute
- collection: erdos
- question_id: erdos:688
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/688.lean#erdos_688.parts.ii
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: In particular, is it true that $\epsilon_n = o(1)$?
- notes: Erdos Problem 688 -- https://www.erdosproblems.com/688
- track: open
- answer_shape: refute
- pair_id: E688_parts_ii
- pair_role: refute
- source_stem: 688
- mathdb_ref: erdos:688
- source_namespace: Erdos688
- source_theorem: erdos_688.parts.ii
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Real Filter

namespace Problem

/--
Define $\epsilon_n$ to be maximal such that there exists some choice of congruence class $a_p$
for all primes $n^{\epsilon_n} < p \leq n$ such that every integer in $[1,n]$ satisfies at least
one of the congruences $\equiv a_p \pmod p$.
-/
def Erdos688Prop (n : ℕ) (ε : ℝ) : Prop :=
  ∃ (a : ℕ → ℕ), ∀ (m : ℕ), 1 ≤ m → m ≤ n →
    ∃ (p : ℕ), p.Prime ∧ (n : ℝ)^ε < p ∧ p ≤ n ∧
      a p ≡ m [MOD p]

noncomputable def epsilonFunction (n : ℕ) : ℝ := sSup {ε : ℝ | Erdos688Prop n ε}

abbrev Target : Prop :=
    ¬ (
      epsilonFunction =o[atTop] (fun (n : ℕ) ↦ (1 : ℝ))
    )

end Problem
