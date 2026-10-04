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

- problem_id: E955_refute
- collection: erdos
- question_id: erdos:955
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/955.lean#erdos_955
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If $A\subset \mathbb{N}$ has density $0$ then $s^{-1}(A)$ must also have density $0$. A conjecture of Erdős, Granville, Pomerance, and Spiro [EGPS90].
- notes: Erdos Problem 955 -- https://www.erdosproblems.com/955
- track: open
- answer_shape: refute
- pair_id: E955
- pair_role: refute
- source_stem: 955
- mathdb_ref: erdos:955
- source_namespace: Erdos955
- source_theorem: erdos_955
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: s_one s_two s_six s_twelve s_twenty_eight
- generator: adapters/formal_conjectures/adapter.py
-/

open Nat Filter
open scoped ArithmeticFunction ArithmeticFunction.sigma Topology

namespace Problem

/--
Let $s(n)=\sigma(n)-n=\sum_{\substack{d\mid n\\ d<n}}d$ be the sum of proper divisors function.
-/
def s (n : ℕ) : ℕ := σ 1 n - n

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem s_one : s 1 = 0 := by decide

@[category test, AMS 11]
theorem s_two : s 2 = 1 := by decide

@[category test, AMS 11]
theorem s_six : s 6 = 6 := by decide

@[category test, AMS 11]
theorem s_twelve : s 12 = 16 := by decide

@[category test, AMS 11]
theorem s_twenty_eight : s 28 = 28 := by decide

abbrev Target : Prop :=
    ¬ (
      ∀ A : Set ℕ, A.HasDensity 0 → { x | s x ∈ A }.HasDensity 0
    )

end Problem
