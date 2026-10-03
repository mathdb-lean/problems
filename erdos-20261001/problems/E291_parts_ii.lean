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

- problem_id: E291_parts_ii
- collection: erdos
- question_id: erdos:291
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/291.lean#erdos_291.parts.ii
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that $(a_n,L_n)>1$ occurs for infinitely many $n$? Steinerberger has observed that the answer to the second question is trivially yes: for example, any $n$ which begins with a $2$ in base $3$ has $3\mid (a_n,L_n)$.
- notes: Erdos Problem 291 -- https://www.erdosproblems.com/291
- track: solved
- answer_shape: decide
- source_stem: 291
- mathdb_ref: erdos:291
- source_namespace: Erdos291
- source_theorem: erdos_291.parts.ii
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: L_eval a_eval
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Nat Finset Set Filter

namespace Problem

/--
$L_n$ is the least common multiple of $\{1,\ldots,n\}$.
-/
def L (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).lcm (fun x ↦ x)

/--
$a_n$ is defined by $\sum_{1\leq k\leq n}\frac{1}{k}=\frac{a_n}{L_n}$.
-/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, L n / k

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem L_eval : L 1 = 1 ∧ L 2 = 2 ∧ L 3 = 6 ∧ L 4 = 12 := by decide

@[category test, AMS 11]
theorem a_eval : a 1 = 1 ∧ a 2 = 3 ∧ a 3 = 11 ∧ a 4 = 25 := by decide

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
      { n : ℕ | Nat.gcd (a n) (L n) > 1 }.Infinite

end Problem
