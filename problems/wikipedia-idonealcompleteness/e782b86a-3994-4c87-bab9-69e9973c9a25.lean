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

- problem_id: NIdonealCompleteness_idoneal_numbers_completeness_prove
- collection: wikipedia
- question_id: wikipedia:IdonealCompleteness
- source: formal-conjectures
- source_locator: FormalConjectures/Wikipedia/IdonealCompleteness.lean#idoneal_numbers_completeness
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Idoneal numbers completeness conjecture.
- notes: Wikipedia: IdonealCompleteness -- https://en.wikipedia.org/wiki/Idoneal_number
- track: open
- answer_shape: prove
- pair_id: NIdonealCompleteness_idoneal_numbers_completeness
- pair_role: prove
- source_stem: IdonealCompleteness
- source_namespace: Idoneal
- source_theorem: idoneal_numbers_completeness
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/--
Equivalent definition: A positive integer $n$ is idoneal if and only if it cannot be written as
$ab + bc + ac$ for distinct positive integers $a, b,$ and $c$.
-/
def IsIdoneal (n : ℕ) : Prop :=
  0 < n ∧
    ¬ ∃ a b c : ℕ,
      0 < a ∧ a < b ∧ b < c ∧ n = a * b + b * c + a * c

/--
The 65 known idoneal numbers that are conjectured to be the only idoneal numbers.
-/
def knownIdonealNumbers : Finset ℕ :=
  {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 15, 16, 18, 21, 22, 24, 25, 28,
   30, 33, 37, 40, 42, 45, 48, 57, 58, 60, 70, 72, 78, 85, 88, 93, 102, 105,
   112, 120, 130, 133, 165, 168, 177, 190, 210, 232, 240, 253, 273, 280, 312,
   330, 345, 357, 385, 408, 462, 520, 760, 840, 1320, 1365, 1848}

abbrev Target : Prop :=
    ∀ n : ℕ, IsIdoneal n → n ∈ knownIdonealNumbers

end Problem
