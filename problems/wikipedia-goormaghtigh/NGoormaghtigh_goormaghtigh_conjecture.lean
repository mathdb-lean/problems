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

- problem_id: NGoormaghtigh_goormaghtigh_conjecture
- collection: wikipedia
- question_id: wikipedia:Goormaghtigh
- source: formal-conjectures
- source_locator: FormalConjectures/Wikipedia/Goormaghtigh.lean#goormaghtigh_conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: The only Goormaghtigh numbers are $31$ and $8191$.
- notes: Wikipedia: Goormaghtigh -- https://en.wikipedia.org/wiki/Goormaghtigh_conjecture
- track: open
- answer_shape: proof
- source_stem: Goormaghtigh
- source_namespace: Goormaghtigh
- source_theorem: goormaghtigh_conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: isGoormaghtighNumber_31 isGoormaghtighNumber_8191 repunit_two_digits
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- The repunit with `digits` digits in the given base, expressed without division. -/
def repunit (base digits : ℕ) : ℕ :=
  ∑ i ∈ Finset.range digits, base ^ i

/-- A number having repunit representations of at least three digits in two distinct bases. -/
def IsGoormaghtighNumber (N : ℕ) : Prop :=
  ∃ base₁ base₂ digits₁ digits₂ : ℕ,
    2 ≤ base₁ ∧ 2 ≤ base₂ ∧ base₁ ≠ base₂ ∧
      3 ≤ digits₁ ∧ 3 ≤ digits₂ ∧
        repunit base₁ digits₁ = N ∧ repunit base₂ digits₂ = N

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- The number $31$ is a repunit in bases $2$ and $5$. -/
@[category test, AMS 11]
theorem isGoormaghtighNumber_31 : IsGoormaghtighNumber 31 := by
  refine ⟨2, 5, 5, 3, ?_⟩
  norm_num [repunit]

/-- The number $8191$ is a repunit in bases $2$ and $90$. -/
@[category test, AMS 11]
theorem isGoormaghtighNumber_8191 : IsGoormaghtighNumber 8191 := by
  refine ⟨2, 90, 13, 3, ?_⟩
  norm_num [repunit]

/-- Allowing two-digit repunits would make $13$ a representation in two distinct bases. -/
@[category test, AMS 11]
theorem repunit_two_digits : repunit 3 3 = 13 ∧ repunit 12 2 = 13 := by
  norm_num [repunit]

abbrev Target : Prop :=
    ∀ (N : ℕ) (hN : IsGoormaghtighNumber N),
      N = 31 ∨ N = 8191

end Problem
