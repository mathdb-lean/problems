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

- problem_id: K1_35c_refute
- collection: kourovka
- question_id: kourovka:1_35c
- source: formal-conjectures
- source_locator: FormalConjectures/Kourovka/1_35c.lean#kourovka_1_35c
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Do there exist simple pro-orderable groups?
- notes: Kourovka Notebook 1_35c
- track: open
- answer_shape: refute
- pair_id: K1_35c
- pair_role: refute
- source_stem: 1_35c
- source_namespace: Kourovka.«1.35c»
- source_theorem: kourovka_1_35c
- source_category: research open
- source_ams: 20
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- A relation on a group is bi-invariant if it is preserved by both left and
right multiplication. -/
def IsBiInvariant (G : Type*) [Group G] (r : G → G → Prop) : Prop :=
  (∀ g a b, r a b → r (g * a) (g * b)) ∧
  (∀ g a b, r a b → r (a * g) (b * g))

/--
`ProOrderable G` means every bi-invariant partial order extends to a
bi-invariant linear order.
-/
def ProOrderable (G : Type*) [Group G] : Prop :=
  ∀ r : G → G → Prop,
    IsPartialOrder G r →
    IsBiInvariant G r →
    ∃ s : G → G → Prop,
      IsLinearOrder G s ∧ IsBiInvariant G s ∧ ∀ x y, r x y → s x y

abbrev Target : Prop :=
    ¬ (
      ∃ (G : Type) (_ : Group G), IsSimpleGroup G ∧ ProOrderable G
    )

end Problem
