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

- problem_id: K20_76_prove
- collection: kourovka
- question_id: kourovka:20_76
- source: formal-conjectures
- source_locator: FormalConjectures/Kourovka/20_76.lean#kourovka_20_76
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $G$ be a finite $p$-group and assume that all abelian normal subgroups of $G$ have order at most $p^k$. Is it true that every abelian subgroup of $G$ has order at most $p^{2k}$?
- notes: Kourovka Notebook 20_76
- track: open
- answer_shape: prove
- pair_id: K20_76
- pair_role: prove
- source_stem: 20_76
- source_namespace: Kourovka.«20.76»
- source_theorem: kourovka_20_76
- source_category: research open
- source_ams: 20
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

abbrev Target : Prop :=
    ∀ᵉ (p : ℕ) (hp : p.Prime) (G : Type) (_ : Group G) (hg : IsPGroup p G) (_ : Finite G) (k : ℕ)
        (h : ∀ H: Subgroup G, H.Normal ∧ IsMulCommutative H → Nat.card H ≤ p ^ k),
        (∀ H : Subgroup G, IsMulCommutative H → Nat.card H ≤ p ^ (2 * k))

end Problem
