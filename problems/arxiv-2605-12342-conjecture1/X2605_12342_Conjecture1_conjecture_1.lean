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

- problem_id: X2605_12342_Conjecture1_conjecture_1
- collection: arxiv
- question_id: arxiv:2605.12342/Conjecture1
- source: formal-conjectures
- source_locator: FormalConjectures/Arxiv/2605.12342/Conjecture1.lean#conjecture_1
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **Conjecture 1 (Fernandes, 2026):** Let $m \ge n \ge 2$ be integers with $(m, n) \notin \{(2,2), (3,3), (4,3), (4,4)\}$. Then the group $$ \Gamma_{m \oplus n} = \{(\sigma_1, \sigma_2) \in \mathrm{S}_m \times \mathrm{S}_n : \mathrm{sgn}(\sigma_1) = \mathrm{sgn}(\sigma_2)\} $$ has rank $2$, i.e., minimal generating set of size $2$. Note: Fernandes states the conjecture for groups of exact rank $2$, which is why $(2,2)$ is in the exception list: $\Gamma_{2 \oplus 2} \cong C_2$ has rank $1$. The formalised conclusion `∃ g₁ g₂, closure {g₁, g₂} = ⊤` encodes 2-generation (at most $2$ generators), which $\Gamma_{2 \oplus 2}$ also satisfies. The other three exceptions $(3,3), (4,3), (4,4)$ have rank $3$ and are genuinely not 2-generated. The proof was developed and formalized by Kenta Kitamura, see [K26] for more details.
- notes: arXiv 2605.12342/Conjecture1 -- https://arxiv.org/abs/2605.12342
- track: solved
- answer_shape: proof
- source_stem: 2605.12342/Conjecture1
- source_namespace: Arxiv.«2605.12342»
- source_theorem: conjecture_1
- source_category: research solved
- source_ams: 20
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Equiv.Perm

/--
The group homomorphism $(\sigma_1, \sigma_2) \mapsto \mathrm{sgn}(\sigma_1) \cdot \mathrm{sgn}(\sigma_2)^{-1}$
from $\mathrm{S}_m \times \mathrm{S}_n$ to $\{+1, -1\}$.

Its kernel is exactly $\Gamma_{m \oplus n}$.
-/
noncomputable def signDiffHom (m n : ℕ) : Equiv.Perm (Fin m) × Equiv.Perm (Fin n) →* ℤˣ :=
  (sign.comp (MonoidHom.fst _ _)) * (sign.comp (MonoidHom.snd _ _))⁻¹

/--
The subgroup $\Gamma_{m \oplus n} \le \mathrm{S}_m \times \mathrm{S}_n$ consisting of all pairs
$(\sigma_1, \sigma_2)$ of permutations with equal signature, i.e.
$\mathrm{sgn}(\sigma_1) = \mathrm{sgn}(\sigma_2)$.

This is the kernel of the sign-difference homomorphism
$(\sigma_1, \sigma_2) \mapsto \mathrm{sgn}(\sigma_1) \cdot \mathrm{sgn}(\sigma_2)^{-1}$,
and is an index-$2$ subgroup of $\mathrm{S}_m \times \mathrm{S}_n$.
-/
noncomputable def gammaSubgroup (m n : ℕ) : Subgroup (Equiv.Perm (Fin m) × Equiv.Perm (Fin n)) :=
  (signDiffHom m n).ker

abbrev Target : Prop :=
    ∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m)
        (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))),
      ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤

end Problem
