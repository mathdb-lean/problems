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

- problem_id: E202
- collection: erdos
- question_id: erdos:202
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/202.lean#erdos_202
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $n_1<\cdots < n_r\leq N$ with associated $a_i\pmod{n_i}$ such that the congruence classes are disjoint (that is, every integer is $\equiv a_i\pmod{n_i}$ for at most one $1\leq i\leq r$). How large can $r$ be in terms of $N$? Let $f(N)$ be the maximum possible $r$, and let $L(N)=\exp(\sqrt{\log N\log\log N})$. This was proved by GPT-5.4 Pro (prompted by Ho Boon Suan), using the argument of [BFV13] together with the resolution of the Kahn-Kalai conjecture by Park and Pham [PaPh24], so that $$f(N)= N L(N)^{-1+o(1)}.$$
- notes: Erdos Problem 202 -- https://www.erdosproblems.com/202
- track: solved
- answer_shape: proof
- source_stem: 202
- mathdb_ref: erdos:202
- source_namespace: Erdos202
- source_theorem: erdos_202
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Real

namespace Problem

/--
`f N` is the maximum possible `r` such that there are moduli $n_1<\cdots<n_r\leq N$ with
associated residues $a_i\pmod{n_i}$ whose congruence classes are disjoint.
-/
noncomputable def f (N : ℕ) : ℕ :=
  sSup {r : ℕ | ∃ n : Fin r → ℕ, ∃ a : Fin r → ℤ,
    StrictMono n ∧ (∀ i, 0 < n i ∧ n i ≤ N) ∧
    ∀ m : ℤ, ∀ i j : Fin r, m ≡ a i [ZMOD (n i : ℤ)] → m ≡ a j [ZMOD (n j : ℤ)] → i = j}

abbrev Target : Prop :=
    ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
        ∀ᶠ N : ℕ in atTop, (f N : ℝ) = (N : ℝ) * scaleL N ^ (-1 + o N)

end Problem
