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

- problem_id: E1180
- collection: erdos
- question_id: erdos:1180
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1180.lean#erdos_1180
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $\epsilon>0$. Does there exist a constant $C_\epsilon$ such that, for all primes $p$, every residue modulo $p$ is the sum of at most $C_\epsilon$ many elements of $$\{ n^{-1} : 1\leq n\leq p^\epsilon\}$$ where $n^{-1}$ denotes the inverse of $n$ modulo $p$? The original question was answered in the affirmative by Shparlinski [Sh02], who proved that $\ll \epsilon^{-3}$ summands suffice for all sufficiently large primes. This was improved to $\ll \epsilon^{-2}$ by Glibichuk [Gl06]. It is trivial that at least $\gg \epsilon^{-1}$ summands are required, and it may be that $C_\epsilon\leq \epsilon^{-1-o(1)}$ is possible. See also [540](https://www.erdosproblems.com/540).
- notes: Erdos Problem 1180 -- https://www.erdosproblems.com/1180
- track: solved
- answer_shape: decide
- source_stem: 1180
- mathdb_ref: erdos:1180
- source_namespace: Erdos1180
- source_theorem: erdos_1180
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter

namespace Problem

/--
`Represents ε p a s` says that the multiset `s` of denominators `n` with `1 ≤ n ≤ p^ε` and
`n` coprime to `p` has `∑ n⁻¹ = a` in `ZMod p`.
-/
def Represents (ε : ℝ) (p : ℕ) (a : ZMod p) (s : Multiset ℕ) : Prop :=
  (∀ n ∈ s, 1 ≤ n ∧ (n : ℝ) ≤ (p : ℝ) ^ ε ∧ n.Coprime p) ∧
    (s.map fun n : ℕ ↦ (n : ZMod p)⁻¹).sum = a

/--
`C ε` is the least `C` such that, for all primes `p`, every residue modulo `p` is the sum of at
most `C` elements of `{n⁻¹ : 1 ≤ n ≤ p^ε}` (or `0` if no such `C` exists).
-/
noncomputable def C (ε : ℝ) : ℕ :=
  sInf {C | ∀ p : ℕ, p.Prime → ∀ a : ZMod p, ∃ s : Multiset ℕ, s.card ≤ C ∧ Represents ε p a s}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℕ, ∀ p : ℕ, p.Prime → ∀ a : ZMod p,
        ∃ s : Multiset ℕ, s.card ≤ C ∧ Represents ε p a s

end Problem
