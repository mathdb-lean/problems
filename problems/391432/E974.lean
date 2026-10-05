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

- problem_id: E974
- collection: erdos
- question_id: erdos:974
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/974.lean#erdos_974
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $z_1,\ldots,z_n\in \mathbb{C}$ be a sequence such that $z_1=1$. Suppose that the sequence of $$s_k=\sum_{1\leq i\leq n}z_i^k$$ contains infinitely many $(n-1)$-tuples of consecutive values of $s_k$ which are all $0$. Then (essentially) $$z_j=e(j/n),$$ where $e(x)=e^{2\pi ix}$. A conjecture of Turán. This is true (in the stronger form with only two such tuples) - in fact if $n$ is odd then the $z_i$ must be exactly the $n$th roots of unity, and if $n$ is even they must be the vertices of two regular $(n/2)$-gons with the same circumscribed circle centred at the origin. This was first proved by Tijdeman [Ti66]. An independent proof of this was given in the comments section by Hu, Tang, and Zhang.
- notes: Erdos Problem 974 -- https://www.erdosproblems.com/974
- track: solved
- answer_shape: proof
- source_stem: 974
- mathdb_ref: erdos:974
- source_namespace: Erdos974
- source_theorem: erdos_974
- source_category: research solved
- source_ams: 11 30
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/--
The configuration described by Tijdeman: if `n` is odd then the `z i` are exactly the `n`th roots
of unity, and if `n` is even then they are the vertices of two regular `(n / 2)`-gons with the
same circumscribed circle centred at the origin, that is, the `(n / 2)`th roots of `1` together
with the `(n / 2)`th roots of some other point `c` on the unit circle.
-/
def IsTuranConfiguration {n : ℕ} (z : Fin n → ℂ) : Prop :=
  (Odd n → Set.range z = {ζ : ℂ | ζ ^ n = 1}) ∧
    (Even n → ∃ c : ℂ, ‖c‖ = 1 ∧ c ≠ 1 ∧
      Set.range z = {ζ : ℂ | ζ ^ (n / 2) = 1} ∪ {ζ : ℂ | ζ ^ (n / 2) = c})

abbrev Target : Prop :=
    ∀ {n : ℕ} [NeZero n] (z : Fin n → ℂ) (hz : z 0 = 1)
        (hs : Set.Infinite {k : ℕ | ∀ j < n - 1, ∑ i, z i ^ (k + j) = 0}),
      IsTuranConfiguration z

end Problem
