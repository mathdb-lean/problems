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

- problem_id: E481
- collection: erdos
- question_id: erdos:481
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/481.lean#erdos_481
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $a_1,\ldots,a_r,b_1,\ldots,b_r\in \mathbb{N}$ such that $\sum_{i}\frac{1}{a_i}>1$. For any finite sequence of $n$ (not necessarily distinct) integers $A=(x_1,\ldots,x_n)$ let $T(A)$ denote the sequence of length $rn$ given by $$(a_ix_j+b_i)_{1\leq j\leq n, 1\leq i\leq r}.$$ Prove that, if $A_1=(1)$ and $A_{i+1}=T(A_i)$, then there must be some $A_k$ with repeated elements. This is true. This appears to have first been shown by Klarner [Kl82], with a generalisation given by Kolpakov and Talambutsa [KoTa22]. Essentially the same proof was found independently by Barreto in the comment section.
- notes: Erdos Problem 481 -- https://www.erdosproblems.com/481
- track: solved
- answer_shape: proof
- source_stem: 481
- mathdb_ref: erdos:481
- source_namespace: Erdos481
- source_theorem: erdos_481
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/--
For a finite sequence of $n$ (not necessarily distinct) integers $A = (x_1,\ldots,x_n)$, the
sequence `T a b A` of length $rn$ given by $(a_ix_j+b_i)_{1\leq j\leq n, 1\leq i\leq r}$.
-/
def T {r : ℕ} (a b : Fin r → ℕ) (A : List ℕ) : List ℕ :=
  (List.finRange r).flatMap (fun i : Fin r => A.map (fun x : ℕ => a i * x + b i))

abbrev Target : Prop :=
    ∀ {r : ℕ} (a b : Fin r → ℕ) (ha : ∀ i, 0 < a i)
        (hab : 1 < ∑ i, (1 : ℝ) / a i),
      ∃ k, ¬ ((T a b)^[k] [1]).Nodup

end Problem
