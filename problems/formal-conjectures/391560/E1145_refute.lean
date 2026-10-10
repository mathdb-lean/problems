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

- problem_id: E1145_refute
- collection: erdos
- question_id: erdos:1145
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1145.lean#erdos_1145
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A=\{1\leq a_1 < a_2 < \cdots\}$ and $B=\{1\leq b_1 < b_2 < \cdots\}$ be sets of integers with $a_n/b_n\to 1$. If $A+B$ contains all sufficiently large positive integers then is it true that $\limsup 1_A\ast 1_B(n)=\infty$? A conjecture of Erdős and Sárközy.
- notes: Erdos Problem 1145 -- https://www.erdosproblems.com/1145
- track: open
- answer_shape: refute
- pair_id: E1145
- pair_role: refute
- source_stem: 1145
- mathdb_ref: erdos:1145
- source_namespace: Erdos1145
- source_theorem: erdos_1145
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Set Filter Pointwise Topology AdditiveCombinatorics

namespace Problem

/--
Let $A=\{1\leq a_1 < a_2 < \cdots\}$ and $B=\{1\leq b_1 < b_2 < \cdots\}$ be sets of integers with
$a_n/b_n\to 1$.

If $A+B$ contains all sufficiently large positive integers then is it true that
$\limsup 1_A\ast 1_B(n)=\infty$?

Formalization note: There's some discussion in the comments of [erdosproblems.com/28] and
[erdosproblems.com/1145] about whether or not $0$ should be included in $A$ or $B$ and has been
left purposely ambiguous. Problem 1145 was originally written as $A + B = \mathbb{N}$, which
would imply that $0$ would need to exist in $A$ or $B$ to include $1$ in $A + B$. However, it's been
made more general and rewritten as "sufficiently large positive integers". The formalization below
is the version that includes $0$.
-/
def Erdos1145Prop : Prop :=
  ∀ ⦃A B : Set ℕ⦄ (_ : A.Infinite) (_ : B.Infinite),
    Tendsto (fun n ↦ (Nat.nth (· ∈ A) n : ℝ) / (Nat.nth (· ∈ B) n : ℝ)) atTop (𝓝 1) →
    (∀ᶠ n in atTop, n ∈ A + B) →
    limsup (fun n => ↑(((𝟙_A ∗ 𝟙_B) : ℕ → ℕ) n)) atTop = (⊤ : ℕ∞)

abbrev Target : Prop :=
    ¬ (
      Erdos1145Prop
    )

end Problem

/-
Let $A=\{1\leq a_1 < a_2 < \cdots\}$ and $B=\{1\leq b_1 < b_2 < \cdots\}$ be sets of integers with
$a_n/b_n\to 1$.

If $A+B$ contains all sufficiently large positive integers then is it true that
$\limsup 1_A\ast 1_B(n)=\infty$?

Formalization note: There's some discussion in the comments of [erdosproblems.com/28] and
[erdosproblems.com/1145] about whether or not $0$ should be included in $A$ or $B$ and has been
left purposely ambiguous. Problem 1145 was originally written as $A + B = \mathbb{N}$, which
would imply that $0$ would need to exist in $A$ or $B$ to include $1$ in $A + B$. However, it's been
made more general and rewritten as "sufficiently large positive integers". The formalization below
is the version that includes $0$.
-/
