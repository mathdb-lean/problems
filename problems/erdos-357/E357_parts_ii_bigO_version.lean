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

- problem_id: E357_parts_ii_bigO_version
- collection: erdos
- question_id: erdos:357
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/357.lean#erdos_357.parts.ii.bigO_version
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $f(n)$ be the maximal $k$ such that there exist integers $1 \le a_1 < \dotsc < a_k \le n$ such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct. How does $f(n)$ grow? Can we find a (good) explicit function $g$ such that $g = O(f)$ ?
- notes: Erdos Problem 357 -- https://www.erdosproblems.com/357
- track: open
- answer_shape: value
- answer_type: ℕ → ℝ
- answer_pinned: false
- answer_pinned_reason: relation_is_reflexive
- source_stem: 357
- mathdb_ref: erdos:357
- source_namespace: Erdos357
- source_theorem: erdos_357.parts.ii.bigO_version
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Filter Asymptotics

def HasDistinctSums {ι α : Type*} [Preorder ι] [AddCommMonoid α] (a : ι → α) : Prop :=
  {J : Finset ι | (J : Set ι).OrdConnected}.InjOn (fun J ↦ ∑ x ∈ J, a x)

/-- Let $f(n)$ be the maximal $k$ such that there exist integers $1 \le a_1 < \dotsc < a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct. -/
noncomputable def f (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ a : Fin k → ℤ, Set.range a ⊆ Set.Icc 1 n ∧ StrictMono a ∧ HasDistinctSums a}

/-- Let $g(n)$ be the maximal $k$ such that there exist integers $1 \le a_1, \dotsc, a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct. -/
noncomputable def g (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ a : Fin k → ℕ, (Set.range a ⊆ Set.Icc 1 n) ∧ HasDistinctSums a}

/-- Let $h(n)$ be the maximal $k$ such that there exist integers $1 \le a_1 \leq \dotsc \leq a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct. -/
noncomputable def h (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ a : Fin k → ℤ, Set.range a ⊆ Set.Icc 1 n ∧ Monotone a ∧ HasDistinctSums a}

abbrev Target (value : ℕ → ℝ) : Prop :=
    value =O[atTop] (fun n ↦ (f n : ℝ))

end Problem

/-
Formalisation note: the next 5 formalisations are an attempt at capturing the question "how does
$f(n)$ grow?". In addition to trivial solutions (e.g. setting `answer(sorry) = 0` in some of these),
it is possible that some of these admit easy solutions that shouldn't count as genuine solutions.
As usual in this repo, solving this problem is not simply providing a term to replace `answer(sorry)`
together with a proof of the theorem, but providing a *mathematically interesting* answer.
Note also that there might be other reasonable (and non equivalent) formal statements that capture this
question.
Similar remarks hold for the `variants.monotone` formalisations later in this file.
-/
