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

- problem_id: E347
- collection: erdos
- question_id: erdos:347
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/347.lean#erdos_347
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is there a sequence $A=\{a_1\leq a_2\leq \cdots\}$ of integers with $$\lim \frac{a_{n+1}}{a_n}=2$$ such that $$P(A')= \left\{\sum_{n\in B}n : B\subseteq A'\textrm{ finite }\right\}$$ has density $1$ for every cofinite subsequence $A'$ of $A$? This has been solved in the affirmative by ebarschkis in the comments (based on idea of Tao and van Doorn, also in the comments). This was formalized in Lean by Barschkis using Aristotle.
- notes: Erdos Problem 347 -- https://www.erdosproblems.com/347
- track: solved
- answer_shape: decide
- source_stem: 347
- mathdb_ref: erdos:347
- source_namespace: Erdos347
- source_theorem: erdos_347
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter Set Topology

namespace Problem

/--
The set of subset sums of a set `A ⊆ ℕ`.
-/
local notation "𝓟" A => subsetSums A

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∃ a : ℕ → ℕ, (Monotone a) ∧
      (Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ)) atTop (𝓝 2)) ∧
      (∀ ι : ℕ → ℕ, (range ι)ᶜ.Finite → HasDensity (𝓟 (range (a ∘ ι))) 1)

end Problem
