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

- problem_id: E692_parts_i
- collection: erdos
- question_id: erdos:692
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/692.lean#erdos_692.parts.i
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $\delta_1(n,m)$ be the density of the set of integers with exactly one divisor in $(n,m)$. Is $\delta_1(n,m)$ unimodular for $m>n+1$ (i.e. increases until some $m$ then decreases thereafter)? Cambie has calculated that unimodularity fails even for $n=2$ and $n=3$. This was formalized in Lean by Monticone using Aristotle.
- notes: Erdos Problem 692 -- https://www.erdosproblems.com/692
- track: solved
- answer_shape: decide
- source_stem: 692
- mathdb_ref: erdos:692
- source_namespace: Erdos692
- source_theorem: erdos_692.parts.i
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

open Filter

/--
The set of integers with exactly one divisor in the open interval $(n, m)$.
-/
def exactlyOneDivisorIn (n m : ℕ) : Set ℕ :=
  {x | {d ∈ Set.Ioo n m | d ∣ x}.ncard = 1}

/--
$\delta_1(n,m)$ is the density of the set of integers with exactly one divisor in $(n,m)$.
-/
def IsDelta₁ (n m : ℕ) (δ : ℝ) : Prop :=
  (exactlyOneDivisorIn n m).HasDensity δ

/--
The set of local maxima of the sequence `f` on `(a, ∞)`. Each local maximum is recorded by the
first index `m` of a maximal interval `[m, b]` on which `f` is constant, with `f` strictly smaller
at `m - 1` and at `b + 1`.
-/
def localMaxima (f : ℕ → ℝ) (a : ℕ) : Set ℕ :=
  {m | a < m ∧ f (m - 1) < f m ∧ ∃ b, m ≤ b ∧ (∀ j ∈ Set.Icc m b, f j = f m) ∧ f (b + 1) < f m}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ δ : ℕ → ℕ → ℝ, (∀ a b, IsDelta₁ a b (δ a b)) → ∀ n, UnimodularOn (δ n) (n + 1)

end Problem
