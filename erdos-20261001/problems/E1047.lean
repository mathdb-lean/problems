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

- problem_id: E1047
- collection: erdos
- question_id: erdos:1047
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1047.lean#erdos_1047
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $f\in \mathbb{C}[x]$ be a monic polynomial with $m$ distinct roots, and let $c>0$ be a constant small enough such that $\{ z: \lvert f(z)\rvert\leq c\}$ has $m$ distinct connected components. Must all these components be convex? A question of Grunsky, which was reported by Erdős, Herzog, and Piranian [EHP58]. The answer is no, as shown by Pommerenke [Po61], who showed that, if $k$ is sufficiently large, and $f(z)=z^k(z-a)$ where $a$ is sufficiently close to $(1+\frac{1}{k})k^{\frac{1}{k+1}}$, then $\{ z: \lvert f(z)\rvert\leq 1\}$ has two components, and the component which contains $0$ is not convex. This was formalized in Lean by Alexeev using Aristotle.
- notes: Erdos Problem 1047 -- https://www.erdosproblems.com/1047
- track: solved
- answer_shape: decide
- source_stem: 1047
- mathdb_ref: erdos:1047
- source_namespace: Erdos1047
- source_theorem: erdos_1047
- source_category: research solved
- source_ams: 30 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Polynomial

namespace Problem

/-- The sublevel set $\{ z: \lvert f(z)\rvert\leq c\}$ of a polynomial $f\in\mathbb{C}[x]$. -/
def sublevelSet (f : ℂ[X]) (c : ℝ) : Set ℂ := {z : ℂ | ‖f.eval z‖ ≤ c}

/-- The strict sublevel set $\{ z: \lvert f(z)\rvert< c\}$ of a polynomial $f\in\mathbb{C}[x]$. -/
def strictSublevelSet (f : ℂ[X]) (c : ℝ) : Set ℂ := {z : ℂ | ‖f.eval z‖ < c}

/-- The connected components of a set `s ⊆ ℂ`, viewed as subsets of `ℂ`. -/
def componentsIn (s : Set ℂ) : Set (Set ℂ) :=
  {t : Set ℂ | ∃ z ∈ s, t = connectedComponentIn s z}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ (f : ℂ[X]) (m : ℕ) (c : ℝ), f.Monic → (f.rootSet ℂ).ncard = m → 0 < c →
          (componentsIn (sublevelSet f c)).ncard = m →
            ∀ t ∈ componentsIn (sublevelSet f c), Convex ℝ t

end Problem
