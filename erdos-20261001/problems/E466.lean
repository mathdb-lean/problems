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

- problem_id: E466
- collection: erdos
- question_id: erdos:466
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/466.lean#erdos_466
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $N(X,\delta)$ denote the maximum number of points $P_1,\ldots,P_n$ which can be chosen in a circle of radius $X$ such that $$\| \lvert P_i-P_j\rvert \| \geq \delta$$ for all $1\leq i<j\leq n$. (Here $\|x\|$ is the distance from $x$ to the nearest integer.) Is there some $\delta>0$ such that $$\lim_{X\to \infty}N(X,\delta)=\infty?$$ Graham proved this is true, and in fact $N(X,1/10)> \frac{\log X}{10}$. This was substantially improved by Sárközy [Sa76], who proved that for all sufficiently small $\delta>0$, $N(X,\delta)>X^{1/2-\delta^{1/7}}$.
- notes: Erdos Problem 466 -- https://www.erdosproblems.com/466
- track: solved
- answer_shape: decide
- source_stem: 466
- mathdb_ref: erdos:466
- source_namespace: Erdos466
- source_theorem: erdos_466
- source_category: research solved
- source_ams: 11 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter Metric

namespace Problem

/--
`N X δ` is the maximum number of points in a closed disc of radius `X` in the plane such that
the distance between any two of them is at least `δ` away from the nearest integer.
-/
noncomputable def N (X δ : ℝ) : ℕ :=
  sSup {n | ∃ (c : EuclideanSpace ℝ (Fin 2)) (P : Finset (EuclideanSpace ℝ (Fin 2))),
    P.card = n ∧ ↑P ⊆ closedBall c X ∧
      (P : Set (EuclideanSpace ℝ (Fin 2))).Pairwise fun x y => δ ≤ distToNearestInt (dist x y)}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∃ δ : ℝ, 0 < δ ∧ Tendsto (fun X ↦ N X δ) atTop atTop

end Problem
