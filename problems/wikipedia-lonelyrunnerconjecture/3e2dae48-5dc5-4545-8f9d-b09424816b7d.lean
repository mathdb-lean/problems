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

- problem_id: NLonelyRunnerConjecture_lonely_runner_conjecture
- collection: wikipedia
- question_id: wikipedia:LonelyRunnerConjecture
- source: formal-conjectures
- source_locator: FormalConjectures/Wikipedia/LonelyRunnerConjecture.lean#lonely_runner_conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Consider $n$ runners on a circular track of unit length. At the initial time $t = 0$, all runners are at the same position and start to run; the runners' speeds are constant, all distinct, and may be negative. A runner is said to be lonely at time $t$ if they are at a distance (measured along the circle) of at least $\frac 1 n$ from every other runner. The lonely runner conjecture states that each runner is lonely at some time, no matter the choice of speeds.
- notes: Wikipedia: LonelyRunnerConjecture -- https://en.wikipedia.org/wiki/Lonely_runner_conjecture
- track: open
- answer_shape: proof
- source_stem: LonelyRunnerConjecture
- source_namespace: LonelyRunnerConjecture
- source_theorem: lonely_runner_conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-
## Variant: Tao (2017)
-/

/--
For an $n$-tuple of distinct integer velocities $v_1,\dots,v_n$,
`deltaTuple v` is the maximal value of $\min_i \|t v_i\|_{\mathbb{R}/\mathbb{Z}}$ over time.
-/
noncomputable def deltaTuple {n : ℕ} (v : Fin n → ℤ) : ℝ :=
  sSup { δ : ℝ | ∃ t : AddCircle (1 : ℝ), ∀ i : Fin n, δ ≤ dist (v i • t : AddCircle (1 : ℝ)) 0 }

/--
The $n$th *gap of loneliness* $\delta_n$: the infimum of `deltaTuple`
over all $n$-tuples of distinct nonzero integer velocities.
-/
noncomputable def deltaGap (n : ℕ) : ℝ :=
  sInf { d : ℝ | ∃ v : Fin n ↪ ℤ, (∀ i : Fin n, v i ≠ 0) ∧ d = deltaTuple v }

abbrev Target : Prop :=
    ∀ (n : ℕ)
        (speed : Fin n ↪ ℝ) (lonely : Fin n → ℝ → Prop)
        (lonely_def :
          ∀ r t, lonely r t ↔
            ∀ r2 : Fin n, r2 ≠ r →
            dist (t * speed r : UnitAddCircle) (t * speed r2) ≥ 1 / n)
        (r : Fin n),
      ∃ t ≥ 0, lonely r t

end Problem
