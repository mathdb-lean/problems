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

- problem_id: G39_prove
- collection: green
- question_id: green:39
- source: formal-conjectures
- source_locator: FormalConjectures/GreensOpenProblems/39.lean#green_39
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If $A \subset \mathbb{Z}/p\mathbb{Z}$ is random, $|A| = \sqrt{p}$, can we almost surely cover $\mathbb{Z}/p\mathbb{Z}$ with $100\sqrt{p}$ translates of $A$? [Gr24]
- notes: Green, open problem 39 -- https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.39
- track: open
- answer_shape: prove
- pair_id: G39
- pair_role: prove
- source_stem: 39
- source_namespace: Green39
- source_theorem: green_39
- source_category: research open
- source_ams: 5 60
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: proportionCoverable_p_p_1 proportionCoverable_t_0 proportionCoverable_2_1_2 proportionCoverable_3_1_2 proportionCoverable_a_gt_p proportionCoverable_7_4_2
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Topology
open scoped Pointwise

namespace Problem

/--
The proportion of subsets of $\mathbb{Z}/p\mathbb{Z}$ of size $k$ that can cover
$\mathbb{Z}/p\mathbb{Z}$ using at most $c$ translates.

If p = 0 or k > p, return 0 by convention.
-/
def proportionCoverable (p k c : ℕ) : ℚ :=
  if h : p = 0 then 0
  else if k > p then 0
  else
    have : NeZero p := ⟨h⟩
    let S : Finset (Finset (ZMod p)) := Finset.powersetCard k Finset.univ
    let coverable := S.filter (fun A => ∃ T : Finset (ZMod p), T.card ≤ c ∧ A + T = Finset.univ)
    (coverable.card : ℚ) / (S.card : ℚ)

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 5 60]
theorem proportionCoverable_p_p_1 : proportionCoverable 3 3 1 = 1 := by decide +kernel

@[category test, AMS 5 60]
theorem proportionCoverable_t_0 : proportionCoverable 5 2 0 = 0 := by decide +kernel

@[category test, AMS 5 60]
theorem proportionCoverable_2_1_2 : proportionCoverable 2 1 2 = 1 := by decide +kernel

@[category test, AMS 5 60]
theorem proportionCoverable_3_1_2 : proportionCoverable 3 1 2 = 0 := by decide +kernel

@[category test, AMS 5 60]
theorem proportionCoverable_a_gt_p : proportionCoverable 3 4 2 = 0 := by decide +kernel

@[category test, AMS 5 60]
theorem proportionCoverable_7_4_2 :
    proportionCoverable 7 4 2 = (3 : ℚ) / 5 := by
  decide +kernel

abbrev Target : Prop :=
    Tendsto
          (fun p : {q : ℕ // q.Prime} ↦
            let k := Nat.sqrt p
            let c := 100 * k
            (proportionCoverable p k c : ℝ))
          atTop (𝓝 1)

end Problem
