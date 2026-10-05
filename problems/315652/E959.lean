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

- problem_id: E959
- collection: erdos
- question_id: erdos:959
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/959.lean#erdos_959
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A\subseteq \mathbb{R}^2$ be a set of size $n$ and let $\{d_1,\ldots,d_k\}$ be the set of distinct distances determined by $A$. Let $f(d)$ be the number of times the distance $d$ is determined, ordered so that $f(d_1)\geq f(d_2)\geq \cdots \geq f(d_k)$. Estimate $$\max (f(d_1)-f(d_2)),$$ where the maximum is taken over all $A$ of size $n$ (this is `extremalGap n`).
- notes: Erdos Problem 959 -- https://www.erdosproblems.com/959
- track: open
- answer_shape: value
- answer_type: ℕ → ℝ
- answer_pinned: false
- answer_pinned_reason: relation_is_reflexive
- source_stem: 959
- mathdb_ref: erdos:959
- source_namespace: Erdos959
- source_theorem: erdos_959
- source_category: research open
- source_ams: 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open EuclideanGeometry Filter

noncomputable section

/-- The unordered index pairs, represented uniquely by the orientation `i < j`. -/
def indexPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  (Finset.univ ×ˢ Finset.univ).filter fun ij => ij.1 < ij.2

/-- The finite set of distinct distances determined by a configuration. -/
def distanceValues {n : ℕ} (P : Fin n → ℝ²) : Finset ℝ :=
  (indexPairs n).image fun ij => dist (P ij.1) (P ij.2)

/-- $f(d)$: the number of unordered pairs in $P$ determining distance $d$. -/
def frequency {n : ℕ} (P : Fin n → ℝ²) (d : ℝ) : ℕ :=
  ((indexPairs n).filter fun ij => dist (P ij.1) (P ij.2) = d).card

/-- For a fixed distance $d$, the largest multiplicity among all *other*
represented distances (`Finset.sup` returns $0$ when there is no other value). -/
def runnerUpFrequency {n : ℕ} (P : Fin n → ℝ²) (d : ℝ) : ℕ :=
  ((distanceValues P).erase d).sup (frequency P)

/-- $f(d_1) - f(d_2)$: the gap between the largest and second-largest distance
multiplicities. The supremum over $d$ handles both a unique winner and a tie:
non-winners contribute $0$ by truncated subtraction, and tied winners also
contribute $0$. -/
def multiplicityGap {n : ℕ} (P : Fin n → ℝ²) : ℕ :=
  (distanceValues P).sup fun d => frequency P d - runnerUpFrequency P d

/-- A configuration represents a set of size $n$ (injective) and has at least
two distinct distances, so that $d_2$ exists. -/
def Admissible {n : ℕ} (P : Fin n → ℝ²) : Prop :=
  Function.Injective P ∧ 2 ≤ (distanceValues P).card

/-- A natural number occurs as the top-two multiplicity gap of some admissible
$n$-point configuration. -/
def AttainableGap (n g : ℕ) : Prop :=
  ∃ P : Fin n → ℝ², Admissible P ∧ multiplicityGap P = g

/-- The extremal quantity of the problem, $\max_{|A| = n} (f(d_1) - f(d_2))$. There
are `Nat.choose n 2` unordered pairs, so this is a valid finite search interval. -/
def extremalGap (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (AttainableGap n) (Nat.choose n 2)

end

abbrev Target (value : ℕ → ℝ) : Prop :=
    (fun n ↦ (extremalGap n : ℝ)) =Θ[atTop] value

end Problem
