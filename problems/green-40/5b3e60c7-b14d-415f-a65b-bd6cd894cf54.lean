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

- problem_id: G40_prove
- collection: green
- question_id: green:40
- source: formal-conjectures
- source_locator: FormalConjectures/GreensOpenProblems/40.lean#green_40
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Does $f(r) \to \infty$? [Gr24]
- notes: Green, open problem 40
- track: open
- answer_shape: prove
- pair_id: G40
- pair_role: prove
- source_stem: 40
- source_namespace: Green40
- source_theorem: green_40
- source_category: research open
- source_ams: 5 94
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Topology Fintype
open scoped ENNReal Pointwise

namespace Problem

/-- The Hamming ball of radius $r$ in $\mathbb{F}_2^n$. -/
def hammingBall (n r : ℕ) : Set (𝔽₂ n) :=
  {x | hammingNorm x ≤ r}

/-- $V$ is a covering subspace of $\mathbb{F}_2^n$ by $H(r)$ if $V + H(r) = \mathbb{F}_2^n$. -/
def IsCoveringSubspace (n r : ℕ) (V : Submodule (ZMod 2) (𝔽₂ n)) : Prop :=
  (V : Set (𝔽₂ n)) + hammingBall n r = Set.univ

/-- The minimal covering density over all covering subspaces for a given n and r.
    We compute in `ℝ≥0∞` (ENNReal) to gracefully handle any potential divergence. -/
noncomputable def minDensity (n r : ℕ) : ℝ≥0∞ :=
  ⨅ (V : Submodule (ZMod 2) (𝔽₂ n)) (_ : IsCoveringSubspace n r V),
    (Nat.card V : ℝ≥0∞) * (Nat.card (hammingBall n r) : ℝ≥0∞) / (2 ^ n : ℝ≥0∞)

/--
Let $f(r)$ be the smallest constant such that there exists an infinite sequence of $n$'s together
with subspaces $V_n \leq \mathbb{F}_2^n$ with $V_n + H(r) = \mathbb{F}_2^n$ and
$|V_n| = \left(f(r) + o(1)\right) \frac{2^n}{|H(r)|}$.
-/
noncomputable def f (r : ℕ) : ℝ≥0∞ :=
  liminf (fun n ↦ minDensity n r) atTop

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- Variant with arbitrary subsets
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

def hammingBallFinset (n r : ℕ) : Finset (𝔽₂ n) :=
  Finset.univ.filter (fun x => hammingNorm x ≤ r)

def IsCoveringFinset (n r : ℕ) (V : Finset (𝔽₂ n)) : Prop :=
  V + hammingBallFinset n r = Finset.univ

noncomputable def minDensityFinset (n r : ℕ) : ℝ≥0∞ :=
  ⨅ (V : Finset (𝔽₂ n)) (_ : IsCoveringFinset n r V),
    (V.card : ℝ≥0∞) * (Nat.card (hammingBall n r) : ℝ≥0∞) / (2 ^ n : ℝ≥0∞)

noncomputable def f_tilde (r : ℕ) : ℝ≥0∞ :=
  liminf (fun n ↦ minDensityFinset n r) atTop

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- Variant for all n
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

noncomputable def f_all (r : ℕ) : ℝ≥0∞ :=
  limsup (fun n ↦ minDensity n r) atTop

abbrev Target : Prop :=
    Tendsto f atTop (𝓝 ⊤)

end Problem
