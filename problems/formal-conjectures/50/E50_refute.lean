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

- problem_id: E50_refute
- collection: erdos
- question_id: erdos:50
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/50.lean#erdos_50
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $f$ be the asymptotic distribution function of $\varphi(n)/n$, so that for each $c \in [0,1]$, $f(c)$ is the natural density of $\{n : \varphi(n) < cn\}$. Is it true that there is no $x$ such that the derivative $f'(x)$ exists and is positive?
- notes: Erdos Problem 50 -- https://www.erdosproblems.com/50
- track: open
- answer_shape: refute
- pair_id: E50
- pair_role: refute
- source_stem: 50
- mathdb_ref: erdos:50
- source_namespace: Erdos50
- source_theorem: erdos_50
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Set MeasureTheory Topology
open scoped Nat Topology

namespace Problem

/--
A function $f : \mathbb{R} \to \mathbb{R}$ is the asymptotic distribution function of the values
of $\varphi(n)/n$ if for all $c \in [0, 1]$, the natural density of $\{n : \varphi(n) < cn\}$
exists and equals $f(c)$.
-/
def IsDistributionOfPhiRatio (f : ℝ → ℝ) : Prop :=
  ∀ c ∈ Icc (0 : ℝ) 1, {n : ℕ | (φ n : ℝ) < c * n}.HasDensity (f c)

/--
A function $f : \mathbb{R} \to \mathbb{R}$ is purely singular (or singular continuous) on a set
$s \subseteq \mathbb{R}$ if it is continuous on $s$ and its derivative within $s$ equals zero
almost everywhere on $s$ with respect to Lebesgue measure.
-/
def IsPurelySingularOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ContinuousOn f s ∧ ∀ᵐ x ∂(volume.restrict s), derivWithin f s x = 0

abbrev Target : Prop :=
    ¬ (
      ∀ᵉ (f : ℝ → ℝ) (hf : IsDistributionOfPhiRatio f),
          ¬∃ x ∈ Icc (0 : ℝ) 1, ∃ y > 0, HasDerivWithinAt f y (Icc 0 1) x
    )

end Problem
