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

- problem_id: RNLSCritical_NLS_apriori
- collection: paper
- question_id: paper:NLSCritical
- source: formal-conjectures
- source_locator: FormalConjectures/Paper/NLSCritical.lean#NLS_apriori
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: The $L^10_{t,x}$ a priori estimate for local schwartz solutions.
- notes: Problem from NLSCritical -- https://doi.org/10.4007/annals.2008.167.767
- track: solved
- answer_shape: proof
- source_stem: NLSCritical
- source_namespace: NLSCritical
- source_theorem: NLS_apriori
- source_category: research solved
- source_ams: 35
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Set ContDiff EuclideanGeometry Laplacian MeasureTheory

namespace Problem

/--
A smooth solution to the NLS equation on the time interval $[-l, l]$.
We additionally require that $x ↦ u(t,x)$ is Schwartz for all $t$ in the interval.
-/
structure LocalSchwartzSolution (l : ℝ) where
  u : ℝ → ℝ^3 → ℂ
  smooth : ContDiffOn ℝ ∞ (Function.uncurry u) (Icc (-l) l ×ˢ univ)
  schwartz : ∀ t ∈ Icc (-l) l, ∃ f : (SchwartzMap (ℝ^3) ℂ), u t = f
  L10_loc : IntegrableOn (fun t ↦ (∫ x, ‖u t x‖^10)) (Icc (-l) l)
  C0H1 : ∃ v : C(ℝ, ℝ^3 →₂[volume] ℝ^3 →L[ℝ] ℂ), ∀ t ∈ Icc (-l) l, ∀ᵐ x, fderiv ℝ (u t ·) x = v t x
  solution : ∀ t ∈ Icc (-l) l, ∀ x, Complex.I * (deriv (u · x) t) + Δ (u t) x = ‖u t x‖^4 * (u t x)

/--
The Hamiltonian of the energy-critical NLS in $ℝ^3$.
-/
noncomputable def energy (u : ℝ^3 → ℂ) : ℝ :=
  ∫ x, (1 / 2) * ‖fderiv ℝ u x‖^2 + (1 / 6) * ‖u x‖^6

/--
The space-time $L^10$ norm, restricted to the time interval $[-l,l]$.
-/
noncomputable def L10_local (l : ℝ) (u : ℝ → ℝ^3 → ℂ) :=
  ∫ t in Icc (-l) l, (∫ x, ‖u t x‖^10)

abbrev Target : Prop :=
    ∃ f : ℝ → ℝ, ∀ l > 0, ∀ s : LocalSchwartzSolution l,
    L10_local l s.u ≤ f (energy (s.u 0))

end Problem
