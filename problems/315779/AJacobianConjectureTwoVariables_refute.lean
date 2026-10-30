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

import FormalConjecturesUtil

/-!
Stated in this library. The definition follows `JacobianConjectureProp` in
formal-conjectures `FormalConjectures/Wikipedia/JacobianConjecture.lean`
(e04cc601), whose open statement `jacobian_conjecture_two_variables` rebinds
the name `k` of a section `variable`; the converter cannot tell a rebinding
from a dependence and refuses it (`unsupported_section_variable`), so the
question is restated here with `k` bound explicitly. The general conjecture is
tagged solved upstream -- a polynomial self-map of `k³` with constant Jacobian
determinant and no inverse -- and only the two-variable case remains open; that
case is what this file states. `RegularFunction` is the support library's
`MvPolynomial.RegularFunction`: a vector of polynomials, one per output variable.

- problem_id: AJacobianConjectureTwoVariables_refute
- collection: authored
- question_id: authored:JacobianConjectureTwoVariables
- source: mathdb-lean
- source_locator: authored/JacobianConjectureTwoVariables.lean#Target
- prose: Does the Jacobian conjecture hold in two variables? Over every field of characteristic zero, is every polynomial map from the plane to itself whose Jacobian determinant is a nonzero constant a polynomial automorphism, with a polynomial inverse?
- notes: Jacobian conjecture -- https://en.wikipedia.org/wiki/Jacobian_conjecture
- track: open
- answer_shape: refute
- pair_id: AJacobianConjectureTwoVariables
- pair_role: refute
- source_category: research open
- source_ams: 14
- generator: adapters/authored/adapter.py
-/

open MvPolynomial RegularFunction

namespace Problem

/-- The Jacobian conjecture for the ring `k` and the variable index type `σ`: every regular
function `kᵠ → kᵠ` whose Jacobian determinant is a unit has a regular inverse on both sides. -/
def JacobianConjectureProp (k σ : Type) [CommRing k] [Fintype σ] [DecidableEq σ] : Prop :=
  ∀ (F : RegularFunction k σ σ), IsUnit F.Jacobian.det →
    ∃ (G : RegularFunction k σ σ), G.comp F = RegularFunction.id k σ ∧
    F.comp G = RegularFunction.id k σ

/-- The Jacobian conjecture holds in two variables over every field of characteristic zero. -/
abbrev Target : Prop :=
  ¬ (
    ∀ (k : Type) [Field k] [CharZero k], JacobianConjectureProp k (Fin 2)
  )

end Problem

/-!
- source_version: b80da422c1869ddababb2992c7dc83556e0f930c
-/
