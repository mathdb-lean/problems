/-
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
A Justin Sun Prize statement on MathDB (statement 0e78c334-6aab-47a8-9051-d04ababeaeef).
MathDB's stored copy imports `MathDBUtil`, MathDB's one-line alias for
`FormalConjecturesUtil`; this copy imports `FormalConjecturesUtil` directly. Its
declarations are MathDB's stored statement unchanged.
-/
namespace Problem
universe u
noncomputable section
/-- The plane Jacobian conjecture: every polynomial map `F = (p, q) : K² → K²` over a
characteristic-zero field whose Jacobian determinant is a nonzero constant has a two-sided
polynomial inverse. -/
abbrev Target : Prop := ∀ (K : Type u) [Field K] [CharZero K]
  (F : Fin 2 → MvPolynomial (Fin 2) K),
    (∃ c : K, c ≠ 0 ∧ Matrix.det (fun i j => MvPolynomial.pderiv j (F i)) = MvPolynomial.C c) →
    ∃ G : Fin 2 → MvPolynomial (Fin 2) K,
      (∀ i, MvPolynomial.bind₁ G (F i) = MvPolynomial.X i) ∧
      (∀ i, MvPolynomial.bind₁ F (G i) = MvPolynomial.X i)
end
end Problem
