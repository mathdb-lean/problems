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

- problem_id: G42_refute
- collection: green
- question_id: green:42
- source: formal-conjectures
- source_locator: FormalConjectures/GreensOpenProblems/42.lean#green_42
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Can the Cohn-Elkies scheme be used to prove the optimal bound for circle-packings in 2 dimensions?
- notes: Green, open problem 42
- track: open
- answer_shape: refute
- pair_id: G42
- pair_role: refute
- source_stem: 42
- source_namespace: Green42
- source_theorem: green_42
- source_category: research open
- source_ams: 51 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Real Complex MeasureTheory
open scoped EuclideanGeometry FourierTransform

namespace Problem

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasureSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

/-- The real-valued Fourier transform used in the Cohn--Elkies conditions.
For real radial admissible functions, the complex Fourier transform is expected
to be real-valued; we take `.re` to expose the real scalar used in the inequality.

**Convention:** Mathlib's `𝓕 f w` expands to $\int e^{-2\pi i \langle v, w \rangle} f(v) dv$, which
matches [CoEl03]'s $\hat{f}(t) = \int f(x) e^{-2\pi i \langle x, t \rangle} dx$.
-/
noncomputable def fHat (f : V → ℝ) (t : V) : ℝ :=
  (𝓕 (fun x ↦ (f x : ℂ)) t).re

/--
Definition 2.1 from [CoEl03]: A function is admissible if it is continuous and both the function
and its Fourier transform decay sufficiently fast. Continuity is essential: changing `f` at a
single point leaves `fHat f` unchanged, so without it every positive bound would be achievable.
-/
def CohnElkiesAdmissible (f : V → ℝ) : Prop :=
  Continuous f ∧ ∃ C > 0, ∃ δ > 0,
    (∀ x : V, |f x| ≤ C / (1 + ‖x‖) ^ ((Module.finrank ℝ V : ℝ) + δ)) ∧
    (∀ t : V, |fHat f t| ≤ C / (1 + ‖t‖) ^ ((Module.finrank ℝ V : ℝ) + δ))

/--
The structural rules a function must satisfy to successfully pass through
the Cohn-Elkies scheme and generate *some* valid upper bound.
-/
def SatisfiesCohnElkiesScheme (f : V → ℝ) : Prop :=
  CohnElkiesAdmissible f ∧
  (∀ x y : V, ‖x‖ = ‖y‖ → f x = f y) ∧ -- Radial symmetry
  (∀ x : V, 2 ≤ ‖x‖ → f x ≤ 0) ∧       -- Spatial constraint (minimum distance 2)
  (∀ t : V, 0 ≤ fHat f t) ∧            -- Frequency positivity
  (0 < fHat f 0) ∧                     -- Non-zero frequency at the origin
  (0 < f 0)                            -- Positive value at the origin

/--
The statement that there exists a function in dimension `d` satisfying the Cohn-Elkies
scheme which achieves the center density bound `bound`.
-/
def CohnElkiesOptimal (d : ℕ) (bound : ℝ) : Prop :=
  ∃ f : ℝ^d → ℝ,
    SatisfiesCohnElkiesScheme f ∧
    f 0 / fHat f 0 = bound

abbrev Target : Prop :=
    ¬ (
      CohnElkiesOptimal 2 (Real.sqrt 3 / 6)
    )

end Problem
