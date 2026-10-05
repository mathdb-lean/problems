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

- problem_id: E525_parts_ii
- collection: erdos
- question_id: erdos:525
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/525.lean#erdos_525.parts.ii
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: What is the behaviour of $$m(f)=\min_{\lvert z\rvert=1}\lvert f(z)\rvert?$$ Cook and Nguyen [CoNg21] have identified the limiting distribution, proving that for any $\epsilon>0$ $$\lim_{n\to \infty} \mathbb{P}(m(f) > \epsilon n^{-1/2}) = e^{-\epsilon \lambda}$$ where $\lambda=\sqrt{\pi/12}$.
- notes: Erdos Problem 525 -- https://www.erdosproblems.com/525
- track: solved
- answer_shape: proof
- source_stem: 525
- mathdb_ref: erdos:525
- source_namespace: Erdos525
- source_theorem: erdos_525.parts.ii
- source_category: research solved
- source_ams: 30 60
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Real Finset

namespace Problem

/-- The degree-`n` polynomial $f(z)=\sum_{j\leq n}\epsilon_j z^j$ with coefficients
`ε : Fin (n + 1) → ℤˣ`, i.e. $\epsilon_j\in\{-1,1\}$, evaluated at `z`. -/
def eval {n : ℕ} (ε : Fin (n + 1) → ℤˣ) (z : ℂ) : ℂ :=
  ∑ j, ((ε j : ℤ) : ℂ) * z ^ (j : ℕ)

/-- The degree-`n` polynomials with $\pm 1$ coefficients such that $|f(z)|\geq 1$ for all
$|z|=1$. -/
def exceptional (n : ℕ) : Set (Fin (n + 1) → ℤˣ) :=
  {ε | ∀ z : ℂ, ‖z‖ = 1 → 1 ≤ ‖eval ε z‖}

/-- $m(f)=\min_{|z|=1}|f(z)|$. -/
noncomputable def m {n : ℕ} (ε : Fin (n + 1) → ℤˣ) : ℝ :=
  sInf ((fun z ↦ ‖eval ε z‖) '' Metric.sphere (0 : ℂ) 1)

open scoped Classical in
/-- The probability that a uniformly random degree-`n` polynomial with $\pm 1$ coefficients
satisfies `P`. -/
noncomputable def prob (n : ℕ) (P : (Fin (n + 1) → ℤˣ) → Prop) : ℝ :=
  ((univ.filter P).card : ℝ) / 2 ^ (n + 1)

abbrev Target : Prop :=
    ∀ (ε : ℝ) (hε : 0 < ε),
      Tendsto (fun n : ℕ ↦ prob n fun f ↦ ε / √n < m f) atTop
        (nhds (exp (-√(π / 12) * ε)))

end Problem
