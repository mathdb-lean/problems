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

- problem_id: E521
- collection: erdos
- question_id: erdos:521
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/521.lean#erdos_521
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $(\epsilon_k)_{k\geq 0}$ be independently uniformly chosen at random from $\{-1,1\}$. If $R_n$ counts the number of real roots of $f_n(z)=\sum_{0\leq k\leq n}\epsilon_k z^k$ then is it true that, almost surely, $$\lim_{n\to \infty}\frac{R_n}{\log n}=\frac{2}{\pi}?$$ The answer is no: this almost-sure limit fails. This result was obtained first by others, who deserve the credit for the problem; the link is to an independent machine-checked proof by Star Fleet Math.
- notes: Erdos Problem 521 -- https://www.erdosproblems.com/521
- track: solved
- answer_shape: decide
- source_stem: 521
- mathdb_ref: erdos:521
- source_namespace: Erdos521
- source_theorem: erdos_521
- source_category: research solved
- source_ams: 11 60
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: fairCoin_apply fairCoin_isProbabilityMeasure
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

open MeasureTheory Filter Polynomial
open scoped Topology

/-- `true` encodes the sign `+1`, `false` the sign `-1`. -/
def sign (b : Bool) : ℝ := if b then 1 else -1

/-- One fair coin: the uniform probability measure on `Bool`. -/
noncomputable def fairCoin : Measure Bool :=
  (2 : ENNReal)⁻¹ • (Measure.dirac true + Measure.dirac false)

/-- The law of an infinite sequence of independent fair coins `(ε_k)_{k ≥ 0}`,
each uniform on `{-1, +1}`. -/
noncomputable def rademacherMeasure : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ ↦ fairCoin)

/-- The degree-`n` Littlewood polynomial `f_n(z) = ∑_{0 ≤ k ≤ n} ε_k z^k`. -/
noncomputable def littlewoodPolynomial (ω : ℕ → Bool) (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.monomial k (sign (ω k))

/-- `R_n`: the number of distinct real roots of `f_n`. -/
noncomputable def realRootCount (ω : ℕ → Bool) (n : ℕ) : ℕ :=
  Set.ncard ((littlewoodPolynomial ω n).rootSet ℝ)

/-- The assertion asked about in Problem 521: almost surely `R_n / log n → 2/π`. -/
def Claim : Prop :=
  ∀ᵐ ω ∂rademacherMeasure,
    Tendsto (fun n : ℕ ↦ (realRootCount ω n : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 ((2 : ℝ) / Real.pi))

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- `fairCoin` gives each of the two signs mass `1/2`. Together with
`fairCoin_isProbabilityMeasure` this pins the definition down, so a proof stating the
same problem with a `Bernoulli(1/2)` measure is stating the same thing. -/
@[category API, AMS 60]
theorem fairCoin_apply (b : Bool) : fairCoin {b} = 2⁻¹ := by
  cases b <;> simp [fairCoin]

/-- `fairCoin` is a probability measure. -/
@[category API, AMS 60]
theorem fairCoin_isProbabilityMeasure : IsProbabilityMeasure fairCoin := by
  constructor
  simp [fairCoin]
  rw [ENNReal.inv_two_add_inv_two]

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ Claim

end Problem
