import Mathlib
/-
Copyright 2026 OpenAI. Licensed under the Apache License, Version 2.0.
Copyright 2026 The mathdb-lean Authors.

The definitions and the statements below are OpenAI's, from
github.com/openai/math at the revision named in the metadata block; see NOTICE.
What this library changed: each `sorry`-bodied theorem became the definition of
the proposition it stated, and `Problem.Target` conjoins those propositions.

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

/-!
Converted from github.com/openai/math. `source_locator` names the comparator
challenge this came from and `source_solution_module` the module there that
proves it; both are at `source_version`. The definitions are the challenge's
own; each sorried theorem became `<name>_statement`, and `Problem.Target`
below conjoins them. `track` is solved because comparator accepted OpenAI's
proof against this very statement. Whether the statement says what the paper's
title says is what the scope note, carried as a caveat, is about.

- problem_id: MatchingPSD
- collection: openai-math
- question_id: openai-math:126
- source: openai-math
- source_locator: lean/ComparatorChallenges/MatchingPSD.lean#OAI.PerfectMatchingPSD.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves that every exact semidefinite lift of the perfect matching polytope has exponential size, answering Rothvoss's polynomial-size lift question negatively. The bound holds even for the positive semidefinite rank of its odd-cut slack matrix after any fixed shift $`0\lt \rho\lt 1`$, allowing arbitrary real positive semidefinite factors. ([Lean](lean/docs/126.md)) For every fixed $`0\lt \rho\lt 1`$, the matrix indexed by odd vertex sets U and perfect matchings M of Kn, with entries $`|M\cap\delta(U)|-1+\rho`$, has real positive semidefinite rank $`2^{\Omega(n)}`$ as even n tends to infinity. Here $`\delta(U)`$ is the edge cut of U. Consequently, every exact semidefinite lift of the perfect matching polytope has exponential size.
- notes: OpenAI math result family 126, Exponential semidefinite complexity of perfect matching -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/126.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.PerfectMatchingPSD.main
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.MatchingPSD.Main
- source_papers: preprints/Exponential-PSD-rank-of-positively-shifted-matching-matrices-October-5-2026/shifted-matching-psd.pdf
- source_scope_note: lean/docs/126.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace PerfectMatchingPSD

abbrev Edge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

def IsPerfectMatching {n : ℕ} (M : Finset (Edge n)) : Prop :=
  ∀ v : Fin n, (M.filter fun e => e.1.1 = v ∨ e.1.2 = v).card = 1

abbrev PerfectMatching (n : ℕ) :=
  {M : Finset (Edge n) // IsPerfectMatching M}

abbrev OddCut (n : ℕ) := {U : Finset (Fin n) // Odd U.card}

abbrev Row (n : ℕ) := Edge n ⊕ OddCut n

def Crosses {n : ℕ} (U : Finset (Fin n)) (e : Edge n) : Prop :=
  (e.1.1 ∈ U ∧ e.1.2 ∉ U) ∨ (e.1.1 ∉ U ∧ e.1.2 ∈ U)

noncomputable def crossingCount {n : ℕ} (U : Finset (Fin n))
    (M : PerfectMatching n) : ℕ := by
  classical
  exact (M.1.filter (Crosses U)).card

noncomputable def slack {n : ℕ} (i : Row n) (M : PerfectMatching n) : ℝ := by
  classical
  exact match i with
  | Sum.inl e => if e ∈ M.1 then 1 else 0
  | Sum.inr U => (crossingCount U.1 M : ℝ) - 1

/-- Real PSD factors of order `r`, without equivariance or rank-one restrictions. -/
def HasFactorization (n r : ℕ) : Prop :=
  ∃ (A : Row n → Matrix (Fin r) (Fin r) ℝ)
    (B : PerfectMatching n → Matrix (Fin r) (Fin r) ℝ),
    (∀ i, (A i).PosSemidef) ∧ (∀ M, (B M).PosSemidef) ∧
    ∀ i M, slack i M = Matrix.trace (A i * B M)

/-- The least positive order of a real PSD factorization. -/
noncomputable def psdRank (n : ℕ) : ℕ :=
  sInf {r : ℕ | 0 < r ∧ HasFactorization n r}

/-- Every positive real power is eventually smaller than the PSD rank,
uniformly over all even vertex counts. The exponentiation is real `rpow`. -/
def MainClaim : Prop :=
  ∀ C : ℝ, 0 < C → ∃ n₀ : ℕ, 4 ≤ n₀ ∧
    ∀ n : ℕ, n₀ ≤ n → Even n → (n : ℝ) ^ C < (psdRank n : ℝ)

def main_statement : Prop :=
  MainClaim

end PerfectMatchingPSD

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.PerfectMatchingPSD.main_statement

end Problem

/- Formalization scope, from lean/docs/126.md: The paper proves exponential PSD-rank lower bounds for positively shifted matching matrices. The linked formalization records the related superpolynomial lower bounds: for every fixed $C>0$, the PSD rank of the selected perfect-matching slack matrix exceeds $n^C$ for all sufficiently large even $n$. Every exact affine semidefinite lift of the perfect-matching polytope likewise requires matrix size greater than $n^C$. These selected statements give superpolynomial growth. They do not state the paper's exponential bound for every fixed positive shift. -/
