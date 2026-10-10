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

- problem_id: KMedianRecovery
- collection: openai-math
- question_id: openai-math:125
- source: openai-math
- source_locator: lean/ComparatorChallenges/KMedianRecovery.lean#OAI.MetricKMedianRecovery.global_application
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Gives a deterministic polynomial-time $`(1+2/e+\varepsilon)`$-approximation for finite rational metric k-median with specified candidate facilities, for every fixed ε &gt; 0. Assuming $`P\ne NP`$, the optimal infimum approximation factor is $`1+2/e`$. ([Lean](lean/docs/125.md)) We give an exact-budget recovery algorithm for metric k-median with single-exponential dependence on the number of comparison clusters without accurate, distinct proxies in a supplied anchor solution. On positive integral metrics of polynomially bounded diameter, a sufficiently small total proxy error and logarithmically many such clusters yield a $`(1+2/e+\varepsilon)`$ approximation in polynomial time with arbitrarily high success probability. We also prove bounded-price strictness for one compatible execution of the logarithmic-surplus construction. Together the recovery and payment arguments give a randomized $`(2-\sigma)`$ approximation, for an absolute σ &gt; 0, on arbitrary finite rational metrics, both with high probability and in expectation, while opening at most k facilities on every output. For every fixed ε &gt; 0, we give a deterministic polynomial-time $`(1+2/e+\varepsilon)`$-approximation for finite rational metric k-median with specified candidate facilities, opening at most k facilities. Under $`P\ne NP`$, the infimum approximation factor in this model is therefore $`1+2/e`$.
- notes: OpenAI math result family 125, The metric <i>k</i>-median approximation threshold and recovery -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/125.md
- track: solved
- answer_shape: proof
- context_lemmas: comparisonSets_nonempty
- source_theorem: OAI.MetricKMedianRecovery.global_application
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.KMedianRecovery.Main
- source_main_result: OAI.MetricKMedianRecovery.global_application
- source_papers: preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf
- source_scope_note: lean/docs/125.md
- source_field: Combinatorics
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace MetricKMedianRecovery

structure RationalMetricInput where
  pointCount : ℕ
  distance : Fin pointCount → Fin pointCount → ℚ
  clients : Finset (Fin pointCount)
  facilities : Finset (Fin pointCount)
  budget : ℕ
  facilities_nonempty : facilities.Nonempty
  budget_pos : 0 < budget
  covered : clients ∪ facilities = Finset.univ
  distance_nonneg : ∀ x y, 0 ≤ distance x y
  distance_self : ∀ x, distance x x = 0
  distance_symm : ∀ x y, distance x y = distance y x
  distance_triangle : ∀ x y z, distance x z ≤ distance x y + distance y z

namespace RationalMetricInput

def size (I : RationalMetricInput) : ℕ := I.clients.card + I.facilities.card

def Feasible (I : RationalMetricInput) (S : Finset (Fin I.pointCount)) : Prop :=
  S ⊆ I.facilities ∧ S.card ≤ I.budget ∧ (I.clients.Nonempty → S.Nonempty)

def cost (I : RationalMetricInput) (S : Finset (Fin I.pointCount)) : ℚ :=
  if hS : S.Nonempty then ∑ p ∈ I.clients, S.inf' hS (I.distance p) else 0

def comparisonSets (I : RationalMetricInput) : Finset (Finset (Fin I.pointCount)) :=
  I.facilities.powerset.filter (fun S => S.Nonempty ∧ S.card ≤ I.budget)

lemma comparisonSets_nonempty (I : RationalMetricInput) : I.comparisonSets.Nonempty := by
  obtain ⟨i, hi⟩ := I.facilities_nonempty
  refine ⟨{i}, ?_⟩
  simp only [comparisonSets, Finset.mem_filter, Finset.mem_powerset,
    Finset.singleton_subset_iff, Finset.singleton_nonempty, Finset.card_singleton, true_and]
  exact ⟨hi, I.budget_pos⟩

def optimum (I : RationalMetricInput) : ℚ :=
  I.comparisonSets.inf' I.comparisonSets_nonempty I.cost

def natBits (n : ℕ) : List Bool :=
  List.replicate (Nat.bits n).length true ++ [false] ++ Nat.bits n

def rationalBits (r : ℚ) : List Bool :=
  [decide (r < 0)] ++ natBits r.num.natAbs ++ natBits r.den

def bits (I : RationalMetricInput) : List Bool :=
  natBits I.pointCount ++ natBits I.budget ++
    List.ofFn (fun i : Fin I.pointCount => decide (i ∈ I.clients)) ++
    List.ofFn (fun i : Fin I.pointCount => decide (i ∈ I.facilities)) ++
    (List.ofFn (fun i : Fin I.pointCount =>
      (List.ofFn (fun j : Fin I.pointCount => rationalBits (I.distance i j))).flatten)).flatten

def decodeOutput (I : RationalMetricInput) (out : List Bool) : Finset (Fin I.pointCount) :=
  I.facilities.filter (fun i => out[i.val]?.getD false = true)

end RationalMetricInput

def pairBits (p : List Bool × List Bool) : List Bool :=
  p.1.flatMap (fun b => [true, b]) ++ [false] ++ p.2

structure BinaryRandomizedAlgorithm where
  randomBits : Polynomial ℕ
  run : List Bool × List Bool → List Bool
  computation : Turing.TM2ComputableInPolyTime pairBits id run
  finiteWorkAlphabet : ∀ k : computation.tm.K, Finite (computation.tm.Γ k)

namespace BinaryRandomizedAlgorithm

def bitCount (A : BinaryRandomizedAlgorithm) (I : RationalMetricInput) : ℕ :=
  A.randomBits.eval I.bits.length

abbrev Seed (A : BinaryRandomizedAlgorithm) (I : RationalMetricInput) :=
  Fin (A.bitCount I) → Bool

def output (A : BinaryRandomizedAlgorithm) (I : RationalMetricInput) (s : A.Seed I) :
    Finset (Fin I.pointCount) :=
  I.decodeOutput (A.run (I.bits, List.ofFn s))

noncomputable def successProbability (A : BinaryRandomizedAlgorithm) (I : RationalMetricInput)
    (bound : ℝ) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun s : A.Seed I => (I.cost (A.output I s) : ℝ) ≤ bound)).card : ℝ) /
    2 ^ (A.bitCount I)

noncomputable def expectedCost (A : BinaryRandomizedAlgorithm) (I : RationalMetricInput) : ℝ :=
  (∑ s : A.Seed I, (I.cost (A.output I s) : ℝ)) / 2 ^ (A.bitCount I)

end BinaryRandomizedAlgorithm

def globalApplicationClaim : Prop :=
  ∃ σ : ℝ, 0 < σ ∧ ∀ a : ℝ, 0 < a → ∃ A : BinaryRandomizedAlgorithm,
    (∀ (I : RationalMetricInput) (s : A.Seed I), I.Feasible (A.output I s)) ∧
    (∀ I : RationalMetricInput,
      1 - Real.rpow ((I.size : ℝ) + 2) (-a) ≤
        A.successProbability I ((2 - σ) * (I.optimum : ℝ))) ∧
    (∀ I : RationalMetricInput, A.expectedCost I ≤ (2 - σ) * (I.optimum : ℝ))

def global_application_statement : Prop :=
  globalApplicationClaim

end MetricKMedianRecovery

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.MetricKMedianRecovery.global_application_statement

end Problem

/- Formalization scope, from lean/docs/125.md: The formalization gives an exact-budget recovery algorithm for metric $k$-median on the stated polynomially bounded integral metrics. Suppose a supplied anchor represents all but logarithmically many comparison clusters by distinct proxies, with total proxy cost at most the comparison cost plus a sufficiently small relative error. The algorithm always opens at most $k$ facilities and, with any requested confidence, attains a $(1+2/e+\varepsilon)$ factor relative to those comparison centers in polynomial time. The linked final approximation result applies to arbitrary finite rational metrics. For one absolute $\sigma>0$, a polynomial-time fair-bit algorithm always returns a feasible solution, has expected cost at most $(2-\sigma)\mathrm{OPT}$, and attains the same factor with arbitrarily high polynomial confidence. The formalization gives, for every fixed $\varepsilon>0$, a deterministic polynomial-time $(1+2/e+\varepsilon)$-approximation for metric $k$-median on finite rational metrics with specified candidate facilities. Every output is a nonempty subset of the candidate facilities and opens at most $k$ of them. Assuming $P\ne NP$, it also proves that the infimum of all polynomial-time approximation factors in this model is exactly $1+2/e$. -/
