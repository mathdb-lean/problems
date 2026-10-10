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

- problem_id: KMedianThreshold
- collection: openai-math
- question_id: openai-math:125
- source: openai-math
- source_locator: lean/ComparatorChallenges/KMedianThreshold.lean#OAI.MetricKMedian.threshold
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Gives a deterministic polynomial-time $`(1+2/e+\varepsilon)`$-approximation for finite rational metric k-median with specified candidate facilities, for every fixed ε &gt; 0. Assuming $`P\ne NP`$, the optimal infimum approximation factor is $`1+2/e`$. ([Lean](lean/docs/125.md)) We give an exact-budget recovery algorithm for metric k-median with single-exponential dependence on the number of comparison clusters without accurate, distinct proxies in a supplied anchor solution. On positive integral metrics of polynomially bounded diameter, a sufficiently small total proxy error and logarithmically many such clusters yield a $`(1+2/e+\varepsilon)`$ approximation in polynomial time with arbitrarily high success probability. We also prove bounded-price strictness for one compatible execution of the logarithmic-surplus construction. Together the recovery and payment arguments give a randomized $`(2-\sigma)`$ approximation, for an absolute σ &gt; 0, on arbitrary finite rational metrics, both with high probability and in expectation, while opening at most k facilities on every output. For every fixed ε &gt; 0, we give a deterministic polynomial-time $`(1+2/e+\varepsilon)`$-approximation for finite rational metric k-median with specified candidate facilities, opening at most k facilities. Under $`P\ne NP`$, the infimum approximation factor in this model is therefore $`1+2/e`$.
- notes: OpenAI math result family 125, The metric <i>k</i>-median approximation threshold and recovery -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/125.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.MetricKMedian.threshold
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.KMedian.Threshold
- source_papers: preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf
- source_scope_note: lean/docs/125.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

section
section
namespace MetricKMedian

structure Instance where
  n : ℕ
  distance : Fin n → Fin n → ℚ
  clients : Finset (Fin n)
  facilities : Finset (Fin n)
  k : ℕ
  distance_nonneg : ∀ i j, 0 ≤ distance i j
  distance_eq_zero : ∀ i j, distance i j = 0 ↔ i = j
  distance_symm : ∀ i j, distance i j = distance j i
  distance_triangle : ∀ i j h, distance i h ≤ distance i j + distance j h
  k_pos : 1 ≤ k
  k_le : k ≤ facilities.card

def encodeNat (n : ℕ) : List Bool :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

def encodeRat (q : ℚ) : List Bool :=
  [decide (q.num < 0)] ++ encodeNat q.num.natAbs ++ encodeNat q.den

def encodeInstance (I : Instance) : List Bool :=
  encodeNat I.n ++ encodeNat I.k ++
    List.ofFn (fun i : Fin I.n => decide (i ∈ I.clients)) ++
    List.ofFn (fun i : Fin I.n => decide (i ∈ I.facilities)) ++
    (List.ofFn (fun i : Fin I.n =>
      (List.ofFn (fun j : Fin I.n => encodeRat (I.distance i j))).flatten)).flatten

noncomputable def nearest (I : Instance) (j : Fin I.n) (S : Finset (Fin I.n)) : ℝ :=
  if h : S.Nonempty then
    (S.image (fun i => (I.distance j i : ℝ))).min' (h.image _)
  else 0

noncomputable def cost (I : Instance) (S : Finset (Fin I.n)) : ℝ :=
  ∑ j ∈ I.clients, nearest I j S

def feasibleSets (I : Instance) : Finset (Finset (Fin I.n)) :=
  I.facilities.powerset.filter (fun S => S.Nonempty ∧ S.card ≤ I.k)

noncomputable def optimum (I : Instance) : ℝ :=
  if h : (feasibleSets I).Nonempty then
    ((feasibleSets I).image (cost I)).min' (h.image _)
  else 0

def Correct (epsilon : ℝ) (I : Instance) (output : List Bool) : Prop :=
  ∃ S : Finset (Fin I.n), S ⊆ I.facilities ∧ S.Nonempty ∧ S.card ≤ I.k ∧
    output = List.ofFn (fun i : Fin I.n => decide (i ∈ S)) ∧
    cost I S ≤ (1 + 2 / Real.exp 1 + epsilon) * optimum I

end MetricKMedian
end
end

namespace MetricKMedian
namespace Complexity
/-- Polynomial-time computation with every physical work alphabet finite. -/
def FinitePolyTime {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (f : α → β) : Prop :=
  ∃ p : Turing.TM2ComputableInPolyTime ea eb f,
    ∀ k : p.tm.K, Finite (p.tm.Γ k)

abbrev Word := List Bool
abbrev Language := Set Word

def encodeBit (b : Bool) : Word := [b]

def encodePair (x : Word × Word) : Word :=
  encodeNat x.1.length ++ x.1 ++ x.2

def P : Set Language := {L | ∃ decideL : Word → Bool,
  FinitePolyTime id encodeBit decideL ∧ ∀ x, decideL x = true ↔ x ∈ L}

def NP : Set Language := {L | ∃ (verify : Word × Word → Bool) (p : Polynomial ℕ),
  FinitePolyTime encodePair encodeBit verify ∧
  ∀ x, x ∈ L ↔ ∃ w : Word, w.length ≤ p.eval x.length ∧ verify (x, w) = true}

/-- Separation of deterministic polynomial time from finite-verifier nondeterministic polynomial time. -/
def PNeNP : Prop := P ≠ NP

end Complexity
/-- An actual nonempty feasible facility set, encoded by its membership mask. -/
def FactorCorrect (α : ℝ) (I : Instance) (output : List Bool) : Prop :=
  ∃ S : Finset (Fin I.n), S ⊆ I.facilities ∧ S.Nonempty ∧ S.card ≤ I.k ∧
    output = List.ofFn (fun i : Fin I.n => decide (i ∈ S)) ∧
    cost I S ≤ α * optimum I

/-- Deterministic polynomial-time approximation factors for arbitrary specified clients and facilities. -/
def approximationFactors : Set ℝ := {α | ∃ algorithm : Instance → List Bool,
  Complexity.FinitePolyTime encodeInstance id algorithm ∧
  ∀ I, FactorCorrect α I (algorithm I)}

end MetricKMedian

namespace MetricKMedian
/-- The deterministic approximation threshold is an infimum; its attainment is not asserted. -/
def threshold_statement : Prop :=
  ∀ (h : Complexity.PNeNP),
    sInf approximationFactors=1+2/Real.exp 1
end MetricKMedian

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.MetricKMedian.threshold_statement

end Problem

/- Formalization scope, from lean/docs/125.md: The formalization gives an exact-budget recovery algorithm for metric $k$-median on the stated polynomially bounded integral metrics. Suppose a supplied anchor represents all but logarithmically many comparison clusters by distinct proxies, with total proxy cost at most the comparison cost plus a sufficiently small relative error. The algorithm always opens at most $k$ facilities and, with any requested confidence, attains a $(1+2/e+\varepsilon)$ factor relative to those comparison centers in polynomial time. The linked final approximation result applies to arbitrary finite rational metrics. For one absolute $\sigma>0$, a polynomial-time fair-bit algorithm always returns a feasible solution, has expected cost at most $(2-\sigma)\mathrm{OPT}$, and attains the same factor with arbitrarily high polynomial confidence. The formalization gives, for every fixed $\varepsilon>0$, a deterministic polynomial-time $(1+2/e+\varepsilon)$-approximation for metric $k$-median on finite rational metrics with specified candidate facilities. Every output is a nonempty subset of the candidate facilities and opens at most $k$ of them. Assuming $P\ne NP$, it also proves that the infimum of all polynomial-time approximation factors in this model is exactly $1+2/e$. -/
