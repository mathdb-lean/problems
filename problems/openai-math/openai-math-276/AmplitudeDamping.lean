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

- problem_id: AmplitudeDamping
- collection: openai-math
- question_id: openai-math:276
- source: openai-math
- source_locator: lean/ComparatorChallenges/AmplitudeDamping.lean#OAI.GAD.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Determines the unassisted classical capacity of every qubit generalized amplitude-damping channel, including all damping and thermal parameters. An explicit one-variable optimization gives the capacity, attained by independent two-state signal ensembles with collective decoding. Holevo capacity, minimum output entropy and regularized classical capacity are additive when tensoring with any finite-dimensional quantum channel. ([Lean](lean/docs/276.md)) We determine the unassisted classical capacity of every qubit generalized amplitude-damping channel, for all damping strengths and thermal occupations. It equals the one-shot Holevo capacity and is given by a one-variable maximum. A binary pure-state ensemble attains the one-use optimum, and its independent products attain the optimum at every block length. We also prove that one-shot Holevo capacity, minimum output entropy, and regularized unassisted classical capacity are additive under tensor product with every finite-dimensional completely positive trace-preserving partner channel.
- notes: OpenAI math result family 276, Classical capacity of generalized amplitude damping -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/276.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.GAD.main
- source_theorem_count: 1
- source_solution_module: OAI.InformationTheory.AmplitudeDamping.Main
- source_main_result: OAI.GAD.main
- source_papers: preprints/Classical-capacity-and-entropy-inequalities-for-generalized-amplitude-damping-September-24-2026/paper.pdf
- source_scope_note: lean/docs/276.md
- source_field: InformationTheory
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

universe u

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix Filter

namespace GAD

abbrev Basis (n : ℕ) := Fin n → Fin 2
abbrev QMatrix (n : ℕ) := Matrix (Basis n) (Basis n) ℂ

/-- The spectral definition of -Tr(P log P), with 0 log 0 = 0. -/
def entropy {ι : Type u} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℂ) : ℝ :=
  (Matrix.trace (cfc Real.negMulLog P)).re

def IsState {ι : Type u} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℂ) : Prop :=
  P.PosSemidef ∧ Matrix.trace P = 1


def kraus (γ ν : ℝ) (r : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  if r = 0 then
    !![(Real.sqrt (1 - ν) : ℂ), 0;
       0, (Real.sqrt (1 - ν) * Real.sqrt (1 - γ) : ℂ)]
  else if r = 1 then
    !![0, (Real.sqrt (γ * (1 - ν)) : ℂ); 0, 0]
  else if r = 2 then
    !![(Real.sqrt ν * Real.sqrt (1 - γ) : ℂ), 0; 0, (Real.sqrt ν : ℂ)]
  else
    !![0, 0; (Real.sqrt (γ * ν) : ℂ), 0]

/-- Tensor products of the single-site Kraus operators, with the full Kraus index. -/
def tensorKraus (γ ν : ℝ) (n : ℕ) (r : Fin n → Fin 4) : QMatrix n :=
  fun i j ↦ ∏ k, kraus γ ν (r k) (i k) (j k)

/-- The memoryless n-fold generalized amplitude-damping channel. -/
def channel (γ ν : ℝ) (n : ℕ) (P : QMatrix n) : QMatrix n :=
  ∑ r : Fin n → Fin 4,
    tensorKraus γ ν n r * P * (tensorKraus γ ν n r).conjTranspose

/-- All finite ensembles, without any product or purity restriction. -/
structure Ensemble (n : ℕ) where
  size : ℕ
  weight : Fin size → ℝ
  weight_nonneg : ∀ a, 0 ≤ weight a
  weight_sum : ∑ a, weight a = 1
  signal : Fin size → QMatrix n
  signal_state : ∀ a, IsState (signal a)

def ensembleValue (γ ν : ℝ) {n : ℕ} (E : Ensemble n) : ℝ :=
  (entropy (∑ a, (E.weight a : ℂ) • channel γ ν n (E.signal a)) -
    ∑ a, E.weight a * entropy (channel γ ν n (E.signal a))) / Real.log 2


def holevo (γ ν : ℝ) (n : ℕ) : ℝ :=
  sSup (Set.range (ensembleValue γ ν : Ensemble n → ℝ))

/-- An unrestricted n-use quantum code with one collective output POVM. -/
structure Code (n : ℕ) where
  messages : ℕ
  messages_pos : 0 < messages
  encoding : Fin messages → QMatrix n
  encoding_state : ∀ a, IsState (encoding a)
  decoding : Fin messages → QMatrix n
  decoding_pos : ∀ a, (decoding a).PosSemidef
  decoding_sum : ∑ a, decoding a = 1

def averageError (γ ν : ℝ) {n : ℕ} (C : Code n) : ℝ :=
  1 - (∑ a, (Matrix.trace (C.decoding a * channel γ ν n (C.encoding a))).re) /
    (C.messages : ℝ)

/-- The liminf rate condition written as its eventual lower-bound characterization.
There is no preshared entanglement, feedback, or restriction on encodings/decoding. -/
def Achievable (γ ν R : ℝ) : Prop :=
  ∃ C : (n : ℕ) → Code n,
    Tendsto (fun n ↦ averageError γ ν (C n)) atTop (nhds 0) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      R - ε ≤ Real.log ((C n).messages : ℝ) / Real.log 2 / (n : ℝ)

/-- Operational unassisted classical capacity, not a definition by regularization. -/
def capacity (γ ν : ℝ) : ℝ := sSup {R : ℝ | Achievable γ ν R}

def g (u : ℝ) : ℝ := Real.binEntropy ((1 + Real.sqrt (1 - 4 * u)) / 2)

def v (γ ν p : ℝ) : ℝ := γ * ν * (1 - ν) + γ * (1 - γ) * (p - ν) ^ 2

def objective (γ ν p : ℝ) : ℝ :=
  Real.binEntropy ((1 - γ) * p + γ * ν) - g (v γ ν p)

def Maximizes (γ ν p : ℝ) : Prop :=
  p ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ q ∈ Set.Icc (0 : ℝ) 1, objective γ ν q ≤ objective γ ν p


def phaseSignal (p : ℝ) (s b : Fin 2) : ℂ :=
  if b = 0 then (Real.sqrt (1 - p) : ℂ)
  else if s = 0 then (Real.sqrt p : ℂ) else -(Real.sqrt p : ℂ)

def phaseProduct (p : ℝ) {n : ℕ} (s : Basis n) (i : Basis n) : ℂ :=
  ∏ k, phaseSignal p (s k) (i k)

def phaseState (p : ℝ) {n : ℕ} (s : Basis n) : QMatrix n :=
  fun i j ↦ phaseProduct p s i * star (phaseProduct p s j)

/-- Holevo value of the explicit 2^n equiprobable product signals. -/
def phaseValue (γ ν p : ℝ) (n : ℕ) : ℝ :=
  (entropy (∑ s : Basis n, (((2 : ℝ) ^ n)⁻¹ : ℂ) • channel γ ν n (phaseState p s)) -
    ∑ s : Basis n, ((2 : ℝ) ^ n)⁻¹ * entropy (channel γ ν n (phaseState p s))) /
    Real.log 2

def main_statement : Prop :=
  ∀ (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (hν : ν ∈ Set.Icc (0 : ℝ) 1),
    (∀ n : ℕ, 1 ≤ n → holevo γ ν n = (n : ℝ) * holevo γ ν 1) ∧
    (∃ p : ℝ, Maximizes γ ν p ∧
      ∀ n : ℕ, 1 ≤ n → holevo γ ν n = (n : ℝ) / Real.log 2 * objective γ ν p) ∧
    capacity γ ν = holevo γ ν 1 ∧
    (∀ p : ℝ, Maximizes γ ν p → ∀ n : ℕ, 1 ≤ n →
      (∀ s : Basis n, IsState (phaseState p s)) ∧
      holevo γ ν n = phaseValue γ ν p n)

end GAD
end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.GAD.main_statement

end Problem

/- Formalization scope, from lean/docs/276.md: The formalized result determines the unassisted classical capacity of every generalized amplitude-damping channel with parameters in $[0,1]^2$. Its unrestricted Holevo information is additive across every number of repeated uses, equals an attained scalar maximum, and agrees with the operational capacity per use. Every maximizing equiprobable phase-pair product ensemble attains the corresponding block value. Additivity with an arbitrary different partner channel and decoding by separate measurements are not included. -/
