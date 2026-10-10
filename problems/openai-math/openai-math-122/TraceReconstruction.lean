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

- problem_id: TraceReconstruction
- collection: openai-math
- question_id: openai-math:122
- source: openai-math
- source_locator: lean/ComparatorChallenges/TraceReconstruction.lean#OAI.TraceReconstruction.quantitative_sample_lower_bound
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: At every fixed deletion probability in $`(0,1)`$, reconstructing an arbitrary length-n binary string requires $`n^{\Omega(\log\log n)}`$ independent traces, ruling out polynomial-sample reconstruction. A uniform decoder achieves quasipolynomial sample and running-time bounds for known fixed rational retention probabilities. When the deletion probability is at most $`n^{-\varepsilon}`$ for fixed ε &gt; 0, both bounds become polynomial in the input and parameter encoding. ([Lean](lean/docs/122.md)) Exact worst-case reconstruction of a binary word from independent deletion traces requires $`n^{\Omega(\log\log n)}`$ samples for every fixed deletion probability $`q\in(0,1)`$, even with unrestricted computation and any fixed positive success probability. This gives a negative answer to the polynomial-sample question for binary trace reconstruction. More generally, when $`q^3\log n\to\infty`$, we prove a lower bound of $`n^{c\log(q^3\log n)}`$ samples for every fixed $`0\lt c\lt 1/(4\log2)`$. Here q is the known deletion probability, and all logarithms are natural.
- notes: OpenAI math result family 122, Quantitative trace-reconstruction bounds with a uniform decoder -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/122.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.TraceReconstruction.quantitative_sample_lower_bound OAI.TraceReconstruction.superpolynomial_one_trace OAI.TraceReconstruction.superpolynomial_sample_complexity
- source_theorem_count: 3
- source_solution_module: OAI.Probability.TraceReconstruction
- source_papers: preprints/quantitative-lower-bounds-for-trace-reconstruction-September-24-2026/paper.pdf
- source_scope_note: lean/docs/122.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

open scoped ENNReal
noncomputable section

namespace TraceReconstruction

abbrev Word (n : ℕ) := Fin n → Bool
abbrev Mask (n : ℕ) := Fin n → Bool
abbrev Trace := List Bool

/-- `true` retains the bit. The observer gets only the resulting list. -/
def traceOfMask {n : ℕ} (x : Word n) (a : Mask n) : Trace :=
  ((List.finRange n).filter fun i => a i).map x

/-- The deletion-mask probability, with deletion probability `q`. -/
def maskWeight {n : ℕ} (q : ℝ) (a : Mask n) : ℝ :=
  ∏ i, if a i then 1 - q else q

/-- Law of a single complete trace. -/
def traceMass {n : ℕ} (q : ℝ) (x : Word n) (w : Trace) : ℝ :=
  ∑ a : Mask n, if traceOfMask x a = w then maskWeight q a else 0

/-- All possible complete outputs from length-n inputs, with lengths included. -/
def traceSpace (n : ℕ) : Finset Trace :=
  Finset.univ.biUnion fun k : Fin (n + 1) =>
    Finset.univ.image fun x : Word k.val => List.ofFn x

/-- 1/2 sum of absolute differences, on the full finite output space. -/
def traceTV {n : ℕ} (q : ℝ) (x y : Word n) : ℝ :=
  (1 / 2 : ℝ) * ∑ w ∈ traceSpace n, |traceMass q x w - traceMass q y w|

/-- The estimator may depend arbitrarily on n, q and every complete sample.
    Its value is its conditional probability of reporting the given input. -/
def IsEstimator {n m : ℕ} (A : (Fin m → Trace) → Word n → ℝ) : Prop :=
  (∀ z x, 0 ≤ A z x) ∧ (∀ z, ∑ x : Word n, A z x = 1)

/-- Independent masks generate independent complete traces; no retained
    positions, boundaries or other latent variables are revealed to A. -/
def reconstructionSuccess {n m : ℕ} (q : ℝ)
    (A : (Fin m → Trace) → Word n → ℝ) (x : Word n) : ℝ :=
  ∑ a : Fin m → Mask n,
    (∏ j, maskWeight q (a j)) * A (fun j => traceOfMask x (a j)) x

def SufficientBudget (n : ℕ) (q s : ℝ) (m : ℕ) : Prop :=
  ∃ A : (Fin m → Trace) → Word n → ℝ,
    IsEstimator A ∧ ∀ x, s ≤ reconstructionSuccess q A x

/-- Natural fixed sample budget; infimum of the empty set is infinity. -/
noncomputable def sampleComplexity (n : ℕ) (q s : ℝ) : ℝ≥0∞ :=
  sInf {t | ∃ m : ℕ, SufficientBudget n q s m ∧ t = (m : ℝ≥0∞)}

/-- The real infimum is a minimum for n>0 (a nonempty finite set). -/
noncomputable def minTraceTV (n : ℕ) (q : ℝ) : ℝ :=
  sInf {t | ∃ x y : Word n, x ≠ y ∧ t = traceTV q x y}

open Filter
open scoped Topology Classical ENNReal

def quantitative_sample_lower_bound_statement : Prop :=
  ∀ (s c : ℝ) (hs : s ∈ Set.Ioc 0 1) (hc : c ∈ Set.Ioo 0 (1 / (4 * Real.log 2))) (n : ℕ → ℕ) (q : ℕ → ℝ) (hn : Tendsto n atTop atTop) (hq : ∀ k, q k ∈ Set.Ioo 0 1) (hscale : Tendsto (fun k => (q k) ^ 3 * Real.log (n k)) atTop atTop),
    ∀ᶠ k in atTop,
      ENNReal.ofReal ((n k : ℝ) ^ (c * Real.log ((q k) ^ 3 * Real.log (n k)))) ≤
        sampleComplexity (n k) (q k) s

def superpolynomial_one_trace_statement : Prop :=
  ∀ (q : ℝ) (hq : q ∈ Set.Ioo 0 1) (C : ℝ) (hC : 0 < C),
    Tendsto (fun n : ℕ => (n : ℝ) ^ C * minTraceTV n q) atTop (𝓝 0)

def superpolynomial_sample_complexity_statement : Prop :=
  ∀ (q : ℝ) (hq : q ∈ Set.Ioo 0 1) (s : ℝ) (hs : s ∈ Set.Ioc 0 1) (C : ℝ) (hC : 0 < C),
    Tendsto
      (fun n : ℕ => sampleComplexity n q s / ENNReal.ofReal ((n : ℝ) ^ C))
      atTop (𝓝 ⊤)

end TraceReconstruction

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.TraceReconstruction.quantitative_sample_lower_bound_statement ∧
  _root_.OAI.TraceReconstruction.superpolynomial_one_trace_statement ∧
  _root_.OAI.TraceReconstruction.superpolynomial_sample_complexity_statement

end Problem

/- Formalization scope, from lean/docs/122.md: The formalization proves superpolynomial sample lower bounds for exact worst-case reconstruction of binary words from independent deletion traces, with unrestricted computation and any fixed positive success probability. For every fixed deletion probability $q\in(0,1)$, sample complexity grows faster than every fixed power of the word length; the minimum total-variation distance between two one-trace laws decays faster than every inverse power. More quantitatively, along sequences with $q^3\log n\to\infty$, the required number of samples is at least $n^{c\log(q^3\log n)}$ eventually for every fixed $0<c<1/(4\log2)$. All logarithms are natural. -/
