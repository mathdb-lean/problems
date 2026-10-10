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

- problem_id: NoiselessRegression
- collection: openai-math
- question_id: openai-math:140
- source: openai-math
- source_locator: lean/ComparatorChallenges/NoiselessRegression.lean#OAI.NoiselessRegression.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: For fixed A &gt; 0, a one-pass learner with $`Ad^2`$ persistent bits needs $`\Omega_A(d\log(1/\epsilon))`$ noiseless Gaussian samples to recover a unit vector to angular error $`0\lt \epsilon\le1/10`$ with probability 2/3, uniformly in accuracy for large d. Computation and randomized updates are unrestricted, but output uses only the terminal state, stopping index and fresh randomness. ([Lean](lean/docs/140.md)) For every fixed A &gt; 0, a learner that retains at most $`Ad^2`$ bits between fresh exact Gaussian linear measurements needs $`\Omega_A(d\log(1/\epsilon))`$ measurements to estimate a uniformly random unit vector to angular error at most ϵ, for any $`0\lt \epsilon\le 1/10`$, with probability at least 2/3. The constant is absolute for $`o(d^2)`$ memory. For a signal with density bounded by L relative to uniform probability on $`S^{d-1}`$, we bound the information in a finite message W formed from exact Gaussian measurements, conditional on an independent projection revealed only to the analyst. For explicit row counts proportional to d, the bound is $`O(H(W)/d+d+\log(2+\log L))`$. Consequently, a finite-state learner with $`o(d^2)`$ persistent bits and a deterministic sample horizon needs $`\Omega(d\log(1/\epsilon))`$ fresh noiseless Gaussian measurements for constant-probability angular accuracy $`0\lt \epsilon\le1/10`$ under the uniform spherical prior. For the image of a uniform cube under a spherical coordinate map, we prove that finite messages from t blocks of $`\Theta(d)`$ exact Gaussian measurements reveal only $`O_A(dt)`$ information when each message has at most $`\exp(Ad^2)`$ values, for fixed A. The same bound holds when each message is supplemented with a nested cell that restores the required geometric spread. We prove moment estimates for exact random projections of finite measures whose mass is controlled on Euclidean balls, and derive positive domination by countable sums of spherical cap measures. For learners with $`M=o(d^2)`$ bits of memory, these estimates give three proofs that uniform-sphere average success at least 2/3 at angular accuracy $`0\lt \epsilon\le1/10`$ requires $`\Omega(d\log(1/\epsilon))`$ noiseless Gaussian observations. The three proofs keep their different stopping and accuracy costs explicit. Replacing the Gaussian rows used to select a finite message by independent rows increases the remaining conditional information by at most $`Cd`$, for a uniform spherical signal, message entropy at most d2, and the specified row dimensions proportional to d. As an application, we prove that learners with $`M=o(d^2)`$ persistent bits need $`T=\Omega(d\log(1/\epsilon))`$ exact observations to attain uniform-sphere angular success at least 3/5, for $`0\lt \epsilon\le1/10`$ and a deterministic finite horizon. Let a finite-state streaming learner estimate a uniformly random unit vector from independent exact Gaussian linear measurements. We prove that $`o(d^2)`$ bits of persistent memory and angular success probability at least 2/3 require at least $`2^{-16}d\log_2(1/\epsilon)`$ samples for all sufficiently large d, uniformly for $`0\lt \epsilon\le1/10`$. The proof conditions each batch on its observed projection and controls the resulting random residual subsphere.
- notes: OpenAI math result family 140, Memory–sample lower bounds for noiseless Gaussian regression -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/140.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.NoiselessRegression.main
- source_theorem_count: 1
- source_solution_module: OAI.Probability.GaussianRegression.Main
- source_papers: preprints/Memory-and-precision-in-noiseless-Gaussian-regression-September-27-2026/paper.pdf preprints/Posterior-replicas-and-conditional-information-in-Gaussian-regression-September-27-2026/paper.pdf preprints/Localization-costs-and-information-growth-for-exact-Gaussian-observations-September-27-2026/paper.pdf preprints/Projection-moments-positive-cap-domination-and-Riesz-estimates-on-the-sphere-September-27-2026/paper.pdf preprints/Replacing-Gaussian-observations-in-memory-constrained-inference-September-27-2026/paper.pdf preprints/Subsphere-methods-for-memory-sample-lower-bounds-in-noiseless-Gaussian-regression-September-27-2026/paper.pdf
- source_scope_note: lean/docs/140.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

/-!
Finite-state Gaussian regression with noiseless labels and angular accuracy.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

abbrev Vector (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev UnitSphere (d : ℕ) := Metric.sphere (0 : Vector d) 1
abbrev State (M : ℕ) := Fin (2 ^ M)
abbrev Samples (d T : ℕ) := Fin T → Vector d

def uniformSphere (d : ℕ) : Measure (UnitSphere d) :=
  let σ := (volume : Measure (Vector d)).toSphere
  (σ Set.univ)⁻¹ • σ

def sampleLaw (d T : ℕ) : Measure (Samples d T) :=
  Measure.pi fun _ => stdGaussian (Vector d)

def observationReference (d : ℕ) : Measure (Vector d × ℝ) :=
  (stdGaussian (Vector d)).prod volume

structure Learner (d M T : ℕ) (Ω : Type u) where
  initialChoice : Ω → Bool × State M
  transition : ℕ → Ω → State M → (Vector d × ℝ) → Bool × State M
  output : ℕ → Ω → State M → UnitSphere d

namespace Learner

abbrev RunStatus (M : ℕ) := Sum (State M) (ℕ × State M)

def start {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω) (ω : Ω) :
    RunStatus M :=
  let a := L.initialChoice ω
  if a.1 then .inr (0, a.2) else .inl a.2

def run {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (s : UnitSphere d) (ω : Ω) (x : Samples d T) : ℕ → RunStatus M
  | 0 => L.start ω
  | n + 1 =>
    match L.run s ω x n with
    | .inr done => .inr done
    | .inl state =>
      if hn : n < T then
        let row := x ⟨n, hn⟩
        let a := L.transition (n + 1) ω state (row, ⟪row, s.val⟫)
        if a.1 then .inr (n + 1, a.2) else .inl a.2
      else .inl state

def terminal {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (s : UnitSphere d) (ω : Ω) (x : Samples d T) : ℕ × State M :=
  match L.run s ω x T with
  | .inl state => (T, state)
  | .inr done => done

def estimate {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (s : UnitSphere d) (ω : Ω) (x : Samples d T) : UnitSphere d :=
  let a := L.terminal s ω x
  L.output a.1 ω a.2

structure Admissible {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) : Prop where
  initialChoice : AEMeasurable L.initialChoice ρ
  transition : ∀ t a, AEMeasurable (fun z : Ω × (Vector d × ℝ) =>
    L.transition t z.1 a z.2) (ρ.prod (observationReference d))
  output : ∀ t a, AEMeasurable (fun ω => L.output t ω a) ρ
  fixed_experiment : ∀ s, AEMeasurable (fun z : Ω × Samples d T =>
    L.estimate s z.1 z.2) (ρ.prod (sampleLaw d T))
  uniform_experiment : AEMeasurable
    (fun z : UnitSphere d × (Ω × Samples d T) => L.estimate z.1 z.2.1 z.2.2)
    ((uniformSphere d).prod (ρ.prod (sampleLaw d T)))

def angularError {d : ℕ} (s ŝ : UnitSphere d) : ℝ :=
  Real.arccos ⟪ŝ.val, s.val⟫

def success {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) (ε : ℝ) (s : UnitSphere d) : ℝ≥0∞ :=
  (ρ.prod (sampleLaw d T))
    {z | angularError s (L.estimate s z.1 z.2) ≤ ε}

def uniformSuccess {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) (ε : ℝ) : ℝ≥0∞ :=
  ((uniformSphere d).prod (ρ.prod (sampleLaw d T)))
    {z | angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε}

end Learner

def SubquadraticMemory : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ → ℕ,
    Asymptotics.IsLittleO atTop (fun d => (M d : ℝ)) (fun d => (d : ℝ) ^ 2) →
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ T : ℕ, ∀ ε : ℝ,
    0 < ε → ε ≤ 1 / 10 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ L : Learner d (M d) T Ω, L.Admissible ρ →
    (((2 : ℕ) / (3 : ℕ) : ℝ≥0∞) ≤ L.uniformSuccess ρ ε ∨
      ∀ s, ((2 : ℕ) / (3 : ℕ) : ℝ≥0∞) ≤ L.success ρ ε s) →
    c * (d : ℝ) * Real.log (1 / ε) ≤ (T : ℝ)

def FixedQuadraticMemory : Prop :=
  ∀ A₀ : ℝ, 0 < A₀ → ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ,
    ∀ d : ℕ, d₀ ≤ d → ∀ M T : ℕ, (M : ℝ) ≤ A₀ * (d : ℝ) ^ 2 →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 10 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ L : Learner d M T Ω, L.Admissible ρ →
    ((2 : ℕ) / (3 : ℕ) : ℝ≥0∞) ≤ L.uniformSuccess ρ ε →
    c * (d : ℝ) * Real.log (1 / ε) ≤ (T : ℝ)

def main_statement : Prop :=
  SubquadraticMemory.{u} ∧ FixedQuadraticMemory.{u}

end NoiselessRegression

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u} : Prop :=
  _root_.OAI.NoiselessRegression.main_statement.{u}

end Problem

/- Formalization scope, from lean/docs/140.md: In noiseless Gaussian regression, a learner observes inner products of an unknown unit vector in $\mathbb R^d$ with independent standard Gaussian vectors. The formalization proves that, for every fixed $A>0$, there is $c_A>0$ such that, in sufficiently large dimension, a learner retaining at most $Ad^2$ bits between observations needs at least $c_A d\log(1/\varepsilon)$ observations to attain angular error at most $\varepsilon$ with probability at least $2/3$ for a uniformly random unit signal, for $0<\varepsilon\le1/10$. For memory $o(d^2)$, the constant can be universal, and the selected statement also permits success at least $2/3$ separately for every signal. The linked supporting results include inverse Gram-matrix moments, exact-projection densities, regularization bounds, and sphere- and cube-prior block estimates. The paper studies how posterior replicas—independent signals drawn conditionally on the same observed data—control information in noiseless Gaussian regression. The formalization establishes the equal-label identity for finite measures, its density and measurable forms, and information bounds for Gaussian, distance, Haar, synthetic, and incidence comparisons. These statements retain exact observation labels, independent side randomness, and randomized transition rules. For a learner using $M(d)=o(d^2)$ bits of memory, the resulting bound says that, for sufficiently large $d$ and $0<\varepsilon\le1/10$, success probability at least $2/3$ under the uniform unit-sphere prior requires $T\ge c d\log(1/\varepsilon)$ observations, where $c>0$ is universal. The formalized streaming result uses the $2/3$ threshold; the stronger $3/5$ variant is outside this scope. The formalization controls information gained from exact Gaussian observations of a spherical image of the uniform cube. Under the stated entropy and size conditions, repeated localization over $t$ observation blocks produces nested disclosures with mutual information at most $C(n+1)t$ and expected final localization level at most $Ct$. The selected estimates include inverse-volume control, kernel coercivity, and drift for the actual observation rows. For a law of finite relative entropy with respect to a uniform cell law in sufficiently large dimension, the regularization procedure terminates almost surely in regular cells. Its expected depth and number of attempts are finite, with at most twice one plus the expected depth in expectation; the remaining relative entropy plus $(\log 2)n/4$ times the expected depth is at most the initial relative entropy plus $2/e$. The paper uses projection moments and domination by positive spherical caps to bound the information carried by exact Gaussian observations of an unknown unit vector. The formalization covers integrated frame and sphere moments, cap domination, Riesz-density estimates with fixed offsets, and bounds valid at every radius. It also covers probability bounds for finite-memory learners at a fixed stopping time and after summing over stopping times. For $M(d)=o(d^2)$ bits of memory, sufficiently large $d$, and $0<\varepsilon\le1/10$, success probability at least $2/3$ under the uniform sphere prior requires $T\ge c d\log(1/\varepsilon)$ observations for a universal $c>0$. A corresponding bound holds when $M\le A d^2$ for each fixed $A>0$, with the constant allowed to depend on $A$. The randomized learner model allows independent shared seeds; its reduction to a finite-state model is proved for dimensions at least three, with the auxiliary dimension-two case outside this scope. The paper compares fresh Gaussian observations with observations coupled to information already held in memory. The formalization covers mixed-moment and actual-row estimates, critical-radius, one-level, and two-label comparisons, and conditional-information bounds across a block of observations. For sufficiently large dimension $d$, the relevant entropy bounds of order $d^2$ bound the information in the fresh experiment by that in the coupled experiment plus a term of order $d$; the associated block information increase also has order $d$. It also covers two-point identities on observation fibers and the fiber-block bound, including the boundary case of $d-2$ observed rows. The uniform unit-sphere prior, Gaussian rows, finite memory states, and randomized transition rules remain part of these statements. The separate streaming consequences and several intermediate comparison constructions are outside this selection. The paper uses subspheres to bound the number of exact Gaussian observations needed to estimate a unit vector with limited memory. The formalization proves that, for $M(d)=o(d^2)$ bits of memory, sufficiently large $d$, and $0<\varepsilon\le1/10$, success probability at least $2/3$ under the uniform sphere prior, or for every unit signal, requires at least $2^{-16}d\log_2(1/\varepsilon)$ observations. Under the uniform prior, a lower bound of the same order with a universal positive constant holds at success probability $1/2$. The formalization also covers radius-weighted block and terminal estimates, affine and dimension estimates, and a vector-valued beta-mixture comparison with its boundary cases. These statements retain their dimension, width, radius, and suffix hypotheses, as well as the finite-state learner's independent randomness and restrictions on stopping and output. -/
