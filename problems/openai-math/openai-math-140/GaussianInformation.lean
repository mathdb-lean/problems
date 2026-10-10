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

- problem_id: GaussianInformation
- collection: openai-math
- question_id: openai-math:140
- source: openai-math
- source_locator: lean/ComparatorChallenges/GaussianInformation.lean#OAI.RepeatedLocalization.repeated_localization
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: For fixed A &gt; 0, a one-pass learner with $`Ad^2`$ persistent bits needs $`\Omega_A(d\log(1/\epsilon))`$ noiseless Gaussian samples to recover a unit vector to angular error $`0\lt \epsilon\le1/10`$ with probability 2/3, uniformly in accuracy for large d. Computation and randomized updates are unrestricted, but output uses only the terminal state, stopping index and fresh randomness. ([Lean](lean/docs/140.md)) For every fixed A &gt; 0, a learner that retains at most $`Ad^2`$ bits between fresh exact Gaussian linear measurements needs $`\Omega_A(d\log(1/\epsilon))`$ measurements to estimate a uniformly random unit vector to angular error at most ϵ, for any $`0\lt \epsilon\le 1/10`$, with probability at least 2/3. The constant is absolute for $`o(d^2)`$ memory. For a signal with density bounded by L relative to uniform probability on $`S^{d-1}`$, we bound the information in a finite message W formed from exact Gaussian measurements, conditional on an independent projection revealed only to the analyst. For explicit row counts proportional to d, the bound is $`O(H(W)/d+d+\log(2+\log L))`$. Consequently, a finite-state learner with $`o(d^2)`$ persistent bits and a deterministic sample horizon needs $`\Omega(d\log(1/\epsilon))`$ fresh noiseless Gaussian measurements for constant-probability angular accuracy $`0\lt \epsilon\le1/10`$ under the uniform spherical prior. For the image of a uniform cube under a spherical coordinate map, we prove that finite messages from t blocks of $`\Theta(d)`$ exact Gaussian measurements reveal only $`O_A(dt)`$ information when each message has at most $`\exp(Ad^2)`$ values, for fixed A. The same bound holds when each message is supplemented with a nested cell that restores the required geometric spread. We prove moment estimates for exact random projections of finite measures whose mass is controlled on Euclidean balls, and derive positive domination by countable sums of spherical cap measures. For learners with $`M=o(d^2)`$ bits of memory, these estimates give three proofs that uniform-sphere average success at least 2/3 at angular accuracy $`0\lt \epsilon\le1/10`$ requires $`\Omega(d\log(1/\epsilon))`$ noiseless Gaussian observations. The three proofs keep their different stopping and accuracy costs explicit. Replacing the Gaussian rows used to select a finite message by independent rows increases the remaining conditional information by at most $`Cd`$, for a uniform spherical signal, message entropy at most d2, and the specified row dimensions proportional to d. As an application, we prove that learners with $`M=o(d^2)`$ persistent bits need $`T=\Omega(d\log(1/\epsilon))`$ exact observations to attain uniform-sphere angular success at least 3/5, for $`0\lt \epsilon\le1/10`$ and a deterministic finite horizon. Let a finite-state streaming learner estimate a uniformly random unit vector from independent exact Gaussian linear measurements. We prove that $`o(d^2)`$ bits of persistent memory and angular success probability at least 2/3 require at least $`2^{-16}d\log_2(1/\epsilon)`$ samples for all sufficiently large d, uniformly for $`0\lt \epsilon\le1/10`$. The proof conditions each batch on its observed projection and controls the resulting random residual subsphere.
- notes: OpenAI math result family 140, Memory–sample lower bounds for noiseless Gaussian regression -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/140.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.RepeatedLocalization.repeated_localization OAI.AllScaleInverseVolume.inverse_volume_without_support OAI.KernelPotential.kernel_coercivity OAI.KernelPotential.actual_row_drift
- source_theorem_count: 4
- source_solution_module: OAI.Probability.GaussianInformation.Main
- source_papers: preprints/Memory-and-precision-in-noiseless-Gaussian-regression-September-27-2026/paper.pdf preprints/Posterior-replicas-and-conditional-information-in-Gaussian-regression-September-27-2026/paper.pdf preprints/Localization-costs-and-information-growth-for-exact-Gaussian-observations-September-27-2026/paper.pdf preprints/Projection-moments-positive-cap-domination-and-Riesz-estimates-on-the-sphere-September-27-2026/paper.pdf preprints/Replacing-Gaussian-observations-in-memory-constrained-inference-September-27-2026/paper.pdf preprints/Subsphere-methods-for-memory-sample-lower-bounds-in-noiseless-Gaussian-regression-September-27-2026/paper.pdf
- source_scope_note: lean/docs/140.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

abbrev Coordinate (n : ℕ) := Fin n → ℝ
abbrev GaussianBlock (n : ℕ) := Fin (n / 16) → Fin (n + 1) → ℝ
abbrev Label (n : ℕ) := Fin (n / 16) → ℝ
abbrev History (N t : ℕ) := Fin t → Fin N
abbrev Cell (n : ℕ) := Σ J : ℕ, Fin n → Fin (2 ^ J)

instance cellMeasurableSpace (n : ℕ) : MeasurableSpace (Cell n) := ⊤

noncomputable def initialCube (n : ℕ) : Set (Coordinate n) :=
  Set.pi Set.univ (fun _ => Set.Ico (-1 / (2 * Real.sqrt n)) (1 / (2 * Real.sqrt n)))

noncomputable def cubePrior (n : ℕ) : Measure (Coordinate n) :=
  ProbabilityTheory.cond volume (initialCube n)

noncomputable def chart {n : ℕ} (z : Coordinate n) : Fin (n + 1) → ℝ :=
  Fin.lastCases (Real.sqrt (1 - ∑ a, (z a) ^ 2)) z

noncomputable def cellSet {n : ℕ} (Q : Cell n) : Set (Coordinate n) :=
  {z | ∀ a, -1 / (2 * Real.sqrt n) + (Q.2 a : ℝ) / (Real.sqrt n * (2 : ℝ) ^ Q.1) ≤ z a ∧
    z a < -1 / (2 * Real.sqrt n) + ((Q.2 a : ℝ) + 1) / (Real.sqrt n * (2 : ℝ) ^ Q.1)}

def rootCell (n : ℕ) : Cell n := ⟨0, fun _ => 0⟩

noncomputable def gaussianBlockLaw (n : ℕ) : Measure (GaussianBlock n) :=
  Measure.pi (fun _ => Measure.pi (fun _ => gaussianReal 0 1))

noncomputable def exactLabel {n : ℕ} (X : GaussianBlock n) (z : Coordinate n) : Label n :=
  fun row => ∑ a, X row a * chart z a

structure BlockRule (n N : ℕ) where
  prob : (GaussianBlock n × Label n) → Fin N → ℝ
  measurable_prob : ∀ w, Measurable (fun data => prob data w)
  nonneg : ∀ data w, 0 ≤ prob data w
  sum_one : ∀ data, ∑ w, prob data w = 1

abbrev Rules (n N t : ℕ) := ∀ i : Fin t, History N i.val → BlockRule n N

def past {N t : ℕ} (w : History N t) (i : Fin t) : History N i.val :=
  fun j => w ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩

def through {N t : ℕ} (w : History N t) (i : Fin t) : History N (i.val + 1) :=
  fun j => w ⟨j.val, Nat.lt_of_lt_of_le j.isLt i.isLt⟩

noncomputable def blockProbability {n N : ℕ} (rule : BlockRule n N)
    (z : Coordinate n) (w : Fin N) : ℝ :=
  ∫ X, rule.prob (X, exactLabel X z) w ∂gaussianBlockLaw n

noncomputable def historyLikelihood {n N t : ℕ} (rules : Rules n N t)
    (z : Coordinate n) (w : History N t) : ℝ :=
  ∏ i, blockProbability (rules i (past w i)) z (w i)

noncomputable def experimentLaw {n N t : ℕ} (rules : Rules n N t) :
    Measure (Coordinate n × History N t) :=
  ∑ w : History N t,
    ((cubePrior n).withDensity (fun z => ENNReal.ofReal (historyLikelihood rules z w))).map
      (fun z => (z, w))

abbrev Disclosure (n N t : ℕ) := ∀ i : Fin t, Coordinate n → History N (i.val + 1) → Cell n

def ValidDisclosure {n N t : ℕ} (Q : Disclosure n N t) : Prop :=
  (∀ i, Measurable (fun zh : Coordinate n × History N (i.val + 1) => Q i zh.1 zh.2)) ∧
  (∀ i, (Set.range (fun zh : Coordinate n × History N (i.val + 1) => Q i zh.1 zh.2)).Finite) ∧
  (∀ z ∈ initialCube n, ∀ w : History N t, ∀ i,
    z ∈ cellSet (Q i z (through w i)) ∧ cellSet (Q i z (through w i)) ⊆ initialCube n) ∧
  (∀ z ∈ initialCube n, ∀ w : History N t, ∀ i j : Fin t, i ≤ j →
    cellSet (Q j z (through w j)) ⊆ cellSet (Q i z (through w i)))

noncomputable def transcriptMap {n N t : ℕ} (Q : Disclosure n N t)
    (zw : Coordinate n × History N t) : Coordinate n × (History N t × (Fin t → Cell n)) :=
  (zw.1, (zw.2, fun i => Q i zw.1 (through zw.2 i)))

noncomputable def augmentedLaw {n N t : ℕ} (rules : Rules n N t) (Q : Disclosure n N t) :=
  (experimentLaw rules).map (transcriptMap Q)

noncomputable def mutualInformation {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure (α × β)) : ℝ≥0∞ :=
  InformationTheory.klDiv μ ((μ.map Prod.fst).prod (μ.map Prod.snd))

noncomputable def finalLevel {n N t : ℕ} (Q : Disclosure n N t)
    (zw : Coordinate n × History N t) : ℕ :=
  if ht : 0 < t then
    let i : Fin t := ⟨t - 1, by omega⟩
    (Q i zw.1 (through zw.2 i)).1
  else 0

def MainStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ C₀ : ℝ, 0 < C₀ →
    ∃ C : ℝ, 0 < C ∧ ∀ (n N t : ℕ), n₀ ≤ n → 1 ≤ N → ∀ rules : Rules n N t,
      (2 / (n / 8 : ℕ) + Real.exp (-c * (n / 16 : ℕ))) * Real.log N ≤ C₀ * (n + 1) →
      ∃ Q : Disclosure n N t, ValidDisclosure Q ∧
        mutualInformation (augmentedLaw rules Q) ≤ ENNReal.ofReal (C * (n + 1) * t) ∧
        (∫ zw, (finalLevel Q zw : ℝ) ∂experimentLaw rules) ≤ C * t

def repeated_localization_statement : Prop :=
  MainStatement

end RepeatedLocalization


open MeasureTheory Metric
open scoped ENNReal
namespace AllScaleInverseVolume
local instance namedAtLeastTwoTwo : Nat.AtLeastTwo 2 := ⟨Nat.le_refl 2⟩

abbrev Ambient (d : ℕ) := EuclideanSpace ℝ (Fin d)

noncomputable local instance ambientSub (d : ℕ) : Sub (Ambient d) where
  sub vector other := WithLp.toLp (2 : ℝ≥0∞)
    (WithLp.ofLp (p := (2 : ℝ≥0∞)) vector - WithLp.ofLp (p := (2 : ℝ≥0∞)) other)

noncomputable local instance ambientInner (d : ℕ) : Inner ℝ (Ambient d) where
  inner vector other := ∑ coordinate : Fin d,
    inner ℝ (WithLp.ofLp (p := (2 : ℝ≥0∞)) vector coordinate)
      (WithLp.ofLp (p := (2 : ℝ≥0∞)) other coordinate)

noncomputable def gramVolume {d k : ℕ} (u : Ambient d) (z : Fin k → Ambient d) : ℝ :=
  Real.sqrt (Matrix.gram ℝ (fun i => z i-u)).det
noncomputable def inverseVolume {d : ℕ} (u : Ambient d) (z : Fin (d/100) → Ambient d) : ℝ≥0∞ :=
  ((ENNReal.ofReal (gramVolume u z))⁻¹)^(d/100)
def BallBound {d : ℕ} (ν : Measure (Ambient d)) : Prop :=
  ∀ (x : Ambient d) (r : ℝ), 0 < r →
    ν (ball x r) ≤ ENNReal.ofReal (r^(((d:ℝ)-1)/2))
def InverseVolumeStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    ∀ ν : Measure (Ambient d), IsProbabilityMeasure ν → BallBound ν →
      ∀ u : Ambient d, (∫⁻ z,inverseVolume u z ∂Measure.pi (fun _ : Fin (d/100) => ν)) ≤
        ENNReal.ofReal (Real.exp (C*d*(d/100:ℕ)))
def inverse_volume_without_support_statement : Prop :=
  InverseVolumeStatement
end AllScaleInverseVolume


open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential
local instance namedAtLeastTwoTwo : Nat.AtLeastTwo 2 := ⟨Nat.le_refl 2⟩

abbrev Ambient (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Rows (d : ℕ) := Fin (d/16) → Fin d → ℝ
noncomputable def radial {d : ℕ} (x : Ambient d) : Ambient d := ‖x‖⁻¹ • x
noncomputable def sphereProbability (d : ℕ) : Measure (Ambient d) :=
  ((volume (ball (0 : Ambient d) 1))⁻¹ • volume.restrict (ball (0 : Ambient d) 1)).map radial
noncomputable def J {d : ℕ} (ν : Measure (Ambient d)) (s : Ambient d) : ℝ≥0∞ :=
  ∫⁻ u,((ENNReal.ofReal ‖u-s‖)⁻¹)^(2*(d/16)) ∂ν
noncomputable def B {d : ℕ} (ν : Measure (Ambient d)) : ℝ :=
  ∫ s, Real.log ((J ν s).toReal) ∂ν
noncomputable def Phi {d : ℕ} (ν : Measure (Ambient d)) : ℝ :=
  (InformationTheory.klDiv ν (sphereProbability d)).toReal - B ν

def BoundedDensity {d : ℕ} (ν : Measure (Ambient d)) : Prop :=
  ∃ H : ℝ, 0 < H ∧ ν ≤ ENNReal.ofReal H • sphereProbability d

noncomputable def rowLaw (d : ℕ) : Measure (Rows d) :=
  Measure.pi (fun _ : Fin (d/16) => Measure.pi (fun _ : Fin d => gaussianReal 0 1))
noncomputable def labels {d : ℕ} (a : Rows d) (s : Ambient d) : Fin (d/16) → ℝ :=
  fun i => ∑ j,a i j*s j
structure BlockRule (d N : ℕ) where
  prob : (Fin N × (Rows d × (Fin (d/16) → ℝ))) → Fin N → ℝ
  measurable_prob : ∀ w, Measurable (fun x => prob x w)
  nonneg_prob : ∀ x w, 0 ≤ prob x w
  sum_prob : ∀ x, ∑ w,prob x w=1

noncomputable def outgoingLaw {d N : ℕ} (μ : Measure (Ambient d × Fin N))
    (rule : BlockRule d N) : Measure (Ambient d × Fin N) :=
  ∑ w : Fin N, ((μ.prod (rowLaw d)).withDensity (fun x =>
    ENNReal.ofReal (rule.prob (x.1.2,x.2,labels x.2 x.1.1) w))).map (fun x => (x.1.1,w))
noncomputable def component {d N : ℕ} (μ : Measure (Ambient d × Fin N)) (v : Fin N) :
    Measure (Ambient d) := (μ.restrict {x|x.2=v}).map Prod.fst
noncomputable def posterior {d N : ℕ} (μ : Measure (Ambient d × Fin N)) (v : Fin N) :
    Measure (Ambient d) := (component μ v univ)⁻¹ • component μ v
noncomputable def averagePhi {d N : ℕ} (μ : Measure (Ambient d × Fin N)) : ℝ :=
  ∑ v : Fin N, (component μ v univ).toReal * Phi (posterior μ v)

def CoercivityStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    (∀ ν : Measure (Ambient d), IsProbabilityMeasure ν → BoundedDensity ν →
      (1/2:ℝ)*(InformationTheory.klDiv ν (sphereProbability d)).toReal-C*d ≤ Phi ν) ∧
    Phi (sphereProbability d) ≤ (2*(d/16):ℕ)*Real.log 2 ∧
    (∀ (q : ℕ) (w : Fin q → ℝ), (∀ i,0 ≤ w i) → (∑ i,w i)=1 →
      ∀ ν : Fin q → Measure (Ambient d), (∀ i,IsProbabilityMeasure (ν i)) →
      (∀ i,BoundedDensity (ν i)) →
      Phi (∑ i,ENNReal.ofReal (w i) • ν i) ≤ ∑ i,w i*Phi (ν i))

def DriftStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ N : ℕ, 1 ≤ N →
    Real.log N ≤ (d:ℝ)^2 → ∀ μ : Measure (Ambient d × Fin N), IsProbabilityMeasure μ →
    μ.map Prod.fst=sphereProbability d → ∀ rule : BlockRule d N,
      averagePhi (outgoingLaw μ rule) ≤ averagePhi μ+C*d

def kernel_coercivity_statement : Prop :=
  CoercivityStatement
def actual_row_drift_statement : Prop :=
  DriftStatement
end KernelPotential

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.RepeatedLocalization.repeated_localization_statement ∧
  _root_.OAI.AllScaleInverseVolume.inverse_volume_without_support_statement ∧
  _root_.OAI.KernelPotential.kernel_coercivity_statement ∧
  _root_.OAI.KernelPotential.actual_row_drift_statement

end Problem

/- Formalization scope, from lean/docs/140.md: In noiseless Gaussian regression, a learner observes inner products of an unknown unit vector in $\mathbb R^d$ with independent standard Gaussian vectors. The formalization proves that, for every fixed $A>0$, there is $c_A>0$ such that, in sufficiently large dimension, a learner retaining at most $Ad^2$ bits between observations needs at least $c_A d\log(1/\varepsilon)$ observations to attain angular error at most $\varepsilon$ with probability at least $2/3$ for a uniformly random unit signal, for $0<\varepsilon\le1/10$. For memory $o(d^2)$, the constant can be universal, and the selected statement also permits success at least $2/3$ separately for every signal. The linked supporting results include inverse Gram-matrix moments, exact-projection densities, regularization bounds, and sphere- and cube-prior block estimates. The paper studies how posterior replicas—independent signals drawn conditionally on the same observed data—control information in noiseless Gaussian regression. The formalization establishes the equal-label identity for finite measures, its density and measurable forms, and information bounds for Gaussian, distance, Haar, synthetic, and incidence comparisons. These statements retain exact observation labels, independent side randomness, and randomized transition rules. For a learner using $M(d)=o(d^2)$ bits of memory, the resulting bound says that, for sufficiently large $d$ and $0<\varepsilon\le1/10$, success probability at least $2/3$ under the uniform unit-sphere prior requires $T\ge c d\log(1/\varepsilon)$ observations, where $c>0$ is universal. The formalized streaming result uses the $2/3$ threshold; the stronger $3/5$ variant is outside this scope. The formalization controls information gained from exact Gaussian observations of a spherical image of the uniform cube. Under the stated entropy and size conditions, repeated localization over $t$ observation blocks produces nested disclosures with mutual information at most $C(n+1)t$ and expected final localization level at most $Ct$. The selected estimates include inverse-volume control, kernel coercivity, and drift for the actual observation rows. For a law of finite relative entropy with respect to a uniform cell law in sufficiently large dimension, the regularization procedure terminates almost surely in regular cells. Its expected depth and number of attempts are finite, with at most twice one plus the expected depth in expectation; the remaining relative entropy plus $(\log 2)n/4$ times the expected depth is at most the initial relative entropy plus $2/e$. The paper uses projection moments and domination by positive spherical caps to bound the information carried by exact Gaussian observations of an unknown unit vector. The formalization covers integrated frame and sphere moments, cap domination, Riesz-density estimates with fixed offsets, and bounds valid at every radius. It also covers probability bounds for finite-memory learners at a fixed stopping time and after summing over stopping times. For $M(d)=o(d^2)$ bits of memory, sufficiently large $d$, and $0<\varepsilon\le1/10$, success probability at least $2/3$ under the uniform sphere prior requires $T\ge c d\log(1/\varepsilon)$ observations for a universal $c>0$. A corresponding bound holds when $M\le A d^2$ for each fixed $A>0$, with the constant allowed to depend on $A$. The randomized learner model allows independent shared seeds; its reduction to a finite-state model is proved for dimensions at least three, with the auxiliary dimension-two case outside this scope. The paper compares fresh Gaussian observations with observations coupled to information already held in memory. The formalization covers mixed-moment and actual-row estimates, critical-radius, one-level, and two-label comparisons, and conditional-information bounds across a block of observations. For sufficiently large dimension $d$, the relevant entropy bounds of order $d^2$ bound the information in the fresh experiment by that in the coupled experiment plus a term of order $d$; the associated block information increase also has order $d$. It also covers two-point identities on observation fibers and the fiber-block bound, including the boundary case of $d-2$ observed rows. The uniform unit-sphere prior, Gaussian rows, finite memory states, and randomized transition rules remain part of these statements. The separate streaming consequences and several intermediate comparison constructions are outside this selection. The paper uses subspheres to bound the number of exact Gaussian observations needed to estimate a unit vector with limited memory. The formalization proves that, for $M(d)=o(d^2)$ bits of memory, sufficiently large $d$, and $0<\varepsilon\le1/10$, success probability at least $2/3$ under the uniform sphere prior, or for every unit signal, requires at least $2^{-16}d\log_2(1/\varepsilon)$ observations. Under the uniform prior, a lower bound of the same order with a universal positive constant holds at success probability $1/2$. The formalization also covers radius-weighted block and terminal estimates, affine and dimension estimates, and a vector-valued beta-mixture comparison with its boundary cases. These statements retain their dimension, width, radius, and suffix hypotheses, as well as the finite-state learner's independent randomness and restrictions on stopping and output. -/
