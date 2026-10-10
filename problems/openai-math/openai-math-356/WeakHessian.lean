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

- problem_id: WeakHessian
- collection: openai-math
- question_id: openai-math:356
- source: openai-math
- source_locator: lean/ComparatorChallenges/WeakHessian.lean#OAI.WeakHessian.every_geodesic
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves Gigli's conjecture: in every integer dimension n ≥ 2, Alexandrov curvature at least κ is characterized by the full-support $`\mathop{\mathrm{RCD}}\nolimits ((n-1)\kappa,n)`$ condition with reference measure $`\mathcal H^n`$ and distributional sectional curvature at least κ in the original global test classes. The RCD condition is unreduced. ([Lean](lean/docs/356.md)) On a full-support $`\mathrm{RCD}(K,N)`$ space with $`1\lt N\lt \infty`$, we prove that a bounded globally Lipschitz function whose distributional Hessian is bounded above by a bounded continuous function satisfies the corresponding second-derivative inequality along every minimizing geodesic.
- notes: OpenAI math result family 356, Gigli’s characterization of Alexandrov curvature -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/356.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.WeakHessian.every_geodesic
- source_theorem_count: 1
- source_solution_module: OAI.Geometry.WeakHessian.Main
- source_main_result: OAI.WeakHessian.every_geodesic
- source_papers: preprints/Weak-Hessian-bounds-along-every-geodesic-in-RCD-spaces-September-24-2026/weak-hessian-geodesics.pdf
- source_scope_note: lean/docs/356.md
- source_field: Geometry
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable
namespace WeakHessian

abbrev Time := Set.Icc (0 : ℝ) 1

def timeZero : Time := ⟨0, le_rfl, zero_le_one⟩
def timeOne : Time := ⟨1, zero_le_one, le_rfl⟩

def clampTime (t : ℝ) : Time :=
  ⟨max 0 (min 1 t), le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

variable {X : Type*} [MetricSpace X]

abbrev Curve (X : Type*) [MetricSpace X] := C(Time, X)

instance curveMeasurableSpace : MeasurableSpace (Curve X) := borel (Curve X)

instance curveBorelSpace : BorelSpace (Curve X) := ⟨rfl⟩

def evalReal (γ : Curve X) (t : ℝ) : X := γ (clampTime t)

/-- The constant-speed minimizing parametrization, including constant curves. -/
def IsGeodesic (γ : Curve X) : Prop :=
  ∀ s t : Time,
    dist (γ s) (γ t) = |(s : ℝ) - (t : ℝ)| * dist (γ timeZero) (γ timeOne)

/-- Metric speed. Limsup agrees a.e. with the metric derivative on AC² curves. -/
def metricSpeed (γ : Curve X) (t : ℝ) : ℝ≥0∞ :=
  Filter.limsup (fun s : ℝ => ENNReal.ofReal
    (dist (evalReal γ s) (evalReal γ t) / |s - t|)) (𝓝[≠] t)

/-- Absolute continuity with a square-integrable metric control. -/
def IsAC2 (γ : Curve X) : Prop :=
  ∃ a : ℝ → ℝ≥0∞, Measurable a ∧
    (∫⁻ t in Set.Icc (0 : ℝ) 1, (a t) ^ 2) < ∞ ∧
    ∀ s t : Time, (s : ℝ) ≤ (t : ℝ) →
      edist (γ s) (γ t) ≤ ∫⁻ r in Set.Icc (s : ℝ) (t : ℝ), a r

variable [MeasurableSpace X] [BorelSpace X]

/-- A 2-test plan: bounded compression and finite average kinetic energy. -/
def IsTestPlan (m : Measure X) (π : Measure (Curve X)) : Prop :=
  IsProbabilityMeasure π ∧
  (∃ C : ℝ≥0, ∀ t : Time,
    Measure.map (fun γ : Curve X => γ t) π ≤ (C : ℝ≥0∞) • m) ∧
  (∀ᵐ γ ∂π, IsAC2 γ) ∧
  (∫⁻ γ, ∫⁻ t in Set.Icc (0 : ℝ) 1, (metricSpeed γ t) ^ 2 ∂volume ∂π) < ∞

/-- Uniform bounded spatial support; used only to define the local Sobolev class. -/
def BoundedTracks (π : Measure (Curve X)) : Prop :=
  ∃ o : X, ∃ R : ℝ, 0 < R ∧ ∀ᵐ γ ∂π, ∀ t : Time, dist (γ t) o ≤ R

def LocallyL2 (m : Measure X) (f : X → ℝ) : Prop :=
  ∀ o : X, ∀ R : ℝ, 0 < R → MemLp f 2 (m.restrict (Metric.ball o R))

/-- Local weak upper gradients, in the integrated test-plan definition. -/
def IsLocalWeakUpperGradient (m : Measure X) (f D : X → ℝ) : Prop :=
  LocallyL2 m D ∧ (∀ᵐ x ∂m, 0 ≤ D x) ∧
  ∀ π : Measure (Curve X), IsTestPlan m π → BoundedTracks π →
    (∫⁻ γ, ENNReal.ofReal |f (γ timeOne) - f (γ timeZero)| ∂π) ≤
      ∫⁻ γ, ∫⁻ t in Set.Icc (0 : ℝ) 1,
        ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t ∂volume ∂π

def IsMinimalLocalWeakUpperGradient (m : Measure X) (f D : X → ℝ) : Prop :=
  IsLocalWeakUpperGradient m f D ∧
  ∀ D' : X → ℝ, IsLocalWeakUpperGradient m f D' → ∀ᵐ x ∂m, D x ≤ D' x

/-- A representative of the minimal weak upper gradient (zero off its domain). -/
def weakGradient (m : Measure X) (f : X → ℝ) : X → ℝ :=
  if h : ∃ D, IsMinimalLocalWeakUpperGradient m f D then Classical.choose h
  else 0

def LocalSobolev (m : Measure X) (f : X → ℝ) : Prop :=
  LocallyL2 m f ∧ ∃ D, IsMinimalLocalWeakUpperGradient m f D

def Sobolev (m : Measure X) (f : X → ℝ) : Prop :=
  MemLp f 2 m ∧ LocalSobolev m f ∧ MemLp (weakGradient m f) 2 m

/-- Polarization of the minimal weak gradient on an infinitesimally Hilbertian space. -/
def gamma (m : Measure X) (f g : X → ℝ) (x : X) : ℝ :=
  ((weakGradient m (fun y => f y + g y) x) ^ 2 -
    (weakGradient m (fun y => f y - g y) x) ^ 2) / 4

/-- Weak nonpositive generator convention, without a global L² assumption on F. -/
def IsLaplacian (m : Measure X) (u L : X → ℝ) : Prop :=
  Sobolev m u ∧ MemLp L 2 m ∧
    ∀ v : X → ℝ, Sobolev m v →
      (∫ x, gamma m u v x ∂m) = -(∫ x, L x * v x ∂m)

def InLaplacianDomain (m : Measure X) (u : X → ℝ) : Prop :=
  ∃ L, IsLaplacian m u L

def laplacian (m : Measure X) (u : X → ℝ) : X → ℝ :=
  if h : ∃ L, IsLaplacian m u L then Classical.choose h else 0

def BoundedFunction (f : X → ℝ) : Prop := ∃ B : ℝ, ∀ x, |f x| ≤ B

def GloballyLipschitz (f : X → ℝ) : Prop := ∃ L : ℝ≥0, LipschitzWith L f

/-- Bounded globally Lipschitz Laplacian-domain functions with Sobolev Laplacian. -/
def IsTestFunction (m : Measure X) (g : X → ℝ) : Prop :=
  InLaplacianDomain m g ∧ BoundedFunction g ∧ GloballyLipschitz g ∧
    Sobolev m (laplacian m g)

/-- The weak Hessian, with ∇_(∇g)∇g = ∇(Γ(g)/2). -/
def weakHessian (m : Measure X) (F g h : X → ℝ) : ℝ :=
  -(∫ x, (gamma m h g x + h x * laplacian m g x) * gamma m F g x ∂m) -
    ∫ x, h x * gamma m F (fun y => gamma m g g y / 2) x ∂m

def WeakHessianUpperBound (m : Measure X) (F G : X → ℝ) : Prop :=
  ∀ g : X → ℝ, IsTestFunction m g → HasCompactSupport g →
    ∀ h : X → ℝ, GloballyLipschitz h → HasCompactSupport h →
      (∀ x, 0 ≤ h x) →
      weakHessian m F g h ≤ ∫ x, h x * G x * gamma m g g x ∂m

/-- Asymptotic Lipschitz slope; zero at an isolated point. -/
def localSlope (f : X → ℝ) (x : X) : ℝ≥0∞ :=
  Filter.limsup (fun y => ENNReal.ofReal (|f y - f x| / dist y x)) (𝓝[≠] x)

/-- Cheeger energy is the L² relaxation of one half the squared local slope. -/
def cheegerEnergy (m : Measure X) (f : X → ℝ) : ℝ≥0∞ :=
  if MemLp f 2 m then
    sInf {a | ∃ fs : ℕ → X → ℝ,
      (∀ n, GloballyLipschitz (fs n) ∧ MemLp (fs n) 2 m) ∧
      Tendsto (fun n => eLpNorm (fun x => fs n x - f x) 2 m) atTop (𝓝 0) ∧
      a = Filter.liminf (fun n => (2 : ℝ≥0∞)⁻¹ *
        ∫⁻ x, (localSlope (fs n) x) ^ 2 ∂m) atTop}
  else ∞

def QuadraticCheegerEnergy (m : Measure X) : Prop :=
  ∀ f g : X → ℝ, cheegerEnergy m f < ∞ → cheegerEnergy m g < ∞ →
    cheegerEnergy m (fun x => f x + g x) + cheegerEnergy m (fun x => f x - g x) =
      2 * cheegerEnergy m f + 2 * cheegerEnergy m g

/-- The unreduced Lott–Sturm–Villani distortion coefficient σ. -/
def sigmaCoeff (K N t θ : ℝ) : ℝ≥0∞ :=
  if t ≤ 0 then 0 else if 1 ≤ t then 1 else
  if θ = 0 then ENNReal.ofReal t else
  if 0 < K then
    if K * θ ^ 2 < N * Real.pi ^ 2 then
      ENNReal.ofReal (Real.sin (t * θ * Real.sqrt (K / N)) /
        Real.sin (θ * Real.sqrt (K / N)))
    else ∞
  else if K = 0 then ENNReal.ofReal t else
    ENNReal.ofReal (Real.sinh (t * θ * Real.sqrt (-K / N)) /
      Real.sinh (θ * Real.sqrt (-K / N)))

/-- The τ coefficient (not the reduced σ coefficient) in CD(K,N). -/
def tauCoeff (K N t θ : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal t) ^ (1 / N) * (sigmaCoeff K (N - 1) t θ) ^ ((N - 1) / N)

def HasSecondMoment (μ : Measure X) : Prop :=
  ∃ o : X, (∫⁻ x, (edist x o) ^ 2 ∂μ) < ∞

def IsCoupling (q : Measure (X × X)) (μ₀ μ₁ : Measure X) : Prop :=
  Measure.map Prod.fst q = μ₀ ∧ Measure.map Prod.snd q = μ₁

def QuadraticTransportCost (q : Measure (X × X)) : ℝ≥0∞ :=
  ∫⁻ p, (edist p.1 p.2) ^ 2 ∂q

def IsOptimalCoupling (q : Measure (X × X)) (μ₀ μ₁ : Measure X) : Prop :=
  IsCoupling q μ₀ μ₁ ∧ ∀ q' : Measure (X × X), IsCoupling q' μ₀ μ₁ →
    QuadraticTransportCost q ≤ QuadraticTransportCost q'

def endpointCoupling (π : Measure (Curve X)) : Measure (X × X) :=
  Measure.map (fun γ : Curve X => (γ timeZero, γ timeOne)) π

def interpolation (π : Measure (Curve X)) (t : Time) : Measure X :=
  Measure.map (fun γ : Curve X => γ t) π

/-- The positive of minus the N-Rényi entropy; singular mass contributes zero. -/
def renyiIntegral (m μ : Measure X) (N : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, (μ.rnDeriv m x) ^ (1 - 1 / N) ∂m

/-- Unreduced CD(K,N), written with the standard dynamical optimal-plan formula. -/
def CurvatureDimension (m : Measure X) (K N : ℝ) : Prop :=
  ∀ μ₀ μ₁ : Measure X,
    IsProbabilityMeasure μ₀ → IsProbabilityMeasure μ₁ →
    HasSecondMoment μ₀ → HasSecondMoment μ₁ →
    μ₀ ≪ m → μ₁ ≪ m →
    ∃ π : Measure (Curve X), IsProbabilityMeasure π ∧
      (∀ᵐ γ ∂π, IsGeodesic γ) ∧
      IsOptimalCoupling (endpointCoupling π) μ₀ μ₁ ∧
      ∀ N' : ℝ, N ≤ N' → ∀ t : Time,
        (∫⁻ γ,
          (tauCoeff K N' (1 - (t : ℝ)) (dist (γ timeZero) (γ timeOne)) *
            (μ₀.rnDeriv m (γ timeZero)) ^ (-1 / N') +
          tauCoeff K N' (t : ℝ) (dist (γ timeZero) (γ timeOne)) *
            (μ₁.rnDeriv m (γ timeOne)) ^ (-1 / N')) ∂π) ≤
        renyiIntegral m (interpolation π t) N'

def RCD (m : Measure X) (K N : ℝ) : Prop :=
  CurvatureDimension m K N ∧ QuadraticCheegerEnergy m

def FullSupport (m : Measure X) : Prop :=
  ∀ U : Set X, IsOpen U → U.Nonempty → 0 < m U

def FiniteOnBoundedSets (m : Measure X) : Prop :=
  ∀ B : Set X, Bornology.IsBounded B → m B < ∞

/-- The literal second-distributional-derivative conclusion on (0,1). -/
def CurveSecondDerivativeBound (F G : X → ℝ) (σ : Curve X) : Prop :=
  ∀ φ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
    tsupport φ ⊆ Set.Ioo (0 : ℝ) 1 → (∀ t, 0 ≤ φ t) →
    (∫ t in Set.Icc (0 : ℝ) 1,
      F (evalReal σ t) * deriv (deriv φ) t) ≤
    (dist (σ timeZero) (σ timeOne)) ^ 2 *
      ∫ t in Set.Icc (0 : ℝ) 1, G (evalReal σ t) * φ t

/-- A weak upper Hessian bound controls the second distributional derivative
along every constant-speed minimizing geodesic. -/
def every_geodesic_statement : Prop :=
  ∀ {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] (m : Measure X) (K N : ℝ) (hN : 1 < N) (hfull : FullSupport m) (hfinite : FiniteOnBoundedSets m) (hrcd : RCD m K N) (F G : X → ℝ) (hFbound : BoundedFunction F) (hFlip : GloballyLipschitz F) (hGbound : BoundedFunction G) (hGcont : Continuous G) (hHess : WeakHessianUpperBound m F G) (σ : Curve X) (hσ : IsGeodesic σ),
    CurveSecondDerivativeBound F G σ

end WeakHessian

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u_1} : Prop :=
  _root_.OAI.WeakHessian.every_geodesic_statement.{u_1}

end Problem

/- Formalization scope, from lean/docs/356.md: The formalization transfers a weak Hessian upper bound to every prescribed minimizing geodesic in an $\mathrm{RCD}(K,N)$ space with finite $N>1$. If a bounded globally Lipschitz function $F$ has weak Hessian bounded above by $G$ times the metric, where $G$ is bounded and continuous, then every constant-speed geodesic $\gamma:[0,1]\to X$ satisfies $(F\circ\gamma)''\le G(\gamma)\,d(\gamma(0),\gamma(1))^2$ in the distributional sense. Constant geodesics are included. The space is complete and separable with full support and measure finite on bounded sets; compactness and metric nonbranching are not assumed. -/
