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

- problem_id: SKHighTemperature
- collection: openai-math
- question_id: openai-math:227
- source: openai-math
- source_locator: lean/ComparatorChallenges/SKHighTemperature.lean#OAI.SKGap.sk_main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: For zero-field Gaussian SK heat-bath dynamics with rate-one updates per spin, proves worst-start cutoff on the $`\log n`$ scale for fixed $`0\le\beta\lt 1`$, mixing time $`n^{2/3+o(1)}`$ at β = 1, and stretched-exponential mixing from a Gibbs-sampled fixed starting configuration for β &gt; 1, in probability over disorder. At criticality, rescaled stationary and quench autocorrelation processes have universal random limits for Gaussian and Rademacher disorder; the quench limit relaxes to the stationary limit. ([Lean](lean/docs/227.md)) For every fixed inverse temperature $`0\lt \beta\lt 1`$, we prove that the unscaled spectral gap of single-site heat-bath dynamics for the zero-field Gaussian Sherrington–Kirkpatrick model is bounded away from zero with probability tending to one over the disorder. Equivalently, the Gibbs law satisfies a dimension-free Poincaré inequality for all functions. We prove worst-case total-variation cutoff for the zero-field Gaussian Sherrington–Kirkpatrick heat-bath dynamics at every fixed inverse temperature $`0\leq\beta\lt 1`$. With rate-one refresh at each spin, the cutoff location is $`\log n/(2\lambda(\beta))`$ for a positive deterministic rate $`\lambda(\beta)`$. The location for uniformly chosen single-site update attempts is n times as large. Convergence is in probability over the disorder. At the critical inverse temperature β = 1, we prove slow mixing for zero-field Gaussian Sherrington–Kirkpatrick heat-bath dynamics from typical equilibrium configurations held fixed as initial states. For every deterministic sequence $`t_n=o(n^{2/3})`$ in rate-one-per-site time, the Gibbs mass of initial states whose time-tn total-variation distance from equilibrium exceeds 1/4 tends to one in probability over the disorder. The same statement holds for every deterministic integer sequence $`k_n=o(n^{5/3})`$ of uniform-site update attempts. At every fixed inverse temperature β &gt; 1, we prove a stretched-exponential obstruction to mixing for the zero-field Sherrington–Kirkpatrick model from typical equilibrium configurations held fixed as initial states. The Gibbs mass of states whose total-variation distance from equilibrium at time $`\exp(n^{1/10000})`$ exceeds 1/4 tends to one in probability over the disorder. This holds for rate-one-per-site heat-bath dynamics and after the same stated number of discrete update attempts.
- notes: OpenAI math result family 227, Critical SK autocorrelation processes and dynamics across the temperature transition -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/227.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.SKGap.sk_main
- source_theorem_count: 1
- source_solution_module: OAI.Probability.SKGap.Main
- source_papers: preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf preprints/Cutoff-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/paper.pdf preprints/Critical-slowing-down-in-the-Sherrington-Kirkpatrick-model-September-24-2026/paper.pdf preprints/Stretched-exponential-barriers-for-typical-SK-initial-states-September-24-2026/paper.pdf
- source_scope_note: lean/docs/227.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter

namespace SKGap

abbrev Spin (n : ℕ) := Fin n → Bool
abbrev Edge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}
abbrev Disorder (n : ℕ) := Edge n → ℝ

def spinValue (b : Bool) : ℝ := if b then 1 else -1

def coupling {n : ℕ} (g : Disorder n) (i k : Fin n) : ℝ :=
  if h : i < k then g ⟨(i, k), h⟩ else
    if h : k < i then g ⟨(k, i), h⟩ else 0

def hamiltonian {n : ℕ} (g : Disorder n) (h : Fin n → ℝ) (x : Spin n) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ k, spinValue (x i) * coupling g i k * spinValue (x k) +
    ∑ i, h i * spinValue (x i)

def weight {n : ℕ} (g : Disorder n) (h : Fin n → ℝ) (x : Spin n) : ℝ :=
  Real.exp (hamiltonian g h x)

def partition {n : ℕ} (g : Disorder n) (h : Fin n → ℝ) : ℝ :=
  ∑ x, weight g h x

def mass {n : ℕ} (g : Disorder n) (h : Fin n → ℝ) (x : Spin n) : ℝ :=
  weight g h x / partition g h

def expectation {n : ℕ} (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) : ℝ :=
  ∑ x, mass g h x * f x

def variance {n : ℕ} (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) : ℝ :=
  expectation g h (fun x => (f x - expectation g h f) ^ 2)

def flip {n : ℕ} (i : Fin n) (x : Spin n) : Spin n :=
  Function.update x i (!(x i))

/-- Conditional expectation under the actual Gibbs law given all other spins. -/
def conditionalExpectation {n : ℕ} (g : Disorder n) (h : Fin n → ℝ)
    (i : Fin n) (f : Spin n → ℝ) (x : Spin n) : ℝ :=
  (weight g h x * f x + weight g h (flip i x) * f (flip i x)) /
    (weight g h x + weight g h (flip i x))

/-- Unscaled form: each site has a rate-one clock. -/
def dirichlet {n : ℕ} (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) : ℝ :=
  ∑ i, expectation g h (fun x => (f x - conditionalExpectation g h i f x) ^ 2)

def disorderLaw (β : ℝ) (n : ℕ) : Measure (Disorder n) :=
  Measure.pi (fun _ : Edge n => gaussianReal 0 (Real.toNNReal (β ^ 2 / n)))

def poincareEvent (n : ℕ) (C : ℝ) : Set (Disorder n) :=
  {g | ∀ f : Spin n → ℝ, variance g 0 f ≤ C * dirichlet g 0 f}

/-- Rayleigh quotient definition of the uniform-site discrete heat-bath gap. -/
def discreteGap {n : ℕ} (g : Disorder n) : ℝ :=
  sInf {r : ℝ | ∃ f : Spin n → ℝ, 0 < variance g 0 f ∧
    r = dirichlet g 0 f / ((n : ℝ) * variance g 0 f)}

def MainStatement (β : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    Tendsto (fun n : ℕ => disorderLaw β n (poincareEvent n C)) atTop (nhds 1) ∧
    Tendsto (fun n : ℕ => disorderLaw β n {g | 1 / (C * (n : ℝ)) ≤ discreteGap g})
      atTop (nhds 1)

def sk_main_statement : Prop :=
  ∀ (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1),
    MainStatement β

end SKGap
end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.SKGap.sk_main_statement

end Problem

/- Formalization scope, from lean/docs/227.md: For every fixed inverse temperature $0<\beta<1$, the formalization proves a dimension-independent Poincaré inequality for the zero-field Gaussian Sherrington–Kirkpatrick model with probability tending to one over the disorder. Equivalently, the unscaled single-site heat-bath spectral gap stays bounded away from zero. For dynamics that choose one site uniformly at each discrete step, the spectral gap is at least $1/(Cn)$ with probability tending to one, for a constant $C$ depending on $\beta$. The formalized supporting result proves ratio cutoff for discrete single-site heat-bath dynamics in the zero-field Gaussian Sherrington–Kirkpatrick model for $0\le\beta<1/2$. For every $0<\varepsilon<1/2$ and $\eta>0$, the probability over the disorder that $t_{\mathrm{mix}}(\varepsilon)/t_{\mathrm{mix}}(1-\varepsilon)>1+\eta$ tends to zero as $n\to\infty$. The denominator is positive for all sufficiently large sizes. The paper's full range $\beta<1$, explicit cutoff location, and continuous-time conclusion are outside this selected statement. At criticality in the zero-field Sherrington–Kirkpatrick model, the formalization proves that for every fixed $\varepsilon>0$, the continuous-time mixing time lies between $n^{2/3-\varepsilon}$ and $e^{\varepsilon n}$, and the discrete-time mixing count lies between $n^{5/3-\varepsilon}$ and $e^{\varepsilon n}$, with probability tending to one over the Gaussian disorder. The disorder has independent off-diagonal entries of variance $1/n$. Continuous updates have rate one per site; discrete time counts uniformly chosen single-site update attempts. Mixing is worst-start total variation at threshold $1/4$, with holding allowed. For deterministic times $t_n=o(n^{2/3})$ or update counts $k_n=o(n^{5/3})$, the Gibbs mass of realized starting states still farther than $1/4$ from equilibrium tends to one in probability. For every deterministic positive sequence $M_n\to\infty$, the covariance operator norm and the linear Rayleigh supremum, using the unscaled heat-bath Dirichlet form, both lie between $n^{2/3}/M_n$ and $M_n n^{2/3}$ with probability tending to one. The covariance result does not give an upper bound for the full inverse spectral gap. The formalization proves a stretched-exponential mixing obstruction for the zero-field Sherrington–Kirkpatrick model at every fixed inverse temperature $\beta>1$. At time $\exp(n^{1/10000})$, the expected Gibbs mass of initial configurations whose total-variation distance from equilibrium exceeds $1/4$ tends to one. Since this mass lies in $[0,1]$, it also tends to one in probability over the disorder. The result covers both rate-one-per-site continuous-time heat-bath dynamics and the same stated number of discrete update attempts. -/
