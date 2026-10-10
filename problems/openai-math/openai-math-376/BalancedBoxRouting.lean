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

- problem_id: BalancedBoxRouting
- collection: openai-math
- question_id: openai-math:376
- source: openai-math
- source_locator: lean/ComparatorChallenges/BalancedBoxRouting.lean#OAI.BoxTransport.Routing.balanced_box_routing
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs viscous incompressible flows starting from rest on a fixed flat three-dimensional domain that perform universal computation under smooth external forcing. A terminating compiler turns a Turing machine and input into a finite program for the force, so a designated particle reaches a fixed region exactly when the machine halts. The viscosity is fixed, positive and computable. ([Lean](lean/docs/376.md)) We construct smooth solenoidal mean-zero forces, periodic from time zero, for which a fixed particle on a flat three-torus reaches a fixed open strip exactly when a given machine halts. The initial fluid velocity and the pressure are zero. We also realize positive diagonal maps on coding sheets by incompressible shears, with explicit normal compensation for changes of planar area, and reciprocal maps on whole boxes of positive thickness. Complete local inverses, initialization rules, and intermediate trajectory bounds connect these geometric constructions to finite computations. At any fixed positive computable viscosity, smooth forces can make a fixed fluid particle detect the halting of an arbitrary machine, starting from rest, while every mixed derivative of the force and velocity decreases faster than every inverse power of time. We give three complete memory constructions: compact moving curls, alternating fractional coordinates, and a periodic lattice on the flat three-torus. Each machine step takes one unit of physical time. The constructions retain earlier records at separated spatial scales and use an exact open detector with a shrinking signal. We construct smooth forces for three-dimensional incompressible Navier–Stokes flow, from rest at any fixed positive computable viscosity, whose velocity field detects whether a prescribed machine halts. On the unit flat torus, a pointwise test of the third velocity component uses successively shorter stirring intervals in a fixed spatial region. On $`\mathbb R^2\times\mathbb T`$, an integral test uses an expanding array of translation regions and a force with globally bounded mixed derivatives. The vertical velocity solves an advection–diffusion equation: short bursts control its pointwise error in the first construction, and a moving cutoff controls the total escaped mass in the second.
- notes: OpenAI math result family 376, Universal computation in forced Navier–Stokes flows -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/376.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.BoxTransport.Routing.balanced_box_routing
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.BoxTransport.Routing
- source_papers: preprints/Geometric-Programs-for-Solenoidal-Forcing-September-27-2026/manuscript.pdf preprints/Computation-under-Rapidly-Vanishing-Navier-Stokes-Forcing-September-27-2026/manuscript.pdf preprints/Velocity-Field-Detection-of-Computation-in-Forced-Navier-Stokes-Flows-September-27-2026/manuscript.pdf
- source_scope_note: lean/docs/376.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

open scoped BigOperators ContDiff

namespace BoxTransport.Routing

abbrev Space := Fin 3 → ℝ
abbrev RationalSpace := Fin 3 → ℚ
abbrev SpaceTime := ℝ × Space
abbrev RationalSpaceTime := ℚ × RationalSpace
abbrev Field := SpaceTime → Space

abbrev Axis := Option (Fin 3)

def coordinateVector (j : Fin 3) : Space := Pi.single j 1

def coordinateDirection : Axis → SpaceTime
  | none => (1, 0)
  | some j => (0, coordinateVector j)

def realPoint (q : RationalSpace) : Space := fun j => (q j : ℝ)

def realSpaceTime (q : RationalSpaceTime) : SpaceTime := (q.1, realPoint q.2)

def realBox (c r : Space) : Set Space :=
  {x | ∀ j, |x j - c j| ≤ r j}

def solidBox (a h : RationalSpace) : Set Space :=
  realBox (realPoint a) (realPoint h)

def prescribedAffine (a b h k : RationalSpace) (x : Space) : Space :=
  fun j => (b j : ℝ) + ((k j / h j : ℚ) : ℝ) * (x j - (a j : ℝ))

noncomputable def mixedDerivative : List Axis → Field → Field
  | [], U => U
  | j :: js, U => fun p => fderiv ℝ (mixedDerivative js U) p (coordinateDirection j)

abbrev RationalCode := ℕ × ℕ × ℕ

def rationalValue (q : RationalCode) : ℚ := ((q.1 : ℚ) - q.2.1) / (q.2.2 + 1)

abbrev RationalPointCode := RationalCode × RationalCode × RationalCode × RationalCode

def codeSpaceTime (q : RationalPointCode) : SpaceTime :=
  ((rationalValue q.1 : ℝ), ![(rationalValue q.2.1 : ℝ),
    (rationalValue q.2.2.1 : ℝ), (rationalValue q.2.2.2 : ℝ)])

abbrev EvaluationRequest := List Axis × RationalPointCode × ℕ × Fin 3

def Effective (U : Field) : Prop :=
  ∃ eval : EvaluationRequest → RationalCode,
    ∃ modulus : List Axis × ℕ → ℕ,
      ∃ bound : List Axis → ℕ,
        Computable eval ∧ Computable modulus ∧ Computable bound ∧
        (∀ (ds : List Axis) (q : RationalPointCode) (n : ℕ) (p : SpaceTime),
          ‖p - codeSpaceTime q‖ ≤ ((modulus (ds, n) : ℝ) + 1)⁻¹ →
          ∀ j : Fin 3,
            |mixedDerivative ds U p j - (rationalValue (eval (ds, q, n, j)) : ℝ)| ≤
              ((n : ℝ) + 1)⁻¹) ∧
        (∀ (ds : List Axis) (p : SpaceTime) (j : Fin 3),
          |mixedDerivative ds U p j| ≤ (bound ds : ℝ))

noncomputable def spatialDivergence (U : Field) (t : ℝ) (x : Space) : ℝ :=
  ∑ j : Fin 3, (fderiv ℝ (fun y => U (t, y)) x (coordinateVector j)) j

def AdmissibleField (U : Field) : Prop :=
  ContDiff ℝ ∞ U ∧ HasCompactSupport U ∧ Effective U ∧
    (∀ t x, spatialDivergence U t x = 0) ∧
    (∀ (t : ℝ) (x : Space), t ∉ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ) → U (t, x) = 0)

def IsGlobalFlow (U : Field) (Φ : ℝ → Space → Space) : Prop :=
  (∀ x, Φ 0 x = x) ∧
    (∀ t x, HasDerivAt (fun s => Φ s x) (U (t, Φ t x)) t) ∧
    (∀ (x : Space) (γ : ℝ → Space), γ 0 = x →
      (∀ t, HasDerivAt γ (U (t, γ t)) t) → ∀ t, γ t = Φ t x)

def Delivers {n : ℕ} (a b h k : Fin n → RationalSpace)
    (Φ : ℝ → Space → Space) : Prop :=
  ∀ i, ∃ O : Set Space, IsOpen O ∧ solidBox (a i) (h i) ⊆ O ∧
    ∀ x ∈ O, Φ 1 x = prescribedAffine (a i) (b i) (h i) (k i) x

def balanced_box_routing_statement : Prop :=
  ∀ (n : ℕ) (a b h k : Fin n → RationalSpace) (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j) (ha : Pairwise fun i j => Disjoint (solidBox (a i) (h i)) (solidBox (a j) (h j))) (hb : Pairwise fun i j => Disjoint (solidBox (b i) (k i)) (solidBox (b j) (k j))) (hvol : ∀ i, ∏ j : Fin 3, k i j / h i j = 1),
    ∃ U : Field, ∃ Φ : ℝ → Space → Space,
      AdmissibleField U ∧ IsGlobalFlow U Φ ∧ Delivers a b h k Φ

end BoxTransport.Routing

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.BoxTransport.Routing.balanced_box_routing_statement

end Problem

/- Formalization scope, from lean/docs/376.md: The formalization realizes finite families of prescribed positive diagonal maps on coding sheets by smooth incompressible flows on a flat three-torus. At every positive computable viscosity, it supplies a solution starting from rest with zero pressure and a force that is divergence free, has spatial mean zero, and is one-periodic from time zero. Each map acts on every point of its source sheet, and the construction provides effective bounds for all mixed derivatives. This selected statement covers the sheet programs. The paper's fixed-particle halting detector and its reciprocal maps on solid boxes are outside its scope. The formalization proves that a fluid particle can detect arbitrary finite-machine halting using alternating-coordinate memory in smooth incompressible Navier–Stokes flows whose velocity and force decay faster than every inverse power of time, including every mixed derivative. For each fixed positive computable viscosity, the construction starts from rest and provides effective forces, unique material trajectories, and an exact equivalence between entering a fixed open detector and halting. The velocity and force share one compact support for every machine and input. The solution-uniqueness assertion uses the stated energy comparison class. The formalization constructs smooth forced three-dimensional Navier–Stokes flows from rest whose velocity fields detect whether a prescribed machine halts, at any positive computable viscosity. On the unit flat torus, halting is equivalent to the vertical velocity exceeding $1/2$ somewhere in a fixed observation strip. On $\mathbb R^2\times\mathbb T$, it is equivalent to the integral of the nonnegative vertical velocity over the observation half-plane times the circle exceeding $1/2$. The torus force is confined to a fixed horizontal region. The cylindrical force has globally bounded mixed derivatives and compact horizontal support on every finite time interval. Both constructions have effective descriptions and uniqueness within their respective smooth solution-comparison classes. The formalization realizes finitely many positive diagonal affine maps of determinant one between rational solid boxes by a smooth compactly supported divergence-free flow. Source boxes are pairwise disjoint and target boxes are pairwise disjoint, while overlap between the two families is allowed. Each map holds on a neighborhood of the entire source box, and the velocity is supported in the middle half of the time interval. It also encodes every finite machine and input in a smooth, compactly supported incompressible Navier–Stokes flow on $\mathbb R^3$ starting from rest: the particle initially at $(4,0,0)$ enters the fixed open box $(-1,2)^3$ exactly when the machine halts. One velocity works for every viscosity $\nu>0$, with zero pressure and force $f_0+\nu f_1$. Velocity and force have bounded mixed derivatives and are one-periodic after time one; the repeated velocity depends only on the machine. The force is computable for computable $\nu$. Velocity is unique among smooth zero-data solutions with $u\in C_tH_x^2\cap C_t^1L_x^2$, bounded $u$ and $\nabla u$ on finite time intervals, and pressure modulo a function of time in $C_tH_x^1$. -/
