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

- problem_id: SolenoidalSheetPrograms
- collection: openai-math
- question_id: openai-math:376
- source: openai-math
- source_locator: lean/ComparatorChallenges/SolenoidalSheetPrograms.lean#OAI.Solenoidal.sheet_theorem
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs viscous incompressible flows starting from rest on a fixed flat three-dimensional domain that perform universal computation under smooth external forcing. A terminating compiler turns a Turing machine and input into a finite program for the force, so a designated particle reaches a fixed region exactly when the machine halts. The viscosity is fixed, positive and computable. ([Lean](lean/docs/376.md)) We construct smooth solenoidal mean-zero forces, periodic from time zero, for which a fixed particle on a flat three-torus reaches a fixed open strip exactly when a given machine halts. The initial fluid velocity and the pressure are zero. We also realize positive diagonal maps on coding sheets by incompressible shears, with explicit normal compensation for changes of planar area, and reciprocal maps on whole boxes of positive thickness. Complete local inverses, initialization rules, and intermediate trajectory bounds connect these geometric constructions to finite computations. At any fixed positive computable viscosity, smooth forces can make a fixed fluid particle detect the halting of an arbitrary machine, starting from rest, while every mixed derivative of the force and velocity decreases faster than every inverse power of time. We give three complete memory constructions: compact moving curls, alternating fractional coordinates, and a periodic lattice on the flat three-torus. Each machine step takes one unit of physical time. The constructions retain earlier records at separated spatial scales and use an exact open detector with a shrinking signal. We construct smooth forces for three-dimensional incompressible Navier–Stokes flow, from rest at any fixed positive computable viscosity, whose velocity field detects whether a prescribed machine halts. On the unit flat torus, a pointwise test of the third velocity component uses successively shorter stirring intervals in a fixed spatial region. On $`\mathbb R^2\times\mathbb T`$, an integral test uses an expanding array of translation regions and a force with globally bounded mixed derivatives. The vertical velocity solves an advection–diffusion equation: short bursts control its pointwise error in the first construction, and a moving cutoff controls the total escaped mass in the second.
- notes: OpenAI math result family 376, Universal computation in forced Navier–Stokes flows -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/376.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Solenoidal.sheet_theorem
- source_theorem_count: 1
- source_solution_module: OAI.MathematicalPhysics.SheetFlows.SheetProgram
- source_papers: preprints/Geometric-Programs-for-Solenoidal-Forcing-September-27-2026/manuscript.pdf preprints/Computation-under-Rapidly-Vanishing-Navier-Stokes-Forcing-September-27-2026/manuscript.pdf preprints/Velocity-Field-Detection-of-Computation-in-Forced-Navier-Stokes-Flows-September-27-2026/manuscript.pdf
- source_scope_note: lean/docs/376.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace Solenoidal

abbrev Plane := Fin 2 → ℝ
abbrev Space := Fin 3 → ℝ
abbrev SpaceTime := ℝ × Space
abbrev Field := ℝ → Space → Space
abbrev Pressure := ℝ → Space → ℝ
abbrev Torus := Fin 3 → AddCircle (10 : ℝ)

def toTorus (x : Space) : Torus := fun i => (x i : AddCircle (10 : ℝ))

def sheet (y : Plane) : Space := ![y 0, y 1, 2]

structure Rectangle where
  lower : Fin 2 → ℚ
  upper : Fin 2 → ℚ
  positive : ∀ j, lower j < upper j

namespace Rectangle

def carrier (R : Rectangle) : Set Plane :=
  {y | ∀ j, (R.lower j : ℝ) ≤ y j ∧ y j ≤ (R.upper j : ℝ)}

def center (R : Rectangle) : Plane :=
  fun j => ((R.lower j : ℝ) + (R.upper j : ℝ)) / 2

def halfWidth (R : Rectangle) : Plane :=
  fun j => ((R.upper j : ℝ) - (R.lower j : ℝ)) / 2

def inCodingSquare (R : Rectangle) : Prop :=
  ∀ j, 2 ≤ R.lower j ∧ R.upper j ≤ 3

end Rectangle

def SeparatelySeparated {N : ℕ} (R : Fin N → Rectangle) : Prop :=
  ∀ i j, i ≠ j → ∃ δ : ℝ, 0 < δ ∧
    ∀ x ∈ (R i).carrier, ∀ y ∈ (R j).carrier, δ ≤ ‖x - y‖

def diagonalMap (P Q : Rectangle) (r : Fin 2 → ℚ) (y : Plane) : Plane :=
  fun j => Q.center j + (r j : ℝ) * (y j - P.center j)

structure SheetData (N : ℕ) where
  source : Fin N → Rectangle
  target : Fin N → Rectangle
  source_inside : ∀ i, (source i).inCodingSquare
  target_inside : ∀ i, (target i).inCodingSquare
  source_separated : SeparatelySeparated source
  target_separated : SeparatelySeparated target
  ratio : Fin N → Fin 2 → ℚ
  ratio_positive : ∀ i j, 0 < ratio i j
  image_eq : ∀ i,
    diagonalMap (source i) (target i) (ratio i) '' (source i).carrier =
      (target i).carrier

def deck (k : Fin 3 → ℤ) : Space := fun j => 10 * (k j : ℝ)

def SpatiallyPeriodic {E : Type*} (g : ℝ → Space → E) : Prop :=
  ∀ t x k, g t (x + deck k) = g t x

def fundamentalCell : Set Space :=
  Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 10)

def basis (j : Fin 3) : Space := Pi.single j 1

def spatialPartial (u : Field) (j : Fin 3) : Field :=
  fun t x => fderiv ℝ (u t) x (basis j)

def timePartial (u : Field) : Field :=
  fun t x => derivWithin (fun s => u s x) (Set.Ici 0) t

def divergence (u : Field) (t : ℝ) (x : Space) : ℝ :=
  ∑ j : Fin 3, spatialPartial u j t x j

def laplacian (u : Field) : Field :=
  fun t x => ∑ j : Fin 3, spatialPartial (spatialPartial u j) j t x

def advection (u : Field) : Field :=
  fun t x => fderiv ℝ (u t) x (u t x)

def gradient (p : Pressure) : Field :=
  fun t x j => fderiv ℝ (p t) x (basis j)

def DivergenceFree (u : Field) : Prop := ∀ t x, divergence u t x = 0

def MeanZero (u : Field) : Prop :=
  ∀ t, (∫ x in fundamentalCell, u t x) = 0

def Smooth (u : Field) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) (fun z : SpaceTime => u z.1 z.2)

def OnePeriodic (u : Field) : Prop := ∀ t x, u (t + 1) x = u t x

def IntegerCollars (u : Field) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ n : ℤ, ∀ t x, |t - (n : ℝ)| < ε → u t x = 0

def cylinder (T : ℝ) : Set SpaceTime := Set.Icc 0 T ×ˢ Set.univ

structure ClassicalSolution (ν : ℝ) (f u : Field) (p : Pressure) : Prop where
  spatial_periodic_u : SpatiallyPeriodic u
  spatial_periodic_p : SpatiallyPeriodic p
  continuous_u : ∀ T, 0 ≤ T →
    ContinuousOn (fun z : SpaceTime => u z.1 z.2) (cylinder T)
  differentiable_t : ∀ t, 0 ≤ t → ∀ x,
    DifferentiableWithinAt ℝ (fun s => u s x) (Set.Ici 0) t
  continuous_t : ∀ T, 0 ≤ T →
    ContinuousOn (fun z : SpaceTime => timePartial u z.1 z.2) (cylinder T)
  differentiable_x : ∀ t, 0 ≤ t → Differentiable ℝ (u t)
  continuous_x : ∀ T, 0 ≤ T → ∀ j,
    ContinuousOn (fun z : SpaceTime => spatialPartial u j z.1 z.2) (cylinder T)
  differentiable_xx : ∀ t, 0 ≤ t → ∀ j,
    Differentiable ℝ (spatialPartial u j t)
  continuous_xx : ∀ T, 0 ≤ T → ∀ i j,
    ContinuousOn (fun z : SpaceTime => spatialPartial (spatialPartial u i) j z.1 z.2)
      (cylinder T)
  continuous_p : ∀ T, 0 ≤ T →
    ContinuousOn (fun z : SpaceTime => p z.1 z.2) (cylinder T)
  differentiable_p : ∀ t, 0 ≤ t → Differentiable ℝ (p t)
  continuous_px : ∀ T, 0 ≤ T →
    ContinuousOn (fun z : SpaceTime => gradient p z.1 z.2) (cylinder T)
  pressure_mean_zero : ∀ t, 0 ≤ t → (∫ x in fundamentalCell, p t x) = 0
  incompressible : ∀ t, 0 ≤ t → ∀ x, divergence u t x = 0
  initial : ∀ x, u 0 x = 0
  equation : ∀ t, 0 ≤ t → ∀ x,
    timePartial u t x + advection u t x =
      -gradient p t x + ν • laplacian u t x + f t x

def MaterialFlow (u : Field) (X : ℝ → Space → Space) : Prop :=
  (∀ a, X 0 a = a) ∧
  (∀ a, ContinuousOn (fun t => X t a) (Set.Ici 0)) ∧
  (∀ a t, 0 ≤ t →
    HasDerivWithinAt (fun s => X s a) (u t (X t a)) (Set.Ici 0) t)

def spacetimeBasis : Fin 4 → SpaceTime :=
  ![(1, 0), (0, basis 0), (0, basis 1), (0, basis 2)]

def mixedDerivative (u : Field) : List (Fin 4) → SpaceTime → Space
  | [] => fun z => u z.1 z.2
  | j :: α => fun z => fderiv ℝ (mixedDerivative u α) z (spacetimeBasis j)

def flatten (z : SpaceTime) : Fin 4 → ℝ := ![z.1, z.2 0, z.2 1, z.2 2]

def NamesReal (c : Nat.Partrec.Code) (r : ℝ) : Prop :=
  ∀ n : ℕ, ∃ q : ℚ, Encodable.encode q ∈ c.eval n ∧
    |(q : ℝ) - r| ≤ (1 / 2 : ℝ) ^ n

def ComputableReal (r : ℝ) : Prop := ∃ c, NamesReal c r

def NamesPoint (c : Nat.Partrec.Code) (z : SpaceTime) : Prop :=
  ∀ n : ℕ, ∃ q : Fin 4 → ℚ,
    @Encodable.encode (Fin 4 → ℚ) Encodable.finArrow q ∈ c.eval n ∧
    ‖(fun j => (q j : ℝ)) - flatten z‖ ≤ (1 / 2 : ℝ) ^ n

def Effective (u : Field) : Prop :=
  ∃ e : Nat.Partrec.Code, ∀ α : List (Fin 4), ∀ c : Nat.Partrec.Code,
    ∀ z : SpaceTime, NamesPoint c z → ∀ ε : ℚ, 0 < ε →
      ∃ q : Fin 3 → ℚ,
        @Encodable.encode (Fin 3 → ℚ) Encodable.finArrow q ∈
          e.eval (Encodable.encode (α, c, ε)) ∧
          ‖(fun j => (q j : ℝ)) - mixedDerivative u α z‖ < (ε : ℝ)

def EffectiveBounds (u : Field) : Prop :=
  ∃ e : Nat.Partrec.Code, ∀ α : List (Fin 4), ∃ B : ℚ,
    Encodable.encode B ∈ e.eval (Encodable.encode α) ∧ 0 ≤ B ∧
      ∀ z : SpaceTime, ‖mixedDerivative u α z‖ ≤ (B : ℝ)

def sheet_theorem_statement : Prop :=
  ∀ {N : ℕ} (D : SheetData N) (ν : ℝ) (hν : 0 < ν) (hνcomp : ComputableReal ν),
    ∃ f u : Field, ∃ X : ℝ → Space → Space,
      SpatiallyPeriodic f ∧ SpatiallyPeriodic u ∧
      Smooth f ∧ Smooth u ∧ Effective f ∧
      MeanZero f ∧ DivergenceFree f ∧ OnePeriodic f ∧
      ClassicalSolution ν f u (fun _ _ => 0) ∧
      (∀ v : Field, ∀ p : Pressure, ClassicalSolution ν f v p →
        ∀ t, 0 ≤ t → ∀ x, v t x = u t x ∧ p t x = 0) ∧
      MaterialFlow u X ∧
      (∀ i : Fin N, ∀ y ∈ (D.source i).carrier,
        toTorus (X 1 (sheet y)) =
          toTorus (sheet (diagonalMap (D.source i) (D.target i) (D.ratio i) y))) ∧
      IntegerCollars u ∧ (∀ t x, advection u t x = 0) ∧
      EffectiveBounds f ∧ EffectiveBounds u ∧
      (N = 0 → f = 0 ∧ u = 0)

end Solenoidal

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.Solenoidal.sheet_theorem_statement

end Problem

/- Formalization scope, from lean/docs/376.md: The formalization realizes finite families of prescribed positive diagonal maps on coding sheets by smooth incompressible flows on a flat three-torus. At every positive computable viscosity, it supplies a solution starting from rest with zero pressure and a force that is divergence free, has spatial mean zero, and is one-periodic from time zero. Each map acts on every point of its source sheet, and the construction provides effective bounds for all mixed derivatives. This selected statement covers the sheet programs. The paper's fixed-particle halting detector and its reciprocal maps on solid boxes are outside its scope. The formalization proves that a fluid particle can detect arbitrary finite-machine halting using alternating-coordinate memory in smooth incompressible Navier–Stokes flows whose velocity and force decay faster than every inverse power of time, including every mixed derivative. For each fixed positive computable viscosity, the construction starts from rest and provides effective forces, unique material trajectories, and an exact equivalence between entering a fixed open detector and halting. The velocity and force share one compact support for every machine and input. The solution-uniqueness assertion uses the stated energy comparison class. The formalization constructs smooth forced three-dimensional Navier–Stokes flows from rest whose velocity fields detect whether a prescribed machine halts, at any positive computable viscosity. On the unit flat torus, halting is equivalent to the vertical velocity exceeding $1/2$ somewhere in a fixed observation strip. On $\mathbb R^2\times\mathbb T$, it is equivalent to the integral of the nonnegative vertical velocity over the observation half-plane times the circle exceeding $1/2$. The torus force is confined to a fixed horizontal region. The cylindrical force has globally bounded mixed derivatives and compact horizontal support on every finite time interval. Both constructions have effective descriptions and uniqueness within their respective smooth solution-comparison classes. The formalization realizes finitely many positive diagonal affine maps of determinant one between rational solid boxes by a smooth compactly supported divergence-free flow. Source boxes are pairwise disjoint and target boxes are pairwise disjoint, while overlap between the two families is allowed. Each map holds on a neighborhood of the entire source box, and the velocity is supported in the middle half of the time interval. It also encodes every finite machine and input in a smooth, compactly supported incompressible Navier–Stokes flow on $\mathbb R^3$ starting from rest: the particle initially at $(4,0,0)$ enters the fixed open box $(-1,2)^3$ exactly when the machine halts. One velocity works for every viscosity $\nu>0$, with zero pressure and force $f_0+\nu f_1$. Velocity and force have bounded mixed derivatives and are one-periodic after time one; the repeated velocity depends only on the machine. The force is computable for computable $\nu$. Velocity is unique among smooth zero-data solutions with $u\in C_tH_x^2\cap C_t^1L_x^2$, bounded $u$ and $\nabla u$ on finite time intervals, and pressure modulo a function of time in $C_tH_x^1$. -/
