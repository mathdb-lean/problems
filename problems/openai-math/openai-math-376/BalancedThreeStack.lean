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

- problem_id: BalancedThreeStack
- collection: openai-math
- question_id: openai-math:376
- source: openai-math
- source_locator: lean/ComparatorChallenges/BalancedThreeStack.lean#OAI.BalancedTransport.balanced_three_stack_realization
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs viscous incompressible flows starting from rest on a fixed flat three-dimensional domain that perform universal computation under smooth external forcing. A terminating compiler turns a Turing machine and input into a finite program for the force, so a designated particle reaches a fixed region exactly when the machine halts. The viscosity is fixed, positive and computable. ([Lean](lean/docs/376.md)) We construct smooth solenoidal mean-zero forces, periodic from time zero, for which a fixed particle on a flat three-torus reaches a fixed open strip exactly when a given machine halts. The initial fluid velocity and the pressure are zero. We also realize positive diagonal maps on coding sheets by incompressible shears, with explicit normal compensation for changes of planar area, and reciprocal maps on whole boxes of positive thickness. Complete local inverses, initialization rules, and intermediate trajectory bounds connect these geometric constructions to finite computations. At any fixed positive computable viscosity, smooth forces can make a fixed fluid particle detect the halting of an arbitrary machine, starting from rest, while every mixed derivative of the force and velocity decreases faster than every inverse power of time. We give three complete memory constructions: compact moving curls, alternating fractional coordinates, and a periodic lattice on the flat three-torus. Each machine step takes one unit of physical time. The constructions retain earlier records at separated spatial scales and use an exact open detector with a shrinking signal. We construct smooth forces for three-dimensional incompressible Navier–Stokes flow, from rest at any fixed positive computable viscosity, whose velocity field detects whether a prescribed machine halts. On the unit flat torus, a pointwise test of the third velocity component uses successively shorter stirring intervals in a fixed spatial region. On $`\mathbb R^2\times\mathbb T`$, an integral test uses an expanding array of translation regions and a force with globally bounded mixed derivatives. The vertical velocity solves an advection–diffusion equation: short bursts control its pointwise error in the first construction, and a moving cutoff controls the total escaped mass in the second.
- notes: OpenAI math result family 376, Universal computation in forced Navier–Stokes flows -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/376.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.BalancedTransport.balanced_three_stack_realization
- source_theorem_count: 1
- source_solution_module: OAI.MathematicalPhysics.NavierStokes.BalancedTransport.MainResult
- source_papers: preprints/Geometric-Programs-for-Solenoidal-Forcing-September-27-2026/manuscript.pdf preprints/Computation-under-Rapidly-Vanishing-Navier-Stokes-Forcing-September-27-2026/manuscript.pdf preprints/Velocity-Field-Detection-of-Computation-in-Forced-Navier-Stokes-Flows-September-27-2026/manuscript.pdf
- source_scope_note: lean/docs/376.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace BalancedTransport
namespace Recorder
inductive Direction where
  | stay | left | right
  deriving DecidableEq

instance : Fintype Direction :=
  ⟨{.stay, .left, .right}, by intro d; cases d <;> simp⟩

structure Transition (Q Γ : Type*) where
  state : Q
  write : Γ
  move : Direction
end Recorder

structure FiniteMachine where
  states : ℕ
  symbols : ℕ
  initial : Fin (states + 1)
  blank : Fin (symbols + 1)
  transition : Fin (states + 1) → Fin (symbols + 1) →
    Option (Recorder.Transition (Fin (states + 1)) (Fin (symbols + 1)))

abbrev Input (M : FiniteMachine) := List (Fin (M.symbols + 1))

structure TapeConfiguration (M : FiniteMachine) where
  state : Fin (M.states + 1)
  head : ℤ
  tape : ℤ → Fin (M.symbols + 1)

def initialConfiguration (M : FiniteMachine) (w : Input M) : TapeConfiguration M :=
  ⟨M.initial, 0, fun z => if 0 ≤ z then w[z.toNat]?.getD M.blank else M.blank⟩

def machineStep (M : FiniteMachine) (c : TapeConfiguration M) : Option (TapeConfiguration M) :=
  (M.transition c.state (c.tape c.head)).map fun v =>
    ⟨v.state, c.head + (match v.move with | .stay => 0 | .left => -1 | .right => 1),
      Function.update c.tape c.head v.write⟩

def Halts (M : FiniteMachine) (w : Input M) : Prop :=
  ∃ c, Relation.ReflTransGen (fun c d => machineStep M c = some d)
    (initialConfiguration M w) c ∧ machineStep M c = none

def Recorder.Direction.number : Recorder.Direction → ℕ
  | .stay => 0
  | .left => 1
  | .right => 2

def FiniteMachine.code (M : FiniteMachine) : ℕ :=
  Encodable.encode (M.states, M.symbols, M.initial.val, M.blank.val,
    (List.finRange (M.states + 1)).map fun q =>
      (List.finRange (M.symbols + 1)).map fun a =>
        (M.transition q a).map fun v => (v.state.val, v.write.val, v.move.number))

def inputCode (M : FiniteMachine) (w : Input M) : ℕ :=
  Encodable.encode (M.code, w.map Fin.val)

abbrev Space := Fin 3 → ℝ
abbrev Field (F : Type*) := ℝ → Space → F
abbrev Velocity := Field Space
abbrev Pressure := Field ℝ
abbrev Family (F : Type*) := (M : FiniteMachine) → Input M → F
abbrev MaterialFlow := ℝ → Space → Space
abbrev MultiIndex := List (Option (Fin 3))
abbrev RationalPoint := ℚ × (Fin 3 → ℚ)

noncomputable section

open MeasureTheory
open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def timeD (v : Field F) : Field F :=
  fun t x => derivWithin (fun s => v s x) (Set.Ici 0) t

def spaceD (i : Fin 3) (v : Field F) : Field F :=
  fun t x => fderiv ℝ (v t) x (Pi.single i 1)

def mixedD : MultiIndex → Field F → Field F
  | [], v => v
  | none :: a, v => timeD (mixedD a v)
  | some i :: a, v => spaceD i (mixedD a v)

def spatialD : List (Fin 3) → Field F → Field F
  | [], v => v
  | i :: a, v => spaceD i (spatialD a v)

def Smooth (v : Field F) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ × Space => v z.1 z.2) (Set.Ici 0 ×ˢ Set.univ)

def BoundedMixed (v : Field F) : Prop :=
  ∀ a : MultiIndex, ∃ C : ℝ, 0 ≤ C ∧ ∀ t, 0 ≤ t → ∀ x, ‖mixedD a v t x‖ ≤ C

def CH (k : ℕ) (v : Field F) : Prop :=
  ∀ a : List (Fin 3), a.length ≤ k →
    ∃ V : ℝ → Lp F 2 (volume : Measure Space),
      ContinuousOn V (Set.Ici 0) ∧
      ∀ t, 0 ≤ t → (V t : Space → F) =ᵐ[volume] spatialD a v t

def C1L2 (v : Field F) : Prop :=
  ∃ V W : ℝ → Lp F 2 (volume : Measure Space),
    ContinuousOn V (Set.Ici 0) ∧ ContinuousOn W (Set.Ici 0) ∧
    ∀ t, 0 ≤ t →
      (V t : Space → F) =ᵐ[volume] v t ∧
      (W t : Space → F) =ᵐ[volume] timeD v t ∧
      HasDerivWithinAt V (W t) (Set.Ici 0) t

def div (u : Velocity) (t : ℝ) (x : Space) : ℝ :=
  ∑ i, spaceD i u t x i

def laplacian (u : Velocity) : Velocity :=
  fun t x => ∑ i, spaceD i (spaceD i u) t x

def convection (u : Velocity) : Velocity :=
  fun t x => ∑ i, (u t x i) • spaceD i u t x

def gradient (p : Pressure) (t : ℝ) (x : Space) : Space :=
  fun i => spaceD i p t x

def affineForce (f₀ f₁ : Velocity) (ν : ℝ) : Velocity :=
  fun t x => f₀ t x + ν • f₁ t x

def inertialCoefficient (u : Velocity) : Velocity :=
  fun t x => timeD u t x + convection u t x

def viscousCoefficient (u : Velocity) : Velocity :=
  fun t x => -laplacian u t x

def ZeroDataSolution (ν : ℝ) (f u : Velocity) (p : Pressure) : Prop :=
  Smooth u ∧ Smooth p ∧
  (∀ x, u 0 x = 0) ∧
  (∀ t, 0 ≤ t → ∀ x, div u t x = 0) ∧
  (∀ t, 0 ≤ t → ∀ x,
    timeD u t x + convection u t x =
      -gradient p t x + ν • laplacian u t x + f t x)

def BoundedOnFiniteSlabs (u : Velocity) : Prop :=
  ∀ T : ℝ, 0 ≤ T → ∃ C : ℝ, 0 ≤ C ∧
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      ‖u t x‖ ≤ C ∧ ∀ i : Fin 3, ‖spaceD i u t x‖ ≤ C

def ComparisonClass (u : Velocity) (p : Pressure) : Prop :=
  CH 2 u ∧ C1L2 u ∧ BoundedOnFiniteSlabs u ∧
    ∃ c : ℝ → ℝ, CH 1 (fun t x => p t x - c t)

def UniqueInComparison (ν : ℝ) (f U : Velocity) : Prop :=
  ∀ u p, ZeroDataSolution ν f u p → ComparisonClass u p →
    (∀ t, 0 ≤ t → ∀ x, u t x = U t x) ∧
    (∀ t, 0 ≤ t → ∀ x y, p t x = p t y)

def CommonCompactSupport (U f₀ f₁ : Velocity) : Prop :=
  ∃ K : Set Space, IsCompact K ∧
    ∀ t, 0 ≤ t → ∀ x, x ∉ K → U t x = 0 ∧ f₀ t x = 0 ∧ f₁ t x = 0

def PeriodicAfterOne (v : Velocity) : Prop :=
  ∀ t, 1 ≤ t → ∀ x, v (t + 1) x = v t x

def IsMaterialFlow (u : Velocity) (X : MaterialFlow) : Prop :=
  (∀ a, X 0 a = a) ∧
  ∀ a t, 0 ≤ t → HasDerivWithinAt (fun s => X s a) (u t (X t a)) (Set.Ici 0) t

def fixedLabel : Space := ![4, 0, 0]

def observer : Set Space :=
  Set.pi Set.univ (fun _ : Fin 3 => Set.Ioo (-1 : ℝ) 2)

def rationalSpace (x : Fin 3 → ℚ) : Space := fun i => (x i : ℝ)

def error (n : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ n

def EffectiveFamily (v : Family Velocity) : Prop :=
  ∃ E : (ℕ × MultiIndex × RationalPoint × ℕ) → (Fin 3 → ℚ),
  ∃ b : (ℕ × MultiIndex) → ℕ,
  ∃ R : ℕ → ℕ,
    Computable E ∧ Computable b ∧ Computable R ∧
    (∀ M w a z n, 0 ≤ z.1 → ∀ i,
      |(E (inputCode M w, a, z, n) i : ℝ) -
        mixedD a (v M w) (z.1 : ℝ) (rationalSpace z.2) i| ≤ error n) ∧
    (∀ M w a t, 0 ≤ t → ∀ x,
      ‖mixedD a (v M w) t x‖ ≤ (b (inputCode M w, a) : ℝ)) ∧
    (∀ M w t, 0 ≤ t → ∀ x,
      (R (inputCode M w) : ℝ) < ‖x‖ → v M w t x = 0)

def EffectiveFieldIn (O : Set (ℕ →. ℕ)) (v : Velocity) : Prop :=
  ∃ E : (MultiIndex × RationalPoint × ℕ) → (Fin 3 → ℚ),
  ∃ b : MultiIndex → ℕ,
    ComputableIn O E ∧ ComputableIn O b ∧
    (∀ a z n, 0 ≤ z.1 → ∀ i,
      |(E (a, z, n) i : ℝ) -
        mixedD a v (z.1 : ℝ) (rationalSpace z.2) i| ≤ error n) ∧
    (∀ a t, 0 ≤ t → ∀ x, ‖mixedD a v t x‖ ≤ (b a : ℝ))

def RealName (name : ℕ → ℚ) (x : ℝ) : Prop :=
  ∀ n, |(name n : ℝ) - x| ≤ error n

def ComputableReal (x : ℝ) : Prop :=
  ∃ name : ℕ → ℚ, Computable name ∧ RealName name x

def nameOracle (name : ℕ → ℚ) : ℕ →. ℕ :=
  fun n => Part.some (Encodable.encode (name n))

end
end BalancedTransport

namespace BalancedTransport

def balanced_three_stack_realization_statement : Prop :=
  ∃ U f₀ f₁ : Family Velocity,
    ∃ X : Family MaterialFlow,
    ∃ repeated : FiniteMachine → Velocity,
      EffectiveFamily U ∧ EffectiveFamily f₀ ∧ EffectiveFamily f₁ ∧
      (∀ M, Function.Periodic (repeated M) 1) ∧
      ∀ (M : FiniteMachine) (w : Input M),
        Smooth (U M w) ∧ Smooth (f₀ M w) ∧ Smooth (f₁ M w) ∧
        f₀ M w = inertialCoefficient (U M w) ∧
        f₁ M w = viscousCoefficient (U M w) ∧
        CommonCompactSupport (U M w) (f₀ M w) (f₁ M w) ∧
        BoundedMixed (U M w) ∧
        PeriodicAfterOne (U M w) ∧
        (∀ t, 1 ≤ t → ∀ x, U M w t x = repeated M t x) ∧
        ComparisonClass (U M w) (fun _ _ => 0) ∧
        IsMaterialFlow (U M w) (X M w) ∧
        ((∃ t : ℝ, 0 ≤ t ∧ X M w t fixedLabel ∈ observer) ↔ Halts M w) ∧
        ∀ ν : ℝ, 0 < ν →
          let f := affineForce (f₀ M w) (f₁ M w) ν
          ZeroDataSolution ν f (U M w) (fun _ _ => 0) ∧
          Smooth f ∧ BoundedMixed f ∧ PeriodicAfterOne f ∧
          UniqueInComparison ν f (U M w) ∧
          (ComputableReal ν → EffectiveFieldIn ∅ f) ∧
          (∀ name : ℕ → ℚ, RealName name ν → EffectiveFieldIn {nameOracle name} f)

end BalancedTransport

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.BalancedTransport.balanced_three_stack_realization_statement

end Problem

/- Formalization scope, from lean/docs/376.md: The formalization realizes finite families of prescribed positive diagonal maps on coding sheets by smooth incompressible flows on a flat three-torus. At every positive computable viscosity, it supplies a solution starting from rest with zero pressure and a force that is divergence free, has spatial mean zero, and is one-periodic from time zero. Each map acts on every point of its source sheet, and the construction provides effective bounds for all mixed derivatives. This selected statement covers the sheet programs. The paper's fixed-particle halting detector and its reciprocal maps on solid boxes are outside its scope. The formalization proves that a fluid particle can detect arbitrary finite-machine halting using alternating-coordinate memory in smooth incompressible Navier–Stokes flows whose velocity and force decay faster than every inverse power of time, including every mixed derivative. For each fixed positive computable viscosity, the construction starts from rest and provides effective forces, unique material trajectories, and an exact equivalence between entering a fixed open detector and halting. The velocity and force share one compact support for every machine and input. The solution-uniqueness assertion uses the stated energy comparison class. The formalization constructs smooth forced three-dimensional Navier–Stokes flows from rest whose velocity fields detect whether a prescribed machine halts, at any positive computable viscosity. On the unit flat torus, halting is equivalent to the vertical velocity exceeding $1/2$ somewhere in a fixed observation strip. On $\mathbb R^2\times\mathbb T$, it is equivalent to the integral of the nonnegative vertical velocity over the observation half-plane times the circle exceeding $1/2$. The torus force is confined to a fixed horizontal region. The cylindrical force has globally bounded mixed derivatives and compact horizontal support on every finite time interval. Both constructions have effective descriptions and uniqueness within their respective smooth solution-comparison classes. The formalization realizes finitely many positive diagonal affine maps of determinant one between rational solid boxes by a smooth compactly supported divergence-free flow. Source boxes are pairwise disjoint and target boxes are pairwise disjoint, while overlap between the two families is allowed. Each map holds on a neighborhood of the entire source box, and the velocity is supported in the middle half of the time interval. It also encodes every finite machine and input in a smooth, compactly supported incompressible Navier–Stokes flow on $\mathbb R^3$ starting from rest: the particle initially at $(4,0,0)$ enters the fixed open box $(-1,2)^3$ exactly when the machine halts. One velocity works for every viscosity $\nu>0$, with zero pressure and force $f_0+\nu f_1$. Velocity and force have bounded mixed derivatives and are one-periodic after time one; the repeated velocity depends only on the machine. The force is computable for computable $\nu$. Velocity is unique among smooth zero-data solutions with $u\in C_tH_x^2\cap C_t^1L_x^2$, bounded $u$ and $\nabla u$ on finite time intervals, and pressure modulo a function of time in $C_tH_x^1$. -/
