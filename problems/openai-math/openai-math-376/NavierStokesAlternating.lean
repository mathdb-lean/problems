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

- problem_id: NavierStokesAlternating
- collection: openai-math
- question_id: openai-math:376
- source: openai-math
- source_locator: lean/ComparatorChallenges/NavierStokesAlternating.lean#OAI.AlternatingNS.alternating
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs viscous incompressible flows starting from rest on a fixed flat three-dimensional domain that perform universal computation under smooth external forcing. A terminating compiler turns a Turing machine and input into a finite program for the force, so a designated particle reaches a fixed region exactly when the machine halts. The viscosity is fixed, positive and computable. ([Lean](lean/docs/376.md)) We construct smooth solenoidal mean-zero forces, periodic from time zero, for which a fixed particle on a flat three-torus reaches a fixed open strip exactly when a given machine halts. The initial fluid velocity and the pressure are zero. We also realize positive diagonal maps on coding sheets by incompressible shears, with explicit normal compensation for changes of planar area, and reciprocal maps on whole boxes of positive thickness. Complete local inverses, initialization rules, and intermediate trajectory bounds connect these geometric constructions to finite computations. At any fixed positive computable viscosity, smooth forces can make a fixed fluid particle detect the halting of an arbitrary machine, starting from rest, while every mixed derivative of the force and velocity decreases faster than every inverse power of time. We give three complete memory constructions: compact moving curls, alternating fractional coordinates, and a periodic lattice on the flat three-torus. Each machine step takes one unit of physical time. The constructions retain earlier records at separated spatial scales and use an exact open detector with a shrinking signal. We construct smooth forces for three-dimensional incompressible Navier–Stokes flow, from rest at any fixed positive computable viscosity, whose velocity field detects whether a prescribed machine halts. On the unit flat torus, a pointwise test of the third velocity component uses successively shorter stirring intervals in a fixed spatial region. On $`\mathbb R^2\times\mathbb T`$, an integral test uses an expanding array of translation regions and a force with globally bounded mixed derivatives. The vertical velocity solves an advection–diffusion equation: short bursts control its pointwise error in the first construction, and a moving cutoff controls the total escaped mass in the second.
- notes: OpenAI math result family 376, Universal computation in forced Navier–Stokes flows -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/376.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.AlternatingNS.alternating
- source_theorem_count: 1
- source_solution_module: OAI.MathematicalPhysics.AlternatingFlow.Development
- source_papers: preprints/Geometric-Programs-for-Solenoidal-Forcing-September-27-2026/manuscript.pdf preprints/Computation-under-Rapidly-Vanishing-Navier-Stokes-Forcing-September-27-2026/manuscript.pdf preprints/Velocity-Field-Detection-of-Computation-in-Forced-Navier-Stokes-Flows-September-27-2026/manuscript.pdf
- source_scope_note: lean/docs/376.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

open scoped BigOperators ENNReal Topology ContDiff
open MeasureTheory

namespace AlternatingNS

abbrev Rule := ℕ × ℕ × Fin 3

abbrev Machine := ℕ × ℕ × ℕ × List ℕ × List (Option Rule)

namespace Machine

def states (M : Machine) : ℕ := M.1 + 1

def alphabet (M : Machine) : ℕ := M.2.1 + 1

def initialState (M : Machine) : ℕ := M.2.2.1

def haltingStates (M : Machine) : List ℕ := M.2.2.2.1

def table (M : Machine) : List (Option Rule) := M.2.2.2.2

def instruction (M : Machine) (q a : ℕ) : Option Rule :=
  (M.table[q * M.alphabet + a]?).join

def WellFormed (M : Machine) : Prop :=
  M.initialState < M.states ∧
  (∀ q ∈ M.haltingStates, q < M.states) ∧
  ∀ q a r, q < M.states → a < M.alphabet → M.instruction q a = some r →
    r.1 < M.states ∧ r.2.1 < M.alphabet

def ValidInput (M : Machine) (w : List ℕ) : Prop :=
  ∀ a ∈ w, a < M.alphabet

structure Configuration where
  state : ℕ
  head : ℤ
  tape : ℤ → ℕ

def isHalting (M : Machine) (c : Configuration) : Bool :=
  decide (c.state = M.states ∨ c.state ∈ M.haltingStates)

def initial (M : Machine) (w : List ℕ) : Configuration where
  state := M.initialState
  head := 0
  tape := fun i => if 0 ≤ i then w[i.toNat]?.getD 0 else 0

def step (M : Machine) (c : Configuration) : Configuration :=
  if M.isHalting c then c else
    match M.instruction c.state (c.tape c.head) with
    | none => { c with state := M.states }
    | some r =>
      { state := r.1
        head := c.head + ((r.2.2.val : ℤ) - 1)
        tape := Function.update c.tape c.head r.2.1 }

def run (M : Machine) (w : List ℕ) (n : ℕ) : Configuration :=
  (M.step)^[n] (M.initial w)

def Halts (M : Machine) (w : List ℕ) : Prop :=
  ∃ n : ℕ, M.isHalting (M.run w n) = true

end Machine

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Field (E : Type*) := ℝ → Space → E
abbrev Velocity := Field Space
abbrev Pressure := Field ℝ
abbrev MultiIndex := Fin 3 → ℕ

noncomputable section

def e (i : Fin 3) : Space := EuclideanSpace.single i 1

def dx {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin 3) (F : Field E) : Field E :=
  fun t x => fderiv ℝ (F t) x (e i)

def dt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Field E) : Field E :=
  fun t x => fderivWithin ℝ (fun s => F s x) (Set.Ici 0) t 1

def spatial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : MultiIndex) (F : Field E) : Field E :=
  (dx 0)^[α 0] ((dx 1)^[α 1] ((dx 2)^[α 2] F))

def mixed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l : ℕ) (α : MultiIndex) (F : Field E) : Field E :=
  dt^[l] (spatial α F)

def div (u : Velocity) (t : ℝ) (x : Space) : ℝ :=
  ∑ i : Fin 3, dx i u t x i

def grad (p : Pressure) (t : ℝ) (x : Space) : Space :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun i => dx i p t x)

def laplacian (u : Velocity) (t : ℝ) (x : Space) : Space :=
  ∑ i : Fin 3, dx i (dx i u) t x

def advection (u : Velocity) (t : ℝ) (x : Space) : Space :=
  fderiv ℝ (u t) x (u t x)

def residual (ν : ℝ) (u : Velocity) : Velocity :=
  fun t x => dt u t x + advection u t x - ν • laplacian u t x

def timeCylinder (T : ℝ) : Set (ℝ × Space) := Set.Icc 0 T ×ˢ Set.univ

def Smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Field E) : Prop :=
  ContDiffOn ℝ (∞) (Function.uncurry F) (Set.Ici 0 ×ˢ Set.univ)

def ClassicalRegularity (u : Velocity) (p : Pressure) : Prop :=
  (∀ x, DifferentiableOn ℝ (fun t => u t x) (Set.Ici 0)) ∧
  (∀ t, 0 ≤ t → Differentiable ℝ (u t)) ∧
  (∀ t, 0 ≤ t → ∀ i, Differentiable ℝ (dx i u t)) ∧
  (∀ t, 0 ≤ t → Differentiable ℝ (p t)) ∧
  ∀ T, 0 ≤ T →
    ContinuousOn (Function.uncurry u) (timeCylinder T) ∧
    ContinuousOn (Function.uncurry (dt u)) (timeCylinder T) ∧
    (∀ i, ContinuousOn (Function.uncurry (dx i u)) (timeCylinder T)) ∧
    (∀ i j, ContinuousOn (Function.uncurry (dx i (dx j u))) (timeCylinder T)) ∧
    ContinuousOn (Function.uncurry p) (timeCylinder T) ∧
    (∀ i, ContinuousOn (Function.uncurry (dx i p)) (timeCylinder T))

def ContinuousInH {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (F : Field E) (T : ℝ) : Prop :=
  ∀ α : MultiIndex, (∑ i, α i) ≤ k →
    ∃ g : ℝ → Lp E 2 (volume : Measure Space),
      ContinuousOn g (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc 0 T,
        ∀ᵐ x ∂(volume : Measure Space), (g t) x = spatial α F t x

def C1InL2 (u : Velocity) (T : ℝ) : Prop :=
  ∃ g g' : ℝ → Lp Space 2 (volume : Measure Space),
    ContinuousOn g (Set.Icc 0 T) ∧
    ContinuousOn g' (Set.Icc 0 T) ∧
    (∀ t ∈ Set.Icc 0 T, HasDerivWithinAt g (g' t) (Set.Icc 0 T) t) ∧
    (∀ t ∈ Set.Icc 0 T, ∀ᵐ x ∂(volume : Measure Space), (g t) x = u t x) ∧
    (∀ t ∈ Set.Icc 0 T, ∀ᵐ x ∂(volume : Measure Space), (g' t) x = dt u t x)

def CompetitorEnergyClass (u : Velocity) (p : Pressure) : Prop :=
  ∀ T, 0 ≤ T →
    ContinuousInH 2 u T ∧ C1InL2 u T ∧ ContinuousInH 1 p T ∧
    ∃ C : ℝ, ∀ t ∈ Set.Icc 0 T, ∀ x, ‖u t x‖ ≤ C

def EnergyClass (u : Velocity) (p : Pressure) : Prop :=
  CompetitorEnergyClass u p ∧
  ∀ T, 0 ≤ T → ∃ C : ℝ, ∀ t ∈ Set.Icc 0 T, ∀ x,
    ‖u t x‖ + ‖fderiv ℝ (u t) x‖ ≤ C

def NavierStokes (ν : ℝ) (f u : Velocity) (p : Pressure) : Prop :=
  ClassicalRegularity u p ∧
  (∀ x, u 0 x = 0) ∧
  ∀ t, 0 ≤ t → ∀ x,
    div u t x = 0 ∧
    dt u t x + advection u t x = -grad p t x + ν • laplacian u t x + f t x

def Rapid (F : Velocity) : Prop :=
  ∀ J l : ℕ, ∀ α : MultiIndex, ∃ C : ℝ, 0 ≤ C ∧
    ∀ t, 0 ≤ t → ∀ x,
      (1 + t + ‖x‖) ^ J * ‖mixed l α F t x‖ ≤ C

def SupportedIn (F : Velocity) (K : Set Space) : Prop :=
  ∀ t, 0 ≤ t → Function.support (F t) ⊆ K

def IsTrajectory (u : Velocity) (a : Space) (γ : ℝ → Space) : Prop :=
  γ 0 = a ∧ ∀ t, 0 ≤ t → HasDerivWithinAt γ (u t (γ t)) (Set.Ici 0) t

def observedParticle : Space := (EuclideanSpace.equiv (Fin 3) ℝ).symm ![-1, 0, 0]

abbrev RationalPoint := ℚ × ℚ × ℚ × ℚ
abbrev RationalVector := ℚ × ℚ × ℚ
abbrev IndexCode := ℕ × ℕ × ℕ
abbrev Program := Nat.Partrec.Code
abbrev FieldProgram := Program × Program × Program

def Returns {A B : Type*} [Encodable A] [Encodable B]
    (c : Program) (a : A) (b : B) : Prop :=
  Encodable.encode b ∈ c.eval (Encodable.encode a)

def index (α : IndexCode) : MultiIndex := ![α.1, α.2.1, α.2.2]

def rationalVector (q : RationalVector) : Space :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm ![(q.1 : ℝ), (q.2.1 : ℝ), (q.2.2 : ℝ)]

def rationalPoint (q : RationalPoint) : ℝ × Space :=
  ((q.1 : ℝ), rationalVector q.2)

def dyadicError (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

def ComputableReal (r : ℝ) : Prop :=
  ∃ a : ℕ → ℚ, Computable (fun n => ((a n).num, (a n).den)) ∧
    ∀ n, |r - (a n : ℝ)| ≤ dyadicError n

def ProgramFor (c : FieldProgram) (F : Velocity) : Prop :=
  (∀ (l : ℕ) (α : IndexCode) (q : RationalPoint) (k : ℕ),
    ∃ v : RationalVector, Returns c.1 (l, α, q, k) v ∧
      (0 ≤ q.1 →
        ‖rationalVector v - mixed l (index α) F (rationalPoint q).1 (rationalPoint q).2‖
          ≤ dyadicError k)) ∧
  (∀ (l : ℕ) (α : IndexCode) (R k : ℕ),
    ∃ m : ℕ, Returns c.2.1 (l, α, R, k) m ∧
      ∀ z z' : ℝ × Space,
        0 ≤ z.1 → 0 ≤ z'.1 → ‖z‖ ≤ R → ‖z'‖ ≤ R →
        ‖z - z'‖ ≤ dyadicError m →
        ‖mixed l (index α) F z.1 z.2 - mixed l (index α) F z'.1 z'.2‖ ≤ dyadicError k) ∧
  (∀ (J l : ℕ) (α : IndexCode),
    ∃ B : ℕ, Returns c.2.2 (J, l, α) B ∧
      ∀ t, 0 ≤ t → ∀ x,
        (1 + t + ‖x‖) ^ J * ‖mixed l (index α) F t x‖ ≤ B)

def AlternatingConclusion (ν : ℝ) : Prop :=
  ∃ (compileForce compileVelocity : Machine × List ℕ → FieldProgram),
    Computable compileForce ∧ Computable compileVelocity ∧
    ∃ K : Set Space, IsCompact K ∧
      ∀ (M : Machine) (w : List ℕ), M.WellFormed → M.ValidInput w →
        ∃ (f U : Velocity) (X : Space → ℝ → Space),
          ProgramFor (compileForce (M, w)) f ∧
          ProgramFor (compileVelocity (M, w)) U ∧
          Smooth f ∧ Smooth U ∧
          SupportedIn f K ∧ SupportedIn U K ∧ Rapid f ∧ Rapid U ∧
          f = residual ν U ∧
          NavierStokes ν f U (fun _ _ => 0) ∧ EnergyClass U (fun _ _ => 0) ∧
          (∀ (v : Velocity) (p : Pressure),
            NavierStokes ν f v p → CompetitorEnergyClass v p →
            ∀ t, 0 ≤ t → ∀ x, v t x = U t x ∧ p t x = 0) ∧
          (∀ a, IsTrajectory U a (X a)) ∧
          (∀ a γ, IsTrajectory U a γ → ∀ t, 0 ≤ t → γ t = X a t) ∧
          ((∃ t : ℝ, 0 ≤ t ∧ 0 < X observedParticle t 0) ↔ M.Halts w)

end
end AlternatingNS

namespace AlternatingNS

def alternating_statement : Prop :=
  ∀ (ν : ℝ) (hν : 0 < ν) (hc : ComputableReal ν),
    AlternatingConclusion ν

end AlternatingNS

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.AlternatingNS.alternating_statement

end Problem

/- Formalization scope, from lean/docs/376.md: The formalization realizes finite families of prescribed positive diagonal maps on coding sheets by smooth incompressible flows on a flat three-torus. At every positive computable viscosity, it supplies a solution starting from rest with zero pressure and a force that is divergence free, has spatial mean zero, and is one-periodic from time zero. Each map acts on every point of its source sheet, and the construction provides effective bounds for all mixed derivatives. This selected statement covers the sheet programs. The paper's fixed-particle halting detector and its reciprocal maps on solid boxes are outside its scope. The formalization proves that a fluid particle can detect arbitrary finite-machine halting using alternating-coordinate memory in smooth incompressible Navier–Stokes flows whose velocity and force decay faster than every inverse power of time, including every mixed derivative. For each fixed positive computable viscosity, the construction starts from rest and provides effective forces, unique material trajectories, and an exact equivalence between entering a fixed open detector and halting. The velocity and force share one compact support for every machine and input. The solution-uniqueness assertion uses the stated energy comparison class. The formalization constructs smooth forced three-dimensional Navier–Stokes flows from rest whose velocity fields detect whether a prescribed machine halts, at any positive computable viscosity. On the unit flat torus, halting is equivalent to the vertical velocity exceeding $1/2$ somewhere in a fixed observation strip. On $\mathbb R^2\times\mathbb T$, it is equivalent to the integral of the nonnegative vertical velocity over the observation half-plane times the circle exceeding $1/2$. The torus force is confined to a fixed horizontal region. The cylindrical force has globally bounded mixed derivatives and compact horizontal support on every finite time interval. Both constructions have effective descriptions and uniqueness within their respective smooth solution-comparison classes. The formalization realizes finitely many positive diagonal affine maps of determinant one between rational solid boxes by a smooth compactly supported divergence-free flow. Source boxes are pairwise disjoint and target boxes are pairwise disjoint, while overlap between the two families is allowed. Each map holds on a neighborhood of the entire source box, and the velocity is supported in the middle half of the time interval. It also encodes every finite machine and input in a smooth, compactly supported incompressible Navier–Stokes flow on $\mathbb R^3$ starting from rest: the particle initially at $(4,0,0)$ enters the fixed open box $(-1,2)^3$ exactly when the machine halts. One velocity works for every viscosity $\nu>0$, with zero pressure and force $f_0+\nu f_1$. Velocity and force have bounded mixed derivatives and are one-periodic after time one; the repeated velocity depends only on the machine. The force is computable for computable $\nu$. Velocity is unique among smooth zero-data solutions with $u\in C_tH_x^2\cap C_t^1L_x^2$, bounded $u$ and $\nabla u$ on finite time intervals, and pressure modulo a function of time in $C_tH_x^1$. -/
