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

- problem_id: KoebeCircleDomains
- collection: openai-math
- question_id: openai-math:071
- source: openai-math
- source_locator: lean/ComparatorChallenges/KoebeCircleDomains.lean#OAI.Problem047.koebe_circle_domain
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Resolves the existence part of Koebe's circle-domain conjecture: every domain in the Riemann sphere is conformally equivalent to a domain whose complementary components are round disks or points. It also proves that circle domains with conformally removable boundary are rigid, meaning every conformal equivalence to another circle domain is Möbius, establishing this direction of the He–Schramm conjecture. ([Lean](lean/docs/071.md)) We prove that a circle domain with conformally removable boundary is conformally rigid, with no restriction on the number of complementary components. This establishes the removability-to-rigidity direction of the He–Schramm Conjecture. We prove that every domain in the Riemann sphere is conformally equivalent to a circle domain, resolving Koebe's circle-domain conjecture positively.
- notes: OpenAI math result family 071, Koebe’s circle-domain conjecture -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/071.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Problem047.koebe_circle_domain OAI.Problem047.removability_implies_rigidity
- source_theorem_count: 2
- source_solution_module: OAI.Analysis.CircleDomains.Main
- source_papers: preprints/Removable-Boundaries-and-Rigidity-of-Circle-Domains-September-23-2026/paper.pdf preprints/Koebes-Circle-Domain-Conjecture-September-23-2026/paper.pdf
- source_scope_note: lean/docs/071.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

/-! Circle-domain uniformization and rigidity under conformal removability. -/

noncomputable section
open Set Classical
open scoped OnePoint

namespace CircleDomainRigidity

abbrev Sphere := OnePoint ℂ
abbrev Mobius := Matrix.GeneralLinearGroup (Fin 2) ℂ

def sphereInv (p : Sphere) : Sphere :=
  p.elim (0 : ℂ) (fun z ↦ if z = 0 then ∞ else (z⁻¹ : ℂ))

def finiteCoord (p : Sphere) : ℂ := p.elim 0 id

def chart (p q : Sphere) : ℂ :=
  if p = ∞ then finiteCoord (sphereInv q) else finiteCoord q

def chartSymm (p : Sphere) (z : ℂ) : Sphere :=
  if p = ∞ then sphereInv (z : Sphere) else (z : Sphere)

def IsConformalAt (f : Sphere → Sphere) (p : Sphere) : Prop :=
  ContinuousAt f p ∧ ∃ d : ℂ, d ≠ 0 ∧
    HasDerivAt (fun z ↦ chart (f p) (f (chartSymm p z))) d (chart p p)

def IsConformalOn (f : Sphere → Sphere) (U : Set Sphere) : Prop :=
  ∀ p ∈ U, IsConformalAt f p

def IsConformalEquivalence (f : Sphere → Sphere) (U V : Set Sphere) : Prop :=
  IsConformalOn f U ∧ MapsTo f U V ∧ ∃ g : Sphere → Sphere,
    IsConformalOn g V ∧ MapsTo g V U ∧
    (∀ z ∈ U, g (f z) = z) ∧ (∀ w ∈ V, f (g w) = w)

def IsRoundClosedDisk (K : Set Sphere) : Prop :=
  ∃ M : Mobius,
    K = (fun p : Sphere ↦ M • p) ''
      (((↑) : ℂ → Sphere) '' Metric.closedBall (0 : ℂ) 1)

def IsCircleDomain (U : Set Sphere) : Prop :=
  IsOpen U ∧ IsConnected U ∧
    ∀ p ∈ Uᶜ, (∃ q : Sphere, connectedComponentIn Uᶜ p = {q}) ∨
      IsRoundClosedDisk (connectedComponentIn Uᶜ p)

def OrientationPreserving (h : Sphere ≃ₜ Sphere) : Prop :=
  ContinuousMap.Homotopic (⟨h, h.continuous⟩ : C(Sphere, Sphere)) (ContinuousMap.id Sphere)

def IsConformallyRemovable (E : Set Sphere) : Prop :=
  IsCompact E ∧ ∀ h : Sphere ≃ₜ Sphere, OrientationPreserving h →
    IsConformalOn h Eᶜ → ∃ M : Mobius, ∀ p : Sphere, h p = M • p

end CircleDomainRigidity

open CircleDomainRigidity

namespace Problem047

def koebe_circle_domain_statement : Prop :=
  ∀ U : Set Sphere, IsOpen U → IsConnected U →
      ∃ (V : Set Sphere) (f : Sphere → Sphere),
        IsCircleDomain V ∧ IsConformalEquivalence f U V

def removability_implies_rigidity_statement : Prop :=
  ∀ (U V : Set Sphere) (f : Sphere → Sphere),
      IsCircleDomain U → IsCircleDomain V →
      IsConformallyRemovable (frontier U) → IsConformalEquivalence f U V →
      ∃ M : Mobius, ∀ p ∈ U, f p = M • p

end Problem047

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.Problem047.koebe_circle_domain_statement ∧
  _root_.OAI.Problem047.removability_implies_rigidity_statement

end Problem

/- Formalization scope, from lean/docs/071.md: The formalization proves the removability-to-rigidity direction of the He–Schramm conjecture. If a circle domain has conformally removable boundary, then every conformal equivalence from it to another circle domain agrees on the source with a Möbius transformation. There is no bound on the number of complementary components. The same Comparator file also states Koebe's circle-domain theorem, which gives a circle-domain representative for every domain in the Riemann sphere. Koebe's circle-domain conjecture asks whether every domain in the Riemann sphere is conformally equivalent to a circle domain, whose complementary components are round disks or points. The formalization proves this for every domain. It also proves rigidity under a separate hypothesis: a conformal equivalence between circle domains is a Möbius transformation when the source boundary is conformally removable. -/
