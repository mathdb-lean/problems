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

- problem_id: GaussianMoat
- collection: openai-math
- question_id: openai-math:028
- source: openai-math
- source_locator: lean/ComparatorChallenges/GaussianMoat.lean#OAI.GaussianMoat.fullMain
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves the Gaussian moat conjecture: no infinite walk through distinct Gaussian primes can have uniformly bounded steps. More strongly, for every distance bound D, the graph joining Gaussian primes at distance at most D has uniformly bounded finite component sizes, depending only on D, including primes on the coordinate axes. ([Lean](lean/docs/028.md)) We prove the Gaussian moat conjecture: no infinite walk through distinct Gaussian primes can have bounded steps. More strongly, for each fixed finite step bound, the connected components of the Gaussian-prime graph have uniformly bounded size. This bound applies to every starting prime, including primes on the coordinate axes, and is nonexplicit. The proof constructs a finite periodic sieve obstruction using geometric sampling and information-theoretic estimates.
- notes: OpenAI math result family 028, Uniformly bounded components of Gaussian-prime graphs -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/028.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.GaussianMoat.fullMain
- source_theorem_count: 1
- source_solution_module: OAI.NumberTheory.GaussianMoat.Main
- source_main_result: OAI.GaussianMoat.fullMain
- source_papers: preprints/Bounded-Step-Walks-on-Gaussian-Primes-September-26-2026/paper.pdf
- source_scope_note: lean/docs/028.md
- source_field: NumberTheory
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace GaussianMoat

abbrev PrimeVertex := {z : GaussianInt // Irreducible z}

noncomputable def primeGraph (D : ℝ) : SimpleGraph PrimeVertex where
  Adj p q := p ≠ q ∧ dist (p.val : ℂ) (q.val : ℂ) ≤ D
  symm := by
    constructor
    intro p q h
    exact ⟨h.1.symm, by simpa only [dist_comm] using h.2⟩
  loopless := by
    constructor
    intro p h
    exact h.1 rfl

def component (D : ℝ) (p : PrimeVertex) : Set PrimeVertex :=
  {q | (primeGraph D).Reachable p q}

def MainEndpoint : Prop :=
  ∀ (D : ℝ) (z : ℕ → GaussianInt),
    (∀ t, Irreducible (z t)) → Function.Injective z →
    (∀ t, dist (z (t + 1) : ℂ) (z t : ℂ) ≤ D) → False

def UniformEndpoint : Prop :=
  ∀ D : ℝ, ∃ B : ℕ,
    (∀ p : PrimeVertex, (component D p).Finite ∧ (component D p).ncard ≤ B) ∧
    (∀ (n : ℕ) (z : Fin n → GaussianInt),
      (∀ i, Irreducible (z i)) → Function.Injective z →
      (∀ i j : Fin n, j.val = i.val + 1 → dist (z j : ℂ) (z i : ℂ) ≤ D) →
      n ≤ B)

def fullMain_statement : Prop :=
  MainEndpoint ∧ UniformEndpoint

end GaussianMoat

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.GaussianMoat.fullMain_statement

end Problem

/- Formalization scope, from lean/docs/028.md: The Gaussian moat problem asks whether an infinite walk through distinct Gaussian primes can have bounded step lengths. The formalized result gives a negative answer for every real step bound $D$. More strongly, one finite bound depending only on $D$ limits the size of every connected component of the bounded-step graph and the length of every injective bounded-step walk. Axis primes and all associates are included. No explicit function of $D$ is supplied. -/
