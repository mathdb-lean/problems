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

- problem_id: MahlerConjecture
- collection: openai-math
- question_id: openai-math:087
- source: openai-math
- source_locator: lean/ComparatorChallenges/MahlerConjecture.lean#OAI.SymmetricMahler.symmetric_mahler
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Resolves the symmetric and nonsymmetric geometric Mahler conjectures in every dimension, with Hanner polytopes and simplices as the respective volume-product minimizers and all equality cases classified. The corresponding sharp functional Mahler inequalities also hold. For n ≥ 2, every symmetric polar product $`K\times K^\circ`$ in dimension $`2n`$ has Gromov width 4. ([Lean](lean/docs/087.md)) We resolve the symmetric Mahler conjecture positively, including its equality classification. Every origin-symmetric convex body in ℝn has volume product at least $`4^n/n!`$, with equality exactly for invertible linear images of Hanner polytopes. We resolve the Mahler conjecture for general convex bodies positively. For every convex body $`K\subset\mathbb R^n`$, n ≥ 1, with Santaló point $`s(K)`$, $`|K|\,|(K-s(K))^\circ|\ge (n+1)^{n+1}/(n!)^2`$, with equality exactly for simplices. For every integer n ≥ 2 and every origin-symmetric convex body $`K\subset\mathbb R^n`$, we prove that the Gromov width of $`\mathop{\mathrm{int}}\nolimits K\times\mathop{\mathrm{int}}\nolimits K^\circ`$ is 4. We construct smooth symplectic embeddings of standard balls of every capacity $`0\lt c\lt 4`$ into this polar product. Volume preservation then resolves the symmetric Mahler conjecture positively in every dimension.
- notes: OpenAI math result family 087, The Mahler conjectures, functional inequalities and polar-product symplectic width -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/087.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.SymmetricMahler.symmetric_mahler
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.Mahler.MainTheorem
- source_main_result: OAI.SymmetricMahler.symmetric_mahler
- source_papers: preprints/The-symmetric-Mahler-conjecture-and-its-equality-cases-September-22-2026/paper.pdf preprints/The-Mahler-Conjecture-for-General-Convex-Bodies-September-22-2026/paper.pdf preprints/Symplectic-Balls-in-Symmetric-Polar-Products-September-22-2026/paper.pdf
- source_scope_note: lean/docs/087.md
- source_field: Analysis
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace SymmetricMahler

variable {I : Type*} [Fintype I]

def coordinatePolar (K : Set (I → ℝ)) : Set (I → ℝ) :=
  {p | ∀ v ∈ K, (∑ i, p i*v i) ≤ 1}

noncomputable section
open Set MeasureTheory

def symmetric_mahler_statement : Prop :=
  ∀ {n : ℕ} (hn : 1 ≤ n) {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hconv : Convex ℝ K) (hsym : ∀ x ∈ K, -x ∈ K) (hint : (interior K).Nonempty),
    (4:ℝ)^n/(Nat.factorial n:ℝ) ≤
      (volume K).toReal*(volume (coordinatePolar K)).toReal

end

end SymmetricMahler

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.SymmetricMahler.symmetric_mahler_statement

end Problem

/- Formalization scope, from lean/docs/087.md: The symmetric Mahler conjecture predicts $|K||K^\circ|\ge4^n/n!$ for every origin-symmetric convex body $K\subset\mathbb R^n$. The formalization establishes this for every $n\ge1$ and characterizes equality exactly by invertible linear images of Hanner bodies, built from intervals using Cartesian products and convex-hull joins. The nonsymmetric Mahler conjecture and the functional inequalities are not included. The general Mahler conjecture gives a sharp lower bound for the volume product of a convex body and its polar. For every $n\ge1$ and compact convex body $K\subset\mathbb R^n$ with nonempty interior, the formalization proves $\inf_{z\in\mathrm{int}\,K}|K|\,|(K-z)^\circ|\ge (n+1)^{n+1}/(n!)^2$. Equality holds exactly when $K$ is a simplex. The paper's functional inequality is outside this selected statement. For an origin-symmetric convex body $K\subset\mathbb R^n$, $n\ge2$, the formalized result determines the symplectic ball capacity of $\mathrm{int}\,K\times\mathrm{int}\,K^\circ$: its Gromov width is $4$, and every ball of capacity $0<c<4$ embeds symplectically into it. The normalization assigns capacity $\pi r^2$ to a ball of radius $r$. No boundary smoothness or strict convexity is assumed. An embedding at capacity exactly $4$ is not asserted. -/
