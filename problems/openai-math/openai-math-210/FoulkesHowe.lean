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

- problem_id: FoulkesHowe
- collection: openai-math
- question_id: openai-math:210
- source: openai-math
- source_locator: lean/ComparatorChallenges/FoulkesHowe.lean#OAI.Problem346.canonical_foulkes_howe_surjective
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves the sixth case of Foulkes’ conjecture: $`\mathop{\mathrm{Sym}}\nolimits ^6(\mathop{\mathrm{Sym}}\nolimits ^bV)`$ embeds equivariantly in $`\mathop{\mathrm{Sym}}\nolimits ^b(\mathop{\mathrm{Sym}}\nolimits ^6V)`$ for every b ≥ 6 and finite-dimensional complex V. More generally, the canonical multiplication map $`\mathop{\mathrm{Sym}}\nolimits ^b(\mathop{\mathrm{Sym}}\nolimits ^aV)\to\mathop{\mathrm{Sym}}\nolimits ^a(\mathop{\mathrm{Sym}}\nolimits ^bV)`$ is surjective for a ≥ 2 and $`b\ge a(a-1)`$, giving dimension-independent quadratic stabilization. ([Lean](lean/docs/210.md)) For every finite-dimensional complex vector space V, we prove that the canonical Foulkes–Howe map $`\mathop{\mathrm{Sym}}\nolimits ^b(\mathop{\mathrm{Sym}}\nolimits ^a V)\longrightarrow\mathop{\mathrm{Sym}}\nolimits ^a(\mathop{\mathrm{Sym}}\nolimits ^b V)`$ is surjective whenever a ≥ 2 and $`b\ge a(a-1)`$. This gives a quadratic stabilization bound independent of $`\dim V`$.
- notes: OpenAI math result family 210, Foulkes' conjecture for sixth powers and quadratic stabilization -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/210.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Problem346.canonical_foulkes_howe_surjective
- source_theorem_count: 1
- source_solution_module: OAI.RepresentationTheory.FoulkesHowe.Stabilization
- source_main_result: OAI.Problem346.canonical_foulkes_howe_surjective
- source_papers: preprints/Quadratic-Stabilization-of-the-Canonical-Foulkes-Howe-Map-September-25-2026/paper.pdf
- source_scope_note: lean/docs/210.md
- source_field: RepresentationTheory
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

open scoped BigOperators
universe u

namespace Problem346

def symMonomialRaw (n : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V]
    (v : Fin n → V) : SymmetricAlgebra ℂ V :=
  ∏ i : Fin n, SymmetricAlgebra.ι ℂ V (v i)

def symPowSubmodule (n : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V] :
    Submodule ℂ (SymmetricAlgebra ℂ V) :=
  Submodule.span ℂ (Set.range (symMonomialRaw n V))

abbrev SymPow (n : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V] :=
  ↥(symPowSubmodule n V)

def symMonomial (n : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V]
    (v : Fin n → V) : SymPow n V :=
  ⟨symMonomialRaw n V v, Submodule.subset_span (Set.mem_range_self v)⟩

def foulkesFormula (a b : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V]
    (v : Fin b → Fin a → V) : SymPow a (SymPow b V) := by
  classical
  exact
    ((a.factorial : ℂ) ^ b)⁻¹ •
      ∑ σ : Fin b → Equiv.Perm (Fin a),
        symMonomial a (SymPow b V)
          (fun i => symMonomial b V (fun j => v j ((σ j) i)))

def IsFoulkesMap (a b : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V]
    (μ : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V)) : Prop :=
  ∀ v : Fin b → Fin a → V,
    μ (symMonomial b (SymPow a V) (fun j => symMonomial a V (v j))) =
      foulkesFormula a b V v

def canonical_foulkes_howe_surjective_statement : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a b : ℕ), 2 ≤ a → a * (a - 1) ≤ b → ∃ μ : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V), IsFoulkesMap a b V μ ∧ Function.Surjective μ ∧ ∀ ν : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V), IsFoulkesMap a b V ν → ν = μ

end Problem346

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u} : Prop :=
  _root_.OAI.Problem346.canonical_foulkes_howe_surjective_statement.{u}

end Problem

/- Formalization scope, from lean/docs/210.md: The formalized result proves surjectivity of the canonical averaged Foulkes–Howe map $\mathrm{Sym}^b(\mathrm{Sym}^a\,V)\to\mathrm{Sym}^a(\mathrm{Sym}^b\,V)$ for every finite-dimensional complex vector space, $a\ge2$, and $b\ge a(a-1)$. It also covers the bijective $a=1$ case, the vanishing-on-products consequence, and the corresponding equivariant embedding in the reverse direction. The sixth-power specialization is covered for $b\ge30$; the companion's full range $b\ge6$ is not included. -/
