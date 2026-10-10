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

- problem_id: KaplanskyFinitelyPresented
- collection: openai-math
- question_id: openai-math:197
- source: openai-math
- source_locator: lean/ComparatorChallenges/KaplanskyFinitelyPresented.lean#OAI.KaplanskyCounterexample.finitelyPresented_counterexample
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs a finitely presented torsion-free nonsofic group whose group algebra over 𝔽2 is not directly finite, disproving Kaplansky's conjecture even without torsion. Companion examples give injective nonsurjective cellular automata on all configurations, refuting Gottschalk's surjunctivity conjecture. Another counterexample is an integral group-ring matrix, invertible over the rational group ring, with Fuglede–Kadison determinant strictly between zero and one, disproving the unrestricted Determinant Conjecture. ([Lean](lean/docs/197.md)) We disprove Kaplansky's direct-finiteness conjecture by constructing a finite field K of characteristic two, a finitely presented group G, and finite sums $`a,b\in K[G]`$ with $`ab=1`$ but $`ba\ne1`$. The group G is nonsofic. The same elements define a cellular automaton on KG that is injective but not surjective, disproving Gottschalk's surjunctivity conjecture. We disprove the unrestricted group-ring Determinant Conjecture. We construct a finitely generated group G and a square matrix over $`\mathbb Z[G]`$ that is invertible over $`\mathbb Q[G]`$ and has Fuglede–Kadison determinant strictly between zero and one. The logarithmic integral defining the determinant is finite. We construct a counterexample to Kaplansky's direct-finiteness conjecture in odd characteristic. For one specified odd prime p, we obtain a field K of order p4, a finitely generated group G containing torsion, and finite sums $`a,b\in K[G]`$ with $`ab=1`$ but $`ba\ne1`$. The same elements define a cellular automaton on KG that is injective but not surjective.
- notes: OpenAI math result family 197, A torsion-free group algebra that is not directly finite -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/197.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.KaplanskyCounterexample.finitelyPresented_counterexample
- source_theorem_count: 1
- source_solution_module: OAI.RingTheory.DirectFiniteness.FinitelyPresented
- source_main_result: OAI.KaplanskyCounterexample.finitelyPresented_counterexample
- source_papers: preprints/A-Counterexample-to-Kaplanskys-Direct-Finiteness-Conjecture-in-Characteristic-Two-September-23-2026/paper.pdf preprints/A-Counterexample-to-the-Group-Ring-Determinant-Conjecture-September-23-2026/paper.pdf preprints/A-Counterexample-to-Kaplanskys-Direct-Finiteness-Conjecture-in-Odd-Characteristic-September-26-2026/paper.pdf
- source_scope_note: lean/docs/197.md
- source_field: RingTheory
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI.KaplanskyCounterexample

/-- A finite characteristic-two field and a finitely presented group with odd-prime
order torsion give a counterexample to direct finiteness (paper, Theorem 1.1). -/
def finitelyPresented_counterexample_statement : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K 2),
      ∃ (G : Type) (_ : Group G) (_ : Group.IsFinitelyPresented G),
        (∃ (ℓ : ℕ) (_ : ℓ.Prime) (_ : Odd ℓ) (g : G), orderOf g = ℓ) ∧
        ∃ a_out b_out : MonoidAlgebra K G, a_out * b_out = 1 ∧ b_out * a_out ≠ 1

end OAI.KaplanskyCounterexample

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.KaplanskyCounterexample.finitelyPresented_counterexample_statement

end Problem

/- Formalization scope, from lean/docs/197.md: Kaplansky's direct-finiteness conjecture asserts that $ab=1$ implies $ba=1$ for $a,b\in K[G]$, for every field $K$ and group $G$. The formalized results construct a finite field of characteristic two and a group algebra violating this implication. One statement records the counterexample for a finitely generated group; the more detailed construction gives a finitely presented group with an element of odd prime order. The detailed construction also gives a precise recipe for choosing the data and proves that the required search terminates. The further conclusion that the group is nonsofic is outside these statements. A nonsingular integer matrix has absolute determinant at least $1$. The group-ring Determinant Conjecture extends this bound to matrices over $\mathbb Z[G]$ for every discrete group $G$. If $T_A$ is the operator induced by such a matrix $A$ on finite direct sums of $\ell^2(G)$, and $\mu_A$ is the spectral measure of $T_A^*T_A$ with respect to the group trace, the conjecture asserts $\displaystyle \int_{(0,\infty)}\log t\,d\mu_A(t)\ge0,$ with the zero spectral atom omitted. For an invertible square matrix, this is equivalent to its Fuglede–Kadison determinant being at least $1$. The formalized result contradicts that bound. It gives a finitely generated group $G$ and an $n\times n$ matrix over $\mathbb Z[G]$, with $n\ge1$, that is invertible over $\mathbb Q[G]$. Its bounded left-regular operator is invertible and has determinant strictly between $0$ and $1$. The formalization uses the trace of $\log(T^*T)$ to define the determinant for the invertible operator $T$. The paper's additional spectral-measure integral conclusion is not included. Kaplansky's direct-finiteness conjecture asserts that $ab=1$ implies $ba=1$ in every group algebra over a field. Let $p$ be the smallest prime divisor of $\bigl(\binom{1200}{600}!\bigr)^2+1$; this prime is odd. The formalized result constructs a field $K$ of order $p^4$, a finitely generated group $G$ with torsion, and elements $a,b$ violating this implication. The associated cellular automaton on all configurations $K^G$ is injective but not surjective. The formalization also contains fixed-field transfer results, separate from the statement linked below. -/
