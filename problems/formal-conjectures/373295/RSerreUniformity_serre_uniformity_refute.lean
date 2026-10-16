/-
Copyright 2025 The Formal Conjectures Authors.
Copyright 2026 The mathdb-lean Authors.

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

import MathDBUtil

/-!
Converted from another corpus. `source` names it, `source_version`
pins the revision, and `source_locator` points at the one
declaration this came from. Every `source_` field describes that
declaration as it stands there, not as it stands here.

Read `track` for whether the problem is solved, which is a fact
about mathematics. `source_has_lean_proof` is a different claim --
whether that corpus holds a machine-checked proof -- and is false
for almost every problem, because it is a statement repository.

- problem_id: RSerreUniformity_serre_uniformity_refute
- collection: paper
- question_id: paper:SerreUniformity
- source: formal-conjectures
- source_locator: FormalConjectures/Paper/SerreUniformity.lean#serre_uniformity
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **Serre's uniformity question over $\mathbb{Q}$** [Ser72, Lem17]: is there a bound $C$ such that every non-CM elliptic curve over $\mathbb{Q}$ has surjective mod-$p$ Galois representation for every prime $p > C$?
- notes: Problem from SerreUniformity -- https://doi.org/10.1007/BF01405086
- track: open
- answer_shape: refute
- pair_id: RSerreUniformity_serre_uniformity
- pair_role: refute
- source_stem: SerreUniformity
- source_namespace: SerreUniformity
- source_theorem: serre_uniformity
- source_category: research open
- source_ams: 11 14
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/--
The thirteen rational CM $j$-invariants.
-/
def cmJInvariants : Finset ℚ :=
  {0, 1728, -3375, 8000, -32768, 54000, 287496, -884736,
    -12288000, 16581375, -884736000, -147197952000, -262537412640768000}

open scoped Classical in
/--
Every additive automorphism of $E[p]$ is induced by a Galois automorphism.
For elliptic $E$ and prime $p$, this means that the mod-$p$ representation is surjective.
-/
def HasFullTorsionAction (E : WeierstrassCurve ℚ) (p : ℕ) : Prop :=
  let T := AddSubgroup.torsionBy (E.baseChange (AlgebraicClosure ℚ)).toAffine.Point (p : ℤ)
  ∀ f : T ≃+ T, ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    ∀ P : T, WeierstrassCurve.Affine.Point.map (W' := E) σ.toAlgHom P.val = (f P).val

abbrev Target : Prop :=
    ¬ (
      ∃ C : ℕ, ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], E.j ∉ cmJInvariants →
          ∀ p : ℕ, p.Prime → C < p → HasFullTorsionAction E p
    )

end Problem
