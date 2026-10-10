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

- problem_id: E1175_refute
- collection: erdos
- question_id: erdos:1175
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1175.lean#erdos_1175
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $\kappa$ be an uncountable cardinal. Must there exist a cardinal $\lambda$ such that every graph with chromatic number $\lambda$ contains a triangle-free subgraph with chromatic number $\kappa$? Shelah proved that a negative answer is consistent when $\kappa = \lambda = \aleph_1$ (see `erdos_1175.variants.aleph_one`).
- notes: Erdos Problem 1175 -- https://www.erdosproblems.com/1175
- track: open
- answer_shape: refute
- pair_id: E1175
- pair_role: refute
- source_stem: 1175
- mathdb_ref: erdos:1175
- source_namespace: Erdos1175
- source_theorem: erdos_1175
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Cardinal SimpleGraph

namespace Problem

abbrev Target : Prop :=
    ¬ (
      ∀ (κ : Cardinal), ℵ₀ < κ →
            ∃ (μ : Cardinal),
              ∀ (V : Type*) (G : SimpleGraph V), G.chromaticCardinal = μ →
                ∃ (H : G.Subgraph), H.coe.CliqueFree 3 ∧ H.coe.chromaticCardinal = κ
    )

end Problem

/-
# Erdős Problem 1175

*Reference:* [erdosproblems.com/1175](https://www.erdosproblems.com/1175)

- [KoSh88] Komjáth, Péter and Shelah, Saharon, *Forcing constructions for uncountably chromatic
  graphs*. J. Symbolic Logic (1988), 696--707.

## Formalization notes

- **Chromatic cardinal**: `SimpleGraph.chromaticCardinal` is the cardinal-valued chromatic number
  defined in `FormalConjecturesForMathlib`. It extends the finite `chromaticNumber` (which takes
  values in `ℕ∞`) to a `Cardinal`, and is therefore able to distinguish between different infinite
  chromatic numbers.
- **Triangle-free subgraph**: a subgraph `H : G.Subgraph` is triangle-free when `H.coe.CliqueFree 3`.
  This is the standard Mathlib formulation: `CliqueFree 3` means the graph has no `K₃` as a clique.
- **Subgraph**: we use `G.Subgraph` (an arbitrary subgraph record) rather than an induced subgraph
  since the problem asks for any subgraph, not just induced ones.
-/
