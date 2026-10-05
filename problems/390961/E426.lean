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

- problem_id: E426
- collection: erdos
- question_id: erdos:426
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/426.lean#erdos_426
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: We say $H$ is a unique subgraph of $G$ if there is exactly one way to find $H$ as a subgraph (not necessarily induced) of $G$. Is there a graph on $n$ vertices with $$\gg \frac{2^{\binom{n}{2}}}{n!}$$ many distinct unique subgraphs? Bradač and Christoph [BrCh24] have proved the answer is no: if $f(n)$ is the maximum number of unique subgraphs in a graph on $n$ vertices then $$f(n) = o\left(\frac{2^{\binom{n}{2}}}{n!}\right).$$ The $\gg$ below is read as: some constant $c>0$ works for arbitrarily large $n$. The negation of the proposition on the right is then exactly $f(n) = o(2^{\binom{n}{2}}/n!)$, the form in which Bradač and Christoph [BrCh24] resolved the problem. The linked file states the resolution in that negated form, as `Tendsto fSeq atTop (nhds 0)`. It counts the isomorphism classes occurring as unique subgraphs, whereas `uniqueSubgraphCount` counts their representatives $G\leq H$; uniqueness forces exactly one representative per class, so the two counts agree.
- notes: Erdos Problem 426 -- https://www.erdosproblems.com/426
- track: solved
- answer_shape: decide
- source_stem: 426
- mathdb_ref: erdos:426
- source_namespace: Erdos426
- source_theorem: erdos_426
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: isUniqueSubgraph_bot_bot
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter SimpleGraph

namespace Problem

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Sanity check: the empty graph `⊥` is a unique subgraph of itself. Its only subgraph is `⊥`
(everything `≤ ⊥` equals `⊥`), which is isomorphic to `⊥` via the identity. -/
@[category test, AMS 5]
theorem isUniqueSubgraph_bot_bot {V : Type*} : IsUniqueSubgraph (⊥ : SimpleGraph V) ⊥ := by
  refine ⟨⊥, ⟨le_refl _, ⟨Iso.refl⟩⟩, ?_⟩
  rintro G' ⟨hle, -⟩
  exact le_bot_iff.mp hle

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ c : ℝ, 0 < c ∧ ∃ᶠ (n : ℕ) in atTop, ∃ H : SimpleGraph (Fin n),
          c * ((2 : ℝ) ^ n.choose 2 / n.factorial) ≤ (uniqueSubgraphCount H : ℝ)

end Problem
