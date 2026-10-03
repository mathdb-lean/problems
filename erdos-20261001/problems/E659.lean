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

import MathdbUtil

/-!
Converted from another corpus. `source` names it, `source_version`
pins the revision, and `source_locator` points at the one
declaration this came from. Every `source_` field describes that
declaration as it stands there, not as it stands here.

Read `track` for whether the problem is solved, which is a fact
about mathematics. `source_has_lean_proof` is a different claim --
whether that corpus holds a machine-checked proof -- and is false
for almost every problem, because it is a statement repository.

- problem_id: E659
- collection: erdos
- question_id: erdos:659
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/659.lean#erdos_659
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is there a set of $n$ points in $\mathbb{R}^2$ such that every subset of $4$ points determines at least $3$ distances, yet the total number of distinct distances is $\ll \frac{n}{\sqrt{\log n}}$? There does exist such a set: a suitable truncation of the lattice $\{(a,b\sqrt{2}): a,b\in\mathbb{Z}\}$ suffices. This construction appears to have been first considered by Moree and Osburn \cite{MoOs06}, who proved that it has $\ll \frac{n}{\sqrt{\log n}}$ many distinct distances. This construction was independently found by [Lund and Sheffer](https://adamsheffer.wordpress.com/2014/07/16/point-sets-with-few-distinct-distances/), who further noted that this configuration contains no squares or equilateral triangles. There are only six possible configurations of $4$ points which determine only $2$ distances (first noted by Erdős and Fishburn [ErFi96]), and five of them contain either a square or an equilateral triangle. The remaining configuration contains four points from a regular pentagon, and Grayzel [Gr26] (using Gemini) has noted in the comments that this configuration can also be ruled out, thus giving a complete solution to this problem. Boris Alexeev provides a formalisation of the reduction, which is conditional on Bernays' theorem (assumed as an axiom in the proof to obtain the $O(n/\sqrt{\log n})$ bound). See the [formal proof](https://github.com/plby/lean-proofs/blob/226d5fad7143dcebea2bbb5ec87f18a3a1dcea69/src/v4.24.0/ErdosProblems/Erdos659.lean).
- notes: Erdos Problem 659 -- https://www.erdosproblems.com/659
- track: solved
- answer_shape: decide
- source_stem: 659
- mathdb_ref: erdos:659
- source_namespace: Erdos659
- source_theorem: erdos_659
- source_category: research solved
- source_ams: 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open EuclideanGeometry Finset Real

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∃ A : ℕ → Finset ℝ²,
       (∀ n, #(A n) = n ∧ ∀ S ⊆ A n, #S = 4 → 3 ≤ distinctDistances S) ∧
        (fun n ↦ distinctDistances (A n)) ≪ fun n ↦ n / sqrt (log n)

end Problem
