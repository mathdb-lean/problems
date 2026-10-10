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

- problem_id: E996_refute
- collection: erdos
- question_id: erdos:996
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/996.lean#erdos_996
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Does there exists a positive constant `C` such that for all `f ∈ L²[0,1]` and all lacunary sequences `n`, if `‖f - fₖ‖₂ = O(1 / log log log k ^ C)`, then for almost every `x`, `lim ∑ k ∈ Finset.range N, f (n k • x)) / N = ∫ t, f t ∂t`?
- notes: Erdos Problem 996 -- https://www.erdosproblems.com/996
- track: open
- answer_shape: refute
- pair_id: E996
- pair_role: refute
- source_stem: 996
- mathdb_ref: erdos:996
- source_namespace: Erdos996
- source_theorem: erdos_996
- source_category: research open
- source_ams: 42
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real

namespace Problem

noncomputable def fourierPartial {T : ℝ} [hT : Fact (0 < T)] (f : Lp ℂ 2 (@haarAddCircle T hT))
    (k : ℕ) : AddCircle T → ℂ :=
  fun x => ∑ i ∈ Icc (-k : ℤ) k, fourierCoeff f i • fourier i x

abbrev Target : Prop :=
    ¬ (
      ∃ (C : ℝ), 0 < C ∧ ∀ (f : Lp ℂ 2 (haarAddCircle (T := 1))) (n : ℕ → ℕ),
          IsLacunary n →
          (fun k => (eLpNorm (⇑f - fourierPartial f k) 2 (haarAddCircle (T := 1))).toReal) =O[atTop]
          (fun k => 1 / (log (log (log k))) ^ C)
          →
          ∀ᵐ x, Tendsto (fun N => (∑ k ∈ .range N, f (n k • x)) / N) atTop
          (𝓝 (∫ t, f t ∂haarAddCircle))
    )

end Problem
