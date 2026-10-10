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

- problem_id: NMahler32_mahler_conjecture
- collection: wikipedia
- question_id: wikipedia:Mahler32
- source: formal-conjectures
- source_locator: FormalConjectures/Wikipedia/Mahler32.lean#mahler_conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: The **Mahler Conjecture** states that there are no Z-numbers.
- notes: Wikipedia: Mahler32 -- https://en.wikipedia.org/wiki/Mahler%27s_3/2_problem
- track: open
- answer_shape: proof
- source_stem: Mahler32
- source_namespace: Mahler32
- source_theorem: mahler_conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- For a real number `α`, define `Ω(α)` as
$$
\Omega (\alpha )=\inf _{\theta > 0}\left({\limsup _{n\rightarrow \infty }\left\lbrace
{\theta \alpha ^{n}}\right\rbrace -\liminf _{n\rightarrow \infty }\left\lbrace {\theta \alpha ^{n}}\right\rbrace }\right).
$$
-/
noncomputable def Ω (α : ℝ) : ℝ :=
  sInf {Filter.atTop.limsup (fun n ↦ Int.fract (θ * α ^ n))
    - Filter.atTop.liminf (fun n ↦ Int.fract (θ * α ^ n)) | (θ : ℝ) (_ : 0 < θ)}

abbrev Target : Prop :=
    ∀ (x : ℝ) (hx : IsZNumber x),
      False

end Problem
