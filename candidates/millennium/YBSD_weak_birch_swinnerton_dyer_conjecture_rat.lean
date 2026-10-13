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

- problem_id: YBSD_weak_birch_swinnerton_dyer_conjecture_rat
- collection: millennium
- question_id: millennium:BSD
- source: formal-conjectures
- source_locator: FormalConjectures/Millennium/BSD.lean#weak_birch_swinnerton_dyer_conjecture_rat
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: The **weak Birch and Swinnerton-Dyer conjecture** over $\mathbb{Q}$, a Clay Millennium Prize Problem.
- notes: Millennium Prize problem BSD -- https://www.claymath.org/millennium/birch-and-swinnerton-dyer-conjecture/
- track: open
- answer_shape: proof
- source_stem: BSD
- source_namespace: BSD
- source_theorem: weak_birch_swinnerton_dyer_conjecture_rat
- source_category: research open
- source_ams: 11 14
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: tools/manual_millennium.py
-/

namespace HasseWeil
variable {K : Type*} [Field K] [NumberField K]
/-- The $L$-series of `E` has the meromorphic continuation `L`: `L` is meromorphic on
$\mathbb{C}$ and agrees with `E.LSeries` on $\operatorname{Re} s > 3/2$, where the series
converges absolutely. -/
def HasMeromorphicContinuation (E : WeierstrassCurve K) (L : ℂ → ℂ) : Prop :=
  Meromorphic L ∧ ∀ s : ℂ, 3 / 2 < s.re → L s = E.LSeries s
end HasseWeil

namespace Problem

open HasseWeil

/-- The **weak Birch and Swinnerton-Dyer conjecture** for a number field $K$: for every elliptic
curve $E$ over $K$, a meromorphic continuation of its $L$-series has order
$\operatorname{rank}_{\mathbb{Z}} E(K)$ at $s = 1$. [Gross2011], Conjecture 2.10 states the
conjecture assuming only a meromorphic continuation near $s = 1$, while
`HasseWeil.HasMeromorphicContinuation` asks for one on all of $\mathbb{C}$.

The rank is `AddCommGroup.freeRank`, which requires $E(K)$ to be finitely generated. That is the
Mordell--Weil theorem, which Mathlib does not have and which this repository states as a `sorry`
in `EllipticCurveRank.mordell_weil`, so it appears here as a hypothesis. -/
def Weak (K : Type*) [Field K] [NumberField K] [DecidableEq K] : Prop :=
  ∀ (E : WeierstrassCurve K) [E.IsElliptic] [AddGroup.FG E.toAffine.Point] (L : ℂ → ℂ),
    HasMeromorphicContinuation E L →
      meromorphicOrderAt L 1 = AddCommGroup.freeRank E.toAffine.Point

abbrev Target : Prop :=
    Weak ℚ

end Problem
