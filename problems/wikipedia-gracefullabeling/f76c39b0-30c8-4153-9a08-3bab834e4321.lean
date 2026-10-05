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

- problem_id: NGracefulLabeling_graceful_tree_conjecture
- collection: wikipedia
- question_id: wikipedia:GracefulLabeling
- source: formal-conjectures
- source_locator: FormalConjectures/Wikipedia/GracefulLabeling.lean#graceful_tree_conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Every tree admits a graceful labeling. A graceful labeling of a tree $T$ with $m$ edges is an injective map $f : V \to \{0, \dots, m\}$ such that the multiset of absolute differences $|f(u) - f(v)|$ over edges $\{u,v\}$ of $T$ equals $\{1, \dots, m\}$.
- notes: Wikipedia: GracefulLabeling -- https://en.wikipedia.org/wiki/Graceful_labeling
- track: open
- answer_shape: proof
- source_stem: GracefulLabeling
- source_namespace: GracefulLabeling
- source_theorem: graceful_tree_conjecture
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: graceful_tree_one_vertex graceful_tree_two_vertex
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open SimpleGraph

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 5]
lemma graceful_tree_one_vertex :
    let T : SimpleGraph Unit := ⊥
    let m := T.edgeFinset.card
    ∃ f : Unit → ℕ,
      Function.Injective f ∧
      (∀ v, f v ≤ m) ∧
      T.edgeFinset.image (fun e =>
        e.lift ⟨fun u v => Int.natAbs ((f u : ℤ) - (f v : ℤ)),
                fun u v => by
                  show ((f u : ℤ) - f v).natAbs = ((f v : ℤ) - f u).natAbs
                  rw [← Int.natAbs_neg, neg_sub]⟩) = Finset.Icc 1 m := by
  intro T m
  use fun _ => 0
  refine ⟨fun _ _ _ => rfl, fun _ => Nat.zero_le _, ?_⟩
  simp [m, T]

@[category test, AMS 5]
lemma graceful_tree_two_vertex :
    let T : SimpleGraph (Fin 2) := ⊤
    let m := T.edgeFinset.card
    ∃ f : Fin 2 → ℕ,
      Function.Injective f ∧
      (∀ v, f v ≤ m) ∧
      T.edgeFinset.image (fun e =>
        e.lift ⟨fun u v => Int.natAbs ((f u : ℤ) - (f v : ℤ)),
                fun u v => by
                  show ((f u : ℤ) - f v).natAbs = ((f v : ℤ) - f u).natAbs
                  rw [← Int.natAbs_neg, neg_sub]⟩) = Finset.Icc 1 m := by
  intro T m
  use Fin.val
  refine ⟨Fin.val_injective, by decide, ?_⟩
  revert m T
  decide

abbrev Target : Prop :=
    ∀ {V : Type*} [Fintype V] [DecidableEq V]
        (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree),
      let m := T.edgeFinset.card
      ∃ f : V → ℕ,
        Function.Injective f ∧
        (∀ v, f v ≤ m) ∧
        T.edgeFinset.image (fun e =>
          e.lift ⟨fun u v => Int.natAbs ((f u : ℤ) - (f v : ℤ)),
                  fun u v => by
                    show ((f u : ℤ) - f v).natAbs = ((f v : ℤ) - f u).natAbs
                    rw [← Int.natAbs_neg, neg_sub]⟩) = Finset.Icc 1 m

end Problem
