/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Benjamin Stanley Frohman
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Abstract metriplectic systems

A metriplectic system on a state type `State` is a Poisson bracket (skew-symmetric), a metric
bracket (symmetric, positive semidefinite on the diagonal), an energy `H` and an entropy `S`,
with the two degeneracy conditions `{F,S} = 0` and `(F,H) = 0`. The evolution of an observable
is `Ḟ = {F,H} + (F,S)`.

What is proved here is algebra: energy conservation, nonnegative entropy production, and the
swap of the degeneracy condition for a symmetric bracket. A concrete nontrivial instance is in
`MetriplecticNS.Galerkin`; the link to the imported Frohmanian tether kernel is in
`MetriplecticNS.TetherBridge`. The Jacobi identity is not part of this structure.
-/

universe u

namespace MetriplecticNS

/-- Functionals on a state space. -/
abbrev Functional (State : Type u) := State → ℝ

/-- Abstract metriplectic system (binary-bracket form). -/
structure MetriplecticSystem (State : Type u) where
  /-- Poisson bracket (skew-symmetric). -/
  poisson : Functional State → Functional State → Functional State
  /-- Metric (dissipative) bracket (symmetric, positive semidefinite). -/
  metric : Functional State → Functional State → Functional State
  /-- Hamiltonian / total energy. -/
  H : Functional State
  /-- Entropy (Casimir of the Poisson bracket). -/
  S : Functional State
  /-- Skew-symmetry of the Poisson bracket. -/
  poisson_skew : ∀ F G, poisson F G = fun s => - (poisson G F s)
  /-- Symmetry of the metric bracket. -/
  metric_sym : ∀ F G, metric F G = metric G F
  /-- Positive semidefiniteness of the metric bracket on the diagonal. -/
  metric_pos : ∀ F s, metric F F s ≥ 0
  /-- Entropy is a Casimir: `{F,S} = 0` for every `F`. -/
  casimir_S : ∀ F s, poisson F S s = 0
  /-- Energy degeneracy: `(F,H) = 0` for every `F`. -/
  null_H : ∀ F s, metric F H s = 0

namespace MetriplecticSystem

variable {State : Type u} (sys : MetriplecticSystem State)

/-- Rate of change of a functional under the metriplectic evolution `Ḟ = {F,H} + (F,S)`. -/
def evolution (F : Functional State) : Functional State :=
  fun s => sys.poisson F sys.H s + sys.metric F sys.S s

/-- `{H,H} = 0`, from skew-symmetry alone. -/
theorem poisson_self_zero (F : Functional State) (s : State) : sys.poisson F F s = 0 := by
  have hskew := congrFun (sys.poisson_skew F F) s
  linarith

/-- `{S,H} = 0`: skew-symmetry turns it into `-{H,S}`, and `{H,S} = 0` because `S` is a Casimir
(field `casimir_S` applied to the functional `H`). -/
theorem poisson_S_H (s : State) : sys.poisson sys.S sys.H s = 0 := by
  have hskew := congrFun (sys.poisson_skew sys.S sys.H) s
  have hcas := sys.casimir_S sys.H s
  rw [hskew, hcas]
  norm_num

/-- `(H,S) = 0`: symmetry turns it into `(S,H)`, which vanishes by energy degeneracy. -/
theorem metric_H_S (s : State) : sys.metric sys.H sys.S s = 0 := by
  rw [sys.metric_sym]
  exact sys.null_H sys.S s

/-- Energy is conserved: `Ḣ = {H,H} + (H,S) = 0`. -/
theorem energy_conserved (s : State) : sys.evolution sys.H s = 0 := by
  unfold evolution
  rw [sys.poisson_self_zero, sys.metric_H_S]
  norm_num

/-- Entropy is nondecreasing: `Ṡ = {S,H} + (S,S) = (S,S) ≥ 0`. -/
theorem entropy_production (s : State) : sys.evolution sys.S s ≥ 0 := by
  unfold evolution
  rw [sys.poisson_S_H, zero_add]
  exact sys.metric_pos sys.S s

/-- Entropy production equals the metric bracket `(S,S)`. -/
theorem entropy_production_eq (s : State) : sys.evolution sys.S s = sys.metric sys.S sys.S s := by
  unfold evolution
  rw [sys.poisson_S_H, zero_add]

/-- Symmetric-swap form of the damping obstruction, for an arbitrary bracket `B` on an arbitrary
state type: if `B` is symmetric and `B(F,H) = 0` for all `F`, then `B(H,F) = 0` for all `F`.
The version stated against the imported `TetherKernel` is
`MetriplecticNS.TetherBridge.metric_left_H_zero` and its corollaries. -/
theorem tether_damping_obstruction
    (B : Functional State → Functional State → Functional State)
    (h_sym : ∀ F G, B F G = B G F)
    (h_null : ∀ F s, B F sys.H s = 0) :
    ∀ F s, B sys.H F s = 0 := by
  intro F s
  rw [h_sym]
  exact h_null F s

end MetriplecticSystem

end MetriplecticNS
