/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Benjamin Stanley Frohman
-/
import MetriplecticNS.Basic
import FrohmanianTether.Combined
import FrohmanianTether.TetherNondegeneracy

/-!
# The metriplectic obstruction, stated against the imported Frohmanian tether kernel

This file imports `FrohmanianTether` (repository `BenFrohman/frohmanian-tether-sdiff`, pinned
in `lakefile.toml` to commit `8b7bd6741f8a54587db6a95b4a5199dcf2775f97`) and uses its
definitions and theorems directly; nothing from the tether development is re-proved or
re-stated here.

Imported objects used:
* `ArnoldGeometric.CoadjointOrbit` (state space) and `ArnoldGeometric.KineticEnergyHamiltonian`;
* `FrohmanianTether.TetherKernel`, `FrohmanianTether.DegenerateWRTKineticEnergy` (condition C2);
* `FrohmanianTether.tetherKernel_comm`, `FrohmanianTether.tetherKernel_quadratic_form`,
  `FrohmanianTether.kappa_pos`;
* `Combined.left_H_zero_of_C2_symm` and `Combined.tetherKernel_left_H_zero`;
* `TetherNondegeneracy.tetherKernel_nondegenerate` (non-vacuity of the sign obstruction).

Status of C2 for `TetherKernel` in the imported repository: **not proved** (see the module
docstring of `FrohmanianTether.Combined`). Every statement below that concerns `TetherKernel` and
needs C2 takes it, or something that implies it, as an explicit hypothesis.
-/

namespace MetriplecticNS.TetherBridge

open ArnoldGeometric

/-- View a bracket on functionals of the vorticity in the argument order used by the tether
development, `B ω F G`. -/
def tetherForm (B : Functional CoadjointOrbit → Functional CoadjointOrbit →
    Functional CoadjointOrbit) :
    CoadjointOrbit → FrohmanianTether.Functional → FrohmanianTether.Functional → ℝ :=
  fun ω F G => B F G ω

/-- A metriplectic system on the tether's state space whose energy is the tether's kinetic-energy
Hamiltonian has a metric bracket satisfying the imported condition (C2). -/
theorem metric_degenerate (sys : MetriplecticSystem CoadjointOrbit)
    (hH : sys.H = KineticEnergyHamiltonian) :
    FrohmanianTether.DegenerateWRTKineticEnergy (tetherForm sys.metric) := by
  intro F ω
  show sys.metric F KineticEnergyHamiltonian ω = 0
  rw [← hH]
  exact sys.null_H F ω

/-- **Obstruction, derived from the imported lemma.** For a metriplectic system on
`CoadjointOrbit` with `H = KineticEnergyHamiltonian`, the metric bracket vanishes with the
Hamiltonian in the first slot. Proof: `Combined.left_H_zero_of_C2_symm` applied to the metric
bracket, with symmetry from `metric_sym` and C2 from `metric_degenerate`. -/
theorem metric_left_H_zero (sys : MetriplecticSystem CoadjointOrbit)
    (hH : sys.H = KineticEnergyHamiltonian) (ω : CoadjointOrbit)
    (M : Functional CoadjointOrbit) :
    sys.metric sys.H M ω = 0 := by
  have h := Combined.left_H_zero_of_C2_symm (tetherForm sys.metric)
    (fun ω F G => by simp only [tetherForm]; rw [sys.metric_sym])
    (metric_degenerate sys hH) ω M
  rw [hH]
  exact h

/-- **Tether kernel as a metric summand.** Suppose the metric bracket of a metriplectic system
on `CoadjointOrbit` (with `H = KineticEnergyHamiltonian`) is `V + TetherKernel` for some bracket
`V` that is itself degenerate on `H`. Then `TetherKernel` satisfies C2, so by the imported
`Combined.tetherKernel_left_H_zero` it vanishes with `H` in either slot: the tether summand
contributes nothing to the energy direction, in both argument orders. -/
theorem tetherKernel_summand_no_H_coupling (sys : MetriplecticSystem CoadjointOrbit)
    (hH : sys.H = KineticEnergyHamiltonian)
    (V : Functional CoadjointOrbit → Functional CoadjointOrbit → Functional CoadjointOrbit)
    (hsplit : ∀ F G ω, sys.metric F G ω = V F G ω + FrohmanianTether.TetherKernel ω F G)
    (hV : ∀ F ω, V F KineticEnergyHamiltonian ω = 0) (ω : CoadjointOrbit)
    (M : Functional CoadjointOrbit) :
    FrohmanianTether.TetherKernel ω KineticEnergyHamiltonian M = 0 ∧
      FrohmanianTether.TetherKernel ω M KineticEnergyHamiltonian = 0 := by
  have hC2 : FrohmanianTether.DegenerateWRTKineticEnergy FrohmanianTether.TetherKernel := by
    intro F ω
    have h1 := hsplit F KineticEnergyHamiltonian ω
    have h2 := hV F ω
    have h3 : sys.metric F KineticEnergyHamiltonian ω = 0 := by
      rw [← hH]; exact sys.null_H F ω
    linarith
  exact Combined.tetherKernel_left_H_zero hC2 ω M

/-- The imported tether kernel is negative semidefinite on the diagonal:
`TetherKernel ω F F = -κ ‖ω‖² ∫ ‖Π_u δF‖² ≤ 0` (from `tetherKernel_quadratic_form`,
`kappa_pos`, and nonnegativity of the enstrophy and of the integral). -/
theorem tetherKernel_diag_nonpos (ω : CoadjointOrbit) (F : FrohmanianTether.Functional) :
    FrohmanianTether.TetherKernel ω F F ≤ 0 := by
  rw [FrohmanianTether.tetherKernel_quadratic_form]
  have hE : 0 ≤ Enstrophy ω := by
    unfold Enstrophy Casimir
    exact MeasureTheory.integral_nonneg fun x => sq_nonneg _
  have hI : 0 ≤ ∫ x, ‖ForMathlib.Pi_u (velocity_from_vorticity ω)
      (FunctionalDerivative F ω) x‖ ^ 2 ∂MeasureTheory.volume :=
    MeasureTheory.integral_nonneg fun x => sq_nonneg _
  have hk : -FrohmanianTether.kappa ≤ 0 := neg_nonpos.mpr FrohmanianTether.kappa_pos.le
  exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hk hE) hI

/-- **Sign obstruction.** The tether kernel cannot be the whole metric bracket of a metriplectic
system: if `metric F G ω = TetherKernel ω F G` for all `F G ω`, positive semidefiniteness
(`metric_pos`) and `tetherKernel_diag_nonpos` force `TetherKernel ω F F = 0` everywhere, so the
system's entropy production `(S,S)` is identically zero. Positive entropy production has to come
from another summand. -/
theorem tetherKernel_as_metric_diag_zero (sys : MetriplecticSystem CoadjointOrbit)
    (hT : ∀ F G ω, sys.metric F G ω = FrohmanianTether.TetherKernel ω F G)
    (ω : CoadjointOrbit) (F : Functional CoadjointOrbit) :
    FrohmanianTether.TetherKernel ω F F = 0 := by
  have h1 := sys.metric_pos F ω
  rw [hT] at h1
  exact le_antisymm (tetherKernel_diag_nonpos ω F) h1

/-- Consequence: with the tether kernel as the whole metric bracket, entropy is constant. -/
theorem tetherKernel_as_metric_no_entropy_production (sys : MetriplecticSystem CoadjointOrbit)
    (hT : ∀ F G ω, sys.metric F G ω = FrohmanianTether.TetherKernel ω F G)
    (ω : CoadjointOrbit) : sys.evolution sys.S ω = 0 := by
  rw [sys.entropy_production_eq, hT]
  exact tetherKernel_as_metric_diag_zero sys hT ω sys.S

/-- **Non-vacuity of the sign obstruction.** The imported tether kernel is strictly negative
somewhere on the diagonal: by the imported `TetherNondegeneracy.tetherKernel_nondegenerate` there
are `ω, F` with `TetherKernel ω F F ≠ 0`, and `tetherKernel_diag_nonpos` gives `≤ 0`. -/
theorem tetherKernel_diag_neg_somewhere :
    ∃ (ω : CoadjointOrbit) (F : FrohmanianTether.Functional),
      FrohmanianTether.TetherKernel ω F F < 0 := by
  obtain ⟨ω, φ, _, _, hne⟩ := TetherNondegeneracy.tetherKernel_nondegenerate
  exact ⟨ω, _, lt_of_le_of_ne (tetherKernel_diag_nonpos ω _) hne⟩

/-- **The tether kernel is not the metric bracket of any metriplectic system** on vorticity
fields. Proof: such a system would force `TetherKernel ω F F = 0` everywhere
(`tetherKernel_as_metric_diag_zero`), contradicting `tetherKernel_diag_neg_somewhere`. -/
theorem no_metriplectic_system_with_tether_metric :
    ¬ ∃ sys : MetriplecticSystem CoadjointOrbit,
      ∀ F G ω, sys.metric F G ω = FrohmanianTether.TetherKernel ω F G := by
  rintro ⟨sys, hT⟩
  obtain ⟨ω, F, hlt⟩ := tetherKernel_diag_neg_somewhere
  have h0 := tetherKernel_as_metric_diag_zero sys hT ω F
  linarith

end MetriplecticNS.TetherBridge
