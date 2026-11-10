/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Benjamin Stanley Frohman
-/
import MetriplecticNS.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# A concrete finite-dimensional metriplectic system with viscous dissipation

State: `x = (u, s)` with `u ∈ ℝⁿ` (velocity coefficients, `EuclideanSpace ℝ (Fin n)`) and an
entropy / internal-energy coordinate `s ∈ ℝ`.

* Energy `H(u,s) = ½‖u‖² + s` (kinetic energy plus internal energy at unit temperature).
* Entropy `S(u,s) = s`.
* Poisson bracket `{F,G}(x) = Σᵢⱼ ∂ᵤᵢF · J(u)ᵢⱼ · ∂ᵤⱼG` for a state-dependent skew matrix `J(u)`.
* Metric bracket `(F,G)(x) = Σᵢ νᵢ (PF)ᵢ (PG)ᵢ`, where `(PF)ᵢ = ∂ᵤᵢF − (∂ₛF) uᵢ` and `νᵢ ≥ 0`
  is a diagonal viscosity matrix (for a Fourier truncation one would take `νᵢ = ν |kᵢ|²`).

All partial derivatives are Fréchet derivatives (`fderiv`) of the functional, so the brackets are
defined on every functional `State → ℝ`. All five structure axioms of `MetriplecticSystem` are
proved, and the induced equations of motion are computed:

`u̇ᵢ = (J(u) u)ᵢ − νᵢ uᵢ`, `ṡ = Σᵢ νᵢ uᵢ²`, `d/dt (½‖u‖²) = −Σᵢ νᵢ uᵢ²`.

The concrete instance `triad` (`n = 3`) uses a quadratic, energy-conserving triad interaction
`J(u)u = (2u₁u₂, 2u₀u₂, −4u₀u₁)` of the type produced by Galerkin truncations of incompressible
fluid equations, and unit viscosities. **This is a finite-dimensional model.** It is not derived
here from a Fourier truncation of the Navier–Stokes nonlinearity, and nothing in this file
concerns the continuum Navier–Stokes equations. The Jacobi identity for `J` is not claimed.
-/

namespace MetriplecticNS.Galerkin

open MetriplecticNS

variable {n : ℕ}

/-- Velocity-coefficient space `ℝⁿ`. -/
abbrev Vel (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- State space: velocity coefficients and entropy coordinate. -/
abbrev State (n : ℕ) := Vel n × ℝ

/-- Unit vector in the `i`-th velocity direction. -/
noncomputable def eU (i : Fin n) : State n := (EuclideanSpace.single i 1, 0)

/-- Unit vector in the entropy direction. -/
def eS : State n := (0, 1)

/-- Partial derivative of `F` in the `i`-th velocity direction. -/
noncomputable def du (F : Functional (State n)) (x : State n) (i : Fin n) : ℝ :=
  fderiv ℝ F x (eU i)

/-- Partial derivative of `F` in the entropy direction. -/
noncomputable def ds (F : Functional (State n)) (x : State n) : ℝ :=
  fderiv ℝ F x eS

/-- Model data: a state-dependent skew matrix and nonnegative viscosities. -/
structure Data (n : ℕ) where
  /-- Poisson (reversible) structure matrix. -/
  J : Vel n → Matrix (Fin n) (Fin n) ℝ
  /-- `J(u)` is skew-symmetric for every `u`. -/
  J_skew : ∀ u i j, J u j i = - J u i j
  /-- Viscosity coefficients. -/
  ν : Fin n → ℝ
  /-- Viscosities are nonnegative. -/
  ν_nonneg : ∀ i, 0 ≤ ν i

/-- Poisson bracket `{F,G}(x) = Σᵢⱼ ∂ᵤᵢF J(u)ᵢⱼ ∂ᵤⱼG`. -/
noncomputable def poisson (D : Data n) (F G : Functional (State n)) : Functional (State n) :=
  fun x => ∑ i, ∑ j, du F x i * D.J x.1 i j * du G x j

/-- Projected gradient `(PF)ᵢ = ∂ᵤᵢF − (∂ₛF) uᵢ`; it annihilates the gradient of `H`. -/
noncomputable def proj (F : Functional (State n)) (x : State n) (i : Fin n) : ℝ :=
  du F x i - ds F x * x.1 i

/-- Metric (viscous) bracket `(F,G)(x) = Σᵢ νᵢ (PF)ᵢ (PG)ᵢ`. -/
noncomputable def metric (D : Data n) (F G : Functional (State n)) : Functional (State n) :=
  fun x => ∑ i, D.ν i * (proj F x i * proj G x i)

/-- Total energy `½‖u‖² + s`. -/
noncomputable def H : Functional (State n) := fun x => (1 / 2) * ‖x.1‖ ^ 2 + x.2

/-- Kinetic energy `½‖u‖²`. -/
noncomputable def K : Functional (State n) := fun x => (1 / 2) * ‖x.1‖ ^ 2

/-- Entropy `s`. -/
def S : Functional (State n) := fun x => x.2

/-- The `i`-th velocity coefficient as an observable. -/
def coord (i : Fin n) : Functional (State n) := fun x => x.1 i

/-! ## Derivatives of `H`, `K`, `S` and the coordinates -/

theorem hasFDerivAt_K (x : State n) :
    HasFDerivAt (K (n := n))
      ((1 / 2 : ℝ) • (2 • (innerSL ℝ x.1).comp (ContinuousLinearMap.fst ℝ (Vel n) ℝ))) x :=
  ((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).norm_sq).const_mul (1 / 2)

theorem fderiv_K_apply (x v : State n) : fderiv ℝ K x v = inner ℝ x.1 v.1 := by
  rw [(hasFDerivAt_K x).fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
  ring

theorem hasFDerivAt_H (x : State n) :
    HasFDerivAt (H (n := n))
      ((1 / 2 : ℝ) • (2 • (innerSL ℝ x.1).comp (ContinuousLinearMap.fst ℝ (Vel n) ℝ))
        + ContinuousLinearMap.snd ℝ (Vel n) ℝ) x :=
  (hasFDerivAt_K x).add (hasFDerivAt_snd (𝕜 := ℝ) (p := x))

theorem fderiv_H_apply (x v : State n) : fderiv ℝ H x v = inner ℝ x.1 v.1 + v.2 := by
  rw [(hasFDerivAt_H x).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
  ring

theorem fderiv_S_apply (x v : State n) : fderiv ℝ S x v = v.2 := by
  have hS : (S : Functional (State n)) = Prod.snd := rfl
  rw [hS, (hasFDerivAt_snd (𝕜 := ℝ) (p := x)).fderiv]
  rfl

theorem inner_single_one (v : Vel n) (i : Fin n) :
    inner ℝ v (EuclideanSpace.single i (1 : ℝ)) = v i := by
  simpa using EuclideanSpace.inner_single_right i (1 : ℝ) v

theorem hasFDerivAt_coord (i : Fin n) (x : State n) :
    HasFDerivAt (coord (n := n) i)
      ((EuclideanSpace.proj i).comp (ContinuousLinearMap.fst ℝ (Vel n) ℝ)) x :=
  ((EuclideanSpace.proj (𝕜 := ℝ) i).comp (ContinuousLinearMap.fst ℝ (Vel n) ℝ)).hasFDerivAt

theorem fderiv_coord_apply (i : Fin n) (x v : State n) : fderiv ℝ (coord i) x v = v.1 i := by
  rw [(hasFDerivAt_coord i x).fderiv]
  rfl

@[simp] theorem du_H (x : State n) (i : Fin n) : du H x i = x.1 i := by
  simp [du, eU, fderiv_H_apply, inner_single_one]

@[simp] theorem ds_H (x : State n) : ds H x = 1 := by
  simp [ds, eS, fderiv_H_apply]

@[simp] theorem du_K (x : State n) (i : Fin n) : du K x i = x.1 i := by
  simp [du, eU, fderiv_K_apply, inner_single_one]

@[simp] theorem ds_K (x : State n) : ds K x = 0 := by
  simp [ds, eS, fderiv_K_apply]

@[simp] theorem du_S (x : State n) (i : Fin n) : du S x i = 0 := by
  simp [du, eU, fderiv_S_apply]

@[simp] theorem ds_S (x : State n) : ds S x = 1 := by
  simp [ds, eS, fderiv_S_apply]

@[simp] theorem du_coord (i j : Fin n) (x : State n) :
    du (coord i) x j = if i = j then 1 else 0 := by
  simp [du, eU, fderiv_coord_apply, PiLp.single_apply]

@[simp] theorem ds_coord (i : Fin n) (x : State n) : ds (coord i) x = 0 := by
  simp [ds, eS, fderiv_coord_apply]

@[simp] theorem proj_H (x : State n) (i : Fin n) : proj H x i = 0 := by
  simp [proj]

@[simp] theorem proj_S (x : State n) (i : Fin n) : proj S x i = - x.1 i := by
  simp [proj]

@[simp] theorem proj_K (x : State n) (i : Fin n) : proj K x i = x.1 i := by
  simp [proj]

@[simp] theorem proj_coord (i j : Fin n) (x : State n) :
    proj (coord i) x j = if i = j then 1 else 0 := by
  simp [proj]

/-! ## The structure axioms -/

theorem poisson_skew (D : Data n) (F G : Functional (State n)) :
    poisson D F G = fun x => - (poisson D G F x) := by
  funext x
  simp only [poisson]
  conv_rhs => rw [Finset.sum_comm]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [D.J_skew x.1 i j]
  ring

theorem metric_sym (D : Data n) (F G : Functional (State n)) :
    metric D F G = metric D G F := by
  funext x
  simp only [metric]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem metric_pos (D : Data n) (F : Functional (State n)) (x : State n) :
    metric D F F x ≥ 0 :=
  Finset.sum_nonneg fun i _ => mul_nonneg (D.ν_nonneg i) (mul_self_nonneg _)

theorem casimir_S (D : Data n) (F : Functional (State n)) (x : State n) :
    poisson D F S x = 0 := by
  simp [poisson]

theorem null_H (D : Data n) (F : Functional (State n)) (x : State n) :
    metric D F H x = 0 := by
  simp [metric]

/-- The assembled metriplectic system. -/
noncomputable def system (D : Data n) : MetriplecticSystem (State n) where
  poisson := poisson D
  metric := metric D
  H := H
  S := S
  poisson_skew := poisson_skew D
  metric_sym := metric_sym D
  metric_pos := metric_pos D
  casimir_S := casimir_S D
  null_H := null_H D

/-! ## Equations of motion -/

/-- The quadratic form of a skew matrix vanishes. -/
theorem skew_quadratic_zero (D : Data n) (u : Vel n) :
    ∑ i, ∑ j, u i * D.J u i j * u j = 0 := by
  have h : ∑ i, ∑ j, u i * D.J u i j * u j = - ∑ i, ∑ j, u i * D.J u i j * u j := by
    conv_rhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [D.J_skew u i j]
    ring
  linarith

theorem poisson_coord_H (D : Data n) (i : Fin n) (x : State n) :
    poisson D (coord i) H x = ∑ j, D.J x.1 i j * x.1 j := by
  simp [poisson, ite_mul]

theorem metric_coord_S (D : Data n) (i : Fin n) (x : State n) :
    metric D (coord i) S x = - (D.ν i * x.1 i) := by
  simp [metric, ite_mul]

/-- Velocity equation: `u̇ᵢ = (J(u) u)ᵢ − νᵢ uᵢ`. -/
theorem evolution_coord (D : Data n) (i : Fin n) (x : State n) :
    (system D).evolution (coord i) x = ∑ j, D.J x.1 i j * x.1 j - D.ν i * x.1 i := by
  show poisson D (coord i) H x + metric D (coord i) S x = _
  rw [poisson_coord_H, metric_coord_S]
  ring

/-- Entropy equation: `ṡ = Σᵢ νᵢ uᵢ²`. -/
theorem evolution_S (D : Data n) (x : State n) :
    (system D).evolution S x = ∑ i, D.ν i * x.1 i ^ 2 := by
  show poisson D S H x + metric D S S x = _
  simp only [poisson, metric, du_S, proj_S, zero_mul, Finset.sum_const_zero, zero_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Kinetic-energy equation: `d/dt ½‖u‖² = −Σᵢ νᵢ uᵢ²` (the reversible part drops out by
skew-symmetry, the viscous part is the dissipation). -/
theorem evolution_K (D : Data n) (x : State n) :
    (system D).evolution K x = - ∑ i, D.ν i * x.1 i ^ 2 := by
  show poisson D K H x + metric D K S x = _
  simp only [poisson, metric, du_K, du_H, proj_K, proj_S]
  rw [skew_quadratic_zero D x.1, zero_add, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- First law for the instance: total energy is conserved (abstract theorem, applied). -/
theorem energy_conserved (D : Data n) (x : State n) : (system D).evolution H x = 0 :=
  (system D).energy_conserved x

/-- Second law for the instance: entropy is nondecreasing (abstract theorem, applied). -/
theorem entropy_production (D : Data n) (x : State n) : (system D).evolution S x ≥ 0 :=
  (system D).entropy_production x

/-- Energy balance: the kinetic energy lost to viscosity equals the entropy produced. -/
theorem kinetic_loss_eq_entropy_gain (D : Data n) (x : State n) :
    (system D).evolution K x = - (system D).evolution S x := by
  rw [evolution_K, evolution_S]

/-! ## A concrete triad instance (`n = 3`) and non-vacuity -/

/-- Skew matrix of a triad interaction: `J(u) = [[0, u₂, u₁], [−u₂, 0, 3u₀], [−u₁, −3u₀, 0]]`,
so `J(u)u = (2u₁u₂, 2u₀u₂, −4u₀u₁)`. -/
def triadJ (u : Vel 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, u 2, u 1; -u 2, 0, 3 * u 0; -u 1, -(3 * u 0), 0]

theorem triadJ_skew (u : Vel 3) (i j : Fin 3) : triadJ u j i = - triadJ u i j := by
  fin_cases i <;> fin_cases j <;> simp [triadJ]

/-- Triad data with unit viscosities. -/
def triad : Data 3 where
  J := triadJ
  J_skew := triadJ_skew
  ν := fun _ => 1
  ν_nonneg := fun _ => zero_le_one

theorem triad_J_mul (u : Vel 3) :
    (∑ j, triadJ u 0 j * u j) = 2 * u 1 * u 2 ∧
    (∑ j, triadJ u 1 j * u j) = 2 * u 0 * u 2 ∧
    (∑ j, triadJ u 2 j * u j) = -4 * u 0 * u 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [triadJ, Fin.sum_univ_three] <;> ring

/-- Coordinate brackets of the general model. -/
theorem poisson_coord_coord (D : Data n) (i j : Fin n) (x : State n) :
    poisson D (coord i) (coord j) x = D.J x.1 i j := by
  simp [poisson, ite_mul]

theorem metric_coord_coord (D : Data n) (i : Fin n) (x : State n) :
    metric D (coord i) (coord i) x = D.ν i := by
  simp [metric]

/-- A sample state `u = e₁ + e₂`, `s = 0`. -/
noncomputable def x₀ : State 3 := (EuclideanSpace.single 1 1 + EuclideanSpace.single 2 1, 0)

/-- Non-vacuity: the Poisson bracket is not identically zero. -/
theorem triad_poisson_ne_zero : poisson triad (coord 0) (coord 1) x₀ ≠ 0 := by
  rw [poisson_coord_coord]
  simp [triad, triadJ, x₀]

/-- Non-vacuity: the metric bracket is not identically zero. -/
theorem triad_metric_ne_zero : metric triad (coord 0) (coord 0) x₀ ≠ 0 := by
  rw [metric_coord_coord]
  simp [triad]

/-- Non-vacuity: the energy is not constant. -/
theorem H_not_const : (H : Functional (State n)) ((0 : Vel n), (0 : ℝ)) ≠ H ((0 : Vel n), (1 : ℝ)) := by
  simp [H]

/-- Non-vacuity: entropy production is strictly positive at `x₀`. -/
theorem triad_entropy_production_pos : 0 < (system triad).evolution S x₀ := by
  rw [evolution_S]
  simp [triad, x₀, Fin.sum_univ_three, PiLp.single_apply]

/-- Non-vacuity: the reversible (Poisson) part of the motion is nonzero, so the dynamics is not
pure decay: at `x₀`, `u̇₀ = 2u₁u₂ − u₀ = 2`. -/
theorem triad_evolution_coord0 : (system triad).evolution (coord 0) x₀ = 2 := by
  rw [evolution_coord]
  simp only [triad]
  rw [(triad_J_mul _).1]
  simp [x₀]

end MetriplecticNS.Galerkin
