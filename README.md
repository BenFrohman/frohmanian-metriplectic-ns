# Metriplectic completion of the Frohmanian Symplectic Tether

Author: Benjamin Stanley Frohman
Affiliation: Independent Researcher, Texas, United States
ORCID: [0009-0006-7068-3718](https://orcid.org/0009-0006-7068-3718)
Email: frohmanbenjamin@gmail.com

Lean 4 formalization and working paper (`paper/metriplectic_ns_paper.tex` and its PDF) on how
the Frohmanian tether kernel fits into the metriplectic formalism.

## Honest scope

- **This is not a Clay Millennium Navier–Stokes proof.** Large-data global regularity remains open.
- **A kernel check is not a geometric, analytic, or physical proof.** It checks that the stated
  theorems follow from the stated definitions and hypotheses.
- **No continuum recovery.** Nothing here formalizes or recovers the continuum Navier–Stokes or
  Navier–Stokes–Fourier equations, the viscous term `νΔu`, integration by parts, Sobolev spaces,
  or the Morrison–Updike 4-bracket. Those appear in the paper only as cited background.
- **The concrete system is finite-dimensional.** `MetriplecticNS/Galerkin.lean` is a genuine
  metriplectic system on `ℝⁿ × ℝ` (velocity coefficients plus an entropy coordinate) with a
  viscous metric bracket. It is **not derived** from a Fourier truncation of the Navier–Stokes
  nonlinearity; the 3-mode triad instance is a model interaction of that type.
- **Condition (C2) for `TetherKernel` is not proved** (in this repo or in the imported tether
  repo). Statements that need it take it, or something implying it, as a hypothesis.
- The Jacobi identity is not part of `MetriplecticSystem` and is not claimed for any bracket here.

## How the tether kernel is used: imported, not re-proved

`lakefile.toml` requires the Lake package `FrohmanianTether` from
[`BenFrohman/frohmanian-tether-sdiff`](https://github.com/BenFrohman/frohmanian-tether-sdiff),
pinned to commit `8b7bd6741f8a54587db6a95b4a5199dcf2775f97`. Both repos use Lean `v4.30.0-rc1`
and Mathlib `0c154d67103f74be3a0f2c509f72ccbf5be9f2a7`, so import works and nothing is re-proved.
`MetriplecticNS/TetherBridge.lean` imports `FrohmanianTether.Combined` and uses
`TetherKernel`, `DegenerateWRTKineticEnergy` (C2), `KineticEnergyHamiltonian`,
`CoadjointOrbit`, `tetherKernel_quadratic_form`, `kappa_pos`, `Combined.left_H_zero_of_C2_symm`
and `Combined.tetherKernel_left_H_zero` directly.

## What Lean proves

All 75 declarations below are audited with `#print axioms`; each depends only on `propext`,
`Classical.choice`, `Quot.sound` (transitively, including the imported tether lemmas).
There are 0 `sorry`, 0 `admit`, 0 `native_decide`, and no `axiom` declarations.

### `MetriplecticNS/Basic.lean` (abstract)

| Theorem | Statement | Rule used in the proof |
|---|---|---|
| `poisson_self_zero` | `{F,F} = 0` | `poisson_skew` at `(F,F)` |
| `poisson_S_H` | `{S,H} = 0` | `poisson_skew` at `(S,H)`, then `casimir_S` at **`F = H`** (`{H,S} = 0`) |
| `metric_H_S` | `(H,S) = 0` | `metric_sym`, then `null_H` at `F = S` |
| `energy_conserved` | `Ḣ = 0` | `poisson_self_zero` at `H`, `metric_H_S` |
| `entropy_production` | `Ṡ ≥ 0` | `poisson_S_H`, then `metric_pos` at `S` |
| `entropy_production_eq` | `Ṡ = (S,S)` | `poisson_S_H` |
| `tether_damping_obstruction` | `B` symmetric, `B(F,H)=0 ∀F` ⇒ `B(H,F)=0 ∀F` | the two hypotheses |

The draft `entropy_production` cited `casimir_S S` (that is `{S,S} = 0`), which is the wrong rule
and did not compile. The proof uses `casimir_S` at `H` plus skew-symmetry, exactly as in the paper.

### `MetriplecticNS/TetherBridge.lean` (stated against the imported kernel)

| Theorem | Statement |
|---|---|
| `metric_degenerate` | metric bracket of a system on `CoadjointOrbit` with `H = KineticEnergyHamiltonian` satisfies the imported C2 |
| `metric_left_H_zero` | such a system has `(H,M) = 0` for all `M`; **proved by `Combined.left_H_zero_of_C2_symm`** |
| `tetherKernel_summand_no_H_coupling` | if `metric = V + TetherKernel` with `V(F,H) = 0`, then `TetherKernel` satisfies C2 and `T(H,M) = T(M,H) = 0`, via `Combined.tetherKernel_left_H_zero` |
| `tetherKernel_diag_nonpos` | `TetherKernel ω F F ≤ 0` |
| `tetherKernel_as_metric_diag_zero` | if `metric = TetherKernel`, then `TetherKernel ω F F = 0` for all `ω, F` |
| `tetherKernel_as_metric_no_entropy_production` | if `metric = TetherKernel`, then `Ṡ = 0` |
| `tetherKernel_diag_neg_somewhere` | `∃ ω F, TetherKernel ω F F < 0`, from the imported `TetherNondegeneracy.tetherKernel_nondegenerate` |
| `no_metriplectic_system_with_tether_metric` | no `MetriplecticSystem CoadjointOrbit` has metric bracket `TetherKernel` |

Non-vacuity on the tether side: the sign obstruction is not vacuous, because its hypothesis is
proved never to hold for the actual kernel. Not shown: that any system of the split form in
`tetherKernel_summand_no_H_coupling` exists with `TetherKernel ≠ 0` (that would prove C2, which is open).

### `MetriplecticNS/Galerkin.lean` (concrete system; the old `Unit`/zero-bracket placeholder is gone)

State `x = (u, s) ∈ EuclideanSpace ℝ (Fin n) × ℝ`. Partial derivatives are Fréchet derivatives
(`fderiv`) of the functional, so the brackets are defined on every functional.

- `{F,G}(x) = Σᵢⱼ ∂ᵤᵢF · J(u)ᵢⱼ · ∂ᵤⱼG`, with `J(u)` skew for every `u` (field `J_skew`).
- `(F,G)(x) = Σᵢ νᵢ (PF)ᵢ (PG)ᵢ`, `(PF)ᵢ = ∂ᵤᵢF − (∂ₛF) uᵢ`, `νᵢ ≥ 0` (field `ν_nonneg`).
- `H = ½‖u‖² + s`, `S = s`.

Proved: derivative lemmas (`du_H`, `ds_H`, `du_S`, `ds_S`, `du_K`, `du_coord`, …); the five
structure axioms (`poisson_skew`, `metric_sym`, `metric_pos`, `casimir_S`, `null_H`) and the
assembled `system D : MetriplecticSystem (State n)`; equations of motion
`evolution_coord` (`u̇ᵢ = (J(u)u)ᵢ − νᵢuᵢ`), `evolution_S` (`ṡ = Σ νᵢuᵢ²`), `evolution_K`
(`d/dt ½‖u‖² = −Σ νᵢuᵢ²`), `kinetic_loss_eq_entropy_gain`; and the abstract theorems applied
(`energy_conserved`, `entropy_production`).

Triad instance `triad` (`n = 3`, `νᵢ = 1`, `J(u) = [[0,u₂,u₁],[−u₂,0,3u₀],[−u₁,−3u₀,0]]`, so
`J(u)u = (2u₁u₂, 2u₀u₂, −4u₀u₁)`), with non-vacuity at `x₀ = (e₁+e₂, 0)`:
`triad_poisson_ne_zero` (`{u₀,u₁} = 1`), `triad_metric_ne_zero` (`(u₀,u₀) = 1`), `H_not_const`,
`triad_entropy_production_pos` (`Ṡ = 2 > 0`), `triad_evolution_coord0` (`u̇₀ = 2`, so the
reversible part is nonzero).

## Lean hypothesis ↔ paper assumption

| Lean field / hypothesis | Paper assumption | Match |
|---|---|---|
| `MetriplecticSystem.poisson_skew` | Def. 3.1 eq. (2) `{F,G} = −{G,F}` | exact |
| `MetriplecticSystem.metric_sym` | Def. 3.1 eq. (3) `(F,G) = (G,F)` | exact |
| `MetriplecticSystem.metric_pos` | Def. 3.1 eq. (4) `(F,F) ≥ 0` | exact (diagonal form of PSD) |
| `MetriplecticSystem.casimir_S` | Def. 3.1 eq. (5) `{F,S} = 0 ∀F` | exact |
| `MetriplecticSystem.null_H` | Def. 3.1 eq. (6) `(F,H) = 0 ∀F` | exact |
| (none) | bilinearity / Leibniz rule of brackets | not assumed in Lean or in Def. 3.1; not used |
| (none) | Jacobi identity | not assumed, not used, not claimed |
| `metric_left_H_zero`: `hH : sys.H = KineticEnergyHamiltonian` | Thm 6.1: `H` is the tether's kinetic-energy Hamiltonian | exact |
| `tetherKernel_summand_no_H_coupling`: `hsplit`, `hV` | Thm 6.2: `(·,·) = V + T`, `V(F,H) = 0` | exact |
| `tetherKernel_as_metric_*`: `hT` | Thm 6.4: metric bracket equals `T` | exact |
| `no_metriplectic_system_with_tether_metric` (no hypotheses) | Cor. 6.5 | exact |
| imported `FrohmanianTether.DegenerateWRTKineticEnergy` | (C2) `T(F,H) = 0 ∀F` | exact; **not proved for `TetherKernel`** |
| imported `TetherKernel` (global `‖ω‖²` outside the integral) | Sec. 5 formula | exact (v0.1 of the paper had a pointwise `|ω(x)|²`; corrected) |
| `Galerkin.Data.J_skew` | Sec. 7.1 `J(u)ᵀ = −J(u)` | exact |
| `Galerkin.Data.ν_nonneg` | Sec. 7.1 `νᵢ ≥ 0` | exact |
| `fderiv` (zero where not differentiable) | Sec. 7.1 derivative convention | exact (stated in the paper) |

Mismatches found and not patched over: none remaining in the current files. Earlier mismatches
(all corrected in paper v1.0 and recorded there): the entropy condition written as `(S,H) ≥ 0`
instead of `(S,S) ≥ 0`; the claim that Lean proved `T(M,H) = 0` (that is C2, a hypothesis); the
claim that `T` is "already degenerate on `H`"; the pointwise-weight tether formula.

## Paper changes in v1.0

Abstract rewritten (no continuum recovery claim); Section 3 entropy condition corrected; Section 5
(former 4) fixes the `T(M,H) = 0` misattribution and states C1/C2 are not proved; new Section 6
derives the obstruction from the imported kernel, with the tether-summand and sign obstructions
(replaces the "insert `T` as a metric summand" claim); new Section 7 is the finite-dimensional
system with full hand proofs; Section 8 lists the Lean modules, dependency pin, audit, rebuild
command and source commit, and says plainly what is not formalized (replaces the integration-by-parts
/ integral-specialization claims); the "Recovery of Navier–Stokes–Fourier" theorem is removed; Corollary 6.5 (the tether is strictly negative somewhere, so it is not the metric bracket of any metriplectic system); a paragraph in Section 8 records the errors Lean checking caught in the original upload (the `{S,S}=0` wrong rule and the `Unit`/zero-bracket placeholder).

## Reproducibility

- Toolchain: Lean `v4.30.0-rc1`; Mathlib `0c154d67103f74be3a0f2c509f72ccbf5be9f2a7`;
  FrohmanianTether `8b7bd6741f8a54587db6a95b4a5199dcf2775f97` (all pinned in `lake-manifest.json`).
- One-command rebuild: `lake exe cache get && lake build && ./scripts/kernel_check.sh`
- Audit: `./scripts/kernel_check.sh` (forbidden-token scan plus `#print axioms` for every
  declaration listed in `scripts/PrintAxioms.lean`). CI uploads the output as the `axiom-audit`
  artifact.
- Lean source commit referenced by paper v1.0: `1ecea6cf99011cd4b962e68ea05a1a03a90e3eb3`.

## Zenodo deposit (paper v1.1)

The Zenodo record *Metriplectic Completion of the Frohmanian Symplectic Tether* (concept DOI
[10.5281/zenodo.24121040](https://doi.org/10.5281/zenodo.24121040)) carries the shorter companion
paper and the single-file Lean module. Its exact files for version 1.1 are in `zenodo/v1.1/`:
the corrected paper (no continuum-recovery claim; `(S,S) ≥ 0`; the `−κ` sign of the tether kernel
stated; energy degeneracy of the viscous bracket stated as an assumption and shown to fail for the
naive candidate), the author's original `MetriplecticNS.lean` (does not compile; kept for provenance)
and `MetriplecticNS_checked.lean` (compiles; only `propext`, `Classical.choice`, `Quot.sound`).
Those files are not part of the Lake build; see `zenodo/v1.1/README.md` for their rebuild command.

## Related repositories

- [frohmanian-tether-sdiff](https://github.com/BenFrohman/frohmanian-tether-sdiff) (imported)
- [frohmanian-tether-conditional-regularity](https://github.com/BenFrohman/frohmanian-tether-conditional-regularity)
- [NS_Millennium_Proof](https://github.com/BenFrohman/NS_Millennium_Proof)
- [frohmanian-tether-verified](https://github.com/BenFrohman/frohmanian-tether-verified)

A prior vacuity-audit side note on related formalization pitfalls is
[10.5281/zenodo.24102969](https://doi.org/10.5281/zenodo.24102969).

## License

- Code: Apache License 2.0 (`LICENSE`).
- Paper (LaTeX and PDF): CC BY 4.0 (`LICENSE-paper`).

## Copyright

© 2026 Benjamin Stanley Frohman.
