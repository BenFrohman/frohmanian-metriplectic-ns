# Metriplectic Completion of the Frohmanian Symplectic Tether

**Thermodynamic Structure and Lean Formalization for the Navier–Stokes Equations** — Version 1.1 (10 November 2026)

Author: Benjamin Stanley Frohman (ORCID [0009-0006-7068-3718](https://orcid.org/0009-0006-7068-3718)), Independent Researcher, Texas, United States. Contact: frohmanbenjamin@gmail.com

© 2026 Benjamin Stanley Frohman. Distributed under the Apache License 2.0.

Part of the ongoing Frohmanian Symplectic Tether program. Not a solution of the Clay Millennium Problem. Lean does not prove recovery of the Navier–Stokes or Navier–Stokes–Fourier equations; continuum recovery and regularity remain open/conditional.

## What this deposit is

A preprint and a Lean 4 module. The preprint builds a metriplectic completion of the Frohmanian Symplectic Tether on SDiff(T³). It adjoins an independent viscous metric bracket to the symmetric tether kernel. The Lean module states an abstract `MetriplecticSystem` structure (Poisson bracket, metric bracket, H, S, and their axioms as structure fields) and three algebraic theorems about it:

- `MetriplecticSystem.energy_conserved`: the evolution of H is 0.
- `MetriplecticSystem.entropy_production`: the evolution of S is ≥ 0.
- `MetriplecticSystem.tether_damping_obstruction`: a symmetric bracket B with B(F,H)=0 for every F also has B(H,F)=0.

The Navier–Stokes section of the Lean file is a placeholder only: `VorticityField := Unit`, and both brackets are identically 0. No continuum recovery, Sobolev analysis or regularity is formalized.

## Files

| File | Contents |
|---|---|
| `metriplectic_ns_paper.pdf` | Compiled preprint, version 1.1 (7 pages) |
| `metriplectic_ns_paper.tex` | LaTeX source |
| `MetriplecticNS.lean` | Lean 4 module, exactly as supplied by the author (does not compile; kept for provenance) |
| `MetriplecticNS_checked.lean` | Corrected Lean 4 module: compiles with 0 errors, 0 sorry; same theorem statements |
| `README.md` | This file |

## Changes in v1.1 (paper only; the two Lean files are byte-identical to v1.0)

- Abstract, Introduction and Section 7 no longer claim that Lean proves recovery of the continuum equations. They state exactly what `MetriplecticNS_checked.lean` proves and that the Navier–Stokes part of the Lean file is a placeholder.
- Entropy production: `(S,H) ≥ 0` corrected to `(S,S) ≥ 0` (from positive semidefiniteness `(F,F) ≥ 0`); `(S,H) = 0` by energy degeneracy and symmetry.
- Tether kernel: written with the global enstrophy factor `‖ω‖²` outside the integral, as formalized; the `−κ` sign (κ > 0) makes the kernel negative semidefinite, the opposite sign to a metric bracket, and this is now stated. (C2) is marked as an unproved hypothesis; the Lean result is `T(H,M) = 0` *assuming* (C2), not `T(M,H) = 0`.
- Viscous bracket: `Ṡ = B_visc(S,H)` corrected to `Ṡ = (S,S)_full = B_visc(S,S) + T(S,S) ≤ B_visc(S,S)`. Energy degeneracy of `B_visc` is now an explicit assumption (A2), together with (A1) = (C2) and (A3) positivity of the sum. The paper shows that the displayed candidate `ν∫∇(δF/δω):∇(δG/δω)` does **not** satisfy (A2): `B_visc(H,H) = ν∫|∇ψ|² > 0` for ω ≠ 0, where ψ = δH/δω is the stream function.
- The "Recovery of Navier–Stokes–Fourier" theorem is now a remark citing the literature (not proved here, not formalized).
- Copyright line, ORCID, affiliation and program note added; Lean toolchain and axiom output recorded in the paper.

An extended Lean development (imported tether kernel, a concrete finite-dimensional viscous metriplectic system, and a proof that the tether kernel is not the metric bracket of any metriplectic system) is in the GitHub repository [BenFrohman/frohmanian-metriplectic-ns](https://github.com/BenFrohman/frohmanian-metriplectic-ns); this deposit's files are also stored there under `zenodo/v1.1/`.

## Lean verification status (checked 10 November 2026)

- Toolchain: `leanprover/lean4:v4.30.0-rc1` (Lean commit 714601baf118066cbf3f282361339c6d06665b2a)
- Mathlib: tag `v4.30.0-rc1`, rev `0c154d67103f74be3a0f2c509f72ccbf5be9f2a7`
- Textual count in `MetriplecticNS.lean`: 0 `sorry`, 0 `admit`, 0 `axiom` declarations.

**The file as supplied does NOT compile.** `lake env lean MetriplecticNS.lean` reports 4 errors:

1. Line 46 (`energy_conserved`): `simp [this] at *` hits maximum recursion depth.
2. Line 58 (`entropy_production`): `sys.casimir_S sys.S s` has type `poisson S S s = 0`, but `poisson S H s = 0` is needed. This needs skew-symmetry plus the Casimir property.
3. Line 79 and the end of the file: a `/-- ... -/` doc comment sits before `section` and at end of file, where no declaration follows. These are parse errors.

Because of errors 1 and 2, Lean closes those two proofs with `sorryAx`. `#print axioms` on the file as supplied gives:

```
'MetriplecticSystem.energy_conserved' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'MetriplecticSystem.entropy_production' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'MetriplecticSystem.tether_damping_obstruction' depends on axioms: [propext, Classical.choice, Quot.sound]
```

A small patch makes it compile with 0 errors, and then all three theorems depend only on `[propext, Classical.choice, Quot.sound]`. The patch changes the two proof steps and turns the two orphan doc comments into ordinary comments. No statement changes. It is provided in this deposit as `MetriplecticNS_checked.lean`, which is the verified, compiled version. Checked 10 November 2026: `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for `energy_conserved`, `entropy_production` and `tether_damping_obstruction`.

## Rebuild and verify

Paper (needs [tectonic](https://tectonic-typesetting.github.io)):

```
tectonic metriplectic_ns_paper.tex
```

Lean (one command, run from the folder containing `MetriplecticNS_checked.lean`; uses the prebuilt Mathlib cache):

```
git clone --depth 1 --branch v4.30.0-rc1 https://github.com/leanprover-community/mathlib4.git && cd mathlib4 && lake exe cache get && printf '\n#print axioms MetriplecticSystem.energy_conserved\n#print axioms MetriplecticSystem.entropy_production\n#print axioms MetriplecticSystem.tether_damping_obstruction\n' | cat ../MetriplecticNS_checked.lean - > /tmp/MetriplecticNS_check.lean && lake env lean /tmp/MetriplecticNS_check.lean
```

Success means no `error:` lines, and no `sorryAx` in the three axiom lists.

## Related records

- 10.5281/zenodo.24120781: *The Frohmanian Tether on SDiff(T^3): A Metriplectic Correction, Its Canonicity, and an Obstruction to Damping*, v0.1.4 (cited in the paper)
- 10.5281/zenodo.24079622: Geometric Phase-Space Completion and Conditional Global Regularity (concept)
- 10.5281/zenodo.23990195: The Frohmanian Tether on SDiff(𝕋³), v4
- 10.5281/zenodo.23942466: The Frohmanian Symplectic Tether: Architecture, Reduced Jacobi Identity, and the Frohmanian Curve (historical build)
