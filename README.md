# Metriplectic completion of the Frohmanian Symplectic Tether

Author: Benjamin Stanley Frohman
Affiliation: Independent Researcher, Texas, United States
ORCID: [0009-0006-7068-3718](https://orcid.org/0009-0006-7068-3718)
Email: frohmanbenjamin@gmail.com

This private companion repository contains an **abstract algebraic** Lean 4
formalization of a metriplectic system, together with the working paper
`paper/metriplectic_ns_paper.tex` (and its compiled PDF). It is intended as
algebraic scaffolding for the Frohmanian tether program, not as a PDE
development and not as a Clay solution.

## Honest scope

- **This is not a Clay Millennium Navier–Stokes proof.** Large-data global
  regularity remains open.
- The Lean file formalizes an abstract structure `MetriplecticSystem` with a
  Poisson bracket and a metric bracket, then proves three algebraic lemmas:
  energy conservation, nonnegative entropy production, and the symmetry
  swap of a degeneracy condition on the Hamiltonian.
- **A kernel check is not a geometric, analytic, or physical proof.** The
  theorems hold for any type `State` and any brackets satisfying the named
  structure fields. They do not mention Sobolev spaces, the 3-torus, or the
  Navier–Stokes equations.
- The `NSSpecialization` section in `MetriplecticNS.lean` is an explicit
  placeholder: `VorticityField` is `Unit`, and both `kksPoisson` and
  `viscousMetric` are the zero function. They are not assembled into a
  `MetriplecticSystem` instance, and they do not recover viscous terms or
  the continuum equations.
- **Recovery of the Navier–Stokes–Fourier equations is not formalized.**
  The paper states that result as a classical theorem once the brackets are
  given. The Lean development does not prove it, and it does not carry out
  integration by parts.
- There is no Lean import of the existing TetherKernel modules. Compatibility
  with the prior obstruction is algebraic only, as described below.

## What Lean actually proves

In `MetriplecticNS.lean`, for an abstract `MetriplecticSystem`:

1. `energy_conserved`: \(\dot H = \{H,H\} + (H,S) = 0\), using skew-symmetry
   of the Poisson bracket and energy degeneracy of the metric bracket
   (plus metric symmetry).
2. `entropy_production`: \(\dot S = \{S,H\} + (S,S) = (S,S) \ge 0\), using
   that \(S\) is a Casimir, skew-symmetry, and positive semi-definiteness.
   The draft proof of this lemma did not typecheck (it cited `casimir_S S`,
   which gives \(\{S,S\}=0\) rather than \(\{S,H\}=0\)). The committed proof
   uses the Casimir axiom on \(H\) together with skew-symmetry, which is the
   justification already written in the paper.
   The draft proof of `energy_conserved` also failed to compile: `simp [this] at *`
   on the function equation `{H,H} = fun s => -{H,H}s` hit the maximum recursion
   depth. The committed proof uses `congrFun` and `linarith` on the same
   skew-symmetry identity. Two `/-- ... -/` comments in the draft (one on
   `section NSSpecialization`, one at end of file with no declaration) were
   ordinary comments in the committed file, because Lean treats `/--` as a
   doc comment that must precede a declaration.
3. `tether_damping_obstruction`: if a bilinear form \(B\) is symmetric and
   \(B(F,H)=0\) for all \(F\), then \(B(H,F)=0\) for all \(F\). This is the
   swap of the two argument slots by symmetry. It does not itself mention
   the tether kernel, damping rates, or the Euler vector field.

The structure fields are used by those lemmas (they are not unused `Prop`
fields). The structure is inhabitible: the zero Poisson and metric brackets,
with any choice of \(H\) and \(S\), satisfy every field, and in that instance
the first two lemmas are true but trivial. No non-trivial instance is
constructed in this repository, and there is no non-vacuity lemma showing
that the obstruction fails if symmetry is dropped.

## Relation to the existing TetherKernel obstruction

The algebraic content of `tether_damping_obstruction` matches the existing
lemma `left_H_zero_of_C2_symm` in
[`frohmanian-tether-sdiff`](https://github.com/BenFrohman/frohmanian-tether-sdiff)
(`FrohmanianTether/Combined.lean` / `manuscript/lean/left_H_zero_of_C2_symm.lean`):
a symmetric bilinear form that is degenerate on the kinetic-energy Hamiltonian
(`DegenerateWRTKineticEnergy`) also vanishes with the Hamiltonian in the first
slot. The concrete companion `tetherKernel_left_H_zero` records both slots
for the actual `TetherKernel`.

This repository does **not** re-prove that the concrete `TetherKernel`
satisfies the degeneracy condition, and it does not instantiate \(B\) as
`TetherKernel`. That degeneracy, under additional hypotheses on the
functional derivative of the kinetic energy, is already in the sdiff
development (`tetherKernel_degenerates_on_kinetic_energy`). Compatibility
here means only that the abstract symmetry-and-degeneracy implication is
the same algebraic fact.

## Paper overclaims (flagged, not rewritten)

The paper body was not rewritten except for the author line (affiliation
"Independent Researcher, Texas, United States" and the email
`frohmanbenjamin@gmail.com` were added). The following claims in the paper
go beyond what the Lean file checks:

- The abstract says the work proves "the recovery of the continuum
  equations." Lean does not prove that. Later the paper itself describes
  recovery as classical once the brackets are given.
- Section 7 describes specialization to integral functionals of fluid
  densities, and recovery of the viscous term by integration by parts, as
  if this were in the Lean development. The Lean file only has the `Unit`
  / zero-bracket placeholders.
- Section 7 says the formalization is compatible with existing Frohmanian
  Tether modules and that the tether kernel may be inserted as a metric
  summand. There is no such import or construction in Lean, only a comment.
- Section 4 attributes to the existing Lean formalization the conclusion
  \(T(M,H)=0\) for every \(M\). In the sdiff formalization that identity,
  with \(H\) in the second slot, is the degeneracy hypothesis
  `DegenerateWRTKineticEnergy` itself; the proved swap is the other slot.

A prior vacuity-audit side note on related formalization pitfalls is
[10.5281/zenodo.24102969](https://doi.org/10.5281/zenodo.24102969).

## Related repositories

- [frohmanian-tether-conditional-regularity](https://github.com/BenFrohman/frohmanian-tether-conditional-regularity)
- [frohmanian-tether-sdiff](https://github.com/BenFrohman/frohmanian-tether-sdiff)
- [NS_Millennium_Proof](https://github.com/BenFrohman/NS_Millennium_Proof)
- [frohmanian-tether-verified](https://github.com/BenFrohman/frohmanian-tether-verified)

## Reproducibility

- Toolchain: Lean 4.30.0-rc1, Mathlib `v4.30.0-rc1`
  (`0c154d67103f74be3a0f2c509f72ccbf5be9f2a7`), pinned in `lean-toolchain`
  and `lake-manifest.json` to the same versions as
  `frohmanian-tether-conditional-regularity`.
- One-command rebuild: `lake exe cache get && lake build`
- Kernel audit: `./scripts/kernel_check.sh` (no `sorry`, `admit`,
  `native_decide`, or new axioms; `#print axioms` may use only `propext`,
  `Classical.choice`, and `Quot.sound`).
- Commit SHA: recorded on GitHub after the initial push; rebuilds should
  name that commit.

## License

- Code: Apache License 2.0 (`LICENSE`).
- Paper (LaTeX and PDF): CC BY 4.0 (`LICENSE-paper`).
