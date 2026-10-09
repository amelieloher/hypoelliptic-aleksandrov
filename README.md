# Kinetic Aleksandrov estimates, formalised in Lean 4

[![Build](https://github.com/amelieloher/hypoelliptic-aleksandrov/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/amelieloher/hypoelliptic-aleksandrov/actions/workflows/build.yml)
[![Comparator](https://github.com/amelieloher/hypoelliptic-aleksandrov/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/amelieloher/hypoelliptic-aleksandrov/actions/workflows/comparator.yml)

A **Lean 4 / Mathlib** formalisation of Aleksandrov maximum principles for kinetic equations in
non-divergence form with measurable, uniformly elliptic coefficients:

```math
\partial_t u+v\cdot\nabla_x u-A:D_v^2u=f,\qquad \lambda I\le A\le\Lambda I .
```

Diffusion acts only in the velocity $`v`$, and the position $`x`$ is moved by transport. A subsolution on a
backward kinetic cylinder $`Q_R^-(P_0)`$ is bounded by its positive part on the kinetic boundary plus
$`C R^{2-(4d+2)/p}\lVert f_+\rVert_{L^p}`$, and the source norm may be restricted to the set where the solution
is positive. The main results are:

- **Coefficients depending on time and velocity.** For $`A=A(t,v)`$, the estimate holds for every source exponent
  $`p>2d+1`$.
- **Autonomous coefficients in one space dimension.** For $`A=a(x,v)`$ with $`d=1`$, it holds for every
  $`p>1+\beta_*(\Lambda/\lambda)`$, where the threshold $`1+\beta_*<4`$ is defined by a homogeneous adjoint
  problem. No exponent below $`4`$ works for all ellipticity ratios at once.
- **Coefficients depending on time, position and velocity.** For general measurable $`A=A(t,x,v)`$, it holds for
  every $`p\ge 1+\tfrac{128d^2}{3}(\Lambda/\lambda)^2`$. This exponent comes from the proof and is not claimed to
  be optimal.
- **Hölder continuity.** In each case, bounded solutions of the homogeneous equation are Hölder continuous in
  the interior, with exponent and constant depending only on $`d,\lambda,\Lambda`$. For coefficients $`A(t,x,v)`$
  this is the kinetic analogue of the Krylov–Safonov theorem.

Along the way the library proves the parabolic Aleksandrov estimate of Krylov (Sibirsk. Mat. Zh. 17 (1976))
and the parabolic Harnack inequality of Krylov and Safonov (Izv. Akad. Nauk SSSR Ser. Mat. 44 (1980)). It also constructs the terminal solution operators of the kinetic
equation and proves classical Dirichlet solvability on ellipsoids. Hörmander's hypoellipticity theorem is
taken from the Lean formalisation
[`hoermander-rothschild-stein`](https://github.com/amelieloher/hoermander-rothschild-stein). The library contains no
`sorry`, and every result uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Verification

Every proof is checked by Lean's kernel. In addition, the main theorems are restated in two standalone
**comparator** files that import only Mathlib and spell out every definition they use (kinetic cylinders,
the kinetic boundary, the classical solution class, the operators, the exponent $`\beta_*`$, the
quasi-distance):

| Configuration | Theorems |
| --- | --- |
| [`AleksandrovComparators/KineticAleksandrov`](AleksandrovComparators/KineticAleksandrov/) | Theorems 1.1 and 1.2 with their localised forms, Corollaries 9.9 and 9.10, Proposition C.1, the exponent $`\beta_*`$, and the parabolic Aleksandrov and Harnack theorems (11 theorems) |
| [`AleksandrovComparators/FullCoefficient`](AleksandrovComparators/FullCoefficient/) | The Aleksandrov and Hölder estimates for coefficients $`A(t,x,v)`$, and Theorem 9.1 (3 theorems) |

Lean's [comparator](https://github.com/leanprover/comparator) checks that each `Solution.lean` proves exactly
the statements of the corresponding `Challenge.lean`, over the same definitions, using only the axioms
`propext`, `Classical.choice` and `Quot.sound`, and replays the proofs through Lean's kernel and the
independent kernel checkers NanoDa and con-ron. Both configurations pass, as checked by
[`scripts/verify-comparator.sh`](scripts/verify-comparator.sh), the way the
[Palomar registry](https://submit.palomar-registry.org/) checks submissions.

## Results formalised

- **Amélie Loher, Connor Mooney and Clément Mouhot, *From Döblin to Aleksandrov*** (long version,
  [PDF](https://amelieloher.github.io/DF-visual-paper/pdf/doeblin-fourier-companion.pdf), version of
  2 October 2026), the full account of the time–velocity and autonomous results. Numbering below refers to
  that version. The short version is *Döblin–Fourier cancellation and kinetic Aleksandrov estimates*
  ([arXiv:2610.03083](https://arxiv.org/abs/2610.03083)).

  | Result | Lean declaration |
  | --- | --- |
  | Theorem 1.1 (coefficients depending on time and velocity) | `HypoellipticAleksandrov.KineticAleksandrov.kinetic_aleksandrov_timeVelocity` |
  | Corollary 1.3 for Theorem 1.1 (localised source) | `HypoellipticAleksandrov.KineticAleksandrov.kinetic_aleksandrov_timeVelocity_localised` |
  | Theorem 1.2 (autonomous coefficients, $`d=1`$) | `HypoellipticAleksandrov.KineticAleksandrov.kinetic_aleksandrov_autonomous` |
  | Corollary 1.3 for Theorem 1.2 | `HypoellipticAleksandrov.KineticAleksandrov.kinetic_aleksandrov_autonomous_localised` |
  | The exponent $`\beta_*`$ (Appendix B): existence and uniqueness | `HypoellipticAleksandrov.KineticAleksandrov.existsUnique_bellmanAdjointExponent` |
  | Proposition C.1 (no smaller threshold uniform in the ellipticity ratio) | `HypoellipticAleksandrov.KineticAleksandrov.kinetic_aleksandrov_autonomous_counterexample` |
  | Theorem 9.1 (the Aleksandrov principle implies Hölder continuity) | `HypoellipticAleksandrov.KineticAleksandrov.kinetic_holder_of_aleksandrov` |
  | Theorem 9.4 (crawling ink spots, kinetic form) | `HypoellipticAleksandrov.KineticAleksandrov.Holder.kinetic_crawling_ink_spots` |
  | Theorem 9.6 (growth lemma) | `HypoellipticAleksandrov.KineticAleksandrov.Holder.kinetic_growth_lemma` |
  | Corollary 9.9 (Hölder continuity, coefficients depending on time and velocity) | `HypoellipticAleksandrov.KineticAleksandrov.kinetic_holder_timeVelocity` |
  | Corollary 9.10 (Hölder continuity, autonomous coefficients) | `HypoellipticAleksandrov.KineticAleksandrov.kinetic_holder_autonomous` |
  | Proposition 2.1 (terminal solution operator) | `HypoellipticAleksandrov.KineticAleksandrov.exists_terminalEvolution` |
  | Theorem 4.1 (parabolic Aleksandrov estimate, Krylov) | `HypoellipticAleksandrov.Parabolic.parabolic_aleksandrov` |
  | Theorem 3.5 (parabolic Harnack inequality, Krylov–Safonov) | `HypoellipticAleksandrov.Parabolic.parabolic_harnack_unit_cylinder` |

- **The adjoint-smoothing proof for coefficients $`A(t,x,v)`$**, presented at
  [weneedabp.github.io/kinetic.html](https://weneedabp.github.io/kinetic.html). The formalisation applies that argument
  to the Green measure of the solution operators above, with explicit constants.

  | Result | Lean declaration |
  | --- | --- |
  | Aleksandrov estimate for coefficients $`A(t,x,v)`$, localised to the positivity set | `HypoellipticAleksandrov.KineticAleksandrov.kinetic_aleksandrov_fullCoefficient` |
  | Interior Hölder estimate for coefficients $`A(t,x,v)`$ | `HypoellipticAleksandrov.KineticAleksandrov.kinetic_holder_fullCoefficient` |
  | $`L^q`$ bound for the Green density, $`1<q\le 1+\tfrac{3}{128d^2}(\lambda/\Lambda)^2`$ | `HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.exists_greenDensity_fullCoefficient` |

- **Classical inputs.** Hörmander's hypoellipticity theorem (L. Hörmander, Acta Math. 119 (1967), Theorem 1.1)
  is proved in `hoermander-rothschild-stein` and transported here
  (`HypoellipticAleksandrov.KineticAleksandrov.exists_smooth_aeRepresentative_of_hormander`). Classical
  solvability of the terminal Cauchy–Dirichlet problem on ellipsoidal cylinders (G. M. Lieberman, *Second Order
  Parabolic Differential Equations*, Theorem 5.14) is proved in this library
  (`HypoellipticAleksandrov.KineticAleksandrov.exists_isClassicalBackwardDirichletSolution_openEllipsoid_uniqueOn_of_lieberman`).

## How the statements read

The solution class is the classical one of the papers: $`u`$ is continuous on the closed cylinder, the derivatives
$`\partial_t u`$, $`\nabla_x u`$ and $`D_v^2u`$ are continuous in the open cylinder, and the inequality
$`\partial_tu+v\cdot\nabla_xu-A:D_v^2u\le f`$ holds almost everywhere. Coefficients are Borel, symmetric, and
satisfy the ellipticity bounds almost everywhere. Each constant is chosen before the coefficient, the cylinder
and the data, and depends only on the quantities named in the paper. Kinetic cylinders, the kinetic boundary and
the kinetic quasi-distance follow the definitions of the companion paper, Section 1. The Hölder estimates bound
the oscillation of $`u`$ between two points of a compact set in terms of the oscillation on a neighbourhood of
doubled cylinders.

## Proof route

For coefficients $`A(t,v)`$ and $`a(x,v)`$ the proofs follow the companion paper. Döblin–Fourier cancellation gives
decay of the non-zero Fourier modes in position of the kinetic evolution. Integrating it yields $`L^q`$ bounds
for the Green measure. A comparison principle on kinetic cylinders turns those bounds into the Aleksandrov
estimate (companion paper, Proposition 6.2). For autonomous coefficients the proof adds a Bellman barrier, a
count of visits by time and position, and a Harnack improvement. The Hölder corollaries follow from the
Aleksandrov principle through the kinetic crawling ink-spots covering and the growth lemma.

For coefficients $`A(t,x,v)`$ the Green density is bounded instead by adjoint smoothing. The Green measure is
smoothed in phase space by a Gaussian flow adapted to transport, and the energy inequality for the smoothed
density controls the coefficient term by the decrease of a bounded quantity along the flow. An absorption
argument then gives the $`L^q`$ bound. The reduction to the Aleksandrov estimate and the passage from smooth to
Borel coefficients are those of the companion paper.

## Build and verify

Install [Lean's elan toolchain manager](https://github.com/leanprover/elan). From a fresh checkout, run:

```sh
lake exe cache get
lake build
```

The toolchain is **`leanprover/lean4:v4.35.0-rc2`**. Mathlib is **`v4.35.0-rc2`**, resolved in `lake-manifest.json`
to **`065356127b1dc0016f66b7283ce0ce2c4055aa55`**. Hörmander's theorem comes from
[`hoermander-rothschild-stein`](https://github.com/amelieloher/hoermander-rothschild-stein), pinned to commit
**`d1462014b4ca69cf04b250582ea45021aa07b546`**; only its module `Hormander.Interface` and its dependencies are
built. The manifest pins all dependencies.

To print the axioms of a main theorem:

```sh
echo 'import HypoellipticAleksandrov.Statements.KineticAleksandrovFullCoefficient
#print axioms HypoellipticAleksandrov.KineticAleksandrov.kinetic_aleksandrov_fullCoefficient' > /tmp/Axioms.lean
lake env lean /tmp/Axioms.lean
```

To run the comparator checks described under [Verification](#verification), install
[bubblewrap](https://github.com/containers/bubblewrap) (`bwrap`) and run:

```sh
scripts/verify-comparator.sh
```

[`scripts/check-lean-sources.py`](scripts/check-lean-sources.py) checks the source requirements: every Lean file is
a regular UTF-8 file, starts with the `module` header of Lean's module system, and has at most 10,000 lines.

## Library map

Each main statement has its own short file in [`HypoellipticAleksandrov/Statements/`](HypoellipticAleksandrov/Statements/).
The library has about 2,500 Lean files and 350,000 lines, all in Lean's module system and none longer than
1,500 lines.

| Directory | Content |
| --- | --- |
| [`HypoellipticAleksandrov/Statements`](HypoellipticAleksandrov/Statements/) | The main statements |
| [`HypoellipticAleksandrov/KineticAleksandrov/Evolution`](HypoellipticAleksandrov/KineticAleksandrov/Evolution/), [`SectionTwo`](HypoellipticAleksandrov/KineticAleksandrov/SectionTwo/), [`Lieberman`](HypoellipticAleksandrov/KineticAleksandrov/Lieberman/) | Terminal solution operators, kernels, Duhamel potentials and Green measures; Dirichlet solvability on ellipsoids |
| [`Decay`](HypoellipticAleksandrov/KineticAleksandrov/Decay/), [`Occupation`](HypoellipticAleksandrov/KineticAleksandrov/Occupation/), [`Reconstruction`](HypoellipticAleksandrov/KineticAleksandrov/Reconstruction/), [`Green`](HypoellipticAleksandrov/KineticAleksandrov/Green/), [`Scaling`](HypoellipticAleksandrov/KineticAleksandrov/Scaling/), [`Interval`](HypoellipticAleksandrov/KineticAleksandrov/Interval/) | Döblin–Fourier cancellation, the velocity marginal, reconstruction of the Green density and its $`L^q`$ bounds |
| [`Maximum`](HypoellipticAleksandrov/KineticAleksandrov/Maximum/), [`TheoremA`](HypoellipticAleksandrov/KineticAleksandrov/TheoremA/), [`LocalA`](HypoellipticAleksandrov/KineticAleksandrov/LocalA/), [`SourceProblem`](HypoellipticAleksandrov/KineticAleksandrov/SourceProblem/) | Kinetic comparison principle, from Green densities to the Aleksandrov estimate, Borel coefficients, local estimates |
| [`Autonomous`](HypoellipticAleksandrov/KineticAleksandrov/Autonomous/), [`Bellman`](HypoellipticAleksandrov/KineticAleksandrov/Bellman/) | Autonomous coefficients: the Bellman barrier and the exponent $`\beta_*`$, visits by time and position, the Harnack improvement |
| [`Counterexample`](HypoellipticAleksandrov/KineticAleksandrov/Counterexample/) | The homogeneous profiles of Proposition C.1 and Kummer-function asymptotics |
| [`Holder`](HypoellipticAleksandrov/KineticAleksandrov/Holder/) | Crawling ink spots, the growth lemma and Hölder continuity from the Aleksandrov principle |
| [`FullCoefficient`](HypoellipticAleksandrov/KineticAleksandrov/FullCoefficient/) | Coefficients $`A(t,x,v)`$: the Gaussian flow, smoothing of measures, the smoothed equation, energy inequality, absorption and the Green density |
| [`HypoellipticAleksandrov/Parabolic`](HypoellipticAleksandrov/Parabolic/) | Parabolic theory: Dirichlet problems, Krylov's Aleksandrov estimate, the Krylov–Safonov Harnack inequality, local Hölder estimates |
| [`HypoellipticAleksandrov/Measure`](HypoellipticAleksandrov/Measure/), [`PDEFoundation`](PDEFoundation/) | Measure theory and Sobolev spaces on the ambient spaces |
| [`AleksandrovComparators`](AleksandrovComparators/) | The two Mathlib-only comparator configurations |

## How this was built

The Lean code was written with AI coding agents under the author's supervision. The author approved every exact
Lean definition and theorem statement before its proof was developed, and Lean checks the proofs against those
statements. The models and tools are recorded in [`formalization.yaml`](formalization.yaml).

## Author and citation

The Lean development is by **Amélie Loher** (All Souls College, University of Oxford).

If you use this formalisation, please cite it using the metadata in [`CITATION.cff`](CITATION.cff).

## Acknowledgements

Amélie Loher acknowledges support from the Fondation Sciences Mathématiques de Paris.

## Licence

The Lean code in this repository is licensed under the **Apache License 2.0** (see [`LICENSE`](LICENSE)).
