# Lean Certificate for the Geometric Gaussian LHL

This repository formalizes *Gaussian Kernel Lattices over Number Fields:
Smoothing Bounds from Theta Integrals*. **All 28 in-scope numbered statements
of the corrected paper have verified Lean counterparts (100% statement coverage)**.
The finite-input numerical construction and polynomial-cost guarantees supporting
the Gaussian-shaping remark are also proved, as are the quantitative consequences
in Remarks 4.13 and 4.16.

The full native build and axiom audit pass for **27 modules / 44,139 Lean lines / 1,877 audited declarations**.

The scope includes Sections 2–4 and 5.1 and the corresponding headline
assertions. Figures, Section 5.2, and technical Section 6 are excluded.
Corollaries 5.2 and 5.3 are in Section 5.1 and remain included.
The theorem statements include the corrected hypotheses and probability budgets.

The computational approach follows the midpoint-Hessian reference project:
explicit algorithms produce values and accumulate declared arithmetic costs.
Operand bit sizes and composed costs must be proved polynomial in finite input
length and requested precision. The former RAM/Turing implementation and the
complexitylib dependency have been removed at the user's request. The numerical
accuracy, canonical-coordinate, and Gaussian-law proofs are retained and refer
directly to rational algorithm outputs. The measured input consists of supplied
finite algebraic metric and width data and the integral coefficient table.
Representation availability is proved; conversion from an unspecified field
presentation is not part of the charged algorithm. Requested precision is
charged by its value.

## Requirements

- `elan` and Lake
- Lean `v4.34.0-rc2`, pinned in `lean-toolchain`
- Mathlib at `e06eff5f95374108acfaf19f1ff7473aa7771df2`

`lake-manifest.json` pins Mathlib and its dependencies. No complexitylib or CSLib
package is required. Builds can reuse the local `.lake` cache.

## Build

From the repository root:

```sh
lake exe cache get
lake build
```

The default library target checks every certificate module, ending with
`GeometricGaussianLHL.Audit`, which prints axiom dependencies. After the first
build, `lake build` alone is sufficient.

The audit and certificate roots can also be built explicitly:

```sh
lake build GeometricGaussianLHL.Audit
lake build GeometricGaussianLHL.Certificate
```

For a clean rebuild:

```sh
lake clean
lake build
```

`lake clean` removes project build products while retaining dependencies.

## Docker Support

Docker provides the pinned Lean toolchain and a Linux build environment.
Docker Engine with Compose, or Docker Desktop, is sufficient.

The image build and full containerized certificate check passed on `linux/arm64`
for the earlier 28-module layout. The current 27-module layout has native build
and axiom-audit validation; Docker has not been rerun for this cleanup.
For further development, use native Lean checks and reserve Docker for final validation.

```sh
docker compose build
docker compose run --rm certificate
```

The `lake-cache` named volume preserves dependencies, Mathlib's precompiled
cache, its downloaded archives, and project build products between runs.
`MATHLIB_CACHE_DIR` points inside that volume so disposable containers reuse
the archives. To discard it:

```sh
docker compose down --volumes
```

Without Compose:

```sh
docker build --tag geometric-gaussian-lhl:local .
docker run --rm --init geometric-gaussian-lhl:local
```

The Debian base and elan installer support `linux/amd64` and `linux/arm64`.
To select a platform explicitly:

```sh
docker buildx build --platform linux/amd64 --load \
  --tag geometric-gaussian-lhl:amd64 .
docker buildx build --platform linux/arm64 --load \
  --tag geometric-gaussian-lhl:arm64 .
```

The `linux/amd64` build example has not been tested here.

## Kernel Audit

[Audit.lean](GeometricGaussianLHL/Audit.lean) prints the axiom dependencies of
the principal completed results. Only Lean's standard logical foundations
are permitted: `propext`, `Classical.choice`, and `Quot.sound`.

The project does not use `sorry`, `admit`, new axioms, or `native_decide` to
stand in for mathematical proofs. A clean axiom audit alone does not establish
paper coverage; the scope and hypotheses of the theorem statements also matter.

## Module Organization

The certificate has **27 proof modules**, all under `GeometricGaussianLHL/`.
Including `lakefile.lean`, the project contains **28 Lean source files** outside
dependencies and temporary verification files. All 27 modules are explicit Lake
roots and are reachable from `Audit.lean`.

`Certificate.lean` is the stable public import. The retained results keep their
theorem names and namespaces; imports of the former small modules must use their new locations.
The contents overviews list the named sections corresponding to the former
small modules. Shared definitions are placed in earlier dependency layers.

| Module | Contents |
| --- | --- |
| [Foundations.lean](GeometricGaussianLHL/Foundations.lean) | Coefficient kernels, duality, and basic parameters |
| [LatticeGeometry.lean](GeometricGaussianLHL/LatticeGeometry.lean) | Intrinsic lattice geometry and covolumes |
| [NumberFieldGeometry.lean](GeometricGaussianLHL/NumberFieldGeometry.lean) | Canonical number-field coordinates and Gram geometry |
| [CyclotomicGeometry.lean](GeometricGaussianLHL/CyclotomicGeometry.lean) | Prime-power and power-of-two geometry |
| [Probability.lean](GeometricGaussianLHL/Probability.lean) | Discrete probability and total variation |
| [GaussianAnalysis.lean](GeometricGaussianLHL/GaussianAnalysis.lean) | Gaussian integrals, products, and periodization |
| [GaussianPoisson.lean](GeometricGaussianLHL/GaussianPoisson.lean) | Poisson summation and lattice Gaussian flatness |
| [GaussianMoments.lean](GeometricGaussianLHL/GaussianMoments.lean) | Gaussian moments, tails, and column estimates |
| [GaussianPushforward.lean](GeometricGaussianLHL/GaussianPushforward.lean) | Gaussian pushforwards and parameter stability |
| [SmoothingBounds.lean](GeometricGaussianLHL/SmoothingBounds.lean) | Smoothing bounds and natural scales |
| [SpectralBounds.lean](GeometricGaussianLHL/SpectralBounds.lean) | Random-matrix spectral bounds |
| [ThetaIntegral.lean](GeometricGaussianLHL/ThetaIntegral.lean) | Theta integrals and coset decomposition |
| [PolynomialWidth.lean](GeometricGaussianLHL/PolynomialWidth.lean) | Polynomial-width smoothing theorems |
| [ConstantWidth.lean](GeometricGaussianLHL/ConstantWidth.lean) | Constant-width smoothing theorems |
| [ShapingGeometry.lean](GeometricGaussianLHL/ShapingGeometry.lean) | Exact spherical shaping and canonical Gram coordinates |
| [Encoding.lean](GeometricGaussianLHL/Encoding.lean) | Finite encodings and dyadic storage |
| [ArithmeticCost.lean](GeometricGaussianLHL/ArithmeticCost.lean) | Arithmetic executions and polynomial cost bounds |
| [AlgebraicInput.lean](GeometricGaussianLHL/AlgebraicInput.lean) | Finite algebraic inputs and interval refinement |
| [MatrixArithmetic.lean](GeometricGaussianLHL/MatrixArithmetic.lean) | Matrix arithmetic, normalization, and costs |
| [MatrixApproximation.lean](GeometricGaussianLHL/MatrixApproximation.lean) | Matrix square-root algorithms, accuracy, and costs |
| [RationalShaping.lean](GeometricGaussianLHL/RationalShaping.lean) | Rational shaping and metric normalization |
| [CanonicalShaping.lean](GeometricGaussianLHL/CanonicalShaping.lean) | Canonical shaping from finite algebraic input |
| [GaussianLHL.lean](GeometricGaussianLHL/GaussianLHL.lean) | Geometric Gaussian leftover-hash theorems |
| [SphericalLHL.lean](GeometricGaussianLHL/SphericalLHL.lean) | Spherical leftover-hash theorems and simultaneous hints |
| [FiniteInputCertificate.lean](GeometricGaussianLHL/FiniteInputCertificate.lean) | Finite-input Gaussian application certificates |
| [Certificate.lean](GeometricGaussianLHL/Certificate.lean) | Public certificate entry point |
| [Audit.lean](GeometricGaussianLHL/Audit.lean) | Axiom audit of the completed certificate |

Each substantial module has a contents overview and named proof sections.
Sections retain the old module names for navigation; related algorithms,
accuracy proofs and cost bounds now share a file. Shared encoding and arithmetic
definitions sit below the numerical algorithms in the import graph.

## Licensing

The code is licensed under Apache License 2.0; see [LICENSE](LICENSE).
