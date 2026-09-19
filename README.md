# Lean Certificates for the Geometric Gaussian LHL

This repository contains Lean 4 certificates for the manuscript
*Gaussian Kernel Lattices and Smoothing Bounds from Theta Integrals*.
`GeometricGaussianLHL` formalizes the kernel-lattice geometry, smoothing bounds,
and Gaussian leftover-hash lemmas, together with finite-input shaping certificates.
`SISToKSIS` formalizes the SIS-to-kSIS reduction from ePrint 2025/1852 with the
manuscript's improved finite parameters, reusing the geometric Gaussian LHL.
Both libraries share this Lake project.

## Requirements

- `elan` and Lake
- the Lean version in `lean-toolchain` (`v4.34.0-rc2`)

Mathlib and its dependencies are pinned in `lake-manifest.json`. Later builds
can reuse the local `.lake` cache.

## Build

From the repository root:

```sh
lake exe cache get
lake build
```

The default targets include all 27 geometric certificate modules and all 29
SIS-to-kSIS modules, including both axiom audits. After the first build,
`lake build` alone is sufficient.

The geometric audit and public certificate can also be built explicitly:

```sh
lake build GeometricGaussianLHL.Audit
lake build GeometricGaussianLHL.Certificate
```

To build the reduction and its audit, together with the geometric modules it
imports:

```sh
lake build SISToKSIS
```

For a clean rebuild:

```sh
lake clean
lake exe cache get
lake build
```

`lake clean` removes project build products but retains downloaded dependencies.
The cache command restores available precompiled Mathlib artifacts.

## Docker Support

Docker provides the pinned Lean toolchain and a Linux build environment, so no
host installation of Lean or Lake is required. Docker Engine with the Compose
plugin, or Docker Desktop, is sufficient.

The recommended workflow uses Compose because its named volume preserves
dependencies, the downloaded Mathlib cache, and project build products:

```sh
docker compose build
docker compose run --rm certificate
```

The first run downloads Mathlib's precompiled cache and checks both certificates.
Later runs reuse the `lake-cache` volume. To intentionally discard that cache
and force a fresh build, run:

```sh
docker compose down --volumes
```

The image can also be used without Compose:

```sh
docker build --tag geometric-gaussian-lhl:local .
docker run --rm --init geometric-gaussian-lhl:local
```

The Debian base image and `elan` installer support both `linux/amd64` and
`linux/arm64`; Docker automatically chooses the native platform. A specific
platform can be selected for CI or cross-platform testing:

```sh
docker buildx build --platform linux/amd64 --load \
  --tag geometric-gaussian-lhl:amd64 .
docker buildx build --platform linux/arm64 --load \
  --tag geometric-gaussian-lhl:arm64 .
```

## Kernel Audit

[`GeometricGaussianLHL/Audit.lean`](GeometricGaussianLHL/Audit.lean) prints the
axiom dependencies of 2,461 certificate declarations.
[`SIS-to-kSIS/Audit.lean`](SIS-to-kSIS/Audit.lean) recursively audits 2,958
declarations in the reduction namespace and rejects unexpected axioms.
Successful audits report only Lean's standard logical foundations:
`propext`, `Classical.choice`, and `Quot.sound`.

The principal geometric declarations, in namespace `GeometricGaussianLHL`, are:

- `numberField_polynomial_lhl`
- `numberField_constantWidth_lhl`
- `numberField_polynomial_finite_spectral`
- `numberField_constantWidth_finite_spectral`
- `canonicalFinite_endToEnd_certificate`

The principal reduction declarations, in namespace `SISToKSIS`, are:

- `encodedReductionRun_field_law`
- `encodedReduction_joint_game`
- `encodedReductionRun_polynomial`
- `powerTwo_polynomial_encoded_SIS_reduction`
- `powerTwo_constant_encoded_SIS_reduction`

The final reduction theorems bound the success probability of the implemented
finite program, including Gaussian sampling, hint construction, the oracle call,
and extraction. They cover both geometric parameter regimes. The scope excludes
figures, comparisons with prior work, k-LWE, asymptotic prime search, and a
separate reduction theorem for asymptotic security families.

The computational certificates use explicit algorithms with declared arithmetic
costs and proved polynomial operand and output sizes, following the
midpoint-Hessian approach. Inputs include supplied finite algebraic metric and
width data; the reduction also takes an encoded basis multiplication table,
unit coordinates, and source matrix. Requested precision is charged by its
value. Conversion from an unspecified field presentation is outside the charged
algorithm. The reduction's polynomial bound assumes a polynomial declared-cost
and output-length contract for its oracle.

## Module Organization

Every proof module is an explicit Lake root. The two libraries contain 56 Lean
source files, grouped below by proof component; dependencies are recorded in
their imports. Substantial modules retain named internal sections for navigation.

### Geometric Gaussian LHL

The 27 modules in [`GeometricGaussianLHL/`](GeometricGaussianLHL/) are:

| Component | Modules | Role |
| --- | --- | --- |
| Lattice and number-field geometry | [Foundations.lean](GeometricGaussianLHL/Foundations.lean), [LatticeGeometry.lean](GeometricGaussianLHL/LatticeGeometry.lean), [NumberFieldGeometry.lean](GeometricGaussianLHL/NumberFieldGeometry.lean), [CyclotomicGeometry.lean](GeometricGaussianLHL/CyclotomicGeometry.lean) | Coefficient kernels, duality, covolumes, and canonical field coordinates |
| Probability and Gaussian analysis | [Probability.lean](GeometricGaussianLHL/Probability.lean), [GaussianAnalysis.lean](GeometricGaussianLHL/GaussianAnalysis.lean), [GaussianPoisson.lean](GeometricGaussianLHL/GaussianPoisson.lean), [GaussianMoments.lean](GeometricGaussianLHL/GaussianMoments.lean), [GaussianPushforward.lean](GeometricGaussianLHL/GaussianPushforward.lean) | Total variation, Gaussian integrals, Poisson summation, moments, and pushforwards |
| Geometric smoothing bounds | [SmoothingBounds.lean](GeometricGaussianLHL/SmoothingBounds.lean), [SpectralBounds.lean](GeometricGaussianLHL/SpectralBounds.lean), [ThetaIntegral.lean](GeometricGaussianLHL/ThetaIntegral.lean), [PolynomialWidth.lean](GeometricGaussianLHL/PolynomialWidth.lean), [ConstantWidth.lean](GeometricGaussianLHL/ConstantWidth.lean) | Theta-integral and spectral estimates for both width regimes |
| Finite inputs and costs | [Encoding.lean](GeometricGaussianLHL/Encoding.lean), [ArithmeticCost.lean](GeometricGaussianLHL/ArithmeticCost.lean), [AlgebraicInput.lean](GeometricGaussianLHL/AlgebraicInput.lean) | Finite encodings, algebraic input refinement, and declared arithmetic costs |
| Gaussian shaping | [ShapingGeometry.lean](GeometricGaussianLHL/ShapingGeometry.lean), [MatrixArithmetic.lean](GeometricGaussianLHL/MatrixArithmetic.lean), [MatrixApproximation.lean](GeometricGaussianLHL/MatrixApproximation.lean), [RationalShaping.lean](GeometricGaussianLHL/RationalShaping.lean), [CanonicalShaping.lean](GeometricGaussianLHL/CanonicalShaping.lean) | Exact shaping, numerical matrix algorithms, accuracy, and polynomial costs |
| Leftover-hash theorems | [GaussianLHL.lean](GeometricGaussianLHL/GaussianLHL.lean), [SphericalLHL.lean](GeometricGaussianLHL/SphericalLHL.lean), [FiniteInputCertificate.lean](GeometricGaussianLHL/FiniteInputCertificate.lean) | Geometric and spherical Gaussian LHLs and their finite-input certificates |
| Public certificate and audit | [Certificate.lean](GeometricGaussianLHL/Certificate.lean), [Audit.lean](GeometricGaussianLHL/Audit.lean) | Public import and axiom dependencies |

`Certificate.lean` is the public import for the geometric, Gaussian, and finite
computational results:

```lean
import GeometricGaussianLHL.Certificate
```

### SIS-to-kSIS Reduction

The 29 modules in [`SIS-to-kSIS/`](SIS-to-kSIS/) are:

| Component | Modules | Role |
| --- | --- | --- |
| Algebra and extraction | [BlockAlgebra.lean](SIS-to-kSIS/BlockAlgebra.lean), [UniformSimulation.lean](SIS-to-kSIS/UniformSimulation.lean), [SolutionExtraction.lean](SIS-to-kSIS/SolutionExtraction.lean) | Exact block identities, uniform public simulation, and nonzero solution extraction |
| Norms and parameters | [OperatorBounds.lean](SIS-to-kSIS/OperatorBounds.lean), [CanonicalExtraction.lean](SIS-to-kSIS/CanonicalExtraction.lean), [Parameters.lean](SIS-to-kSIS/Parameters.lean) | Operator norm loss and explicit arithmetic and error bounds |
| Geometric hints | [GeometricHints.lean](SIS-to-kSIS/GeometricHints.lean), [SpectralHints.lean](SIS-to-kSIS/SpectralHints.lean) | Reuse of the geometric LHL and simultaneous spectral hint bounds |
| Gaussian change of measure | [GaussianChangeOfMeasure.lean](SIS-to-kSIS/GaussianChangeOfMeasure.lean), [AdversaryChangeOfMeasure.lean](SIS-to-kSIS/AdversaryChangeOfMeasure.lean), [GaussianWidths.lean](SIS-to-kSIS/GaussianWidths.lean) | Centered-to-shifted comparison, shift energy, and adversary success loss |
| Probability games | [GameBounds.lean](SIS-to-kSIS/GameBounds.lean), [HintGames.lean](SIS-to-kSIS/HintGames.lean), [ReverseSampling.lean](SIS-to-kSIS/ReverseSampling.lean), [GaussianConditioning.lean](SIS-to-kSIS/GaussianConditioning.lean) | Conditioning, reverse sampling, and hybrid comparisons |
| Residue mass and independence | [ModularLattices.lean](SIS-to-kSIS/ModularLattices.lean), [IdealGeometry.lean](SIS-to-kSIS/IdealGeometry.lean), [PrimeResidueBounds.lean](SIS-to-kSIS/PrimeResidueBounds.lean), [ResidueMass.lean](SIS-to-kSIS/ResidueMass.lean), [HintIndependence.lean](SIS-to-kSIS/HintIndependence.lean) | Modular lattices, prime-ideal Gaussian mass, and hint independence |
| Modular Gaussian regularity | [FiniteResidueGames.lean](SIS-to-kSIS/FiniteResidueGames.lean), [ModularReverseSampling.lean](SIS-to-kSIS/ModularReverseSampling.lean), [ModularDuality.lean](SIS-to-kSIS/ModularDuality.lean), [GaussianRegularity.lean](SIS-to-kSIS/GaussianRegularity.lean), [CosetAveraging.lean](SIS-to-kSIS/CosetAveraging.lean) | Finite quotient laws, dual Gaussian mass, and regularity for uniform public matrices |
| Finite sampling | [FiniteSampling.lean](SIS-to-kSIS/FiniteSampling.lean), [GaussianFactorization.lean](SIS-to-kSIS/GaussianFactorization.lean) | Finite-word Gaussian samplers, stored matrix algorithms, accuracy, and costs |
| Final reduction | [ModularRegularity.lean](SIS-to-kSIS/ModularRegularity.lean) | Complete encoded program, oracle integration, and both final parameter theorems |
| Kernel audit | [Audit.lean](SIS-to-kSIS/Audit.lean) | Recursive axiom audit of the reduction namespace |

`ModularRegularity.lean` assembles the encoded program, its probability laws and
polynomial costs, and both final parameter theorems. The supporting regularity
and sampling modules connect the finite implementation to the existing
geometric LHL. Import the reduction through:

```lean
import «SIS-to-kSIS».ModularRegularity
```

## Dependencies and Licensing

Mathlib is pinned to commit
`e06eff5f95374108acfaf19f1ff7473aa7771df2` in `lakefile.lean` and
`lake-manifest.json`. It supplies the algebra, analysis, probability, and
number-field foundations. The SIS-to-kSIS library imports the local
`GeometricGaussianLHL` library directly.

This repository is licensed under Apache License 2.0; see
[`LICENSE`](LICENSE).
