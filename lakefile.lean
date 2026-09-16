import Lake

open Lake DSL

package «geometric-gaussian-lhl-certificate» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "e06eff5f95374108acfaf19f1ff7473aa7771df2"


-- Explicit roots also ensure that every proof module is built independently.
@[default_target]
lean_lib GeometricGaussianLHL where
  roots := #[
    `GeometricGaussianLHL.Foundations,
    `GeometricGaussianLHL.LatticeGeometry,
    `GeometricGaussianLHL.NumberFieldGeometry,
    `GeometricGaussianLHL.CyclotomicGeometry,
    `GeometricGaussianLHL.Probability,
    `GeometricGaussianLHL.GaussianAnalysis,
    `GeometricGaussianLHL.GaussianPoisson,
    `GeometricGaussianLHL.GaussianMoments,
    `GeometricGaussianLHL.GaussianPushforward,
    `GeometricGaussianLHL.SmoothingBounds,
    `GeometricGaussianLHL.SpectralBounds,
    `GeometricGaussianLHL.ThetaIntegral,
    `GeometricGaussianLHL.PolynomialWidth,
    `GeometricGaussianLHL.ConstantWidth,
    `GeometricGaussianLHL.ShapingGeometry,
    `GeometricGaussianLHL.Encoding,
    `GeometricGaussianLHL.ArithmeticCost,
    `GeometricGaussianLHL.AlgebraicInput,
    `GeometricGaussianLHL.MatrixArithmetic,
    `GeometricGaussianLHL.MatrixApproximation,
    `GeometricGaussianLHL.RationalShaping,
    `GeometricGaussianLHL.CanonicalShaping,
    `GeometricGaussianLHL.GaussianLHL,
    `GeometricGaussianLHL.SphericalLHL,
    `GeometricGaussianLHL.FiniteInputCertificate,
    `GeometricGaussianLHL.Certificate,
    `GeometricGaussianLHL.Audit
  ]

@[default_target]
lean_lib SISToKSIS where
  roots := #[`«SIS-to-kSIS».BlockAlgebra, `«SIS-to-kSIS».UniformSimulation,
    `«SIS-to-kSIS».SolutionExtraction, `«SIS-to-kSIS».OperatorBounds,
    `«SIS-to-kSIS».GeometricHints, `«SIS-to-kSIS».GaussianChangeOfMeasure,
    `«SIS-to-kSIS».GameBounds, `«SIS-to-kSIS».Parameters,
    `«SIS-to-kSIS».ModularLattices, `«SIS-to-kSIS».AdversaryChangeOfMeasure,
    `«SIS-to-kSIS».HintGames, `«SIS-to-kSIS».GaussianWidths,
    `«SIS-to-kSIS».CanonicalExtraction, `«SIS-to-kSIS».ReverseSampling,
    `«SIS-to-kSIS».GaussianConditioning,
    `«SIS-to-kSIS».GaussianFactorization,
    `«SIS-to-kSIS».SpectralHints,
    `«SIS-to-kSIS».IdealGeometry,
    `«SIS-to-kSIS».PrimeResidueBounds,
    `«SIS-to-kSIS».ResidueMass,
    `«SIS-to-kSIS».HintIndependence,
    `«SIS-to-kSIS».FiniteResidueGames,
    `«SIS-to-kSIS».ModularReverseSampling,
    `«SIS-to-kSIS».ModularDuality,
    `«SIS-to-kSIS».GaussianRegularity,
    `«SIS-to-kSIS».CosetAveraging,
    `«SIS-to-kSIS».ModularRegularity,
    `«SIS-to-kSIS».FiniteSampling,
    `«SIS-to-kSIS».Audit]
