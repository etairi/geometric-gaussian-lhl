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
