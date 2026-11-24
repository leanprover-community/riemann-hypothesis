module

public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightConvolutionOperatorAeEqIntegralAdelic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Formalism.FormalDegreeBessel.StatementWR

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.rightConvolution_operator_ae_eq_integral_adelic : ∀ (B : RowsAut) (φ : B.I.GA → ℂ) (T : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund), B.I.IsRConv B.μf B.fund B.R φ T → ∀ y : B.I.L2 B.μf B.fund, (∀ᵐ x ∂((B.I.muA B.μf).restrict B.fund), Integrable (fun g => φ g * B.I.ext y (x * g)) (B.I.muA B.μf)) ∧ (T y : B.I.GA → ℂ) =ᵐ[(B.I.muA B.μf).restrict B.fund] fun x => ∫ g, φ g * B.I.ext y (x * g) ∂(B.I.muA B.μf) := by
  first | exact @GlobalTheory.ConvKernel.rconv_eq_integral | exact GlobalTheory.ConvKernel.rconv_eq_integral | (intros; apply GlobalTheory.ConvKernel.rconv_eq_integral <;> assumption)
