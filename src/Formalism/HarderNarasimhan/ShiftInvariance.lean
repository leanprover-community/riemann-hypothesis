module

public import Formalism.HarderNarasimhan.DegSupermodZ
public import Formalism.HarderNarasimhan.QuotRealize
public import Formalism.HarderNarasimhan.StatementFrameF
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DegSupermod
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DualPl
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.ExistsSmulMemOfFinrankEq
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.FinSup
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HNSlopes
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HNStep
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtGram
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtImage
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.MuChar
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PolygonSlopeSum
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.QuotRealize
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.RatioMax
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Rerealize
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.RescaleCovol
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SatBasic
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.ShiftInvariance
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeIneq
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeMu
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneqMean
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.TheoremFSharp
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.TwistFinrankEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.HN

theorem satR : SatR := real_saturation_property
theorem finSup : FinSup := finite_supremum_slopes
theorem satBasic : SatBasic := saturation_basic_properties
theorem ratioMax : RatioMax := maximal_slope_ratio
theorem degSupermod : DegSupermod := degree_supermodular
theorem muChar : MuChar := slope_characterization
theorem hnStep_spec : HNStep := hnStep_of degSupermod muChar ratioMax finSup satR satBasic
theorem hnSum : HNSum := polygon_slope_sum
theorem hnSlopes : HNSlopes := polygon_slopes_characterization
theorem shiftInvariance : ShiftInvariance := shiftInvariance_of muChar muChar hnSlopes
theorem plLat : PlLat := place_lattice_structure
theorem sizeMu : SizeMu := size_maximal_slope
theorem rescaleCovol : RescaleCovol := rescale_covolume_formula
theorem twist : Twist := twist_of rescaleCovol plLat shiftInvariance
theorem slopeIneqMean : SlopeIneqMean := slope_inequality_mean
theorem htGram : HtGram := height_gram_determinant
theorem htImage : HtImage := height_image_formula
theorem sizeIneq : SizeIneq := sizeIneq_of size_maximal_slope height_image_formula place_lattice_structure
theorem rerealize : Rerealize := lattice_rerealization
theorem quotRealize : QuotRealize := quotient_lattice_realization
theorem theoremFSharp : TheoremFSharp := frame_theorem_sharp
theorem theoremF : TheoremF := frame_theorem_log_ideal
theorem dualPl : DualPl := dual_polygon_identity

end Formalism.HN
