module

public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.StatementS
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.CurveFormalFirstLevelHolds
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Hurwitz
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.HurwitzB
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.InverseEndoIntegralHolds
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Several
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

@[expose] public section

namespace Formalism.L2.Th1.G

theorem jetsInNorm : JetsInNorm := jets_in_norm_holds
theorem jetsRing : JetsRing := jets_ring_holds
theorem jetsExp : JetsExp := jets_exp_holds
theorem jetsFourth : JetsFourth := jets_fourth_holds
theorem intDJets : IntDJets := integral_dist_jets_holds

theorem invEndInt : InvEndInt := inverse_endo_integral_holds
theorem adjUnitNorm : AdjUnitNorm := adjoint_unit_norm_holds
theorem ramifiedShape : RamifiedShape := ramified_shape_holds
theorem curveNegNorm : CurveNegNorm := curve_neg_norm_holds
theorem weierstrass_biadditive_mod_equiv : WeierstrassBiadditiveModEquiv := curve_formal_first_level_holds
theorem curveRamified : CurveRamified := CurveRamified_of_shape ramifiedShape adjUnitNorm invEndInt

theorem eigenSplit : EigenSplit := eigen_split_holds
theorem shapeCong : ShapeCong := shape_congruence_holds
theorem shapeOrth : ShapeOrth := shape_orthogonal_holds

end Formalism.L2.Th1.G
