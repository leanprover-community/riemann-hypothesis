module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEX2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXHeadFam
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMkCpt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXPbEquiv2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXPbRight2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXPbSmooth
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXPbSupp2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXRadSliceTop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXSliceTop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXTopPt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEX_UwTop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXp
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstBasisVectorIsRadialSlice
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameParameterRegularity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadGermSmoothExtension
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbHeadTopOf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopUnipotentIntegralPositive
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

namespace Formalism.FourierDecayAlt.P

theorem pb_exhPic_of_mkTop (hMk : CutEX.MkTop) : PBI.ExhPic :=
  CutEX.exhPic_of_leaves CutEX.exceptional_assumption_holds unipotent_weight_top slice_top_exhaustion pullback_smooth
    pullback_right_action pullback_support pullback_equivalence hMk compact_truncation_construction top_point_existence
    determinant_exceptional_holds head_family_exhaustion radial_slice_top radial_of_function_exceptional radial_extension_exceptional
    residue_top_exceptional_level frame_parameter_regularity (pb_radWordSliceOfHeadPic head_picture) level_zero_picture_of_slice

theorem pb_headTop_of_mkTop (hMk : CutEX.MkTop) : KB.HeadTop :=
  pb_headTop_of top_unipotent_integral (pb_exhPic_of_mkTop hMk)

end Formalism.FourierDecayAlt.P
