module

public import Formalism.HermitianCurvature.ArchimedeanUniformConstantsCompactSupport
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BuiltBoundsCompactOfLeaves
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DegreeTop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermRateBound
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadGermSmoothExtension
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormsJointContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGDegLift
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopLocalBuiltPlaces
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopRatioAlt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UniformDecayOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UniformDecayOfPlace
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
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermPartsCompactSupport

@[expose] public section

namespace Formalism.FourierDecayAlt.P

theorem built_bounds_compact_of_head_top (hH : Formalism.FourierDecayAlt.KB.HeadTop) : Formalism.FourierDecayAlt.KB.BuiltBounds2Cpt := fun hA =>
  built_bounds_compact_of_leaves radial_head hH degree_of_lift_pairing top_local_built_places degree_top
    top_ratio (germ_parts_compact_support kernel_continuity_built germ_rate_bound hA)
    (fun hA' => uniform_decay_of_place hA' radial_head hH
      (uniform_decay_of_heads radial_head hH)) hA

end Formalism.FourierDecayAlt.P
