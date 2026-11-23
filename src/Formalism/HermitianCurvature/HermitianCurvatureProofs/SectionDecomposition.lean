module

public import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FlagSpanVanishing
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFlagVector
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.InverseSplitting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerParabolicCoordinates
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SectionDecompositionOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerPairs
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerSplit
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ZhatSectionExists
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.FourierDecayAlt.P

theorem c2_section_decomp : Formalism.FourierDecayAlt.C2.SectionDecomp :=
  c2_section_decomp_of_pieces stabilizer_split stabilizer_pairs unipotent_radical_image upper_splitting standard_flag_property
    unipotent_map_frame zhat_equivalence c2_tau_mem

end Formalism.FourierDecayAlt.P
