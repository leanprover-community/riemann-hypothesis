module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomAssemble
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomAtGq
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomUBL
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.EmbeddingMulVecFactorization
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GeometryEquivarianceEmbedding
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GeometryEquivarianceFirstVector
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothHermitianRankTwo
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

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem second_shift_geometry_holds : SSn.SSnGeom :=
  SSn.Geom.geometry_assembly_holds SSn.Geom.geometry_smoothness_holds SSn.Geom.geometry_equivariance_first_vector SSn.Geom.geometry_equivariance_embedding
    SSn.Geom.geometry_at_level_function SSn.Geom.geometry_boundedness_at_zero SSn.Geom.geometry_unipotent_bound_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
