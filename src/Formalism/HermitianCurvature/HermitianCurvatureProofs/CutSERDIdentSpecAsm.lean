module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSCoordAdj
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDOpFF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDResRad
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSFund
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSSection
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSYReal
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

namespace Formalism.FourierDecayAlt.P.CutSE

theorem rDIdentSpec_of_open (h0 : RDSOpAv) (h1 : RDSOpR) (h2 : RDSOpRv) (h3 : RDSOpA)
    (hp : RDSPAdj) (hQ : RDSQQAdj) (hX : RDSXiTest) (hP : RDSPair) : RDIdentSpec :=
  rDIdentSpec_of_cut spectral_Y_real h0 h1 h2 h3 spectral_inner_product_linear (rDSCoordAdj_of_p hp) spectral_function_adjoint hQ hX spectral_fundamental_identity spectral_section_identity hP
    radial_residue_formula radial_operator_function_field

end Formalism.FourierDecayAlt.P.CutSE
