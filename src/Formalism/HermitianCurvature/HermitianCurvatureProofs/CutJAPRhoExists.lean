module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRho
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRhoAssembly
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRhoCapSmooth
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRhoEigOrth
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRhoFrameLoc
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRhoLagrange
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

theorem rho_projection_existence : PRho.PRhoExists :=
  PRhoCut.pRhoExists_of_cut PRhoCut.rho_projection_assembly PRhoCut.frame_locality_holds PRhoCut.capacity_smoothness_holds
    PRhoCut.eigenvector_orthogonality_holds PRhoCut.lagrange_annihilation

end Formalism.FourierDecayAlt.P.CutMP.JA
