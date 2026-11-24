module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCapAdjCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCV
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCap
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCapAdjFrom
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERComm
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

namespace Formalism.FourierDecayAlt.P.CutMP.ER

theorem energyReal_of_capAdj (hA : CapAdj) : Formalism.FourierDecayAlt.P.CutMP.EnergyReal :=
  energyReal_of_leaves hA capacity_theta_facts coefficient_vector_smoothness coefficient_vector_in_class coefficient_vector_support coefficient_vector_congr coefficient_vector_commutation
    beta_form_congr_holds

theorem energyReal_of_capAdjInt (hI : CapAdjInt) : Formalism.FourierDecayAlt.P.CutMP.EnergyReal :=
  energyReal_of_capAdj (capAdj_of_int hI)

end Formalism.FourierDecayAlt.P.CutMP.ER
