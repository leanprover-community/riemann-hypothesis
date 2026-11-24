module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.WickFormula
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.WickFormula.GenPow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.WickFormula.GenVan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.WickFormula.LprodAddSmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.WickFormula.XdegLeTotalDegree

@[expose] public section

theorem wick_formula : PI.WickFormula :=
  PI.WickFormula.wickFormula_of PI.WickFormula.ordLin_holds PI.WickFormula.ordX_holds
    PI.WickFormula.base_holds PI.WickFormula.bComm_holds PI.WickFormula.Gen.powXL_holds
    PI.WickFormula.Gen.commL_holds PI.WickFormula.Gen.vanL_holds
