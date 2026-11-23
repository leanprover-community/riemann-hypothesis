module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.InductiveHeisenbergInputs
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.AStepSuccOf
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.BStepSuccOf
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HeisenbergHaarFactsHold
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.IndexEmbeddingBijective
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.MeasurableHaarKernelTriple
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.OsOf
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.OscillatoryBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.PolynomialGrowthIntegrals
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.ProdIicCastLE
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.TLeftH
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.TailFinOf
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.XiExists2
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.XiIntH
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.XiIntStepOf

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.DS.Xi

theorem xiExists_of_in (h : InductiveHeisenbergInputs) : Formalism.FourierDecayAlt.B.XiExists :=
  xiExists_of_induction_steps (aStepBase_of h (tBothH iwB h))
    (aStepSucc_of h iwB (tLeftH iwB h) FormulaFAux.formulaF_all (ch_of c1))
    (bStepBase_of h)
    (bStepSucc_of h iwB FormulaFAux.formulaF_all
      (oscillatoryBound' (tailFin_of (ch_of c1)) c1 quadraticSublevelDecay' ker slow))
    (coefStep_of h (tBothH iwB h) (det_of h)) (xiIntH h)

theorem xiExists : Formalism.FourierDecayAlt.B.XiExists := xiExists_of_in heisenbergHaarFacts_hold

end ReciprocityTheory.ChartRestriction.DS.Xi
