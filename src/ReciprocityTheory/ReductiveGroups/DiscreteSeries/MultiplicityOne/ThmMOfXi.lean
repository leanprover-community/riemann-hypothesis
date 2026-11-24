module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.InHolds
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBeConv
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBeEquiv
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBeHerm
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBePos
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBetaInf
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JDichoG
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JDichoW
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JFrame
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvCC
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvChar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvGroup
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JMixed
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JPairs
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JRankOne
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JRepro
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSchurG
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSchurW
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSmooth
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSymBeta
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JTransM
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StReps
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StSInt
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.TheoremMOf
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UuInv
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.XiExistsOfIn

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

theorem thmM_of_xi (h : UnitaryGroupStructuralFacts) (hXi : Formalism.FourierDecayAlt.B.XiExists) : ThmM :=
  theoremM_of h hXi (stBeHerm h) (stBePos h) (stSchurW h) (stSInt h) stSchurG (stPairs h) (stBeConv h) (stBeEquiv h)
    (stRepro h) (stSmooth h) stFrame (stInvGroup h) stInvChar stInvCC (stReps h) (stTransM h) (stSym h) (stSymBeta h)
    (stBetaInf h) (stDichoG h) (stDichoW h) (stMixed h) rankOneMinors

theorem thmM : ThmM := thmM_of_xi multiplicity_one_hypotheses_hold ReciprocityTheory.ChartRestriction.DS.Xi.xiExists

end ReciprocityTheory.ChartRestriction.DS.Mult1
