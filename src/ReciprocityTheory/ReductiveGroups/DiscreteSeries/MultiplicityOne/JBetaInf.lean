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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBetaInfA

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem stBetaInf (h : UnitaryGroupStructuralFacts) : StBetaInf := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hRB, hRA, -, hAe, hDJ⟩ := h
  have hDJ' : DilJacAll := by first | exact hDJ | exact hDJ.1
  intro k r Wp Wq _ _ _ _ _ _ D A hXi hA F F' hF hF' hP
  obtain ⟨Ξ, hCB, hXI⟩ := hXi k r Wp Wq D A hA
  exact BetaInfA.betaInf_eq_of D A hAe (hRB k r Wp Wq D Ξ A hA hCB hXI)
    (hRA k r Wp Wq D Ξ A hA hCB hXI (hDJ' k r Wp Wq D)) (BetaInfA.inCC_five_four hF)
    (BetaInfA.inCC_five_four hF') hP

end ReciprocityTheory.ChartRestriction.DS.Mult1
