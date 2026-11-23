module

public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreDefs
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.TensorIrr
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreComb
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreMain
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreNonv
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CorePair
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreSide
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

theorem coreLM : CoreLM := by
  intro D h
  obtain ⟨hn, hm, e1, e2, hP, hQ, hQ', hP'⟩ := nm_facts h
  have c1 : ((D.κ : ℂ) / 2) = (((D.κ : ℚ) / 2 : ℚ) : ℂ) := by push_cast; rfl
  have c2 : (-((D.κ : ℂ) / 2)) = ((-((D.κ : ℚ) / 2) : ℚ) : ℂ) := by push_cast; rfl
  have n1 : Nontrivial (ThV D) :=
    nontrivial_of_pair _ _ c1 (c1 ▸ pair_pos hP hQ hn hm _ e1 e2)
  have n2 : Nontrivial (ThV' D) :=
    nontrivial_of_pair _ _ c2 (c2 ▸ pair_neg hQ' hP' hn hm _ (by linarith) (by linarith))
  have s1 := side_of ((D.κ : ℂ) / 2) 0 _ 0 c1 (by simp) _ (combV h) n1
  have s2 := side_of (-((D.κ : ℂ) / 2)) ((D.κ : ℂ) / 2) _ _ c2 c1 _ (combV' h) n2
  rw [la_eq h] at s2
  obtain ⟨Pi, i1, i2, act, π, π', h1, h2, h3, h4, h5, h6⟩ := common_quot _ _ _ _ _ s1 s2
  refine ⟨Pi, i1, i2, act, π, π', h1, h2, fun W x => ?_, fun W x => h4 W x, h5, h6⟩
  rw [← h3 W x]
  congr 1
  simp [thAct, opV]

end PositivityTheory.KReal

end
