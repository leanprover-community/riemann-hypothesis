module

public import CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.ZuckDualTOfZuckDual
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Transported
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.FormalDegreeConstantDiscrete

@[expose] public section

namespace CompanionTheory.Zuck

theorem zuckT_thrS : CompanionTheory.LimBd.Main.ZuckT fun _ ε => ReciprocityTheory.ChartRestriction.DS.G2.thrS ε := by
  intro n ε μ H _ _ _ σ hμ hσ h hg hlt
  obtain ⟨X, -⟩ := ReciprocityTheory.ChartRestriction.DS.G2.zuckerman_tensor_exists n ε μ H σ hμ hσ h hg hlt
  exact ⟨X⟩

theorem zuckDualT_thrS : CompanionTheory.LimBd.Main.ZuckDualT fun _ ε => ReciprocityTheory.ChartRestriction.DS.G2.thrS ε := by
  intro n ε μ H _ _ _ σ hμ hσ h hg hlt
  obtain ⟨X, -⟩ := ReciprocityTheory.ChartRestriction.DS.G2.zuckerman_dual_tensor_exists n ε μ H σ hμ hσ h hg hlt
  exact ⟨X⟩

end CompanionTheory.Zuck
