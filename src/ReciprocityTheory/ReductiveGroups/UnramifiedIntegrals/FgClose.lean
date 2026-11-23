module

public import Formalism.FormalGroupLog.Statement
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.CoeffOneSubstOfConstantCoeffEqZero
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.EndIntegral
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgBasic
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgMulN
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.NormSqrtNegPowPrimeSqSub
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ShortWIntModel
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TchOfIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneSubTwoOmegaSq

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

theorem integral_of_map_kur {l : ℕ} [Fact l.Prime] {f : PowerSeries (MaximalUnramifiedExtension l)}
    (h : IntegralPS (PowerSeries.map (MaximalUnramifiedExtension l).subtype f)) : IntegralPS f := fun n => by
  have := h n
  rw [PowerSeries.coeff_map] at this
  exact this

theorem cm3 : CM3 :=
  GlobalTheory.HondaCM3.cm3

end ReciprocityTheory.ChartRestriction.L1
