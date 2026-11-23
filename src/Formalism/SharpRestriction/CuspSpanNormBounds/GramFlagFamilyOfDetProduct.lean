module

public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GenusMassPosOfMassLowerBound

@[expose] public section

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.GramProductBounds

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals
  Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem NE_pow (D : D7) : NE (E := D.host.E) (gS D) ^ (D.R.rS + 1) = (gS D : ℝ) ^ (D.R.m * D.R.f) := by
  unfold NE
  rw [j_finrank D, ← pow_mul]
  congr 1
  have h2 := D.R.two_le_m
  obtain ⟨k, hk⟩ := D.R.m_even
  have hm : 2 * (D.R.rS + 1) = D.R.m := by
    unfold Ranks.rS
    omega
  rw [← hm]
  ring

end Formalism.MainNotions.GramProductBounds

end
