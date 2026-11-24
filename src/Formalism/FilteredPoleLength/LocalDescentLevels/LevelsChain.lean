module

public import Formalism.FilteredPoleLength.ReducedBasisBounds.LengthBaseChangeLocal
public import Formalism.FilteredPoleLength.LocalDescentLevels.BCount
public import Formalism.FilteredPoleLength.LocalDescentLevels.FilIntegerStep
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

@[expose] public section

namespace Formalism.LatticeBaseChangeAlt

open Module

theorem levelsChain : LevelsChain := by
  intro ι _ ep f ν v νs c' T e hep hT hc' hv hν hcase
  apply levelsSum ι ep f (fun z => max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - e)⌉) v T c'
  intro z
  have hpos : (0 : ℝ) < ep z := by exact_mod_cast hep z
  have h : ((max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - e)⌉ : ℤ) : ℝ) / ep z ≤ T * c' * v z := by
    rcases hcase with ⟨h1, h2⟩ | h3
    · exact poleOrderGood (ep z) T (ν z) νs c' (v z) e (hep z) hc' (hv z) (hν z) (h2 z) h1
    · subst h3
      exact poleOrderBad (ep z) T (ν z) νs c' (v z) (hep z) hT hc' (hv z) (hν z)
  rw [div_le_iff₀ hpos] at h
  linarith

end Formalism.LatticeBaseChangeAlt
