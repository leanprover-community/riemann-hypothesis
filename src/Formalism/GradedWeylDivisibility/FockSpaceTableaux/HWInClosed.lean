module

public import Formalism.GradedWeylDivisibility.StatementB
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwinLemmas
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

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem hwInClosed_of (h1 : HWLine) (h2 : RowDivClosedGraded) : HWInClosed := by
  intro r n hn ν hν M hMle hM hne
  obtain ⟨v, hvM, hv0, hkill⟩ := lhwin_exists_killed h2 M hM hne
  obtain ⟨c, hc⟩ := h1 ℚ r n hn ν hν v (hMle hvM) hkill
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hv0 (by simpa using hc)
  have e : hw ℚ hn ν = c⁻¹ • v := by
    rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [e]
  exact M.smul_mem _ hvM

end Formalism.GradedWeylDivisibility
