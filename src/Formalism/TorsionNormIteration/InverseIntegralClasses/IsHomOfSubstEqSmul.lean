module

public import Mathlib.RingTheory.PowerSeries.Substitution
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule

@[expose] public section

noncomputable section

open PowerSeries

namespace Formalism.LT.PadicP

open Formalism.G

section LtLog

variable {p : ℕ} [hp : Fact p.Prime]


end LtLog

theorem coeff_one_subst {R : Type} [CommRing R] (f a : PowerSeries R)
    (hf0 : constantCoeff f = 0) (ha0 : constantCoeff a = 0) :
    coeff 1 (f.subst a) = coeff 1 f * coeff 1 a := by
  have ha : HasSubst a := HasSubst.of_constantCoeff_zero' ha0
  change MvPowerSeries.coeff (Finsupp.single () 1) _ = _
  rw [coeff_subst ha]
  change ∑ᶠ d, coeff d f • coeff 1 (a ^ d) = _
  rw [finsum_eq_single _ 1]
  · rw [pow_one, smul_eq_mul]
  · intro d hd
    obtain ⟨a', rfl⟩ := X_dvd_iff.mpr ha0
    rcases Nat.lt_or_gt_of_ne hd with h | h
    · have h0 : d = 0 := by omega
      subst h0
      rw [pow_zero, coeff_one, if_neg one_ne_zero, smul_zero]
    · rw [mul_pow, coeff_X_pow_mul', if_neg (by omega), smul_zero]

end Formalism.LT.PadicP

namespace Formalism.LT

end Formalism.LT
