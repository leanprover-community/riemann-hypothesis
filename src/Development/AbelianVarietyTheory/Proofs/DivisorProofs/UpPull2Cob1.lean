module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
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
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

@[expose] public section

set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory

namespace Katz

namespace ExtCoeff

variable {O E : Type} [CommRing O] [CommRing E] {d : ℕ}

theorem hasSubst_XL : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) O)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem hasSubst_XR : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) O)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem map_inL (h : O →+* E) (f : MvPowerSeries (Fin d) O) : map h (inL f) = inL (map h f) := by
  unfold inL
  rw [map_subst hasSubst_XL]
  congr 1
  funext i
  exact map_X h _

theorem map_inR (h : O →+* E) (f : MvPowerSeries (Fin d) O) : map h (inR f) = inR (map h f) := by
  unfold inR
  rw [map_subst hasSubst_XR]
  congr 1
  funext i
  exact map_X h _

theorem map_formalGroupLawCoboundaryOne_eq (h : O →+* E) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O)
    (s : MvPowerSeries (Fin d) O) (hμ : ∀ i, constantCoeff (μ i) = 0) :
    cob1 (fun i => map h (μ i)) (map h s) = map h (cob1 μ s) := by
  unfold cob1
  rw [map_sub, map_sub, map_subst (hasSubst_of_constantCoeff_zero hμ), map_inL, map_inR]

end ExtCoeff

end Katz

end GlobalTheory
