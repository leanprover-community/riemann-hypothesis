module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LtPrime
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

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.InertPrimeEleven

theorem eleven_le : ∀ eps : ℝ, 0 < eps → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (l : ℕ),
    L.sc.ez = eps → x0 ≤ L.sc.x → l.Prime → InertUnr D l → 11 ≤ l := by
  intro eps heps
  refine ⟨(11 : ℝ) ^ (5 / eps), ?_⟩
  intro D L l he hx hl hin
  have hlt := GlobalTheory.InertPrimeLarge.lt_prime L l hl hin.ne_two hin.2.2.2
  rw [he] at hlt
  have h0 : (0 : ℝ) ≤ (11 : ℝ) ^ (5 / eps) := Real.rpow_nonneg (by norm_num) _
  have hmono : ((11 : ℝ) ^ (5 / eps)) ^ (eps / 5) ≤ L.sc.x ^ (eps / 5) :=
    Real.rpow_le_rpow h0 hx (by positivity)
  have h11 : ((11 : ℝ) ^ (5 / eps)) ^ (eps / 5) = 11 := by
    rw [← Real.rpow_mul (by norm_num)]
    have : 5 / eps * (eps / 5) = 1 := by field_simp
    rw [this, Real.rpow_one]
  have : (11 : ℝ) < l := by linarith
  exact_mod_cast this.le

end GlobalTheory.InertPrimeEleven
