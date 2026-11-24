module

public import Formalism.FormalGroupWitt.SubstInjectiveV
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

universe u v w

namespace Formalism.FG.IntegralSubstitution

open Formalism.G

variable {K : Type u} [NormedField K] [IsUltrametricDist K] {τ : Type w}

theorem integral_mul {A B : MvPowerSeries τ K} (hA : IntegralMv A) (hB : IntegralMv B) :
    IntegralMv (A * B) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun p _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hA _) (norm_nonneg _) (hB _)

theorem integral_one : IntegralMv (1 : MvPowerSeries τ K) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_one]
  split_ifs <;> simp

theorem integral_pow {A : MvPowerSeries τ K} (hA : IntegralMv A) (n : ℕ) :
    IntegralMv (A ^ n) := by
  induction n with
  | zero => simpa using integral_one
  | succ n ih => rw [pow_succ]; exact integral_mul ih hA

theorem integral_finsuppProd {ι : Type v} (a : ι → MvPowerSeries τ K) (ha : ∀ i, IntegralMv (a i))
    (n : ι →₀ ℕ) : IntegralMv (n.prod fun s e => (a s) ^ e) := by
  classical
  unfold Finsupp.prod
  exact Finset.prod_induction _ (fun x => IntegralMv x) (fun _ _ hx hy => integral_mul hx hy)
    integral_one (fun i _ => integral_pow (ha i) _)

theorem integralSubstV {ι : Type v} [Finite ι] (g : MvPowerSeries ι K)
    (a : ι → MvPowerSeries τ K) (hg : IntegralMv g)
    (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (ha : ∀ i, IntegralMv (a i)) :
    IntegralMv (MvPowerSeries.subst a g) := by
  intro d
  have hs : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  rw [MvPowerSeries.coeff_subst hs g d]
  have hfin := MvPowerSeries.coeff_subst_finite hs g d
  rw [finsum_eq_sum _ hfin]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun n _ => ?_
  rw [smul_eq_mul, norm_mul]
  exact mul_le_one₀ (hg n) (norm_nonneg _) (integral_finsuppProd a ha n d)

end Formalism.FG.IntegralSubstitution

theorem Formalism.FG.integral_subst_vector : Formalism.FG.IntegralSubstV.{u, v, w} :=
  fun _ _ _ _ _ _ g a hg ha0 ha => Formalism.FG.IntegralSubstitution.integralSubstV g a hg ha0 ha
