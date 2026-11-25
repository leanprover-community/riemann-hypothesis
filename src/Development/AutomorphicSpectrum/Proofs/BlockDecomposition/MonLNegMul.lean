module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

noncomputable section
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.LaurentD

variable {K : Type} [Field K] {n d : ℕ}

theorem monL_zero' : monL K (0 : Gam n d) = 1 := rfl

theorem monL_add' (g g' : Gam n d) : monL K (g + g') = monL K g * monL K g' := by
  unfold monL
  rw [mon_mul]

theorem monL_neg_mul (g : Gam n d) : monL K (-g) * monL K g = 1 := by
  rw [← monL_add', neg_add_cancel, monL_zero']

def lam (K : Type) [Field K] {n d : ℕ} (g : Gam n d) : Ω[Lr K n d⁄K] :=
  monL K (-g) • KaehlerDifferential.D K (Lr K n d) (monL K g)

theorem lam_add (g g' : Gam n d) : lam K (g + g') = lam K g + lam K g' := by
  unfold lam
  have h1 : monL K (-(g + g')) = monL K (-g) * monL K (-g') := by
    rw [neg_add, monL_add']
  have e1 : monL K (-g) * monL K (-g') * monL K g = monL K (-g') := by
    rw [mul_comm (monL K (-g)), mul_assoc, monL_neg_mul, mul_one]
  have e2 : monL K (-g) * monL K (-g') * monL K g' = monL K (-g) := by
    rw [mul_assoc, monL_neg_mul, mul_one]
  rw [monL_add', Derivation.leibniz, smul_add, smul_smul, smul_smul, h1, e1, e2]
  exact add_comm _ _

def lamHom (K : Type) [Field K] (n d : ℕ) : Gam n d →+ Ω[Lr K n d⁄K] :=
  AddMonoidHom.mk' (lam K) lam_add

theorem exp_eq_sum (g : Gam n d) : g = ∑ e, g e • (oneE e : Gam n d) := by
  funext x
  simp [oneE, Finset.sum_apply, Pi.single_apply]

theorem lam_eq_sum (g : Gam n d) : lam K g = ∑ e, (g e) • (dl e : Ω[Lr K n d⁄K]) := by
  have h : lam K g = lamHom K n d g := rfl
  rw [h]
  conv_lhs => rw [exp_eq_sum g]

  rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_zsmul]
  rfl

theorem D_monL (g : Gam n d) :
    KaehlerDifferential.D K (Lr K n d) (monL K g) = monL K g • ∑ e, (g e) • (dl e : Ω[Lr K n d⁄K]) := by
  rw [← lam_eq_sum]
  unfold lam
  rw [smul_smul, mul_comm, monL_neg_mul, one_smul]

end GlobalTheory.CompanionTheory.SurjectionOntoH4.LaurentD
