module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.FockLatticeFiniteSpanning
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.DividedPowerPadicValuationBound
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.IntegralPolyLinearMapClosed
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees

@[expose] public section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem monomial_eq_smul_basis {K σ : Type} [CommRing K] (m : σ →₀ ℕ) (c : K) :
    monomial m c = c • (basisMonomials σ K m) := by
  rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

theorem divided_power_monomial {K : Type} [CommRing K] {ι : Type} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (a b : Fin n) (k : ℕ) (m : ι × Fin n →₀ ℕ) (c : K) :
    divPow K LL S a b k (monomial m c) = c • divPowMono K LL S a b k m := by
  rw [monomial_eq_smul_basis, map_smul]
  unfold divPow
  rw [Module.Basis.constr_basis]

theorem binomial_operator_monomial {K : Type} [CommRing K] {ι : Type} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (a : Fin n) (k : ℕ) (m : ι × Fin n →₀ ℕ) (c : K) :
    binomPol K LL S a k (monomial m c) = monomial m (c * ((Ring.choose (wtS LL S m a) k : ℤ) : K)) := by
  rw [monomial_eq_smul_basis, map_smul]
  unfold binomPol
  rw [Module.Basis.constr_basis, MvPolynomial.smul_monomial, smul_eq_mul]

def dividedPowerTermCoefficient {ι : Type} {n : ℕ} (LL : Letters ι) (a b : Fin n) (m : ι × Fin n →₀ ℕ) (f : ι →₀ ℕ) (l : ι) : ℤ :=
  if LL.vec l then ((m (l, b)).choose (f l) : ℤ) else (-1 : ℤ) ^ (f l) * ((m (l, a)).choose (f l) : ℤ)

open Classical in
theorem divided_power_monomial_expansion {K : Type} [CommRing K] {ι : Type} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (a b : Fin n) (k : ℕ) (m : ι × Fin n →₀ ℕ) (c : K) :
    c • divPowMono K LL S a b k m =
      ∑ f ∈ Finset.finsuppAntidiag (Finset.univ.filter (· ∈ S)) k,
        monomial ((m - ∑ l ∈ f.support, Finsupp.single (if LL.vec l then (l, b) else (l, a)) (f l))
          + ∑ l ∈ f.support, Finsupp.single (if LL.vec l then (l, a) else (l, b)) (f l))
          (c * ((∏ l ∈ f.support, dividedPowerTermCoefficient LL a b m f l : ℤ) : K)) := by
  unfold divPowMono
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [MvPolynomial.smul_monomial, smul_eq_mul, Int.cast_prod]
  congr 2
  refine Finset.prod_congr rfl fun l _ => ?_
  unfold dividedPowerTermCoefficient
  split_ifs <;> push_cast <;> rfl

theorem integral_formula_stability_holds {p : ℕ} (hp : p.Prime) (hV : ValuationProperties p O) : PolynomialIntegralFormPreservesLattices p O := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  intro n ι _ LL S
  refine ⟨?_, ?_⟩
  · intro u hu x hx
    refine integral_poly_linear_map_closed u (fun m => ?_) x hx
    rcases hu with ⟨a, b, k, -, rfl⟩ | ⟨a, k, rfl⟩
    · rw [divided_power_monomial, divided_power_monomial_expansion]
      refine Submodule.sum_mem _ fun f _ => ?_
      rw [one_mul]
      exact integer_monomial_mem_integral _ _
    · rw [binomial_operator_monomial, one_mul]
      exact integer_monomial_mem_integral _ _
  · intro u hu F hF
    refine fock_lattice_linear_map_closed hV u (fun m c hmc => ?_) F hF
    rcases hu with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩
    · rw [divided_power_monomial, divided_power_monomial_expansion]
      refine fock_lattice_sum_mem hV _ _ fun f _ => ?_
      refine fock_lattice_monomial_rescale hV m _ c _ hmc ?_
      exact divided_power_padic_valuation_bound p (fun l => if LL.vec l then (l, b) else (l, a))
        (fun l => if LL.vec l then (l, a) else (l, b))
        (fun l => by split_ifs <;> rfl) (fun l => by split_ifs <;> rfl)
        (fun l => by split_ifs <;> simp [hab, Ne.symm hab]) m f (dividedPowerTermCoefficient LL a b m f)
        (fun l => by unfold dividedPowerTermCoefficient; split_ifs <;> simp [Int.natAbs_mul, Int.natAbs_pow])
    · rw [binomial_operator_monomial]
      exact fock_lattice_monomial_rescale hV m m c _ hmc (Or.inr (Nat.le_add_left _ _))

end Formalism.MainNotions.G.GLWeightTheory
