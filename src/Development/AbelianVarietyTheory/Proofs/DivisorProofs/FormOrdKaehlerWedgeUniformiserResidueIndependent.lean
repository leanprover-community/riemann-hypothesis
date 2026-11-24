module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrdDFormUniformiserCons
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory

theorem formOrd_dForm_cons_of_ord_eq_one : ∀ {K : Type} [Field K] (cK : ℂ →+* K) (F : Place cK) (m : ℕ) (π : K) (y : Fin m → K),
  F.ord π = 1 → (∀ i, y i ∈ F.ring) →
  (∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 → MvPolynomial.eval₂ cK y P ≠ 0 ∧ (MvPolynomial.eval₂ cK y P)⁻¹ ∈ F.ring) →
  TrBasis cK (Fin.cons π y : Fin (m + 1) → K) →
  (fun ω => @dite ℤ (∃ a, F.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm cK (Fin.cons π y : Fin (m + 1) → K)) = 0 := by
  intro K _ cK F m π y hπ hy hP hB
  have hπ0 : π ≠ 0 := by
    rintro rfl
    simp [Place.ord] at hπ
  have hπm : π ∈ F.ring := (F.ord_nonneg_iff hπ0).1 (by rw [hπ]; norm_num)
  have hirr : Irreducible (⟨π, hπm⟩ : F.ring) := by
    obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible F.ring
    have hne : (⟨π, hπm⟩ : F.ring) ≠ 0 := fun h => hπ0 (congrArg Subtype.val h)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne ht
    have e : π = ((u : F.ring) : K) * (t : K) ^ n := by
      simpa using congrArg Subtype.val hu
    have hu0 : ((u : F.ring) : K) ≠ 0 := (u.isUnit.map F.ring.subtype).ne_zero
    have ht0 : (t : K) ≠ 0 := fun h => ht.ne_zero (Subtype.ext h)
    have h1 : F.ord π = n := by
      rw [e, F.ord_mul hu0 (pow_ne_zero _ ht0), F.ord_eq_zero u.isUnit, F.ord_pow,
        F.ord_irreducible ht]
      simp
    obtain rfl : n = 1 := by
      rw [hπ] at h1
      exact_mod_cast h1.symm
    rw [hu, pow_one]
    exact (irreducible_units_mul u).2 ht
  refine formOrd_dForm_uniformiser_cons cK m F ⟨π, hπm⟩ (fun i => ⟨y i, hy i⟩) hirr ?_ ⟨_, hB⟩
  intro P hP0
  obtain ⟨h0, hi⟩ := hP P hP0
  have e : ((MvPolynomial.eval₂ F.const (fun i => (⟨y i, hy i⟩ : F.ring)) P : F.ring) : K) =
      MvPolynomial.eval₂ cK y P :=
    MvPolynomial.eval₂_comp_left F.ring.subtype F.const (fun i => (⟨y i, hy i⟩ : F.ring)) P
  refine IsUnit.of_mul_eq_one (⟨_, hi⟩ : F.ring) (Subtype.ext ?_)
  change ((MvPolynomial.eval₂ F.const (fun i => (⟨y i, hy i⟩ : F.ring)) P : F.ring) : K) * _ = 1
  rw [e]
  exact mul_inv_cancel₀ h0

end GlobalTheory
