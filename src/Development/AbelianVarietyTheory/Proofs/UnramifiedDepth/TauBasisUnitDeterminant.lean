module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StAvDefs
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitDeterminantBasis
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open scoped TensorProduct
open IsLocalRing ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs

namespace GlobalTheory.tau_basis_unit_determinant

theorem exists_basis_isUnit_det : ∀ (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE]
    [Module.Free ℤ OE] [Module.Finite ℤ OE] (O : Type) [CommRing O] [IsLocalRing O]
    [Algebra ℤ_[p] O] (w : PlaceU p OE) (t : Fin w.n → (OE →+* O)),
    (∀ j, t j ∈ Emb (O := O) w.e) →
    (∀ j j', (∀ x, t j x - t j' x ∈ maximalIdeal O) → j = j') →
    ∃ b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)),
      IsUnit (Matrix.det (Matrix.of fun i j => tauExt (t j) (b i : ℤ_[p] ⊗[ℤ] OE))) := by
  intro p _ OE _ _ _ O _ _ _ w t ht hsep
  let b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)) :=
    Module.finBasisOfFinrankEq _ _ rfl
  refine ⟨b, ?_⟩
  by_contra hx
  have hxM := (mem_maximalIdeal _).2 hx
  let T : Fin w.n → (TensorProduct ℤ ℤ_[p] OE →ₐ[ℤ_[p]] O ⧸ maximalIdeal O) := fun j =>
    (Ideal.Quotient.mkₐ ℤ_[p] (maximalIdeal O)).comp (tauExt (t j))
  refine GlobalTheory.UnitDeterminantBasis.det_ne_zero b T ?_ ?_ ?_
  · intro j j' h
    refine hsep _ _ fun a => ?_
    have h1 := DFunLike.congr_fun h (1 ⊗ₜ a)
    rw [← Ideal.Quotient.eq]
    simpa [T, tauExt] using h1
  · intro j
    have h1 : tauExt (t j) w.e = 1 := ht j
    simp only [T, AlgHom.comp_apply, h1, map_one]
  · have h1 := Ideal.Quotient.eq_zero_iff_mem.2 hxM
    rw [RingHom.map_det] at h1
    exact h1

end GlobalTheory.tau_basis_unit_determinant
