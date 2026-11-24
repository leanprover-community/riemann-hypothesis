module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
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

open PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.Tf.Loc

theorem isUnitIntegral_of_conj_mem_unitGL {F : Type} [Field F] [ValuativeRel F] {n : ℕ}
    (γ g : GL (Fin n) F) (h : g⁻¹ * γ * g ∈ unitGL (n := Fin n) F) : IsUnitIntegral γ := by
  obtain ⟨u, hu⟩ := h
  have hcp : (γ : Matrix (Fin n) (Fin n) F).charpoly =
      ((u : Matrix (Fin n) (Fin n) (intO F)).charpoly).map (intO F).subtype := by
    have h1 : ((g⁻¹ * γ * g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).charpoly =
        (γ : Matrix (Fin n) (Fin n) F).charpoly := by
      rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj']
    rw [← h1, ← hu, ← Matrix.charpoly_map]
    rfl
  have hint := Valuation.integer.integers (ValuativeRel.valuation F)
  refine ⟨fun i => ?_, ?_⟩
  · rw [hcp, Polynomial.coeff_map]
    exact SetLike.coe_mem _
  · rw [hcp, Polynomial.coeff_map]
    have hdet : IsUnit (u : Matrix (Fin n) (Fin n) (intO F)).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 u.isUnit
    have hc : IsUnit ((u : Matrix (Fin n) (Fin n) (intO F)).charpoly.coeff 0) := by
      rw [Matrix.det_eq_sign_charpoly_coeff] at hdet
      exact isUnit_of_mul_isUnit_right hdet
    exact hint.isUnit_iff_valuation_eq_one.1 hc

theorem normGL_mem_unitGL {k E : Type} [Field k] [Field E] [ValuativeRel E] [Algebra k E] {n : ℕ}
    (σ : E ≃ₐ[k] E)
    (hστ : ∀ (τ : E ≃ₐ[k] E) (g : GL (Fin n) E),
      sigmaGL τ g ∈ unitGL (n := Fin n) E ↔ g ∈ unitGL (n := Fin n) E)
    {u : GL (Fin n) E} (hu : u ∈ unitGL (n := Fin n) E) :
    normGL σ u ∈ unitGL (n := Fin n) E := by
  refine Subgroup.list_prod_mem _ ?_
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  rw [← sigmaGL_pow]
  exact (hστ _ _).2 hu

theorem stableLattice_unitIntegral : D0a → L2 := by
  intro hD
  refine ⟨?_, ?_⟩
  · rintro F _ _ _ _ n γ ⟨g, hg⟩
    exact isUnitIntegral_of_conj_mem_unitGL γ g hg
  · intro k E _ _ _ _ _ _ _ _ _ _ _ _ hun σ hgen n δ g hmem
    have hστ := (hD k E hun σ hgen).2.2.2.1
    have hℓ : σ ^ Module.finrank k E = 1 := by
      rw [← IsGalois.card_aut_eq_finrank]; exact pow_card_eq_one'
    have hθ : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1 := by
      rw [← sigmaGL_pow, hℓ, sigmaGL_one]
    have h := normGL_mem_unitGL σ (hστ · n ·) hmem
    rw [normGL, twNorm_twConj_of_pow_eq_one _ hθ] at h
    exact h

end GlobalTheory.CompanionTheory.Tf.Loc
