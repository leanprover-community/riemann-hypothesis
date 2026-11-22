module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolynomialRootsOfClosedQuotientStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewtonPolygonSlopeExistenceStatement

@[expose] public section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.NewtonStep

theorem isUnit_or_of_add_quot {S : Type} [CommRing S] (ϖ : S)
    (hj : ϖ ∈ (⊥ : Ideal S).jacobson) (hD : Dich ϖ) (a b : S ⧸ Ideal.span {ϖ ^ 2})
    (h : IsUnit (a + b)) : IsUnit a ∨ IsUnit b := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨w', hw'⟩ := h.exists_right_inv
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w'
  have h1 : (a + b) * w - 1 ∈ Ideal.span {ϖ ^ 2} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [map_sub, map_mul, map_add (f := _), map_one]
    rw [hw', sub_self]
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp h1
  have hu : IsUnit ((a + b) * w) := by
    have hj' : ϖ ∈ Ring.jacobson S := by simpa only [Ideal.jacobson_bot] using hj
    have h2 := Ring.mem_jacobson_iff.mp hj' (ϖ * v)
    have e : (a + b) * w = ϖ * (ϖ * v) + 1 := by linear_combination hv
    rw [e]; exact h2
  have hab : IsUnit (a + b) := isUnit_of_mul_isUnit_left hu
  have hspan : ϖ ^ 0 ∈ Ideal.span {a, b} := by
    obtain ⟨t, ht⟩ := hab.exists_right_inv
    have h3 : (a + b) * t ∈ Ideal.span {a, b} :=
      Ideal.mul_mem_right _ _ (Ideal.add_mem _ (Ideal.subset_span (by simp))
        (Ideal.subset_span (by simp)))
    rw [ht] at h3
    simpa using h3
  rcases hD a b ⟨0, hspan⟩ with h4 | h4
  · right
    exact (isUnit_of_dvd_unit (dvd_add h4 dvd_rfl) hab).map _
  · left
    exact (isUnit_of_dvd_unit (dvd_add dvd_rfl h4) hab).map _

end GlobalTheory.CompanionTheory.NewtonStep
