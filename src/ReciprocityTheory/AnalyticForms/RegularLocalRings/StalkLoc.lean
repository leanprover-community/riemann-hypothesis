module

public import Mathlib
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChart
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.StalkLocA

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace ReciprocityTheory.AnForm.R

noncomputable section

variable {W : Scheme.{0}} {s : W ⟶ Spec (.of ℂ)}

namespace AffPres

variable (P : AffPres s)

end AffPres

theorem exists_mk_locRing {n : ℕ} (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    (t : locRing K p) : ∃ a b : MvPolynomial (Fin n) ℂ, eval p b ≠ 0 ∧
      t * algebraMap _ (locRing K p) b = algebraMap _ (locRing K p) a := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective t
  obtain ⟨⟨a, ⟨b, hb⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (ptIdeal p).primeCompl y
  have hb' : b ∉ ptIdeal p := hb
  refine ⟨a, b, ?_, ?_⟩
  · intro h
    apply hb'
    simp only [ptIdeal, RingHom.mem_ker]
    exact h
  · first
    | rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap, ← map_mul,
        IsLocalization.mk'_spec]
    | (show Ideal.Quotient.mk _ (IsLocalization.mk' _ a ⟨b, hb⟩) *
          Ideal.Quotient.mk _ (algebraMap _ _ b) = Ideal.Quotient.mk _ (algebraMap _ _ a)
       rw [← map_mul, IsLocalization.mk'_spec])

end

end ReciprocityTheory.AnForm.R
