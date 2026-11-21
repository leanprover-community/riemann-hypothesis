import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Definitions.Divisors.SmoothOfRelativeDimensionPspace
import ReciprocityTheory.AnalyticForms.RegularLocalRings.WChartsC

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.Principalise.Model

attribute [local instance] MvPolynomial.gradedAlgebra

def Concl {k : Type} [Field k] (d : ℕ) {Y : Scheme.{0}} (f : Y ⟶ Sp k) (I : Y.IdealSheafData) : Prop :=
  ∃ (Y' : Scheme.{0}) (s : Y' ⟶ Y),
    IsIntegral Y' ∧ SmoothOfRelativeDimension d (s ≫ f) ∧ IsProjOver (s ≫ f) ∧
    IsSmoothBlowupSeq f (I.support : Set Y) s ∧ IsIso (s ∣_ I.support.compl) ∧
    FinalTheorems.EffCartier (I.comap s) ∧ FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal (I.comap s).support)



theorem isEmpty_of_effCartier_bot {W : Scheme.{0}} (h : FinalTheorems.EffCartier (⊥ : W.IdealSheafData)) : IsEmpty W := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, f, hx, hf, e⟩ := h x
  have hf0 : f = 0 := by
    have : f ∈ (⊥ : W.IdealSheafData).ideal U := e ▸ Ideal.mem_span_singleton_self f
    simpa using this
  have : Nonempty U.1 := ⟨⟨x, hx⟩⟩
  exact nonZeroDivisors.ne_zero hf hf0





section Proj
variable (k : Type) [Field k] (N : ℕ)

def hypPt : PSpace k (N + 1) :=
  (⟨⟨Ideal.span {MvPolynomial.X 0}, Ideal.homogeneous_span _ _ (by
      rintro _ rfl; exact ⟨1, MvPolynomial.isHomogeneous_X k 0⟩)⟩,
    (Ideal.span_singleton_prime (MvPolynomial.X_ne_zero 0)).2 MvPolynomial.X_prime, fun h => by
      have h1 : (MvPolynomial.X 1 : MvPolynomial (Fin (N + 1 + 1)) k) ∈
          HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (N + 1 + 1)) k) :=
        HomogeneousIdeal.mem_irrelevant_of_mem _ (i := 1) one_pos (MvPolynomial.isHomogeneous_X k 1)
      have h2 := Ideal.mem_span_singleton.1 (h h1)
      rw [MvPolynomial.X_dvd_X] at h2
      exact absurd h2 (by simp)⟩ : ProjectiveSpectrum _)

def hypPt' : PSpace k (N + 1) :=
  (⟨⟨Ideal.span {MvPolynomial.X 1}, Ideal.homogeneous_span _ _ (by
      rintro _ rfl; exact ⟨1, MvPolynomial.isHomogeneous_X k 1⟩)⟩,
    (Ideal.span_singleton_prime (MvPolynomial.X_ne_zero 1)).2 MvPolynomial.X_prime, fun h => by
      have h1 : (MvPolynomial.X 0 : MvPolynomial (Fin (N + 1 + 1)) k) ∈
          HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (N + 1 + 1)) k) :=
        HomogeneousIdeal.mem_irrelevant_of_mem _ (i := 1) one_pos (MvPolynomial.isHomogeneous_X k 0)
      have h2 := Ideal.mem_span_singleton.1 (h h1)
      rw [MvPolynomial.X_dvd_X] at h2
      exact absurd h2 (by simp)⟩ : ProjectiveSpectrum _)

def hypIdeal : (PSpace k (N + 1)).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (Opens.compl (Proj.basicOpen _ (MvPolynomial.X 0)))

theorem mem_support : hypPt k N ∈ (hypIdeal k N).support := by
  rw [hypIdeal, ← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact fun h => (Proj.mem_basicOpen _ _ _).1 h (Ideal.mem_span_singleton_self _)




end Proj

section Line
variable (k : Type) [Field k]

abbrev origin : Sp k ⟶ Sp (Polynomial k) := spMap (Polynomial.evalRingHom 0)

instance : IsClosedImmersion (origin k) :=
  IsClosedImmersion.spec_of_surjective _ fun a => ⟨Polynomial.C a, by simp⟩




end Line

end GlobalTheory.Principalise.Model
