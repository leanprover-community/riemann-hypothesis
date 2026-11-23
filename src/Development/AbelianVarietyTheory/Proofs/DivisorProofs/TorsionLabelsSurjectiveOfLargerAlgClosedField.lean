module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointsAlgClosureFractionRingBijectiveStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc

theorem GlobalTheory.Mum.Desc.lab_onto_of_labExt : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (N : ℕ), 1 ≤ N → ∀ (lab : QkPt D (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (lab' : QkPt D F N → (TFK (R := R) F ⟶ A.A)), LabExt em lab lab' → (∀ x : TFK (R := R) F ⟶ A.A, x ^ N = 1 ↔ ∃ p, lab' p = x) → ∀ x : TFK (R := R) (Kb R) ⟶ A.A, x ^ N = 1 ↔ ∃ p, lab p = x := by
  intro R _ _ _ D A N hN lab F _ _ _ em lab' hext hon x
  obtain ⟨h1, h2⟩ := GlobalTheory.T.levelPoints_algClosure_fractionRing_bijective R D F em N hN
  have cancel : ∀ y y' : TFK (R := R) (Kb R) ⟶ A.A, baseEm em ≫ y = baseEm em ≫ y' → y = y' := by
    intro y y' h
    apply Over.OverMorphism.ext
    have spec_map_field_cancel {K C : Type} [Field K] [Field C] (gam : K →+* C)
        {X : Scheme} (y y' : Sp K ⟶ X)
        (h : spMap gam ≫ y = spMap gam ≫ y') : y = y' := by
      obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y
      obtain ⟨⟨p', φ'⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y'
      simp only [Scheme.SpecToEquivOfField_symm_apply] at h ⊢
      have e : ∀ (q : X) (ψ : X.residueField q ⟶ CommRingCat.of K),
          spMap gam ≫ (Spec.map ψ ≫ X.fromSpecResidueField q) =
            (Scheme.SpecToEquivOfField C X).symm ⟨q, ψ ≫ CommRingCat.ofHom gam⟩ := by
        intro q ψ
        simp only [Scheme.SpecToEquivOfField_symm_apply, spMap, Spec.map_comp, Category.assoc]
      rw [e, e] at h
      have h2 := (Scheme.SpecToEquivOfField C X).symm.injective h
      simp only [Sigma.mk.inj_iff] at h2
      obtain ⟨rfl, h3⟩ := h2
      have h4 : φ = φ' := by
        have h5 : φ ≫ CommRingCat.ofHom gam = φ' ≫ CommRingCat.ofHom gam := eq_of_heq h3
        ext x
        apply gam.injective
        have := congrArg (fun f => f.hom x) h5
        simpa using this
      rw [h4]
    exact spec_map_field_cancel em.toRingHom y.left y'.left (congrArg CommaMorphism.left h)
  have hlab : ∀ p p', QkExt em.toRingHom p p' → lab' p' = baseEm em ≫ lab p := by
    intro p p' hp
    apply Over.OverMorphism.ext
    exact hext p p' hp
  constructor
  · intro hx
    have hx' : (baseEm em ≫ x) ^ N = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
    obtain ⟨p', hp'⟩ := (hon _).1 hx'
    obtain ⟨p, hp, -⟩ := h2 p'
    refine ⟨p, cancel _ _ ?_⟩
    rw [← hlab p p' hp, hp']
  · rintro ⟨p, rfl⟩
    obtain ⟨p', hp', -⟩ := h1 p
    have h3 := (hon (lab' p')).2 ⟨p', rfl⟩
    rw [hlab p p' hp'] at h3
    apply cancel
    rw [MonObj.comp_pow, h3, MonObj.comp_one]
