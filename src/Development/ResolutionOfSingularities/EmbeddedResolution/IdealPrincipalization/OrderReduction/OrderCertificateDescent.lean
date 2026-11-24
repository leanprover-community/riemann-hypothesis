module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CertificateOpenRestriction
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.CoverDescent
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ComapSubschemeIso
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

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

variable {A B C : Scheme.{u}}

theorem comap_isoRangeOpens_inv (γ : A ⟶ B) (W : A.Opens) (h : IsOpenImmersion (W.ι ≫ γ))
    (J : B.IdealSheafData) :
    ((J.comap γ).comap W.ι).comap (isoRangeOpens γ W h).inv = J.comap (rangeOpens γ W h).ι := by
  simp [← isoRangeOpens_inv_comp γ W h]

theorem preimage_isoRangeOpens_inv (γ : A ⟶ B) (W : A.Opens) (h : IsOpenImmersion (W.ι ≫ γ))
    (S : Set ↥B) :
    (isoRangeOpens γ W h).inv.base ⁻¹' (W.ι.base ⁻¹' (γ.base ⁻¹' S))
      = (rangeOpens γ W h).ι.base ⁻¹' S := by
  ext x
  simp [← isoRangeOpens_inv_comp γ W h]

theorem rangeOpens_ι_comp (γ : A ⟶ B) (W : A.Opens) (h : IsOpenImmersion (W.ι ≫ γ))
    (f : B ⟶ C) :
    (rangeOpens γ W h).ι ≫ f = (isoRangeOpens γ W h).inv ≫ W.ι ≫ γ ≫ f :=
  (isoRangeOpens_inv_comp_assoc γ W h f).symm

theorem exists_opens_orderCertificate_of_isLocalIsomorphism
    (hopen : ∀ (k : Type u) [Field k], OpenImmersionStability k)
    {k : Type u} [Field k] {W W' : Scheme.{u}} (p : W ⟶ Spec (CommRingCat.of k))
    (g : W' ⟶ W) (hg : MaxContactFunctoriality.IsLocalIsomorphism g)
    [AlgebraicGeometry.Surjective g]
    (N : W.IdealSheafData) (μ : ℕ) (Mem : Set ↥W) (Z : W.IdealSheafData)
    (hcert : OrderCertificate W' (g ≫ p) (N.comap g) μ (g.base ⁻¹' Mem) (Z.comap g))
    (x : ↥W) :
    ∃ V : W.Opens, x ∈ V ∧
      OrderCertificate V.toScheme (V.ι ≫ p) (N.comap V.ι) μ (V.ι.base ⁻¹' Mem) (Z.comap V.ι) := by
  obtain ⟨U, hU, hxU⟩ := exists_mem_rangeOpens g hg x
  refine ⟨rangeOpens g U hU, hxU, ?_⟩
  have hres := hcert.restrict (hopen k) U
  have htr := OrderCertificate.comap_iso_of_eq_iso_hom_comp (isoRangeOpens g U hU).symm
    (rangeOpens_ι_comp g U hU p) hres
  simp only [Iso.symm_hom, comap_isoRangeOpens_inv, preimage_isoRangeOpens_inv] at htr
  exact htr

def OrderCertificateLocalToGlobal : Prop :=
  ∀ (k : Type u) [Field k] (W : Scheme.{u}) (p : W ⟶ Spec (CommRingCat.of k))
    (N : W.IdealSheafData) (μ : ℕ) (Mem : Set ↥W) (Z : W.IdealSheafData),
    (∀ x : ↥W, ∃ V : W.Opens, x ∈ V ∧
      OrderCertificate V.toScheme (V.ι ≫ p) (N.comap V.ι) μ (V.ι.base ⁻¹' Mem) (Z.comap V.ι)) →
    OrderCertificate W p N μ Mem Z

theorem orderCertificate_of_comap_of_isLocalIsomorphism
    (hopen : ∀ (k : Type u) [Field k], OpenImmersionStability k)
    (hglue : OrderCertificateLocalToGlobal.{u})
    (k : Type u) [Field k] (W W' : Scheme.{u}) (p : W ⟶ Spec (CommRingCat.of k))
    (g : W' ⟶ W) (hg : MaxContactFunctoriality.IsLocalIsomorphism g)
    [AlgebraicGeometry.Surjective g]
    (N : W.IdealSheafData) (μ : ℕ) (Mem : Set ↥W) (Z : W.IdealSheafData)
    (hcert : OrderCertificate W' (g ≫ p) (N.comap g) μ (g.base ⁻¹' Mem) (Z.comap g)) :
    OrderCertificate W p N μ Mem Z :=
  hglue k W p N μ Mem Z
    (fun x => exists_opens_orderCertificate_of_isLocalIsomorphism hopen p g hg N μ Mem Z hcert x)

end FunctorialResolution.EmbeddedResolution
