module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.ZM.DwModel

private lemma spMap_comp_moduli_spaces {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

private lemma spMap_surjective' {A B : Type} [CommRing A] [CommRing B] (y : Sp B ⟶ Sp A) :
    ∃ f : A →+* B, spMap f = y :=
  ⟨(Spec.preimage y).hom, by simp [spMap]⟩

private lemma spMap_inj_lemma_3 {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) :
    f = g := by
  have h' := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom h'

theorem isGaloisCover_field (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    IsGaloisCover (L ≃ₐ[K] L) (fun σ => spMap (σ : L →+* L)) (spMap (algebraMap K L)) := by
  refine
    { finite := inferInstance
      one := ?_
      mul := ?_
      inv := ?_
      fin := ?_
      etale := ?_
      onto := ?_
      fibre := ?_ }
  · show Spec.map _ = _
    convert Spec.map_id (CommRingCat.of L)
    rfl
  · intro a c
    show spMap (((a * c : L ≃ₐ[K] L) : L →+* L)) = _
    rw [← spMap_comp_moduli_spaces]
    rfl
  · intro a
    rw [← spMap_comp_moduli_spaces]
    congr 1
    ext r
    exact a.commutes r
  · show IsFinite (Spec.map _)
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  · show Etale (Spec.map _)
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    show (algebraMap K L).Etale
    rw [RingHom.etale_algebraMap]
    exact ⟨Algebra.FormallyEtale.of_isSeparable K L, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  · exact ⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩
  · intro K' _ _ y y' h
    obtain ⟨f, rfl⟩ := spMap_surjective' y
    obtain ⟨f', rfl⟩ := spMap_surjective' y'
    rw [← spMap_comp_moduli_spaces, ← spMap_comp_moduli_spaces] at h
    have hfa := spMap_inj_lemma_3 h
    let _ : Algebra K K' := (f.comp (algebraMap K L)).toAlgebra
    let φ : L →ₐ[K] K' := { f with commutes' := fun _ => rfl }
    let φ' : L →ₐ[K] K' :=
      { f' with commutes' := fun r => (RingHom.congr_fun hfa r).symm }
    let Φ : (L ≃ₐ[K] L) → (L →ₐ[K] K') := fun a => φ.comp a.toAlgHom
    have hinj : Function.Injective Φ := by
      intro a b hab
      ext x
      exact f.injective (AlgHom.congr_fun hab x)
    have hcard : Nat.card (L →ₐ[K] K') ≤ Nat.card (L ≃ₐ[K] L) := by
      rw [IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card, AlgHom.card]
    obtain ⟨a, ha⟩ := (hinj.bijective_of_nat_card_le hcard).2 φ'
    refine ⟨a, ?_, fun b hb => ?_⟩
    · show spMap f ≫ spMap (a : L →+* L) = spMap f'
      rw [← spMap_comp_moduli_spaces]
      congr 1
      ext x
      exact AlgHom.congr_fun ha x
    · have hb' : f.comp (b : L →+* L) = f' := by
        have hb0 : spMap f ≫ spMap (b : L →+* L) = spMap f' := hb
        rw [← spMap_comp_moduli_spaces] at hb0
        exact spMap_inj_lemma_3 hb0
      apply hinj
      ext x
      exact (RingHom.congr_fun hb' x).trans (AlgHom.congr_fun ha x).symm

end GlobalTheory.ZM.DwModel
end
