module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFaithfullyFlatRingHomBasicPropertiesStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem etale_sigmaDesc_of_isOpenImmersion {ι : Type} (V : Scheme.{0}) (Y : ι → Scheme.{0})
    (u : ∀ i, Y i ⟶ V) [∀ i, IsOpenImmersion (u i)] : Etale (Sigma.desc u) := by
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale)
  exact IsZariskiLocalAtSource.sigmaDesc fun _ => inferInstance

theorem etFF_preimage_of_etale_surjective (A B : CommRingCat.{0}) (k : Spec B ⟶ Spec A)
    [Etale k] [Surjective k] : EtFF (Spec.preimage k) := by
  rw [(GlobalTheory.T.etaleFaithfullyFlatRingHom_basic_properties.2.1 A B _), Spec.map_preimage]
  exact ⟨inferInstance, inferInstance⟩

theorem exists_etFF_of_isAffine (A : CommRingCat.{0}) (X V : Scheme.{0}) [IsAffine X]
    (h' : X ⟶ V) (f : V ⟶ Spec A) [Etale (h' ≫ f)] [Surjective (h' ≫ f)] :
    ∃ (B : CommRingCat.{0}) (g : A ⟶ B) (h : Spec B ⟶ V), EtFF g ∧ h ≫ f = Spec.map g := by
  have he : Etale (X.isoSpec.inv ≫ h' ≫ f) := inferInstance
  have hs : Surjective (X.isoSpec.inv ≫ h' ≫ f) := inferInstance
  refine ⟨Γ(X, ⊤), Spec.preimage (X.isoSpec.inv ≫ h' ≫ f), X.isoSpec.inv ≫ h',
    etFF_preimage_of_etale_surjective _ _ _, ?_⟩
  rw [Spec.map_preimage, Category.assoc]

theorem exists_etFF_refine_of_etale_surjective :
    ∀ (A : CommRingCat.{0}) (V : Scheme.{0}) (f : V ⟶ Spec A), Etale f → Surjective f →
      ∃ (B : CommRingCat.{0}) (g : A ⟶ B) (h : Spec B ⟶ V), EtFF g ∧ h ≫ f = Spec.map g := by
  intro A V f hf hs
  have hopen : ∀ x : V.affineCover.I₀, IsOpen (Set.range (V.affineCover.f x ≫ f)) := fun x =>
    (V.affineCover.f x ≫ f).isOpenMap.isOpen_range
  have hcov : Set.univ ⊆ ⋃ x : V.affineCover.I₀, Set.range (V.affineCover.f x ≫ f) := by
    intro y _
    obtain ⟨v, rfl⟩ := f.surjective y
    obtain ⟨x, hx⟩ := V.affineCover.covers v
    exact Set.mem_iUnion.mpr ⟨V.affineCover.idx v, ⟨_, by rw [Scheme.Hom.comp_apply, hx]⟩⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ hopen hcov
  let Y : t → Scheme.{0} := fun i => V.affineCover.X i.1
  let u : ∀ i, Y i ⟶ V := fun i => V.affineCover.f i.1
  haveI : ∀ i, IsAffine (Y i) := fun i => inferInstanceAs (IsAffine (Spec _))
  haveI : ∀ i, IsOpenImmersion (u i) := fun i => inferInstanceAs (IsOpenImmersion (V.affineCover.f i.1))
  haveI : Etale (Sigma.desc u) := etale_sigmaDesc_of_isOpenImmersion V Y u
  have hcomp : Sigma.desc u ≫ f = Sigma.desc fun i => u i ≫ f := by
    ext i; simp
  haveI hsurj : Surjective (Sigma.desc u ≫ f) := by
    rw [hcomp]
    apply Surjective.sigmaDesc_of_union_range_eq_univ
    refine Set.eq_univ_of_univ_subset (fun y hy => ?_)
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.mp (ht hy)
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hy⟩
  exact exists_etFF_of_isAffine A (∐ Y) V (Sigma.desc u) f

end GlobalTheory.EtC
