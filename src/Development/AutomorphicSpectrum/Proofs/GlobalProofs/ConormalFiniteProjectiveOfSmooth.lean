module

public import Mathlib.RingTheory.RingHom.Smooth
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocPrincipalSpan
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver


open TensorProduct in
theorem GlobalTheory.CompanionTheory.Hypotheses₂.Conormal.finite_projective_cotangent :
    ∀ {k A : Type} [Field k] [CommRing A] (φ : k →+* A) (I : Ideal A), φ.Smooth →
      ((Ideal.Quotient.mk I).comp φ).Smooth →
        Module.Finite (A ⧸ I) I.Cotangent ∧ Module.Projective (A ⧸ I) I.Cotangent := by
  intro k A _ _ φ I h1 h2
  letI := φ.toAlgebra
  haveI hA : Algebra.Smooth k A := h1
  have halg : (Ideal.Quotient.algebra k : Algebra k (A ⧸ I)) =
      ((Ideal.Quotient.mk I).comp φ).toAlgebra := Algebra.algebra_ext _ _ fun _ => rfl
  have hQ : Algebra.FormallySmooth k (A ⧸ I) := by
    have hs : @Algebra.Smooth k _ (A ⧸ I) _ ((Ideal.Quotient.mk I).comp φ).toAlgebra := h2
    rw [← halg] at hs
    exact hs.formallySmooth
  haveI : Algebra.FormallySmooth k A := hA.formallySmooth
  haveI : Module.Projective A (KaehlerDifferential k A) :=
    Algebra.FormallySmooth.projective_kaehlerDifferential
  haveI : Algebra.FinitePresentation k A := hA.finitePresentation
  haveI : Algebra.FiniteType k A := Algebra.FiniteType.of_finitePresentation
  haveI : Algebra.EssFiniteType k A := Algebra.EssFiniteType.of_finiteType k A
  haveI : Module.Finite A (KaehlerDifferential k A) := KaehlerDifferential.finite k A
  haveI : Module.Finite (A ⧸ I) ((A ⧸ I) ⊗[A] KaehlerDifferential k A) :=
    Module.Finite.base_change A (A ⧸ I) _
  haveI : IsScalarTower A (A ⧸ I) I.Cotangent := by
    first
    | infer_instance
    | exact IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection (R := k) (P := A) (A := A ⧸ I)
    Ideal.Quotient.mk_surjective).mp hQ
  have hsurj : Function.Surjective (algebraMap A (A ⧸ I)) := Ideal.Quotient.mk_surjective
  let e := Ideal.Cotangent.equivOfEq _ _ (Ideal.mk_ker (I := I))
  let i : I.Cotangent →ₗ[A ⧸ I] (A ⧸ I) ⊗[A] KaehlerDifferential k A :=
    LinearMap.extendScalarsOfSurjective hsurj
      (KaehlerDifferential.kerCotangentToTensor k A (A ⧸ I) ∘ₗ e.symm.toLinearMap)
  let s : (A ⧸ I) ⊗[A] KaehlerDifferential k A →ₗ[A ⧸ I] I.Cotangent :=
    LinearMap.extendScalarsOfSurjective hsurj (e.toLinearMap ∘ₗ l)
  have hsi : s ∘ₗ i = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    have h := LinearMap.congr_fun hl (e.symm x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
    first
    | (simp only [s, i, LinearMap.comp_apply, LinearMap.extendScalarsOfSurjective_apply,
        LinearEquiv.coe_coe, LinearMap.id_apply, h, LinearEquiv.apply_symm_apply]; done)
    | (show e (l (KaehlerDifferential.kerCotangentToTensor k A (A ⧸ I) (e.symm x))) = x
       rw [h, LinearEquiv.apply_symm_apply])
  refine ⟨Module.Finite.of_surjective s fun x => ⟨i x, ?_⟩, Module.Projective.of_split i s hsi⟩
  simpa only [LinearMap.comp_apply, LinearMap.id_apply] using LinearMap.congr_fun hsi x
