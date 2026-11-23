module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Formalism.ConjugateSelfDual.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC Formalism.MainNotions.N ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem UpperTheory.V.Ws.Pu.exists_separating_element {O A k : Type} [CommRing O] [Ring A] [Field k] [Algebra O A] [Algebra O k]
    {n : ℕ} (f g : Fin n → A →ₐ[O] k) (e : Fin n → Fin n → A)
    (h1 : ∀ a b, f a (e a b) = 1) (h0 : ∀ a b, g b (e a b) = 0) :
    ∃ y : A, (∀ a, f a y = 1) ∧ ∀ b, g b y = 0 := by
  let ya : Fin n → A := fun a => ((List.finRange n).map (e a)).prod
  have hf : ∀ a, f a (ya a) = 1 := by
    intro a
    simp only [ya, map_list_prod, List.map_map]
    apply List.prod_eq_one
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨b, -, rfl⟩ := hx
    exact h1 a b
  have hg : ∀ a b, g b (ya a) = 0 := by
    intro a b
    simp only [ya, map_list_prod, List.map_map]
    apply List.prod_eq_zero
    rw [List.mem_map]
    exact ⟨b, List.mem_finRange b, h0 a b⟩
  refine ⟨1 - ((List.finRange n).map (fun a => 1 - ya a)).prod, ?_, ?_⟩
  · intro a
    rw [map_sub, map_one, map_list_prod, List.map_map, List.prod_eq_zero, sub_zero]
    rw [List.mem_map]
    exact ⟨a, List.mem_finRange a, by simp [hf a]⟩
  · intro b
    rw [map_sub, map_one, map_list_prod, List.map_map, List.prod_eq_one, sub_self]
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨a, -, rfl⟩ := hx
    simp [hg a b]

theorem UpperTheory.V.Ws.Pu.sepEl :
    ∀ {O Γ : Type} [CommRing O] [IsLocalRing O] [Group Γ] {n : ℕ} (χ ψ : Fin n → Γ →* (ResidueField O)ˣ), (∀ a b, χ a ≠ ψ b) →
      ∃ y : MonoidAlgebra O Γ, (∀ a, MonoidAlgebra.lift O (ResidueField O) Γ ((Units.coeHom _).comp (χ a)) y = 1) ∧
        ∀ b, MonoidAlgebra.lift O (ResidueField O) Γ ((Units.coeHom _).comp (ψ b)) y = 0 := by
  intro O Γ _ _ _ n χ ψ hne
  have key : ∀ a b, ∃ e : MonoidAlgebra O Γ, MonoidAlgebra.lift O (ResidueField O) Γ ((Units.coeHom _).comp (χ a)) e = 1 ∧ MonoidAlgebra.lift O (ResidueField O) Γ ((Units.coeHom _).comp (ψ b)) e = 0 := by
    intro a b
    obtain ⟨γ, hγ⟩ : ∃ γ, χ a γ ≠ ψ b γ := by
      by_contra hc
      push_neg at hc
      exact hne a b (MonoidHom.ext hc)
    have hu : ((χ a γ : ResidueField O) - (ψ b γ : ResidueField O)) ≠ 0 := sub_ne_zero.2 (fun h => hγ (Units.ext h))
    obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective (ψ b γ : ResidueField O)
    obtain ⟨s, hs⟩ := IsLocalRing.residue_surjective ((χ a γ : ResidueField O) - (ψ b γ : ResidueField O))⁻¹
    refine ⟨MonoidAlgebra.single γ s - MonoidAlgebra.single 1 (s * r), ?_, ?_⟩
    · simp only [map_sub, MonoidAlgebra.lift_single, MonoidHom.comp_apply, Units.coeHom_apply, map_one, Units.val_one, Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq, map_mul, hr, hs, mul_one]
      rw [← mul_sub, inv_mul_cancel₀ hu]
    · simp only [map_sub, MonoidAlgebra.lift_single, MonoidHom.comp_apply, Units.coeHom_apply, map_one, Units.val_one, Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq, map_mul, hr, hs, mul_one, sub_self]
  choose e he using key
  exact UpperTheory.V.Ws.Pu.exists_separating_element (fun a => MonoidAlgebra.lift O (ResidueField O) Γ ((Units.coeHom _).comp (χ a))) (fun b => MonoidAlgebra.lift O (ResidueField O) Γ ((Units.coeHom _).comp (ψ b))) e (fun a b => (he a b).1) (fun a b => (he a b).2)
