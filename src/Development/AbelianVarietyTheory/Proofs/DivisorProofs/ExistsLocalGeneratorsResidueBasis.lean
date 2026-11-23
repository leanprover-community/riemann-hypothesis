module

public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.LocalRing.Module
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.FibreBasisSpread

theorem exists_away_linearCombination_bijective : ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] (J : Type) [Fintype J] (v : J → M) (p : Ideal R) [p.IsPrime],
    Function.Bijective (Finsupp.linearCombination p.ResidueField (fun i => (1 : p.ResidueField) ⊗ₜ[R] v i)) →
    ∃ g : R, g ∉ p ∧ (∀ x : M, ∃ (n : ℕ) (c : J →₀ R), g ^ n • x = Finsupp.linearCombination R v c) ∧
      (∀ c : J →₀ R, Finsupp.linearCombination R v c = 0 → ∃ n : ℕ, g ^ n • c = 0) := by
  intro R _ M _ _ _ _ J _ v p _ hbij
  classical
  haveI : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  let Rp := Localization.AtPrime p
  have hloc : Function.Bijective (IsLocalizedModule.map p.primeCompl
      (Finsupp.mapRange.linearMap (Algebra.linearMap R Rp)) (TensorProduct.mk R Rp M 1)
      (Finsupp.linearCombination R v)) := by
    rw [IsLocalizedModule.map_linearCombination, LinearMap.coe_restrictScalars]
    apply Module.IsLocalRing.linearCombination_bijective_of_flat
    rw [← (AlgebraTensorModule.cancelBaseChange R Rp p.ResidueField p.ResidueField M).comp_bijective]
    have heq : (AlgebraTensorModule.cancelBaseChange R Rp p.ResidueField p.ResidueField M).toLinearMap ∘ₗ
        Finsupp.linearCombination p.ResidueField
          (TensorProduct.mk Rp p.ResidueField (Rp ⊗[R] M) 1 ∘ (TensorProduct.mk R Rp M 1 ∘ v)) =
        Finsupp.linearCombination p.ResidueField (fun i => (1 : p.ResidueField) ⊗ₜ[R] v i) := by
      ext i
      simp
    convert hbij using 1
    rw [← heq, LinearMap.coe_comp]
    rfl
  obtain ⟨g, hg, h⟩ := Module.FinitePresentation.exists_notMem_bijective
    (Finsupp.linearCombination R v) p _ _ hloc
  refine ⟨g, hg, fun x => ?_, fun c hc => ?_⟩
  · obtain ⟨y, hy⟩ := h.2 (LocalizedModule.mk x 1)
    induction y using LocalizedModule.induction_on with
    | h c s =>
      rw [LocalizedModule.map_mk, LocalizedModule.mk_eq] at hy
      obtain ⟨⟨u, hu⟩, hu'⟩ := hy
      obtain ⟨a, rfl⟩ := hu
      obtain ⟨b, hb⟩ := s.2
      refine ⟨a + b, g ^ a • c, ?_⟩
      have hb' : (s : R) = g ^ b := hb.symm
      simp only [Submonoid.smul_def, one_smul] at hu'
      rw [map_smul, hu', hb', smul_smul, pow_add]
  · have h0 : LocalizedModule.map (Submonoid.powers g) (Finsupp.linearCombination R v)
        (LocalizedModule.mk c 1) = LocalizedModule.map (Submonoid.powers g)
        (Finsupp.linearCombination R v) 0 := by
      rw [LocalizedModule.map_mk, hc, map_zero, LocalizedModule.zero_mk]
    have h1 := h.1 h0
    rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at h1
    obtain ⟨⟨u, hu⟩, hu'⟩ := h1
    obtain ⟨a, rfl⟩ := hu
    exact ⟨a, by simpa [Submonoid.smul_def] using hu'⟩

end GlobalTheory.FibreBasisSpread
