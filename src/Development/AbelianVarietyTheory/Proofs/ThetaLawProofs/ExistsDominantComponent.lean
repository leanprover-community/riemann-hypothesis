module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory.KeyCx


open TensorProduct in
theorem exists_dominant_component :
    ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra.FiniteType ℤ R] (g : R →+* ℂ), ∃ (E : Type) (_ : CommRing E) (_ : IsDomain E) (_ : Algebra ℂ E) (ρ : R →+* E) (e : E →ₐ[ℂ] ℂ), Algebra.FiniteType ℂ E ∧ Function.Injective ρ ∧ e.toRingHom.comp ρ = g := by
  intro R _ _ _ g
  letI : Algebra R (ℂ ⊗[ℤ] R) := Algebra.TensorProduct.rightAlgebra
  haveI : Module.Flat R (ℂ ⊗[ℤ] R) :=
    Module.Flat.of_linearEquiv (Algebra.TensorProduct.commRight ℤ R ℂ).symm.toLinearEquiv
  let e₀ : (ℂ ⊗[ℤ] R) →ₐ[ℂ] ℂ :=
    Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) g.toIntAlgHom (fun _ _ => Commute.all _ _)
  have he : ∀ r : R, e₀ (algebraMap R (ℂ ⊗[ℤ] R) r) = g r := by
    intro r
    change e₀ (1 ⊗ₜ r) = g r
    simp [e₀]
  let Q : Ideal (ℂ ⊗[ℤ] R) := RingHom.ker e₀.toRingHom
  haveI : Q.IsPrime := RingHom.ker_isPrime _
  obtain ⟨q, hqQ, hq, hlo⟩ := Ideal.exists_ideal_le_liesOver_of_le
    (p := (⊥ : Ideal R)) (q := Q.under R) Q bot_le
  refine ⟨(ℂ ⊗[ℤ] R) ⧸ q, inferInstance, inferInstance, inferInstance,
    (Ideal.Quotient.mk q).comp (algebraMap R _),
    Ideal.Quotient.liftₐ q e₀ (fun a ha => hqQ ha), inferInstance, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro r hr
    have h1 : r ∈ q.under R :=
      Ideal.mem_comap.mpr (Ideal.Quotient.eq_zero_iff_mem.mp hr)
    rw [← hlo.over] at h1
    exact h1
  · ext r
    exact he r

end GlobalTheory.KeyCx
