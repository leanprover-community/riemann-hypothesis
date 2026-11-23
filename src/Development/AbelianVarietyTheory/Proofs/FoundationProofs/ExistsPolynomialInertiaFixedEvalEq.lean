module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import ReciprocityTheory.GaloisValuations.Global
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

namespace GlobalTheory

theorem exists_polynomial_closedSubgroup_fixed_eval_eq {F Ω : Type*} [Field F] [Field Ω]
    [Algebra F Ω] [IsGalois F Ω] (H : ClosedSubgroup (Ω ≃ₐ[F] Ω)) (ζ u : Ω)
    (h : ∀ s ∈ H.toSubgroup, s ζ = ζ → s u = u) :
    ∃ P : Polynomial Ω, (∀ s ∈ H.toSubgroup, ∀ d, s (P.coeff d) = P.coeff d) ∧
      P.eval ζ = u := by
  classical
  let T : IntermediateField F Ω := IntermediateField.fixedField H.toSubgroup
  have hT : T.fixingSubgroup = H.toSubgroup := InfiniteGalois.fixingSubgroup_fixedField H
  let E : IntermediateField F Ω :=
    (IntermediateField.adjoin T ({ζ} : Set Ω)).restrictScalars F
  have hu : u ∈ E := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
    intro s hs
    rw [IntermediateField.mem_fixingSubgroup_iff] at hs
    refine h s ?_ (hs ζ (IntermediateField.mem_adjoin_simple_self T ζ))
    have : s ∈ T.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact hs x ((IntermediateField.adjoin T ({ζ} : Set Ω)).algebraMap_mem ⟨x, hx⟩)
    rw [hT] at this
    exact this
  have hint : IsIntegral T ζ :=
    (Algebra.IsAlgebraic.isAlgebraic (R := F) ζ).isIntegral.tower_top
  have hu' : u ∈ (IntermediateField.adjoin T ({ζ} : Set Ω)).toSubalgebra := hu
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval] at hu'
  obtain ⟨Q, hQ⟩ := hu'
  refine ⟨Q.map (algebraMap T Ω), ?_, ?_⟩
  · intro s hs d
    rw [Polynomial.coeff_map]
    exact (IntermediateField.mem_fixedField_iff H.toSubgroup _).1 (Q.coeff d).2 s hs
  · rw [Polynomial.eval_map_algebraMap]
    exact hQ

theorem exists_polynomial_inertia_fixed_eval_eq (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (ζ u : Ω)
    (h : ∀ s ∈ Ine (F := ℚ) A, s ζ = ζ → s u = u) :
    ∃ P : Polynomial Ω, (∀ s ∈ Ine (F := ℚ) A, ∀ d, s (P.coeff d) = P.coeff d) ∧
      P.eval ζ = u :=
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  exists_polynomial_closedSubgroup_fixed_eval_eq
    ⟨Ine (F := ℚ) A, isClosed_Ine (F := ℚ) A⟩ ζ u h

end GlobalTheory
