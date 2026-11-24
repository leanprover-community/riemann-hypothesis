module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Defs
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AddJFintype
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

namespace GlobalTheory.CompanionTheory.Ar.FlagStep.AdjoinLower

theorem adjoin_lower_eq_top : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω] (S : Type) (r : S → ℕ)
    (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) Ω),
    (∀ σ k, u σ k k = 1) → (∀ σ l k, l < k → u σ l k = 0) →
    Module.finrank (IntermediateField.adjoin Ω₀
      (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2)) Ω = 1 →
    IntermediateField.adjoin Ω₀
      (Set.range fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2) = ⊤ := by
  intro Ω₀ Ω _ _ _ S r u hdiag hup hfin
  rw [IntermediateField.finrank_eq_one_iff_eq_top] at hfin
  rw [← hfin]
  apply le_antisymm
  · apply IntermediateField.adjoin.mono
    rintro _ ⟨⟨σ, ⟨l, k⟩, _⟩, rfl⟩
    exact ⟨⟨σ, l, k⟩, rfl⟩
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨σ, l, k⟩, rfl⟩
    rcases lt_trichotomy l k with h | h | h
    · simp only [hup σ l k h]
      exact zero_mem _
    · subst h
      simp only [hdiag σ l]
      exact one_mem _
    · exact IntermediateField.subset_adjoin _ _ ⟨⟨σ, ⟨l, k⟩, h⟩, rfl⟩

end GlobalTheory.CompanionTheory.Ar.FlagStep.AdjoinLower
