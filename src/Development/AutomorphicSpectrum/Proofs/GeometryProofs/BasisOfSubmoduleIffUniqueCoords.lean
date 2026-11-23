module

public import Mathlib.LinearAlgebra.LinearIndependent.Defs
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem basis_iff_unique_combinations : ∀ (K W : Type) [Field K] [AddCommGroup W] [Module K W] (S : Submodule K W) (n : ℕ) (b : Fin n → W),
    (LinearIndependent K b ∧ Submodule.span K (Set.range b) = S) ↔
      (∀ i, b i ∈ S) ∧ ∀ e ∈ S, ∃! x : Fin n → K, e = ∑ i, x i • b i := by
  intro K W _ _ _ S n b
  constructor
  · rintro ⟨hli, hspan⟩
    refine ⟨fun i => hspan ▸ Submodule.subset_span ⟨i, rfl⟩, fun e he => ?_⟩
    rw [← hspan, Submodule.mem_span_range_iff_exists_fun] at he
    obtain ⟨x, hx⟩ := he
    refine ⟨x, hx.symm, fun y hy => ?_⟩
    have h0 : ∑ i, (y - x) i • b i = 0 := by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, ← hy, hx, sub_self]
    funext i
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h0 i)
  · rintro ⟨hb, huniq⟩
    refine ⟨Fintype.linearIndependent_iff.mpr fun g hg i => ?_, le_antisymm ?_ fun e he => ?_⟩
    · obtain ⟨x, _, hx⟩ := huniq 0 S.zero_mem
      have hg0 : g = x := hx g hg.symm
      have h00 : (0 : Fin n → K) = x := hx 0 (by simp)
      rw [hg0, ← h00]
      rfl
    · exact Submodule.span_le.mpr (Set.range_subset_iff.mpr hb)
    · obtain ⟨x, hx, _⟩ := huniq e he
      rw [hx]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
