module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Development.WeilBound.CoreStatements.HodgeTatePoints.PdvrExt
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
public import Mathlib.FieldTheory.Extension
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.CompanionTheory.Relay.complete_dvr_dominating_valuation : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (l : Type) [Field l] [Algebra (IsLocalRing.ResidueField V) l] [FiniteDimensional (IsLocalRing.ResidueField V) l], ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R) (f : V →+* R) (_ : IsLocalHom f) (s : l →+* IsLocalRing.ResidueField R), IsAdicComplete (IsLocalRing.maximalIdeal R) R ∧ Function.Injective f ∧ s.comp (algebraMap _ l) = IsLocalRing.ResidueField.map f := by
  intro V _ _ _ l _ _ _
  obtain ⟨n, b⟩ : ∃ n, Nonempty (Module.Basis (Fin n) (IsLocalRing.ResidueField V) l) :=
    ⟨_, ⟨Module.finBasis (IsLocalRing.ResidueField V) l⟩⟩
  obtain ⟨b⟩ := b
  have hne : ∀ i, minpoly (IsLocalRing.ResidueField V) (b i) ≠ 0 := fun i =>
    minpoly.ne_zero (Algebra.IsIntegral.isIntegral (b i))
  obtain ⟨R1, _, _, _, f1, _, hinj1, hsplit⟩ := PositivityTheory.HtPt.Pdvr.exists_splits _ V
    (∏ i, minpoly (IsLocalRing.ResidueField V) (b i)) rfl
  letI : Algebra (IsLocalRing.ResidueField V) (IsLocalRing.ResidueField R1) :=
    (IsLocalRing.ResidueField.map f1).toAlgebra
  have hS : IntermediateField.adjoin (IsLocalRing.ResidueField V) (Set.range b) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hspan : Submodule.span (IsLocalRing.ResidueField V) (Set.range b) ≤
        (IntermediateField.adjoin (IsLocalRing.ResidueField V) (Set.range b)).toSubalgebra.toSubmodule :=
      Submodule.span_le.mpr (IntermediateField.subset_adjoin _ _)
    exact hspan (b.span_eq ▸ Submodule.mem_top)
  have hK : ∀ s ∈ Set.range b, IsIntegral (IsLocalRing.ResidueField V) s ∧
      ((minpoly (IsLocalRing.ResidueField V) s).map
        (algebraMap (IsLocalRing.ResidueField V) (IsLocalRing.ResidueField R1))).Splits := by
    rintro s ⟨i, rfl⟩
    refine ⟨Algebra.IsIntegral.isIntegral (b i), ?_⟩
    refine Polynomial.Splits.of_dvd hsplit ?_ ?_
    · exact Polynomial.map_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ => hne j)
    · exact Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  obtain ⟨φ⟩ := IntermediateField.nonempty_algHom_of_adjoin_splits hK hS
  obtain ⟨R, _, _, _, f2, _, hcomp, hinj2⟩ := PositivityTheory.HtPt.Pdvr.exists_complete R1
  refine ⟨R, inferInstance, inferInstance, inferInstance, f2.comp f1, inferInstance,
    (IsLocalRing.ResidueField.map f2).comp φ.toRingHom, hcomp, hinj2.comp hinj1, ?_⟩
  ext x
  rw [IsLocalRing.ResidueField.map_comp]
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  rfl
