module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Order.CompletePartialOrder
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenConnectedComponentOfIsLocallyNoetherian
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory

theorem exists_integral_clopen_cover_of_smooth_field :
    ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k) [Smooth f] [QuasiCompact f], ∃ (κ : Type) (U : κ → X.Opens), ⨆ c, U c = ⊤ ∧ (Pairwise fun a b => Disjoint (U a) (U b)) ∧ ∀ c, IsIntegral (U c).toScheme ∧ IsClosedImmersion (U c).ι := by
  intro k _ X f _ _
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hopen : ∀ c : _root_.ConnectedComponents X, IsOpen ((_root_.ConnectedComponents.mk : X → _) ⁻¹' {c}) := by
    intro c
    obtain ⟨x, rfl⟩ := _root_.ConnectedComponents.surjective_coe c
    rw [connectedComponents_preimage_singleton]
    exact GlobalTheory.isOpen_connectedComponent_of_isLocallyNoetherian X inferInstance x
  let U : _root_.ConnectedComponents X → X.Opens := fun c => ⟨_, hopen c⟩
  refine ⟨_root_.ConnectedComponents X, U, ?_, ?_, fun c => ?_⟩
  · rw [eq_top_iff]
    intro x _
    exact Opens.mem_iSup.2 ⟨_root_.ConnectedComponents.mk x, rfl⟩
  · intro a b hab
    rw [disjoint_iff, ← SetLike.coe_set_eq]
    ext x
    simp only [U, Opens.coe_inf, Opens.coe_mk, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, Opens.coe_bot, Set.mem_empty_iff_false, iff_false, not_and]
    rintro rfl rfl
    exact hab rfl
  · obtain ⟨x, rfl⟩ := _root_.ConnectedComponents.surjective_coe c
    have hU : ((U (_root_.ConnectedComponents.mk x) : X.Opens) : Set X) = connectedComponent x :=
      connectedComponents_preimage_singleton
    constructor
    · haveI : ConnectedSpace (U (_root_.ConnectedComponents.mk x)).toScheme := by
        show ConnectedSpace ((U (_root_.ConnectedComponents.mk x) : Set X))
        rw [← isConnected_iff_connectedSpace, hU]
        exact isConnected_connectedComponent
      exact isIntegral_of_smooth_field_of_connectedSpace ((U (_root_.ConnectedComponents.mk x)).ι ≫ f)
    · refine IsClosedImmersion.of_isPreimmersion _ ?_
      rw [Scheme.Opens.range_ι, hU]
      exact isClosed_connectedComponent

end GlobalTheory
