module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominantSmoothMapCoords
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChartFType

theorem finiteType_of_equiv {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra ℤ C]
    [Algebra.FiniteType ℤ C] (E : B ≃+* C) (g : ℤ →+* A) (f : A →+* B) : f.FiniteType := by
  have hC : (algebraMap ℤ C).FiniteType := RingHom.finiteType_algebraMap.2 inferInstance
  have hE : (E.symm.toRingHom).FiniteType := RingHom.FiniteType.of_surjective _ E.symm.surjective
  have h1 : ((E.symm.toRingHom).comp (algebraMap ℤ C)).FiniteType := hE.comp hC
  have h2 : f.comp (Int.castRingHom A) = (E.symm.toRingHom).comp (algebraMap ℤ C) := RingHom.ext_int _ _
  rw [← h2] at h1
  exact RingHom.FiniteType.of_comp_finiteType h1

theorem main : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) [Finite κ] (x : κ → Ω), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ x → ∃ s : X ⟶ Spec (CommRingCat.of ℤ), LocallyOfFiniteType s ∧ QuasiCompact s ∧ ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap ℤ Ω)) := by
  intro X Ω _ ξ κ _ x hall T
  refine ⟨specZIsTerminal.from X, ?_, ?_, specZIsTerminal.hom_ext _ _⟩
  · have hQ := (RingHom.finiteType_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.finiteType_holdsForLocalizationAway).1
    rw [HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFiniteType) hQ]
    intro q
    obtain ⟨c, hcq⟩ := T.cover ⟨q, hall q⟩
    obtain ⟨U, hUa, hU⟩ := T.affine c hcq.1
    have hqU : q ∈ U := (hU q).2 ⟨hall q, hcq⟩
    have hg : genPt ξ ∈ U := (hall q).mem_open U.isOpen hqU
    obtain ⟨E, -⟩ := GlobalTheory.CompanionTheory.Ar.ChartSmooth.exists_secEquiv hall T hcq.1 hU hg
    haveI : Algebra.FiniteType ℤ (Algebra.adjoin ℤ (Set.range fun j => x j / x c)) :=
      (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)
    exact ⟨⟨⊤, isAffineOpen_top _⟩, ⟨U, hUa⟩, hqU, by simp, finiteType_of_equiv E (Int.castRingHom _) _⟩
  · rw [quasiCompact_iff_compactSpace]
    choose U hUa hU using T.affine
    refine ⟨?_⟩
    have hcov : (Set.univ : Set X) = ⋃ (c : κ) (hc : x c ≠ 0), (U c hc : Set X) := by
      ext q
      simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
      obtain ⟨c, hcq⟩ := T.cover ⟨q, hall q⟩
      exact ⟨c, hcq.1, (hU c hcq.1 q).2 ⟨hall q, hcq⟩⟩
    rw [hcov]
    exact isCompact_iUnion fun c => isCompact_iUnion fun hc => (hUa c hc).isCompact

end GlobalTheory.CompanionTheory.Ar.ChartFType
