module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.PullbackCarrier
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_mem_fibre_of_geometric_lifting :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (S P' X : Scheme.{0}) (π : S ⟶ Sp R) (h : P' ⟶ Sp R) (a : X ⟶ P') (q : X ⟶ S), Surjective π → ∀ x : P', h x = closedPoint R → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ P') (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ h = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ q = s) → ∃ z : X, a z = x := by
  intro R _ _ S P' X π h a q hπ x hx H
  obtain ⟨s₀, hs₀⟩ := π.surjective (h x)
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := h) (g := π) x s₀ hs₀.symm
  let Ω : Type := AlgebraicClosure ((pullback h π).residueField w)
  let t : Sp Ω ⟶ pullback h π :=
    Spec.map (CommRingCat.ofHom (algebraMap ((pullback h π).residueField w) Ω)) ≫
      (pullback h π).fromSpecResidueField w
  have ht : ∀ y, t y = w := by
    intro y
    simp only [t, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _
  have hξ : ∀ y, (t ≫ pullback.fst h π) y = x := by
    intro y
    rw [Scheme.Hom.comp_apply, ht, hw]
  obtain ⟨p, hp, -⟩ := H Ω (t ≫ pullback.fst h π) (t ≫ pullback.snd h π)
    (by
      ext y
      constructor
      · rintro ⟨u, rfl⟩
        exact hξ u
      · rintro rfl
        exact ⟨closedPoint Ω, hξ _⟩)
    (by simp [pullback.condition])
  refine ⟨p (closedPoint Ω), ?_⟩
  have h₀ := hξ (closedPoint Ω)
  rw [← hp] at h₀
  exact (Scheme.Hom.comp_apply p a _).symm.trans h₀

end GlobalTheory.Mum
