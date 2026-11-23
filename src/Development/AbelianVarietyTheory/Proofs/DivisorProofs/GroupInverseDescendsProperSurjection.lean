module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentOfEqualisedProperCoverNormalStatement
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem inv_pullback_left_fst {X Y : Scheme.{0}} (f : X ⟶ Y) (G' : Over Y) [GrpObj G'] {T : Over X}
    (z : T ⟶ (Over.pullback f).obj G') :
    (z⁻¹).left ≫ pullback.fst G'.hom f = z.left ≫ pullback.fst G'.hom f ≫ ι[G'].left := by
  show (z ≫ (Over.pullback f).map ι[G']).left ≫ _ = _
  rw [Over.comp_left, Category.assoc]
  congr 1
  simp only [Over.pullback_map_left]
  first | exact pullback.lift_fst _ _ _ | erw [pullback.lift_fst]

theorem exists_inv_descent : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] (G : Over (Sp R)) (β : G'.left ⟶ G.left), Smooth G.hom → IsPullback β G'.hom G.hom π → ∀ φ : (Over.pullback (pullback.fst π π)).obj G' ≅ (Over.pullback (pullback.snd π π)).obj G', IsMonHom φ.hom → pullback.fst G'.hom (pullback.fst π π) ≫ β = φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β → ∃ i : G ⟶ G, ∀ (T : Over S) (x : T ⟶ G') (x₀ : Over.mk (T.hom ≫ π) ⟶ G), x₀.left = x.left ≫ β → (x₀ ≫ i).left = x⁻¹.left ≫ β := by
  intro R _ _ _ _ S π hP hS hI G' _ G β hsm hpb φ hφ hc
  have hfl : Flat G.hom := inferInstance
  have D := fun (W : Scheme.{0}) => GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S G.left G'.left W π G.hom β G'.hom hP hS hI hfl hpb
  have epi : ∀ {W : Scheme.{0}} (a b : G.left ⟶ W), β ≫ a = β ≫ b → a = b := by
    intro W a b hab
    obtain ⟨h₀, -, hu⟩ := D W (β ≫ a) (by rw [pullback.condition_assoc])
    exact (hu a rfl).trans (hu b hab.symm).symm
  have hw : β ≫ G.hom = G'.hom ≫ π := hpb.w
  set a₁ := pullback.fst β β
  set a₂ := pullback.snd β β
  have hσ : (a₁ ≫ G'.hom) ≫ π = (a₂ ≫ G'.hom) ≫ π := by
    simp only [Category.assoc, ← hw]; rw [pullback.condition_assoc]
  let σ : pullback β β ⟶ pullback π π := pullback.lift _ _ hσ
  let x : Over.mk σ ⟶ (Over.pullback (pullback.fst π π)).obj G' :=
    Over.homMk (pullback.lift a₁ σ (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)
  have hcx : ∀ y : Over.mk σ ⟶ (Over.pullback (pullback.fst π π)).obj G',
      y.left ≫ pullback.fst G'.hom (pullback.fst π π) ≫ β =
        (y ≫ φ.hom).left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β := by
    intro y; rw [Over.comp_left, Category.assoc, ← hc]
  have h2 : (x ≫ φ.hom).left ≫ pullback.fst G'.hom (pullback.snd π π) = a₂ := by
    apply hpb.hom_ext
    · rw [Category.assoc, ← hcx x]
      show pullback.lift a₁ σ _ ≫ _ ≫ β = _
      rw [pullback.lift_fst_assoc]
      exact pullback.condition
    · rw [Category.assoc, pullback.condition, ← Category.assoc,
        show (x ≫ φ.hom).left ≫ pullback.snd G'.hom (pullback.snd π π) = σ from Over.w (x ≫ φ.hom)]
      exact pullback.lift_snd _ _ _
  have eq : a₁ ≫ ι[G'].left ≫ β = a₂ ≫ ι[G'].left ≫ β := by
    have := hcx x⁻¹
    rw [GrpObj.inv_comp, reassoc_of% inv_pullback_left_fst, reassoc_of% inv_pullback_left_fst,
      reassoc_of% h2] at this
    simp only [x, Over.homMk_left] at this
    rwa [pullback.lift_fst_assoc] at this
  obtain ⟨h₀, hh₀, -⟩ := D G.left (ι[G'].left ≫ β) eq
  have hover : h₀ ≫ G.hom = G.hom := by
    apply epi
    rw [reassoc_of% hh₀, hw, ← Category.assoc, Over.w ι[G']]
  refine ⟨Over.homMk h₀ hover, ?_⟩
  intro T x' x₀ hx
  rw [Over.comp_left]
  show x₀.left ≫ h₀ = _
  rw [hx, Category.assoc, hh₀]
  show _ = (x' ≫ ι[G']).left ≫ β
  rw [Over.comp_left, Category.assoc]

end GlobalTheory.Mum
