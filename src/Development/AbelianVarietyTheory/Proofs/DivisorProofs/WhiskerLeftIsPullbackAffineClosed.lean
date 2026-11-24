module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Glues
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionWhiskerLeftRangePreimageSnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchedFunctionsGlueAffineFlatBaseChangeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSquareSectionsGlueOfBasisStatement
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PinchLift

theorem whiskerLeft_isPullback_affine_closed (S : Scheme.{0}) (E X X' Z Z' : Over S) (p : X' ⟶ X) (i : Z ⟶ X)
    (i' : Z' ⟶ X') (p' : Z' ⟶ Z) (hc : i' ≫ p = p' ≫ i) (hpb : IsPullback i'.left p'.left p.left i.left)
    [IsAffineHom p.left] [IsClosedImmersion i.left] :
    IsPullback (E ◁ i').left (E ◁ p').left (E ◁ p).left (E ◁ i).left ∧ IsAffineHom (E ◁ p).left ∧
      IsClosedImmersion (E ◁ i).left := by
  have hP := GlobalTheory.DualCon.isPullback_whiskerLeft_snd_left E p
  have hI := GlobalTheory.DualCon.isPullback_whiskerLeft_snd_left E i
  have hP' := GlobalTheory.DualCon.isPullback_whiskerLeft_snd_left E p'
  refine ⟨?_, MorphismProperty.of_isPullback hP.flip ‹_›, MorphismProperty.of_isPullback hI.flip ‹_›⟩
  have hout := hP'.flip.paste_horiz hpb
  refine IsPullback.of_right ?_ ?_ hP.flip
  · have h1 : (E ◁ i').left ≫ (snd E X').left = (snd E Z').left ≫ i'.left := by
      rw [← Over.comp_left, ← Over.comp_left]; simp
    have h2 : (E ◁ i).left ≫ (snd E X).left = (snd E Z).left ≫ i.left := by
      rw [← Over.comp_left, ← Over.comp_left]; simp
    rw [h1, h2]; exact hout
  · rw [← Over.comp_left, ← Over.comp_left, ← whiskerLeft_comp, ← whiskerLeft_comp, hc]

theorem glues_whiskerLeft : ∀ (S : Scheme.{0}) (E X X' Z Z' : Over S) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), Flat E.hom → i' ≫ p = p' ≫ i → IsPullback i'.left p'.left p.left i.left → IsAffineHom p.left → IsClosedImmersion i.left → GlobalTheory.PinchLift.Glues p.left i.left i'.left p'.left → IsPullback (E ◁ i').left (E ◁ p').left (E ◁ p).left (E ◁ i).left ∧ IsAffineHom (E ◁ p).left ∧ IsClosedImmersion (E ◁ i).left ∧ GlobalTheory.PinchLift.Glues (E ◁ p).left (E ◁ i).left (E ◁ i').left (E ◁ p').left := by
  intro S E X X' Z Z' p i i' p' hE hc hpb hp hi hg
  obtain ⟨h1, h2, h3⟩ := whiskerLeft_isPullback_affine_closed S E X X' Z Z' p i i' p' hc hpb
  refine ⟨h1, h2, h3, ?_⟩
  refine GlobalTheory.T.pullback_square_sections_glue_of_basis (E ◁ p).left (E ◁ i).left (E ◁ i').left (E ◁ p').left
    {W | IsAffineOpen W ∧ ∃ V : X.left.Opens, IsAffineOpen V ∧ W ≤ (snd E X).left ⁻¹ᵁ V} ?_ ?_
  · intro W x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := X.left.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ ((snd E X).left x)) isOpen_univ
    obtain ⟨_, ⟨W', hW', rfl⟩, hxW', hle⟩ := (E ⊗ X).left.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ ((W ⊓ (snd E X).left ⁻¹ᵁ V : (E ⊗ X).left.Opens) : Set (E ⊗ X).left) from ⟨hx, hxV⟩)
      (W ⊓ (snd E X).left ⁻¹ᵁ V).isOpen
    exact ⟨W', ⟨hW', V, hV, fun y hy => (hle hy).2⟩, hxW', fun y hy => (hle hy).1⟩
  · rintro W ⟨hW, V, hV, hWV⟩
    exact GlobalTheory.T.pinched_functions_glue_affine_flat_baseChange S E X X' Z Z' p i i' p' hE hc hpb hp hi hg V W hV hW hWV

end GlobalTheory.PinchLift
