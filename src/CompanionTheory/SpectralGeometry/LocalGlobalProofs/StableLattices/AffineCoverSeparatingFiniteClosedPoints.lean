module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Limits
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
import Mathlib.Tactic.NormNum.Prime
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibAc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

noncomputable section

namespace GlobalTheory.CompanionTheory.CoverPoints

theorem exists_affine_cover_finite_closed_points : ∀ (X : Scheme.{0}) [CompactSpace X] (F : Set X) (hF : F.Finite) (hc : ∀ x ∈ F, IsClosed ({x} : Set X)), ∃ (r : ℕ) (V : Fin (r + 1) → X.Opens), (∀ j, IsAffineOpen (V j)) ∧ ⨆ j, V j = ⊤ ∧
      ∀ x ∈ F, ∀ i j, x ∈ V i → x ∈ V j → i = j := by
  intro X _ F hF hc
  have hcl : ∀ G : Set X, G ⊆ F → IsClosed G := fun G hG => by
    have h := (hF.subset hG).isClosed_biUnion (fun x hx => hc x (hG hx))
    simpa using h

  have hW : ∀ x : F, ∃ W : X.Opens, IsAffineOpen W ∧ x.1 ∈ W ∧ ∀ y ∈ F, y ∈ W → y = x.1 := by
    intro x
    have hx : x.1 ∈ (F \ {x.1})ᶜ := fun h => h.2 rfl
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWo⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx
      (hcl _ Set.diff_subset).isOpen_compl
    refine ⟨W, hW, hxW, fun y hy hyW => ?_⟩
    by_contra hne
    exact hWo hyW ⟨hy, hne⟩
  choose W hWa hWx hWF using hW

  have hC : IsCompact ((⨆ x, W x : X.Opens) : Set X)ᶜ :=
    (⨆ x, W x : X.Opens).isOpen.isClosed_compl.isCompact
  obtain ⟨s, hs⟩ := hC.elim_finite_subcover
    (fun U : {U : X.Opens // IsAffineOpen U ∧ ∀ x ∈ F, x ∉ U} => (U.1 : Set X))
    (fun U => U.1.isOpen) (by
      intro y hy
      have hy' : y ∈ Fᶜ := fun h => hy (by
        exact (TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, h⟩, hWx ⟨y, h⟩⟩ : y ∈ (⨆ x, W x : X.Opens)))
      obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUo⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hy'
        (hcl F subset_rfl).isOpen_compl
      exact Set.mem_iUnion.2 ⟨⟨U, hU, fun x hx hxU => hUo hxU hx⟩, hyU⟩)
  haveI : Fintype F := hF.fintype

  let V' : Option (F ⊕ s) → X.Opens := fun a => match a with
    | none => ⊥
    | some (Sum.inl x) => W x
    | some (Sum.inr U) => U.1.1
  have hV'a : ∀ a, IsAffineOpen (V' a) := by
    rintro (_ | x | U)
    · exact isAffineOpen_bot X
    · exact hWa x
    · exact U.1.2.1
  have hV'F : ∀ x (hx : x ∈ F) a, x ∈ V' a → a = some (Sum.inl ⟨x, hx⟩) := by
    rintro x hx (_ | y | U) h
    · exact absurd h (by simp [V'])
    · have : x = y.1 := hWF y x hx h
      subst this
      rfl
    · exact absurd h (U.1.2.2 x hx)
  let e : Option (F ⊕ s) ≃ Fin (Fintype.card (F ⊕ s) + 1) :=
    Fintype.equivFinOfCardEq Fintype.card_option
  refine ⟨Fintype.card (F ⊕ s), fun j => V' (e.symm j), fun j => hV'a _, ?_, ?_⟩
  · refine top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ?_
    by_cases hy : y ∈ (⨆ x, W x : X.Opens)
    · obtain ⟨x, hx⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
      exact ⟨e (some (Sum.inl x)), by simpa [V'] using hx⟩
    · obtain ⟨U, hU, hyU⟩ := Set.mem_iUnion₂.1 (hs hy)
      exact ⟨e (some (Sum.inr ⟨U, hU⟩)), by simpa [V'] using hyU⟩
  · intro x hx i j hi hj
    exact e.symm.injective ((hV'F x hx _ hi).trans (hV'F x hx _ hj).symm)

end GlobalTheory.CompanionTheory.CoverPoints
