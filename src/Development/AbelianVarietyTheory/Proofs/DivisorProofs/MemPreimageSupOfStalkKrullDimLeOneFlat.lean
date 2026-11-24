module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.Combinatorics.Quiver.ReflQuiver
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CodimOne

theorem mem_preimage_sup_of_ringKrullDim_stalk_le_one :
    ∀ (X S : Scheme.{0}) [IsIntegral S] (f : X ⟶ S) [Flat f] [GeometricallyIntegral f] (V : X.Opens) (U : S.Opens), (∀ s : S, ∃ x ∈ V, f x = s) → (U : Set S).Nonempty → (∀ z : X, ringKrullDim ((X).presheaf.stalk z) ≤ 1 → z ∈ f ⁻¹ᵁ U ⊔ V) := by
  intro X S _ f _ _ V U hV hU z hz
  by_contra hzm
  have hzU : f z ∉ U := fun h => hzm (Or.inl h)
  have hzV : z ∉ V := fun h => hzm (Or.inr h)
  set s := f z with hs

  let ξ : X := f.fiberι s (genericPoint (f.fiber s))
  have hfξ : f ξ = s := (f.range_fiberι s).le ⟨_, rfl⟩
  have hrange : ∀ y : X, f y = s → ξ ⤳ y := by
    intro y hy
    obtain ⟨w, rfl⟩ : y ∈ Set.range (f.fiberι s) := (f.range_fiberι s).ge hy
    exact (genericPoint_specializes w).map (f.fiberι s).continuous
  obtain ⟨x, hxV, hxs⟩ := hV s
  have hξV : ξ ∈ V := (hrange x hxs).mem_open V.isOpen hxV
  have hξz : ξ ⤳ z := hrange z rfl
  have hξnez : ξ ≠ z := fun h => hzV (h ▸ hξV)

  obtain ⟨u, huU⟩ := hU
  have hηU : genericPoint S ∈ U := (genericPoint_specializes u).mem_open U.isOpen huU
  have hηs : genericPoint S ⤳ f ξ := hfξ ▸ genericPoint_specializes s
  obtain ⟨ζ, hζξ, hfζ⟩ := (Flat.generalizingMap f) hηs
  have hζneξ : ζ ≠ ξ := by
    intro h
    apply hzU
    rw [← hfξ, ← h, hfζ]
    exact hηU
  have h1 : z < ξ := lt_of_le_not_ge hξz (fun h => hξnez (hξz.antisymm h).eq)
  have h2 : ξ < ζ := lt_of_le_not_ge hζξ (fun h => hζneξ (hζξ.antisymm h).eq)
  have hc : (2 : ℕ∞) ≤ Order.coheight z := by
    have a := Order.coheight_add_one_le h1
    have b := Order.coheight_add_one_le h2
    have : (1 : ℕ∞) + 1 ≤ Order.coheight ζ + 1 + 1 := by gcongr; exact le_add_self
    calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ Order.coheight ζ + 1 + 1 := this
      _ ≤ Order.coheight ξ + 1 := by gcongr
      _ ≤ Order.coheight z := a
  rw [ringKrullDim_stalk_eq_coheight] at hz
  have : Order.coheight z ≤ 1 := by exact_mod_cast hz
  exact absurd (hc.trans this) (by norm_num)

end GlobalTheory.CodimOne
