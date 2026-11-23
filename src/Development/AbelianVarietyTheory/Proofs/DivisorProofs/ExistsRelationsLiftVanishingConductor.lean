module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem relations_lift_vanishing : (∀ (R R' ν : Type) [CommRing R] [CommRing R'] [Algebra R R'] (c : Ideal R), (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ G ∈ (c.map (algebraMap R R')).map (MvPolynomial.C : R' →+* MvPolynomial ν R'), ∃ H : MvPolynomial ν R, MvPolynomial.map (Ideal.Quotient.mk c) H = 0 ∧ MvPolynomial.map (algebraMap R R') H = G) → ∀ (R R' C' D E ν : Type) [CommRing R] [CommRing R'] [CommRing C'] [CommRing D] [CommRing E] [Algebra R R'] [Algebra R' C'] (c : Ideal R) [Algebra (R ⧸ c) D], (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (π : C' →+* E) (ψ : D →+* E) (ζ : ν → D) (ξ : ν → C'), RingHom.ker π = c.map ((algebraMap R' C').comp (algebraMap R R')) → ψ.comp ((algebraMap (R ⧸ c) D).comp (Ideal.Quotient.mk c)) = (π.comp (algebraMap R' C')).comp (algebraMap R R') → (∀ s, π (ξ s) = ψ (ζ s)) → Function.Surjective (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C') → ∀ f : MvPolynomial ν (R ⧸ c), MvPolynomial.aeval ζ f = 0 → ∃ F : MvPolynomial ν R, MvPolynomial.map (Ideal.Quotient.mk c) F = f ∧ MvPolynomial.aeval ξ (MvPolynomial.map (algebraMap R R') F) = 0 := by
  intro hH R R' C' D E ν _ _ _ _ _ _ _ c _ hc π ψ ζ ξ hker hcomm hξ hsurj f hf
  obtain ⟨F₀, rfl⟩ := MvPolynomial.map_surjective (Ideal.Quotient.mk c) Ideal.Quotient.mk_surjective f
  have hπ : π (MvPolynomial.aeval ξ (MvPolynomial.map (algebraMap R R') F₀)) = 0 := by
    have h1 : π (MvPolynomial.aeval ξ (MvPolynomial.map (algebraMap R R') F₀))
        = ψ (MvPolynomial.aeval ζ (MvPolynomial.map (Ideal.Quotient.mk c) F₀)) := by
      rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_map, MvPolynomial.eval₂_map,
        MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left, ← RingHom.comp_assoc, hcomm]
      congr 1
      funext s
      exact hξ s
    rw [h1, hf, map_zero]
  have hmem : MvPolynomial.aeval ξ (MvPolynomial.map (algebraMap R R') F₀) ∈
      ((c.map (algebraMap R R')).map (MvPolynomial.C : R' →+* MvPolynomial ν R')).map
        (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C') := by
    rw [Ideal.map_map]
    change _ ∈ Ideal.map ((MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C') : MvPolynomial ν R' →+* C') _
    rw [Ideal.map_map]
    have : ((MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C') : MvPolynomial ν R' →+* C').comp
        ((MvPolynomial.C : R' →+* MvPolynomial ν R').comp (algebraMap R R'))
        = (algebraMap R' C').comp (algebraMap R R') := by
      ext x; simp
    rw [this, ← hker]
    exact hπ
  obtain ⟨G, hG, hGe⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).1 hmem
  obtain ⟨H, hH0, hHG⟩ := hH R R' ν c hc G hG
  refine ⟨F₀ - H, ?_, ?_⟩
  · rw [map_sub, hH0, sub_zero]
  · rw [map_sub, hHG, map_sub, hGe, sub_self]

end GlobalTheory.Pinch
