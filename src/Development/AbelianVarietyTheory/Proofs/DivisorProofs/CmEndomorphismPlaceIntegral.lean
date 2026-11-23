module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.BirigidLift
open scoped nonZeroDivisors
open scoped CategoryTheory.Obj

namespace GlobalTheory.PlaceModel


set_option autoImplicit false in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
attribute [local instance] Over.cartesianMonoidalCategory in
open scoped nonZeroDivisors in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.PlaceModel.exists_factor_pullback {S S' S'' : Scheme.{0}} {G : Over S}
    {G' : Over S'} {G'' : Over S''} [GrpObj G]
    [GrpObj G'] [GrpObj G''] {f : S' ⟶ S} {c : S'' ⟶ S} {φ : G'.left ⟶ G.left}
    {ψ : G''.left ⟶ G.left}
    (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G f φ) (n : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G'' G c ψ) (g : S'' ⟶ S') (e : g ≫ f = c) :
    ∃ φ' : G''.left ⟶ G'.left, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G'' G' g φ' ∧ φ' ≫ φ = ψ := by
  subst e
  obtain ⟨hφ, hφm⟩ := h
  obtain ⟨hψ, hψm⟩ := n
  refine ⟨hφ.lift ψ (G''.hom ≫ g) (by rw [hψ.w, Category.assoc]), ⟨?_, ?_⟩, hφ.lift_fst _ _ _⟩
  · refine IsPullback.of_right ?_ (hφ.lift_snd _ _ _) hφ
    rwa [hφ.lift_fst]
  · intro T x y x₀ y₀ hx hy
    apply hφ.hom_ext
    · rw [Category.assoc, hφ.lift_fst]
      let u : Over.mk ((T.hom ≫ g) ≫ f) ⟶ Over.mk (T.hom ≫ g ≫ f) :=
        Over.homMk (𝟙 T.left) (by simp)
      let x₁ : Over.mk (T.hom ≫ g ≫ f) ⟶ G := Over.homMk (x.left ≫ ψ) (by
        simp only [Over.mk_hom, Category.assoc, hψ.w]; simp only [← Category.assoc, Over.w])
      let y₁ : Over.mk (T.hom ≫ g ≫ f) ⟶ G := Over.homMk (y.left ≫ ψ) (by
        simp only [Over.mk_hom, Category.assoc, hψ.w]; simp only [← Category.assoc, Over.w])
      have hψxy := hψm T x y x₁ y₁ rfl rfl
      have hφxy := hφm (Over.mk (T.hom ≫ g)) x₀ y₀ (u ≫ x₁) (u ≫ y₁)
        (by simp [u, x₁, hx, hφ.lift_fst]) (by simp [u, y₁, hy, hφ.lift_fst])
      rw [← hφxy, ← hψxy, ← comp_mul]
      simp [u]
    · rw [Category.assoc, hφ.lift_snd, ← Category.assoc, Over.w, Over.w]
      rfl

end GlobalTheory.PlaceModel

namespace GlobalTheory.PlaceModel

end GlobalTheory.PlaceModel

namespace GlobalTheory.PlaceModel

end GlobalTheory.PlaceModel
