module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AddJFintype
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagStep

theorem flagStep_linearEquiv_image {Ω F F' : Type} [Field Ω] [AddCommGroup F] [Module Ω F] [AddCommGroup F']
    [Module Ω F'] (Φ : F ≃ₗ[Ω] F') {r : ℕ} (d : Fin r → F) (i : ℕ) :
    flagStep Ω (fun k => Φ (d k)) i = (flagStep Ω d i).map Φ.toLinearMap := by
  unfold flagStep
  rw [Submodule.map_span, ← Set.image_comp]
  rfl

theorem isFlagVBOn_pull_map : ∀ (X X' : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω]
    (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X) (E F F' : Type)
    [AddCommGroup E] [Module Ω₀ E] [AddCommGroup F] [Module Ω F] [AddCommGroup F'] [Module Ω F']
    (L : Lat ξ E) (j : E →+ F) (Φ : F ≃ₗ[Ω] F') (T : Set (Cpt ξ')) (r : ℕ) (b : Fin r → F),
    (L.pull ξ' f j).IsFlagVBOn T b →
    (L.pull ξ' f (Φ.toLinearMap.toAddMonoidHom.comp j)).IsFlagVBOn T (fun k => Φ (b k)) := by
  intro X X' Ω₀ Ω _ _ ξ ξ' f E F F' _ _ _ _ _ _ L j Φ T r b h
  unfold Lat.IsFlagVBOn at h ⊢
  intro p hp
  obtain ⟨U, hpU, c, hc, hframe⟩ := h p hp
  refine ⟨U, hpU, fun k => Φ (c k), fun i => ?_, fun q hq hqU => ?_⟩
  · rw [flagStep_linearEquiv_image, flagStep_linearEquiv_image, hc i]
  · have hq' := hframe q hq hqU
    unfold Lat.IsFrameAt at hq' ⊢
    obtain ⟨hli, hsp⟩ := hq'
    refine ⟨hli.map' Φ.toLinearMap Φ.ker, ?_⟩
    let φ : F →ₗ[regAt ξ' q] F' := Φ.toLinearMap.restrictScalars (regAt ξ' q)
    unfold Lat.pull at hsp ⊢
    rw [show Set.range (fun k => Φ (c k)) = φ '' Set.range c from Set.range_comp φ c]
    rw [← Submodule.map_span φ, ← hsp, Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨h, e, he, rfl⟩
      exact ⟨j e, ⟨h, e, he, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨h, e, he, rfl⟩, rfl⟩
      exact ⟨h, e, he, rfl⟩

end GlobalTheory.CompanionTheory.Ar.FlagStep
