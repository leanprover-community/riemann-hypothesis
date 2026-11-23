module

public import Mathlib.RingTheory.RingHom.Etale
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtalePolynomialSubstitution
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtArith
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Ar.EtaleCoord

theorem etale_of_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S)
    (g : S →+* T) (hf : f.Etale) (h : (g.comp f).Etale) : g.Etale := by
  algebraize [f, g, g.comp f]
  exact Algebra.Etale.of_restrictScalars R S T

theorem etale_eval₂Hom_iff_int : ∀ (k A : Type) [CommRing k] [CommRing A] (N : ℕ), (Int.castRingHom (Localization.Away (N : k))).Etale → ∀ (φ : k →+* A), IsUnit (N : A) → ∀ (D : ℕ) (x : Fin D → A), (MvPolynomial.eval₂Hom φ x).Etale ↔ (MvPolynomial.eval₂Hom (Int.castRingHom A) x).Etale := by
  intro k A _ _ N hN φ hu D x
  let ι : k →+* Localization.Away (N : k) := algebraMap k _
  have hφN : IsUnit (φ (N : k)) := by simpa using hu
  let ψ : Localization.Away (N : k) →+* A := IsLocalization.Away.lift (N : k) hφN
  have hψ : ψ.comp ι = φ := by
    ext a
    simp [ψ, ι]
  have hι : ι.Etale := by
    rw [RingHom.etale_algebraMap]
    exact Algebra.Etale.of_isLocalizationAway (N : k)
  have ha : (MvPolynomial.map (σ := Fin D) ι).Etale := etale_mvPolynomial_map_of_etale ι hι
  have hb : (MvPolynomial.map (σ := Fin D) (Int.castRingHom (Localization.Away (N : k)))).Etale :=
    etale_mvPolynomial_map_of_etale _ hN
  let Θ := MvPolynomial.eval₂Hom ψ x
  have e1 : MvPolynomial.eval₂Hom φ x = Θ.comp (MvPolynomial.map ι) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [Θ, ← hψ]
    · intro j
      simp [Θ]
  have e2 : MvPolynomial.eval₂Hom (Int.castRingHom A) x =
      Θ.comp (MvPolynomial.map (Int.castRingHom (Localization.Away (N : k)))) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [Θ]
    · intro j
      simp [Θ]
  rw [e1, e2]
  exact ⟨fun h => RingHom.Etale.stableUnderComposition _ _ hb (etale_of_comp _ _ ha h),
    fun h => RingHom.Etale.stableUnderComposition _ _ ha (etale_of_comp _ _ hb h)⟩

end GlobalTheory.CompanionTheory.Ar.EtaleCoord
