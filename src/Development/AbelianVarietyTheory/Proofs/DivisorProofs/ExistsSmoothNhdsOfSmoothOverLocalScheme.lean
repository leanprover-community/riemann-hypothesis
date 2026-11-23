module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SmoothDense
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothOfRelativeDimensionSpreadFromGeneric
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkGenerizationGermCompat
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.Desc

theorem exists_smooth_nhds_of_smooth_fromSpecStalk :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : Scheme.{0}) (p : P ⟶ Sp R) (x : Sp R) (V W : P.Opens), W ≤ V → Smooth (Limits.pullback.snd (V.ι ≫ p) ((Sp R).fromSpecStalk x)) → LocallyOfFiniteType (W.ι ≫ p) → ∀ z : P, z ∈ W → (p z).asIdeal ≤ x.asIdeal → ∃ W' : P.Opens, z ∈ W' ∧ W' ≤ W ∧ Smooth (W'.ι ≫ p) := by
  intro R _ _ P p x V W hWV hV hW z hz hle
  have : LocallyOfFinitePresentation (W.ι ≫ p) := inferInstance
  have : Flat ((Sp R).fromSpecStalk x) := GlobalTheory.LocalRingGeneralisation.flat_fromSpecStalk _ x
  have : SurjectiveOnStalks ((Sp R).fromSpecStalk x) := inferInstance
  have e : W.ι ≫ p = P.homOfLE hWV ≫ V.ι ≫ p := by simp
  have h1 : Smooth (Limits.pullback.snd (P.homOfLE hWV ≫ V.ι ≫ p) ((Sp R).fromSpecStalk x)) := by
    rw [← pullbackRightPullbackFstIso_inv_snd_snd]
    infer_instance
  have h2 : Smooth (Limits.pullback.snd (W.ι ≫ p) ((Sp R).fromSpecStalk x)) := by
    rw [e]; exact h1
  have hs : p z ⤳ x := (PrimeSpectrum.le_iff_specializes (R := R) _ _).1 hle
  obtain ⟨y, hy⟩ : p z ∈ Set.range ((Sp R).fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]; exact hs
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := W.ι ≫ p)
    (g := (Sp R).fromSpecStalk x) (⟨z, hz⟩ : W) y hy.symm
  have h3 := GlobalTheory.GenSpread.mem_smoothLocus_of_isPullback
    (IsPullback.of_hasPullback (W.ι ≫ p) ((Sp R).fromSpecStalk x)) w
  rw [hw] at h3
  have h4 : Smooth ((W.ι ≫ p).smoothLocus.ι ≫ W.ι ≫ p) := GlobalTheory.smooth_smoothLocus_ι_comp _
  refine ⟨W.ι ''ᵁ (W.ι ≫ p).smoothLocus, ⟨⟨z, hz⟩, h3, rfl⟩, W.ι_image_le _, ?_⟩
  rw [← Scheme.Hom.isoImage_inv_ι, Category.assoc, Category.assoc]
  infer_instance

end GlobalTheory.Desc
