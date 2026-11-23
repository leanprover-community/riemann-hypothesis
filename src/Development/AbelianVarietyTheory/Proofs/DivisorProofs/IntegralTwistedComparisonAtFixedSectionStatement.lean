module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAtSection
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralTwistedComparisonAtFixedSection
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.integral_twisted_comparison_at_fixed_section : ∀ (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) (σ : K' ≃+* K') (τ : W →+* W), (∀ l : K', l ≠ 0 → ∃ a : W, σ l = algebraMap W K' a * l) → ∀ (φ : G.left ⟶ G.left) (e₀ : Sp W ⟶ G.left), e₀ ≫ G.hom = 𝟙 _ → e₀ ≫ φ = spMap τ ≫ e₀ → ∀ (ρ : pullback G.hom (spMap (algebraMap W K')) ⟶ pullback G.hom (spMap (algebraMap W K'))) (x : Sp K' ⟶ pullback G.hom (spMap (algebraMap W K'))), x ≫ pullback.fst G.hom (spMap (algebraMap W K')) = spMap (algebraMap W K') ≫ e₀ → x ≫ pullback.snd G.hom (spMap (algebraMap W K')) = 𝟙 _ → x ≫ ρ = spMap (σ : K' →+* K') ≫ x → ∀ (M : LB G.left) (N : LB (pullback G.hom (spMap (algebraMap W K')))), M.IsLB → N.IsLB → ∀ (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) N) (w₁ : LB.Iso ((M.pull φ).pull (pullback.fst G.hom (spMap (algebraMap W K')))) N), (∀ (n : N.ι) (i : ((M.pull φ).pull (pullback.fst G.hom (spMap (algebraMap W K')))).ι) (h : ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ ((M.pull φ).pull (pullback.fst G.hom (spMap (algebraMap W K')))).U i)) (h' : ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i PUnit.unit PUnit.unit))), (Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom ((x.appLE _ ⊤ h).hom (w₁.s (n, i)).val) = σ ((Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom ((x.appLE _ ⊤ h').hom (w.s (n, fun _ => i PUnit.unit PUnit.unit)).val))) → GlobalTheory.SectionLattice.IntegralAtSection G.hom w w₁ := by
  first | exact @GlobalTheory.SectionLattice.integralAtSection_of_conj | exact GlobalTheory.SectionLattice.integralAtSection_of_conj | (intros; apply GlobalTheory.SectionLattice.integralAtSection_of_conj <;> assumption)
