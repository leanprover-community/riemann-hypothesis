module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SheetCoverOfArithmeticVariety
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

theorem _root_.GlobalTheory.T.sheet_cover_of_arithmetic_variety : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (n nc : ℕ) (Bd : Set ((Σ k, J k) → ℂ)) (χ : Fin nc → GroundTheory.Heights₂.Heights.LowerBoundFree.SncChart P n Bd) (V B : ℕ → Set (Fin n → ℂ)) (γ : ℕ → (Fin n → ℂ) → (Σ k, J k) → ℂ) (A : HermLine J) (G : ((Σ k, J k) → ℂ) → ℝ), IsArithVar P (n + 1) → (∀ z ∈ mcPts P, ∃ a, ∃ t : Fin n → ℂ, ‖t‖ ≤ 1 / 2 ∧ z ∈ torusSat {(χ a).γ t}) → IsSheetCover χ V B γ → (∀ m, ContDiffOn ℝ 2 (fun t => Real.log (A.h (γ m t))) (V m)) → (∀ w ∈ mcPts P \ Bd, ∀ w' ∈ torusSat {w}, G w' = G w) → (∀ m, IntegrableOn (fun t => G (γ m t) * maDensity (fun (_ : Fin n) t' => Real.log (A.h (γ m t'))) t) (B m)) → Summable (fun m => ∫ t in B m, |G (γ m t) * maDensity (fun (_ : Fin n) t' => Real.log (A.h (γ m t'))) t|) → ptsIntegral (e := n) P (fun _ z => Real.log (A.h z)) G = ∑' m, ∫ t in B m, G (γ m t) * maDensity (fun (_ : Fin n) t' => Real.log (A.h (γ m t'))) t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.ptsIntegral_sheets | exact GlobalTheory.CompanionTheory.Ar.Cusp.ptsIntegral_sheets | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.ptsIntegral_sheets <;> assumption)
