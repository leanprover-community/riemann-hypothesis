module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThPr
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureFunctionThetaSeriesInvariance
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

theorem _root_.GlobalTheory.T.pure_function_theta_series_invariance : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ →
    ∀ (S T : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (a : (AF F)ˣ),
    Continuous G → HasCompactSupport G → (∀ v ∈ S, Continuous (g v) ∧ HasCompactSupport (g v)) → S ⊆ T →
    (∀ v, v ∉ T → (a : AF F).2 v ∈ v.adicCompletionIntegers F ∧ ((a⁻¹ : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F) →
    ∀ δ : ℝ, 0 < δ →
    {x : F | (∀ v, v ∉ T → algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F) ∧
      phiA G a (fun _ => θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ T, psiA S g a v (fun _ => algebraMap F (Fv F v) x) ≠ 0}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.BasePsi.finite_contributing | exact GlobalTheory.CompanionTheory.BasePsi.finite_contributing | (intros; apply GlobalTheory.CompanionTheory.BasePsi.finite_contributing <;> assumption)
