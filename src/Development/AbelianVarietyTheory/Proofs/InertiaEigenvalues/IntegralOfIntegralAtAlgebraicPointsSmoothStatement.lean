module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralOfIntegralAtAlgebraicPointsSmooth
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
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtIn

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg GlobalTheory.GoodPts GlobalTheory.GoodTransfer

theorem _root_.GlobalTheory.T.integral_of_integral_at_algebraic_points_smooth : ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (la : HeightOneSpectrum (𝓞 K)) (gens : Finset Ω) (e : Ω), Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)) = ⊤ → e ≠ 0 → e ∈ Subring.closure (Set.range ((algebraMap K Ω).comp (la.valuation K).valuationSubring.subtype) ∪ (gens : Set Ω)) → Algebra.Smooth K (Algebra.adjoin K (insert e⁻¹ (gens : Set Ω))) → ∀ r : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)), (∀ (T : CDVR) (io : K →+* T.Fr) (n : ℕ), OverLa la T.V io n → T.FinRes → ∀ ψ : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)) →+* T.Fr, (∀ k : K, ψ (algebraMap K _ k) = io k) → (∀ g : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)), (g : Ω) ∈ gens → InV T (ψ g)) → InV T (ψ r)) → ∀ (T : CDVR) (io : K →+* T.Fr) (n : ℕ), OverLa la T.V io n → ∀ ψ : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)) →+* T.Fr, (∀ k : K, ψ (algebraMap K _ k) = io k) → (∀ g : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)), (g : Ω) ∈ gens → InV T (ψ g)) → InV T (ψ r) := by
  first | exact @GlobalTheory.ChartIntegral.integral_of_integral_at_algebraic_points | exact GlobalTheory.ChartIntegral.integral_of_integral_at_algebraic_points | (intros; apply GlobalTheory.ChartIntegral.integral_of_integral_at_algebraic_points <;> assumption)
