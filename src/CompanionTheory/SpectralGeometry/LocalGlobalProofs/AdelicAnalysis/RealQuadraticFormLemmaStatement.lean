module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RealQuadraticFormLemma
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

theorem _root_.GlobalTheory.T.real_quadratic_form_lemma : ∀ (F : Type) [Field F] [NumberField F], ∀ [MeasurableSpace (A F)] [BorelSpace (A F)], ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) (gf : Ω → Matrix ι ι (A F)) (gi : Ω → InfinitePlace F → Matrix ι ι ℝ), CountData M B ρ Pr gf gi → ∀ a : ℕ, 0 < a → ∀ β : F, β ≠ 0 → ∀ N : ℕ, 0 < N → (∃ r : 𝓞 F, (r : F) = (N : F) * β) → (∀ y : ι → A F, (∀ i, (a : A F) * y i ∈ Oh F) → (N : A F) * qf (hf F) (Bf B) y ∈ Oh F) → ∀ D : Set (InfinitePlace F → ℝ), IsAddFundamentalDomain (latR ρ N) D volume → ∃ I : ℝ≥0, ∫⁻ ω, ∑' x : {x : ι → F // qf (1 / 2 : F) B x = β}, ‖thTerm B ρ P (gf ω) (gi ω) (indL a) (fun _ => Complex.I) x.1‖ₑ ∂Pr = (I : ℝ≥0∞) ∧ IntegrableOn (fun x : InfinitePlace F → ℝ => (∫ ω, theta B ρ P (gf ω) (gi ω) (indL a) (fun w => (x w : ℂ) + Complex.I) ∂Pr) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ))) D volume ∧ ∫ x in D, (∫ ω, theta B ρ P (gf ω) (gi ω) (indL a) (fun w => (x w : ℂ) + Complex.I) ∂Pr) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) = ((volume D).toReal : ℂ) * ((I : ℝ) : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.SW.CoefTheta.fourier_coefficient | exact GlobalTheory.CompanionTheory.SW.CoefTheta.fourier_coefficient | (intros; apply GlobalTheory.CompanionTheory.SW.CoefTheta.fourier_coefficient <;> assumption)
